module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusFixed
import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank
import CFSG.LocalAnalysis.StandardType.GGTorCPlane

public section

namespace CFSG.StandardType.CommonJSpTwo

open CFSG.Open (StatedSp)
open CFSG.StandardType.SpJoin
open Multiplicative

private lemma card_inf_centralizer_of_aut {K : Type} [Field K] [Finite K] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {J : Subgroup (StatedSp r K)}
    {Γ : Subgroup (MulAut (Fin r → Multiplicative (ZMod 3)))}
    (hAut : FrameBs.sectionFrameAut (spPlaneTorus r ζ) J = Γ)
    (hfix : ∀ f : Fin r → Multiplicative (ZMod 3), (∀ τ ∈ Γ, τ f = f) →
      ∀ j ∈ J, spPlaneTorus r ζ f * j = j * spPlaneTorus r ζ f) :
    Nat.card ↥((spPlaneTorus r ζ).range ⊓
        Subgroup.centralizer (J : Set (StatedSp r K))) =
      Nat.card {f : Fin r → Multiplicative (ZMod 3) // ∀ τ ∈ Γ, τ f = f} := by
  classical
  have hinj : Function.Injective (spPlaneTorus r ζ) := TorC.spPlaneTorus_injective hζ r
  let toFixed : ↥((spPlaneTorus r ζ).range ⊓
        Subgroup.centralizer (J : Set (StatedSp r K))) →
      {f : Fin r → Multiplicative (ZMod 3) // ∀ τ ∈ Γ, τ f = f} := fun x =>
    let g := Classical.choose (MonoidHom.mem_range.mp x.2.1)
    ⟨g, by
      have hg : spPlaneTorus r ζ g = x.1 :=
        Classical.choose_spec (MonoidHom.mem_range.mp x.2.1)
      have hfixed : ∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus r ζ) J, τ g = g := by
        intro τ hτ
        obtain ⟨n, hnJ, hn⟩ := hτ
        have hx : x.1 * n = n * x.1 :=
          (Subgroup.mem_centralizer_iff.mp x.2.2 n hnJ).symm
        refine hinj ?_
        rw [← hn g, hg]
        exact mul_inv_eq_iff_eq_mul.mpr hx.symm
      simpa only [hAut] using hfixed⟩
  let ofFixed : {f : Fin r → Multiplicative (ZMod 3) // ∀ τ ∈ Γ, τ f = f} →
      ↥((spPlaneTorus r ζ).range ⊓
        Subgroup.centralizer (J : Set (StatedSp r K))) := fun f =>
    ⟨spPlaneTorus r ζ f.1,
      Subgroup.mem_inf.mpr
        ⟨MonoidHom.mem_range.mpr ⟨f.1, rfl⟩,
          Subgroup.mem_centralizer_iff.mpr fun j hj => (hfix f.1 f.2 j hj).symm⟩⟩
  refine Nat.card_congr ?_
  refine
    { toFun := toFixed
      invFun := ofFixed
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    exact Classical.choose_spec (MonoidHom.mem_range.mp x.2.1)
  · intro f
    apply Subtype.ext
    exact hinj (Classical.choose_spec
      (MonoidHom.mem_range.mp (ofFixed f).2.1))

private lemma card_fixed_signed {r : ℕ} (S : Finset (Fin r)) :
    Nat.card {f : Fin r → Multiplicative (ZMod 3) //
        ∀ τ ∈ TypeBDatum.signedSupportedAut r 3 S, τ f = f} = 3 ^ (r - S.card) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun f => ⟨
    fun hf i hi => OrthTorus.tbjA_fixed_of_mem_signedSupportedAut (p := 3) (by norm_num)
      hf i hi,
    fun hf τ hτ => SympMinus.fixed_of_vanish_signedSupportedAut (p := 3) S hf τ hτ⟩)]
  exact FrameBs.card_frame_trivial_on S

private lemma card_fixed_twisted {r : ℕ} {S : Finset (Fin r)} {s : Fin r → ZMod 3}
    (hs : ∀ i, s i * s i = 1) (hS : 2 ≤ S.card) :
    Nat.card {f : Fin r → Multiplicative (ZMod 3) //
        ∀ τ ∈ TypeBDatum.twistedPermAut r 3 S s hs, τ f = f} = 3 ^ (r + 1 - S.card) := by
  classical
  haveI : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  let fwd : {f : Fin r → Multiplicative (ZMod 3) //
        ∀ τ ∈ TypeBDatum.twistedPermAut r 3 S s hs, τ f = f} →
      ZMod 3 × ({i : Fin r // i ∉ S} → Multiplicative (ZMod 3)) :=
    fun f => (toAdd (f.1 i₀) * s i₀, fun i => f.1 i.1)
  let bwd : ZMod 3 × ({i : Fin r // i ∉ S} → Multiplicative (ZMod 3)) →
      {f : Fin r → Multiplicative (ZMod 3) //
        ∀ τ ∈ TypeBDatum.twistedPermAut r 3 S s hs, τ f = f} := fun ag =>
    ⟨fun i => if h : i ∈ S then ofAdd (s i * ag.1) else ag.2 ⟨i, h⟩, by
      refine SympMinus.fixed_of_twisted_twistedPermAut (p := 3) S hs (a := ag.1) ?_
      intro i hi
      simp only [hi, dif_pos, toAdd_ofAdd]⟩
  have hleft : Function.LeftInverse bwd fwd := by
    intro f
    apply Subtype.ext
    funext i
    dsimp only [bwd, fwd]
    by_cases hi : i ∈ S
    · obtain ⟨a, ha⟩ := OrthTorus.tbjA_fixed_of_mem_twistedPermAut (p := 3) s hs f.2
      have h0 : toAdd (f.1 i₀) * s i₀ = a := by
        rw [ha i₀ hi₀, mul_assoc, hs i₀, mul_one]
      rw [dif_pos hi, h0, mul_comm (s i) a, ← ha i hi, ofAdd_toAdd]
    · rw [dif_neg hi]
  have hright : Function.RightInverse bwd fwd := by
    intro ag
    refine Prod.ext ?_ ?_
    · change toAdd (if h : i₀ ∈ S then ofAdd (s i₀ * ag.1) else ag.2 ⟨i₀, h⟩) * s i₀ = ag.1
      rw [dif_pos hi₀]
      simp only [toAdd_ofAdd]
      rw [mul_comm (s i₀) ag.1, mul_assoc, hs i₀, mul_one]
    · funext i
      change (if h : i.1 ∈ S then ofAdd (s i.1 * ag.1) else ag.2 ⟨i.1, h⟩) = ag.2 i
      rw [dif_neg i.2]
  rw [Nat.card_congr
    { toFun := fwd, invFun := bwd, left_inv := hleft, right_inv := hright }]
  rw [Nat.card_prod, Nat.card_zmod, Nat.card_fun,
    Nat.card_congr (Multiplicative.toAdd), Nat.card_zmod,
    Nat.card_eq_fintype_card (α := {i : Fin r // i ∉ S}),
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
  have hSr : S.card ≤ r := by simpa using Finset.card_le_univ S
  have h1 : r + 1 - S.card = r - S.card + 1 := by omega
  rw [h1, pow_succ]
  ring

theorem ggCommonJSpTwo_count_signed {K : Type} [Field K] [Finite K] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ)
    {J : Subgroup (StatedSp r K)} {S : Finset (Fin r)} (hS : 1 ≤ S.card)
    (hAut : FrameBs.sectionFrameAut (spPlaneTorus r ζ) J =
      TypeBDatum.signedSupportedAut r 3 S)
    (hfix : ∀ f : Fin r → Multiplicative (ZMod 3),
      (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus r ζ) J, τ f = f) →
        ∀ j ∈ J, spPlaneTorus r ζ f * j = j * spPlaneTorus r ζ f) :
    Nat.card ↥((spPlaneTorus r ζ).range ⊓
      Subgroup.centralizer (J : Set (StatedSp r K))) = 3 ^ (r - S.card) := by
  rw [card_inf_centralizer_of_aut hζ
    (Γ := FrameBs.sectionFrameAut (spPlaneTorus r ζ) J) rfl hfix, hAut]
  exact card_fixed_signed S

theorem ggCommonJSpTwo_count_twisted {K : Type} [Field K] [Finite K] {r : ℕ}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ)
    {J : Subgroup (StatedSp r K)} {S : Finset (Fin r)} {s : Fin r → ZMod 3}
    (hs : ∀ i, s i * s i = 1) (hS : 2 ≤ S.card)
    (hAut : FrameBs.sectionFrameAut (spPlaneTorus r ζ) J =
      TypeBDatum.twistedPermAut r 3 S s hs)
    (hfix : ∀ f : Fin r → Multiplicative (ZMod 3),
      (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus r ζ) J, τ f = f) →
        ∀ j ∈ J, spPlaneTorus r ζ f * j = j * spPlaneTorus r ζ f) :
    Nat.card ↥((spPlaneTorus r ζ).range ⊓
      Subgroup.centralizer (J : Set (StatedSp r K))) = 3 ^ (r + 1 - S.card) := by
  rw [card_inf_centralizer_of_aut hζ
    (Γ := FrameBs.sectionFrameAut (spPlaneTorus r ζ) J) rfl hfix, hAut]
  exact card_fixed_twisted hs hS

end CFSG.StandardType.CommonJSpTwo

end
