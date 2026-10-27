module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordTorus
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelB

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord
open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SULCoordAux_modelCfg
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} [Fact p.Prime]
    (hH : GGHdRo7SULCoordHyp p B Bs x L D J) (hRig : GGLabelRigidInput)
    (hrow : GGHdRo7SULabL p L) :
    ∃ (m : ℕ) (hx : x ∈ Bs) (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧
      τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, hx⟩ ∧
      SUCoordModel p Bs L m τ := by
  obtain ⟨-, hx, -, -, -⟩ := hdRo7SULCoordAux_rowDataCfg hH hrow
  obtain ⟨m, e, hp3, hm7, hm3d, hiff⟩ := hdRo7SULCoordAux_torusCfg hH hRig hrow hx
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h
    have hp : p ∣ m := (CharP.cast_eq_zero_iff (ZMod p) p m).mp h
    rw [hp3] at hp
    exact hm3d hp
  let dec := hdRo7SULCoordAux_decomp m p hm0
  let τC := hdRo7SULCoordAux_axisEquivCfg hH hx hp3
  let Φ := hdRo7SULCoordAux_prodEquivCfg hH hRig hrow
  let τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs := dec.trans ((e.prodCongr τC).trans Φ)
  let eB : ↥(sumZero m p) →* ↥Bs :=
    { toFun := fun g => ⟨(e g : G), (e g).2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  let τCB : Multiplicative (ZMod p) →* ↥Bs :=
    { toFun := fun b => ⟨(τC b : G), (τC b).2.1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b c => Subtype.ext (by simp) }
  have hτ : ∀ f : Fin m → Multiplicative (ZMod p), τ f = eB ((dec f).1) * τCB ((dec f).2) :=
    fun _ => rfl
  have hτCB1 : τCB (Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, hx⟩ := by
    apply Subtype.ext
    show (τC (Multiplicative.ofAdd (1 : ZMod p)) : G) = x
    exact congrArg Subtype.val (hdRo7SULCoordAux_axisEquiv_apply_oneCfg hH hx hp3)
  have hS_perm : ∀ (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)),
      (∑ j, Multiplicative.toAdd (f (σ⁻¹ j))) = (∑ j, Multiplicative.toAdd (f j)) :=
    fun σ f => Equiv.sum_comp σ⁻¹ (fun j => Multiplicative.toAdd (f j))
  have hdec_perm : ∀ (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)),
      dec (fun i => f (σ⁻¹ i)) = (permAutV σ (dec f).1, (dec f).2) := by
    intro σ f
    apply Prod.ext
    · apply ext_crd
      intro i
      rw [hdRo7SULCoordAux_decomp_crd, crd_permAutV, hdRo7SULCoordAux_decomp_crd,
        hS_perm σ f]
    · rw [hdRo7SULCoordAux_decomp_snd_apply, hdRo7SULCoordAux_decomp_snd_apply, hS_perm σ f]
  have hfixC : ∀ (a : MulAut ↥Bs), a ⟨x, hx⟩ = ⟨x, hx⟩ →
      ∀ b : Multiplicative (ZMod p), a (τCB b) = τCB b := by
    intro a hax b
    have hb : (τC b : G) ∈ Subgroup.zpowers x := by
      rw [← hdRo7SULCoordAux_centralizerCfg hH hp3]
      exact (τC b).2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hb_eq : τCB b = (⟨x, hx⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      show (τC b : G) = x ^ k
      exact hk.symm
    rw [hb_eq, map_zpow, hax]
  have hmain : ∀ a : MulAut ↥Bs,
      (a ⟨x, hx⟩ = ⟨x, hx⟩ ∧ ∃ σ : Equiv.Perm (Fin m),
        ∀ g : ↥(sumZero m p), a (eB g) = eB (permAutV σ g)) ↔
      (∃ σ : Equiv.Perm (Fin m), ∀ f : Fin m → Multiplicative (ZMod p),
        a (τ f) = τ (fun i => f (σ⁻¹ i))) := by
    intro a
    constructor
    · rintro ⟨hax, σ, hσ⟩
      refine ⟨σ, fun f => ?_⟩
      rw [hτ f, hτ (fun i => f (σ⁻¹ i)), hdec_perm σ f, map_mul, hσ (dec f).1,
        hfixC a hax (dec f).2]
    · rintro ⟨σ, hσ⟩
      have hxfix : a ⟨x, hx⟩ = ⟨x, hx⟩ := by
        have h1 : a (τ (fun _ => Multiplicative.ofAdd (1 : ZMod p))) =
            τ (fun i => (fun _ => Multiplicative.ofAdd (1 : ZMod p)) (σ⁻¹ i)) := hσ _
        have h2 : (fun i => (fun _ => Multiplicative.ofAdd (1 : ZMod p)) (σ⁻¹ i)) =
            (fun _ => Multiplicative.ofAdd (1 : ZMod p)) := rfl
        rw [h2, hτ (fun _ => Multiplicative.ofAdd (1 : ZMod p)),
          hdRo7SULCoordAux_decomp_ones m p hm0, map_one, hτCB1, one_mul] at h1
        exact h1
      refine ⟨hxfix, σ, fun g => ?_⟩
      have h1 : a (τ (dec.symm (g, (1 : Multiplicative (ZMod p))))) =
          τ (fun i => (dec.symm (g, (1 : Multiplicative (ZMod p)))) (σ⁻¹ i)) := hσ _
      have hfst : (dec (dec.symm (g, (1 : Multiplicative (ZMod p))))).1 = g := by simp
      have hsnd : (dec (dec.symm (g, (1 : Multiplicative (ZMod p))))).2 = 1 := by simp
      simp only [hτ (dec.symm (g, 1)), hτ (fun i => (dec.symm (g, 1)) (σ⁻¹ i)),
        hdec_perm σ (dec.symm (g, 1)), hfst, hsnd, map_mul, map_one, mul_one] at h1
      exact h1
  refine ⟨m, hx, τ, hp3, hm7, hm3d, ?_, ?_⟩
  · rw [hτ (fun _ => Multiplicative.ofAdd (1 : ZMod p)),
      hdRo7SULCoordAux_decomp_ones m p hm0, map_one, hτCB1, one_mul]
  · intro a
    rw [hiff a]
    have hiffB : (a ⟨x, hx⟩ = ⟨x, hx⟩ ∧ ∃ σ : Equiv.Perm (Fin m),
        ∀ f : ↥(sumZero m p),
          ((a ⟨(e f).1, (e f).2.1⟩ : ↥Bs) : G) =
            ((e (permAutV σ f) : ↥(Bs ⊓ L)) : G)) ↔
        (a ⟨x, hx⟩ = ⟨x, hx⟩ ∧ ∃ σ : Equiv.Perm (Fin m),
          ∀ g : ↥(sumZero m p), a (eB g) = eB (permAutV σ g)) := by
      constructor
      · rintro ⟨hax, σ, hσ⟩
        exact ⟨hax, σ, fun g => Subtype.ext (by simpa [eB] using hσ g)⟩
      · rintro ⟨hax, σ, hσ⟩
        exact ⟨hax, σ, fun g => by
          simpa [eB] using congrArg Subtype.val (hσ g)⟩
    rw [hiffB, hmain a]
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun f i => ?_⟩
      have h1 : τ.symm (a (τ f)) = fun i => f (σ⁻¹ i) := by
        rw [hσ f, MulEquiv.symm_apply_apply]
      rw [h1]
      simp
    · rintro ⟨σ, hσ⟩
      refine ⟨σ, fun f => ?_⟩
      have hg : τ.symm (a (τ f)) = fun i => f (σ⁻¹ i) := by
        funext k
        have h1 := hσ f (σ⁻¹ k)
        exact Multiplicative.toAdd.injective (by simpa using h1)
      rw [← hg, MulEquiv.apply_symm_apply]

theorem hdRo7SULCoordAux_model
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} [Fact p.Prime]
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J L) :
    ∃ (m : ℕ) (hx : x ∈ Bs) (τ : (Fin m → Multiplicative (ZMod p)) ≃* ↥Bs),
      p = 3 ∧ 7 ≤ m ∧ ¬ 3 ∣ m ∧
      τ (fun _ => Multiplicative.ofAdd (1 : ZMod p)) = ⟨x, hx⟩ ∧
      SUCoordModel p Bs L m τ :=
  hdRo7SULCoordAux_modelCfg (hdRo7SULCoordAux_hyp_of_resHyp hH) hRig
    (hdRo7SULCoordAux_labL_of_row hrow)

end CFSG.StandardType.HdRo7SU

end
