module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixF
public import CFSG.LocalAnalysis.WeakClosure81.W15Inputs
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenFinal
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2 commutatorElement

theorem conjSub_eq_of_forall_mem {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (k : LGL 2 V) (Z : Submodule (ZMod 2) V) (h : ∀ z ∈ Z, k z ∈ Z) :
    CFSG.Quasithin.G11.conjSub k Z = Z := by
  have hle : CFSG.Quasithin.G11.conjSub k Z ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact h z hz
  haveI : FiniteDimensional (ZMod 2) ↥Z := Module.Finite.of_finite
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq k Z)

theorem mem_iff_forall_of_isMaxSubgroupIn {Γ V : Type} [Group Γ] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Γ →* LGL 2 V) {B : Subgroup Γ}
    (hB : IsMaxSubgroupIn ⊤ B) (Z : Submodule (ZMod 2) V)
    (hBZ : ∀ g ∈ B, ∀ z ∈ Z, ρ g z ∈ Z) (hnot : ∃ g : Γ, ∃ z ∈ Z, ρ g z ∉ Z) (g : Γ) :
    g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z := by
  let N : Subgroup Γ := (CFSG.Quasithin.G11.stabilizerOf (⊤ : Subgroup (LGL 2 V)) Z).comap ρ
  have hN : ∀ g : Γ, g ∈ N ↔ ∀ z ∈ Z, ρ g z ∈ Z := by
    intro g
    constructor
    · intro hg z hz
      have h1 : CFSG.Quasithin.G11.conjSub (ρ g) Z = Z := hg.2
      rw [← h1]
      exact ⟨z, hz, rfl⟩
    · intro hg
      exact ⟨Subgroup.mem_top _, conjSub_eq_of_forall_mem (ρ g) Z hg⟩
  have hBN : B ≤ N := fun g hg => (hN g).2 (hBZ g hg)
  have hNtop : N ≠ ⊤ := by
    intro htop
    obtain ⟨g, z, hz, hgz⟩ := hnot
    exact hgz ((hN g).1 (htop ▸ Subgroup.mem_top g) z hz)
  have hNB : N = B := by
    by_contra hne
    exact hNtop (hB.2 N (lt_of_le_of_ne hBN (Ne.symm hne)) le_top)
  rw [← hNB]
  exact hN g

theorem exists_pow_isPGroup_orderOf_map_eq {G Q : Type*} [Group G] [Finite G] [Group Q]
    {X : Subgroup G} (π : ↥X →* Q) {y : G} (hy : y ∈ X) {r : ℕ} (hr : r.Prime)
    (hπ : orderOf (π ⟨y, hy⟩) = r) :
    ∃ k : ℕ, ∃ hk : y ^ k ∈ X, IsPGroup r (Subgroup.zpowers (y ^ k)) ∧
      orderOf (π ⟨y ^ k, hk⟩) = r := by
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, s, hs, hys⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy0 r hr.ne_one
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (dvd_zero r)
  have hdvds : s ∣ orderOf y := ⟨r ^ a, by rw [hys, mul_comm]⟩
  have hord : orderOf (y ^ s) = r ^ a := by
    rw [orderOf_pow_of_dvd hs0 hdvds, hys]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)
  refine ⟨s, X.pow_mem hy s, IsPGroup.of_card (by rw [Nat.card_zpowers, hord]), ?_⟩
  have hpow : (⟨y ^ s, X.pow_mem hy s⟩ : ↥X) = (⟨y, hy⟩ : ↥X) ^ s := rfl
  rw [hpow, map_pow, Nat.Coprime.orderOf_pow, hπ]
  rw [hπ]
  exact (Nat.Prime.coprime_iff_not_dvd hr).2 hs

theorem kerQuotMk_mem_kerQuotImg_iff {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (x : ↥H) : kerQuotMk M H x ∈ kerQuotImg M H M ↔ (x : G) ∈ M := by
  obtain ⟨x, hx⟩ := x
  have h1 := mem_kerQuotLift_iff (M := M) (H := H) (Y := kerQuotImg M H M) (x := x)
  rw [kerQuotLift_kerQuotImg_left] at h1
  constructor
  · intro hmem
    exact (Subgroup.mem_inf.1 (h1.2 ⟨hx, hmem⟩)).1
  · intro hxM
    obtain ⟨hx', hmem⟩ := h1.1 (Subgroup.mem_inf.2 ⟨hxM, hx⟩)
    exact hmem

variable {G : Type} [Group G] [Finite G]

namespace Cex156

variable {M V₀ V U S A X T : Subgroup G}

theorem exists_repBar [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T)
    (hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G)) :
    ∃ ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T)),
      ∀ x : ↥X, ρ (kerQuotMk M X x) = h.rep x := by
  have hle : (M.subgroupOf X).normalCore ≤ h.rep.ker := by
    rw [h.ker_rep, ← subgroupOf_kerMOf]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 ⟨x.2, hK (Subgroup.mem_subgroupOf.1 hx)⟩
  exact ⟨QuotientGroup.lift _ h.rep hle, fun x => rfl⟩

theorem quotient_min (h : Cex156 M V₀ V U S A X T) :
    ∀ L : Subgroup (KerQuot M X), kerQuotImg M X A ≤ L → ¬ L ≤ kerQuotImg M X M → L = ⊤ := by
  intro L hAL hLB
  by_contra hne
  obtain ⟨L', hL'max, hLL'⟩ := exists_isMaxSubgroupIn (lt_top_iff_ne_top.2 hne)
  have hmem : L' ∈ maxOver ⊤ (kerQuotImg M X A) := ⟨hL'max, hAL.trans hLL'⟩
  rw [maxOver_kerQuotImg_of_inf h.A_le_X h.min.toPairAt.maxOver_eq, Set.mem_singleton_iff] at hmem
  exact hLB (hLL'.trans hmem.le)

theorem finrank_sub_le [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T) :
    Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) ≤ mSub V₀ := by
  have h1 : Nat.card (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 := CFSG.Goldschmidt.G2.card_sub (A := eSub V₀ X T) V₀
  have h3 : Nat.card ↥(eSub V₀ X T ⊓ V₀) ∣ Nat.card ↥V₀ := Subgroup.card_dvd_of_le inf_le_right
  rw [← h2, h1, card_eq_two_pow_mSub h.cex.hyp.elemAbelian₀.isPGroup] at h3
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3

theorem le_eSub_of_finrank_eq [Fact (IsElemAbelian 2 (eSub V₀ X T))]
    (h : Cex156 M V₀ V U S A X T)
    (hfin : Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) = mSub V₀) :
    V₀ ≤ eSub V₀ X T := by
  have h1 : Nat.card (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 := CFSG.Goldschmidt.G2.card_sub (A := eSub V₀ X T) V₀
  have hcard : Nat.card ↥V₀ ≤ Nat.card ↥(eSub V₀ X T ⊓ V₀) := by
    rw [← h2, h1, hfin, card_eq_two_pow_mSub h.cex.hyp.elemAbelian₀.isPGroup]
  exact inf_eq_right.1 (Subgroup.eq_of_le_of_card_ge inf_le_right hcard)

theorem setting12One [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h : Cex156 M V₀ V U S A X T)
    {n : ℕ} (hn : IsPSL 2 2 n (KerQuot M X) ∨ IsSz n (KerQuot M X))
    (hB : IsBorelIn (⊤ : Subgroup (KerQuot M X)) (kerQuotImg M X M))
    {ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T))}
    (hρ : ∀ x : ↥X, ρ (kerQuotMk M X x) = h.rep x) :
    Setting12One ρ (kerQuotImg M X M) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀)
      (kerQuotImg M X A) n (mSub V₀) where
  type := hn
  borel := hB
  stab := by
    have hBmax : IsMaxSubgroupIn ⊤ (kerQuotImg M X M) := by
      have hmem : kerQuotImg M X M ∈ maxOver ⊤ (kerQuotImg M X A) := by
        rw [maxOver_kerQuotImg_of_inf h.A_le_X h.min.toPairAt.maxOver_eq]
        exact Set.mem_singleton _
      exact hmem.1
    have hBZ : ∀ g ∈ kerQuotImg M X M, ∀ z ∈ CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀,
        ρ g z ∈ CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ := by
      intro g hg z hz
      obtain ⟨x, rfl⟩ := kerQuotMk_surjective M X g
      have hxM : (x : G) ∈ M := (kerQuotMk_mem_kerQuotImg_iff x).1 hg
      rw [hρ x, CFSG.Goldschmidt.G2.mem_sub, h.rep_apply]
      have hnorm : (x : G) ∈ normalizer (V₀ : Set G) := by
        rw [h.cex.hyp.normalizer₀]
        exact hxM
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 hz
    have hnot : ∃ g : KerQuot M X, ∃ z ∈ CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀,
        ρ g z ∉ CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ := by
      by_contra hcon
      push Not at hcon
      have hEV : eSub V₀ X T ≤ V₀ := by
        refine conjClosure_le fun x hx z hz => ?_
        have hzE : z ∈ eSub V₀ X T := le_conjClosure _ _ hz
        have := hcon (kerQuotMk M X ⟨x, hx⟩) (Additive.ofMul ⟨z, hzE⟩) hz.1
        rw [hρ, CFSG.Goldschmidt.G2.mem_sub, h.rep_apply] at this
        simpa using this
      have hAE : A ≤ centralizer (eSub V₀ X T : Set G) := by
        refine Subgroup.le_centralizer_iff.2 fun e he => ?_
        exact Subgroup.mem_centralizer_iff.2 fun a ha => h.commute_A_V₀ a ha e (hEV he)
      apply h.A_ne_bot
      rw [eq_bot_iff, ← h.inf_centralizer_eq_bot]
      exact le_inf le_rfl hAE
    exact mem_iff_forall_of_isMaxSubgroupIn ρ hBmax _ hBZ hnot
  A_le_B := kerQuotImg_mono h.A_le_M
  A_elem := isElemAbelian_kerQuotImg h.isElemAbelian_A
  A_card := by
    rw [card_kerQuotImg h.A_le_X, h.inf_ker_eq_bot, Subgroup.relIndex_bot_left, h.card_A]
  one_lt_m := h.cex.one_lt_mSub
  quad := by
    have hmap : (kerQuotImg M X A).map ρ = (A.subgroupOf X).map h.rep := by
      unfold kerQuotImg
      rw [Subgroup.map_map]
      congr 1
      exact MonoidHom.ext hρ
    have := h.repQuad
    unfold RepQuad at this ⊢
    rwa [hmap]

theorem fixedPointFree [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h122 : W3Lem122Two)
    (h : Cex156 M V₀ V U S A X T) {n : ℕ}
    (hn : IsPSL 2 2 n (KerQuot M X) ∨ IsSz n (KerQuot M X))
    (hB : IsBorelIn (⊤ : Subgroup (KerQuot M X)) (kerQuotImg M X M))
    (hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G))
    {y : G} (hyX : y ∈ X) (hyM : y ∈ M)
    (hodd : Odd (orderOf (kerQuotMk M X ⟨y, hyX⟩))) (hne : kerQuotMk M X ⟨y, hyX⟩ ≠ 1) :
    ∀ v ∈ V₀, y * v * y⁻¹ = v → v = 1 := by
  obtain ⟨ρ, hρ⟩ := h.exists_repBar hK
  obtain ⟨-, hrank, hfix⟩ := h122 ρ (kerQuotImg M X M) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀)
    (kerQuotImg M X A) n (mSub V₀) (h.setting12One hn hB hρ) h.quotient_min h.finrank_sub_le
  have hV₀E : V₀ ≤ eSub V₀ X T := h.le_eSub_of_finrank_eq hrank
  intro v hv hyv
  have hvE : v ∈ eSub V₀ X T := hV₀E hv
  have hmemB : kerQuotMk M X ⟨y, hyX⟩ ∈ kerQuotImg M X M :=
    (kerQuotMk_mem_kerQuotImg_iff ⟨y, hyX⟩).2 hyM
  have hz : Additive.ofMul (⟨v, hvE⟩ : ↥(eSub V₀ X T)) ∈
      CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀ := hv
  have h0 := hfix _ hmemB hodd hne _ hz (by
    rw [hρ]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [h.rep_apply]
    simpa using hyv)
  have h1 := congrArg (fun w : Additive ↥(eSub V₀ X T) => ((Additive.toMul w : ↥(eSub V₀ X T)) : G))
    h0
  simpa using h1

end Cex156

end CFSG.LocalAnalysis.WeakClosure81
