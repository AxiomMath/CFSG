module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Quadratic

variable {W : Type*} [CommGroup W] [Finite W]

private theorem s16b_padicValNat_card_eq_finrank {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] : padicValNat 2 (Nat.card M) = Module.finrank (ZMod 2) M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M), Nat.card_zmod,
    padicValNat.prime_pow]

theorem two_mul_rk_le_of_totallySingular (hW : ∀ x : W, x * x = 1) {Q : W → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (U : Subgroup W) (hU : ∀ u ∈ U, Q u = 0) :
    2 * rk ↥U ≤ rk ↥(⊤ : Subgroup W) := by
  classical
  have h2 : ∀ x : Additive W, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact congrArg Additive.ofMul (hW (Additive.toMul x))
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hadd_l : ∀ x y z : W, polarQ Q (x * y) z = polarQ Q x z + polarQ Q y z := hQ.1.1
  have hadd_r : ∀ x y z : W, polarQ Q x (y * z) = polarQ Q x y + polarQ Q x z := hQ.1.2
  have hone_l : ∀ z : W, polarQ Q 1 z = 0 := by
    intro z
    have := hadd_l 1 1 z
    simpa using this
  have hone_r : ∀ z : W, polarQ Q z 1 = 0 := by
    intro z
    have := hadd_r z 1 1
    simpa using this
  have hsc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  let B : LinearMap.BilinForm (ZMod 2) (Additive W) :=
    LinearMap.mk₂ (ZMod 2) (fun x y => polarQ Q (Additive.toMul x) (Additive.toMul y))
      (fun x y z => hadd_l _ _ _)
      (fun c x y => by
        rcases hsc c with rfl | rfl
        · simp [hone_l]
        · simp)
      (fun x y z => hadd_r _ _ _)
      (fun c x y => by
        rcases hsc c with rfl | rfl
        · simp [hone_r]
        · simp)
  have hsymm : ∀ x y : W, polarQ Q x y = polarQ Q y x := by
    intro x y
    unfold polarQ
    rw [mul_comm x y]
    ring
  have hB : B.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · by_contra hne
      have hne' : Additive.toMul x ≠ 1 := fun h => hne (by simpa using congrArg Additive.ofMul h)
      obtain ⟨y, hy⟩ := hQ.2 _ hne'
      exact hy (hx (Additive.ofMul y))
    · by_contra hne
      have hne' : Additive.toMul y ≠ 1 := fun h => hne (by simpa using congrArg Additive.ofMul h)
      obtain ⟨x, hx⟩ := hQ.2 _ hne'
      exact hx (by rw [hsymm]; exact hy (Additive.ofMul x))
  set U' : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup U) with hU'
  have hmem : ∀ x : Additive W, x ∈ U' ↔ Additive.toMul x ∈ U := fun x => Iff.rfl
  have hle : U' ≤ B.orthogonal U' := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    show polarQ Q (Additive.toMul n) (Additive.toMul x) = 0
    have hn' := (hmem n).1 hn
    have hx' := (hmem x).1 hx
    unfold polarQ
    rw [hU _ hn', hU _ hx', hU _ (U.mul_mem hn' hx')]
    simp
  have h1 := Submodule.finrank_mono hle
  have h3 := LinearMap.BilinForm.finrank_orthogonal hB U'
  have h4 := Submodule.finrank_le U'
  have hcU : rk ↥U = Module.finrank (ZMod 2) ↥U' := by
    unfold rk
    rw [← s16b_padicValNat_card_eq_finrank]
    congr 1
  have hcT : rk ↥(⊤ : Subgroup W) = Module.finrank (ZMod 2) (Additive W) := by
    unfold rk
    rw [← s16b_padicValNat_card_eq_finrank (M := Additive W)]
    congr 1
    exact Nat.card_congr ((Subgroup.topEquiv).toEquiv.trans (Equiv.refl _))
  rw [hcU, hcT]
  omega

theorem two_mul_rk_lt_of_totallySingular_minus (hW : ∀ x : W, x * x = 1) {Q : W → ZMod 2}
    (hQ : IsMinusQuadF2 Q) (U : Subgroup W) (hU : ∀ u ∈ U, Q u = 0) :
    2 * rk ↥U < rk ↥(⊤ : Subgroup W) := by
  refine lt_of_le_of_ne (two_mul_rk_le_of_totallySingular hW hQ.1 U hU) fun h => ?_
  exact hQ.2 ⟨U, hU, h⟩

end Quadratic

section Section16

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_M_of_mem_inf_V₀ (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {U : Subgroup G} {z : G} (hzU : z ∈ U) (hzV₀ : z ∈ V₀) (hz : z ≠ 1) :
    centralizer (U : Set G) ≤ D.M := by
  have hXV : Subgroup.zpowers z ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
  have hX1 : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz
  have hN := h.hyp62.normalizer_le _ hXV hX1
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)).trans
    (((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN)

theorem rk_top_vtil_add_mSub (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) :
    rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V := by
  have h := s15_Infra_mSub_eq_rk_imgTil_add V₀ V V hV le_rfl
  rw [s15_Infra_imgTil_top, inf_eq_right.2 hV₀] at h
  exact h.symm

theorem mSub_eq_mQuot_add (V U : Subgroup G) (hV : IsElemAbelian 2 V) (hUV : U ≤ V) :
    mSub V = E3.mQuot V U + mSub U := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hU2 : IsPGroup 2 U := hV2.to_le hUV
  have h := E3.card_eq_two_pow_mul hV2 hUV
  rw [card_eq_two_pow_mSub hV2, card_eq_two_pow_mSub hU2, ← pow_add] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem le_rMV_of_forall_rk_imgTil_le (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {b c : ℕ} (hbc : b + c ≤ mSub V)
    (hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil V₀ V h.isElemAbelian U) ≤ b) :
    (c : ℕ∞) ≤ rMV D.M V := by
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUC⟩ := hU
  have hV := h.isElemAbelian
  have hinf : U ⊓ V₀ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    exact hUC (centralizer_le_M_of_mem_inf_V₀ D h hz.1 hz.2 hz1)
  have hmU : mSub U = rk ↥(imgTil V₀ V hV U) := by
    have := s15_Infra_mSub_eq_rk_imgTil_add V₀ V U hV hUV
    rw [hinf] at this
    simpa [mSub, rk] using this
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hbU := hb U hUV hUC
  exact_mod_cast (by omega : c ≤ E3.mQuot V U)

theorem sixteen_twentyEight_r (D : Data G) (h26 : R16_26 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_8 D V₀ V hV L → ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  intro V₀ V L hV hS h8
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  obtain ⟨⟨Q, hQ, hQinv⟩, hall⟩ := h26 V₀ V L hV hS h8
  have hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M :=
    fun x hx => ((hall Q hQ hQinv).2 _ hx).2 x rfl
  have hV₀V : V₀ ≤ V := hH.pairFacts.le
  have hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V :=
    rk_top_vtil_add_mSub V₀ V hV hV₀V
  have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le hH hV
  have hrk1 : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) + mSub (v1Sub D.M V₀ V hV L) = mSub V :=
    rk_top_vtil_add_mSub (v1Sub D.M V₀ V hV L) V hV hV₁V
  have hmono : mSub V₀ ≤ mSub (v1Sub D.M V₀ V hV L) :=
    rk_mono (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have h8rk : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 8 := h8.2.1
  have hbc : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) / 2 + (mSub V₀ + 4) ≤ mSub V := by omega
  refine le_rMV_of_forall_rk_imgTil_le D hH hbc ?_
  intro U hUV hUC
  have hts : ∀ q ∈ imgTil V₀ V hV U, Q q = 0 := by
    intro q hq
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
    by_contra hne
    exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans (hns x hne))
  have hsq : ∀ w : Vtil V₀ V hV, w * w = 1 := fun w => by
    simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  have hW := two_mul_rk_le_of_totallySingular hsq hQ.1 (imgTil V₀ V hV U) hts
  omega

end Section16

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
