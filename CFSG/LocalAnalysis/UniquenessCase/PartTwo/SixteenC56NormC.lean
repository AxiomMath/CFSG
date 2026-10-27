module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem exists_ne_zero_one_add_mul_ne_zero (K : Type*) [Field K] [Finite K] [CharP K 2]
    (h : 4 ≤ Nat.card K) (a : K) : ∃ c : K, c ≠ 0 ∧ 1 + c * a ≠ 0 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : 4 ≤ Fintype.card K := by simpa [Nat.card_eq_fintype_card] using h
  have hbad : ({0, a⁻¹} : Finset K).card ≤ 2 := by
    calc ({0, a⁻¹} : Finset K).card
        = (insert 0 {a⁻¹} : Finset K).card := rfl
      _ ≤ ({a⁻¹} : Finset K).card + 1 := Finset.card_insert_le 0 {a⁻¹}
      _ = 2 := by simp
  have hlt : ({0, a⁻¹} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨c, hc.1, ?_⟩
  intro hzero
  have hca : c * a = 1 := (CharTwo.add_eq_zero.mp hzero).symm
  by_cases ha : a = 0
  · rw [ha, mul_zero] at hca
    exact zero_ne_one hca
  · refine hc.2 ?_
    have hc_eq : c = a⁻¹ := by
      rw [← inv_inv c, ← eq_inv_of_mul_eq_one_right hca]
    exact hc_eq

theorem card_fixed_le_of_isometry {g : MulAut W}
    (hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w))
    (hiso : ∀ w : W, S.Q (g w) = S.Q w) {w : W} (h1 : g w * w⁻¹ ≠ 1)
    (h0 : S.Q (g w * w⁻¹) = 0) :
    Nat.card {v : W // g v = v} ≤ Nat.card S.K ^ 2 := by
  classical
  obtain ⟨γ, hγ⟩ := S.exists_actHom_of_smul_comm hlin
  let U : W := g w * w⁻¹
  have hUne : U ≠ 1 := h1
  have hUQ : S.Q U = 0 := h0
  let L : (OmI → S.K) →ₗ[S.K] (OmI → S.K) :=
    Matrix.mulVecLin (γ : Matrix OmI OmI S.K) - LinearMap.id
  have hLapply : ∀ x : OmI → S.K,
      L x = (γ : Matrix OmI OmI S.K) *ᵥ x - x := by
    intro x
    simp [L, Matrix.mulVecLin_apply]
  let u : OmI → S.K := S.vec U
  have hu_ne : u ≠ 0 := by
    intro h
    apply hUne
    apply S.vec_injective
    rw [S.vec_one]
    exact h
  have hLw : L (S.vec w) = u := by
    rw [hLapply]
    change (γ : Matrix OmI OmI S.K) *ᵥ S.vec w - S.vec w = S.vec (g w * w⁻¹)
    rw [S.vec_mul, S.vec_inv, ← hγ, S.actHom_vec, sub_eq_add_neg]
  have hfix : ∀ X : W, g X = X ↔ L (S.vec X) = 0 := by
    intro X
    simp only [hLapply, sub_eq_zero]
    constructor
    · intro h
      have := congrArg S.vec h
      rwa [← hγ, S.actHom_vec] at this
    · intro h
      apply S.vec_injective
      rw [← hγ, S.actHom_vec, h]
  let fixEquiv : {X : W // g X = X} ≃ L.ker :=
    { toFun := fun X => ⟨S.vec X.1, (hfix X.1).mp X.2⟩
      invFun := fun Y => ⟨S.ofVec Y.1,
        (hfix (S.ofVec Y.1)).mpr (by rw [S.vec_ofVec]; exact Y.2)⟩
      left_inv := fun X => Subtype.ext (S.ofVec_vec X.1)
      right_inv := fun Y => Subtype.ext (S.vec_ofVec Y.1) }
  have hcard : Nat.card {v : W // g v = v}
      = Nat.card S.K ^ Module.finrank S.K L.ker := by
    haveI : Module.Finite S.K L.ker := inferInstance
    calc Nat.card {v : W // g v = v} = Nat.card L.ker := Nat.card_congr fixEquiv
      _ = Nat.card S.K ^ Module.finrank S.K L.ker :=
            Module.natCard_eq_pow_finrank (K := S.K) (V := L.ker)
  have hrg : 2 ≤ Module.finrank S.K L.range := by
    by_contra hlt
    simp only [not_le] at hlt
    have hu_mem : u ∈ L.range := ⟨S.vec w, hLw⟩
    have h1r : 1 ≤ Module.finrank S.K L.range := by
      rw [← finrank_span_singleton (K := S.K) hu_ne]
      exact Submodule.finrank_mono
        ((Submodule.span_singleton_le_iff_mem u L.range).mpr hu_mem)
    have hk1 : Module.finrank S.K L.range = 1 := by omega
    have hspan : L.range = S.K ∙ u :=
      eq_span_singleton_of_mem_of_finrank_eq_one hk1 hu_mem hu_ne
    have hmem : ∀ x : OmI → S.K, ∃ c : S.K, L x = c • u := by
      intro x
      have hx : L x ∈ S.K ∙ u := by rw [← hspan]; exact LinearMap.mem_range_self L x
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, hc.symm⟩
    let a : (OmI → S.K) → S.K := fun x => Classical.choose (hmem x)
    have ha : ∀ x, L x = a x • u := fun x => Classical.choose_spec (hmem x)
    have huniq : ∀ {x : OmI → S.K} {c : S.K}, L x = c • u → c = a x := by
      intro x c hc
      have h : c • u = a x • u := by rw [← hc, ha x]
      exact smul_left_injective (R := S.K) hu_ne h
    have ha_add : ∀ x y : OmI → S.K, a (x + y) = a x + a y := by
      intro x y
      have h : L (x + y) = (a x + a y) • u := by
        rw [map_add, ha x, ha y, add_smul]
      exact (huniq h).symm
    have ha_smul : ∀ (c : S.K) (x : OmI → S.K), a (c • x) = c * a x := by
      intro c x
      have h : L (c • x) = (c * a x) • u := by
        rw [map_smul, ha x, mul_smul]
      exact (huniq h).symm
    have hw1 : a (S.vec w) = 1 := by
      have h : L (S.vec w) = (1 : S.K) • u := by rw [hLw, one_smul]
      exact (huniq h).symm
    have hcoord : ∀ x : OmI → S.K,
        (γ : Matrix OmI OmI S.K) *ᵥ x = a x • u + x := by
      intro x
      have hx := ha x
      rw [hLapply] at hx
      rw [← hx, sub_add_cancel]
    have hgX : ∀ X : W, g X = S.smul (a (S.vec X)) U * X := by
      intro X
      rw [← hγ]
      apply S.vec_injective
      rw [S.actHom_vec, S.vec_mul, S.vec_smul, hcoord (S.vec X)]
    have hrel : ∀ X : W, a (S.vec X) * S.pol U X = 0 := by
      intro X
      have hisoX : S.Q (S.smul (a (S.vec X)) U * X) = S.Q X := by
        rw [← hgX X]; exact hiso X
      rw [S.Q_mul, S.Q_smul, S.pol_smul_left, hUQ, mul_zero, zero_add] at hisoX
      exact add_left_cancel (show S.Q X + a (S.vec X) * S.pol U X = S.Q X + 0 by
        rw [hisoX, add_zero])
    have hpolUw : S.pol U w = 0 := by
      have := hrel w
      rwa [hw1, one_mul] at this
    have hex : ∃ X₂ : W, S.pol U X₂ ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hUne (S.eq_one_of_pol_eq_zero hall)
    obtain ⟨X₂, hX₂⟩ := hex
    obtain ⟨c, hc0, hc1⟩ :=
      exists_ne_zero_one_add_mul_ne_zero S.K S.four_le (a (S.vec X₂))
    let X : W := w * S.smul c X₂
    have hvecX : S.vec X = S.vec w + c • S.vec X₂ := by
      change S.vec (w * S.smul c X₂) = S.vec w + c • S.vec X₂
      rw [S.vec_mul, S.vec_smul]
    have hlX : a (S.vec X) ≠ 0 := by
      rw [hvecX, ha_add, ha_smul, hw1]
      exact hc1
    have hpolX : S.pol U X ≠ 0 := by
      change S.pol U (w * S.smul c X₂) ≠ 0
      rw [S.pol_mul_right, S.pol_smul_right, hpolUw, zero_add]
      exact mul_ne_zero hc0 hX₂
    exact absurd (hrel X) (mul_ne_zero hlX hpolX)
  have hk : Module.finrank S.K L.ker ≤ 2 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    have hV : Module.finrank S.K (OmI → S.K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      decide
    omega
  rw [hcard]
  exact pow_le_pow_right' (show (1 : ℕ) ≤ Nat.card S.K by have := S.four_le; omega) hk

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
