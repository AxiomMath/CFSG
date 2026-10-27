module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem linear_isometry_of_card_fixed_gt {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (S.omega : Set (MulAut W))) (hord : g * g = 1)
    (hfix : Nat.card S.K ^ 2 < Nat.card {v : W // g v = v}) :
    (∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w)) ∧
      ∀ w : W, S.Q (g w) = S.Q w := by
  obtain ⟨σ, hσ⟩ := S.exists_ringEquiv_of_mem_normalizer hg
  have hσ1 : σ = RingEquiv.refl S.K := by
    by_contra hne
    exact absurd (S.card_fixed_le_of_semilinear hne hσ) (not_le.2 hfix)
  have hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w) := by
    intro c w
    simpa [hσ1] using hσ c w
  obtain ⟨c, -, hc⟩ := S.exists_similitude_of_linear hg hlin
  exact ⟨hlin, S.Q_apply_eq_of_similitude hc ⟨1, by rw [pow_one, pow_two]; exact hord⟩⟩

theorem exists_line_of_card_fixed_gt {g : MulAut W}
    (hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w))
    (hiso : ∀ w : W, S.Q (g w) = S.Q w) (hg1 : g ≠ 1)
    (hfix : Nat.card S.K ^ 2 < Nat.card {v : W // g v = v}) :
    ∃ e : W, S.Q e ≠ 0 ∧ (∃ w₀ : W, g w₀ * w₀⁻¹ = e) ∧
      ∀ w : W, ∃ a : S.K, g w * w⁻¹ = S.smul a e := by
  classical
  obtain ⟨γ, hγ⟩ := S.exists_actHom_of_smul_comm hlin
  let L : (OmI → S.K) →ₗ[S.K] (OmI → S.K) :=
    Matrix.mulVecLin (γ : Matrix OmI OmI S.K) - LinearMap.id
  have hLapply : ∀ x : OmI → S.K,
      L x = (γ : Matrix OmI OmI S.K) *ᵥ x - x := by
    intro x
    simp [L, Matrix.mulVecLin_apply]
  have hLw : ∀ w : W, L (S.vec w) = S.vec (g w * w⁻¹) := by
    intro w
    rw [hLapply]
    change (γ : Matrix OmI OmI S.K) *ᵥ S.vec w - S.vec w = S.vec (g w * w⁻¹)
    rw [S.vec_mul, S.vec_inv, ← hγ, S.actHom_vec, sub_eq_add_neg]
  have hfixp : ∀ X : W, g X = X ↔ L (S.vec X) = 0 := by
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
    { toFun := fun X => ⟨S.vec X.1, (hfixp X.1).mp X.2⟩
      invFun := fun Y => ⟨S.ofVec Y.1,
        (hfixp (S.ofVec Y.1)).mpr (by rw [S.vec_ofVec]; exact Y.2)⟩
      left_inv := fun X => Subtype.ext (S.ofVec_vec X.1)
      right_inv := fun Y => Subtype.ext (S.vec_ofVec Y.1) }
  have hcard : Nat.card {v : W // g v = v}
      = Nat.card S.K ^ Module.finrank S.K L.ker := by
    haveI : Module.Finite S.K L.ker := inferInstance
    calc Nat.card {v : W // g v = v} = Nat.card L.ker := Nat.card_congr fixEquiv
      _ = Nat.card S.K ^ Module.finrank S.K L.ker :=
            Module.natCard_eq_pow_finrank (K := S.K) (V := L.ker)
  have hq : 1 < Nat.card S.K := by have := S.four_le; omega
  have hker3 : 2 < Module.finrank S.K L.ker := by
    have hpow : Nat.card S.K ^ 2 < Nat.card S.K ^ Module.finrank S.K L.ker :=
      calc Nat.card S.K ^ 2 < Nat.card {v : W // g v = v} := hfix
        _ = Nat.card S.K ^ Module.finrank S.K L.ker := hcard
    exact (Nat.pow_lt_pow_iff_right hq).mp hpow
  have hV : Module.finrank S.K (OmI → S.K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    decide
  have hrange1 : Module.finrank S.K L.range ≤ 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker L
    rw [hV] at hrn
    omega
  have hex : ∃ w₀ : W, g w₀ ≠ w₀ := by
    by_contra h
    apply hg1
    ext w
    simpa using not_not.mp (not_exists.mp h w)
  obtain ⟨w₀, hw0ne⟩ := hex
  let e : W := g w₀ * w₀⁻¹
  have he1 : e ≠ 1 := fun h => hw0ne (mul_inv_eq_one.mp h)
  let u : OmI → S.K := S.vec e
  have hu_ne : u ≠ 0 := by
    intro h
    apply he1
    apply S.vec_injective
    rw [S.vec_one]
    exact h
  have hu_mem : u ∈ L.range := ⟨S.vec w₀, hLw w₀⟩
  have h1r : 1 ≤ Module.finrank S.K L.range := by
    rw [← finrank_span_singleton (K := S.K) hu_ne]
    exact Submodule.finrank_mono
      ((Submodule.span_singleton_le_iff_mem u L.range).mpr hu_mem)
  have hk1 : Module.finrank S.K L.range = 1 := by omega
  have hspan : L.range = S.K ∙ u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hk1 hu_mem hu_ne
  have hline : ∀ w : W, ∃ a : S.K, g w * w⁻¹ = S.smul a e := by
    intro w
    have hx : L (S.vec w) ∈ S.K ∙ u := by
      rw [← hspan]
      exact LinearMap.mem_range_self L (S.vec w)
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    apply S.vec_injective
    rw [← hLw w, ← ha, S.vec_smul]
  have hQ : S.Q e ≠ 0 := by
    intro hQ0
    have hbad := S.card_fixed_le_of_isometry hlin hiso (w := w₀) he1 hQ0
    exact absurd hbad (not_le.2 hfix)
  exact ⟨e, hQ, ⟨w₀, rfl⟩, hline⟩

theorem apply_eq_of_commute {g h : MulAut W}
    (hh : ∀ (c : S.K) (w : W), h (S.smul c w) = S.smul c (h w)) (hh2 : h * h = 1)
    (hgh : g * h = h * g) {e : W} (he1 : e ≠ 1)
    (hline : ∀ w : W, ∃ a : S.K, g w * w⁻¹ = S.smul a e) {w₀ : W} (hw₀ : g w₀ * w₀⁻¹ = e) :
    h e = e := by
  obtain ⟨a, ha⟩ := hline (h w₀)
  have hcomm : h (g w₀) = g (h w₀) := by
    have h1 := congrArg (fun f : MulAut W => f w₀) hgh
    simpa [MulAut.mul_apply] using h1.symm
  have hhe : h e = S.smul a e := by
    calc h e = h (g w₀ * w₀⁻¹) := by rw [← hw₀]
      _ = h (g w₀) * (h w₀)⁻¹ := by rw [map_mul, map_inv]
      _ = g (h w₀) * (h w₀)⁻¹ := by rw [hcomm]
      _ = S.smul a e := ha
  have hsq : S.smul (a * a) e = e := by
    calc S.smul (a * a) e = S.smul a (S.smul a e) := (S.smul_smul_eq a a e).symm
      _ = S.smul a (h e) := by rw [hhe]
      _ = h (S.smul a e) := (hh a e).symm
      _ = h (h e) := by rw [hhe]
      _ = (h * h) e := by rw [MulAut.mul_apply]
      _ = e := by rw [hh2, MulAut.one_apply]
  have hcoef : a * a = 1 := by
    have hvec_ne : S.vec e ≠ 0 := by
      intro h0
      apply he1
      apply S.vec_injective
      rw [S.vec_one]
      exact h0
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hvec_ne
    have hi' : S.vec e i ≠ 0 := hi
    have h1 : S.smul (a * a) e = S.smul 1 e := by rw [hsq, S.smul_one_eq]
    have h1' : (a * a) • S.vec e = (1 : S.K) • S.vec e := by
      have := congrArg S.vec h1
      rwa [S.vec_smul, S.vec_smul] at this
    have h2 : (a * a) * S.vec e i = 1 * S.vec e i := by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun h1' i
    exact mul_right_cancel₀ hi' h2
  have ha1 : a = 1 := by
    have hsq2 : a ^ 2 = 1 ^ 2 := by rw [pow_two, hcoef, one_pow]
    exact CharTwo.sq_inj.mp hsq2
  rw [hhe, ha1, S.smul_one_eq]

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
