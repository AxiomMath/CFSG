module

public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut

open CFSG.GorensteinWalter CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem le_range_pglAction_of_isPGroup_two {F : Type*} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p ^ f) (hf : Odd f)
    {P : Subgroup (MulAut (PSL2 F))} (hP : IsPGroup 2 P) : P ≤ (pglAction F).range := by
  intro α hα
  apply mem_range_pglAction_of_rightHom_eq_one
  set x : F ≃+* F := SemidirectProduct.rightHom ((semilinearEquivAut F).symm α) with hxdef
  obtain ⟨k, hk⟩ := hP ⟨α, hα⟩
  have hαk : α ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : x ^ 2 ^ k = 1 := by
    rw [hxdef, ← map_pow, ← map_pow, hαk, map_one, map_one]
  have h3 : orderOf x ∣ f := by
    rw [← (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hF).1]
    exact orderOf_dvd_natCard x
  have h4 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hc : Nat.Coprime f (2 ^ k) := Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hf)
  have h5 : orderOf x ∣ 1 := by
    rw [← hc.gcd_eq_one]
    exact Nat.dvd_gcd h3 h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

section Action

variable {X : Type*} [Group X] {F : Type*} [Field F]

@[expose] noncomputable def pglToAut (ε : X ≃* PSL2 F) : PGL2 F →* MulAut X :=
  (MulAut.congr ε).symm.toMonoidHom.comp (pglAction F)

theorem pglToAut_injective [Finite F] (ε : X ≃* PSL2 F) : Function.Injective (pglToAut ε) :=
  (MulAut.congr ε).symm.injective.comp (pglAction_injective (K := F))

theorem toPGL_pglToAut_apply (ε : X ≃* PSL2 F) (g : PGL2 F) (x : X) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (ε (pglToAut ε g x)) =
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL (ε x) * g⁻¹ := by
  simp [pglToAut, MulAut.congr_symm_apply, toPGL_pglAction]

theorem pglToAut_toPGL (ε : X ≃* PSL2 F) (s : X) :
    pglToAut ε (Matrix.ProjectiveSpecialLinearGroup.toPGL (ε s)) = MulAut.conj s := by
  ext y
  simp [pglToAut, pglAction_toPGL, MulAut.congr_symm_apply]

theorem le_range_pglToAut_of_isPGroup_two [Finite F] {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ f) (hf : Odd f) (ε : X ≃* PSL2 F) {P : Subgroup (MulAut X)}
    (hP : IsPGroup 2 P) : P ≤ (pglToAut ε).range := by
  intro α hα
  have h1 := le_range_pglAction_of_isPGroup_two hp hF hf
    (hP.map (MulAut.congr ε).toMonoidHom) ⟨α, hα, rfl⟩
  obtain ⟨g, hg⟩ := h1
  refine ⟨g, ?_⟩
  change (MulAut.congr ε).symm (pglAction F g) = α
  rw [hg, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem isCyclic_of_isCyclic_comap [Finite F] (ε : X ≃* PSL2 F) {P : Subgroup (MulAut X)}
    (hP : P ≤ (pglToAut ε).range) (h : IsCyclic (P.comap (pglToAut ε))) : IsCyclic P := by
  let f : P.comap (pglToAut ε) →* P :=
    ((pglToAut ε).comp (P.comap (pglToAut ε)).subtype).codRestrict P (fun q => q.2)
  have hf : Function.Surjective f := by
    intro α
    obtain ⟨g, hg⟩ := hP α.2
    exact ⟨⟨g, by simpa [hg] using α.2⟩, Subtype.ext hg⟩
  exact isCyclic_of_surjective f hf

theorem comap_ne_bot [Finite F] (ε : X ≃* PSL2 F) {P : Subgroup (MulAut X)}
    (hP : P ≤ (pglToAut ε).range) (hP1 : P ≠ ⊥) : P.comap (pglToAut ε) ≠ ⊥ := by
  intro h
  apply hP1
  rw [← Subgroup.map_comap_eq_self hP, h, Subgroup.map_bot]

end Action

section GaloisFieldCube

variable (p : ℕ) [Fact p.Prime]

theorem card_galoisField_cube : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := by
  rw [GaloisField.card p (3 * 1) (by norm_num)]

theorem two_ne_zero_galoisField (hp : 5 ≤ p) (n : ℕ) : (2 : GaloisField p n) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : GaloisField p n) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField p n) p] at h'
  exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)

end GaloisFieldCube

end CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut
