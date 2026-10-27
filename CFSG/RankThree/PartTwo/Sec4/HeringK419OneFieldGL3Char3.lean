module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldSL2
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldBlock

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open Matrix
open scoped _root_.Classical

theorem exists_injective_slTwo_of_fixed_vector {E : Type} [Field E] {P : Type} [Group P]
    (hs : IsSimpleGroup P) (hnc : ∃ a b : P, a * b ≠ b * a) (M : P →* Matrix (Fin 3) (Fin 3) E)
    (hM : Function.Injective M) (hcol : ∀ (p : P) (i : Fin 3), M p i 0 = if i = 0 then 1 else 0) :
    ∃ f : P →* SpecialLinearGroup (Fin 2) E, Function.Injective f := by
  have hperf := commutator_eq_top_of_simple_nonabelian hs hnc
  have h10 : ∀ p, M p 1 0 = 0 := fun p => by simpa using hcol p 1
  have h20 : ∀ p, M p 2 0 = 0 := fun p => by simpa using hcol p 2
  have h00 : ∀ p, M p 0 0 = 1 := fun p => by simpa using hcol p 0
  let S : P →* Matrix (Fin 2) (Fin 2) E :=
    { toFun := fun p => Matrix.of fun i j => M p i.succ j.succ
      map_one' := by
        ext i j
        simp [Matrix.one_apply, Fin.succ_inj]
      map_mul' := by
        intro p q
        ext i j
        have h : (M (p * q)) i.succ j.succ = ∑ k, M p i.succ k * M q k j.succ := by
          rw [map_mul, Matrix.mul_apply]
        rw [Fin.sum_univ_succ] at h
        have hi : M p i.succ 0 = 0 := by simpa using hcol p i.succ
        simp only [Matrix.of_apply, Matrix.mul_apply]
        rw [h, hi, zero_mul, zero_add] }
  have hSapply : ∀ p i j, S p i j = M p i.succ j.succ := fun p i j => rfl
  have hdet : ∀ p : P, (S p).det = 1 := by
    intro p
    have h0 := eq_one_of_perfect hperf
      ((Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) E →* E).comp S).toHomUnits p
    have h1 := congrArg Units.val h0
    simpa using h1
  let f : P →* SpecialLinearGroup (Fin 2) E :=
    { toFun := fun p => ⟨S p, hdet p⟩
      map_one' := by
        apply Subtype.ext
        change S 1 = 1
        rw [map_one]
      map_mul' := by
        intro p q
        apply Subtype.ext
        change S (p * q) = S p * S q
        rw [map_mul] }
  refine ⟨f, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact h
  · exfalso
    have hone : ∀ p, S p = 1 := fun p => by
      have : p ∈ f.ker := by rw [h]; exact Subgroup.mem_top p
      exact congrArg Subtype.val this
    have e11 : ∀ p, M p 1 1 = 1 := fun p => by
      have := congrFun (congrFun (hone p) 0) 0
      simpa [hSapply] using this
    have e12 : ∀ p, M p 1 2 = 0 := fun p => by
      have := congrFun (congrFun (hone p) 0) 1
      simpa [hSapply] using this
    have e21 : ∀ p, M p 2 1 = 0 := fun p => by
      have := congrFun (congrFun (hone p) 1) 0
      simpa [hSapply] using this
    have e22 : ∀ p, M p 2 2 = 1 := fun p => by
      have := congrFun (congrFun (hone p) 1) 1
      simpa [hSapply] using this
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    apply hM
    rw [map_mul, map_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, e11, e12, e21, e22] <;> ring

theorem exists_gl_first_column {E : Type} [Field E] (u : Fin 3 → E) (hu : u ≠ 0) :
    ∃ T : GL (Fin 3) E, ∀ i, (T : Matrix (Fin 3) (Fin 3) E) i 0 = u i := by
  by_cases h0 : u 0 = 0
  · by_cases h1 : u 1 = 0
    · have h2 : u 2 ≠ 0 := by
        intro h2
        apply hu
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      have hdet : (!![0, 1, 0; 0, 0, 1; u 2, 0, 0] : Matrix (Fin 3) (Fin 3) E).det ≠ 0 := by
        simp [Matrix.det_fin_three, h2]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, h0, h1]
    · have hdet : (!![0, 1, 0; u 1, 0, 0; u 2, 0, 1] : Matrix (Fin 3) (Fin 3) E).det ≠ 0 := by
        simp [Matrix.det_fin_three, h1]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, h0]
  · have hdet : (!![u 0, 0, 0; u 1, 1, 0; u 2, 0, 1] : Matrix (Fin 3) (Fin 3) E).det ≠ 0 := by
      simp [Matrix.det_fin_three, h0]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, fun i => ?_⟩
    fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem exists_fixed_vector_of_commute_nilpotent {E : Type} [Field E] {P : Type} [Group P]
    (hP : commutator P = ⊤) (ρ : P →* GL (Fin 3) E) (N : Matrix (Fin 3) (Fin 3) E)
    (hN3 : N ^ 3 = 0) (hN0 : N ≠ 0)
    (hcomm : ∀ p : P, ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * N =
      N * ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) :
    ∃ u : Fin 3 → E, u ≠ 0 ∧ ∀ p : P,
      ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u = u := by
  have hline : ∃ u : Fin 3 → E, u ≠ 0 ∧ ∀ p : P, ∃ c : E,
      ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u = c • u := by
    have hker : ∃ v : Fin 3 → E, v ≠ 0 ∧ N *ᵥ v = 0 := by
      by_contra hcon
      push Not at hcon
      have h0 : (Pi.single 0 1 : Fin 3 → E) ≠ 0 := by
        intro h
        have := congrFun h 0
        simp at this
      have h3 := hcon _ (hcon _ (hcon _ h0))
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_three', hN3, Matrix.zero_mulVec] at h3
      exact h3 rfl
    have hrange : ∃ w : Fin 3 → E, N *ᵥ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hN0
      ext i j
      have := congrFun (hcon (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    set f : (Fin 3 → E) →ₗ[E] (Fin 3 → E) := Matrix.mulVecLin N with hf
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at hrn
    have hk1 : 0 < Module.finrank E (LinearMap.ker f) := by
      obtain ⟨v, hv0, hv⟩ := hker
      exact Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨v, by simpa [hf] using hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    have hr1 : 0 < Module.finrank E (LinearMap.range f) := by
      obtain ⟨w, hw⟩ := hrange
      exact Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨N *ᵥ w, ⟨w, rfl⟩⟩, fun h => hw (congrArg Subtype.val h)⟩
    have key : ∀ W : Submodule E (Fin 3 → E), Module.finrank E W = 1 →
        (∀ p : P, ∀ w ∈ W, ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ w ∈ W) →
        ∃ u : Fin 3 → E, u ≠ 0 ∧ ∀ p : P, ∃ c : E,
          ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u = c • u := by
      intro W hW hinv
      obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hW
      refine ⟨v.1, fun h => hv0 (Subtype.ext h), fun p => ?_⟩
      obtain ⟨c, hc⟩ := hv ⟨_, hinv p v.1 v.2⟩
      exact ⟨c, (congrArg Subtype.val hc).symm⟩
    rcases (show Module.finrank E (LinearMap.ker f) = 1 ∨ Module.finrank E (LinearMap.range f) = 1
      by omega) with h1 | h1
    · refine key (LinearMap.ker f) h1 ?_
      intro p w hw
      rw [LinearMap.mem_ker, hf, Matrix.mulVecLin_apply] at hw ⊢
      rw [Matrix.mulVec_mulVec, ← hcomm p, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    · refine key (LinearMap.range f) h1 ?_
      intro p w hw
      obtain ⟨y, rfl⟩ := hw
      refine ⟨((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ y, ?_⟩
      rw [hf, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, hcomm p]
  obtain ⟨u, hu0, hu⟩ := hline
  choose c hc using hu
  have hcu : ∀ (p : P) (d : E), ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u = d • u →
      d = c p := fun p d h =>
    smul_left_injective E hu0 (by simpa using (h.symm.trans (hc p)))
  have hcne : ∀ p, c p ≠ 0 := by
    intro p h0
    have h1 := hc p
    rw [h0, zero_smul] at h1
    apply hu0
    have h2 : ((ρ p⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ
        (((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [h1, Matrix.mulVec_zero] at h2
    exact h2.symm
  let χ : P →* Eˣ :=
    { toFun := fun p => Units.mk0 (c p) (hcne p)
      map_one' := by
        apply Units.ext
        change c 1 = 1
        exact (hcu 1 1 (by rw [map_one, Units.val_one, Matrix.one_mulVec, one_smul])).symm
      map_mul' := by
        intro p q
        apply Units.ext
        change c (p * q) = c p * c q
        symm
        apply hcu (p * q)
        rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc q, Matrix.mulVec_smul, hc p,
          smul_smul, mul_comm] }
  refine ⟨u, hu0, fun p => ?_⟩
  have h1 := congrArg Units.val (eq_one_of_perfect hP χ p)
  have h2 : c p = 1 := h1
  rw [hc p, h2, one_smul]

section Engine


theorem not_isType419_of_commute_gl3_char3 {E : Type} [Field E] [Finite E] [CharP E 3]
    {P : Type} [Group P] (hP : commutator P = ⊤) (ρ : P →* GL (Fin 3) E)
    (hρ : Function.Injective ρ) {K : Type} [Group K]
    (hK : IsType419 K) (hs : IsSimpleGroup K) (hZ : Subgroup.center K = ⊥)
    (π : P →* K) (hπ : Function.Surjective π)
    (hker : ∀ p : P, π p = 1 →
      ∃ z : Eˣ, ρ p = Matrix.GeneralLinearGroup.scalar (Fin 3) z)
    (A : GL (Fin 3) E) (c : Eˣ)
    (hA3 : ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ^ 3 =
      (c : E) • (1 : Matrix (Fin 3) (Fin 3) E))
    (hAn : ∀ b : E, ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) ≠
      b • (1 : Matrix (Fin 3) (Fin 3) E))
    (hcomm : ∀ p : P, ρ p * A = A * ρ p) : False := by
  have hnc := Item419Res3.exists_noncommuting_isType419 hK hZ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : E, γ ^ 3 = (c : E) := by
    obtain ⟨γ, hγ⟩ := Finite.surjective_of_injective (frobenius_inj E 3) (c : E)
    exact ⟨γ, by simpa [frobenius_def] using hγ⟩
  set Am : Matrix (Fin 3) (Fin 3) E := ((A : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hAm
  set N : Matrix (Fin 3) (Fin 3) E := Am - γ • 1 with hN
  have hN3 : N ^ 3 = 0 := by
    have h1 : (Am - γ • (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 =
        Am ^ 3 - (γ • (1 : Matrix (Fin 3) (Fin 3) E)) ^ 3 :=
      sub_pow_char_of_commute 3 ((Commute.one_right Am).smul_right γ)
    rw [hN, h1, hA3, _root_.smul_pow, one_pow, hγ, sub_self]
  have hN0 : N ≠ 0 := by
    intro h0
    exact hAn γ (sub_eq_zero.mp h0)
  have hNcomm : ∀ p : P, ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * N =
      N * ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
    intro p
    have h1 : ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * Am =
        Am * ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) := by
      have := congrArg Units.val (hcomm p)
      simpa [Units.val_mul] using this
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  obtain ⟨u, hu0, hfix⟩ := exists_fixed_vector_of_commute_nilpotent hP ρ N hN3 hN0 hNcomm
  obtain ⟨T, hT⟩ := exists_gl_first_column u hu0
  let M : P →* Matrix (Fin 3) (Fin 3) E :=
    (Units.coeHom (Matrix (Fin 3) (Fin 3) E)).comp ((MulAut.conj T⁻¹).toMonoidHom.comp ρ)
  have hMp : ∀ p, M p = ((T⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *
      ((ρ p : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) * (T : Matrix (Fin 3) (Fin 3) E) := by
    intro p
    simp [M, MulAut.conj_apply]
  have hTe : (T : Matrix (Fin 3) (Fin 3) E) *ᵥ (Pi.single 0 1 : Fin 3 → E) = u := by
    ext i
    rw [Matrix.mulVec_single_one]
    exact hT i
  have hMe : ∀ p, M p *ᵥ (Pi.single 0 1 : Fin 3 → E) = Pi.single 0 1 := by
    intro p
    have hu' : ((T⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) *ᵥ u = Pi.single 0 1 := by
      rw [← hTe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hMp p, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTe, hfix p, hu']
  have hcol : ∀ (p : P) (i : Fin 3), M p i 0 = if i = 0 then 1 else 0 := by
    intro p i
    have := congrFun (hMe p) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  have hMinj : Function.Injective M := by
    intro p q h
    apply hρ
    exact (MulAut.conj T⁻¹).injective (Units.ext h)
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    obtain ⟨z, hz⟩ := hker p hp
    have hMz : M p = (z : E) • (1 : Matrix (Fin 3) (Fin 3) E) := by
      rw [hMp p, hz, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz1 : (z : E) = 1 := by
      have h1 := hcol p 0
      rw [hMz] at h1
      simpa using h1
    have hz1' : z = 1 := Units.ext (by simpa using hz1)
    rw [Subgroup.mem_bot]
    apply hρ
    rw [hz, hz1', map_one, map_one]
  let eKP : K ≃* P := (MulEquiv.ofBijective π ⟨hπinj, hπ⟩).symm
  let M' : K →* Matrix (Fin 3) (Fin 3) E := M.comp eKP.toMonoidHom
  have hM'inj : Function.Injective M' := fun k₁ k₂ h => eKP.injective (hMinj h)
  obtain ⟨f, hf⟩ := exists_injective_slTwo_of_fixed_vector hs hnc M' hM'inj
    (fun k i => hcol _ i)
  exact Item419Res3.not_isType419_of_injective_slTwo_field hK hs hZ f hf

end Engine

end CFSG.RankThree.PartTwo.Sec4.HeringOF
