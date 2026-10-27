module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ReducedAlgebra
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.StatedDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private lemma sA2_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ {a b : Matrix ι ι F}, a ∈ Algebra.adjoin F (Units.val '' S) →
      b ∈ Algebra.adjoin F (Units.val '' S) → a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι F)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι F) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (s : Matrix ι ι F)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin F (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm F hcommS
  intro a b ha hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin F (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin F (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma sA2_mem_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (x e : Matrix ι ι F) :
    x ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) ↔ ∃ a ∈ A, a * e = x := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨a, ha, hfa⟩
    exact ⟨a, (Subalgebra.mem_toSubmodule A).mp ha, by rwa [LinearMap.mulRight_apply] at hfa⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Subalgebra.mem_toSubmodule A).mpr ha, by rw [LinearMap.mulRight_apply]⟩

private lemma sA2_blockDegree_lt {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F))
    (hAcomm : ∀ {a b : Matrix ι ι F}, a ∈ A → b ∈ A → a * b = b * a)
    {e x : Matrix ι ι F} (hxA : x ∈ A)
    (hxidem : IsIdempotentElem x) (hxe : x * e = x) (hxne : x ≠ e) :
    blockDegree A x < blockDegree A e := by
  have hle : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F x) ≤
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    intro y hy
    rw [sA2_mem_block] at hy ⊢
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨a * x, Subalgebra.mul_mem A ha hxA, by rw [Matrix.mul_assoc, hxe]⟩
  have hne : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F x) ≠
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    intro hEq
    have he_in : e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
      rw [sA2_mem_block]
      exact ⟨1, Subalgebra.one_mem A, by rw [Matrix.one_mul]⟩
    rw [← hEq, sA2_mem_block] at he_in
    obtain ⟨a, ha, hae⟩ := he_in
    have hxe' : e - x = (a - 1) * x := by
      rw [Matrix.sub_mul, Matrix.one_mul, hae]
    have hzero : x * (e - x) = 0 := by
      rw [Matrix.mul_sub, hxe, hxidem.eq, sub_self]
    have hcommx : x * (a - 1) = (a - 1) * x :=
      hAcomm hxA (Subalgebra.sub_mem A ha (Subalgebra.one_mem A))
    have hcalc : x * (e - x) = e - x := by
      rw [hxe', ← Matrix.mul_assoc, hcommx, Matrix.mul_assoc, hxidem.eq]
    have hzero' : e - x = 0 := by rw [← hcalc, hzero]
    exact hxne (sub_eq_zero.mp hzero').symm
  change Module.finrank F ((Subalgebra.toSubmodule A).map (LinearMap.mulRight F x)) <
    Module.finrank F ((Subalgebra.toSubmodule A).map (LinearMap.mulRight F e))
  exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)

theorem exists_isPrimIdemIn_of_isPrimAdjIdemIn {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [Finite F] (σ : F →+* F) (hσ : ∀ x, σ (σ x) = x)
    {G : Matrix ι ι F} (hG : IsUnit G.det) (hGh : Matrix.transpose (G.map σ) = G)
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    {ε : Matrix ι ι F}
    (hε : IsPrimAdjIdemIn σ G (Algebra.adjoin F (Units.val '' S)) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e ∧ e * ε = e ∧
      (e = ε ∨ (e ≠ ε ∧ formAdj σ G e ≠ e ∧ ε = e + formAdj σ G e)) := by
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  have hAcomm : ∀ {a b : Matrix ι ι F}, a ∈ A → b ∈ A → a * b = b * a :=
    sA2_adjoin_comm hS
  let T : Set (Matrix ι ι F) :=
    {e | e ∈ A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧ e * ε = e}
  have hεT : ε ∈ T := ⟨hε.1, hε.2.1, hε.2.2.1, by rw [hε.2.1]⟩
  have hneT : (blockDegree A '' T).Nonempty := ⟨blockDegree A ε, ε, hεT, rfl⟩
  let m : ℕ := sInf (blockDegree A '' T)
  have hm : m ∈ blockDegree A '' T := Nat.sInf_mem hneT
  obtain ⟨e, heT, hedeg⟩ := hm
  have heA : e ∈ A := heT.1
  have heidem : IsIdempotentElem e := heT.2.1
  have hene : e ≠ 0 := heT.2.2.1
  have hee : e * ε = e := heT.2.2.2
  have hmin : ∀ e' ∈ T, m ≤ blockDegree A e' := fun e' he' => Nat.sInf_le ⟨e', he', rfl⟩
  have heprim : ∀ x ∈ A, IsIdempotentElem x → x * e = x → x = 0 ∨ x = e := by
    intro x hxA hxidem hxe
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      by_contra hxne
      have hxε : x * ε = x := by rw [← hxe, Matrix.mul_assoc, hee]
      have hxT : x ∈ T := ⟨hxA, hxidem, hx0, hxε⟩
      have hlt := sA2_blockDegree_lt A hAcomm hxA hxidem hxe hxne
      have hle : m ≤ blockDegree A x := hmin x hxT
      rw [hedeg] at hlt
      exact absurd hle (not_le.mpr hlt)
  have hstarA : ∀ {a : Matrix ι ι F}, a ∈ A → formAdj σ G a ∈ A :=
    fun ha => Geo.formAdj_mem_adjoin σ hG hSU ha
  have hstar_e_idem : IsIdempotentElem (formAdj σ G e) := by
    show formAdj σ G e * formAdj σ G e = formAdj σ G e
    rw [← Geo.formAdj_mul σ hG e e, heidem.eq]
  have hstar_eps : formAdj σ G ε = ε := hε.2.2.2.1
  have hεe : ε * e = e := by rw [hAcomm hε.1 heA, hee]
  have hstar_e_eps : formAdj σ G e * ε = formAdj σ G e := by
    have h1 : formAdj σ G (ε * e) = formAdj σ G e := by rw [hεe]
    rw [Geo.formAdj_mul σ hG ε e, hstar_eps] at h1
    exact h1
  have he_star_comm : e * formAdj σ G e = formAdj σ G e * e := hAcomm heA (hstarA heA)
  refine ⟨e, ⟨heA, heidem, hene, heprim⟩, hee, ?_⟩
  by_cases hfix : formAdj σ G e = e
  · refine Or.inl ?_
    rcases hε.2.2.2.2 e heA heidem hfix hee with h | h
    · exact absurd h hene
    · exact h
  · have hxzero : e * formAdj σ G e = 0 := by
      by_cases hx0 : e * formAdj σ G e = 0
      · exact hx0
      · exfalso
        have hxidem : IsIdempotentElem (e * formAdj σ G e) :=
          IsIdempotentElem.mul_of_commute he_star_comm heidem hstar_e_idem
        have hxe : (e * formAdj σ G e) * e = e * formAdj σ G e := by
          rw [Matrix.mul_assoc, ← he_star_comm, ← Matrix.mul_assoc, heidem.eq]
        rcases heprim (e * formAdj σ G e) (Subalgebra.mul_mem A heA (hstarA heA)) hxidem hxe
          with h | h
        · exact hx0 h
        · apply hfix
          have hxe' : e * formAdj σ G e = e := h
          calc formAdj σ G e = formAdj σ G (e * formAdj σ G e) := by rw [hxe']
            _ = formAdj σ G (formAdj σ G e) * formAdj σ G e :=
                Geo.formAdj_mul σ hG e (formAdj σ G e)
            _ = e * formAdj σ G e := by rw [Geo.formAdj_formAdj σ hσ hG hGh e]
            _ = e := hxe'
    have hε'idem : IsIdempotentElem (e + formAdj σ G e) := by
      refine IsIdempotentElem.add heidem hstar_e_idem ?_
      rw [hxzero, ← he_star_comm, hxzero, add_zero]
    have hstar_ε' : formAdj σ G (e + formAdj σ G e) = e + formAdj σ G e := by
      rw [Geo.formAdj_add, Geo.formAdj_formAdj σ hσ hG hGh e, add_comm]
    have hε'ε : (e + formAdj σ G e) * ε = e + formAdj σ G e := by
      rw [Matrix.add_mul, hee, hstar_e_eps]
    have hε'A : e + formAdj σ G e ∈ A := Subalgebra.add_mem A heA (hstarA heA)
    have hε'e : (e + formAdj σ G e) * e = e := by
      rw [Matrix.add_mul, heidem.eq, ← he_star_comm, hxzero, add_zero]
    have hε'ne : e + formAdj σ G e ≠ 0 := by
      intro h0
      rw [h0, Matrix.zero_mul] at hε'e
      exact hene hε'e.symm
    have hε'eq : e + formAdj σ G e = ε := by
      rcases hε.2.2.2.2 (e + formAdj σ G e) hε'A hε'idem hstar_ε' hε'ε with h | h
      · exact absurd h hε'ne
      · exact h
    refine Or.inr ⟨?_, hfix, hε'eq.symm⟩
    intro h
    exact hfix (by rw [h, hstar_eps])

private lemma sA2_psp_eq_J {n f : ℕ} :
    Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0
      = Matrix.J (Fin n) (GaloisField 2 f) := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [CharTwo.neg_eq]
    · simp [h]
  rw [Matrix.J, Matrix.fromBlocks_inj]
  exact ⟨rfl, hneg.symm, hneg, rfl⟩

private lemma sA2_psp_isUnit {n f : ℕ} :
    IsUnit (Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0).det := by
  rw [sA2_psp_eq_J]
  exact Matrix.isUnit_det_J (Fin n) (GaloisField 2 f)

private lemma sA2_psp_transpose {n f : ℕ} :
    Matrix.transpose ((Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0).map (RingHom.id (GaloisField 2 f)))
      = Matrix.fromBlocks (0 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (1 : Matrix (Fin n) (Fin n) (GaloisField 2 f))
      (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) 0 := by
  have hneg : (-1 : Matrix (Fin n) (Fin n) (GaloisField 2 f)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [CharTwo.neg_eq]
    · simp [h]
  rw [show (⇑(RingHom.id (GaloisField 2 f)) : GaloisField 2 f → GaloisField 2 f) = id
    from rfl, Matrix.map_id, sA2_psp_eq_J, Matrix.J, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, rfl⟩
  · rw [Matrix.transpose_one]
    exact hneg.symm
  · rw [Matrix.transpose_neg, Matrix.transpose_one]
    exact hneg

private lemma sA2_psu_transpose (n g : ℕ) :
    Matrix.transpose (((Unitary.antidiag n : Matrix (Fin n) (Fin n)
      (GaloisField 2 (2 * (g + 1)))).map
      (⇑(CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
        (g + 1)).toRingHom))) = Unitary.antidiag n := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.map_apply]
  have hanti : ∀ (a b : Fin n),
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) a b
      = if b = a.rev then 1 else 0 := fun a b => rfl
  rw [hanti j i, hanti i j]
  by_cases h : i = j.rev
  · have h2 : j = i.rev := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h2, map_one]
  · have h2 : j ≠ i.rev := by
      intro h2
      apply h
      rw [h2, Fin.rev_rev]
    rw [if_neg h, if_neg h2, map_zero]

private lemma sA2_psu_involutive (g : ℕ) :
    ∀ x : GaloisField 2 (2 * (g + 1)),
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
        (g + 1)).toRingHom
        ((CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2
          (g + 1)).toRingHom x) = x := by
  have hcard : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega), ← pow_mul]
    congr 1
    ring
  intro x
  exact CFSG.LieType.BorelTits.unitaryInvolution_involutive hcard x

private lemma sA2_gram_isUnit {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) :
    IsUnit (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).det := by
  have hEqB : Matrix.toLinearMap₂' F (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q))
      = QuadraticMap.polarBilin Q := by
    rw [show LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) from rfl]
    exact Matrix.toLinearMap₂'_toMatrix' _
  have hJnd : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).Nondegenerate := by
    refine ⟨Matrix.separatingLeft_def.mpr fun v hv => ?_,
      Matrix.separatingRight_def.mpr fun w hw => ?_⟩
    · apply hnd.1 v
      intro w
      have h := hv w
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)),
        hEqB] at h
    · apply hnd.2 w
      intro v
      have h := hw v
      rwa [← Matrix.toLinearMap₂'_apply' (M := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)),
        hEqB] at h
  exact isUnit_iff_ne_zero.mpr (Matrix.nondegenerate_iff_det_ne_zero.mp hJnd)

private lemma sA2_gram_transpose {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) :
    Matrix.transpose ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).map (RingHom.id F))
      = LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  rw [show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply]
  exact QuadraticMap.polar_comm Q (Pi.single j 1) (Pi.single i 1)

private lemma sA2_gram_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) {s : GL ι F}
    (hs : s ∈ (Spin.spinMatrix Q).range) :
    Matrix.transpose ((s : Matrix ι ι F).map (RingHom.id F)) *
      LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) * (s : Matrix ι ι F)
      = LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) := by
  obtain ⟨x, rfl⟩ := hs
  set G := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q) with hGdef
  have hEqB : Matrix.toBilin' G = QuadraticMap.polarBilin Q := by
    rw [hGdef, show LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)
      = LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) from rfl]
    exact Matrix.toBilin'_toMatrix' _
  have hcomp := Matrix.toBilin'_comp G (Spin.spinMatrix Q x : Matrix ι ι F)
    (Spin.spinMatrix Q x : Matrix ι ι F)
  have hEq : Matrix.toBilin' (Matrix.transpose (Spin.spinMatrix Q x : Matrix ι ι F) * G *
      (Spin.spinMatrix Q x : Matrix ι ι F)) = Matrix.toBilin' G := by
    rw [← hcomp]
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hEqB,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    simp only [Spin.spinMatrix_mulVec]
    exact Spin.polar_spinAction Q x v w
  have hmap : ((Spin.spinMatrix Q x : Matrix ι ι F)).map (⇑(RingHom.id F))
      = (Spin.spinMatrix Q x : Matrix ι ι F) := by
    rw [show (⇑(RingHom.id F) : F → F) = id from rfl, Matrix.map_id]
  rw [hmap]
  exact (Matrix.toBilin' (R₁ := F)).injective hEq

theorem exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSU (n g : ℕ)
    (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hSU : ∀ s ∈ S, Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * Unitary.antidiag n *
      (s : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = Unitary.antidiag n)
        (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (hε : IsPrimAdjIdemIn
    (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
    (Unitary.antidiag n) (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e ∧ e * ε = e
      ∧
      (e = ε ∨
        (e ≠ ε ∧ formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e ≠ e ∧ ε = e + formAdj
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) e)) := by
  have hσ := sA2_psu_involutive g
  have hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n)
      (GaloisField 2 (2 * (g + 1)))).det :=
    isUnit_iff_ne_zero.mpr (Unitary.det_antidiag_ne_zero n)
  have hGh := sA2_psu_transpose n g
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (CFSG.LieType.BorelTits.unitaryInvolution
    (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom hσ hG hGh hS ?_ hε
  intro s hs
  simpa [Unitary.conjTr] using hSU s hs

theorem exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSp (n f : ℕ)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e ∧ e * ε = e ∧
      (e = ε ∨
        (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e
        ≠ e ∧ ε = e + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e)) := by
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (fun x => rfl)
    sA2_psp_isUnit sA2_psp_transpose hS ?_ hε
  intro s hs
  have h := CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSU s hs)
  rwa [show (⇑(RingHom.id (GaloisField 2 f)) : GaloisField 2 f → GaloisField 2 f) = id
    from rfl, Matrix.map_id]

theorem exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus (k f : ℕ)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
    (LinearMap.toMatrix₂' (GaloisField 2 f)
    (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
    (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e ∧ e * ε = e ∧
      (e = ε ∨
        (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e ≠ e ∧ ε = e + formAdj
        (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e)) := by
  have hnd := Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (fun x => rfl)
    (sA2_gram_isUnit (Spin.quadPlus (k + 3) (GaloisField 2 f)) hnd)
    (sA2_gram_transpose (Spin.quadPlus (k + 3) (GaloisField 2 f))) hS ?_ hε
  intro s hs
  exact sA2_gram_isometry (Spin.quadPlus (k + 3) (GaloisField 2 f)) (hSU s hs)

theorem exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaMinus (n f : ℕ)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈
      (Spin.spinMatrix
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
      (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
      (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
      (QuadraticMap.polarBilin
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e ∧ e * ε = e ∧
      (e = ε ∨
        (e ≠ ε ∧ formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e ≠ e ∧ ε = e
        + formAdj (RingHom.id (GaloisField 2 f))
        (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin
        (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e)) := by
  have hnd := Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f)
    (minusCoeffs_irr 2 f)
  refine exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id (GaloisField 2 f)) (fun x => rfl)
    (sA2_gram_isUnit _ hnd) (sA2_gram_transpose _) hS ?_ hε
  intro s hs
  exact sA2_gram_isometry _ (hSU s hs)

end CFSG.StandardType.ClassicalPosition
