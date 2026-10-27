module

public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedPattern
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedTrace
public import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedNormal
import CFSG.RankThree.PartOne.KF.UnitaryDiag
import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4b
import CFSG.Assembly.Subnormal
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzBal2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KFU
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private lemma ggLieSU3Fixed_permGL_conj_diagonal {K : Type} [Field K] {d : ℕ}
    (σ : Equiv.Perm (Fin d)) (t : Fin d → K) :
    ((permGL σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t *
        (((permGL σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (t ∘ σ.symm) := by
  rw [coe_permGL, coe_permGL_inv]
  have h1 : (σ⁻¹.permMatrix K) * diagonal t =
      (diagonal t).submatrix (σ⁻¹ : Equiv.Perm (Fin d)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((diagonal t).submatrix (σ⁻¹ : Equiv.Perm (Fin d)) id) * σ.permMatrix K =
      ((diagonal t).submatrix (σ⁻¹ : Equiv.Perm (Fin d)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  ext k l
  simp only [Matrix.submatrix_apply, id_eq, Matrix.diagonal_apply, Function.comp_apply]
  by_cases hkl : k = l
  · subst hkl
    simp [Equiv.Perm.inv_def]
  · have hne : σ⁻¹ k ≠ σ.symm l := by
      intro h'
      apply hkl
      have : σ.symm k = σ.symm l := by rw [← Equiv.Perm.inv_def]; exact h'
      exact σ.symm.injective this
    simp [hkl, hne]

private lemma ggLieSU3Fixed_core_case_not_dvd {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (Jh : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) (hJperf : ⁅Jh, Jh⁆ = Jh)
    {z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} (hzJ : z ∈ Jh)
    (hzc : ∀ j ∈ Jh, z * j = j * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (h3 : ¬ 3 ∣ 2 ^ n + 1) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have hmain : ∀ m : ℕ, 3 ∣ (2 ^ m) ^ 2 - 1 := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        obtain ⟨c, hc⟩ := ih
        have hge : 1 ≤ (2 ^ m) ^ 2 :=
          Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero m (by norm_num)))
        have hpow : (2 ^ (m + 1)) ^ 2 = 4 * (2 ^ m) ^ 2 := by
          rw [pow_succ]; ring
        rw [hpow]
        exact ⟨4 * c + 1, by omega⟩
    exact hmain n
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hω : IsPrimitiveRoot ((u : Kˣ) : K) 3 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hu]
    exact IsPrimitiveRoot.orderOf u
  have hzGL3 : (z : GL (Fin 4) K) ^ 3 = 1 := by
    have h := congrArg (fun w : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) => (w : GL (Fin 4) K)) hz3
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
  have hzmat3 : ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hzGL3, Units.val_one]
  obtain ⟨T, δ, hT, _hδ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz2.exists_conj_diagonal_of_pow_eq_one
      hω ((z : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) hzmat3
  let A : Subgroup (GL (Fin 4) K) := Jh.map (Subgroup.subtype (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
  let H : Subgroup (GL (Fin 4) K) := A.map (MulAut.conj T).toMonoidHom
  have hA : ⁅A, A⁆ = A := by
    have h := Subgroup.map_commutator Jh Jh
      (Subgroup.subtype (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    rw [hJperf] at h
    exact h.symm
  have hHperf : ⁅H, H⁆ = H := by
    have h := Subgroup.map_commutator A A (MulAut.conj T).toMonoidHom
    rw [hA] at h
    exact h.symm
  let z' : GL (Fin 4) K := (MulAut.conj T) (z : GL (Fin 4) K)
  have hz'eq : z' = T * (z : GL (Fin 4) K) * T⁻¹ := MulAut.conj_apply T (z : GL (Fin 4) K)
  have hz'diag : ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag := by
    rw [hz'eq, Units.val_mul, Units.val_mul, hT]
    exact Matrix.isDiag_diagonal δ
  have hz'3 : z' ^ 3 = 1 := by
    change ((MulAut.conj T) (z : GL (Fin 4) K)) ^ 3 = 1
    rw [← map_pow, hzGL3, map_one]
  have hz'H : z' ∈ H :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzJ)
  have hHz : ∀ g ∈ H, g * z' = z' * g := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [Subgroup.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hjc : (j : GL (Fin 4) K) * (z : GL (Fin 4) K) =
        (z : GL (Fin 4) K) * (j : GL (Fin 4) K) := by
      have h := congrArg (fun w : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) => (w : GL (Fin 4) K))
        (hzc j hj)
      have h' : (z : GL (Fin 4) K) * (j : GL (Fin 4) K) =
          (j : GL (Fin 4) K) * (z : GL (Fin 4) K) := by
        simpa only [Subgroup.coe_mul] using h
      exact h'.symm
    change (MulAut.conj T) (j : GL (Fin 4) K) * (MulAut.conj T) (z : GL (Fin 4) K) =
      (MulAut.conj T) (z : GL (Fin 4) K) * (MulAut.conj T) (j : GL (Fin 4) K)
    rw [← map_mul, ← map_mul, hjc]
  have hHd : ∀ g ∈ H, g * (1 : GL (Fin 4) K) = (1 : GL (Fin 4) K) * g := fun g _ => by simp
  rcases ggLieSU3Fixed_diag_pattern hz'diag (by simpa using Matrix.isDiag_one) hz'3 H hHperf hz'H
      hHz hHd with hz'1 | ⟨k, β, α, hβ1, hzk, hrest⟩
  · have hz1' : (MulAut.conj T) (z : GL (Fin 4) K) = (MulAut.conj T) 1 := by
      rw [map_one]; exact hz'1
    have hzGL : (z : GL (Fin 4) K) = 1 := (MulAut.conj T).injective hz1'
    exact hz1 (Subtype.ext hzGL)
  ·
    have hpow : β ^ (2 ^ n + 1) = 1 := by
      refine ggLieSU3Fixed_pow_succ_of_conj_diag hK z.2 T k ?_ ?_ ?_
      · rw [← hz'eq]; exact hz'diag
      · rw [← hz'eq]; exact hzk
      · intro i hi; rw [← hz'eq]; exact (hrest i hi).1
    have hβ3 : β ^ 3 = 1 := by
      have hcube : ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hz'3, Units.val_one]
      have hdiag : ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          Matrix.diagonal (((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).diag) :=
        hz'diag.diagonal_diag.symm
      rw [hdiag, Matrix.diagonal_pow] at hcube
      obtain ⟨i, hik⟩ : ∃ i : Fin 4, i ≠ k := by
        by_cases hk0 : k = 0
        · exact ⟨1, by rw [hk0]; decide⟩
        · exact ⟨0, fun h => hk0 h.symm⟩
      have hii := congrFun (congrFun hcube i) i
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hii
      have hzi : ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i = β := (hrest i hik).1
      simpa [Matrix.diag, Pi.pow_apply, hzi] using hii
    have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
    have hdvd' : 3 ∣ 2 ^ n + 1 := by
      have h := orderOf_dvd_of_pow_eq_one hpow
      rwa [hord] at h
    exact h3 hdvd'

private lemma ggLieSU3Fixed_core_case_dvd {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (E : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    {d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (Jh : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hJsub : CFSG.Assembly.IsSubnormal Jh
      (Subgroup.centralizer ({d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))))
    (hJperf : ⁅Jh, Jh⁆ = Jh)
    {z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} (hzJ : z ∈ Jh)
    (hzc : ∀ j ∈ Jh, z * j = j * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzE : ∀ x ∈ E, z * x = x * z) (h3 : 3 ∣ 2 ^ n + 1) :
    ∃ t ∈ Jh, (∀ x ∈ E, t * x = x * t) ∧ ∃ u ∈ Jh, t * u ≠ u * t := by
  classical
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hSUeq : unitarySU 2 n K 4 = LargeEvenSUGroup (Fin 4) K (2 ^ n) := rfl
  let S : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := E ∪ {z}
  let G0 : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := Subgroup.closure S
  have hScomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | rfl
    · rcases hy with hyE | rfl
      · exact hEc x hxE y hyE
      · exact (hzE x hxE).symm
    · rcases hy with hyE | rfl
      · exact hzE y hyE
      · rfl
  have hSpow : ∀ x ∈ S, x ^ 3 = 1 := by
    intro x hx
    rcases hx with hxE | rfl
    · exact hE3 x hxE
    · exact hz3
  have hG0comm : ∀ x ∈ G0, ∀ y ∈ G0, x * y = y * x := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y = y * x)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · intro x y hx hy; exact hScomm x hx y hy
    · intro x hx; rw [one_mul, mul_one]
    · intro x hx; rw [mul_one, one_mul]
    · intro x y z hx hy hz hxz hyz
      calc (x * y) * z = x * (y * z) := by group
        _ = x * (z * y) := by rw [hyz]
        _ = (x * z) * y := by group
        _ = (z * x) * y := by rw [hxz]
        _ = z * (x * y) := by group
    · intro y z x hy hz hx hxy hxz
      calc x * (y * z) = (x * y) * z := by group
        _ = (y * x) * z := by rw [hxy]
        _ = y * (x * z) := by group
        _ = y * (z * x) := by rw [hxz]
        _ = (y * z) * x := by group
    · intro x y hx hy hxy
      calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * y) * x⁻¹ := by rw [← hxy]
        _ = y * x⁻¹ := by group
    · intro x y hx hy hxy
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [← hxy]
        _ = y⁻¹ * x := by group
  have hG0pow : ∀ x ∈ G0, x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy; exact hSpow y hy
    · exact one_pow 3
    · intro x y hx hy hx3 hy3
      have hxy : Commute x y := (commute_iff_eq x y).mpr (hG0comm x hx y hy)
      rw [hxy.mul_pow 3, hx3, hy3, one_mul]
    · intro x hx hx3
      rw [inv_pow, hx3, inv_one]
  have hSUle : LargeEvenSUGroup (Fin 4) K (2 ^ n) ≤ primeFormUnitary h (idGram K 4) :=
    unitarySU_le_primeFormUnitary (n := 4) h
  let G' : Subgroup (primeFormUnitary h (idGram K 4)) := G0.map (Subgroup.inclusion hSUle)
  have hG'comm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.mem_map] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hG0comm x0 hx0 y0 hy0]
  have hG'pow : ∀ x ∈ G', x ^ 3 = 1 := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    rw [← map_pow, hG0pow x0 hx0, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h Nat.prime_three h3 G' hG'comm hG'pow
  let c : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃*
      ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
    { toFun := fun g => ⟨(P : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (P : GL (Fin 4) K), by
        have hh := conj_mem_unitarySU h (inv_mem P.2) g.2
        rw [hSUeq] at hh
        simpa only [Subgroup.coe_inv, inv_inv] using hh⟩
      invFun := fun g => ⟨(P : GL (Fin 4) K) * (g : GL (Fin 4) K) * (P : GL (Fin 4) K)⁻¹, by
        have hh := conj_mem_unitarySU h P.2 g.2
        rw [hSUeq] at hh
        exact hh⟩
      left_inv := fun g => Subtype.ext (by
        show (P : GL (Fin 4) K) * ((P : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (P : GL (Fin 4) K)) *
          (P : GL (Fin 4) K)⁻¹ = (g : GL (Fin 4) K)
        group)
      right_inv := fun g => Subtype.ext (by
        show (P : GL (Fin 4) K)⁻¹ * ((P : GL (Fin 4) K) * (g : GL (Fin 4) K) * (P : GL (Fin 4) K)⁻¹) *
          (P : GL (Fin 4) K) = (g : GL (Fin 4) K)
        group)
      map_mul' := fun g g' => Subtype.ext (by
        show (P : GL (Fin 4) K)⁻¹ * ((g * g' : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) *
            (P : GL (Fin 4) K) =
          ((P : GL (Fin 4) K)⁻¹ * (g : GL (Fin 4) K) * (P : GL (Fin 4) K)) *
            ((P : GL (Fin 4) K)⁻¹ * (g' : GL (Fin 4) K) * (P : GL (Fin 4) K))
        rw [Subgroup.coe_mul]
        group) }
  have hcx_diag : ∀ x ∈ G0,
      (((c x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).IsDiag := by
    intro x hx
    have hx' : (⟨x, hSUle x.2⟩ : ↥(primeFormUnitary h (idGram K 4))) ∈ G' :=
      Subgroup.mem_map_of_mem (Subgroup.inclusion hSUle) hx
    have hdiag := hP (⟨x, hSUle x.2⟩ : ↥(primeFormUnitary h (idGram K 4))) hx'
    have hcoe : ((c x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) =
        (P : GL (Fin 4) K)⁻¹ * (x : GL (Fin 4) K) * (P : GL (Fin 4) K) := rfl
    rw [hcoe]
    simpa only [Units.val_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, inv_inv] using hdiag
  let z' : GL (Fin 4) K := (c z : GL (Fin 4) K)
  let dw : GL (Fin 4) K := (c d : GL (Fin 4) K)
  have hz'diag : ((z' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag :=
    hcx_diag z (Subgroup.subset_closure (Or.inr rfl))
  have hddiag : ((dw : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag :=
    hcx_diag d (Subgroup.subset_closure (Or.inl hdE))
  have hz'3 : z' ^ 3 = 1 := by
    have hcz3 : (c z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) ^ 3 = 1 := by
      rw [← map_pow, hz3, map_one]
    have hh := congrArg (fun w : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) => (w : GL (Fin 4) K)) hcz3
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hh
  let A : Subgroup (GL (Fin 4) K) :=
    (Jh.map c.toMonoidHom).map (Subgroup.subtype (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
  have hAperf : ⁅A, A⁆ = A := by
    have h1 : ⁅Jh.map c.toMonoidHom, Jh.map c.toMonoidHom⁆ = Jh.map c.toMonoidHom := by
      have hh := Subgroup.map_commutator Jh Jh c.toMonoidHom
      rw [hJperf] at hh
      exact hh.symm
    have hh := Subgroup.map_commutator (Jh.map c.toMonoidHom) (Jh.map c.toMonoidHom)
      (Subgroup.subtype (LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    rw [h1] at hh
    exact hh.symm
  have hz'A : z' ∈ A := Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzJ)
  have hHz : ∀ g ∈ A, g * z' = z' * g := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [Subgroup.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    change ((c j : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) *
        ((c z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) =
      ((c z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) *
        ((c j : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    rw [← map_mul, ← map_mul, hzc j hj]
  have hHdw : ∀ g ∈ A, g * dw = dw * g := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [Subgroup.mem_map] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hjd : j * d = d * j := Subgroup.mem_centralizer_singleton_iff.mp (hJsub.le hj)
    change ((c j : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) *
        ((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) =
      ((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) *
        ((c j : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    rw [← map_mul, ← map_mul, hjd]
  rcases ggLieSU3Fixed_diag_pattern hz'diag hddiag hz'3 A hAperf hz'A hHz hHdw with
    hz'1 | ⟨k, β, α, hβ1, hzk, hrest⟩
  · have hcz : c z = 1 := by
      apply Subtype.ext
      show (c z : GL (Fin 4) K) = 1
      exact hz'1
    exact absurd (c.injective (by rw [hcz, map_one])) hz1
  ·
    let σ : Equiv.Perm (Fin 4) := Equiv.swap k 3
    let wGL : GL (Fin 4) K := permGL σ
    have hwSU : wGL ∈ unitarySU 2 n K 4 := permGL_mem_unitarySU h σ
    let wSU : ↥(unitarySU 2 n K 4) := ⟨wGL, hwSU⟩
    let wPF : primeFormUnitary h (idGram K 4) := ⟨wSU, unitarySU_le_primeFormUnitary h wSU.2⟩
    let wconj : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃*
        ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) :=
      { toFun := fun g => ⟨wGL * (g : GL (Fin 4) K) * wGL⁻¹, by
          have hh := conj_mem_unitarySU h wPF.2 g.2
          rw [hSUeq] at hh
          exact hh⟩
        invFun := fun g => ⟨wGL⁻¹ * (g : GL (Fin 4) K) * wGL, by
          have hh := conj_mem_unitarySU h (inv_mem wPF.2) g.2
          rw [hSUeq] at hh
          simpa only [Subgroup.coe_inv, inv_inv] using hh⟩
        left_inv := fun g => Subtype.ext (by
          show wGL⁻¹ * (wGL * (g : GL (Fin 4) K) * wGL⁻¹) * wGL = (g : GL (Fin 4) K)
          group)
        right_inv := fun g => Subtype.ext (by
          show wGL * (wGL⁻¹ * (g : GL (Fin 4) K) * wGL) * wGL⁻¹ = (g : GL (Fin 4) K)
          group)
        map_mul' := fun g g' => Subtype.ext (by
          show wGL * ((g * g' : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) * wGL⁻¹ =
            (wGL * (g : GL (Fin 4) K) * wGL⁻¹) * (wGL * (g' : GL (Fin 4) K) * wGL⁻¹)
          rw [Subgroup.coe_mul]
          group) }
    let c' : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) ≃*
        ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := c.trans wconj
    set e : K := ((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) k k with he
    have hdwα : ∀ i, i ≠ k →
        (((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) i i = α := fun i hi => (hrest i hi).2
    have hcd'_coe : ((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) =
        wGL * ((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) * wGL⁻¹ := rfl
    have hcd'mat : (((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
        (wGL : Matrix (Fin 4) (Fin 4) K) * (((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) :
          GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (((wGL)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      rw [hcd'_coe, Units.val_mul, Units.val_mul]
    have hδfun : ((((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)).diag ∘ σ.symm = ![α, α, α, e] := by
      funext i
      fin_cases k <;> fin_cases i <;>
        simp [σ, he, hdwα, Equiv.swap_apply_def, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcd_form : (((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![α, α, α, e] := by
      rw [hcd'mat, ← hddiag.diagonal_diag, ggLieSU3Fixed_permGL_conj_diagonal σ
        (((c d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K).diag, hδfun]
    have hdet1 : ((((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)).det = 1 := by
      have hmem : ((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) ∈
          unitarySU 2 n K 4 := (c' d).2
      exact ((mem_unitarySU_iff h).mp hmem).1
    have hα3e : α ^ 3 * e = 1 := by
      rw [hcd_form, Matrix.det_diagonal, Fin.prod_univ_four] at hdet1
      have h' : α * α * α * e = 1 := by simpa using hdet1
      rwa [show α * α * α * e = α ^ 3 * e by ring] at h'
    have hα3 : α ^ 3 = 1 := by
      have hcube : ((((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) ^ 3 = 1 := by
        have hh : (c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) ^ 3 = 1 := by
          rw [← map_pow, hE3 d hdE, map_one]
        have hh' := congrArg (fun w : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) => (w : GL (Fin 4) K)) hh
        rw [Subgroup.coe_pow, Subgroup.coe_one] at hh'
        rw [← Units.val_pow_eq_pow_val, hh', Units.val_one]
      rw [hcd_form, Matrix.diagonal_pow] at hcube
      have hh := congrFun (congrFun hcube 0) 0
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hh
      simpa [Pi.pow_apply, Matrix.cons_val_zero] using hh
    have he1 : e = 1 := by
      rw [hα3, one_mul] at hα3e
      exact hα3e
    have hcd_final : (((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![α, α, α, 1] := by
      rw [hcd_form, he1]
    have hα1 : α ≠ 1 := by
      intro hα
      refine hd1 ?_
      have hmat : ((((c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) = 1 := by
        rw [hcd_final, hα]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hsu : (c' d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) = 1 := by
        apply Subtype.ext; apply Units.ext
        simpa using hmat
      exact c'.injective (by rw [hsu, map_one])
    let Jh' : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)) := Jh.map c'.toMonoidHom
    have hJh'perf : ⁅Jh', Jh'⁆ = Jh' := by
      have hh := Subgroup.map_commutator Jh Jh c'.toMonoidHom
      rw [hJperf] at hh
      exact hh.symm
    have hJh'1 : Jh' ≠ ⊥ := by
      intro hbot
      have hcz : c' z ∈ Jh' := Subgroup.mem_map_of_mem c'.toMonoidHom hzJ
      rw [hbot] at hcz
      have hcz1 : c' z = 1 := Subgroup.mem_bot.mp hcz
      exact hz1 (c'.injective (by rw [hcz1, map_one]))
    have hJh'sub : CFSG.Assembly.IsSubnormal Jh'
        (Subgroup.centralizer ({c' d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))) := by
      have hcent : Subgroup.map c'.toMonoidHom
            (Subgroup.centralizer ({d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))) =
          Subgroup.centralizer ({c' d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) := by
        ext x
        rw [Subgroup.mem_map]
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
          change c' y * c' d = c' d * c' y
          rw [← c'.map_mul, ← c'.map_mul, hy]
        · intro hx
          refine ⟨c'.symm x, ?_, by simp⟩
          rw [Subgroup.mem_centralizer_singleton_iff] at hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply c'.injective
          rw [c'.map_mul, c'.map_mul, MulEquiv.apply_symm_apply]
          exact hx
      rw [← hcent]
      exact hJsub.map c'.toMonoidHom
    obtain ⟨t'', ht''J, ht''diag, u'', hu''J, ht''u''⟩ :=
      ggLieSU3Fixed_normal hK hn h3 hα1 hcd_final Jh' hJh'sub hJh'perf hJh'1
    have hcx'diag : ∀ x ∈ E, ((((c' x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)).IsDiag := by
      intro x hxE
      have hxG0 : x ∈ G0 := Subgroup.subset_closure (Or.inl hxE)
      have hcx : ((((c x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)).IsDiag := hcx_diag x hxG0
      have hcoe : ((c' x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) =
          wGL * ((c x : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))) : GL (Fin 4) K) * wGL⁻¹ := rfl
      rw [hcoe, Units.val_mul, Units.val_mul, ← hcx.diagonal_diag,
        ggLieSU3Fixed_permGL_conj_diagonal]
      exact Matrix.isDiag_diagonal _
    have ht''commE : ∀ x ∈ E, t'' * (c' x) = (c' x) * t'' := by
      intro x hxE
      have hcx := hcx'diag x hxE
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
        ← ht''diag.diagonal_diag, ← hcx.diagonal_diag]
      exact (Matrix.commute_diagonal _ _).eq
    refine ⟨c'.symm t'', ?_, ?_, c'.symm u'', ?_, ?_⟩
    · change t'' ∈ Subgroup.map c'.toMonoidHom Jh at ht''J
      rw [Subgroup.mem_map] at ht''J
      obtain ⟨j, hj, hcj⟩ := ht''J
      have hres : c'.symm t'' = j := by
        rw [← hcj]
        exact MulEquiv.symm_apply_apply c' j
      rw [hres]; exact hj
    · intro x hxE
      have hh := congrArg c'.symm (ht''commE x hxE)
      simp only [map_mul, MulEquiv.symm_apply_apply] at hh
      exact hh
    · change u'' ∈ Subgroup.map c'.toMonoidHom Jh at hu''J
      rw [Subgroup.mem_map] at hu''J
      obtain ⟨j, hj, huj⟩ := hu''J
      have hres : c'.symm u'' = j := by
        rw [← huj]
        exact MulEquiv.symm_apply_apply c' j
      rw [hres]; exact hj
    · intro htu
      apply ht''u''
      have hh := congrArg c' htu
      simp only [map_mul, MulEquiv.apply_symm_apply] at hh
      exact hh

theorem ggLieSU3Fixed_core {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (E : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    {d : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} (hdE : d ∈ E) (hd1 : d ≠ 1)
    (Jh : Subgroup ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))
    (hJsub : CFSG.Assembly.IsSubnormal Jh
      (Subgroup.centralizer ({d} : Set ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n)))))
    (hJperf : ⁅Jh, Jh⁆ = Jh)
    {z : ↥(LargeEvenSUGroup (Fin 4) K (2 ^ n))} (hzJ : z ∈ Jh)
    (hzc : ∀ j ∈ Jh, z * j = j * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hzE : ∀ x ∈ E, z * x = x * z) :
    ∃ t ∈ Jh, (∀ x ∈ E, t * x = x * t) ∧ ∃ u ∈ Jh, t * u ≠ u * t := by
  by_cases h3 : 3 ∣ 2 ^ n + 1
  · exact ggLieSU3Fixed_core_case_dvd hK hn E hEc hE3 hdE hd1 Jh hJsub hJperf hzJ hzc hz3 hz1
      hzE h3
  · exact (ggLieSU3Fixed_core_case_not_dvd hK Jh hJperf hzJ hzc hz3 hz1 h3).elim

end CFSG.StandardType
