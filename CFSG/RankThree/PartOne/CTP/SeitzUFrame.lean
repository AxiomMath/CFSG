module

public import CFSG.RankThree.PartOne.CTP.SeitzUToral

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag

section Roots

variable {F : Type*} [Field F] {n : ℕ}

theorem single_comm_diag_of_eq (d : Fin n → F) (i j : Fin n) (c : F) (h : d i = d j) :
    Matrix.single i j c * Matrix.diagonal d = Matrix.diagonal d * Matrix.single i j c := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [h, mul_comm]
  · simp [hab]

theorem rootMatrix_comm_diag_of_eq (σ : F ≃+* F) (d : Fin n → F) (i j : Fin n) (c : F)
    (h : d i = d j) (h' : d (Fin.rev j) = d (Fin.rev i)) :
    rootMatrix σ i j c * Matrix.diagonal d = Matrix.diagonal d * rootMatrix σ i j c := by
  rw [rootMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, single_comm_diag_of_eq d i j c h,
    single_comm_diag_of_eq d (Fin.rev j) (Fin.rev i) (σ c) h']

theorem longRootMatrix_comm_diag_of_eq (d : Fin n → F) (i : Fin n) (c : F)
    (h : d i = d (Fin.rev i)) :
    longRootMatrix i c * Matrix.diagonal d = Matrix.diagonal d * longRootMatrix i c := by
  rw [longRootMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    single_comm_diag_of_eq d i (Fin.rev i) c h]

theorem heisenbergMatrix_comm_diag_of_eq (σ : F ≃+* F) (d : Fin n → F) (i k : Fin n) (a b : F)
    (h1 : d i = d k) (h2 : d k = d (Fin.rev i)) :
    heisenbergMatrix σ i k a b * Matrix.diagonal d =
      Matrix.diagonal d * heisenbergMatrix σ i k a b := by
  have h3 : d i = d (Fin.rev i) := h1.trans h2
  simp only [heisenbergMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, single_comm_diag_of_eq d i k a h1,
    single_comm_diag_of_eq d k (Fin.rev i) (σ a) h2, single_comm_diag_of_eq d i (Fin.rev i) b h3]

end Roots

section Frame

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem closure_centralizers_unitarySU_of_frame [Finite K] [Fact ℓ.Prime] [CharP K ℓ]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1)
    (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n)) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (P : GL (Fin n) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = antidiag n)
    (hdiag : ∀ x ∈ E, (((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).IsDiag) :
    Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} = ⊤ := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  let ε : Su K ℓ f n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let Φ : SU σ n ≃* unitarySU ℓ f K n := (conjEquiv P hP).trans ε
  have hΦ : ∀ a : SU σ n, ((Φ a : unitarySU ℓ f K n) : GL (Fin n) K) =
      P * (a : GL (Fin n) K) * P⁻¹ := fun a => rfl
  let Dg : E → GL (Fin n) K := fun x =>
    P⁻¹ * (((x : unitarySU ℓ f K n)) : GL (Fin n) K) * P
  have hDg : ∀ x : E, ((Φ.symm (x : unitarySU ℓ f K n) : SU σ n) : GL (Fin n) K) = Dg x :=
    fun x => rfl
  have hdiagE : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag :=
    fun x => hdiag x x.2
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin n → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiagE x) c }
  have hD : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun c => χ c x) := fun x => ((hdiagE x).diagonal_diag).symm
  have hnz : ∀ (c : Fin n) (x : E), χ c x ≠ 0 := by
    intro c x
    have h1 : (((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((Dg x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiagE x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hχp : ∀ (c : Fin n) (x : E), (χ c x) ^ p = 1 := fun c x => by
    rw [← map_pow, hexpE, map_one]
  have hσχ : ∀ (c : Fin n) (x : E), σ (χ c x) = χ c x := by
    intro c x
    rw [hσdef, unitaryInvolution_apply]
    obtain ⟨k, hk⟩ := hpq
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hq : ℓ ^ f = 1 + p * k := by omega
    rw [hq, pow_add, pow_one, pow_mul, hχp, one_pow, mul_one]
  have hrel : ∀ (c : Fin n) (x : E), χ c x * χ (Fin.rev c) x = 1 := by
    intro c x
    have hmem := (Φ.symm (x : unitarySU ℓ f K n)).2.2
    rw [hDg, hD x] at hmem
    have h1 := congrFun (congrFun hmem c) (Fin.rev c)
    have hconj : conjTr σ (Matrix.diagonal (fun c => χ c x)) =
        Matrix.diagonal (fun c => σ (χ c x)) := by
      rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    rw [hconj, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [antidiag, Matrix.of_apply, ite_true, mul_one] at h1
    rw [hσχ] at h1
    exact h1
  have hmemS : ∀ (a : SU σ n) (x : E), x ≠ 1 →
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      Φ a ∈ Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} := by
    intro a x hx1 hcomm
    refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K n), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_⟩
    apply Subtype.ext
    have hYD : (a : GL (Fin n) K) * Dg x = Dg x * (a : GL (Fin n) K) := by
      apply Units.ext
      simpa only [Units.val_mul] using hcomm
    have hxeq : ((x : unitarySU ℓ f K n) : GL (Fin n) K) = P * Dg x * P⁻¹ := by
      simp [Dg, mul_assoc]
    show P * (a : GL (Fin n) K) * P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) =
      ((x : unitarySU ℓ f K n) : GL (Fin n) K) * (P * (a : GL (Fin n) K) * P⁻¹)
    rw [hxeq]
    calc P * (a : GL (Fin n) K) * P⁻¹ * (P * Dg x * P⁻¹)
        = P * ((a : GL (Fin n) K) * Dg x) * P⁻¹ := by group
      _ = P * (Dg x * (a : GL (Fin n) K)) * P⁻¹ := by rw [hYD]
      _ = P * Dg x * P⁻¹ * (P * (a : GL (Fin n) K) * P⁻¹) := by group
  have hrev : ∀ (i j : Fin n) (x : E), χ i x = χ j x → χ (Fin.rev j) x = χ (Fin.rev i) x := by
    intro i j x hij
    have h1 := hrel i x
    have h2 := hrel j x
    rw [hij] at h1
    exact mul_left_cancel₀ (hnz j x) (h2.trans h1.symm)
  have hR : Subgroup.comap Φ.toMonoidHom
      (Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}) = ⊤ := by
    refine eq_top_of_rootElements_le hσ.invol hσ.exists_traceZero hσ.trace_surj
      (fun x hx => hσ.exists_norm hx) hn _ ?_ ?_ ?_
    · intro i j hij hi hj hjr c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ j)
      refine hmemS _ x hx1 ?_
      rw [coe_rootHom, hD x]
      exact rootMatrix_comm_diag_of_eq σ (fun c => χ c x) i j _ hxeq (hrev i j x hxeq)
    · intro i hi c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ (Fin.rev i))
      refine hmemS _ x hx1 ?_
      rw [coe_longRootHom, hD x]
      exact longRootMatrix_comm_diag_of_eq (fun c => χ c x) i _ hxeq
    · intro i k hi hik hk g hg
      obtain ⟨a, b, -, hga⟩ := hg
      have hmid : ∀ x : E, χ k x = 1 := by
        intro x
        have hsq : (χ k x) ^ 2 = 1 := by
          have := hrel k x
          rw [hk] at this
          simpa [sq] using this
        obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
        have h3 : χ k x ^ p = χ k x := by
          rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
        rw [← h3]
        exact hχp k x
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ k)
      refine hmemS g x hx1 ?_
      have h1i : χ i x = 1 := hxeq.trans (hmid x)
      have hr : χ (Fin.rev i) x = 1 := by
        have := hrel i x
        rwa [h1i, one_mul] at this
      rw [hga, hD x]
      exact heisenbergMatrix_comm_diag_of_eq σ (fun c => χ c x) i k a b hxeq
        ((hmid x).trans hr.symm)
  refine eq_top_iff.2 fun y _ => ?_
  have hy : Φ.symm y ∈ Subgroup.comap Φ.toMonoidHom
      (Subgroup.closure {g : unitarySU ℓ f K n | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}) := by
    rw [hR]
    exact Subgroup.mem_top _
  simpa using hy

end Frame

end CFSG.RankThree.PartOne.CTP
