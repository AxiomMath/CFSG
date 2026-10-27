module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Mat

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_lift (g : projImage (slPi π 3 (p ^ f) K)) :
    ∃ A ∈ slPi π 3 (p ^ f) K, ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K) :=
  g.2

theorem exists_conj_of_mk_comm {A B : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk A * ProjGenLinGroup.mk B =
      ProjGenLinGroup.mk B * ProjGenLinGroup.mk A) :
    ∃ u : Kˣ, A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * B := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u⁻¹, ?_⟩
  have e : A * B = B * A * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by
    rw [← hu, mul_inv_cancel_right]
  rw [e, map_inv]
  calc B * A * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * A⁻¹ =
      B * (A * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ * A⁻¹) := by group
    _ = B * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by
        rw [← map_inv, scalar_mul_comm, mul_inv_cancel_right]
    _ = _ := by rw [← map_inv, scalar_mul_comm]

theorem exists_conj_of_comm {g h : projImage (slPi π 3 (p ^ f) K)} (hgh : g * h = h * g)
    {A B : GL (Fin 3) K} (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K))
    (hB : ProjGenLinGroup.mk B = (h : ProjGenLinGroup (Fin 3) K)) :
    ∃ u : Kˣ, A * B * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * B := by
  refine exists_conj_of_mk_comm ?_
  rw [hA, hB]
  exact congrArg Subtype.val hgh

theorem neg_one_mem_rootsOfUnity (hp2 : p ≠ 2) (hp : p.Prime) :
    (-1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  rw [mem_rootsOfUnity]
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have heven : Even (qSubPi π (p ^ f)) := by
    cases π
    · exact Odd.add_one hodd
    · exact Nat.Odd.sub_odd hodd odd_one
  exact heven.neg_one_pow

theorem mem_slPi_of_isTInv (hK : PiField π p f K) (hp2 : p ≠ 2) {t : GL (Fin 3) K}
    (ht : IsTInv t) : t ∈ slPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h1 : (1 : Kˣ) ∈ rootsOfUnity (qSubPi π (p ^ f)) K := one_mem _
  have hm := neg_one_mem_rootsOfUnity (π := π) (K := K) (f := f) hp2 hK.prime
  rw [mem_slPi_iff hπ]
  rcases ht with rfl | rfl | rfl
  · exact ⟨diagUnits_mem_glPi hK h1 hm hm, by
      rw [tOne, coe_diagUnits, det_diagonal, Fin.prod_univ_three]; simp⟩
  · exact ⟨diagUnits_mem_glPi hK hm h1 hm, by
      rw [tTwo, coe_diagUnits, det_diagonal, Fin.prod_univ_three]; simp⟩
  · exact ⟨diagUnits_mem_glPi hK hm hm h1, by
      rw [tThree, coe_diagUnits, det_diagonal, Fin.prod_univ_three]; simp⟩

@[expose] noncomputable def tM (hK : PiField π p f K) (hp2 : p ≠ 2) (t : GL (Fin 3) K)
    (ht : IsTInv t) : projImage (slPi π 3 (p ^ f) K) :=
  ⟨ProjGenLinGroup.mk t, t, mem_slPi_of_isTInv hK hp2 ht, rfl⟩

theorem coe_tM (hK : PiField π p f K) (hp2 : p ≠ 2) {t : GL (Fin 3) K} (ht : IsTInv t) :
    (tM hK hp2 t ht : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk t :=
  rfl

theorem isTInv_tOne : IsTInv (tOne K) := Or.inl rfl

theorem isTInv_tTwo : IsTInv (tTwo K) := Or.inr (Or.inl rfl)

theorem isTInv_tThree : IsTInv (tThree K) := Or.inr (Or.inr rfl)

@[expose] def IsTM (hK : PiField π p f K) (hp2 : p ≠ 2) (x : projImage (slPi π 3 (p ^ f) K)) :
    Prop :=
  x = tM hK hp2 _ isTInv_tOne ∨ x = tM hK hp2 _ isTInv_tTwo ∨ x = tM hK hp2 _ isTInv_tThree

theorem isTM_of_mk (hK : PiField π p f K) (hp2 : p ≠ 2) {x : projImage (slPi π 3 (p ^ f) K)}
    {t : GL (Fin 3) K} (ht : IsTInv t) (hx : (x : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk t) : IsTM hK hp2 x := by
  rcases ht with rfl | rfl | rfl
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr (Or.inl (Subtype.ext hx))
  · exact Or.inr (Or.inr (Subtype.ext hx))

theorem two_ne_zero_of_piField (hK : PiField π p f K) (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have hp : p.Prime := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  have := hK.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (cond π f (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, hK.card]
    cases π
    · change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    · rfl
  have : CharP K p := charP_of_card_eq_prime_pow hcard
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ1 in
theorem offDiag_of_comm_diagTau {A : GL (Fin 3) K} (hA : A * diagTau hτ = diagTau hτ * A) :
    ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hτ0 := tau_ne_zero hτ
  have hM1 : (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
      diagonal ![τ, τ ^ 2, 1] * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA
    simpa only [Units.val_mul, coe_diagTau_eq_diagonal] using this
  have hτ2 : τ ^ 2 ≠ τ := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hτ21 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by
          rw [show τ ^ 3 = τ * τ ^ 2 by ring, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hτ0),
            mul_one]
      _ = 1 := by rw [hτ, h, inv_one, mul_one]
  intro i j hij
  refine entry_eq_zero_of_commute_diagonal hM1 ?_
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem exists_scalar_of_pow_eq_one {g : projImage (slPi π 3 (p ^ f) K)} {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K)) {m : ℕ} (hg : g ^ m = 1) :
    ∃ w : Kˣ, A ^ m = GeneralLinearGroup.scalar (Fin 3) w := by
  have h1 : ProjGenLinGroup.mk (A ^ m) = 1 := by
    rw [map_pow, hA]
    exact congrArg Subtype.val hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, hw.symm⟩

include hτ1 in
theorem offDiag_of_comm_d_of_pow {dM g : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hgd : g * dM = dM * g) {n : ℕ} (hg : g ^ 2 ^ n = 1) {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K)) :
    ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨u, hu⟩ := exists_conj_of_comm hgd hA hdM.symm
  obtain ⟨w, hw⟩ := exists_scalar_of_pow_eq_one hA hg
  exact offDiag_of_comm_diagTau hτ hτ1 (commute_of_conj_diag_of_pow hτ hu hw)

theorem offDiag_of_comm_t (hK : PiField π p f K) (hp2 : p ≠ 2)
    {g : projImage (slPi π 3 (p ^ f) K)}
    (h1 : g * tM hK hp2 _ isTInv_tOne = tM hK hp2 _ isTInv_tOne * g)
    (h2 : g * tM hK hp2 _ isTInv_tTwo = tM hK hp2 _ isTInv_tTwo * g) {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K)) :
    ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  obtain ⟨u, hu⟩ := exists_conj_of_comm h1 hA (coe_tM hK hp2 isTInv_tOne).symm
  obtain ⟨v, hv⟩ := exists_conj_of_comm h2 hA (coe_tM hK hp2 isTInv_tTwo).symm
  have hu1 := eq_one_of_conj_involution tOne_sq det_tOne hu
  have hv1 := eq_one_of_conj_involution tTwo_sq det_tTwo hv
  rw [hu1, map_one, one_mul] at hu
  rw [hv1, map_one, one_mul] at hv
  refine offDiag_eq_zero_of_comm_t (two_ne_zero_of_piField hK hp2) ?_ ?_
  · calc A * tOne K = A * tOne K * A⁻¹ * A := by group
      _ = tOne K * A := by rw [hu]
  · calc A * tTwo K = A * tTwo K * A⁻¹ * A := by group
      _ = tTwo K * A := by rw [hv]

theorem comm_of_offDiag {g : projImage (slPi π 3 (p ^ f) K)} {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K))
    (hoff : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0)
    {x : projImage (slPi π 3 (p ^ f) K)} {a b c : Kˣ}
    (hx : (x : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagUnits a b c)) :
    g * x = x * g := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, hx, ← map_mul, ← map_mul,
    comm_diagUnits_of_offDiag hoff]

theorem comm_of_offDiag_offDiag {g h : projImage (slPi π 3 (p ^ f) K)} {A B : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K))
    (hB : ProjGenLinGroup.mk B = (h : ProjGenLinGroup (Fin 3) K))
    (hoffA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0)
    (hoffB : ∀ i j : Fin 3, i ≠ j → (B : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    g * h = h * g := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hA, ← hB, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, eq_diagonal_of_offDiag hoffA, eq_diagonal_of_offDiag hoffB,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isTM_of_offDiag (hK : PiField π p f K) (hp2 : p ≠ 2)
    {g : projImage (slPi π 3 (p ^ f) K)} (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) {A : GL (Fin 3) K}
    (hA : ProjGenLinGroup.mk A = (g : ProjGenLinGroup (Fin 3) K))
    (hoff : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) :
    IsTM hK hp2 g := by
  obtain ⟨w, hw⟩ := exists_scalar_of_pow_eq_one hA hg2
  rcases mk_eq_of_offDiag_of_sq hoff hw with h | h | h | h
  · exact absurd (Subtype.ext (hA.symm.trans h)) hg1
  · exact isTM_of_mk hK hp2 isTInv_tOne (hA.symm.trans h)
  · exact isTM_of_mk hK hp2 isTInv_tTwo (hA.symm.trans h)
  · exact isTM_of_mk hK hp2 isTInv_tThree (hA.symm.trans h)

include hτ1 in
theorem isTM_conj_of_comm_d (hK : PiField π p f K) (hp2 : p ≠ 2)
    {dM g : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hgd : g * dM = dM * g) {x : projImage (slPi π 3 (p ^ f) K)} (hx : IsTM hK hp2 x) :
    IsTM hK hp2 (g * x * g⁻¹) := by
  obtain ⟨A, -, hA⟩ := exists_lift g
  obtain ⟨u, hu⟩ := exists_conj_of_comm hgd hA hdM.symm
  have key : ∀ (t : GL (Fin 3) K) (ht : IsTInv t), x = tM hK hp2 t ht →
      IsTM hK hp2 (g * x * g⁻¹) := by
    intro t ht hxt
    refine isTM_of_mk hK hp2 (isTInv_conj_of_conj_diag hτ hτ1 hu ht) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hA, hxt, coe_tM, ← map_inv,
      ← map_mul, ← map_mul]
  rcases hx with h | h | h
  · exact key _ _ h
  · exact key _ _ h
  · exact key _ _ h

theorem tM_one_mul_tM_two (hK : PiField π p f K) (hp2 : p ≠ 2) :
    tM hK hp2 _ isTInv_tOne * tM hK hp2 _ isTInv_tTwo = tM hK hp2 _ isTInv_tThree :=
  Subtype.ext (by rw [Subgroup.coe_mul, coe_tM, coe_tM, coe_tM, ← map_mul, tOne_mul_tTwo])

theorem tM_sq (hK : PiField π p f K) (hp2 : p ≠ 2) {t : GL (Fin 3) K} (ht : IsTInv t) :
    tM hK hp2 t ht ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_tM, ← map_pow, OneMemClass.coe_one, ProjGenLinGroup.mk_eq_one]
  have : t ^ 2 = 1 := by
    rcases ht with rfl | rfl | rfl
    · exact tOne_sq
    · exact tTwo_sq
    · rw [← tOne_mul_tTwo, sq, show tOne K * tTwo K * (tOne K * tTwo K) =
        tOne K * (tTwo K * tOne K) * tTwo K by group, ← tOne_mul_tTwo_comm,
        show tOne K * (tOne K * tTwo K) * tTwo K = (tOne K * tOne K) * (tTwo K * tTwo K) by group,
        tOne_mul_tOne, tTwo_mul_tTwo, one_mul]
  rw [this]
  exact Subgroup.one_mem _

theorem tM_ne_one (hK : PiField π p f K) (hp2 : p ≠ 2) {t : GL (Fin 3) K} (ht : IsTInv t) :
    tM hK hp2 t ht ≠ 1 := by
  have h2 := two_ne_zero_of_piField hK hp2
  intro h
  have h' : ProjGenLinGroup.mk t = 1 := by
    have := congrArg Subtype.val h
    rwa [coe_tM] at this
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h'
  obtain ⟨u, hu⟩ := h'
  have hne : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  rcases ht with rfl | rfl | rfl
  · have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have e1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hu
    simp [tOne, coe_diagUnits] at e0 e1
    exact hne (by simpa using congrArg Units.val (e0.symm.trans e1))
  · have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have e1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hu
    simp [tTwo, coe_diagUnits] at e0 e1
    exact hne (by simpa using congrArg Units.val (e1.symm.trans e0))
  · have e0 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    have e2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 2 2) hu
    simp [tThree, coe_diagUnits] at e0 e2
    exact hne (by simpa using congrArg Units.val (e2.symm.trans e0))

theorem cM_conj_tM (hK : PiField π p f K) (hp2 : p ≠ 2) {cM : projImage (slPi π 3 (p ^ f) K)}
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)) :
    cM * tM hK hp2 _ isTInv_tOne * cM⁻¹ = tM hK hp2 _ isTInv_tTwo ∧
      cM * tM hK hp2 _ isTInv_tTwo * cM⁻¹ = tM hK hp2 _ isTInv_tThree ∧
      cM * tM hK hp2 _ isTInv_tThree * cM⁻¹ = tM hK hp2 _ isTInv_tOne := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcM, coe_tM, coe_tM, ← map_inv,
      ← map_mul, ← map_mul]
  · rw [cyc_conj_tOne]
  · rw [cyc_conj_tTwo]
  · rw [cyc_conj_tThree]

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7
