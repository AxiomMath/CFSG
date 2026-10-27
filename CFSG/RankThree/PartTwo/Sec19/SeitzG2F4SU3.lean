module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.RankThree.PartOne.SEITZQ1.Plane
public import CFSG.RankThree.PartOne.SEITZ3.PlaneCount

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.SEITZQ1

variable {f : ℕ} {K' : Type} [Field K']


variable {f : ℕ} {K' : Type} [Field K']

theorem su3_cube_root_cases {ω : K'} (hω : ω ^ 2 + ω + 1 = 0) {u : K'} (hu : u ^ 3 = 1) :
    u = 1 ∨ u = ω ∨ u = ω ^ 2 := by
  have h : (u - 1) * (u - ω) * (u - ω ^ 2) = 0 := by
    linear_combination hu + (-(ω - 1) - u ^ 2 + u * ω) * hω
  rcases mul_eq_zero.1 h with h1 | h3
  · rcases mul_eq_zero.1 h1 with h1 | h2
    · exact Or.inl (sub_eq_zero.1 h1)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h3))

theorem su3_mem_zpowers_of_cube {ω : K'ˣ} (hω : (ω : K') ^ 2 + (ω : K') + 1 = 0) {u : K'ˣ}
    (hu : u ^ 3 = 1) : u ∈ Subgroup.zpowers ω := by
  have hu' : (u : K') ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  rcases su3_cube_root_cases hω hu' with h | h | h
  · have : u = 1 := Units.ext h
    rw [this]; exact Subgroup.one_mem _
  · have : u = ω := Units.ext h
    rw [this]; exact Subgroup.mem_zpowers ω
  · have : u = ω ^ 2 := Units.ext (by rw [h, Units.val_pow_eq_pow_val])
    rw [this]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers ω) 2

@[expose] noncomputable def su3DiagPlane (ω : K'ˣ) : Subgroup (GL (Fin 3) K') :=
  ((Subgroup.zpowers ω).prod (Subgroup.zpowers ω)).map q1DiagTorus

theorem card_su3DiagPlane {ω : K'ˣ} (hω : orderOf ω = 3) : Nat.card (su3DiagPlane ω) = 9 := by
  rw [su3DiagPlane, Subgroup.card_map_of_injective q1DiagTorus_injective,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers, hω]


theorem mem_su3DiagPlane_of_diag {ω : K'ˣ} (hω : (ω : K') ^ 2 + (ω : K') + 1 = 0)
    {x : GL (Fin 3) K'} (hd : ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').IsDiag)
    (hdet : ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').det = 1) (hx3 : x ^ 3 = 1) :
    x ∈ su3DiagPlane ω := by
  set M : Matrix (Fin 3) (Fin 3) K' := ((x : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') with hM
  have hMd : M = Matrix.diagonal (fun i => M i i) := hd.diagonal_diag.symm
  have hprod : M 0 0 * M 1 1 * M 2 2 = 1 := by
    have := hdet
    rw [hMd, Matrix.det_diagonal, Fin.prod_univ_three] at this
    simpa using this
  have hnz0 : M 0 0 ≠ 0 := fun h => by rw [h] at hprod; simp at hprod
  have hnz1 : M 1 1 ≠ 0 := fun h => by rw [h] at hprod; simp at hprod
  have hnz2 : M 2 2 ≠ 0 := fun h => by rw [h] at hprod; simp at hprod
  have hcube : ∀ i, (M i i) ^ 3 = 1 := by
    intro i
    have h3 : M ^ 3 = 1 := by
      have := congrArg (fun g : GL (Fin 3) K' => (g : Matrix (Fin 3) (Fin 3) K')) hx3
      simpa using this
    rw [hMd, Matrix.diagonal_pow] at h3
    have := congrFun (congrFun h3 i) i
    simpa using this
  set a0 : K'ˣ := Units.mk0 (M 0 0) hnz0 with ha0
  set a2 : K'ˣ := Units.mk0 (M 2 2) hnz2 with ha2
  have ha0c : a0 ^ 3 = 1 := Units.ext (by simpa [ha0] using hcube 0)
  have ha2c : a2 ^ 3 = 1 := Units.ext (by simpa [ha2] using hcube 2)
  have hs : a0 ∈ Subgroup.zpowers ω := su3_mem_zpowers_of_cube hω ha0c
  have ht : a2⁻¹ ∈ Subgroup.zpowers ω :=
    su3_mem_zpowers_of_cube hω (by rw [inv_pow, ha2c, inv_one])
  refine ⟨(a0, a2⁻¹), ⟨hs, ht⟩, ?_⟩
  apply Units.ext
  rw [coe_q1DiagTorus]
  have e0 : (a0 : K') = M 0 0 := by simp [ha0]
  have e2 : ((a2⁻¹ : K'ˣ) : K') = (M 2 2)⁻¹ := by simp [ha2]
  have e1 : (M 0 0)⁻¹ * (M 2 2)⁻¹ = M 1 1 := by
    calc (M 0 0)⁻¹ * (M 2 2)⁻¹ = (M 0 0)⁻¹ * (M 2 2)⁻¹ * (M 0 0 * M 1 1 * M 2 2) := by
          rw [hprod, mul_one]
      _ = M 1 1 := by field_simp
  show Matrix.diagonal ![(a0 : K'), (a0 : K')⁻¹ * ((a2⁻¹ : K'ˣ) : K'),
    ((a2⁻¹ : K'ˣ) : K')⁻¹] = M
  rw [e0, e2, e1, inv_inv]
  conv_rhs => rw [hMd]
  congr 1
  funext i
  fin_cases i <;> rfl


theorem su3_isDiag_mul {A B : Matrix (Fin 3) (Fin 3) K'} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

theorem su3_diag_unitary (h : UnitaryFieldData 2 f K') (d : K'ˣ) (hbd : h.bar (d : K') * (d : K') = 1) :
    q1DiagGL ![d⁻¹, 1, 1] ∈ primeFormUnitary h (idGram K' 3) := by
  rw [mem_primeFormUnitary]
  have hmat : (q1DiagGL ![d⁻¹, 1, 1] : Matrix (Fin 3) (Fin 3) K') =
      Matrix.diagonal ![((d⁻¹ : K'ˣ) : K'), 1, 1] := by
    rw [coe_q1DiagGL]
    congr 1
    funext i
    fin_cases i <;> simp
  have hid : idGram K' 3 = 1 := by simp [idGram]
  rw [hid, Matrix.mul_one, hmat, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Units.val_inv_eq_inv_val, map_inv₀]
    have hd0 : (d : K') ≠ 0 := d.ne_zero
    field_simp
    exact hbd.symm
  · simp
  · simp


theorem exists_conj_to_su3DiagPlane (h : UnitaryFieldData 2 f K') {ω : K'ˣ}
    (hω : (ω : K') ^ 2 + (ω : K') + 1 = 0) (hpq : 3 ∣ 2 ^ f + 1)
    (S : Subgroup (unitarySU 2 f K' 3)) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hexp : ∀ x ∈ S, x ^ 3 = 1) :
    ∃ s : unitarySU 2 f K' 3, ∀ x ∈ S,
      ((s⁻¹ * x * s : unitarySU 2 f K' 3) : GL (Fin 3) K') ∈ su3DiagPlane ω := by
  classical
  have hle : unitarySU 2 f K' 3 ≤ primeFormUnitary h (idGram K' 3) :=
    KFU.unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K' 3)) := S.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hGexp : ∀ u ∈ G, u ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨P, hP⟩ := KFU.exists_unitary_conj_diag h Nat.prime_three hpq G hGcomm hGexp
  set Pg : GL (Fin 3) K' := (P : GL (Fin 3) K') with hPg
  have hPmem : Pg ∈ primeFormUnitary h (idGram K' 3) := P.2
  have hid : idGram K' 3 = 1 := by simp [idGram]
  set d : K'ˣ := Matrix.GeneralLinearGroup.det Pg with hd
  have hdv : ((d : K'ˣ) : K') = (Pg : Matrix (Fin 3) (Fin 3) K').det := rfl
  have hbd : h.bar (d : K') * (d : K') = 1 := by
    have h1 := (mem_primeFormUnitary).1 hPmem
    rw [hid, Matrix.mul_one] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
    have h3 : ((Pg : Matrix (Fin 3) (Fin 3) K').map h.bar).det = h.bar (Pg : Matrix (Fin 3) (Fin 3) K').det := by
      rw [RingHom.map_det]; rfl
    rw [h3] at h2
    rw [hdv]
    exact h2
  set δ : GL (Fin 3) K' := q1DiagGL ![d⁻¹, 1, 1] with hδ
  have hδmat : (δ : Matrix (Fin 3) (Fin 3) K') =
      Matrix.diagonal ![((d⁻¹ : K'ˣ) : K'), 1, 1] := by
    rw [hδ, coe_q1DiagGL]
    congr 1
    funext i
    fin_cases i <;> simp
  have hδmem : δ ∈ primeFormUnitary h (idGram K' 3) := su3_diag_unitary h d hbd
  have hδinv : δ⁻¹ = q1DiagGL ![d, 1, 1] := by
    rw [hδ, ← map_inv]
    congr 1
    funext i
    fin_cases i <;> simp
  have hs'mem : Pg * δ ∈ unitarySU 2 f K' 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hδmat, Matrix.det_diagonal, Fin.prod_univ_three, ← hdv]
      simp [Units.val_inv_eq_inv_val]
    · have := (mem_primeFormUnitary).1 (mul_mem hPmem hδmem)
      rwa [hid, Matrix.mul_one] at this
  set s : unitarySU 2 f K' 3 := ⟨Pg * δ, hs'mem⟩ with hs
  refine ⟨s, fun x hx => ?_⟩
  have hxP : ((Pg⁻¹ * (x : GL (Fin 3) K') * Pg : GL (Fin 3) K') :
      Matrix (Fin 3) (Fin 3) K').IsDiag := by
    have := hP (Subgroup.inclusion hle x) ⟨x, hx, rfl⟩
    simpa [hPg] using this
  have hconj : ((s⁻¹ * x * s : unitarySU 2 f K' 3) : GL (Fin 3) K') =
      δ⁻¹ * (Pg⁻¹ * (x : GL (Fin 3) K') * Pg) * δ := by
    simp [hs, mul_assoc]
  have hmemSU : ((s⁻¹ * x * s : unitarySU 2 f K' 3) : GL (Fin 3) K') ∈ unitarySU 2 f K' 3 :=
    SetLike.coe_mem _
  refine mem_su3DiagPlane_of_diag hω ?_ ((mem_unitarySU_iff h).1 hmemSU).1 ?_
  · rw [hconj, Units.val_mul, Units.val_mul]
    refine su3_isDiag_mul (su3_isDiag_mul ?_ hxP) ?_
    · rw [hδinv, coe_q1DiagGL]; exact Matrix.isDiag_diagonal _
    · rw [hδ, coe_q1DiagGL]; exact Matrix.isDiag_diagonal _
  · have h3 : (s⁻¹ * x * s : unitarySU 2 f K' 3) ^ 3 = 1 := by
      have e : (s⁻¹ * x * s : unitarySU 2 f K' 3) = s⁻¹ * x * s⁻¹⁻¹ := by rw [inv_inv]
      rw [e, conj_pow, hexp x hx]
      group
    have := congrArg (fun y : unitarySU 2 f K' 3 => (y : GL (Fin 3) K')) h3
    simpa using this


open CFSG.RankThree.PartOne.SEITZ3 in
theorem su3_cj_mul_cj {G : Type*} [Group G] (E : Subgroup G) (a b : G) :
    cj (cj E a) b = cj E (b * a) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj]
  simp [mul_assoc]

theorem su3DiagPlane_le_su (h : UnitaryFieldData 2 f K') {ω : K'ˣ} (hω3 : ω ^ 3 = 1)
    (hpq : 3 ∣ 2 ^ f + 1) : su3DiagPlane ω ≤ unitarySU 2 f K' 3 := by
  have hq : ∀ s ∈ Subgroup.zpowers ω, s ^ (2 ^ f + 1) = 1 := by
    intro s hs
    have h3 : s ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1
        ((orderOf_dvd_of_mem_zpowers hs).trans (orderOf_dvd_of_pow_eq_one hω3))
    obtain ⟨c, hc⟩ := hpq
    rw [hc, pow_mul, h3, one_pow]
  rintro _ ⟨u, hu, rfl⟩
  exact q1DiagTorus_mem_unitarySU h (Prod.ext (hq _ hu.1) (hq _ hu.2))

open CFSG.RankThree.PartOne.SEITZ3 in
theorem su3_planes_conj (h : UnitaryFieldData 2 f K') (hf : Odd f)
    (S S' : Subgroup (unitarySU 2 f K' 3)) (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hexp : ∀ x ∈ S, x ^ 3 = 1) (hSc : Nat.card S = 9)
    (hcomm' : ∀ x ∈ S', ∀ y ∈ S', x * y = y * x) (hexp' : ∀ x ∈ S', x ^ 3 = 1)
    (hSc' : Nat.card S' = 9) : ∃ s : unitarySU 2 f K' 3, cj S s = S' := by
  classical
  have hchar : CharP K' 2 := h.charP
  have hfin : Finite K' := h.finite
  obtain ⟨ω, hω, -⟩ := q1_exists_omega h hf
  have hω0 : ω ≠ 0 := fun h0 => by rw [h0] at hω; simp at hω
  set ωu : K'ˣ := Units.mk0 ω hω0 with hωu
  have hωu' : (ωu : K') ^ 2 + (ωu : K') + 1 = 0 := by simpa [hωu] using hω
  have hω3 : ωu ^ 3 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu, Units.val_mk0]
    linear_combination (ω - 1) * hω
  have hω1 : ωu ≠ 1 := by
    intro h1
    have h1' : ω = 1 := by simpa [hωu] using congrArg Units.val h1
    rw [h1'] at hω
    have h3 : (3 : K') = 0 := by linear_combination hω
    have h2 : (2 : K') = 0 := CharTwo.two_eq_zero
    have : (1 : K') = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  have hord : orderOf ωu = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hω3 hω1
  have hpq : 3 ∣ 2 ^ f + 1 := by simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hf
  have hle : su3DiagPlane ωu ≤ unitarySU 2 f K' 3 := su3DiagPlane_le_su h hω3 hpq
  set P3 : Subgroup (unitarySU 2 f K' 3) := (su3DiagPlane ωu).subgroupOf (unitarySU 2 f K' 3) with hP3
  have hP3c : Nat.card P3 = 9 := by
    rw [hP3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_su3DiagPlane hord]
  have key : ∀ T : Subgroup (unitarySU 2 f K' 3),
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) → (∀ x ∈ T, x ^ 3 = 1) → Nat.card T = 9 →
      ∃ s : unitarySU 2 f K' 3, cj P3 s = T := by
    intro T hc he hTc
    obtain ⟨s, hs⟩ := exists_conj_to_su3DiagPlane h hωu' hpq T hc he
    refine ⟨s, ?_⟩
    have hle' : T ≤ cj P3 s := fun x hx => by
      rw [mem_cj]
      exact Subgroup.mem_subgroupOf.2 (hs x hx)
    exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [card_cj, hP3c, hTc])).symm
  obtain ⟨s₁, hs₁⟩ := key S hcomm hexp hSc
  obtain ⟨s₂, hs₂⟩ := key S' hcomm' hexp' hSc'
  refine ⟨s₂ * s₁⁻¹, ?_⟩
  rw [← hs₂, ← hs₁, su3_cj_mul_cj]
  congr 1
  group


end CFSG.RankThree.PartTwo.Sec19
