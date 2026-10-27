module

public import CFSG.RankThree.PartOne.K1320.L4Torus

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eM_apply_fvec_of_ne {i j : Fin 4} (h : i ≠ j) (c : K) {l : Fin 4} (hl : l ≠ j) :
    ((eM h c : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) = fvec K l := by
  rw [apply_fvec, adSL_eM, Matrix.SpecialLinearGroup.transvection_coe]
  have hk : ∀ k : Fin 4, (1 + Matrix.single i j c : Matrix (Fin 4) (Fin 4) K) k l =
      if k = l then 1 else 0 := by
    intro k
    have hne : ¬(i = k ∧ j = l) := fun h2 => hl h2.2.symm
    simp [Matrix.one_apply, hne]
  simp [hk]

theorem fixes_of_mem_slB {i j : Fin 4} {g : ↥(M8 K)} (hg : g ∈ slB K i j) {k : Fin 4}
    (hki : k ≠ i) (hkj : k ≠ j) :
    (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K k) = fvec K k := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, c, rfl | rfl⟩ := hx
    · exact eM_apply_fvec_of_ne h c hkj
    · exact eM_apply_fvec_of_ne h.symm c hki
  | one => rfl
  | mul x y _ _ hx hy =>
    show (x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
      (fvec K k)) = _
    rw [hy, hx]
  | inv x _ hx =>
    have h1 : ((x⁻¹ * x : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K k) =
        ((x⁻¹ : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K k) := by
      show ((x⁻¹ : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))
        ((x : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K k)) = _
      rw [hx]
    rw [← h1, inv_mul_cancel]
    rfl

theorem diagHom_apply_fvec (v : Fin 3 → Kˣ) (l : Fin 4) :
    ((diagHom K v : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (fvec K l) =
      dvec v l • fvec K l := by
  rw [apply_fvec, adSL_diagHom, coe_diag4]
  simp [Matrix.diagonal_apply, ite_smul]

theorem eq_one_of_smul_fvec {c : K} {l : Fin 4} (h : c • fvec K l = fvec K l) : c = 1 := by
  have h0 : fvec K l ≠ 0 := by
    rw [← fbasis_apply]
    exact (fbasis K).ne_zero l
  by_contra hc
  apply h0
  have h1 : (c - 1) • fvec K l = 0 := by rw [sub_smul, one_smul, h, sub_self]
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact absurd (sub_eq_zero.1 h2) hc
  · exact h2

theorem dvec_eq_one_of_mem_slB {v : Fin 3 → Kˣ} {i j : Fin 4} (hg : diagHom K v ∈ slB K i j)
    {k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) : dvec v k = 1 :=
  eq_one_of_smul_fvec (by rw [← diagHom_apply_fvec]; exact fixes_of_mem_slB hg hki hkj)

theorem diagHom_mem_slB_zero_one_iff (v : Fin 3 → Kˣ) :
    diagHom K v ∈ slB K 0 1 ↔ v 2 = 1 ∧ v 0 * v 1 = 1 := by
  constructor
  · intro h
    have h2 := dvec_eq_one_of_mem_slB h (k := 2) (by decide) (by decide)
    have h3 := dvec_eq_one_of_mem_slB h (k := 3) (by decide) (by decide)
    have hv2 : v 2 = 1 := Units.ext h2
    refine ⟨hv2, ?_⟩
    rw [dvec_three] at h3
    have h4 : (v 0 * v 1 * v 2)⁻¹ = 1 := Units.ext h3
    rw [inv_eq_one, hv2, mul_one] at h4
    exact h4
  · rintro ⟨h2, h01⟩
    have hv : v = ![v 0, (v 0)⁻¹, 1] := by
      funext i
      fin_cases i
      · rfl
      · exact eq_inv_of_mul_eq_one_right h01
      · exact h2
    rw [hv]
    exact diagHom_mem_slB_zero_one _

theorem diagHom_mem_slB_two_three_iff (v : Fin 3 → Kˣ) :
    diagHom K v ∈ slB K 2 3 ↔ v 0 = 1 ∧ v 1 = 1 := by
  constructor
  · intro h
    exact ⟨Units.ext (dvec_eq_one_of_mem_slB h (k := 0) (by decide) (by decide)),
      Units.ext (dvec_eq_one_of_mem_slB h (k := 1) (by decide) (by decide))⟩
  · rintro ⟨h0, h1⟩
    have hv : v = ![1, 1, v 2] := by
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · rfl
    rw [hv]
    exact diagHom_mem_slB_two_three _

theorem diagHom_mem_slB_one_two_iff (v : Fin 3 → Kˣ) :
    diagHom K v ∈ slB K 1 2 ↔ v 0 = 1 ∧ v 1 * v 2 = 1 := by
  constructor
  · intro h
    have h0 := dvec_eq_one_of_mem_slB h (k := 0) (by decide) (by decide)
    have h3 := dvec_eq_one_of_mem_slB h (k := 3) (by decide) (by decide)
    have hv0 : v 0 = 1 := Units.ext h0
    refine ⟨hv0, ?_⟩
    rw [dvec_three] at h3
    have h4 : (v 0 * v 1 * v 2)⁻¹ = 1 := Units.ext h3
    rw [inv_eq_one, hv0, one_mul] at h4
    exact h4
  · rintro ⟨h0, h12⟩
    have hv : v = ![1, v 1, (v 1)⁻¹] := by
      funext i
      fin_cases i
      · exact h0
      · rfl
      · exact eq_inv_of_mul_eq_one_right h12
    rw [hv]
    exact diagHom_mem_slB_one_two _

theorem diagHom_mem_torusF_iff {r : ℕ} (v : Fin 3 → Kˣ) :
    diagHom K v ∈ torusF K r ↔ ∀ i, v i ^ r = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := mem_torusF_iff.1 h
    have hv : trIncl K r y = v := diagHom_injective hy
    intro i
    rw [← hv]
    exact (mem_rootsOfUnity r _).1 (y i).2
  · exact diagHom_mem_torusF v

@[expose] noncomputable def prod01 (K : Type) [Field K] (r : ℕ) :
    (Fin 3 → ↥(rootsOfUnity r K)) →* ↥(rootsOfUnity r K) :=
  Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) 0 *
    Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) 1

omit [Finite K] [CharP K 2] in
theorem prod01_apply (r : ℕ) (x : Fin 3 → ↥(rootsOfUnity r K)) : prod01 K r x = x 0 * x 1 := rfl

omit [Finite K] [CharP K 2] in
theorem prod01_surjective (r : ℕ) : Function.Surjective (prod01 K r) := fun z =>
  ⟨![z, 1, 1], by simp [prod01_apply]⟩

@[expose] noncomputable def psi01 (K : Type) [Field K] : (Fin 3 → Kˣ) →* Kˣ :=
  Pi.evalMonoidHom (fun _ => Kˣ) 0 * Pi.evalMonoidHom (fun _ => Kˣ) 1

theorem diagHom_mem_Pk_iff (v : Fin 3 → Kˣ) :
    diagHom K v ∈ (MonoidHom.ker (psi01 K)).map (diagHom K) ↔ v 0 * v 1 = 1 := by
  rw [Subgroup.mem_map_iff_mem diagHom_injective, MonoidHom.mem_ker]
  rfl

theorem diagHom_mem_P_iff {r : ℕ} (v : Fin 3 → Kˣ) :
    diagHom K v ∈ (torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3) ↔
      (∀ i, v i ^ r = 1) ∧ v 0 * v 1 = 1 := by
  constructor
  · intro h
    have hle : (torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3) ≤
        torusF K r ⊓ (MonoidHom.ker (psi01 K)).map (diagHom K) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨hF, hS⟩ := Subgroup.mem_inf.1 hg
        obtain ⟨y, rfl⟩ := mem_torusF_iff.1 hF
        exact Subgroup.mem_inf.2 ⟨hF, (diagHom_mem_Pk_iff _).2
          ((diagHom_mem_slB_zero_one_iff _).1 hS).2⟩
      · obtain ⟨hF, hS⟩ := Subgroup.mem_inf.1 hg
        obtain ⟨y, rfl⟩ := mem_torusF_iff.1 hF
        obtain ⟨h0, h1⟩ := (diagHom_mem_slB_two_three_iff _).1 hS
        exact Subgroup.mem_inf.2 ⟨hF, (diagHom_mem_Pk_iff _).2 (by rw [h0, h1, mul_one])⟩
    obtain ⟨hF, hP⟩ := Subgroup.mem_inf.1 (hle h)
    exact ⟨(diagHom_mem_torusF_iff v).1 hF, (diagHom_mem_Pk_iff v).1 hP⟩
  · rintro ⟨hv, h01⟩
    have e : v = ![v 0, v 1, 1] * ![1, 1, v 2] := by
      funext i
      fin_cases i <;> simp
    rw [e, map_mul]
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
      (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
    · refine (diagHom_mem_torusF_iff _).2 fun i => ?_
      fin_cases i
      · exact hv 0
      · exact hv 1
      · exact one_pow r
    · exact (diagHom_mem_slB_zero_one_iff _).2 ⟨rfl, h01⟩
    · refine (diagHom_mem_torusF_iff _).2 fun i => ?_
      fin_cases i
      · exact one_pow r
      · exact one_pow r
      · exact hv 2
    · exact (diagHom_mem_slB_two_three_iff _).2 ⟨rfl, rfl⟩

theorem P_le_torusF (r : ℕ) :
    (torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3) ≤ torusF K r :=
  sup_le inf_le_left inf_le_left

theorem torusF_mem_decomp {r : ℕ} (y : Fin 3 → ↥(rootsOfUnity r K)) :
    ∃ a u w : Kˣ, a ^ r = 1 ∧ u ^ r = 1 ∧ w ^ r = 1 ∧
      trIncl K r y = ![a, a, a⁻¹] * ![u, u⁻¹, 1] * ![1, 1, w] := by
  have hx : ∀ i, ((y i : rootsOfUnity r K) : Kˣ) ^ r = 1 := fun i =>
    (mem_rootsOfUnity r _).1 (y i).2
  set x0 : Kˣ := ((y 0 : rootsOfUnity r K) : Kˣ) with hx0
  set x1 : Kˣ := ((y 1 : rootsOfUnity r K) : Kˣ) with hx1
  set x2 : Kˣ := ((y 2 : rootsOfUnity r K) : Kˣ) with hx2
  obtain ⟨l, hl2, hlr⟩ := exists_sqrt_root (r := r) (w := x0 * x1)
    (by rw [mul_pow, hx 0, hx 1, one_mul])
  have hl2K : (l : K) * l = x0 * x1 := by
    have := congrArg Units.val hl2
    simpa [pow_two] using this
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hh00 : (x0 : K) ≠ 0 := x0.ne_zero
  refine ⟨l, x0 * l⁻¹, x2 * l, hlr, ?_, ?_, ?_⟩
  · rw [mul_pow, inv_pow, hx 0, hlr]
    simp
  · rw [mul_pow, hx 2, hlr, one_mul]
  · funext i
    apply Units.ext
    fin_cases i
    · show (x0 : K) = _
      simp
    · show (x1 : K) = _
      simp
      field_simp
      linear_combination -hl2K
    · show (x2 : K) = _
      simp

theorem torusF_decomp_three {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2) (hrq : r ∣ Nat.card K - 1) :
    torusF K r = ((torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3)) ⊔ Rr K r ∧
      ((torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3)).relIndex (torusF K r) = r := by
  refine ⟨le_antisymm ?_ (sup_le (P_le_torusF r) (Rr_le_torusF r)), ?_⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨a, u, w, ha, hu, hw, e⟩ := torusF_mem_decomp y
    show diagHom K (trIncl K r y) ∈ _
    rw [e, map_mul, map_mul, ← Tl_eq_diagHom]
    refine mul_mem (mul_mem (Subgroup.mem_sup_right ⟨a, (mem_rootsOfUnity r a).2 ha, rfl⟩)
      (Subgroup.mem_sup_left ((diagHom_mem_P_iff _).2 ⟨fun i => ?_, ?_⟩)))
      (Subgroup.mem_sup_left ((diagHom_mem_P_iff _).2 ⟨fun i => ?_, ?_⟩))
    · fin_cases i
      · exact hu
      · show (u⁻¹) ^ r = 1
        rw [inv_pow, hu, inv_one]
      · exact one_pow r
    · show u * u⁻¹ = 1
      exact mul_inv_cancel u
    · fin_cases i
      · exact one_pow r
      · exact one_pow r
      · exact hw
    · show (1 : Kˣ) * 1 = 1
      exact one_mul 1
  · have hP := P_le_torusF (K := K) r
    rw [← inf_eq_right.2 hP]
    have h := relIndex_torusF_of_ker (prod01 K r) (prod01_surjective r)
      ((torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3)) (fun y => ?_)
    · rw [h, natCard_rootsOfUnity_eq hr hrq]
    · rw [diagHom_mem_P_iff, prod01_apply, Subtype.ext_iff]
      refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
      exact (mem_rootsOfUnity r _).1 (y i).2

theorem relIndex_torusF_one_three {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) :
    ((torusF K r ⊓ Subgroup.centralizer (slB K 0 1 : Set ↥(M8 K))) ⊓
      ((torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3))).relIndex (torusF K r) = r ^ 2 := by
  let φ : (Fin 3 → ↥(rootsOfUnity r K)) →* ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K) :=
    (Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) 0).prod
      (Pi.evalMonoidHom (fun _ => ↥(rootsOfUnity r K)) 1)
  have hφ : Function.Surjective φ := fun z => ⟨![z.1, z.2, 1], by simp [φ]⟩
  rw [inf_assoc, relIndex_torusF_of_ker φ hφ _ (fun y => ?_), Nat.card_prod,
    natCard_rootsOfUnity_eq hr hrq, sq]
  rw [Subgroup.mem_inf, diagHom_mem_centralizer_slB_iff _ (by decide), diagHom_mem_P_iff]
  show _ ↔ ((y 0, y 1) : ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K)) = 1
  rw [Prod.mk_eq_one]
  constructor
  · rintro ⟨hc, -, h01⟩
    have h : ((y 0 : rootsOfUnity r K) : Kˣ) = (y 1 : rootsOfUnity r K) := Units.ext hc
    have h0 : ((y 0 : rootsOfUnity r K) : Kˣ) = 1 := by
      apply sq_units_eq_one
      rw [pow_two]
      nth_rewrite 2 [h]
      exact h01
    refine ⟨Subtype.ext h0, Subtype.ext ?_⟩
    rw [← h, h0]
    rfl
  · rintro ⟨h0, h1⟩
    have h0' : ((y 0 : rootsOfUnity r K) : Kˣ) = 1 := congrArg Subtype.val h0
    have h1' : ((y 1 : rootsOfUnity r K) : Kˣ) = 1 := congrArg Subtype.val h1
    refine ⟨?_, fun i => (mem_rootsOfUnity r _).1 (y i).2, ?_⟩
    · show (((y 0 : rootsOfUnity r K) : Kˣ) : K) = (((y 1 : rootsOfUnity r K) : Kˣ) : K)
      rw [h0', h1']
    · show ((y 0 : rootsOfUnity r K) : Kˣ) * (y 1 : rootsOfUnity r K) = 1
      rw [h0', h1', mul_one]

theorem relIndex_torusF_two_three {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) :
    ((torusF K r ⊓ Subgroup.centralizer (slB K 1 2 : Set ↥(M8 K))) ⊓
      ((torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3))).relIndex (torusF K r) = r ^ 2 := by
  let φ : (Fin 3 → ↥(rootsOfUnity r K)) →* ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K) :=
    ((Pi.evalMonoidHom (fun _ : Fin 3 => ↥(rootsOfUnity r K)) 1) /
      (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(rootsOfUnity r K)) 2)).prod (prod01 K r)
  have hφ : Function.Surjective φ := fun z =>
    ⟨![z.2 * z.1⁻¹, z.1, 1], by simp [φ, prod01_apply]⟩
  rw [inf_assoc, relIndex_torusF_of_ker φ hφ _ (fun y => ?_), Nat.card_prod,
    natCard_rootsOfUnity_eq hr hrq, sq]
  rw [Subgroup.mem_inf, diagHom_mem_centralizer_slB_iff _ (by decide), diagHom_mem_P_iff]
  show _ ↔ ((y 1 / y 2, y 0 * y 1) : ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K)) = 1
  rw [Prod.mk_eq_one, div_eq_one, Subtype.ext_iff, Subtype.ext_iff]
  constructor
  · rintro ⟨hc, -, h01⟩
    exact ⟨Units.ext hc, h01⟩
  · rintro ⟨h12, h01⟩
    refine ⟨?_, fun i => (mem_rootsOfUnity r _).1 (y i).2, h01⟩
    show (((y 1 : rootsOfUnity r K) : Kˣ) : K) = (((y 2 : rootsOfUnity r K) : Kˣ) : K)
    rw [h12]

theorem torusF_inf_slB_one_two_not_le {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) :
    ¬ (torusF K r ⊓ slB K 1 2 ≤ (torusF K r ⊓ slB K 0 1) ⊔ (torusF K r ⊓ slB K 2 3)) := by
  intro hle
  have hcard : 1 < Nat.card (rootsOfUnity r K) := by
    rw [natCard_rootsOfUnity_eq hr hrq]
    exact hr.one_lt
  have : Nontrivial (rootsOfUnity r K) := by
    have := Fintype.ofFinite (rootsOfUnity r K)
    rw [Nat.card_eq_fintype_card] at hcard
    exact Fintype.one_lt_card_iff_nontrivial.1 hcard
  obtain ⟨u, hu⟩ := exists_ne (1 : rootsOfUnity r K)
  have hmem : diagHom K ![1, (u : Kˣ), (u : Kˣ)⁻¹] ∈ torusF K r ⊓ slB K 1 2 := by
    refine Subgroup.mem_inf.2 ⟨(diagHom_mem_torusF_iff _).2 fun i => ?_,
      (diagHom_mem_slB_one_two_iff _).2 ⟨rfl, mul_inv_cancel _⟩⟩
    fin_cases i
    · exact one_pow r
    · exact (mem_rootsOfUnity r _).1 u.2
    · show ((u : Kˣ)⁻¹) ^ r = 1
      rw [inv_pow, (mem_rootsOfUnity r _).1 u.2, inv_one]
  have h := (diagHom_mem_P_iff _).1 (hle hmem)
  exact hu (Subtype.ext (by simpa using h.2))

theorem card_torusF_inf_slB_one_two {r : ℕ} (hr : r.Prime) (_hr2 : r ≠ 2)
    (hrq : r ∣ Nat.card K - 1) : Nat.card ↥(torusF K r ⊓ slB K 1 2) = r := by
  let φ : (Fin 3 → ↥(rootsOfUnity r K)) →* ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K) :=
    (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(rootsOfUnity r K)) 0).prod
      (Pi.evalMonoidHom (fun _ : Fin 3 => ↥(rootsOfUnity r K)) 1 *
        Pi.evalMonoidHom (fun _ : Fin 3 => ↥(rootsOfUnity r K)) 2)
  have hφ : Function.Surjective φ := fun z => ⟨![z.1, z.2, 1], by simp [φ]⟩
  have hinj : Function.Injective ((diagHom K).comp (trIncl K r)) :=
    diagHom_injective.comp (trIncl_injective r)
  have h1 : torusF K r ⊓ slB K 1 2 = (φ.ker).map ((diagHom K).comp (trIncl K r)) := by
    ext g
    constructor
    · rintro ⟨hg, hS⟩
      obtain ⟨y, rfl⟩ := mem_torusF_iff.1 hg
      obtain ⟨h0, h12⟩ := (diagHom_mem_slB_one_two_iff _).1 hS
      refine ⟨y, ?_, rfl⟩
      show φ y = 1
      exact Prod.ext (Subtype.ext h0) (Subtype.ext h12)
    · rintro ⟨y, hy, rfl⟩
      have hy' : ((y 0, y 1 * y 2) : ↥(rootsOfUnity r K) × ↥(rootsOfUnity r K)) = 1 := hy
      refine ⟨⟨y, rfl⟩, (diagHom_mem_slB_one_two_iff _).2 ⟨congrArg Subtype.val
        (Prod.mk_eq_one.1 hy').1, congrArg Subtype.val (Prod.mk_eq_one.1 hy').2⟩⟩
  have hTr : Nat.card (Fin 3 → ↥(rootsOfUnity r K)) = r ^ 3 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      natCard_rootsOfUnity_eq hr hrq]
  have h2 := Subgroup.card_ker_mul_card_of_surjective hφ
  rw [Nat.card_prod, natCard_rootsOfUnity_eq hr hrq, hTr] at h2
  rw [h1, Subgroup.card_map_of_injective hinj]
  have hr0 : 0 < r * r := Nat.mul_pos hr.pos hr.pos
  have h3 : Nat.card ↥φ.ker * (r * r) = r * (r * r) := by
    rw [h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hr0 h3

theorem Rr_inf_slB_one_two (r : ℕ) : Rr K r ⊓ slB K 1 2 = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨a, -, rfl⟩, hS⟩
  rw [Tl_eq_diagHom] at hS
  have h0 := dvec_eq_one_of_mem_slB hS (k := 0) (by decide) (by decide)
  have ha : a = 1 := Units.ext h0
  rw [Subgroup.mem_bot, ha, map_one]

end CFSG.RankThree.PartOne.K1320
