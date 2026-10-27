module

public import CFSG.Quasithin.EmptyFaithful.SzN2Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin.SzN2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K]

theorem not_isSolvable_sl2 (hK4 : ∃ s : Finset K, s.card = 4) :
    ¬ Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
  intro hs
  have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := K) hK4
  obtain ⟨n, hn⟩ := hs.solvable
  have htop : ∀ m, derivedSeries (SpecialLinearGroup (Fin 2) K) m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih]; exact hperf.commutator_eq_top
  rw [htop] at hn
  have hall : ∀ x : SpecialLinearGroup (Fin 2) K, x = 1 :=
    fun x => Subgroup.mem_bot.1 (hn ▸ Subgroup.mem_top x)
  have h := hall ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have h01 := congrArg
    (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp at h01

theorem upperTriangular_eq_flagStabilizer_full (n : ℕ) :
    upperTriangular n K = flagStabilizer n K {i | 1 ≤ i ∧ i < n} := by
  have h := (borel_overgroups (upperTriangular n K) le_rfl).1
  have hc : borelOvergroupCuts (upperTriangular n K) = {i | 1 ≤ i ∧ i < n} := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      exact ⟨hi, hin⟩
    · rintro ⟨hi, hin⟩
      exact ⟨hi, hin, by
        rw [← reflElt_of_lt hi hin]
        exact reflElt_not_mem_upperTriangular hi hin⟩
  rwa [hc] at h

theorem le_upperTriangular_of_cuts {n : ℕ} {A : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hle : A ≤ flagStabilizer n K (borelOvergroupCuts A))
    (hcuts : ∀ i, 1 ≤ i → i < n → i ∈ borelOvergroupCuts A) : A ≤ upperTriangular n K := by
  rw [upperTriangular_eq_flagStabilizer_full]
  intro g hg
  rw [mem_flagStabilizer]
  intro i hi
  exact mem_flagStabilizer.mp (hle hg) i (hcuts i hi.1 hi.2)

theorem sl2_le_upperTriangular_of_solvable (hK4 : ∃ s : Finset K, s.card = 4)
    {A : Subgroup (SpecialLinearGroup (Fin 2) K)} (hVA : unitriangular 2 K ≤ A)
    (hA : Group.IsSolvable ↥A) : A ≤ upperTriangular 2 K := by
  obtain ⟨hle, hiff⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := 2) (K := K)).1 A hVA
  refine le_upperTriangular_of_cuts hle fun i hi1 hin => ?_
  have hi : i = 1 := by omega
  subst hi
  by_contra h1
  have hempty : borelOvergroupCuts A = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun j hj => ?_
    obtain ⟨hj1, hjn, -⟩ := id hj
    have hj' : j = 1 := by omega
    subst hj'
    exact h1 hj
  have htop : A = ⊤ := hiff.mp hempty
  subst htop
  exact not_isSolvable_sl2 hK4
    (Group.isSolvable_of_isSolvable_injective (f := (Subgroup.topEquiv (G := _)).symm.toMonoidHom)
      (MulEquiv.injective _))

theorem sl3_le_upperTriangular_of_solvable [Finite K] (hK4 : ∃ s : Finset K, s.card = 4)
    {A : Subgroup (SpecialLinearGroup (Fin 3) K)} (hVA : unitriangular 3 K ≤ A)
    (hA : Group.IsSolvable ↥A) : A ≤ upperTriangular 3 K := by
  obtain ⟨hle, -⟩ := (linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 A hVA
  refine le_upperTriangular_of_cuts hle fun i hi1 hin => ?_
  by_contra hcut
  have hrA : reflElt 3 K i ∈ A := by
    rw [reflElt_of_lt hi1 hin]
    by_contra hnot
    exact hcut ⟨hi1, hin, hnot⟩
  have hj : 2 - i < 2 := by omega
  let j : Fin 2 := ⟨2 - i, hj⟩
  have hHA : H3 K j ≤ A := by
    have h2 : (2 : ℕ) - (j : ℕ) = i := by
      show 2 - (2 - i) = i
      omega
    show reflGroup 3 K (2 - (j : ℕ)) ≤ A
    rw [h2]
    exact sup_le hVA ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hrA))
  have hpc : perfectCore (Q3 K j) ≤ A :=
    calc perfectCore (Q3 K j) = ⁅perfectCore (Q3 K j), perfectCore (Q3 K j)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅Q3 K j, Q3 K j⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
      _ ≤ H3 K j := commutator_Q3_le j
      _ ≤ A := hHA
  have hs : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hpc)
      (Subgroup.inclusion_injective hpc)
  exact not_isSolvable_sl2 hK4 (Group.isSolvable_of_surjective
    (f := CFSG.QuasithinUnique.Vol2Native.A312L.blk3 j)
    (CFSG.QuasithinUnique.Vol2Native.A312L.blk3_surjective hK4 j))

theorem not_three_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h]
  omega

theorem orderOf_ne_three_of_mem_upperTriangular [Finite K] {n : ℕ}
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (h3 : ¬ 3 ∣ Nat.card K - 1)
    {b : SpecialLinearGroup (Fin n) K} (hb : b ∈ upperTriangular n K) : orderOf b ≠ 3 := by
  intro h
  obtain ⟨k, hk⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (unitriangular n K) :=
    IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])
  let β : ↥(upperTriangular n K) := ⟨b, hb⟩
  have hβ : orderOf β = 3 := by rw [← h]; exact Subgroup.orderOf_mk b hb
  have hd : diagHomLin n K β = 1 := by
    funext i
    have h1 : (diagHomLin n K β i) ^ 3 = 1 := by
      have h' : (diagHomLin n K β) ^ 3 = 1 := by
        rw [← map_pow, ← hβ, pow_orderOf_eq_one, map_one]
      simpa using congrFun h' i
    have h2 : orderOf (diagHomLin n K β i) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3' : orderOf (diagHomLin n K β i) ∣ Nat.card K - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (Nat.card K - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact orderOf_eq_one_iff.1 ((Nat.Coprime.coprime_dvd_left h2 hcop).eq_one_of_dvd h3')
  have hmem : β ∈ (diagHomLin n K).ker := hd
  rw [ker_diagHomLin, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨j, hj⟩ := hU ⟨b, hmem⟩
  have hpow : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h32 : 3 ∣ 2 ^ j := h ▸ orderOf_dvd_of_pow_eq_one hpow
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32
  omega

theorem isSylowTwoOf_unitriangular [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) :
    IsSylowTwoOf (unitriangular n K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) hn
  exact hP ▸ isSylowTwoOf_top_of_sylow P

theorem sl_solvable_overgroup_le_normalizer [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ A : Subgroup (SpecialLinearGroup (Fin n) K), unitriangular n K ≤ A →
      Group.IsSolvable ↥A → A ≤ upperTriangular n K) :
    ∀ Ū Y : Subgroup (SpecialLinearGroup (Fin n) K), IsSylowTwoOf Ū ⊤ → Ū ≤ Y →
      Group.IsSolvable ↥Y → Y ≤ Subgroup.normalizer (Ū : Set (SpecialLinearGroup (Fin n) K)) :=
  fun _ _ hŪ hUY hY =>
    solvable_overgroup_le_normalizer_of_sylow (isSylowTwoOf_unitriangular hn)
      (fun _ hY hs => by rw [normalizer_unitriangular]; exact h _ hY hs) hŪ hUY hY

theorem sl_no_order_three [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (h3 : ¬ 3 ∣ Nat.card K - 1)
    (h : ∀ A : Subgroup (SpecialLinearGroup (Fin n) K), unitriangular n K ≤ A →
      Group.IsSolvable ↥A → A ≤ upperTriangular n K) :
    ∀ Ū Y : Subgroup (SpecialLinearGroup (Fin n) K), IsSylowTwoOf Ū ⊤ → Ū ≤ Y →
      Group.IsSolvable ↥Y → ∀ y ∈ Y, orderOf y ≠ 3 :=
  fun _ _ hŪ hUY hY =>
    solvable_overgroup_orderOf_ne_of_sylow (isSylowTwoOf_unitriangular hn)
      (fun _ hY hs _ hy => orderOf_ne_three_of_mem_upperTriangular hK h3 (h _ hY hs hy)) hŪ hUY hY

theorem sl3_residualOvergroupsAt [Finite K] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ResidualOvergroupsAt (SpecialLinearGroup (Fin 3) K) (unitriangular 3 K)
      (fun j : Fin 2 => Q3 K j) := by
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  have h := residualOvergroupsAt_of_rank_two_data
    (π := MonoidHom.id (SpecialLinearGroup (Fin 3) K)) Function.surjective_id
    (V := unitriangular 3 K) (B := upperTriangular 3 K) (Q := Q3 K) (H := H3 K)
    (by rw [MonoidHom.ker_id]; exact bot_le) (unitriangular_le_upperTriangular 3 K)
    (fun j => by rw [Q3_eq]; exact upperTriangular_le_flagStabilizer _)
    Q3_ne covBy_Q3 (fun A hVA hAt => contained_in_Q3 hVA hAt) hB commutator_Q3_le
    (fun j A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns)
  simpa [Subgroup.map_id] using h

theorem sl3_rankTwoData [Finite K] [CharP K 2] (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    ∀ Ū : Subgroup (SpecialLinearGroup (Fin 3) K), IsSylowTwoOf Ū ⊤ →
      ∃ P : Fin 2 → Subgroup (SpecialLinearGroup (Fin 3) K), P 0 ≠ P 1 ∧
        (∀ A : Subgroup (SpecialLinearGroup (Fin 3) K), Ū ≤ A → (A ⋖ ⊤ ↔ ∃ j, A = P j)) ∧
        ∀ j, Subgroup.normalizer (Ū : Set (SpecialLinearGroup (Fin 3) K)) ≤ P j := by
  intro Ū hŪ
  obtain ⟨φ, hφ, hres⟩ := (sl3_residualOvergroupsAt hK).exists_iso_of_isSylow (MulEquiv.refl _)
    (isSylowTwoOf_unitriangular (by norm_num)) hŪ
  refine ⟨fun j => (Q3 K j).map φ.symm.toMonoidHom, hres.1, hres.2.2.1, fun j x hx => ?_⟩
  have h1 : (Subgroup.normalizer (Ū : Set (SpecialLinearGroup (Fin 3) K))).map φ.toMonoidHom =
      Subgroup.normalizer (unitriangular 3 K : Set (SpecialLinearGroup (Fin 3) K)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hφ]
  have h2 : φ x ∈ Q3 K j := by
    have h3 : φ x ∈ (Subgroup.normalizer (Ū : Set (SpecialLinearGroup (Fin 3) K))).map
        φ.toMonoidHom := ⟨x, hx, rfl⟩
    rw [h1, normalizer_unitriangular] at h3
    rw [Q3_eq]
    exact upperTriangular_le_flagStabilizer _ h3
  exact ⟨φ x, h2, by simp⟩

end CFSG.Quasithin.SzN2
