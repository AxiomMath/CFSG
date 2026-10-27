module

public import CFSG.Quasithin.EmptyFaithful.S14620F

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

section Model

private abbrev SL5 : Type := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

private def MaxSolv {Z : Type*} [Group Z] (W : Subgroup Z) : Set (Subgroup Z) :=
  {V | W ≤ V ∧ Group.IsSolvable ↥V ∧ ∀ V' : Subgroup Z, V ≤ V' → Group.IsSolvable ↥V' → V' = V}

private theorem hK2 : Nat.card (ZMod 2) = 2 := by simp

private def Q (J : Set ℕ) : Subgroup SL5 := flagStabilizer 5 (ZMod 2) J
private def J13 : Set ℕ := {1, 3}
private def J23 : Set ℕ := {2, 3}
private def J24 : Set ℕ := {2, 4}
private def U0 : Subgroup SL5 := unitriangular 5 (ZMod 2)

private theorem Q_anti {I J : Set ℕ} (h : J ⊆ I) : Q I ≤ Q J := fun _ hg =>
  mem_flagStabilizer.mpr fun i hi => mem_flagStabilizer.mp hg i (h hi)

private theorem U0_le_Q (J : Set ℕ) : U0 ≤ Q J :=
  (unitriangular_le_upperTriangular 5 (ZMod 2)).trans (upperTriangular_le_flagStabilizer J)

private theorem small_J13 : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ J13) → (a + m = 5 ∨ a + m ∈ J13) →
    (∀ c ∈ J13, ¬ (a < c ∧ c < a + m)) → m ≤ 2 := by
  intro a m h ha hb hno
  have h1 := hno 1 (by simp [J13])
  have h2 := hno 3 (by simp [J13])
  simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  omega

private theorem small_J23 : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ J23) → (a + m = 5 ∨ a + m ∈ J23) →
    (∀ c ∈ J23, ¬ (a < c ∧ c < a + m)) → m ≤ 2 := by
  intro a m h ha hb hno
  have h1 := hno 2 (by simp [J23])
  have h2 := hno 3 (by simp [J23])
  simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  omega

private theorem small_J24 : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ J24) → (a + m = 5 ∨ a + m ∈ J24) →
    (∀ c ∈ J24, ¬ (a < c ∧ c < a + m)) → m ≤ 2 := by
  intro a m h ha hb hno
  have h1 := hno 2 (by simp [J24])
  have h2 := hno 4 (by simp [J24])
  simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  omega

private theorem isSolvable_Q {J : Set ℕ}
    (h : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ J) → (a + m = 5 ∨ a + m ∈ J) →
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) → m ≤ 2) : Group.IsSolvable ↥(Q J) :=
  (isSolvable_iff_perfectCore_eq_bot (Q J)).mpr (perfectCore_eq_bot_of_small hK2 (by norm_num) h)

private theorem not_isSolvable_Q {J : Set ℕ} {a m : ℕ} (h : a + m ≤ 5) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ J) (hb : a + m = 5 ∨ a + m ∈ J) (hno : ∀ c ∈ J, ¬ (a < c ∧ c < a + m)) :
    ¬ Group.IsSolvable ↥(Q J) := by
  intro hs
  have hbot := (isSolvable_iff_perfectCore_eq_bot (Q J)).mp hs
  have hsurj := bigBlockHom_surjective (K := ZMod 2) hK2 h hm3 ha hb hno
  have hsimple := sl_isSimple_of_card_two hK2 hm3
  obtain ⟨y, hy⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin m) (ZMod 2))
  obtain ⟨x, hx⟩ := hsurj y
  have hx1 : x = 1 := by
    apply Subtype.ext
    have h3 := (SetLike.ext_iff.mp hbot (x : SL5)).mp x.2
    simpa using h3
  apply hy
  rw [← hx, hx1, map_one]

private theorem exists_pair_of_small {I : Set ℕ}
    (hsmall : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ I) → (a + m = 5 ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) :
    (1 ∈ I ∧ 3 ∈ I) ∨ (2 ∈ I ∧ 3 ∈ I) ∨ (2 ∈ I ∧ 4 ∈ I) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h13, h23, h24⟩ := hcon
  have key : ∀ a m : ℕ, a + m ≤ 5 → 3 ≤ m → (a = 0 ∨ a ∈ I) → (a + m = 5 ∨ a + m ∈ I) →
      (∀ c, a < c → c < a + m → c ∉ I) → False := by
    intro a m h hm ha hb hno
    have := hsmall a m h ha hb (fun c hc hc' => hno c hc'.1 hc'.2 hc)
    omega
  by_cases h2 : 2 ∈ I
  · have h3 : 3 ∉ I := h23 h2
    have h4 : 4 ∉ I := h24 h2
    exact key 2 3 (by norm_num) le_rfl (Or.inr h2) (Or.inl rfl) (by
      intro c hc1 hc2
      have : c = 3 ∨ c = 4 := by omega
      rcases this with rfl | rfl <;> assumption)
  · by_cases h3 : 3 ∈ I
    · have h1 : 1 ∉ I := fun h => h13 h h3
      exact key 0 3 (by norm_num) le_rfl (Or.inl rfl) (Or.inr (by simpa using h3)) (by
        intro c hc1 hc2
        have : c = 1 ∨ c = 2 := by omega
        rcases this with rfl | rfl <;> assumption)
    · by_cases h4 : 4 ∈ I
      · by_cases h1 : 1 ∈ I
        · exact key 1 3 (by norm_num) le_rfl (Or.inr h1) (Or.inr (by simpa using h4)) (by
            intro c hc1 hc2
            have : c = 2 ∨ c = 3 := by omega
            rcases this with rfl | rfl <;> assumption)
        · exact key 0 4 (by norm_num) (by norm_num) (Or.inl rfl) (Or.inr (by simpa using h4)) (by
            intro c hc1 hc2
            have : c = 1 ∨ c = 2 ∨ c = 3 := by omega
            rcases this with rfl | rfl | rfl <;> assumption)
      · by_cases h1 : 1 ∈ I
        · exact key 1 4 (by norm_num) (by norm_num) (Or.inr h1) (Or.inl rfl) (by
            intro c hc1 hc2
            have : c = 2 ∨ c = 3 ∨ c = 4 := by omega
            rcases this with rfl | rfl | rfl <;> assumption)
        · exact key 0 5 (by norm_num) (by norm_num) (Or.inl rfl) (Or.inl rfl) (by
            intro c hc1 hc2
            have : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by omega
            rcases this with rfl | rfl | rfl | rfl <;> assumption)

private theorem small_of_isSolvable_Q {I : Set ℕ} (hs : Group.IsSolvable ↥(Q I)) :
    ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ I) → (a + m = 5 ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2 := by
  intro a m h ha hb hno
  by_contra hm
  exact not_isSolvable_Q h (by omega) ha hb hno hs

private theorem range_J13 : ∀ i ∈ J13, 1 ≤ i ∧ i < 5 := by
  intro i hi; simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega
private theorem range_J23 : ∀ i ∈ J23, 1 ≤ i ∧ i < 5 := by
  intro i hi; simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega
private theorem range_J24 : ∀ i ∈ J24, 1 ≤ i ∧ i < 5 := by
  intro i hi; simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega

private theorem small_three {J : Set ℕ} (hJ : J = J13 ∨ J = J23 ∨ J = J24) :
    ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ J) → (a + m = 5 ∨ a + m ∈ J) →
      (∀ c ∈ J, ¬ (a < c ∧ c < a + m)) → m ≤ 2 := by
  rcases hJ with rfl | rfl | rfl
  · exact small_J13
  · exact small_J23
  · exact small_J24

private theorem upper_le_U0 : upperTriangular 5 (ZMod 2) ≤ U0 := upperTriangular_le_unitriangular hK2

private theorem cuts_subset_of_Q_le {J : Set ℕ} {V : Subgroup SL5} (h : Q J ≤ V) :
    borelOvergroupCuts V ⊆ J := by
  rintro i ⟨hi, hin, hnot⟩
  by_contra hiJ
  exact hnot (h (((subflag_stabilizer_generation (K := ZMod 2) (n := 5) J).2.2 i hi hin).mpr hiJ))

private theorem eq_of_sub {I J : Set ℕ} (hIJ : I ⊆ J) (hJ : J = J13 ∨ J = J23 ∨ J = J24)
    (h : (1 ∈ I ∧ 3 ∈ I) ∨ (2 ∈ I ∧ 3 ∈ I) ∨ (2 ∈ I ∧ 4 ∈ I)) : I = J := by
  rcases hJ with rfl | rfl | rfl
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine Set.Subset.antisymm hIJ fun x hx => ?_
      simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    · have := hIJ ha
      simp [J13] at this
    · have := hIJ ha
      simp [J13] at this
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := hIJ ha
      simp [J23] at this
    · refine Set.Subset.antisymm hIJ fun x hx => ?_
      simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption
    · have := hIJ hb
      simp [J23] at this
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have := hIJ ha
      simp [J24] at this
    · have := hIJ hb
      simp [J24] at this
    · refine Set.Subset.antisymm hIJ fun x hx => ?_
      simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> assumption

private theorem Q_mem_maxSolv {J : Set ℕ} (hJ : J = J13 ∨ J = J23 ∨ J = J24) : Q J ∈ MaxSolv U0 := by
  refine ⟨U0_le_Q J, isSolvable_Q (small_three hJ), ?_⟩
  intro V hle hs
  have hBV : upperTriangular 5 (ZMod 2) ≤ V := upper_le_U0.trans ((U0_le_Q J).trans hle)
  obtain ⟨hVQ, -⟩ := borel_overgroups V hBV
  have hVQ' : V = Q (borelOvergroupCuts V) := hVQ
  have hsQ : Group.IsSolvable ↥(Q (borelOvergroupCuts V)) := by rw [← hVQ']; exact hs
  have hpair := exists_pair_of_small (small_of_isSolvable_Q hsQ)
  have hIJ : borelOvergroupCuts V ⊆ J := cuts_subset_of_Q_le hle
  have hIeq : borelOvergroupCuts V = J := eq_of_sub hIJ hJ hpair
  rw [hVQ', hIeq]

private theorem maxSolv_U0 : MaxSolv U0 = {Q J13, Q J23, Q J24} := by
  ext V
  constructor
  · rintro ⟨hUV, hsolv, hmax⟩
    have hBV : upperTriangular 5 (ZMod 2) ≤ V := upper_le_U0.trans hUV
    obtain ⟨hVQ, -⟩ := borel_overgroups V hBV
    have hVQ' : V = Q (borelOvergroupCuts V) := hVQ
    have hsQ : Group.IsSolvable ↥(Q (borelOvergroupCuts V)) := by rw [← hVQ']; exact hsolv
    have hpair := exists_pair_of_small (small_of_isSolvable_Q hsQ)
    have hex : ∃ J, (J = J13 ∨ J = J23 ∨ J = J24) ∧ J ⊆ borelOvergroupCuts V := by
      rcases hpair with ⟨h1, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h4⟩
      · refine ⟨J13, Or.inl rfl, ?_⟩
        intro x hx
        simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption
      · refine ⟨J23, Or.inr (Or.inl rfl), ?_⟩
        intro x hx
        simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption
      · refine ⟨J24, Or.inr (Or.inr rfl), ?_⟩
        intro x hx
        simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl <;> assumption
    obtain ⟨J, hJ, hJI⟩ := hex
    have hle : V ≤ Q J := calc V = Q (borelOvergroupCuts V) := hVQ'
      _ ≤ Q J := Q_anti hJI
    have heq : Q J = V := hmax (Q J) hle (isSolvable_Q (small_three hJ))
    rcases hJ with rfl | rfl | rfl
    · left; exact heq.symm
    · right; left; exact heq.symm
    · right; right; exact heq.symm
  · rintro (rfl | rfl | rfl)
    · exact Q_mem_maxSolv (Or.inl rfl)
    · exact Q_mem_maxSolv (Or.inr (Or.inl rfl))
    · exact Q_mem_maxSolv (Or.inr (Or.inr rfl))

private theorem Q_inj {I J : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 5) (hJ : ∀ i ∈ J, 1 ≤ i ∧ i < 5)
    (h : Q I = Q J) : I = J := by
  have h1 : I = borelOvergroupCuts (Q I) :=
    (borel_overgroups (Q I) (upperTriangular_le_flagStabilizer I)).2 I hI rfl
  have h2 : J = borelOvergroupCuts (Q J) :=
    (borel_overgroups (Q J) (upperTriangular_le_flagStabilizer J)).2 J hJ rfl
  calc I = borelOvergroupCuts (Q I) := h1
    _ = borelOvergroupCuts (Q J) := by rw [h]
    _ = J := h2.symm

private theorem ncard_maxSolv_U0 : (MaxSolv U0).ncard = 3 := by
  rw [maxSolv_U0]
  refine Set.ncard_eq_three.mpr ⟨Q J13, Q J23, Q J24, ?_, ?_, ?_, rfl⟩
  · intro h
    have := Q_inj range_J13 range_J23 h
    have h1 := congrArg (fun S : Set ℕ => 1 ∈ S) this
    simp [J13, J23] at h1
  · intro h
    have := Q_inj range_J13 range_J24 h
    have h1 := congrArg (fun S : Set ℕ => 1 ∈ S) this
    simp [J13, J24] at h1
  · intro h
    have := Q_inj range_J23 range_J24 h
    have h1 := congrArg (fun S : Set ℕ => 3 ∈ S) this
    simp [J23, J24] at h1

private def a01 : SL5 :=
  ⟨!![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩
private def a12 : SL5 :=
  ⟨!![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩
private def a23 : SL5 :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩
private def a34 : SL5 :=
  ⟨!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1], by decide +kernel⟩

private theorem a01_pow : a01 ^ 3 = 1 := by decide +kernel
private theorem a12_pow : a12 ^ 3 = 1 := by decide +kernel
private theorem a23_pow : a23 ^ 3 = 1 := by decide +kernel
private theorem a34_pow : a34 ^ 3 = 1 := by decide +kernel
private theorem a01_ne : a01 ≠ 1 := by decide +kernel
private theorem a12_ne : a12 ≠ 1 := by decide +kernel
private theorem a23_ne : a23 ≠ 1 := by decide +kernel
private theorem a34_ne : a34 ≠ 1 := by decide +kernel

private theorem comm_12_34 : a12 * a34 = a34 * a12 := by decide +kernel
private theorem comm_01_34 : a01 * a34 = a34 * a01 := by decide +kernel
private theorem comm_01_23 : a01 * a23 = a23 * a01 := by decide +kernel
private theorem ne_12_34 : a12 ≠ a34 := by decide +kernel
private theorem ne_12_34' : a12 ≠ a34 ^ 2 := by decide +kernel
private theorem ne_01_34 : a01 ≠ a34 := by decide +kernel
private theorem ne_01_34' : a01 ≠ a34 ^ 2 := by decide +kernel
private theorem ne_01_23 : a01 ≠ a23 := by decide +kernel
private theorem ne_01_23' : a01 ≠ a23 ^ 2 := by decide +kernel

private theorem mem_Q_of_blocks {J : Set ℕ} {g : SL5}
    (h : ∀ i ∈ J, ∀ a b : Fin 5, b.val < i → i ≤ a.val →
      ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b).val = 0) : g ∈ Q J := by
  refine mem_flagStabilizer.mpr fun i hi => mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ j : Fin 5, i ≤ j.val → v j = 0 := mem_flagSpace.mp hv
  refine mem_flagSpace.mpr fun j hj => ?_
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : b.val < i
  · rw [(ZMod.val_eq_zero _).mp (h i hi j b hb hj), zero_mul]
  · rw [hv' b (not_lt.mp hb), mul_zero]

private theorem a12_mem_J13 : a12 ∈ Q J13 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel
private theorem a34_mem_J13 : a34 ∈ Q J13 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J13, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel
private theorem a01_mem_J23 : a01 ∈ Q J23 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel
private theorem a34_mem_J23 : a34 ∈ Q J23 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J23, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel
private theorem a01_mem_J24 : a01 ∈ Q J24 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel
private theorem a23_mem_J24 : a23 ∈ Q J24 := by
  refine mem_Q_of_blocks fun i hi => ?_
  simp only [J24, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with rfl | rfl <;> decide +kernel

private theorem two_le_pRank_pair {G : Type*} [Group G] [Finite G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b = b * a) (h1 : a ≠ b) (h2 : a ≠ b ^ 2) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoa : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxB⟩
    rw [Subgroup.mem_bot]
    have hA := mem_zpowers_of_orderOf_eq_three hoa hxA
    have hB := mem_zpowers_of_orderOf_eq_three hob hxB
    have ha4 : (a ^ 2) ^ 2 = a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]
    have hb4 : (b ^ 2) ^ 2 = b := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hb, one_mul]
    rcases hA with h | h | h
    · exact h
    · rcases hB with h' | h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') h1
      · exact absurd (h.symm.trans h') h2
    · rcases hB with h' | h' | h'
      · exact h'
      · exfalso
        have hba : b = a ^ 2 := h'.symm.trans h
        have : b ^ 2 = a := by rw [hba]; exact ha4
        exact h2 this.symm
      · exfalso
        apply h1
        have hba : b ^ 2 = a ^ 2 := h'.symm.trans h
        calc a = (a ^ 2) ^ 2 := ha4.symm
          _ = (b ^ 2) ^ 2 := by rw [hba]
          _ = b := hb4
  have hc : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute a b from hab) i j)).eq
  have h0 := pRank_add_le_pRank_sup Nat.prime_three hc hinf
  have h3 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers a) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one ha) (k := 1) ?_
    rw [Nat.card_zpowers, hoa]; simp
  have h4 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers b) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers_of_pow_eq_one hb) (k := 1) ?_
    rw [Nat.card_zpowers, hob]; simp
  omega

private theorem two_le_pRank_Q {J : Set ℕ} (hJ : J = J13 ∨ J = J23 ∨ J = J24) :
    2 ≤ CFSG.Open.pRank 3 (Q J) := by
  have key : ∀ {a b : SL5}, a ^ 3 = 1 → b ^ 3 = 1 → a ≠ 1 → b ≠ 1 → a * b = b * a → a ≠ b → a ≠ b ^ 2 →
      a ∈ Q J → b ∈ Q J → 2 ≤ CFSG.Open.pRank 3 (Q J) := by
    intro a b ha hb ha1 hb1 hab h1 h2 haJ hbJ
    have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Q J :=
      sup_le (Subgroup.zpowers_le.mpr haJ) (Subgroup.zpowers_le.mpr hbJ)
    exact (two_le_pRank_pair ha hb ha1 hb1 hab h1 h2).trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle)
  rcases hJ with rfl | rfl | rfl
  · exact key a12_pow a34_pow a12_ne a34_ne comm_12_34 ne_12_34 ne_12_34' a12_mem_J13 a34_mem_J13
  · exact key a01_pow a34_pow a01_ne a34_ne comm_01_34 ne_01_34 ne_01_34' a01_mem_J23 a34_mem_J23
  · exact key a01_pow a23_pow a01_ne a23_ne comm_01_23 ne_01_23 ne_01_23' a01_mem_J24 a23_mem_J24

end Model

section Transport

private theorem pRank_map_injective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (E : Subgroup A) :
    CFSG.Open.pRank 3 (E.map f) = CFSG.Open.pRank 3 E := by
  have e : ↥E ≃* ↥(E.map f) := E.equivMapOfInjective f hf
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  rw [pRank_top_subtype, pRank_top_subtype] at h1
  exact h1.symm

private theorem isSolvable_map_iff {Z Z' : Type*} [Group Z] [Group Z'] (θ : Z ≃* Z') (V : Subgroup Z) :
    Group.IsSolvable ↥(V.map θ.toMonoidHom) ↔ Group.IsSolvable ↥V := by
  have e : ↥V ≃* ↥(V.map θ.toMonoidHom) := V.equivMapOfInjective θ.toMonoidHom θ.injective
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

private theorem maxSolv_map_iff {Z Z' : Type*} [Group Z] [Group Z'] (θ : Z ≃* Z') (W V : Subgroup Z) :
    V.map θ.toMonoidHom ∈ MaxSolv (W.map θ.toMonoidHom) ↔ V ∈ MaxSolv W := by
  have hinj := θ.injective
  have hsurj := θ.surjective
  unfold MaxSolv
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(Subgroup.map_le_map_iff_of_injective hinj).mp h1, (isSolvable_map_iff θ V).mp h2, ?_⟩
    intro V' hV' hs'
    have := h3 (V'.map θ.toMonoidHom) (Subgroup.map_mono hV') ((isSolvable_map_iff θ V').mpr hs')
    exact Subgroup.map_injective hinj this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Subgroup.map_mono h1, (isSolvable_map_iff θ V).mpr h2, ?_⟩
    intro V'' hV'' hs''
    have hV'map : (V''.comap θ.toMonoidHom).map θ.toMonoidHom = V'' :=
      Subgroup.map_comap_eq_self_of_surjective hsurj V''
    have hVV' : V ≤ V''.comap θ.toMonoidHom := Subgroup.map_le_iff_le_comap.mp hV''
    have hs' : Group.IsSolvable ↥(V''.comap θ.toMonoidHom) :=
      (isSolvable_map_iff θ _).mp (by rw [hV'map]; exact hs'')
    have := h3 _ hVV' hs'
    rw [← hV'map, this]

private theorem ncard_and_pRank {Z : Type*} [Group Z] [Finite Z] (θ : Z ≃* SL5) (W : Subgroup Z)
    (hW : W.map θ.toMonoidHom = U0) :
    (MaxSolv W).ncard = 3 ∧ ∀ V ∈ MaxSolv W, 2 ≤ CFSG.Open.pRank 3 V := by
  have : Finite SL5 := Finite.of_equiv Z θ.toEquiv
  have himg : (fun V : Subgroup Z => V.map θ.toMonoidHom) '' MaxSolv W = MaxSolv U0 := by
    ext V'
    constructor
    · rintro ⟨V, hV, rfl⟩
      have := (maxSolv_map_iff θ W V).mpr hV
      rwa [hW] at this
    · intro hV'
      refine ⟨V'.comap θ.toMonoidHom, ?_, Subgroup.map_comap_eq_self_of_surjective θ.surjective V'⟩
      rw [← maxSolv_map_iff θ W, Subgroup.map_comap_eq_self_of_surjective θ.surjective, hW]
      exact hV'
  refine ⟨?_, ?_⟩
  · rw [← Set.ncard_image_of_injective (MaxSolv W) (Subgroup.map_injective (f := θ.toMonoidHom) θ.injective), himg]
    exact ncard_maxSolv_U0
  · intro V hV
    have h1 : V.map θ.toMonoidHom ∈ MaxSolv U0 := by rw [← himg]; exact ⟨V, hV, rfl⟩
    rw [maxSolv_U0] at h1
    have h2 : 2 ≤ CFSG.Open.pRank 3 (V.map θ.toMonoidHom) := by
      rcases h1 with h | h | h
      · rw [h]; exact two_le_pRank_Q (Or.inl rfl)
      · rw [h]; exact two_le_pRank_Q (Or.inr (Or.inl rfl))
      · rw [h]; exact two_le_pRank_Q (Or.inr (Or.inr rfl))
    rwa [pRank_map_injective θ.toMonoidHom θ.injective V] at h2

end Transport

section Fixed

private theorem exists_fixed_maxSolv {Z : Type*} [Group Z] [Finite Z] (W : Subgroup Z)
    {Γ : Type*} [Group Γ] (hΓ : IsPGroup 2 Γ) (φ : Γ →* MulAut Z)
    (hW : ∀ γ, W.map (φ γ).toMonoidHom = W) (h3 : (MaxSolv W).ncard = 3) :
    ∃ V ∈ MaxSolv W, ∀ γ, V.map (φ γ).toMonoidHom = V := by
  classical
  have hstab : ∀ γ V, V ∈ MaxSolv W → V.map (φ γ).toMonoidHom ∈ MaxSolv W := by
    intro γ V hV
    have := (maxSolv_map_iff (φ γ) W V).mpr hV
    rwa [hW γ] at this
  have hone : ∀ V : Subgroup Z, V.map (φ 1).toMonoidHom = V := by
    intro V
    have : (φ 1).toMonoidHom = MonoidHom.id Z := by
      ext z
      simp
    rw [this, Subgroup.map_id]
  have hmul : ∀ γ δ (V : Subgroup Z),
      V.map (φ (γ * δ)).toMonoidHom = (V.map (φ δ).toMonoidHom).map (φ γ).toMonoidHom := by
    intro γ δ V
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp
  let _ : MulAction Γ (MaxSolv W) :=
    { smul := fun γ V => ⟨V.1.map (φ γ).toMonoidHom, hstab γ V.1 V.2⟩
      one_smul := fun V => Subtype.ext (hone V.1)
      mul_smul := fun γ δ V => Subtype.ext (hmul γ δ V.1) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup Z) :=
    Finite.of_injective (SetLike.coe : Subgroup Z → Set Z) SetLike.coe_injective
  have hmod := hΓ.card_modEq_card_fixedPoints (MaxSolv W)
  rw [Nat.card_coe_set_eq, h3] at hmod
  have hne : Nat.card (MulAction.fixedPoints Γ (MaxSolv W)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  refine ⟨x.1, x.2, fun γ => ?_⟩
  exact congrArg Subtype.val (MulAction.mem_fixedPoints.mp hx γ)

end Fixed

section Final

private theorem isSylowTwoOf_map_top {Z Z' : Type*} [Group Z] [Group Z'] (θ : Z ≃* Z') {W : Subgroup Z}
    (hW : IsSylowTwoOf W ⊤) : IsSylowTwoOf (W.map θ.toMonoidHom) ⊤ := by
  refine ⟨le_top, hW.2.1.of_equiv (W.equivMapOfInjective θ.toMonoidHom θ.injective), ?_⟩
  have h1 := Subgroup.relIndex_map_map_of_injective (f := θ.toMonoidHom) W ⊤ θ.injective
  rw [Subgroup.map_top_of_surjective _ θ.surjective] at h1
  show ¬ 2 ∣ (W.map θ.toMonoidHom).relIndex ⊤
  rw [h1]
  exact hW.2.2

private theorem isSylowTwoOf_subgroupOf_top'' {X : Type*} [Group X] {T H : Subgroup X}
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, ?_, ?_⟩
  · have e : ↥(T.subgroupOf H) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hT.1
    exact hT.2.1.of_injective e.toMonoidHom e.injective
  · have h := hT.2.2
    have e : ((T.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (T.subgroupOf H).index :=
      Subgroup.index_comap_of_surjective (T.subgroupOf H) (f := (⊤ : Subgroup ↥H).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    rw [e]
    exact h

private theorem isSylowTwoOf_U0 : IsSylowTwoOf U0 ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have h := isSylowTwoOf_top_of_sylow P
  rw [hP] at h
  exact h

private theorem map_conjNormal_inf_le {Y : Type*} [Group Y] {Kh : Subgroup Y} [Kh.Normal] {S : Subgroup Y}
    {s : Y} (hs : s ∈ S) :
    ((S ⊓ Kh).subgroupOf Kh).map (MulAut.conjNormal (H := Kh) s).toMonoidHom ≤ (S ⊓ Kh).subgroupOf Kh := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ (S ⊓ Kh).subgroupOf Kh := hw
  rw [Subgroup.mem_subgroupOf] at hw' ⊢
  have h1 : ((MulAut.conjNormal (H := Kh) s w : Kh) : Y) = s * (w : Y) * s⁻¹ := MulAut.conjNormal_apply s w
  show ((MulAut.conjNormal (H := Kh) s w : Kh) : Y) ∈ S ⊓ Kh
  rw [h1]
  exact ⟨S.mul_mem (S.mul_mem hs hw'.1) (S.inv_mem hs), (MulAut.conjNormal (H := Kh) s w).2⟩

end Final

section Main

theorem l5_two_core : L5Core := by
  intro Y _ _ Kh T' hKh hP _ hT
  have hKh' : Kh.Normal := hKh
  obtain ⟨S, hS, hTS⟩ := A4.exists_isSylowTwoOf_ge (le_top : T' ≤ ⊤) hT
  have hKN : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (Kh : Set Y) := fun x _ =>
    (Subgroup.normalizer_eq_top_iff.mpr hKh') ▸ Subgroup.mem_top x
  have hW : IsSylowTwoOf (S ⊓ Kh) Kh := A4.isSylowTwoOf_inf_normal hS le_top hKN
  have hWz : IsSylowTwoOf ((S ⊓ Kh).subgroupOf Kh) ⊤ := isSylowTwoOf_subgroupOf_top'' hW
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_sl_of_isPSL hP
  have hW' := isSylowTwoOf_map_top θ₀ hWz
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_U0 hW'
  let θ : ↥Kh ≃* SL5 := θ₀.trans (MulAut.conj g⁻¹)
  have hθ : ∀ w : ↥Kh, θ.toMonoidHom w = g⁻¹ * θ₀ w * g := fun w => by
    show (MulAut.conj g⁻¹) (θ₀ w) = _
    simp
  have hθW : ((S ⊓ Kh).subgroupOf Kh).map θ.toMonoidHom = U0 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 : θ₀ w ∈ ((S ⊓ Kh).subgroupOf Kh).map θ₀.toMonoidHom := ⟨w, hw, rfl⟩
      rw [hθ]
      exact (hg (θ₀ w)).mp h1
    · intro hx
      have h2 : g * x * g⁻¹ ∈ ((S ⊓ Kh).subgroupOf Kh).map θ₀.toMonoidHom :=
        (hg _).mpr (by simpa [mul_assoc] using hx)
      obtain ⟨w, hw, hwx⟩ := h2
      refine ⟨w, hw, ?_⟩
      rw [hθ]
      have : θ₀ w = g * x * g⁻¹ := hwx
      rw [this]
      group
  obtain ⟨h3, hrk⟩ := ncard_and_pRank θ _ hθW
  let φ : ↥S →* MulAut ↥Kh := MulAut.conjNormal.comp S.subtype
  have hWφ : ∀ γ : ↥S, ((S ⊓ Kh).subgroupOf Kh).map (φ γ).toMonoidHom = (S ⊓ Kh).subgroupOf Kh := by
    intro γ
    refine le_antisymm (map_conjNormal_inf_le γ.2) fun w hw => ?_
    refine ⟨MulAut.conjNormal (γ : Y)⁻¹ w, map_conjNormal_inf_le (S.inv_mem γ.2) ⟨w, hw, rfl⟩, ?_⟩
    show (MulAut.conjNormal (γ : Y)) ((MulAut.conjNormal (γ : Y)⁻¹) w) = w
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  obtain ⟨V, hV, hfix⟩ := exists_fixed_maxSolv _ hS.2.1 φ hWφ h3
  have hVs : Group.IsSolvable ↥V := hV.2.1
  refine ⟨V.map Kh.subtype, Subgroup.map_subtype_le V, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ S := hTS ht
    have key : ∀ s ∈ S, ∀ x ∈ V.map Kh.subtype, s * x * s⁻¹ ∈ V.map Kh.subtype := by
      intro s hs x hx
      obtain ⟨v, hv, rfl⟩ := hx
      have hf := hfix ⟨s, hs⟩
      have hmem : (φ ⟨s, hs⟩) v ∈ V := by
        have : (φ ⟨s, hs⟩) v ∈ V.map (φ ⟨s, hs⟩).toMonoidHom := ⟨v, hv, rfl⟩
        rwa [hf] at this
      exact ⟨(φ ⟨s, hs⟩) v, hmem, MulAut.conjNormal_apply s v⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key t ht' x
    · intro hx
      have := key t⁻¹ (S.inv_mem ht') _ hx
      simpa [mul_assoc] using this
  · exact Group.isSolvable_of_isSolvable_injective
      (f := (V.equivMapOfInjective Kh.subtype Kh.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  · rw [pRank_map_injective Kh.subtype Kh.subtype_injective V]
    exact hrk V hV

end Main

theorem stage14620_of_remaining_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) (i2 : Input14620M22)
    (i5 : Input14620Rank2) (i6 : Input14620Bender) : Stage14620 :=
  stage14620_of_reduced_inputs h37 h38 hD36 hD37 hD321 hI5 hD310 hD391 hI4 i2 l5_two_core i5 i6

end CFSG.Quasithin
