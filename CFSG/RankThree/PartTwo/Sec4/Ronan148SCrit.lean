module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows
public import CFSG.RankThree.PartTwo.Sec4.Item426RestNumerics

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Orders

@[expose] def typeOrders425 (M B : ℕ) : List ℕ :=
  ([1080, 7560, 1330560].filter fun t => decide (t ∣ M)) ++
    ((List.range B).filter fun q => decide (2 < q) && decide (q % 3 = 1) &&
      decide (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ M)).map
        (fun q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ++
    ((List.range B).filter fun q => decide (2 < q) && decide (q % 3 = 2) &&
      decide (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ M)).map
        (fun q => q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))

theorem lt_of_cube_le {M B q : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3) (hq : q ^ 3 ∣ M) : q < B := by
  by_contra hqB
  have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hqB) 3
  have h2 := Nat.le_of_dvd hM0 hq
  omega

theorem card_mem_typeOrders425 {X : Type} [Group X] [Finite X] (hXq : IsQuasisimple X)
    {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3) (hX : IsType425 X) (hM : Nat.card X ∣ M) :
    Nat.card X ∈ typeOrders425 M B := by
  unfold typeOrders425
  have hcardA : ∀ n : ℕ, 2 ≤ n → Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 :=
    fun n hn => KFacts.KS14.card_alternatingGroup_fin hn
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rcases hX with hX | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩
  · have hT : IsSLThreePi (⊤ : Subgroup X) := isSLThreePi_congr Subgroup.topEquiv.symm hX
    have hTq : IsQuasisimple (⊤ : Subgroup X) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hXq
    obtain ⟨π, p, f, K, _, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hT hTq
    have hc := Sec13.card_slPi_three (π := π) hK
    rw [← Nat.card_congr e.toEquiv, Subgroup.card_top] at hc
    have hq3 : (p ^ f) ^ 3 ∣ M := (Dvd.intro _ (by rw [hc, mul_assoc])).trans hM
    have hqB := lt_of_cube_le hM0 hB hq3
    cases π
    ·
      have hmod : p ^ f % 3 = 2 := hq
      have hc' : Nat.card X = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
        rw [hc]; simp [mul_assoc]
      refine List.mem_append_right _ (List.mem_map.mpr ⟨p ^ f, List.mem_filter.mpr
        ⟨List.mem_range.mpr hqB, ?_⟩, hc'.symm⟩)
      simp [hq2, hmod, ← hc', hM]
    ·
      have hmod : p ^ f % 3 = 1 := hq
      have hc' : Nat.card X = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
        rw [hc]; simp [mul_assoc]
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨p ^ f,
        List.mem_filter.mpr ⟨List.mem_range.mpr hqB, ?_⟩, hc'.symm⟩))
      simp [hq2, hmod, ← hc', hM]
  all_goals
    have hcard : Nat.card X = Nat.card N * Nat.card (X ⧸ N) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N).trans (mul_comm _ _)
    rw [Nat.card_congr eN.toEquiv, Nat.card_congr eQ.toEquiv, hZ3] at hcard
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_filter.mpr ⟨?_, ?_⟩))
  · rw [hcard, hcardA 6 (by norm_num)]
    decide
  · exact decide_eq_true hM
  · rw [hcard, hcardA 7 (by norm_num)]
    decide
  · exact decide_eq_true hM
  · rw [hcard, KFacts.KS14.card_nativeM22]
    decide
  · exact decide_eq_true hM

theorem twentySeven_dvd_card_of_isType425 {X : Type} [Group X] [Finite X]
    (hXq : IsQuasisimple X) (hX : IsType425 X) : 27 ∣ Nat.card X := by
  have h0 : 0 < Nat.card X := Nat.card_pos
  have hB : Nat.card X < (Nat.card X + 1) ^ 3 :=
    calc Nat.card X < Nat.card X + 1 := Nat.lt_succ_self _
      _ ≤ (Nat.card X + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hmem := card_mem_typeOrders425 hXq h0 hB hX dvd_rfl
  unfold typeOrders425 at hmem
  simp only [List.mem_append, List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with (⟨ht, -⟩ | ⟨q, ⟨-, hq⟩, hqt⟩) | ⟨q, ⟨-, hq⟩, hqt⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h | h | h <;> rw [h] <;> norm_num
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    rw [← hqt, ← mul_assoc]
    exact Item426Rest.twentySeven_dvd_sl hq.1.2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    rw [← hqt, ← mul_assoc]
    exact Item426Rest.twentySeven_dvd_su hq.1.2

end Orders

section Criteria

variable {S : Type} [Group S] [Finite S]

theorem card_theta_quot_dvd (K : Subgroup S) :
    Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ Nat.card K :=
  Subgroup.card_quotient_dvd_card _

theorem noCC425_of_card_dvd {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : typeOrders425 M B = [])
    (hC : ∀ s : S, orderOf s = 3 → Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ M) :
    NoCQ425 S := by
  intro s K hs3 _ hKs hKq hT
  have hXq := isQuasisimple_theta_quot hKq
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ M :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_dvd_of_le hKs).trans (hC s hs3))
  have := card_mem_typeOrders425 hXq hM0 hB hT hdvd
  rw [hfree] at this
  exact List.not_mem_nil this

theorem noCC425_of_card_group_dvd {M B : ℕ} (hM0 : 0 < M) (hB : M < B ^ 3)
    (hfree : typeOrders425 M B = []) (hS : Nat.card S ∣ M) : NoCQ425 S :=
  noCC425_of_card_dvd hM0 hB hfree fun _ _ => (Subgroup.card_subgroup_dvd_card _).trans hS

theorem noCQ425_of_not_dvd (h27 : ¬ 27 ∣ Nat.card S) : NoCQ425 S := by
  intro s K _ _ _ hKq hT
  apply h27
  exact (twentySeven_dvd_card_of_isType425 (isQuasisimple_theta_quot hKq) hT).trans
    ((card_theta_quot_dvd K).trans (Subgroup.card_subgroup_dvd_card K))

theorem noCC425_of_abelian_sylow
    (h : ∀ P : Sylow 3 S, ∀ a b : S, a ∈ (P : Subgroup S) → b ∈ (P : Subgroup S) →
      a * b = b * a) :
    NoCQ425 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s K hs3 hsK hKs hKq _
  have hKp : Group.IsPerfect K := hKq.1
  set k : K := ⟨s, hsK⟩
  have hk3 : IsPGroup 3 (Subgroup.zpowers k) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hs3, pow_one])
  obtain ⟨Q, hQ⟩ := hk3.exists_le_sylow
  have hkQ : k ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers k)
  have hQ3 : IsPGroup 3 ((Q : Subgroup K).map K.subtype) := Q.isPGroup'.map _
  obtain ⟨P, hP⟩ := hQ3.exists_le_sylow
  have hQab : ∀ a b : K, a ∈ (Q : Subgroup K) → b ∈ (Q : Subgroup K) → a * b = b * a := by
    intro a b ha hb
    exact Subtype.ext (h P a b (hP ⟨a, ha, rfl⟩) (hP ⟨b, hb, rfl⟩))
  have hkZ : k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKs g.2))
  have hk1 := RonanK432.eq_one_of_mem_center_of_abelian_sylow hKp Q hQab hkZ hkQ
  have hs1 : s = 1 := congrArg Subtype.val hk1
  have := hs3
  rw [hs1, orderOf_one] at this
  exact absurd this (by norm_num)

variable {T : Type} [Group T] [Finite T]

theorem NoCQ425.of_mulEquiv (e : S ≃* T) (h : NoCQ425 T) : NoCQ425 S := by
  intro s K hs3 hsK hKs hKq hT
  have eK : K ≃* K.map (e : S →* T) := K.equivMapOfInjective _ e.injective
  refine h (e s) (K.map (e : S →* T)) (by rw [MulEquiv.orderOf_eq]; exact hs3) ⟨s, hsK, rfl⟩
    ?_ (CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq) (isType425_theta_congr eK hT)
  rw [← map_centralizer_singleton_equiv e s]
  exact Subgroup.map_mono hKs

end Criteria

abbrev NoCQOf (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → NoCQ425 S

theorem NoCQOf.of_noCQ425 {X : Type} [Group X] [Finite X] (h : NoCQ425 X) : NoCQOf X :=
  fun _ _ _ _ _ ⟨e⟩ => h.of_mulEquiv e

theorem NoCQOf.of_not_dvd {X : Type} [Group X] (hX : ¬ 27 ∣ Nat.card X) : NoCQOf X :=
  fun _ _ _ _ _ ⟨e⟩ => noCQ425_of_not_dvd (by rwa [Nat.card_congr e.toEquiv])

theorem NoCQOf.of_card_dvd {X : Type} [Group X] {M B : ℕ} (hX : Nat.card X ∣ M)
    (hM0 : 0 < M) (hB : M < B ^ 3) (hfree : typeOrders425 M B = []) : NoCQOf X :=
  fun _ _ _ _ _ ⟨e⟩ =>
    noCC425_of_card_group_dvd hM0 hB hfree (by rwa [Nat.card_congr e.toEquiv])

section RowsNoCQ

theorem rowOf425_of_noCQ {X : Type} [Group X] (h : NoCQOf X) : RowOf425 X :=
  rowOf425_of_noCC fun S _ _ hs hna hX => (h S hs hna hX).noCC425

theorem rowOf425_of_noCQ' {X : Type} [Group X] [Finite X] (h : NoCQ425 X) : RowOf425 X :=
  rowOf425_of_noCQ (NoCQOf.of_noCQ425 h)

end RowsNoCQ

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
