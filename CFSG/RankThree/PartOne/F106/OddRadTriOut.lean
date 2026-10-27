module

public import CFSG.RankThree.PartOne.F106.OddRadTriSplit
public import CFSG.RankThree.PartOne.F106.OddRadTriQPlus
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

set_option linter.unusedSectionVars false

theorem fixSub_le_of_mem_zpowers' {G : Type} [Group G] {α β : MulAut G}
    (h : α ∈ Subgroup.zpowers β) : fixSub β ≤ fixSub α := by
  intro x hx
  have hs : β ∈ MulAction.stabilizer (MulAut G) x := by
    rw [MulAction.mem_stabilizer_iff]
    exact hx
  have := Subgroup.zpowers_le.2 hs h
  rw [MulAction.mem_stabilizer_iff] at this
  exact this

theorem oddRadConcl_D4_outer {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ : orderOf β = 5)
    (hβinn : β ∉ innerAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    OddRadConcl ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) β := by
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form hf K hK σ hσ
  have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  obtain ⟨hηord, hpf, ⟨h0, hh0⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial Nat.prime_two hf K hK σ hσ
      Θ hΘ hp (by omega) ⊤ le_top ⟨β, Subgroup.mem_top β⟩ hβinn
      (by rw [Subgroup.orderOf_mk]; exact hβ)
  obtain ⟨d, rfl⟩ := hpf
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hf
      omega
    · exact h
  have hK3 : Nat.card K = 2 ^ (3 * d * 5) := by
    rw [hK, ← pow_mul]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ 2 ^ (d * 5) := fun c => by rw [hσ c, mul_comm 5 d]
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by omega : 1 ≤ 3 * d * 5) hK3
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let φ : K →+* K := iterateFrobenius K 2 (3 * d)
  let δ : K ≃+* K := RingEquiv.ofBijective φ (Finite.injective_iff_bijective.mp φ.injective)
  have hδ : ∀ c, δ c = c ^ 2 ^ (3 * d) := fun c => iterateFrobenius_def 2 (3 * d) c
  have hm3 : Nat.Coprime 5 3 := by norm_num
  obtain ⟨-, hδord, -⟩ := triality_canonical_field_facts Nat.prime_two hd1 (by omega : 2 ≤ 5)
    hm3 hK3 hσ' hδ
  obtain ⟨-, -, -, -, -, -, himage, hsimple, hnc, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel Nat.prime_two hd1
      (by omega : 2 ≤ 5) hm3 K hK3 σ hσ' δ hδ
  have : IsCyclic (K ≃+* K) := hcyc
  set η : K ≃+* K := Θ β with hη
  have hηp : η ^ 5 = 1 := hηord ▸ pow_orderOf_eq_one η
  have hδp : δ ^ 5 = 1 := hδord ▸ pow_orderOf_eq_one δ
  have hηδ : η ∈ Subgroup.zpowers δ := mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hδord hηp
  have hδη : δ ∈ Subgroup.zpowers η := mem_zpowers_of_pow_eq_one_of_isCyclic hp.pos hηord hδp
  have hact : ∀ {a b : K ≃+* K}, a ∈ Subgroup.zpowers b →
      fieldActor (t := TwistTag.D4) σ a ∈ Subgroup.zpowers (fieldActor (t := TwistTag.D4) σ b) := by
    intro a b hab
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hab
    exact ⟨k, (map_zpow (fieldActorHom (t := TwistTag.D4) σ) b k).symm⟩
  have hfix : fixSub (fieldActor (t := TwistTag.D4) σ η) =
      fixSub (fieldActor (t := TwistTag.D4) σ δ) :=
    le_antisymm (fixSub_le_of_mem_zpowers' (hact hδη)) (fixSub_le_of_mem_zpowers' (hact hηδ))
  have hcg : MulAut.congr (MulAut.conj h0) β = fieldActor σ η := hh0
  let e1 : ↥(fixSub β) ≃* ↥(fixSub (fieldActor (t := TwistTag.D4) σ η)) :=
    (fixSubEquiv (MulAut.conj h0) β).trans (MulEquiv.subgroupCongr (by rw [hcg]))
  let e2 : ↥(fixSub (fieldActor (t := TwistTag.D4) σ η)) ≃*
      ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) :=
    MulEquiv.subgroupCongr hfix
  let e3 : ↥(fixSub (fieldActor (t := TwistTag.D4) σ δ)) ≃* ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr himage)
  let ε : ↥(fixSub β) ≃* ↥(trialityFieldImage σ δ) := (e1.trans e2).trans e3
  have hnc' : ∃ u v : ↥(trialityFieldImage σ δ), u * v ≠ v * u := by
    by_contra hcon
    push Not at hcon
    exact hnc hcon
  have : IsSimpleGroup ↥(trialityFieldImage σ δ) := hsimple
  unfold OddRadConcl
  change Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(fixSub β))))
  rw [card_solvableRadical_perfectResidual_eq ε, card_radical_residual_of_simple_nonabelian hnc']
  exact odd_one

theorem five_dvd_sub_or_add_of_dvd_ordD4 {q : ℕ} (hq : 1 ≤ q) (h5 : ¬ 5 ∣ q)
    (h : 5 ∣ q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) :
    5 ∣ q - 1 ∨ 5 ∣ q + 1 := by
  have hz : ((q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1) : ℕ) : ZMod 5) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at hz
  have hx : (q : ZMod 5) ≠ 0 := fun h0 => h5 ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have key : ∀ x : ZMod 5, x ≠ 0 →
      x ^ 12 * (x ^ 2 - 1) * (x ^ 6 - 1) * (x ^ 8 + x ^ 4 + 1) = 0 → x = 1 ∨ x = -1 := by
    decide
  rcases key _ hx hz with h1 | h1
  · left
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq, h1]
    simp
  · right
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h1]
    simp

theorem oddRadConcl_D4 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ : orderOf β = 5) :
    OddRadConcl ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) β := by
  classical
  by_cases hinn : β ∈ innerAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  · obtain ⟨t, rfl⟩ := hinn
    obtain ⟨-, -, -, -, -, -, hZ, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
    have htord : orderOf t = 5 := by rw [← orderOf_conj_eq hZ t]; exact hβ
    have h5 : 5 ∣ Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      htord ▸ orderOf_dvd_natCard t
    have hσ1 : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
      rw [pow_one]
      exact hσ c
    obtain ⟨hC, -⟩ := triality_both_orientations_exact_finite_order 2 f Nat.prime_two hf K hK 1
      (Or.inl rfl) σ.toRingHom hσ1
    rw [hC] at h5
    have h5q : ¬ 5 ∣ 2 ^ f := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
      omega
    unfold OddRadConcl
    rw [eqLocus_conj_eq_centralizer t]
    rcases five_dvd_sub_or_add_of_dvd_ordD4 (Nat.one_le_two_pow) h5q h5 with h | h
    · exact oddRad_D4_split hf K hK σ hσ h t htord
    · exact oddRad_D4_qplus hf K hK σ hσ h t htord
  · exact oddRadConcl_D4_outer hf K hK σ hσ β hβ hinn

theorem oddRadAt_smallModel_trialityD4 : OddRadAt (SmallModel .trialityD4) := by
  intro T _ _ _ hS β hβ
  obtain ⟨n, f, hadm, hM, -⟩ := hS
  obtain ⟨-, hCEM⟩ := lieModel_trialityD4_iff.mp hM
  have hf : 1 ≤ f := hCEM.1.2.1
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hCEM.2
  have hK : Nat.card K = (2 ^ f) ^ 3 := hKcard
  exact oddRadConcl_of_mulEquiv e (fun β' hβ' => oddRadConcl_D4 hf K hK σ hσ β' hβ') β hβ

end CFSG.RankThree.PartOne.F106
