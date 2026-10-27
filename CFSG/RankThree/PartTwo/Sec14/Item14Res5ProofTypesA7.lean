module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesModel
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res5TypesA7

open Equiv KFacts.KP2 Res4A7 Res5Types

@[expose] def c1 : ↥(alternatingGroup (Fin 7)) :=
  ⟨cOne, eNine_le_alternatingGroup cOne_mem_eNine⟩

@[expose] def c2 : ↥(alternatingGroup (Fin 7)) :=
  ⟨cTwo, eNine_le_alternatingGroup cTwo_mem_eNine⟩

@[expose] def P7 : Subgroup ↥(alternatingGroup (Fin 7)) :=
  eNine.subgroupOf (alternatingGroup (Fin 7))

@[expose] def V1 : Subgroup ↥(alternatingGroup (Fin 7)) :=
  vOne.subgroupOf (alternatingGroup (Fin 7))

@[expose] def V2 : Subgroup ↥(alternatingGroup (Fin 7)) :=
  vTwo.subgroupOf (alternatingGroup (Fin 7))

@[expose] def v1 (m : Fin 4) : ↥(alternatingGroup (Fin 7)) :=
  ⟨vOneF m, vOne_le_alternatingGroup ⟨m, rfl⟩⟩

@[expose] def v2 (m : Fin 4) : ↥(alternatingGroup (Fin 7)) :=
  ⟨vTwoF m, vTwo_le_alternatingGroup ⟨m, rfl⟩⟩

theorem c1_mem_P7 : c1 ∈ P7 := Subgroup.mem_subgroupOf.mpr cOne_mem_eNine

theorem c2_mem_P7 : c2 ∈ P7 := Subgroup.mem_subgroupOf.mpr cTwo_mem_eNine

theorem card_P7 : Nat.card P7 = 9 := by
  rw [P7, Nat.card_congr (Subgroup.subgroupOfEquivOfLe eNine_le_alternatingGroup).toEquiv,
    card_eNine]

theorem vOne_facts : vOneF 1 * vOneF 1 = 1 ∧ vOneF 2 * vOneF 2 = 1 ∧
    vOneF 1 * vOneF 2 = vOneF 2 * vOneF 1 ∧ vOneF 1 ≠ 1 ∧ vOneF 2 ≠ 1 ∧ vOneF 1 ≠ vOneF 2 ∧
    vOneF 0 = 1 ∧ vOneF 3 = vOneF 1 * vOneF 2 ∧ cTwo * vOneF 1 * cTwo⁻¹ = vOneF 1 * vOneF 2 ∧
    cTwo * vOneF 2 * cTwo⁻¹ = vOneF 1 := by
  decide +kernel

theorem vTwo_facts : vTwoF 1 * vTwoF 1 = 1 ∧ vTwoF 2 * vTwoF 2 = 1 ∧
    vTwoF 1 * vTwoF 2 = vTwoF 2 * vTwoF 1 ∧ vTwoF 1 ≠ 1 ∧ vTwoF 2 ≠ 1 ∧ vTwoF 1 ≠ vTwoF 2 ∧
    vTwoF 0 = 1 ∧ vTwoF 3 = vTwoF 1 * vTwoF 2 ∧ cOne * vTwoF 1 * cOne⁻¹ = vTwoF 1 * vTwoF 2 ∧
    cOne * vTwoF 2 * cOne⁻¹ = vTwoF 1 := by
  decide +kernel

theorem mem_V1_iff (v : ↥(alternatingGroup (Fin 7))) :
    v ∈ V1 ↔ v = 1 ∨ v = v1 1 ∨ v = v1 2 ∨ v = v1 1 * v1 2 := by
  obtain ⟨-, -, -, -, -, -, h0, h3, -, -⟩ := vOne_facts
  rw [V1, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm⟩
    fin_cases m
    · exact Or.inl (Subtype.ext (hm.trans h0))
    · exact Or.inr (Or.inl (Subtype.ext hm))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext hm)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (hm.trans h3))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, h3.symm⟩

theorem mem_V2_iff (v : ↥(alternatingGroup (Fin 7))) :
    v ∈ V2 ↔ v = 1 ∨ v = v2 1 ∨ v = v2 2 ∨ v = v2 1 * v2 2 := by
  obtain ⟨-, -, -, -, -, -, h0, h3, -, -⟩ := vTwo_facts
  rw [V2, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm⟩
    fin_cases m
    · exact Or.inl (Subtype.ext (hm.trans h0))
    · exact Or.inr (Or.inl (Subtype.ext hm))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext hm)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (hm.trans h3))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, h3.symm⟩

theorem map_centralizer (x : ↥(alternatingGroup (Fin 7))) :
    (Subgroup.centralizer ({x} : Set ↥(alternatingGroup (Fin 7)))).map
        (alternatingGroup (Fin 7)).subtype =
      Subgroup.centralizer ({(x : Perm (Fin 7))} : Set (Perm (Fin 7))) ⊓
        alternatingGroup (Fin 7) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨congrArg Subtype.val hz, z.2⟩
  · rintro ⟨hy, hyA⟩
    exact ⟨⟨y, hyA⟩, Subtype.ext hy, rfl⟩

theorem theta_c1 :
    inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({c1} : Set ↥(alternatingGroup (Fin 7)))) = V1 := by
  apply Subgroup.map_injective (alternatingGroup (Fin 7)).subtype_injective
  rw [Sec6.map_inSubgroup_theta_of_injective _ (alternatingGroup (Fin 7)).subtype_injective, V1,
    Subgroup.map_subgroupOf_eq_of_le vOne_le_alternatingGroup, map_centralizer]
  exact theta_centOne

theorem theta_c2 :
    inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({c2} : Set ↥(alternatingGroup (Fin 7)))) = V2 := by
  apply Subgroup.map_injective (alternatingGroup (Fin 7)).subtype_injective
  rw [Sec6.map_inSubgroup_theta_of_injective _ (alternatingGroup (Fin 7)).subtype_injective, V2,
    Subgroup.map_subgroupOf_eq_of_le vTwo_le_alternatingGroup, map_centralizer]
  exact theta_centTwo

theorem aut_eq_one_A7 {τ : MulAut ↥(alternatingGroup (Fin 7))} (hτ : ∀ p ∈ P7, τ p = p)
    {n : ℕ} (hn : ¬ 3 ∣ n) (hτn : τ ^ n = 1) : τ = 1 := by
  have h1 : τ c1 = c1 := hτ c1 c1_mem_P7
  have h2 : τ c2 = c2 := hτ c2 c2_mem_P7
  have hV1 : ∀ v ∈ V1, τ v ∈ V1 := fun v hv => by
    rw [← theta_c1, ← map_theta_centralizer_eq h1]
    exact ⟨v, theta_c1 ▸ hv, rfl⟩
  have hV2 : ∀ v ∈ V2, τ v ∈ V2 := fun v hv => by
    rw [← theta_c2, ← map_theta_centralizer_eq h2]
    exact ⟨v, theta_c2 ▸ hv, rfl⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9, a10⟩ := vOne_facts
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10⟩ := vTwo_facts
  have hne : ∀ {u w : ↥(alternatingGroup (Fin 7))}, (u : Perm (Fin 7)) ≠ w → u ≠ w :=
    fun h e => h (e ▸ rfl)
  have hfix1 := fix_four hn hτn (V := V1) (a := v1 1) (b := v1 2) (t := c2) mem_V1_iff hV1
    (Subtype.ext a1) (Subtype.ext a2) (Subtype.ext a3) (hne a4) (hne a5) (hne a6) h2
    (Subtype.ext a9) (Subtype.ext a10)
  have hfix2 := fix_four hn hτn (V := V2) (a := v2 1) (b := v2 2) (t := c1) mem_V2_iff hV2
    (Subtype.ext b1) (Subtype.ext b2) (Subtype.ext b3) (hne b4) (hne b5) (hne b6) h1
    (Subtype.ext b9) (Subtype.ext b10)
  refine eq_one_of_top_le_fixSubgroup ?_
  have htop : V1 ⊔ V2 = ⊤ := by
    rw [V1, V2, ← Subgroup.subgroupOf_sup vOne_le_alternatingGroup vTwo_le_alternatingGroup,
      vOne_sup_vTwo, Subgroup.subgroupOf_self]
  rw [← htop]
  exact sup_le (fun v hv => hfix1 v hv) (fun v hv => hfix2 v hv)

theorem le_V_of_invariant {Y : Subgroup ↥(alternatingGroup (Fin 7))} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hYP : P7 ≤ Subgroup.normalizer (Y : Set ↥(alternatingGroup (Fin 7)))) :
    Y ≤ V1 ∨ Y ≤ V2 := by
  set Q := Y.map (alternatingGroup (Fin 7)).subtype with hQ
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    rw [hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hY3
  have hN : ∀ p ∈ P7, (p : Perm (Fin 7)) ∈ Subgroup.normalizer (Q : Set (Perm (Fin 7))) :=
    fun p hp => Subgroup.le_normalizer_map _ ⟨p, hYP hp, rfl⟩
  rcases le_vOne_or_le_vTwo hQ3 (hN c1 c1_mem_P7) (hN c2 c2_mem_P7) with h | h
  · exact Or.inl fun y hy => Subgroup.mem_subgroupOf.mpr (h ⟨y, hy, rfl⟩)
  · exact Or.inr fun y hy => Subgroup.mem_subgroupOf.mpr (h ⟨y, hy, rfl⟩)

theorem centralizer_P7_le :
    Subgroup.centralizer (P7 : Set ↥(alternatingGroup (Fin 7))) ≤ P7 := by
  intro g hg
  have h1 : g * c1 = c1 * g := (Subgroup.mem_centralizer_iff.mp hg c1 c1_mem_P7).symm
  have h2 : g * c2 = c2 * g := (Subgroup.mem_centralizer_iff.mp hg c2 c2_mem_P7).symm
  rw [P7, Subgroup.mem_subgroupOf]
  by_contra hne
  exact forall_not_of_card_filter_eq_zero card_filter_centralizer_eNine g.1
    ⟨congrArg Subtype.val h1, congrArg Subtype.val h2, fun ⟨i, j, hij⟩ => hne ⟨i, j, hij⟩⟩

theorem V_facts : Nat.card V1 = 4 ∧ Nat.card V2 = 4 ∧
    P7 ≤ Subgroup.normalizer (V1 : Set ↥(alternatingGroup (Fin 7))) ∧
    P7 ≤ Subgroup.normalizer (V2 : Set ↥(alternatingGroup (Fin 7))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [V1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe vOne_le_alternatingGroup).toEquiv,
      card_vOne]
  · rw [V2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe vTwo_le_alternatingGroup).toEquiv,
      card_vTwo]
  · intro p hp
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, V1, Subgroup.mem_subgroupOf] at hv ⊢
    exact (Subgroup.mem_normalizer_iff.mp (eNine_le_normalizer_vOne
      (Subgroup.mem_subgroupOf.mp hp)) _).mp hv
  · intro p hp
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rw [SetLike.mem_coe, V2, Subgroup.mem_subgroupOf] at hv ⊢
    exact (Subgroup.mem_normalizer_iff.mp (eNine_le_normalizer_vTwo
      (Subgroup.mem_subgroupOf.mp hp)) _).mp hv

variable {G : Type} [Group G] [Finite G]

theorem typesOne_A7
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) [(ker142 A (lB A) c).Normal] {Q : Subgroup G}
    (hQ : Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3))
    (hK : k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥(alternatingGroup (Fin 7))) :
    ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
      img142 A (lB A) c Q =
        thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2)
    (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq φ card_P7 (Res5Gen.card_image_inf h h9) hfac
  have hcent := cent_of_rigid h φ' hφ'E fun τ hτ n hn hτn => aut_eq_one_A7 hτ hn hτn
  have d : Inner142 A c L := ⟨h, hAc, hK, hcent⟩
  obtain ⟨hV1, hV2, hN1, hN2⟩ := V_facts
  have hc1 : c1 ≠ 1 := fun h1 => by
    have : (c1 : Perm (Fin 7)) = 1 := congrArg Subtype.val h1
    exact absurd this (by decide +kernel)
  have hc2 : c2 ≠ 1 := fun h1 => by
    have : (c2 : Perm (Fin 7)) = 1 := congrArg Subtype.val h1
    exact absurd this (by decide +kernel)
  refine d.typesOne_of_model φ' hφ'E ![V1, V2] ![c1, c2] (fun i => by fin_cases i <;>
    simp [c1_mem_P7, c2_mem_P7]) (fun i => by fin_cases i <;> simp [hc1, hc2])
    (fun i => by fin_cases i <;> simp [theta_c1, theta_c2])
    (fun i => by fin_cases i <;> simp [hV1, hV2]) (fun i => by fin_cases i <;> simp [hN1, hN2])
    (fun Y hY3 hYP => ?_) ((IsPGroup.of_card (n := 2) (by rw [card_P7]; norm_num)).to_le
      centralizer_P7_le) hQ
  rcases le_V_of_invariant hY3 hYP with h1 | h2
  · exact ⟨0, h1⟩
  · exact ⟨1, h2⟩

end Res5TypesA7

end CFSG.RankThree.PartTwo.Sec14
