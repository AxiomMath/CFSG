module

public import CFSG.Quasithin.H13.Statements
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.CharacterTheory.Burnside
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LieType.SteinbergBRAutGL32
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33DcPG
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate19953
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13.A7

open Subgroup CFSG.Quasithin
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem isSolvable_of_natCard_eq [Finite G] {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem card_sylow_two_eq [Finite G] (S : Sylow 2 G) {a m : ℕ} (hG : Nat.card G = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [Sylow.card_eq_multiplicity, hG, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem card_dvd_factorial_index_of_simple [Finite G] [IsSimpleGroup G] {H : Subgroup G}
    (hH : H < ⊤) : Nat.card G ∣ H.index.factorial := by
  have h := H.index_normalCore_dvd_factorial_index
  have hbot : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ H.normalCore_le) (not_le_of_gt hH)
  rwa [hbot, Subgroup.index_bot] at h

theorem isSolvable_of_simple_card_three_sixty [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) {H : Subgroup G} (hH : H < ⊤) (h8 : 8 ∣ Nat.card H) :
    Group.IsSolvable H := by
  have hdvd : Nat.card H ∣ 360 := hG ▸ card_subgroup_dvd_card H
  have hne : Nat.card H ≠ 360 := fun h =>
    hH.ne ((card_eq_iff_eq_top H).1 (h.trans hG.symm))
  have hidx : Nat.card H * H.index = 360 := hG ▸ card_mul_index H
  have hcases : ∀ n < 361, n ∣ 360 → 8 ∣ n → n ≠ 360 → n < 60 ∨ n = 72 ∨ n = 120 := by
    decide +kernel
  rcases hcases _ (by have := Nat.le_of_dvd (by norm_num) hdvd; omega) hdvd h8 hne with
    h | h | h
  · exact CFSG.GroupTheory.groups_order_below_sixty_solvable h
  · exact isSolvable_of_natCard_eq (a := 3) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [h]; norm_num)
  · exfalso
    have h3 : H.index = 3 := by
      rw [h] at hidx
      omega
    have := card_dvd_factorial_index_of_simple hH
    rw [h3, hG] at this
    exact absurd this (by decide)

theorem index_eq_one_add_two_pow [Finite G] {T A : Subgroup G} (hTA : T ≤ A)
    (hT : IsPGroup 2 T) {D : G} (hDA : D ∈ A) (hDT : D ∉ T)
    (hA : ∀ g ∈ A, g ∈ T ∨ ∃ t₁ ∈ T, ∃ t₂ ∈ T, g = t₁ * D * t₂) :
    ∃ j : ℕ, (T.subgroupOf A).index = 1 + 2 ^ j ∧ 2 ^ j ≤ Nat.card T := by
  classical
  set T' := T.subgroupOf A with hT'
  have hT'2 : IsPGroup 2 T' := hT.of_equiv (subgroupOfEquivOfLe hTA).symm
  have hmk : ∀ a b : A, (QuotientGroup.mk a : A ⧸ T') = QuotientGroup.mk b ↔
      ((a : G)⁻¹ * b) ∈ T := by
    intro a b
    rw [QuotientGroup.eq, hT', mem_subgroupOf]
    simp
  have hsmul : ∀ (t : T') (b : A), t • (QuotientGroup.mk b : A ⧸ T') =
      QuotientGroup.mk ((t : A) * b) := fun _ _ => rfl
  set x₀ : A ⧸ T' := QuotientGroup.mk 1 with hx₀
  set x₁ : A ⧸ T' := QuotientGroup.mk ⟨D, hDA⟩ with hx₁
  set O := MulAction.orbit T' x₁ with hO
  have hcover : ∀ x : A ⧸ T', x = x₀ ∨ x ∈ O := by
    intro x
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective x
    rcases hA g hg with hgT | ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    · left
      rw [hx₀, hmk]
      simpa using T.inv_mem hgT
    · right
      refine ⟨⟨⟨t₁, hTA ht₁⟩, by rw [hT', mem_subgroupOf]; exact ht₁⟩, ?_⟩
      show _ • x₁ = _
      rw [hx₁, hsmul, hmk]
      simpa [mul_assoc] using ht₂
  have hnot : x₀ ∉ O := by
    rintro ⟨t, ht⟩
    change t • x₁ = x₀ at ht
    rw [hx₁, hx₀, hsmul, hmk] at ht
    have htT : ((t : A) : G) ∈ T := mem_subgroupOf.1 t.2
    apply hDT
    have h1 : ((t : A) : G) * D ∈ T := by
      have := T.inv_mem ht
      simpa using this
    have := T.mul_mem (T.inv_mem htT) h1
    simpa using this
  have hcard : Nat.card (A ⧸ T') = 1 + Nat.card O := by
    have huniv : (Set.univ : Set (A ⧸ T')) = insert x₀ O := by
      ext x
      simp only [Set.mem_univ, Set.mem_insert_iff, true_iff]
      exact hcover x
    rw [← Set.ncard_univ, huniv, Set.ncard_insert_of_notMem hnot, Nat.card_coe_set_eq,
      add_comm]
  obtain ⟨j, hj⟩ := hT'2.card_orbit x₁
  refine ⟨j, ?_, ?_⟩
  · rw [Subgroup.index, hcard, hj]
  · have h1 : Nat.card O ∣ Nat.card T' := by
      rw [hO, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
      exact index_dvd_card _
    rw [← hj]
    calc Nat.card O ≤ Nat.card T' := Nat.le_of_dvd Nat.card_pos h1
      _ = Nat.card T := Nat.card_congr (subgroupOfEquivOfLe hTA).toEquiv

theorem commutatorElement_mul_central_left {a b z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : z * b = b * z := (mem_center_iff.1 hz b).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * z * b * (z⁻¹ * a⁻¹) * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_central_right {a b z : G} (hz : z ∈ center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have hza : z * a⁻¹ = a⁻¹ * z := (mem_center_iff.1 hz a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc a * (b * z) * a⁻¹ * (z⁻¹ * b⁻¹) = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hza]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem map_mk_center_ne_top_of_perfect [Group.IsPerfect G] {H : Subgroup G} (hH : H < ⊤) :
    H.map (QuotientGroup.mk' (center G)) ≠ ⊤ := by
  intro hHb
  have hdec : ∀ a : G, ∃ h ∈ H, h⁻¹ * a ∈ center G := by
    intro a
    have : QuotientGroup.mk' (center G) a ∈ H.map (QuotientGroup.mk' (center G)) := by
      rw [hHb]
      exact mem_top _
    obtain ⟨h, hh, hha⟩ := this
    exact ⟨h, hh, QuotientGroup.eq.1 hha⟩
  have hcomm : commutator G ≤ H := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    obtain ⟨h₁, hh₁, hz₁⟩ := hdec a
    obtain ⟨h₂, hh₂, hz₂⟩ := hdec b
    have ha : a = h₁ * (h₁⁻¹ * a) := by group
    have hb : b = h₂ * (h₂⁻¹ * b) := by group
    rw [ha, hb, commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  rw [Group.IsPerfect.commutator_eq_top] at hcomm
  exact hH.ne (top_le_iff.1 hcomm)

end General

section U33

theorem u33_isSolvable_of_double_coset
    {A : Subgroup U33G} (hcard : Nat.card U33G = 6048)
    (hTA : u33Data.T ≤ A) {D : U33G} (hDA : D ∈ A) (hDT : D ∉ u33Data.T)
    (hA : ∀ g ∈ A, g ∈ u33Data.T ∨ ∃ t₁ ∈ u33Data.T, ∃ t₂ ∈ u33Data.T, g = t₁ * D * t₂) :
    Group.IsSolvable A := by
  have : Finite U33G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨j, hj, hj32⟩ := index_eq_one_add_two_pow hTA u33_syl.1 hDA hDT hA
  rw [u33_card_T] at hj32
  have hA' : Nat.card A = 32 * (1 + 2 ^ j) := by
    rw [← card_mul_index (u33Data.T.subgroupOf A), hj,
      Nat.card_congr (subgroupOfEquivOfLe hTA).toEquiv, u33_card_T]
  have hdvd : 32 * (1 + 2 ^ j) ∣ 6048 := hA' ▸ hcard ▸ card_subgroup_dvd_card A
  have hj5 : j ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hcases : ∀ i ≤ 5, 32 * (1 + 2 ^ i) ∣ 6048 → i = 1 ∨ i = 3 := by decide
  rcases hcases j hj5 hdvd with rfl | rfl
  · exact isSolvable_of_natCard_eq (a := 5) (b := 1) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hA']; norm_num)
  · exact isSolvable_of_natCard_eq (a := 5) (b := 2) Nat.prime_two Nat.prime_three
      (by norm_num) (by rw [hA']; norm_num)

theorem u33_proper_overgroup_isSolvable
    (hcard : Nat.card U33G = 6048) {H : Subgroup U33G}
    (hTH : u33Data.T ≤ H) (hH : H < ⊤) : Group.IsSolvable H := by
  have : Finite U33G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases u33Data.lattice H hTH with rfl | rfl | rfl | rfl
  · have := u33_syl.1.isNilpotent
    infer_instance
  · refine u33_isSolvable_of_double_coset hcard u33Data.T_le_A u33Data.D_ja
      u33Data.D_ja_notMem_T fun g hg => ?_
    obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_A_iff g).1 hg
    rcases hj with rfl | rfl
    · left
      rw [u33Data.D_zero, mul_one]
      exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
    · exact Or.inr ⟨_, u33Data.Tel_mem_T i₁, _, u33Data.Tel_mem_T i₂, rfl⟩
  · refine u33_isSolvable_of_double_coset hcard u33Data.T_le_B u33Data.D_jb
      u33Data.D_jb_notMem_T fun g hg => ?_
    obtain ⟨j, hj, i₁, i₂, rfl⟩ := (u33Data.mem_B_iff g).1 hg
    rcases hj with rfl | rfl
    · left
      rw [u33Data.D_zero, mul_one]
      exact u33Data.T.mul_mem (u33Data.Tel_mem_T i₁) (u33Data.Tel_mem_T i₂)
    · exact Or.inr ⟨_, u33Data.Tel_mem_T i₁, _, u33Data.Tel_mem_T i₂, rfl⟩
  · exact absurd rfl hH.ne

end U33

theorem five_model_proper_Sylow_two_overgroups_are_solvable
    {Q : Type} [Group Q] [Finite Q]
    (hQ : QT13Five Q) (S : Sylow 2 Q) {H : Subgroup Q} (hSH : (S : Subgroup Q) ≤ H)
    (hH : H < ⊤) : Group.IsSolvable H := by
  classical
  have hHQ : Nat.card H < Nat.card Q := by
    refine lt_of_le_of_ne (card_le_card_group H) fun h => hH.ne ?_
    exact (card_eq_iff_eq_top H).1 h
  have hSH8 : Nat.card S ∣ Nat.card H := card_dvd_of_le hSH
  rcases hQ with he | hL | he | ⟨hperf, hZ, hφ⟩ | hU
  ·
    obtain ⟨e⟩ := he
    have hQ60 : Nat.card Q = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable (hQ60 ▸ hHQ)
  ·
    obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
    have hQ168 : Nat.card Q = 168 := by
      rw [Nat.card_congr e.toEquiv, CFSG.LieType.SteinbergBR.AutGL32.card_GL32]
    have hS : Nat.card S = 8 :=
      card_sylow_two_eq S (a := 3) (m := 21) (by rw [hQ168]; norm_num) (by norm_num)
    have hdvd : Nat.card H ∣ 168 := hQ168 ▸ card_subgroup_dvd_card H
    have hcases : ∀ n < 169, n ∣ 168 → 8 ∣ n → n < 168 → n < 60 := by decide +kernel
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable
      (hcases _ (by have := Nat.le_of_dvd (by norm_num) hdvd; omega) hdvd (hS ▸ hSH8)
        (hQ168 ▸ hHQ))
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup Q := e.isSimpleGroup
    have hQ360 : Nat.card Q = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    have hS : Nat.card S = 8 :=
      card_sylow_two_eq S (a := 3) (m := 45) (by rw [hQ360]; norm_num) (by norm_num)
    exact isSolvable_of_simple_card_three_sixty hQ360 hH (hS ▸ hSH8)
  ·
    obtain ⟨φ⟩ := hφ
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hQZ : Nat.card (Q ⧸ center Q) = 360 := by rw [Nat.card_congr φ.toEquiv, hA6]
    have hQ : Nat.card Q = 1080 := by
      rw [card_eq_card_quotient_mul_card_subgroup (center Q), hQZ, hZ]
    have hS : Nat.card S = 8 :=
      card_sylow_two_eq S (a := 3) (m := 135) (by rw [hQ]; norm_num) (by norm_num)
    set π := QuotientGroup.mk' (center Q) with hπ
    set Hb := H.map π with hHb
    have hHbne : Hb ≠ ⊤ := map_mk_center_ne_top_of_perfect hH
    have hSb : Nat.card ((S : Subgroup Q).map π) = 8 := by
      rw [← relIndex_ker, QuotientGroup.ker_mk']
      have h1 := relIndex_mul_card (center Q) (S : Subgroup Q)
      have h2 : Nat.card ↥(center Q ⊓ (S : Subgroup Q)) = 1 := by
        have d1 : Nat.card ↥(center Q ⊓ (S : Subgroup Q)) ∣ 3 :=
          hZ ▸ card_dvd_of_le inf_le_left
        have d2 : Nat.card ↥(center Q ⊓ (S : Subgroup Q)) ∣ 8 :=
          hS ▸ card_dvd_of_le inf_le_right
        exact Nat.eq_one_of_dvd_coprimes (by norm_num) d1 d2
      rw [h2, mul_one, hS] at h1
      exact h1
    have h8 : 8 ∣ Nat.card Hb := hSb ▸ card_dvd_of_le (map_mono hSH)
    have hK := isSolvable_of_simple_card_three_sixty hA6
      (H := Hb.map φ.toMonoidHom) (lt_top_iff_ne_top.2 fun h => hHbne ?_) ?_
    · have : Group.IsSolvable Hb := Group.isSolvable_of_surjective
        (f := (Hb.equivMapOfInjective φ.toMonoidHom φ.injective).symm.toMonoidHom)
        (Hb.equivMapOfInjective φ.toMonoidHom φ.injective).symm.surjective
      have : Group.IsSolvable ((center Q).subgroupOf H) := Group.isSolvable_of_comm
        fun a b => Subtype.ext (Subtype.ext (mem_center_iff.1 (mem_subgroupOf.1 b.2) a))
      refine Group.isSolvable_of_ker_le_range ((center Q).subgroupOf H).subtype
        (π.subgroupMap H) fun x hx => ?_
      rw [range_subtype, mem_subgroupOf]
      rw [MonoidHom.mem_ker] at hx
      have hx' : π x = 1 := congrArg Subtype.val hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    · have := congrArg (Subgroup.map φ.symm.toMonoidHom) h
      rwa [map_map, map_top_of_surjective _ φ.symm.surjective, show φ.symm.toMonoidHom.comp
        φ.toMonoidHom = MonoidHom.id _ from by ext; simp, map_id] at this
    · rwa [card_map_of_injective φ.injective]
  ·
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hU
    have hQ : Nat.card Q = 6048 := by
      rw [Nat.card_congr eK.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
        Nat.prime_three (le_refl 1) hK (by norm_num : 2 ≤ 3),
        show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
      norm_num
    have eU : Q ≃* U33G := (CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU).some.trans
      u33Pres_mulEquiv_PSU3.some.symm
    have hU33 : Nat.card U33G = 6048 := by rw [← Nat.card_congr eU.toEquiv, hQ]
    have : Finite U33G := Nat.finite_of_card_ne_zero (by rw [hU33]; norm_num)
    set TU : Sylow 2 U33G := IsPGroup.toSylow u33_syl.1 u33_syl.2 with hTU
    have hS' : IsPGroup 2 ((S : Subgroup Q).map eU.toMonoidHom) := S.isPGroup'.map _
    have hS'i : ¬ 2 ∣ ((S : Subgroup Q).map eU.toMonoidHom).index := by
      rw [index_map_of_bijective eU.bijective]
      exact S.not_dvd_index
    set SU : Sylow 2 U33G := IsPGroup.toSylow hS' hS'i with hSU
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U33G SU TU
    set χ : Q ≃* U33G := eU.trans (MulAut.conj g) with hχ
    have hSχ : (S : Subgroup Q).map χ.toMonoidHom = u33Data.T := by
      have h1 : ((g • SU : Sylow 2 U33G) : Subgroup U33G) = u33Data.T := by
        rw [hg]
        rfl
      rw [Sylow.coe_subgroup_smul] at h1
      rw [← h1]
      ext x
      rw [mem_map, Subgroup.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨eU s, ⟨s, hs, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
    have hTH : u33Data.T ≤ H.map χ.toMonoidHom := by
      rw [← hSχ]
      exact map_mono hSH
    have hHlt : H.map χ.toMonoidHom < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => ?_
      have h2 : Nat.card (H.map χ.toMonoidHom) = Nat.card H :=
        card_map_of_injective (f := χ.toMonoidHom) χ.injective
      rw [h, card_top, hU33, ← hQ] at h2
      exact hHQ.ne h2.symm
    have := u33_proper_overgroup_isSolvable hU33 hTH hHlt
    exact Group.isSolvable_of_surjective
      (f := (H.equivMapOfInjective χ.toMonoidHom χ.injective).symm.toMonoidHom)
      (H.equivMapOfInjective χ.toMonoidHom χ.injective).symm.surjective

end CFSG.Quasithin.H13.A7
