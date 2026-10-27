module

public import CFSG.Quasithin.H13.U3Confined
public import CFSG.Quasithin.H13.U3ElemNine
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import Certificates.Certificate110
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate19953
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped MatrixGroups

theorem exists_fusionBenderBorel {G : Type*} [Group G] [Finite G] (h : fusionIsBenderGroup G) :
    ∃ q k : ℕ, fusionBenderBorel G q k := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv G e.toEquiv
    exact ⟨_, _, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 f) := Finite.of_equiv G e.toEquiv
    exact ⟨_, _, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv G e.toEquiv
    exact ⟨_, _, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩

theorem le_of_fusionStronglyEmbedded {G : Type*} [Group G] [Finite G] {B E P : Subgroup G}
    (hB : fusionStronglyEmbedded B) (hP2 : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hPB : P ≤ B)
    (hEP : E ≤ normalizer (P : Set G)) : E ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro e he
  by_contra heB
  obtain ⟨c, hc⟩ := hB.2.2 e heB
  have hsub : P ≤ B ⊓ B.map (MulAut.conj e⁻¹).toMonoidHom := by
    refine le_inf hPB fun x hx => mem_map.2
      ⟨e * x * e⁻¹, hPB ((mem_normalizer_iff.1 (hEP he) x).1 hx), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h2 : 2 ∣ Nat.card P :=
    hP2.card_eq_or_dvd.resolve_left fun h => hP1 (Subgroup.card_eq_one.1 h)
  have h3 := h2.trans (Subgroup.card_dvd_of_le hsub)
  omega

theorem isSolvable_normalizer_of_sup {G : Type*} [Group G] [Finite G] {Q D : Subgroup G}
    (hQ : IsPGroup 2 Q) (hD : IsCyclic D) (hQD : Q ⊔ D = normalizer (Q : Set G)) :
    Group.IsSolvable (normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := normalizer (Q : Set G) with hB
  have hQB : Q ≤ B := le_normalizer
  have hDB : D ≤ B := hQD ▸ le_sup_right
  set Q' : Subgroup B := Q.subgroupOf B with hQ'
  have : Q'.Normal := Subgroup.normal_in_normalizer
  set D' : Subgroup B := D.subgroupOf B with hD'
  have hD'c : IsCyclic D' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDB).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDB).symm.surjective
  have htop : Q' ⊔ D' = ⊤ := by
    rw [hQ', hD', ← Subgroup.subgroupOf_sup hQB hDB, hQD, Subgroup.subgroupOf_self]
  have hmap : D'.map (QuotientGroup.mk' Q') = ⊤ := by
    have h1 : (Q' ⊔ D').map (QuotientGroup.mk' Q') = ⊤ := by
      rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Q')]
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff Q').2 (QuotientGroup.ker_mk' Q').ge,
      bot_sup_eq] at h1
  have hsurj : Function.Surjective ((QuotientGroup.mk' Q').comp D'.subtype) := by
    intro y
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top y)
    exact ⟨⟨d, hd⟩, rfl⟩
  have : IsCyclic (↥B ⧸ Q') := isCyclic_of_surjective _ hsurj
  have hsq : Group.IsSolvable (↥B ⧸ Q') :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := ↥B ⧸ Q')).comm a b
  have hsQ : Group.IsSolvable Q' := by
    have := (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQB).symm).isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range Q'.subtype (QuotientGroup.mk' Q')
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

theorem exists_lift_exponent_three {L : Type*} [Group L] [Finite L] {R : Subgroup L} [R.Normal]
    (hR : IsPGroup 2 R) {A : Subgroup (L ⧸ R)} (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hA9 : 9 ∣ Nat.card A) : ∃ S : Subgroup L, 9 ∣ Nat.card S ∧ ∀ s ∈ S, s ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' R
  set D := A.comap π with hD
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 D) := inferInstance
  refine ⟨(S₀ : Subgroup D).map D.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective D.subtype_injective]
    have hDA : 9 ∣ Nat.card D := by
      have hmap : D.map π = A := Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective R) A
      exact hA9.trans (hmap ▸ Subgroup.card_map_dvd D π)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 S₀.isPGroup'
    have hidx : ¬ 3 ∣ (S₀ : Subgroup D).index := S₀.not_dvd_index
    have hcop : Nat.Coprime 9 (S₀ : Subgroup D).index :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hidx)
    have h1 := (S₀ : Subgroup D).card_mul_index
    rw [← h1] at hDA
    exact hcop.dvd_of_dvd_mul_right hDA
  · rintro _ ⟨s, hs, rfl⟩
    have hsA : π (s : L) ∈ A := s.2
    have h1 : π ((s : L) ^ 3) = 1 := by rw [map_pow, hA3 _ hsA]
    have hR3 : (s : L) ^ 3 ∈ R := by
      rwa [← QuotientGroup.ker_mk' R, MonoidHom.mem_ker]
    obtain ⟨n, hn⟩ := hR ⟨_, hR3⟩
    obtain ⟨k, hk⟩ := S₀.isPGroup' ⟨s, hs⟩
    have hn' : ((s : L) ^ 3) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have hk' : ((s : L) ^ 3) ^ 3 ^ k = 1 := by
      have h := congrArg (fun x : (S₀ : Subgroup D) => ((x : D) : L) ^ 3) hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one, one_pow] at h
      rw [← pow_mul, mul_comm, pow_mul]
      exact h
    have hcop : Nat.Coprime (2 ^ n) (3 ^ k) := Nat.Coprime.pow n k (by norm_num)
    have hord := (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hn') hcop).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one hk')
    exact orderOf_eq_one_iff.1 hord

theorem not_isCyclic_of_exponent_three {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (h9 : 9 ∣ Nat.card S) (h3 : ∀ s ∈ S, s ^ 3 = 1) : ¬ IsCyclic S := by
  intro hc
  have hexp : Monoid.exponent S ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun s => Subtype.ext (by simpa using h3 _ s.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  have hpos : 0 < Nat.card S := Nat.card_pos
  have := Nat.le_of_dvd (by norm_num) hexp
  obtain ⟨c, hc⟩ := h9
  omega

theorem unique_models_exclude_U3_sections
    : UniqueModelsExcludeU3Sections := by
  intro G _ _ T E L R _ hsimple hnonab hT hTE hO2 hLE hR2 hLie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hLie
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  let e : ↥L ⧸ R ≃* U33G := e1.trans e2.symm
  have h32 : 32 ∣ Nat.card G := by
    have h1 : Nat.card (↥L ⧸ R) = 6048 := (Nat.card_congr e.toEquiv).trans card_u33G
    have h2 : Nat.card (↥L ⧸ R) ∣ Nat.card G :=
      (Subgroup.card_quotient_dvd_card R).trans (Subgroup.card_subgroup_dvd_card L)
    rw [h1] at h2
    exact (show 32 ∣ 6048 by norm_num).trans h2
  have hLns : ¬ Group.IsSolvable L := by
    intro hs
    have hsU : Group.IsSolvable U33G :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
    obtain ⟨x, y, hxy⟩ := u33Pres_nonabelian
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 hsU x y)
  have hEns : ¬ Group.IsSolvable E := fun hs =>
    hLns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLE))
  refine ⟨fun hB => ?_, fun hS => ?_⟩
  ·
    obtain ⟨q, k, hBB⟩ := exists_fusionBenderBorel hB
    obtain ⟨hSE, ⟨D, hDc, -, -, hsup⟩, -⟩ := hBB (hT.1.toSylow hT.2)
    rw [IsPGroup.toSylow_coe] at hSE hsup
    have hPT : pCoreOf 2 E ≤ T :=
      QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT hTE)
    have hEB : E ≤ normalizer (T : Set G) :=
      le_of_fusionStronglyEmbedded hSE (LieType.BorelTits.pCoreOf_isPGroup 2 E) hO2
        (hPT.trans le_normalizer) (LieType.BorelTits.le_normalizer_pCoreOf 2 E)
    have := isSolvable_normalizer_of_sup hT.1 hDc hsup
    exact hEns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hEB))
  · rcases hS with ⟨p, hp, hp7, -, ⟨eG⟩⟩ | ⟨⟨eG⟩⟩ | ⟨⟨eG⟩⟩
    ·
      have : Fact p.Prime := ⟨hp⟩
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hpodd : Odd p := hp.odd_of_ne_two (by omega)
      have hdata := CFSG.Semidihedral.OddProjectiveCoverKernel.odd_projective_linear_two_Sylow_data
        (K := ZMod p) hp hpodd le_rfl (by rw [Nat.card_zmod, pow_one])
      have hcyc3 := hdata.2.2.2.2.2.2 3 Nat.prime_three (by decide) (by omega)
      let φ : G ≃* CFSG.Semidihedral.OddProjectiveCoverKernel.S (ZMod p) :=
        eG.trans (CFSG.Semidihedral.ProjectiveSL2Cover.scalarProjectiveEquivNative (ZMod p) 2).symm
      obtain ⟨⟨A, hAe, hA9⟩, -⟩ := unitary_three_field_three_elementary_nine_subgroup hLie
      have hA3 : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
      obtain ⟨S, hS9, hS3⟩ := exists_lift_exponent_three hR2 hA3 (by rw [hA9])
      set SG := S.map L.subtype with hSG
      have hSG9 : 9 ∣ Nat.card SG := by
        rw [hSG, Subgroup.card_map_of_injective L.subtype_injective]
        exact hS9
      have hSG3 : ∀ x ∈ SG, x ^ 3 = 1 := by
        rintro _ ⟨s, hs, rfl⟩
        rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hS3 s hs, Subgroup.coe_one]
      have hSGp : IsPGroup 3 SG := fun x => ⟨1, Subtype.ext (by simpa using hSG3 _ x.2)⟩
      obtain ⟨P, hP⟩ := (hSGp.map φ.toMonoidHom).exists_le_sylow
      have := hcyc3 P
      have : IsCyclic (SG.map φ.toMonoidHom) := isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom (MulEquiv.surjective _)
      have : IsCyclic SG := isCyclic_of_surjective
        (SG.equivMapOfInjective φ.toMonoidHom φ.injective).symm.toMonoidHom
        (MulEquiv.surjective _)
      exact not_isCyclic_of_exponent_three hSG9 hSG3 this
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) =
          3 ^ (3 * (3 - 1) / 2) * ∏ j ∈ Finset.Icc 2 3, (3 ^ j - 1) :=
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linear_order (K := ZMod 3) 3 3
          (Nat.card_zmod 3) (by norm_num)).2.1
      have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 5616 := by
        rw [hSL]
        decide
      have hdvd : Nat.card G ∣ 5616 := by
        rw [Nat.card_congr eG.toEquiv, ← hSL']
        exact Subgroup.card_quotient_dvd_card _
      have := h32.trans hdvd
      norm_num at this
    ·
      have hM : Nat.card G = 7920 := by
        rw [Nat.card_congr eG.toEquiv,
          ← Nat.card_congr CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.toEquiv]
        exact CFSG.Semidihedral.GL2Recognition.card_statedM11
      rw [hM] at h32
      norm_num at h32

end CFSG.Quasithin.H13.U3
