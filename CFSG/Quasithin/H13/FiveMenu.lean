module

public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.SteinbergBMQuasisimpleCenterlessImage
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Certificates.Certificate8064
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped IsMulCommutative

theorem qt13Excluded_of_alt12_2_2 {G : Type} [Group G] (h : Alt12_2_2 G) : QT13Excluded G := by
  rcases h with ⟨t, n, f, hf, -, hadm, hm⟩ | hU | hM22 | hM23 | hJ4
  · exact Or.inl ⟨t, n, f, hf, hadm, hm⟩
  · exact Or.inl ⟨.PSU, 5, 2, le_rfl, ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩, hU⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl hM22)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM23))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ4))))))

theorem lieModel_psl_of_mulEquiv_sl_zmod_two {Q : Type} [Group Q] {n : ℕ} (hn : 3 ≤ n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : LieModel Q .PSL n 2 1 := by
  have h2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by omega, fun h => ?_, fun h => ?_⟩, ZMod 2,
    inferInstance, inferInstance, by rw [h2, pow_one],
    ⟨e.trans (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two n (ZMod 2) h2).symm⟩⟩
  · have := congrArg Prod.fst h
    simp only at this
    omega
  · have := congrArg Prod.fst h
    simp only at this
    omega

theorem nonempty_mulEquiv_sl_two_of_lieModel {Q : Type} [Group Q] {n : ℕ}
    (h : LieModel Q .PSL n 2 1) : Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  exact ⟨e.trans (QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two n K
    (by rw [hK, pow_one]))⟩

theorem exists_mulEquiv_g2Derived_of_lieModel {Q : Type} [Group Q]
    (h : LieModel Q .PSU 3 3 1) :
    ∃ (K : Type) (_ : Field K), Nat.card K = 2 ∧
      Nonempty (Q ≃* ↥(⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ : Subgroup (ModGL .G2 K))) := by
  obtain ⟨e₁⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel h
  obtain ⟨e₂⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
    (EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (ZMod 2) (Nat.card_zmod 2))
  exact ⟨ZMod 2, inferInstance, Nat.card_zmod 2, ⟨e₁.trans e₂.symm⟩⟩

theorem alternatingGroup_nonabelian {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h03 : i₀ ≠ i₃ := by simp [i₀, i₃, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have h13 : i₁ ≠ i₃ := by simp [i₁, i₃, Fin.ext_iff]
  have h23 : i₂ ≠ i₃ := by simp [i₂, i₃, Fin.ext_iff]
  refine ⟨⟨Equiv.swap i₀ i₁ * Equiv.swap i₀ i₂, ?_⟩, ⟨Equiv.swap i₀ i₁ * Equiv.swap i₂ i₃, ?_⟩,
    fun h => ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h02]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h01,
      Equiv.Perm.sign_swap h23]
    rfl
  · have := congrArg (fun x : alternatingGroup (Fin n) => (x : Equiv.Perm (Fin n)) i₃) h
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply] at this
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm,
      Equiv.swap_apply_right, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h03.symm h23.symm,
      Equiv.swap_apply_of_ne_of_ne h03.symm h13.symm, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm] at this
    exact h12 this

theorem exists_orderOf_eq_three_alternatingGroup {n : ℕ} (hn : 3 ≤ n) :
    ∃ g : alternatingGroup (Fin n), orderOf g = 3 := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have hc : (Equiv.swap i₀ i₁ * Equiv.swap i₀ i₂).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  refine ⟨⟨_, hc.mem_alternatingGroup⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact hc.orderOf

theorem pCore_le_ker_of_surjective_alternating {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hn : 5 ≤ n) (φ : L →* alternatingGroup (Fin n)) (hφ : Function.Surjective φ) :
    CFSG.pCore 2 L ≤ φ.ker := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn)
  have hN : ((CFSG.pCore 2 L).map φ).Normal := CFSG.pCore_normal.map φ hφ
  rcases hN.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h2 : IsPGroup 2 ((CFSG.pCore 2 L).map φ) := CFSG.pCore_isPGroup.map φ
    obtain ⟨g, hg⟩ := exists_orderOf_eq_three_alternatingGroup (n := n) (by omega)
    have hgN : g ∈ (CFSG.pCore 2 L).map φ := h ▸ Subgroup.mem_top g
    obtain ⟨k, hk⟩ := h2 ⟨g, hgN⟩
    have hk' : g ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : 3 ∣ 2 ^ k := hg ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
    omega

theorem pCoreOf_le_inf_centralizer_of_surjective {G : Type} [Group G] [Finite G]
    {L V : Subgroup G} {n : ℕ} (hn : 5 ≤ n) (φ : ↥L →* ↥(alternatingGroup (Fin n)))
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L) :
    pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer (V : Set G) ∧
      L ⊓ Subgroup.centralizer (V : Set G) < L := by
  refine ⟨?_, lt_of_le_of_ne inf_le_left fun heq => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ CFSG.pCore 2 ↥L := by assumption
    have hyk : y ∈ φ.ker := pCore_le_ker_of_surjective_alternating hn φ hφ hy'
    rw [hker, Subgroup.mem_subgroupOf] at hyk
    exact ⟨y.2, hyk⟩
  · obtain ⟨g, hg⟩ := exists_orderOf_eq_three_alternatingGroup (n := n) (by omega)
    obtain ⟨x, rfl⟩ := hφ g
    have hx : x ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact (heq.symm ▸ x.2 : (x : G) ∈ L ⊓ Subgroup.centralizer (V : Set G)).2
    rw [MonoidHom.mem_ker] at hx
    rw [hx, orderOf_one] at hg
    omega

theorem five_selected_action_menu_producer
    (h1222 : Stmt12_2_2) : StmtFiveSelectedMenu := by
  intro G _ _ T L hs hnab hQ hT hnex hmax hf hq
  rcases h1222 G T hs hnab hQ hT with hA | h3
  · exact absurd (qt13Excluded_of_alt12_2_2 hA) hnex
  obtain ⟨-, ⟨V, hV⟩, hall⟩ := h3 L hmax hf hq
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hcomm, hmod⟩ := hall V hV
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have helem : IsElemAbelian 2 V := by
    refine ⟨hcomm, fun x hx => ?_⟩
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, hVLT hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | ⟨-, -, hA6, -⟩
  · exact Or.inl ⟨n, hn, lieModel_psl_of_mulEquiv_sl_zmod_two (by omega) e⟩
  · exact Or.inl ⟨3, Or.inl rfl, lieModel_psl_of_mulEquiv_sl_zmod_two le_rfl e⟩
  · exact Or.inl ⟨5, Or.inr (Or.inr rfl), lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e⟩
  · obtain ⟨hO2, hlt⟩ := pCoreOf_le_inf_centralizer_of_surjective hn5 φ hφ hker
    exact Or.inr (Or.inr (Or.inr ⟨n, hn5, hn8, V, hV.2.1, helem, hV.2.2.1, hO2, hlt, φ, hφ,
      hker⟩))
  · obtain ⟨hO2, hlt⟩ := pCoreOf_le_inf_centralizer_of_surjective (by norm_num) φ hφ hker
    exact Or.inr (Or.inr (Or.inr ⟨7, by norm_num, by norm_num, V, hV.2.1, helem, hV.2.2.1, hO2,
      hlt, φ, hφ, hker⟩))
  · exact Or.inr (Or.inl (exists_mulEquiv_g2Derived_of_lieModel hU))
  · exact Or.inr (Or.inr (Or.inl hA6))

theorem five_action_menu_to_candidate_quotients (hmenu : StmtFiveSelectedMenu) :
    StmtFiveCandidateMenu := by
  intro G _ _ T L hs hnab hQ hT hnex hmax hf hq
  rcases hmenu G T L hs hnab hQ hT hnex hmax hf hq with ⟨n, hn, h⟩ | ⟨K, _, hK, e⟩ | hA6 |
      ⟨n, hn5, hn8, V, -, -, -, -, -, φ, hφ, -⟩
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl ⟨K, inferInstance, hK, e⟩)
  · exact Or.inr (Or.inr ⟨6, by norm_num, by norm_num, hA6⟩)
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨n, hn5, hn8, ⟨e⟩⟩)

end CFSG.Quasithin.H13
