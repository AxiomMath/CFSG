module

public import CFSG.Quasithin.SteinbergCAStrictFixedSpaceSum
public import CFSG.Quasithin.H13.NQCoreWholeModuleTools
public import CFSG.LieType.Steinberg.Collection
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Quasithin.H13.NQRigidSeed
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.SteinbergCDOddResidualTools
public import CFSG.Quasithin.Vol2.Ch10StatementsB
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Walter.J1
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module CFSG.Open
open scoped IsMulCommutative

local notation "fixS" => CFSG.QuasithinUnique.Setup.Offender.fixSub
local notation "centS" => CFSG.QuasithinUnique.Setup.Offender.centSub

variable {G : Type} [Group G] [Finite G]

theorem exists_relIndex_eq_two_pow {B D : Subgroup G} (hB : IsPGroup 2 B) (hDB : D ≤ B)
    (C : Subgroup G) : ∃ e : ℕ, C.relIndex D = 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (hB.to_le hDB).exists_card_eq
  have hdvd : C.relIndex D ∣ Nat.card D := index_dvd_card _
  rw [ha] at hdvd
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨e, he⟩

theorem pow_lt_relIndex_of_iSup_conj {H V B : Subgroup G} (k : ℕ)
    (hUe : IsElemAbelian 2 (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom))
    (hB2 : IsPGroup 2 B)
    (hBV : ∀ h ∈ H, B ≤ normalizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G))
    (hbound : ∀ h ∈ H, ∀ D ≤ B,
      ¬ D ≤ centralizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) →
        (centralizer ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)).relIndex D ^ k <
          (centralizer (D : Set G)).relIndex (V.map (MulAut.conj h).toMonoidHom))
    (hBU : ¬ B ≤ centralizer
      (((⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) : Subgroup G) : Set G)) :
    (centralizer (((⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom) : Subgroup G) :
        Set G)).relIndex B ^ k <
      (centralizer (B : Set G)).relIndex (⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom)
    := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := ⨆ (h : G) (_ : h ∈ H), V.map (MulAut.conj h).toMonoidHom with hUdef
  have hVU : ∀ h ∈ H, V.map (MulAut.conj h).toMonoidHom ≤ U := fun h hh =>
    le_iSup₂_of_le (f := fun (g : G) (_ : g ∈ H) => V.map (MulAut.conj g).toMonoidHom) h hh
      le_rfl
  have : IsElementaryAbelian 2 ↥U :=
    { toIsMulCommutative := hUe.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun u =>
        Subtype.ext (by simpa using hUe.2 u u.2) }
  have : Finite (Additive ↥U) := inferInstanceAs (Finite ↥U)
  have : FiniteDimensional (ZMod 2) (Additive ↥U) := Module.Finite.of_finite
  have hBUn : B ≤ normalizer (U : Set G) := by
    intro b hb
    rw [LieType.Steinberg.mem_normalizer_iff_map_conj, hUdef, Subgroup.map_iSup]
    refine iSup_congr fun h => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hh => LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hBV h hh hb)
  set ρ : ↥B →* (Additive ↥U ≃ₗ[ZMod 2] Additive ↥U) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive ↥U)).toMonoidHom.comp
      ((mulAutToGL U).comp (U.normalizerMonoidHom.comp (inclusion hBUn))) with hρ
  have hρapply : ∀ (b : ↥B) (u : ↥U), ρ b (Additive.ofMul u) =
      Additive.ofMul (⟨(b : G) * u * (b : G)⁻¹,
        (mem_normalizer_iff.mp (hBUn b.2) u).mp u.2⟩ : ↥U) := fun b u => rfl
  set sub : Subgroup G → Submodule (ZMod 2) (Additive ↥U) := fun X =>
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (X.subgroupOf U)) with hsub
  have hmemsub : ∀ (X : Subgroup G) (u : ↥U), Additive.ofMul u ∈ sub X ↔ (u : G) ∈ X :=
    fun X u => Iff.rfl
  have hfix : ∀ (D : Subgroup ↥B) (u : ↥U), Additive.ofMul u ∈ fixS ρ D ↔
      (u : G) ∈ centralizer ((D.map B.subtype : Subgroup G) : Set G) := by
    intro D u
    rw [CFSG.QuasithinUnique.Setup.Offender.mem_fixSub, mem_centralizer_iff]
    constructor
    · rintro h _ ⟨d, hd, rfl⟩
      have h1 := congrArg (fun w : Additive ↥U => ((Additive.toMul w : ↥U) : G)) (h d hd)
      simp only [hρapply] at h1
      change (d : G) * u * (d : G)⁻¹ = u at h1
      calc ((d : ↥B) : G) * u = ((d : G) * u * (d : G)⁻¹) * d := by group
        _ = u * d := by rw [h1]
    · intro h d hd
      rw [hρapply]
      congr 1
      apply Subtype.ext
      change (d : G) * u * (d : G)⁻¹ = u
      have h2 : (d : G) * u = u * d := h _ ⟨d, hd, rfl⟩
      rw [h2, mul_inv_cancel_right]
  have hcent : ∀ (X : Subgroup G) (b : ↥B), X ≤ U →
      (b ∈ centS ρ (sub X) ↔ (b : G) ∈ centralizer (X : Set G)) := by
    intro X b hXU
    rw [CFSG.QuasithinUnique.Setup.Offender.mem_centSub, mem_centralizer_iff]
    constructor
    · intro h x hx
      have h1 := congrArg (fun w : Additive ↥U => ((Additive.toMul w : ↥U) : G))
        (h (Additive.ofMul ⟨x, hXU hx⟩) hx)
      simp only [hρapply] at h1
      change (b : G) * x * (b : G)⁻¹ = x at h1
      calc x * b = ((b : G) * x * (b : G)⁻¹) * b := by rw [h1]
        _ = b * x := by group
    · intro h w hw
      obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
      rw [hρapply]
      congr 1
      apply Subtype.ext
      change (b : G) * u * (b : G)⁻¹ = u
      rw [← h u hw, mul_inv_cancel_right]
  have hrelB : ∀ (X : Subgroup G) (D : Subgroup ↥B), X ≤ U →
      (centS ρ (sub X)).relIndex D = (centralizer (X : Set G)).relIndex (D.map B.subtype) := by
    intro X D hXU
    have h1 : centS ρ (sub X) = (centralizer (X : Set G)).subgroupOf B := by
      ext b
      rw [hcent X b hXU, mem_subgroupOf]
    rw [h1, ← relIndex_map_map_of_injective _ _ B.subtype_injective, subgroupOf_map_subtype,
      ← inf_relIndex_right, inf_assoc, inf_eq_right.mpr (map_subtype_le D), inf_relIndex_right]
  have hcardq : ∀ (X : Subgroup G) (D : Subgroup ↥B), X ≤ U →
      Nat.card (↥(sub X) ⧸ (fixS ρ D).comap (sub X).subtype) =
        (centralizer ((D.map B.subtype : Subgroup G) : Set G)).relIndex X := by
    intro X D hXU
    set C := centralizer ((D.map B.subtype : Subgroup G) : Set G) with hC
    have h1 := Submodule.card_eq_card_quotient_mul_card ((fixS ρ D).comap (sub X).subtype)
    have h2 : Nat.card ↥(sub X) = Nat.card ↥X :=
      Nat.card_congr
        { toFun := fun w => ⟨((Additive.toMul (w : Additive ↥U) : ↥U) : G),
            (hmemsub X _).mp w.2⟩
          invFun := fun x => ⟨Additive.ofMul ⟨x, hXU x.2⟩, (hmemsub X _).mpr x.2⟩
          left_inv := fun w => rfl
          right_inv := fun x => rfl }
    have h3 : Nat.card ↥((fixS ρ D).comap (sub X).subtype) =
        Nat.card ↥(C.subgroupOf X) := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun w => ⟨⟨((Additive.toMul (w : Additive ↥U) : ↥U) : G), w.1.2⟩, ?_⟩
          invFun := fun x => ⟨⟨Additive.ofMul ⟨x, hXU x.1.2⟩, x.1.2⟩, ?_⟩
          left_inv := fun w => rfl
          right_inv := fun x => rfl }
      · exact (hfix D _).mp w.2
      · exact (hfix D ⟨x, hXU x.1.2⟩).mpr x.2
    have h4 := (C.subgroupOf X).card_mul_index
    rw [h2, h3, ← h4, ← relIndex] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
  have hfinrank : ∀ (X : Subgroup G) (D : Subgroup ↥B), X ≤ U →
      2 ^ finrank (ZMod 2) (↥(sub X) ⧸ (fixS ρ D).comap (sub X).subtype) =
        (centralizer ((D.map B.subtype : Subgroup G) : Set G)).relIndex X := by
    intro X D hXU
    have : Finite ↥(sub X) := inferInstance
    have : Finite (↥(sub X) ⧸ (fixS ρ D).comap (sub X).subtype) :=
      Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
    have : Module.Finite (ZMod 2) (↥(sub X) ⧸ (fixS ρ D).comap (sub X).subtype) :=
      Module.Finite.of_finite
    rw [← hcardq X D hXU, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  set e := (Finite.equivFin ↥H).symm with he
  set W : Fin (Nat.card ↥H) → Submodule (ZMod 2) (Additive ↥U) := fun i =>
    sub (V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom) with hW
  have hWU : ∀ i, V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom ≤ U := fun i =>
    hVU _ (e i).2
  have hWtop : ⨆ i, W i = ⊤ := by
    have h1 : ⨆ i, (V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom).subgroupOf U = ⊤ := by
      apply map_injective U.subtype_injective
      rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
      refine le_antisymm (iSup_le fun i => map_subtype_le _) ?_
      refine iSup₂_le fun h hh => ?_
      have h2 : e (e.symm ⟨h, hh⟩) = ⟨h, hh⟩ := e.apply_symm_apply _
      refine le_iSup_of_le (e.symm ⟨h, hh⟩) ?_
      rw [h2, subgroupOf_map_subtype, inf_eq_left.mpr (hVU h hh)]
    have h3 : ⨆ i, W i = AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
        (⨆ i, (V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom).subgroupOf U)) := by
      rw [hW, (Subgroup.toAddSubgroup).map_iSup, (AddSubgroup.toZModSubmodule 2).map_iSup]
    rw [h3, h1]
    rfl
  have hbound' : ∀ (i : Fin (Nat.card ↥H)) (D : Subgroup ↥B), ¬ D ≤ centS ρ (W i) →
      k * Nat.log 2 ((centS ρ (W i)).relIndex D) <
        finrank (ZMod 2) (↥(W i) ⧸ (fixS ρ D).comap (W i).subtype) := by
    intro i D hD
    have hDB : D.map B.subtype ≤ B := map_subtype_le D
    have hnc : ¬ D.map B.subtype ≤
        centralizer ((V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom : Subgroup G) :
          Set G) := by
      rintro h
      refine hD fun d hd => ?_
      exact (hcent _ d (hWU i)).mpr (h ⟨d, hd, rfl⟩)
    have h1 := hbound _ (e i).2 _ hDB hnc
    rw [hrelB _ D (hWU i)]
    rw [← hfinrank _ D (hWU i)] at h1
    obtain ⟨a, ha⟩ := exists_relIndex_eq_two_pow hB2 hDB
      (centralizer ((V.map (MulAut.conj ((e i : ↥H) : G)).toMonoidHom : Subgroup G) : Set G))
    rw [ha, ← pow_mul] at h1
    rw [ha, Nat.log_pow (by norm_num), mul_comm]
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hBtop : ¬ (⊤ : Subgroup ↥B) ≤ centS ρ ⊤ := by
    intro h
    refine hBU fun b hb => ?_
    have h1 : (⟨b, hb⟩ : ↥B) ∈ centS ρ (sub U) := by
      have : sub U = ⊤ := by
        rw [eq_top_iff]
        intro w _
        obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
        exact (hmemsub U u).mpr u.2
      rw [this]
      exact h (mem_top _)
    exact (hcent U ⟨b, hb⟩ le_rfl).mp h1
  have hmain := SteinbergCA.strict_fixed_space_bounds_pass_from_invariant_generators_to_their_sum
    hB2 ρ W hWtop k hbound' ⊤ hBtop
  have hsubU : sub U = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u, rfl⟩ : ∃ u : ↥U, Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
    exact (hmemsub U u).mpr u.2
  have hBmap : (⊤ : Subgroup ↥B).map B.subtype = B := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hrel := hrelB U ⊤ le_rfl
  rw [hsubU, hBmap] at hrel
  rw [hrel] at hmain
  obtain ⟨a, ha⟩ := exists_relIndex_eq_two_pow hB2 le_rfl (centralizer (U : Set G))
  rw [ha, Nat.log_pow (by norm_num)] at hmain
  have hq : Nat.card (Additive ↥U ⧸ fixS ρ ⊤) = (centralizer (B : Set G)).relIndex U := by
    have h1 := Submodule.card_eq_card_quotient_mul_card (fixS ρ (⊤ : Subgroup ↥B))
    have h3 : Nat.card ↥(fixS ρ (⊤ : Subgroup ↥B)) =
        Nat.card ↥((centralizer (B : Set G)).subgroupOf U) := by
      refine Nat.card_congr
        { toFun := fun w => ⟨Additive.toMul (w : Additive ↥U), ?_⟩
          invFun := fun x => ⟨Additive.ofMul (x : ↥U), ?_⟩
          left_inv := fun w => rfl
          right_inv := fun x => rfl }
      · have h4 := (hfix ⊤ (Additive.toMul (w : Additive ↥U))).mp w.2
        rw [hBmap] at h4
        exact h4
      · refine (hfix ⊤ x).mpr ?_
        rw [hBmap]
        exact x.2
    have h4 := ((centralizer (B : Set G)).subgroupOf U).card_mul_index
    rw [show Nat.card (Additive ↥U) = Nat.card ↥U from rfl, h3, ← h4, ← relIndex] at h1
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
  have hq2 : 2 ^ finrank (ZMod 2) (Additive ↥U ⧸ fixS ρ ⊤) =
      (centralizer (B : Set G)).relIndex U := by
    have : Finite (Additive ↥U ⧸ fixS ρ (⊤ : Subgroup ↥B)) :=
      Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
    have : Module.Finite (ZMod 2) (Additive ↥U ⧸ fixS ρ (⊤ : Subgroup ↥B)) :=
      Module.Finite.of_finite
    rw [← hq, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [ha, ← hq2, ← pow_mul]
  exact Nat.pow_lt_pow_right (by norm_num) (by rw [mul_comm]; exact hmain)

end CFSG.Quasithin.H13.NQCore
