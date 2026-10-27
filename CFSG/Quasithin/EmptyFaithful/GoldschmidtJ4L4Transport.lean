module

public import CFSG.Quasithin.EmptyFaithful.A38c8Defs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
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
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Open CFSG.LieType.BorelTits

abbrev HasA8 {Λ : Type} [Group Λ] (B : Subgroup Λ) : Prop :=
  Nonempty (CFSG.Quasithin.ModO2 B ≃* alternatingGroup (Fin 8))

theorem pCoreOf_map_injective {Λ Γ : Type*} [Group Λ] [Group Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (B : Subgroup Λ) :
    pCoreOf 2 (B.map φ) = (pCoreOf 2 B).map φ := by
  unfold pCoreOf
  let ε : B ≃* B.map φ := Subgroup.equivMapOfInjective B φ hφ
  rw [← map_pCore_mulEquiv 2 ε, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem hasA8_map_iff {Λ Γ : Type} [Group Λ] [Group Γ] (φ : Λ →* Γ) (hφ : Function.Injective φ)
    (B : Subgroup Λ) : HasA8 (B.map φ) ↔ HasA8 B := by
  let ε : ↥B ≃* ↥(B.map φ) := Subgroup.equivMapOfInjective B φ hφ
  have hε : (CFSG.pCore 2 ↥B).map ε.toMonoidHom = CFSG.pCore 2 ↥(B.map φ) :=
    CFSG.pCore_map_iso 2 ε
  let e : CFSG.Quasithin.ModO2 B ≃* CFSG.Quasithin.ModO2 (B.map φ) :=
    QuotientGroup.congr _ _ ε hε
  exact ⟨fun ⟨f⟩ => ⟨e.trans f⟩, fun ⟨f⟩ => ⟨e.symm.trans f⟩⟩

theorem exists_hom_of_hasA8 {Λ : Type} [Group Λ] {B : Subgroup Λ} (h : HasA8 B) :
    ∃ f : ↥B →* alternatingGroup (Fin 8), Function.Surjective f ∧ f.ker = CFSG.Open.pCore 2 ↥B := by
  obtain ⟨e⟩ := h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥B)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · try with_reducible rfl
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff x

theorem ker_eq_pCore_of_alt8 {Γ : Type*} [Group Γ] [Finite Γ]
    (g : Γ →* alternatingGroup (Fin 8)) (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker) :
    g.ker = CFSG.Open.pCore 2 Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  apply le_antisymm
  · exact le_pCore 2 (MonoidHom.normal_ker g) hker
  · have hn : ((CFSG.Open.pCore 2 Γ).map g).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2).map g hg
    have hp : IsPGroup 2 ((CFSG.Open.pCore 2 Γ).map g) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map g
    have := hn
    rcases hsimple.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCore 2 Γ).map g) with h | h
    · intro x hx
      have : g x ∈ (CFSG.Open.pCore 2 Γ).map g := Subgroup.mem_map_of_mem g hx
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      rw [h] at hp
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      rw [Subgroup.card_top, card_alt8] at hk
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk]
        norm_num
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega

theorem innerOnModO2_map_iff {Λ Γ : Type} [Group Λ] [Group Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (B : Subgroup Λ) (x : Λ) :
    A38c8.InnerOnModO2 (B.map φ) (φ x) ↔ A38c8.InnerOnModO2 B x := by
  unfold A38c8.InnerOnModO2
  rw [pCoreOf_map_injective φ hφ B]
  constructor
  · rintro ⟨b', ⟨b, hb, rfl⟩, h⟩
    refine ⟨b, hb, fun y hy => ?_⟩
    have := h (φ y) ⟨y, hy, rfl⟩
    have e : (φ x * φ y * (φ x)⁻¹)⁻¹ * (φ b * φ y * (φ b)⁻¹) =
        φ ((x * y * x⁻¹)⁻¹ * (b * y * b⁻¹)) := by simp [map_mul, map_inv]
    rw [e] at this
    exact (Subgroup.mem_map_iff_mem hφ).1 this
  · rintro ⟨b, hb, h⟩
    refine ⟨φ b, ⟨b, hb, rfl⟩, fun y' hy' => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hy'
    have e : (φ x * φ y * (φ x)⁻¹)⁻¹ * (φ b * φ y * (φ b)⁻¹) =
        φ ((x * y * x⁻¹)⁻¹ * (b * y * b⁻¹)) := by simp [map_mul, map_inv]
    rw [e]
    exact ⟨_, h y hy, rfl⟩

end CFSG.Quasithin.J4L4
