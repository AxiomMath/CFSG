module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Gen

variable {G : Type} [Group G]

@[expose] def ggFixG (Bs : Subgroup G) (t : MulAut ↥Bs) : Subgroup G :=
  (ggFix t).map Bs.subtype

@[expose] def GGRootCompGenAvoiding (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∀ ρ : MulAut ↥Bs, X = ⨆ (t : MulAut ↥Bs) (Jt : Subgroup G)
    (_ : t ≠ ρ ∧ GGIsReflection p t ∧ t ∈ ggInduced Jt Bs ∧ Jt ≤ X ∧
      Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) ∧
      IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G)))), Jt

@[expose] def GGHypCompInG0 [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    Prop :=
  ∃ ρ : MulAut ↥Bs, ∀ (t : MulAut ↥Bs) (Jt : Subgroup G), t ≠ ρ → GGIsReflection p t →
    t ∈ ggInduced Jt Bs → Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) →
    IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))) →
    Jt ≤ ggG0 p B x L D J

section Transport

variable {Bs : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))

theorem GGIsReflection.conj' {p : ℕ} {φ : MulAut ↥Bs} (h : GGIsReflection p φ)
    (ψ : MulAut ↥Bs) : GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

include hg in
theorem ggConjAut_conj_apply (t : MulAut ↥Bs) (b : ↥Bs) :
    (((ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) b : ↥Bs) : G) =
      g * (t ⟨g⁻¹ * b * g, ((ggConjAut Bs hg)⁻¹ b).2⟩ : G) * g⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply]
  rfl

include hg in
theorem mem_ggInduced_map_conj {t : MulAut ↥Bs} {Jt : Subgroup G} (ht : t ∈ ggInduced Jt Bs) :
    ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹ ∈
      ggInduced (Jt.map (MulAut.conj g).toMonoidHom) Bs := by
  obtain ⟨k, hkJ, hkN, hk⟩ := ht
  refine ⟨g * k * g⁻¹, ⟨k, hkJ, rfl⟩, ?_, fun b => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hkN) (Subgroup.inv_mem _ hg)
  · rw [ggConjAut_conj_apply hg, hk]
    simp only
    group

include hg in
theorem ggFixG_conj (t : MulAut ↥Bs) :
    ggFixG Bs (ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) =
      (ggFixG Bs t).map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [ggFixG, Subgroup.mem_map, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨g⁻¹ * b * g, ⟨(ggConjAut Bs hg)⁻¹ b, ?_, rfl⟩, by group⟩
    change t ((ggConjAut Bs hg)⁻¹ b) = (ggConjAut Bs hg)⁻¹ b
    have hb' : (ggConjAut Bs hg) (t ((ggConjAut Bs hg)⁻¹ b)) = b := hb
    have h3 : (ggConjAut Bs hg)⁻¹ ((ggConjAut Bs hg) (t ((ggConjAut Bs hg)⁻¹ b))) =
        (ggConjAut Bs hg)⁻¹ b := by rw [hb']
    rwa [MulAut.inv_apply_self] at h3
  · rintro ⟨z, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨ggConjAut Bs hg b, ?_, rfl⟩
    change (ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) (ggConjAut Bs hg b) = ggConjAut Bs hg b
    have hb' : t b = b := hb
    simp [MulAut.mul_apply, hb']

theorem centralizer_map_conj (S : Subgroup G) (g : G) :
    Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h s hs
    have := h (g * s * g⁻¹) (by rw [show g⁻¹ * (g * s * g⁻¹) * g = s by group]; exact hs)
    calc s * (g⁻¹ * y * g) = g⁻¹ * ((g * s * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * s * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * s := by group
  · intro h s hs
    have := h (g⁻¹ * s * g) hs
    calc s * y = g * ((g⁻¹ * s * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = y * s := by group

end Transport

theorem normalizer_le_normalizer_ggG0 [Finite G] {p : ℕ} (hp : p.Prime) {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hH : GGHypCompInG0 p B Bs x L D J)
    (hL : GGRootCompGenAvoiding p Bs L)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGRootCompGenAvoiding p Bs K) :
    Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  intro g hg
  obtain ⟨ρ, hρ⟩ := hH
  set c := ggConjAut Bs hg
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  have key : ∀ X : Subgroup G, GGRootCompGenAvoiding p Bs X →
      X ≤ (ggG0 p B x L D J).comap f := by
    intro X hX
    rw [hX (c⁻¹ * ρ * c)]
    refine iSup_le fun t => iSup_le fun Jt => iSup_le fun ⟨hne, hr, hind, _, hJC, hpc⟩ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine hρ (c * t * c⁻¹) (Jt.map f) ?_ (hr.conj' c) (mem_ggInduced_map_conj hg hind) ?_ ?_
    · intro h
      apply hne
      rw [← h]
      group
    · rw [ggFixG_conj hg, centralizer_map_conj]
      exact Subgroup.map_mono hJC
    · rw [ggFixG_conj hg, centralizer_map_conj]
      exact (CFSG.ComponentClassification.Burgoyne.isPComponent_subgroupOf_map_iff p hp hf).mp hpc
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have hle : ggG0 p B x L D J ≤ (ggG0 p B x L D J).comap f := by
    refine sup_le (key L hL) (iSup_le fun y => iSup_le fun K => iSup_le fun hyK => ?_)
    exact key K (hK y K hyK)
  have := hle hn
  simpa [f, Subgroup.mem_comap, MulAut.conj_apply] using this

end Gen

@[expose] def GGHypG0Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        GGHypCompInG0 p B Bs x L D J

@[expose] def GGRootGenLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        GGRootCompGenAvoiding p Bs L

@[expose] def GGRootGenNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGRootCompGenAvoiding p Bs K

theorem ggCorFiveTwentyQFourWeylInput_of_rootGen (hH : GGHypG0Input) (hL : GGRootGenLInput)
    (hK : GGRootGenNbrInput) : GGCorFiveTwentyQFourWeylInput :=
  fun G _ _ p B Bs x L D J hHyp hq hN hW =>
    normalizer_le_normalizer_ggG0 hHyp.1.1.2.2.2.2.2.1.1 (hH G p B Bs x L D J hHyp hq hN hW)
      (hL G p B Bs x L D J hHyp hq hN hW) (hK G p B Bs x L D J hHyp hq hN hW)

theorem ggCorFiveTwentyInput_of_rootGen (hR : GGCorFiveTwentyResidualInput)
    (hN : GGCorFiveTwentyQFourNonWeylInput) (hH : GGHypG0Input) (hL : GGRootGenLInput)
    (hK : GGRootGenNbrInput) : GGCorFiveTwentyInput :=
  ggCorFiveTwentyInput_of_split hR
    (ggCorFiveTwentyQFourInput_of_weyl hN (ggCorFiveTwentyQFourWeylInput_of_rootGen hH hL hK))

end CFSG.StandardType
