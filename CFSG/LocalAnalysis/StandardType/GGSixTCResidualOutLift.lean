module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExcOut
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Sporadic.Co1.Module.TwoBCertBase
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import Certificates.Certificate3085Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.TCResidual

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms

private lemma two_pow_dvd_six_le_one {k : ℕ} (h : 2 ^ k ∣ 6) : k ≤ 1 := by
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
  have h4 : 4 ∣ 2 ^ (2 + j) := by
    rw [pow_add]
    exact dvd_mul_right 4 (2 ^ j)
  have h46 : 4 ∣ 6 := h4.trans h
  obtain ⟨c, hc⟩ := h46
  omega

theorem ggU62_out {G : Type} [Group G] [Finite G] {L : Subgroup G} (hperf : commutator ↥L = ⊤)
    (hmod : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1) :
    ∀ T' : Subgroup G, IsPGroup 2 T' → T' ≤ Subgroup.normalizer (L : Set G) →
      (∀ t ∈ T', ∀ l ∈ L, (∀ g ∈ L, t * g * t⁻¹ = l * g * l⁻¹) →
        t ∈ Subgroup.centralizer (L : Set G)) →
      Nat.card T' ≤ 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
  intro T' hT'2 hT'N hT'inn
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 :=
    hmod.statedClassicalModel (by decide)
  have hdvdOut64 : Nat.card (Outer (↥L ⧸ Subgroup.center ↥L)) ∣ 6 :=
    CFSG.ComponentClassification.Foote5.card_outer_dvd_six_of_psu_field_two (by norm_num) hmodel
  have hdvdOut : Nat.card (Outer ↥L) ∣ 6 :=
    (Subgroup.card_dvd_of_injective (centerQuotientOuterHom ↥L)
      (centerQuotient_outer_injective ↥L)).trans hdvdOut64
  let ν : ↥T' →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hT'N)
  let π : ↥T' →* Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp ν
  have hνcoe : ∀ (t : ↥T') (g : ↥L),
      ((ν t g : ↥L) : G) = (t : G) * (g : G) * (t : G)⁻¹ := by
    intro t g
    change ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hT'N t) g : ↥L) : G) =
      (t : G) * (g : G) * (t : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  have hmem : ∀ t : ↥T', t ∈ π.ker ↔ (t : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro t
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro ht
      have hinner : ν t ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
        (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
          (ν t)).mp ht
      change ν t ∈ (MulAut.conj : ↥L →* MulAut ↥L).range at hinner
      rw [MonoidHom.mem_range] at hinner
      obtain ⟨l, hl⟩ := hinner
      refine hT'inn (t : G) t.2 (l : G) l.2 ?_
      intro g hg
      have hconj : ((MulAut.conj l ⟨g, hg⟩ : ↥L) : G) = (l : G) * g * (l : G)⁻¹ := by
        rw [MulAut.conj_apply]
        rfl
      have heq : ((MulAut.conj l ⟨g, hg⟩ : ↥L) : G) = ((ν t ⟨g, hg⟩ : ↥L) : G) :=
        congrArg (fun f : MulAut ↥L => ((f ⟨g, hg⟩ : ↥L) : G)) hl
      rw [hconj, hνcoe t ⟨g, hg⟩] at heq
      exact heq.symm
    · intro ht
      refine (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)
        (ν t)).mpr ?_
      change ν t ∈ (MulAut.conj : ↥L →* MulAut ↥L).range
      rw [MonoidHom.mem_range]
      refine ⟨1, ?_⟩
      apply MulEquiv.ext
      intro g
      apply Subtype.ext
      have hc := Subgroup.mem_centralizer_iff.mp ht (g : G) g.2
      rw [MulAut.conj_apply, hνcoe t g]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, one_mul, inv_one,
        mul_one]
      rw [← hc]
      group
  have hker_map : π.ker.map T'.subtype = T' ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (hmem z).mp hz⟩
    · rintro ⟨hxT, hxC⟩
      exact ⟨⟨x, hxT⟩, (hmem ⟨x, hxT⟩).mpr hxC, rfl⟩
  have hker_card : Nat.card π.ker =
      Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective (K := π.ker) T'.subtype_injective, hker_map]
  have hπ2 : IsPGroup 2 ↥π.range :=
    hT'2.of_surjective π.rangeRestrict π.rangeRestrict_surjective
  have hdvd6 : Nat.card π.range ∣ 6 :=
    (Subgroup.card_subgroup_dvd_card π.range).trans hdvdOut
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hπ2.exists_card_eq
  have hk_le : k ≤ 1 := two_pow_dvd_six_le_one (hk ▸ hdvd6)
  have hrange : Nat.card π.range ≤ 2 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk_le
      _ = 2 := by norm_num
  have hcard := Subgroup.card_ker_mul_card_range π
  rw [hker_card] at hcard
  calc Nat.card T' = Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) *
        Nat.card π.range := hcard.symm
    _ ≤ Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) * 2 :=
        Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by ring

end CFSG.StandardType.TCResidual

end
