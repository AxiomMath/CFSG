module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xh_exists_lift {L B : Subgroup G} (hBN : B ≤ normalizer (L : Set G))
    (hB : Odd (Nat.card B)) (l : ↥L)
    (hl : ∀ b : ↥(normalizer (L : Set G)), (b : G) ∈ B →
      UC6S846.rhoL L b (QuotientGroup.mk l) = QuotientGroup.mk l) :
    ∃ c : ↥L, (c : G) ∈ centralizer (B : Set G) ∧
      (QuotientGroup.mk c : Bar2 L) = QuotientGroup.mk l := by
  let : MulDistribMulAction ↥B ↥L :=
    MulDistribMulAction.compHom ↥L (L.normalizerMonoidHom.comp (Subgroup.inclusion hBN))
  have hsmul : ∀ (b : ↥B) (y : ↥L), ((b • y : ↥L) : G) = (b : G) * (y : G) * (b : G)⁻¹ :=
    fun _ _ => rfl
  have hNinv : CFSG.IsInvariant ↥B ↥L (CFSG.pCore 2 ↥L) := by
    refine ⟨fun b y => ?_⟩
    have he : b • y = (L.normalizerMonoidHom ⟨b, hBN b.2⟩) y := rfl
    have hfix : (CFSG.pCore 2 ↥L).map (L.normalizerMonoidHom ⟨b, hBN b.2⟩).toMonoidHom =
        CFSG.pCore 2 ↥L := CFSG.pCore_map_iso 2 _
    rw [he]
    constructor
    · intro hy
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    · intro hy
      rw [← hfix] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      rw [← (L.normalizerMonoidHom ⟨b, hBN b.2⟩).injective hyy]
      exact hy'
  have hNp : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hNsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := by
    haveI := hNp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥(CFSG.pCore 2 ↥L)) := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hB)
  obtain ⟨c, hc, hcl⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed (CFSG.pCore 2 ↥L) hNinv
    hNsolv hcop l (fun b => by
      have h := hl ⟨b, hBN b.2⟩ b.2
      rw [UC6S846.rhoL_mk] at h
      exact QuotientGroup.eq.mp h.symm)
  refine ⟨c, ?_, QuotientGroup.eq.mpr hcl⟩
  rw [mem_centralizer_iff]
  intro b hb
  have h := congrArg Subtype.val (hc ⟨b, hb⟩)
  rw [hsmul] at h
  calc b * (c : G) = b * c * b⁻¹ * b := by group
    _ = c * b := by rw [h]

end CFSG.LocalAnalysis.UniquenessCase.UC22
