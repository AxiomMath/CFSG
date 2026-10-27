module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_card_starImg_mul {K Y : Subgroup G} (hY : Y ≤ K) :
    Nat.card ↥(starImg K Y) * Nat.card ↥(Y ⊓ pCoreOf 2 K) = Nat.card ↥Y := by
  let Y' : Subgroup ↥K := Y.subgroupOf K
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let ψ : ↥Y' →* Bar2 K := π.comp Y'.subtype
  have hrange : ψ.range = starImg K Y := by
    show (π.comp Y'.subtype).range = (Y.subgroupOf K).map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card ↥ψ.ker = Nat.card ↥(Y ⊓ pCoreOf 2 K) := by
    have hker_eq : ψ.ker = ((Y ⊓ pCoreOf 2 K).subgroupOf K).subgroupOf Y' := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro hy
        have hψ : ψ y = 1 := (MonoidHom.mem_ker).mpr hy
        have hπ : π (y : ↥K) = 1 := by
          change (π.comp Y'.subtype) y = 1
          simpa only [ψ] using hψ
        have hpcore : (y : ↥K) ∈ CFSG.pCore 2 ↥K := by
          have hmem : (y : ↥K) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
            rw [MonoidHom.mem_ker]
            simpa only [π] using hπ
          rwa [QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K)] at hmem
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp y.2,
          Subgroup.mem_map.mpr ⟨(y : ↥K), hpcore, rfl⟩⟩
      · intro hy
        obtain ⟨-, hpcore⟩ := Subgroup.mem_inf.mp hy
        obtain ⟨o, ho, hoo⟩ := Subgroup.mem_map.mp hpcore
        have hoy : o = (y : ↥K) := Subtype.ext hoo
        have hπo : π o = 1 := by
          have hmem : o ∈ CFSG.pCore 2 ↥K := ho
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K)] at hmem
          simpa only [π] using (MonoidHom.mem_ker).mp hmem
        have hπ : π (y : ↥K) = 1 := by rw [← hoy]; exact hπo
        rw [MonoidHom.mem_ker]
        change (π.comp Y'.subtype) y = 1
        simpa using hπ
    rw [hker_eq]
    have hle1 : (Y ⊓ pCoreOf 2 K).subgroupOf K ≤ Y' := by
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact (Subgroup.mem_inf.mp hw).1
    calc Nat.card ↥(((Y ⊓ pCoreOf 2 K).subgroupOf K).subgroupOf Y')
        = Nat.card ↥((Y ⊓ pCoreOf 2 K).subgroupOf K) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv
      _ = Nat.card ↥(Y ⊓ pCoreOf 2 K) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            ((inf_le_left : Y ⊓ pCoreOf 2 K ≤ Y).trans hY)).toEquiv
  have hcardY' : Nat.card ↥Y' = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hmain := Subgroup.card_ker_mul_card_range ψ
  rw [hrange, hker, hcardY'] at hmain
  rw [mul_comm] at hmain
  exact hmain

theorem s16c1_G47_card_starImg_le {K K' Y : Subgroup G} (hYK : Y ≤ K) (hYK' : Y ≤ K')
    (h : Y ⊓ pCoreOf 2 K' ≤ pCoreOf 2 K) :
    Nat.card ↥(starImg K Y) ≤ Nat.card ↥(starImg K' Y) := by
  have h1 := s16c1_G47_card_starImg_mul hYK
  have h2 := s16c1_G47_card_starImg_mul hYK'
  have h3 : Nat.card ↥(Y ⊓ pCoreOf 2 K') ≤ Nat.card ↥(Y ⊓ pCoreOf 2 K) :=
    Subgroup.card_le_of_le (le_inf inf_le_left h)
  have hpos : 0 < Nat.card ↥(Y ⊓ pCoreOf 2 K') := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h4 : Nat.card ↥(starImg K' Y) * Nat.card ↥(Y ⊓ pCoreOf 2 K') <
      Nat.card ↥(starImg K Y) * Nat.card ↥(Y ⊓ pCoreOf 2 K') :=
    Nat.mul_lt_mul_of_pos_right hlt hpos
  have h5 : Nat.card ↥(starImg K Y) * Nat.card ↥(Y ⊓ pCoreOf 2 K') ≤
      Nat.card ↥(starImg K Y) * Nat.card ↥(Y ⊓ pCoreOf 2 K) := Nat.mul_le_mul_left _ h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
