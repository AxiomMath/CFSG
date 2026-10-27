module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGHyper
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmegaPlanes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGOmegaE
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal.Spin

local notation "ι₆" => Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

private theorem s1614_ao_charP (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    CharP K 2 := by
  haveI := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by exact_mod_cast h)

theorem s1614_hyp2iii_omega (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    S1614Hyp2iii (FFModel.nat (StatedOmega (StatedQuadMinus 3 K b c))) := by
  haveI : CharP K 2 := s1614_ao_charP K hK
  rw [← coe_quadMinus 3 K b c]
  intro H hkH hHs h2
  obtain ⟨s, hs, hH⟩ := s1614_hyperplane _ K hK h2
  obtain ⟨a, a', x, x', hF, has, ha's⟩ := s1614_om_planes K hK b c hbc hs
  obtain ⟨E', hEΩ, ⟨hcomm, hexp⟩, hE9, hstab⟩ := s1614_om_E (quadMinus 3 K b c) hF
  have hXH : Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'} ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    rcases hy with hy | hy
    · rw [hy]
      exact (hH a).2 has
    · rw [Set.mem_singleton_iff.1 hy]
      exact (hH a').2 ha's
  have hXcard := s1614_om_X_card (quadMinus 3 K b c) hF.1 hF.2.1 hF.2.2.2.2.1
  have hmap := Subgroup.map_comap_eq (StatedOmega ⇑(quadMinus 3 K b c)).subtype E'
  have hr : (StatedOmega ⇑(quadMinus 3 K b c)).subtype.range =
      StatedOmega ⇑(quadMinus 3 K b c) := Subgroup.range_subtype _
  rw [hr, inf_of_le_right hEΩ] at hmap
  have hcard := Subgroup.card_map_of_injective
    (K := E'.comap (StatedOmega ⇑(quadMinus 3 K b c)).subtype)
    (Subgroup.subtype_injective (StatedOmega ⇑(quadMinus 3 K b c)))
  rw [hmap] at hcard
  refine ⟨Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'}, bot_le, hXH, ?_,
    E'.comap (StatedOmega ⇑(quadMinus 3 K b c)).subtype, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · show Nat.card ↥(Subgroup.closure {Multiplicative.ofAdd a, Multiplicative.ofAdd a'}) =
      4 * Nat.card ↥(⊥ : Subgroup (Multiplicative (ι₆ → K)))
    rw [Subgroup.card_bot, mul_one]
    exact hXcard
  · refine ⟨⟨fun u v => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have h := hcomm.is_comm.comm (⟨u.1.1, u.2⟩ : E') ⟨v.1.1, v.2⟩
    exact congrArg (fun z : E' => (z : GL ι₆ K)) h
  · rintro (u : ↥(StatedOmega ⇑(quadMinus 3 K b c))) hu
    apply Subtype.ext
    have h3 : u.1 ^ 3 = 1 := hexp u.1 hu
    exact h3
  · exact le_of_le_of_eq hE9 hcard
  · rintro (e : ↥(StatedOmega ⇑(quadMinus 3 K b c))) he y hy
    exact hstab _ he y hy
  · rintro (e : ↥(StatedOmega ⇑(quadMinus 3 K b c))) _ h
    apply Subtype.ext
    apply Units.ext
    apply Matrix.mulVec_injective
    funext v
    have h1 := h (Multiplicative.ofAdd v) (Subgroup.mem_top _)
    have h3 : Multiplicative.ofAdd (((e : GL ι₆ K) : Matrix ι₆ ι₆ K).mulVec v) *
        (Multiplicative.ofAdd v)⁻¹ = 1 := Subgroup.mem_bot.1 h1
    have h5 : Multiplicative.ofAdd (((e : GL ι₆ K) : Matrix ι₆ ι₆ K).mulVec v) =
        Multiplicative.ofAdd v := mul_inv_eq_one.1 h3
    have h4 : ((e : GL ι₆ K) : Matrix ι₆ ι₆ K).mulVec v = v :=
      Multiplicative.ofAdd.injective h5
    show ((e : GL ι₆ K) : Matrix ι₆ ι₆ K).mulVec v =
      ((1 : GL ι₆ K) : Matrix ι₆ ι₆ K).mulVec v
    rw [Units.val_one, Matrix.one_mulVec]
    exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
