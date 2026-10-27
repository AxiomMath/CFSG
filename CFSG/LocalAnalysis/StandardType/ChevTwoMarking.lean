module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import Certificates.Certificate43
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate8064
import CFSG.Adapters.TauCetiLieModels
import CFSG.Adapters.LinearSmallCatalog
import CFSG.Adapters.StatedPSLTwoSeven
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.ChevTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
open CFSG.Yardstones.Md0ec50421ce4

theorem lieModel_psl_two_four_of_alternating_five {S : Type}
    [Group S] (e : S ≃* alternatingGroup (Fin 5)) : CFSG.Blueprint.LieModel S .PSL 2 2 2 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [card_galoisField_two (by norm_num)]
    norm_num
  obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (.inl hK)
  exact .inl ⟨by simp [classicalTags], ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
    GaloisField 2 2, inferInstance, inferInstance, by rw [hK]; norm_num, ⟨e.trans e₅.symm⟩⟩

theorem lieModel_psl_four_two_of_alternating_eight {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin 8)) : CFSG.Blueprint.LieModel S .PSL 4 2 1 := by
  obtain ⟨e'⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e
  exact .inl ⟨by simp [classicalTags], ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩,
    ZMod 2, inferInstance, inferInstance, by simp, ⟨e'⟩⟩

theorem lieModel_psl_three_two_of_A_one {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) : CFSG.Blueprint.LieModel S .PSL 3 2 1 := by
  have h7 : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def, hq]
  obtain ⟨hp, he⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 h7
  have h := CFSG.Models.lieModel_A 1 q hv e
  rw [hp, he] at h
  have hc : StatedClassicalModel S .PSL 2 7 1 :=
    (blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h).statedClassicalModel
      (by simp [classicalTags])
  exact .inl ⟨by simp [classicalTags],
    CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven hc⟩

theorem statedClassicalModel_psu_three_three_of_twistedA_two {S : Type} [Group S] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) : StatedClassicalModel S .PSU 3 3 1 := by
  have h3 : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def, hq]
  obtain ⟨hp, he⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).1 h3
  have h := CFSG.Models.lieModel_twistedA 2 q hv e
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = 3 :=
    (LieTypeIndex.characteristic_twistedA 2 q).trans hp
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = 1 :=
    (LieTypeIndex.fieldExponent_twistedA 2 q).trans he
  rw [hc, hf] at h
  exact (blueprintLieModel_of_modelsLieModel (by simp [classicalTags]) h).statedClassicalModel
    (by simp [classicalTags])

theorem ambiguousChev_two_cases {i : TauCeti.CFSGIndex} (h : ambiguousChev 2 i) :
    (∃ h5, i = .alternating 5 h5) ∨ (∃ h6, i = .alternating 6 h6) ∨
      (∃ h8, i = .alternating 8 h8) ∨
      (∃ (q : PrimePower) (hv : (LieTypeIndex.A 1 q).Valid), q.card = 7 ∧ i = .lie ⟨.A 1 q, hv⟩) ∨
      (∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid), q.card = 3 ∧
        i = .lie ⟨.twistedA 2 q, hv⟩) := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d, hv⟩ | s
  · exact h.elim
  · simp only [ambiguousChev] at h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl ⟨hn, rfl⟩
    · exact .inr (.inl ⟨hn, rfl⟩)
    · exact .inr (.inr (.inl ⟨hn, rfl⟩))
  · simp only [ambiguousChev] at h
    split at h
    · rename_i q
      rcases h with ⟨h7, -⟩ | ⟨-, h⟩
      · exact .inr (.inr (.inr (.inl ⟨q, hv, h7, rfl⟩)))
      · exact absurd h (by norm_num)
    · rename_i q
      exact .inr (.inr (.inr (.inr ⟨q, hv, h.1, rfl⟩)))
    · exact absurd h.2 (by norm_num)
    · exact h.elim
  · exact h.elim

theorem chevTwo_cases
    {S : Type} [Group S] (h : IsChevSimple 2 S) :
    (∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel S .PSU 3 3 1 := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | d | s
    · exact hi.elim
    · exact hi.elim
    · exact .inl (exists_lieModel_two_of_valid d hi e)
    · exact hi.elim
  · rcases ambiguousChev_two_cases hi with ⟨h5, rfl⟩ | ⟨h6, rfl⟩ | ⟨h8, rfl⟩ | ⟨q, hv, hq, rfl⟩ |
        ⟨q, hv, hq, rfl⟩
    · exact .inl ⟨.PSL, 2, 2, lieModel_psl_two_four_of_alternating_five e⟩
    · exact .inr (.inl ⟨e⟩)
    · exact .inl ⟨.PSL, 4, 1, lieModel_psl_four_two_of_alternating_eight e⟩
    · exact .inl ⟨.PSL, 3, 1, lieModel_psl_three_two_of_A_one q hv hq e⟩
    · exact .inr (.inr (statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e))

theorem marking_b2der {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)]
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    LargeEvenMarking X fun _ _ _ _ _ _ => True := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₆⟩ := nonempty_b2der_equiv_alternatingGroup hK
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  let θ := e.trans e₆.symm
  refine ⟨hX, ⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ, trivial⟩

theorem marking_g2der {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)]
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1) :
    LargeEvenMarking X fun _ _ _ _ _ _ => True := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hC : StatedClassicalModel ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ .PSU 3 3 1 :=
    (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (ZMod 2)
      hK).statedClassicalModel (by simp [classicalTags])
  obtain ⟨φ⟩ := CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique (by norm_num) h hC
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  have : IsSimpleGroup ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    φ.symm.isSimpleGroup
  have hZ := center_eq_bot_of_isSimpleGroup_of_nonabelian (nonabelian_of_mulEquiv φ hnab)
  let ψ : CFSG.Blueprint.DerivedCentralQuotient (adjointGroup .G2 (ZMod 2)) ≃*
      ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv (ZMod 2) .G2
  let θ := (φ.trans ψ.symm).trans e₁.symm
  refine ⟨hX, ⟨.G2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, nonabelian_of_mulEquiv θ hnab, θ, trivial⟩

theorem ys08_holds_legacy :
    YS08Legacy := by
  intro X _ _ hq hchev
  obtain ⟨hX, hS⟩ := hq
  rcases chevTwo_cases hchev with ⟨t, n, f, h⟩ | he | h
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot hX h)
  · obtain ⟨e⟩ := he
    exact marking_b2der hX e
  · exact marking_g2der hX h

theorem ys08_holds :
    YS08 := by
  intro X _ _ hq hchev
  exact CFSG.Assembly.largeEvenMarkingLegacy_to_canonical_carrier
    (ys08_holds_legacy X hq hchev)

end CFSG.StandardType.ChevTwo
