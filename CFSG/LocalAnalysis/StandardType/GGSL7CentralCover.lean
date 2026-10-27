module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import CFSG.Quasithin.Vol2.Ch7Prop711Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem injective_of_surjective_projectiveSL_of_card_two {d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] (hd : 5 ≤ d) (hK : Nat.card K = 2)
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Function.Injective ψ := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨φ, hφsurj, hφ⟩ :=
    TypeA.exists_sl_cover (TypeA.slHasSections_of_five_le (K := K) hd) ψ hψ hker hperf
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro l hl
  obtain ⟨g, rfl⟩ := hφsurj l
  rw [Subgroup.mem_bot]
  have h1 : ψ (φ g) = 1 := MonoidHom.mem_ker.mp hl
  have h2 : proj d K g = 1 := by rw [← hφ g, h1]
  have h3 : g = 1 :=
    CFSG.Quasithin.H13.Prop711.proj_injective_of_card_two (n := d) hK (by rw [h2, map_one])
  rw [h3]
  exact map_one φ

theorem bijective_of_surjective_projectiveSL_of_card_two {d : ℕ} {K : Type} [Field K]
    {L' : Type} [Group L'] (hd : 5 ≤ d) (hK : Nat.card K = 2)
    (ψ : L' →* projectiveSL d K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    Function.Bijective ψ :=
  ⟨injective_of_surjective_projectiveSL_of_card_two hd hK ψ hψ hker hperf, hψ⟩

theorem centrallyClosed_projectiveSL_of_card_two {d : ℕ} {K : Type} [Field K]
    (hd : 5 ≤ d) (hK : Nat.card K = 2) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* projectiveSL d K),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Function.Injective ψ := by
  intro L' _ _ ψ hψ hker hperf
  exact injective_of_surjective_projectiveSL_of_card_two hd hK ψ hψ hker hperf

theorem centrallyClosed_projectiveSL_seven_two :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* projectiveSL 7 (ZMod 2)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Function.Injective ψ :=
  centrallyClosed_projectiveSL_of_card_two (by norm_num) (Nat.card_zmod 2)

end CFSG.StandardType
