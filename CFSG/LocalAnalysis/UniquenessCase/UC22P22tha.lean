module

public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

theorem uc22p22th_center_eq_bot {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    (hO2 : CFSG.pCore 2 X = ⊥)
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1) :
    Subgroup.center X = ⊥ := by
  haveI : Group.IsPerfect X := ⟨hX⟩
  have hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (Subgroup.center X) := by
    intro p hp hp2 hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center hp2 hdvd
    have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank hp.one_lt (le_top : E ≤ ⊤) hE hcard
    have h1 := hrank p hp hp2
    omega
  have hZ2 : IsPGroup 2 (Subgroup.center X) := by
    have hne : Nat.card (Subgroup.center X) ≠ 0 := Nat.card_pos.ne'
    exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne fun {d} hd hdd =>
      by_contra fun h => hodd d hd h hdd)
  have hle : Subgroup.center X ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, hZ2⟩
  rw [hO2] at hle
  exact le_bot_iff.1 hle

theorem uc22p22th_simple {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) (hZ : Subgroup.center X = ⊥) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  haveI hs : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  let e : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  haveI hsX : IsSimpleGroup X := e.isSimpleGroup_congr.1 hs
  refine ⟨hsX, ?_⟩
  haveI : Group.IsPerfect X := ⟨hq.1⟩
  by_contra h
  push Not at h
  haveI : IsMulCommutative X := ⟨⟨fun a b => h a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative X ‹_›

theorem uc22p22th_catalog {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : CFSG.IsKGroup X) (hB : CFSG.RankThree.PartOne.TauCetiCatalogBridge) : CFSG.Blueprint.Catalog X :=
  hB X hnonab (CFSG.KCore.KGroupAllSimple.catalogue_self CFSG.Assembly.inCatalog_isoInvariant hK)

theorem uc22p22th_two_le_pRank_psl_sq {X : Type} [Group X] [Finite X] {p : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel X .PSL 2 p 2) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases h with ⟨-, ⟨-, hr⟩ | ⟨hn, -⟩ | hr⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | hr
  · exact hr
  · exact absurd hn (by norm_num)
  · omega
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega

theorem uc22p22th_of_a134 {X : Type} [Group X] [Finite X]
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1)
    (h : CFSG.Quasithin.A134Types X) :
    (∃ a : ℕ, IsL2 X a) ∨ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd X p) ∨ (∃ a : ℕ, IsSz X a) ∨ IsJ1 X := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, e, hp, hp3, he1, he2, hmodel⟩
  · exact Or.inl ⟨n, (CFSG.Blueprint.LieModel.classical_iff (by decide)).2 hn⟩
  · exact Or.inr (Or.inr (Or.inl ⟨n, CFSG.Blueprint.LieModel.twistedB2_iff.2 ⟨rfl, hn⟩⟩))
  · exact Or.inr (Or.inr (Or.inr hJ))
  · have hp2 : p ≠ 2 := by omega
    rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
    · exact Or.inr (Or.inl ⟨p, hp, hp2, (CFSG.Blueprint.LieModel.classical_iff (by decide)).2 hmodel⟩)
    · exact absurd (hrank p hp hp2) (by have := uc22p22th_two_le_pRank_psl_sq hp2 hmodel; omega)

end CFSG.LocalAnalysis.UniquenessCase.UC22
