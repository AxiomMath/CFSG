module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812
import CFSG.GroupTheory.CoprimeCentralizerRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace Ctx812E

theorem pRank_inf_centralizer_le_one (c : Ctx812E G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {P E : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M)
    (hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G)) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) ≤ 1 := by
  by_contra hle
  have h2 : 1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) := not_le.mp hle
  have hp1 : 1 < p := (c.sig_prime p hp).1.one_lt
  have hPle : P ≤ c.S.M := CFSG.ABGLocalTools.IsSylowOf.le hP
  have hEM : E ≤ c.S.M := (hE.trans inf_le_left).trans hPle
  have hEX : ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) := by
    intro X hXE _
    have hXcE : X ≤ Subgroup.centralizer (E : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      haveI : IsMulCommutative ↥E := hEab.1
      exact congrArg Subtype.val (mul_comm' (⟨e, he⟩ : E) (⟨x, hXE hx⟩ : E))
    have hle' : c.S.M ⊓ Subgroup.centralizer (E : Set G) ≤
        c.S.M ⊓ Subgroup.normalizer (X : Set G) :=
      inf_le_inf_left _ ((Subgroup.centralizer_le (fun x hx => hXE hx)).trans
        (Subgroup.centralizer_le_normalizer _))
    exact lt_of_lt_of_le h2 (CFSG.SectionRank.pRank_mono hp1 hle')
  have hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ c.S.M :=
    h76 3 (by norm_num) E hEM hEab hcard (lt_trans Nat.zero_lt_one h2) hEX
  exact c.not_rankThreeGamma_le_of_le_center hP hE hEab hcard hΓ

theorem false_of_commutator_le_pCoreOf (c : Ctx812E G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {P E R : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M)
    (hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G)) (hEab : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hRM : R ≤ c.S.M) (hR : IsPGroup p R)
    (hrank : 2 ≤ CFSG.Open.pRank p R)
    (hcomm : ⁅R, E⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M) : False := by
  have hpp : p.Prime := (c.sig_prime p hp).1
  have hp2 : p ≠ 2 := (c.sig_prime p hp).2
  have hPle : P ≤ c.S.M := CFSG.ABGLocalTools.IsSylowOf.le hP
  have hEP : E ≤ P := hE.trans inf_le_left
  have hE3 : IsPGroup 3 E :=
    IsPGroup.to_le (CFSG.ABGLocalTools.IsSylowOf.isPGroup hP) hEP
  set O : Subgroup G := CFSG.Open.pCoreOf 2 c.S.M with hO
  have hOM : O ≤ c.S.M := by
    rw [hO]
    exact CFSG.openPCoreOf_le 2 c.S.M
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 O := by
    rw [hO, CFSG.openPCoreOf_eq_map_pCore]
    exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥c.S.M)) c.S.M.subtype
  have hON : c.S.M ≤ Subgroup.normalizer (O : Set G) := by
    have hOn : (O.subgroupOf c.S.M).Normal := by
      rw [hO, CFSG.openPCoreOf_subgroupOf]
      exact CFSG.pCore_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mp hOn
  have hpO : ¬ p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow hdvd))
  have h3O : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro hdvd
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdvd
    norm_num at h32
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hbound : CFSG.Open.pRank p R ≤
      CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) :=
    CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le (p := p) (q := 3)
      hRM hOM (hRM.trans hON) ((hEP.trans hPle).trans hON) hR hE3 hpO h3O hcomm
  have hle := c.pRank_inf_centralizer_le_one hp h76 hP hE hEab hcard
  omega

end Ctx812E

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
