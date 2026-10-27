module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPSp4Dvd
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPCent
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218N
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.KFieldCentHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeB0
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsEleven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s2122np_sp4_strong3 {D : Data G} {Ch : Choice2011 G}
    (h218 : S21_8N D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {a : ℕ} (ha : Odd a) (hX : IsSp4 (Bar2 L) a) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  classical
  have hSp4bar : IsSp4 (BarInf L) a := uc22p218s_isSp4_barInf hL hX
  have ha2 : 2 ≤ a := by
    have h1 : 1 ≤ a := hX.admissible.2.1
    have h2 : a ≠ 1 := fun h => hX.admissible.2.2.2 (by rw [h]; norm_num)
    omega
  have hnotpow : ¬ IsPowTwo a := by
    rintro ⟨k, rfl⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num at ha2
      · exact hk
    obtain ⟨m, hm⟩ := dvd_pow_self 2 (by omega : k ≠ 0)
    obtain ⟨j, hj⟩ := ha
    omega
  have h2a : 2 ^ a - 1 ≠ 1 := by
    have h4 : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
    omega
  obtain ⟨s, hs, hsdvd⟩ := Nat.exists_prime_and_dvd h2a
  obtain ⟨⟨-, -, -⟩, ⟨-, hk1⟩, -⟩ := h218 h1930 c L hL a hSp4bar hnotpow s hs hsdvd
  have hk1' : kParam D.M = 1 := by simpa [Data.k] using hk1
  by_contra h
  rw [kParam, if_neg h] at hk1'
  omega

private theorem uc22s2122np_sp4_basic {D : Data G} {Ch : Choice2011 G}
    (h1930 : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) :
    ∃ (s : ℕ) (b : G), s.Prime ∧ b ∈ c.B0 ∧ orderOf b = s ∧ Odd c.n := by
  classical
  have hodd : Odd c.n := u4p_odd_n D Ch h1930 c hsp3
  have hn2 : 2 ≤ c.n := by omega
  obtain ⟨s', hs', b, hbB0, hbs⟩ := P22fin3.exists_orderOf_mem_B0 D c hn2
  exact ⟨s', b, hs', hbB0, hbs, hodd⟩

private theorem uc22s2122np_sp4_split {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (hK3 : StronglyEmbeddedThree) (h211 : S21_1 D Ch)
    (h218 : S21_8N D Ch) (h218UR : S21_8UR D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {a : ℕ} (ha : Odd a) (hX : IsSp4 (Bar2 L) a) {s : ℕ} (hs : s.Prime)
    {b : G} (hbB0 : b ∈ c.B0) (hbT : b ∈ normalizer (D.T : Set G)) (hbs : orderOf b = s)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M) : False := by
  classical
  have hs2 : s ≠ 2 := by
    intro h
    have hodd : Odd s := hbs ▸ uc22p21d_odd_orderOf_of_mem_calB1 c.hB0 hbB0
    rw [h] at hodd
    obtain ⟨j, hj⟩ := hodd
    omega
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hLN
  have hbN : b ∈ normalizer (L : Set G) := hML (c.hBM hbB0)
  let S : Subgroup G := D.T ⊓ L
  have hS : IsSylowOf 2 S L := D.sylowM.inf_of_le_normalizer hL.1.le hML
  have hbS : b ∈ normalizer (S : Set G) := CFSG.ABGLocalTools.mem_normalizer_inf hbT hbN
  by_cases hsa : s ∣ 2 ^ a - 1
  · exact uc22s2122np_false_of_dvd h211 h1930 c hH₁ hH₂ hL0 hfX hSg hσ h218UR hL hLN ha hX
      hbB0 hbT hs hbs hsa
  · by_cases hinn : inducedQuotInfAut L b hbN ∈
        (MulAut.conj : (BarInf L ⧸ center (BarInf L)) →*
          MulAut (BarInf L ⧸ center (BarInf L))).range
    · exact uc22s2122np_false_of_centralizesBar hK3 h1930 c hL hX hsp3 hbB0 hs hs2 hbs
        (uc22s2122np_centralizesBar_of_not_dvd hL hX hS hbN hbS hs hs2 hbs hsa hinn)
    · let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
      have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
      have hSp4X : IsSp4 (BarInf L ⧸ center (BarInf L)) a :=
        CFSG.Blueprint.LieModel.quotient_center hZ (uc22p218s_isSp4_barInf hL hX)
      exact CFSG.LocalAnalysis.UniquenessCase.UC22.false_of_isSp4_shape h218 kFieldCent_holds
        h1930 (c := c₀) hL hLN hbB0 hbN (inducedQuotInf_inducedQuotInfAut L b hbN)
        (hbs ▸ (Nat.prime_iff.mp hs).squarefree) (hbs ▸ hs.odd_of_ne_two hs2) hSp4X hinn

theorem uc22s2122np_false_of_sp4 {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (hK3 : StronglyEmbeddedThree) (h211 : S21_1 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h218 : S21_8N D Ch) (h218UR : S21_8UR D Ch)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal)
    {a : ℕ} (ha : Odd a) (hX : IsSp4 (Bar2 L) a) : False := by
  classical
  have hsp3 := uc22s2122np_sp4_strong3 h218 h1930 c hL ha hX
  obtain ⟨s, b, hs, hbB0, hbs, hodd⟩ := uc22s2122np_sp4_basic h1930 c (hn3 h1930 c) hsp3
  have hbT : b ∈ normalizer (D.T : Set G) := Ctx21.B0_le_normalizer c hodd hbB0
  exact uc22s2122np_sp4_split hSg hK3 h211 h218 h218UR hσ h1930 c hH₁ hH₂ hL0 hfX hL hLN
    ha hX hs hbB0 hbT hbs hsp3

end CFSG.LocalAnalysis.UniquenessCase.UC22
