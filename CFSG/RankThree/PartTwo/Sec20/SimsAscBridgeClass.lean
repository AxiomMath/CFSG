module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeTypes
public import CFSG.RankThree.PartTwo.Sec18.Item189KTypeBridge
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeSimple

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem even_of_two_pow_mod_three {m : ℕ} (h : 2 ^ m % 3 = 1) : Even m := by
  rcases Nat.even_or_odd m with he | ⟨k, rfl⟩
  · exact he
  · exfalso
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at h
    norm_num at h

theorem yAlphaClass_of_isRankOneType {M X T : Subgroup G} {c : G}
    (hL2m : ∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m)))
    (h : Sec18.IsRankOneType189 ↥(yAlpha M X T c)) :
    Nonempty (↥(yAlpha M X T c) ≃* CFSG.Blueprint.NativeSporadic.J1) ∨
      (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 1 ≤ e ∧
        Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField p e))) ∨
      ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ p ^ e % 3 = 2 ∧
          Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e))) ∨
        (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 1 ∧
          Nonempty (↥(yAlpha M X T c) ≃* projSU 3 p e))) ∨
      (∃ m : ℕ, Even m ∧ 0 < m ∧ Nonempty (↥(yAlpha M X T c) ≃* projSU 3 2 m)) := by
  rcases h with ⟨p, f, hp, hp3, hf, hiso⟩ | ⟨p, f, hp, hf, hpf, hiso⟩ |
    ⟨p, f, hp, hf, hpf, hiso⟩ | hiso
  · by_cases hp2 : p = 2
    · subst hp2
      exact absurd hiso (hL2m f)
    · exact Or.inr (Or.inl ⟨p, f, hp, hp2, hp3, hf, hiso⟩)
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨p, f, hp, hf, hpf, hiso⟩)))
  · by_cases hp2 : p = 2
    · subst hp2
      exact Or.inr (Or.inr (Or.inr ⟨f, even_of_two_pow_mod_three hpf, hf, hiso⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨p, f, hp, hp2, hf, hpf, hiso⟩)))
  · exact Or.inl hiso

theorem inCatalog_yAlpha {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] : Assembly.InCatalog ↥(yAlpha M X T c) := by
  have : IsSimpleGroup G := hset.isSimpleGroup
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hcX : c ∈ X := hKTX (Subgroup.mem_sup_left (self_mem_normalClosureIn M c))
  have hYRX : yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ X :=
    sup_le (normalClosureIn_le hcX) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX)
  have hXtop : X ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hset.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hX.1)
  have hYRtop : yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≠ ⊤ :=
    ne_top_of_le_ne_top hXtop hYRX
  have hKG : IsKGroup ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) :=
    (hset.toTheoremFourHyp.sectionFourHyp hYRtop).kGroup
  exact KCore.KGroupAllSimple.catalogue_self (C := Assembly.InCatalog)
    Assembly.inCatalog_isoInvariant ((hKG.quotient _).subgroup _)

end AscBridge

open AscBridge in
theorem step204YAlphaClass_holds
  :
    Step204YAlphaClass := by
  intro G _ _ A M L N c T i j P hset X hX _ hm hL2m _
  obtain ⟨hs, hnab⟩ := isSimpleGroup_yAlpha hset hX hm
  obtain ⟨idx, ⟨e⟩⟩ := inCatalog_yAlpha hset hX
  exact yAlphaClass_of_isRankOneType hL2m
    (Sec18.isRankOneType189_of_index hs hnab idx e (pRank_yAlpha_eq_one hset hX hm))

end CFSG.RankThree.PartTwo.Sec20
