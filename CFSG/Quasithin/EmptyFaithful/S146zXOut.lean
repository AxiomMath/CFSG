module

public import CFSG.Quasithin.EmptyFaithful.S146zXFive

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def InvTypeThree (X : Type) [Group X] : Prop :=
  StatedClassicalModel X StatedLieTag.PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3))) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.M11) ∨
    StatedClassicalModel X StatedLieTag.PSL 4 2 1 ∨
    StatedClassicalModel X StatedLieTag.PSL 5 2 1 ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.He)

@[expose] def InvTypeFive (p : ℕ) [Fact p.Prime] (X : Type) [Group X] : Prop :=
  StatedClassicalModel X StatedLieTag.PSL 3 p 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod p)))

variable {G : Type} [Group G] [Finite G]

@[expose] def Out134 (p : ℕ) [Fact p.Prime] (T Mc K P : Subgroup G) : Prop :=
  Mc ≤ Subgroup.normalizer (K : Set G) ∨
  ∃ L : Subgroup G, L ∈ cComp Mc ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
    K ≤ conjClosure L T ∧
    ((¬ T ≤ Subgroup.normalizer (L : Set G) ∧ P ⊓ L ≠ ⊥ ∧
        ((∃ n : ℕ, p ∣ 2 ^ n - 1 ∧
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 2 n) ∨
          ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 q 1)) ∨
      (T ≤ Subgroup.normalizer (L : Set G) ∧
        ((p = 3 ∧ InvTypeThree (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
          (p = 5 ∧ InvTypeFive p (↥L ⧸ CFSG.pCore 2 ↥L)))) ∨
      (T ≤ Subgroup.normalizer (L : Set G) ∧ EmptyFaithfulMultiple.AutCyclic T P))

omit [Finite G] in
theorem inf_ne_bot_of_eq_sup {P L : Subgroup G} {t : G}
    (hPeq : P = P ⊓ L ⊔ conjByElt t (P ⊓ L)) (hP : P ≠ ⊥) : P ⊓ L ≠ ⊥ := by
  intro hbot
  apply hP
  rw [hPeq, hbot]
  simp [conjByElt]

theorem three_dvd_two_pow_sub_one' {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 4 - 1 ∣ 4 ^ k - 1 := Nat.sub_one_dvd_pow_sub_one 4 k
  have e : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [e]
  exact h

theorem out134_of_three (h134 : EmptyFaithfulMultiple.Prop134E9He) {Mc T K P : Subgroup G}
    (hsq : CFSG.SectionRank.IsSQTKCat ↥Mc) (hPMc : pCoreOf 2 Mc ≠ ⊥) (hsyl : IsSylowTwoOf T Mc)
    (hKMc : K ≤ Mc) (hX : IsXi T K) (hi : (pCoreOf 2 K).relIndex K = 9) (hPK : P ≤ K)
    (hPp : IsPGroup 3 P) (hPc : Nat.card P = 9) : Out134 3 T Mc K P := by
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    omega
  rcases h134 G Mc T K P hsq hPMc hsyl hKMc hX hi hPK hPp hPc with
    hN | ⟨L, hL, hq, hXL, hcases⟩
  · exact Or.inl hN
  refine Or.inr ⟨L, hL, hq, hXL, ?_⟩
  rcases hcases with ⟨⟨t, htSN, htL, hPeq, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨hTL, -, hcyc⟩ |
      ⟨hTL, htype⟩ | ⟨hMcL, hHe⟩
  · refine Or.inl ⟨fun hTL => htL (hTL htSN.1), inf_ne_bot_of_eq_sup hPeq hPne, ?_⟩
    rcases htype with ⟨n, hn, hm⟩ | hq'
    · exact Or.inl ⟨n, three_dvd_two_pow_sub_one' hn, hm⟩
    · exact Or.inr hq'
  · refine Or.inr (Or.inl ⟨hTL, Or.inl ⟨rfl, ?_⟩⟩)
    rcases htype with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hTL, hcyc⟩)
  · refine Or.inr (Or.inl ⟨hTL, Or.inl ⟨rfl, ?_⟩⟩)
    rcases htype with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inl ⟨fun g hg => hMcL (hsyl.1 hg), Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hHe))))⟩⟩)

theorem out134_of_five (h5 : Prop134Five) {p : ℕ} [Fact p.Prime] (hp : p = 5)
    {Mc T K P : Subgroup G} (hsq : CFSG.SectionRank.IsSQTKCat ↥Mc) (hPMc : pCoreOf 2 Mc ≠ ⊥)
    (hsyl : IsSylowTwoOf T Mc) (hKMc : K ≤ Mc) (hX : IsXi T K)
    (hi : (pCoreOf 2 K).relIndex K = p ^ 2) (hPK : P ≤ K) (hPp : IsPGroup p P)
    (hPc : Nat.card P = p ^ 2) : Out134 p T Mc K P := by
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    have h2 := (Fact.out : p.Prime).two_le
    nlinarith
  rcases h5 p hp G Mc T K P hsq hPMc hsyl hKMc hX hi hPK hPp hPc with
    hN | ⟨L, hL, hq, hXL, h1 | h2 | h3⟩
  · exact Or.inl hN
  · exact Or.inr ⟨L, hL, hq, hXL, Or.inl h1⟩
  · exact Or.inr ⟨L, hL, hq, hXL, Or.inr (Or.inl ⟨h2.1, Or.inr ⟨hp, h2.2⟩⟩)⟩
  · exact Or.inr ⟨L, hL, hq, hXL, Or.inr (Or.inr h3)⟩

end CFSG.Quasithin.S146zX
