module

public import CFSG.RankThree.PartOne.K133.TwoLoc

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K
open scoped commutatorElement

@[expose] def GoodAction (p : ℕ) (X : Type) [Group X] (Ē : Subgroup (MulAut X)) : Prop :=
  (∃ S : Subgroup X, S ≠ ⊥ ∧ IsPGroup 2 S ∧ ∀ φ ∈ Ē, ∀ s ∈ S, φ s ∈ S) ∨
  (∃ P : Subgroup (MulAut X), P ≤ Ē ∧ Nat.card P = p ^ 2 ∧ ∃ S : Subgroup X, IsPGroup 2 S ∧
    (∀ φ ∈ P, ∀ s ∈ S, φ s ∈ S) ∧ ∃ φ ∈ P, ∃ s ∈ S, φ s ≠ s)

@[expose] def Good (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ Ē : Subgroup (MulAut X), IsElementaryAbelian p Ē → Nat.card Ē = p ^ 3 → GoodAction p X Ē

theorem Dead.good {p : ℕ} {X : Type} [Group X] (h : Dead p X) : Good p X :=
  fun Ē hE hc => Or.inl (h Ē hE hc)

theorem exists_B_of_goodAction {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E ≠ A)
    {t : MulAut E} {b : G} (hb : b ∈ autFixedInG E t) (hb1 : b ≠ 1) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsAt p b) (hD : thetaQuotientCentralizer p E J = Subgroup.zpowers b)
    (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hcard3 : Nat.card (simpleQuotAction p hEJ).range = p ^ 3)
    (hGA : GoodAction p (SimpleQuot p J) (simpleQuotAction p hEJ).range) :
    ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ J ∈ sectionTenZero p B := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  have hEe := h.E_elem
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ
  have hbE : b ∈ E := (Subgroup.map_subtype_le _) hb
  rcases hGA with ⟨S, hS1, hS2, hSst⟩ | ⟨P, hPE, hPcard, S, hS2, hSst, φ, hφP, s, hsS, hφs⟩
  · exfalso
    obtain ⟨R, hRJ, hR1, hR2, hER, -⟩ := exists_two_subgroup_of_simpleQuot hp (by omega)
      (IsElementaryAbelian.isPGroup p E) hEJ hS1 hS2 (fun x s hs => hSst _ ⟨x, rfl⟩ s hs)
    exact false_of_normalizes_two h hF hEA hR1 hR2 hER
  ·
    set f := simpleQuotAction p hEJ with hf
    set B₀ : Subgroup ↥E := P.comap f with hB₀
    set B : Subgroup G := B₀.map E.subtype with hB
    have hBE : B ≤ E := Subgroup.map_subtype_le _
    have hBEJ : B ≤ Subgroup.normalizer (J : Set G) := hBE.trans hEJ
    have hfb : f ⟨b, hbE⟩ = 1 := by
      have hmem : b ∈ thetaQuotientCentralizer p E J := hD ▸ Subgroup.mem_zpowers b
      rw [thetaQuotientCentralizer_eq_map_ker p hEJ] at hmem
      obtain ⟨x, hxk, hxb⟩ := Subgroup.mem_map.1 hmem
      have hx : x = ⟨b, hbE⟩ := Subtype.ext hxb
      rw [hx] at hxk
      exact MonoidHom.mem_ker.1 ((ker_simpleQuotAction p hq.1 hEJ ⟨b, hbE⟩).2 hxk)
    have hbB : b ∈ B := by
      refine Subgroup.mem_map.2 ⟨⟨b, hbE⟩, ?_, rfl⟩
      rw [hB₀, Subgroup.mem_comap, hfb]
      exact P.one_mem
    have hBel : IsElementaryAbelian p B := isElementaryAbelian_of_le hEe hBE
    have hkerc : Nat.card f.ker = p := by
      have hmul := Subgroup.card_ker_mul_card_range f
      rw [card_E_of_ne hF hEA, hcard3] at hmul
      have hp0 : 0 < p ^ 3 := pow_pos hp.pos 3
      apply Nat.eq_of_mul_eq_mul_right hp0
      rw [hmul]
      ring
    have hB₀card : Nat.card B₀ = p ^ 3 := by
      have hidx : B₀.index = P.relIndex f.range := Subgroup.index_comap P f
      have hPc : Nat.card (P.subgroupOf f.range) = p ^ 2 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv, hPcard]
      have h1 := Subgroup.card_mul_index (P.subgroupOf f.range)
      rw [hPc, hcard3] at h1
      have hrel : P.relIndex f.range = p := by
        have hp0 : 0 < p ^ 2 := pow_pos hp.pos 2
        apply Nat.eq_of_mul_eq_mul_left hp0
        rw [Subgroup.relIndex] at *
        rw [h1]
        ring
      have h2 := Subgroup.card_mul_index B₀
      rw [hidx, hrel, card_E_of_ne hF hEA] at h2
      have hp0 : 0 < p := hp.pos
      apply Nat.eq_of_mul_eq_mul_right hp0
      rw [h2]
      ring
    have hBcard : Nat.card B = p ^ 3 := by
      rw [hB, Subgroup.card_map_of_injective E.subtype_injective, hB₀card]
    have hst : ∀ x : ↥B, ∀ s' ∈ S, simpleQuotAction p hBEJ x s' ∈ S := by
      intro x s' hs'
      obtain ⟨x₀, hx₀, hx₀x⟩ := Subgroup.mem_map.1 x.2
      have hx₀' : x₀ = ⟨(x : G), hBE x.2⟩ := Subtype.ext hx₀x
      have hfx : f ⟨(x : G), hBE x.2⟩ ∈ P := by
        rw [← hx₀']
        exact Subgroup.mem_comap.1 hx₀
      exact hSst _ hfx s' hs'
    have hS1 : S ≠ ⊥ := by
      intro hbot
      rw [hbot] at hsS
      exact hφs (by rw [Subgroup.mem_bot.1 hsS, map_one])
    obtain ⟨R, hRJ, hR1, hR2, hBR, hmv⟩ := exists_two_subgroup_of_simpleQuot hp (by omega)
      (IsElementaryAbelian.isPGroup p B) hBEJ hS1 hS2 hst
    obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥E, f x₁ = φ := by
      have := hPE hφP
      exact this
    have hx₁B : (x₁ : G) ∈ B := Subgroup.mem_map.2 ⟨x₁, by rw [hB₀, Subgroup.mem_comap, hx₁]; exact hφP, rfl⟩
    obtain ⟨r, hrR, hrne⟩ := hmv ⟨(x₁ : G), hx₁B⟩ ⟨s, hsS, by
      show f ⟨(x₁ : G), hBE hx₁B⟩ s ≠ s
      have : (⟨(x₁ : G), hBE hx₁B⟩ : ↥E) = x₁ := Subtype.ext rfl
      rw [this, hx₁]
      exact hφs⟩
    have hTR : ⁅R, B⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.1 hBR
    refine ⟨B, hBE, hBcard, mem_thetaComponentFamily_iff.2 ⟨b, hbB, hb1, hJ⟩, ⁅R, B⁆,
      hTR.trans hRJ, ?_, hR2.to_le hTR, le_normalizer_commutator' B R B hBR Subgroup.le_normalizer,
      ?_⟩
    · intro hbot
      have hc : ⁅r, (x₁ : G)⁆ ∈ ⁅R, B⁆ := Subgroup.commutator_mem_commutator hrR hx₁B
      rw [hbot, Subgroup.mem_bot] at hc
      apply hrne
      have : r * (x₁ : G) = (x₁ : G) * r := by
        have h1 : r * (x₁ : G) * r⁻¹ * (x₁ : G)⁻¹ = 1 := hc
        calc r * (x₁ : G) = (r * (x₁ : G) * r⁻¹ * (x₁ : G)⁻¹) * ((x₁ : G) * r) := by group
          _ = (x₁ : G) * r := by rw [h1, one_mul]
      calc (x₁ : G) * r * (x₁ : G)⁻¹ = (r * (x₁ : G)) * (x₁ : G)⁻¹ := by rw [this]
        _ = r := by group
    · have hcop : Nat.Coprime (Nat.card B) (Nat.card R) := by
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hR2
        rw [hBcard, hm]
        exact Nat.Coprime.pow 3 m ((Nat.coprime_primes hp Nat.prime_two).2 (by omega))
      have : Group.IsNilpotent R := hR2.isNilpotent
      exact (HNB.commutator_double_eq_self_of_coprime_solvable B R hBR hcop inferInstance).symm


theorem KF133ResMaxAt.of_good {P : (X : Type) → [Group X] → Prop}
    (hP : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      P X → ∀ p : ℕ, p.Prime → 5 ≤ p → Good p X) :
    KF133ResMaxAt P := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK b hb hb1 J hJ hKJ hmax hD hc hPJ
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  obtain ⟨hEJ, hEl, hcard3⟩ := simpleQuotAction_image h hF hEA hb hb1 hJ hD
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ
  have : IsSimpleGroup (SimpleQuot p J) := hq.2.1
  exact exists_B_of_goodAction h hF hEA hb hb1 hJ hD hEJ hcard3
    (hP _ hq.2.2 hPJ p hp h5 _ hEl hcard3)

end CFSG.RankThree.PartOne.K133
