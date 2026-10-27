module

public import CFSG.RankThree.PartOne.S12.Sec15
public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def Node1511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ B : Subgroup G, B ≤ A →
      ((E = A ∧ Nat.card A ≤ p * Nat.card B) ∨
        (Outcome152Five p E A (lieGenerated p E) ∧ B = A)) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining (B : Set G), M ≤ lieNormalizer p E

@[expose] def Node1514 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      (E = A → ∃ n ∈ lieNormalizer p E, ∃ B₁ : Subgroup G, B₁ ≤ A ∧
        B₁.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
        Nat.card A ≤ p * Nat.card B₁) ∧
      (E = A →
        ∃ n ∈ lieNormalizer p E, ∃ B₂ : Subgroup G, B₂ ≤ A ∧
        B₂.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) ∧
        Nat.card A ≤ p * Nat.card B₂) ∧
      (Outcome152Five p E A (lieGenerated p E) →
        A ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) ∧
        ∃ B : Subgroup G, B ≤ E ∧
          B ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
          IsElementaryAbelian p B ∧ Nat.card B = p ^ 2)

@[expose] def Node1514' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) ∧
      (E = A → ∃ n ∈ lieNormalizer p E, ∃ B₁ : Subgroup G, B₁ ≤ A ∧
        B₁.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
        Nat.card A ≤ p * Nat.card B₁) ∧
      (E = A → ∃ x ∈ omegaOneCenterIn T, x ≠ 1 ∧
        ∃ n ∈ lieNormalizer p E, ∃ B₂ : Subgroup G, B₂ ≤ A ∧
        B₂.map (MulAut.conj n).toMonoidHom ≤
          (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer ({x} : Set G) ∧
        Nat.card A ≤ p * Nat.card B₂) ∧
      (Outcome152Five p E A (lieGenerated p E) →
        A ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) ∧
        ∃ B : Subgroup G, B ≤ E ∧
          B ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
          IsElementaryAbelian p B ∧ Nat.card B = p ^ 2)

@[expose] def Node1515U5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ T : Subgroup G, IsSylowOf 2 T (lieNormalizer p E) →
      A ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.centralizer (omegaOneCenterIn T : Set G) →
      (∃ B : Subgroup G, B ≤ E ∧
        B ≤ (lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ∧
        IsElementaryAbelian p B ∧ Nat.card B = p ^ 2) →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining
        (((lieGenerated p E ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) : Subgroup G) :
          Set G), M ≤ lieNormalizer p E

theorem maximalTwoLocalsContaining_mono {G : Type} [Group G] {B X : Set G} (h : B ⊆ X) :
    CFSG.maximalTwoLocalsContaining X ⊆ CFSG.maximalTwoLocalsContaining B :=
  fun _ hM => ⟨hM.1, fun _ hx => hM.2 (h hx)⟩

theorem le_of_conj_maximalTwoLocals {G : Type} [Group G] {B X N M : Subgroup G} {n : G}
    (hnN : n ∈ N) (hBX : B.map (MulAut.conj n).toMonoidHom ≤ X)
    (hM : M ∈ CFSG.maximalTwoLocalsContaining (X : Set G))
    (h : ∀ M' ∈ CFSG.maximalTwoLocalsContaining (B : Set G), M' ≤ N) : M ≤ N := by
  have hmax : CFSG.IsMaximalTwoLocal (M.map (MulAut.conj n⁻¹).toMonoidHom) :=
    CFSG.RankThree.PartTwo.Late.isMaximalTwoLocal_map hM.1 (MulAut.conj n⁻¹)
  have hB : (B : Set G) ⊆ M.map (MulAut.conj n⁻¹).toMonoidHom := by
    intro b hb
    refine Subgroup.mem_map.2 ⟨n * b * n⁻¹, hM.2 (hBX (Subgroup.mem_map.2 ⟨b, hb, rfl⟩)), ?_⟩
    simp [mul_assoc]
  intro m hm
  have h1 := h _ ⟨hmax, hB⟩ (Subgroup.mem_map.2 ⟨m, hm, rfl⟩)
  have h2 : n * (n⁻¹ * m * n) * n⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem hnN (by simpa [MulAut.conj_apply, mul_assoc] using h1)) (N.inv_mem hnN)
  simpa [mul_assoc] using h2

theorem Outcome152.five_of_ne {G : Type} [Group G] {p : ℕ} {E A I : Subgroup G}
    (h : Outcome152 p E A I) (hAE : ¬ E = A) : Outcome152Five p E A I := by
  rcases h with ⟨-, -, -, -, -, hEA, -⟩ | ⟨-, -, -, -, -, hEA, -⟩ | ⟨-, -, -, -, -, hEA, -⟩ |
    ⟨-, -, -, -, -, hEA, -⟩ | h
  · exact absurd hEA hAE
  · exact absurd hEA hAE
  · exact absurd hEA hAE
  · exact absurd hEA hAE
  · exact h

theorem node1515_of_items (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h125 : Node125) (h1511 : Node1511) (h1514 : Node1514)
    (h15u5 : Node1515U5) : Node1515 := by
  intro G _ _ p A c L E h15 hout
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h15.h12
  obtain ⟨T, hT, hX, hY, h5⟩ := h1514 G p A c L E h15 hF12 hout
  refine ⟨T, hT, ?_, ?_⟩
  · intro M hM
    by_cases hAE : E = A
    · obtain ⟨n, hn, B₁, hB₁A, hB₁X, hB₁c⟩ := hX hAE
      exact le_of_conj_maximalTwoLocals hn hB₁X hM
        (h1511 G p A c L E h15 hF12 hout B₁ hB₁A (Or.inl ⟨hAE, hB₁c⟩))
    · have hfive : Outcome152Five p E A (lieGenerated p E) := hout.five_of_ne hAE
      obtain ⟨hAY, hB⟩ := h5 hfive
      exact h15u5 G p A c L E h15 hF12 hfive T hT hAY hB M hM
  · intro M hM
    by_cases hAE : E = A
    · obtain ⟨n, hn, B₂, hB₂A, hB₂Y, hB₂c⟩ := hY hAE
      exact le_of_conj_maximalTwoLocals hn hB₂Y hM
        (h1511 G p A c L E h15 hF12 hout B₂ hB₂A (Or.inl ⟨hAE, hB₂c⟩))
    · have hfive : Outcome152Five p E A (lieGenerated p E) := hout.five_of_ne hAE
      exact h1511 G p A c L E h15 hF12 hout A le_rfl (Or.inr ⟨hfive, rfl⟩) M
        (maximalTwoLocalsContaining_mono (fun x hx => (h5 hfive).1 hx) hM)

theorem centralizer_singleton_le_normalizer_zpowers_aux {G : Type} [Group G] (x : G) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  intro g hg
  have hgx : Commute g x := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hc : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hgx.zpow_right n).symm).eq
  exact Subgroup.centralizer_le_normalizer _ hc

theorem node1515'_of_items (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h125 : Node125) (h1511 : Node1511) (h1514 : Node1514')
    (h15u5 : Node1515U5) : Node1515' := by
  intro G _ _ p A c L E h15 hout
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h15.h12
  obtain ⟨T, hT, hX, hY, h5⟩ := h1514 G p A c L E h15 hF12 hout
  refine ⟨T, hT, ?_, ?_⟩
  · intro M hM
    by_cases hAE : E = A
    · obtain ⟨n, hn, B₁, hB₁A, hB₁X, hB₁c⟩ := hX hAE
      exact le_of_conj_maximalTwoLocals hn hB₁X hM
        (h1511 G p A c L E h15 hF12 hout B₁ hB₁A (Or.inl ⟨hAE, hB₁c⟩))
    · have hfive : Outcome152Five p E A (lieGenerated p E) := hout.five_of_ne hAE
      obtain ⟨hAY, hB⟩ := h5 hfive
      exact h15u5 G p A c L E h15 hF12 hfive T hT hAY hB M hM
  · have hT2 : IsPGroup 2 T := hT.2.1
    have hT1 : T ≠ ⊥ := by
      intro hbot
      have h2N : 2 ∣ Nat.card (lieNormalizer p E) :=
        (even_iff_two_dvd.mp hout.even_card).trans
          (Subgroup.card_dvd_of_le (Subgroup.le_normalizer : lieGenerated p E ≤ lieNormalizer p E))
      have h1 := hT.2.2
      rw [hbot, Subgroup.relIndex_bot_left] at h1
      exact h1 h2N
    by_cases hAE : E = A
    · obtain ⟨x, hxZ, hx1, n, hn, B₂, hB₂A, hB₂Y, hB₂c⟩ := hY hAE
      have hxT : x ∈ T := Sec15Final.omegaOneCenterIn_le T hxZ
      have hZ2 : IsPGroup 2 (Subgroup.zpowers x) := hT2.to_le (Subgroup.zpowers_le.2 hxT)
      have hZ1 : Subgroup.zpowers x ≠ ⊥ := by
        rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1
      have hXN : B₂.map (MulAut.conj n).toMonoidHom ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
        hB₂Y.trans (inf_le_right.trans (centralizer_singleton_le_normalizer_zpowers_aux x))
      have hMX : ∀ M ∈ CFSG.maximalTwoLocalsContaining
          ((B₂.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G), M ≤ lieNormalizer p E :=
        fun M hM => le_of_conj_maximalTwoLocals hn le_rfl hM
          (h1511 G p A c L E h15 hF12 hout B₂ hB₂A (Or.inl ⟨hAE, hB₂c⟩))
      have hN : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ lieNormalizer p E :=
        Sec15Final.normalizer_le_of_forall_maximal hZ1 hZ2 hXN hMX
      exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxZ)).trans
        ((centralizer_singleton_le_normalizer_zpowers_aux x).trans hN)
    · have hfive : Outcome152Five p E A (lieGenerated p E) := hout.five_of_ne hAE
      have hAY := (h5 hfive).1
      have hZ2 : IsPGroup 2 (omegaOneCenterIn T) :=
        hT2.to_le (Sec15Final.omegaOneCenterIn_le T)
      have hZ1 : omegaOneCenterIn T ≠ ⊥ := Sec15Final.omegaOneCenterIn_ne_bot hT2 hT1
      have hXN : A ≤ Subgroup.normalizer (omegaOneCenterIn T : Set G) :=
        hAY.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
      have hMX : ∀ M ∈ CFSG.maximalTwoLocalsContaining (A : Set G), M ≤ lieNormalizer p E :=
        h1511 G p A c L E h15 hF12 hout A le_rfl (Or.inr ⟨hfive, rfl⟩)
      exact (Subgroup.centralizer_le_normalizer _).trans
        (Sec15Final.normalizer_le_of_forall_maximal hZ1 hZ2 hXN hMX)

end CFSG.RankThree.PartOne
