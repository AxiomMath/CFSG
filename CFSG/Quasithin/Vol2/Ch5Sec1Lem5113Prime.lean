module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NQ
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113TypeF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

@[expose] def FactType513Prime : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Q R S B D : Subgroup A), Star513 Q R S B D →
    (IsAlt 7 ↥Q ∨ IsHat ↥Q (alternatingGroup (Fin 7)) ∨ IsSporadic .M22 ↥Q ∨
      IsHat ↥Q (NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 ↥Q ∨ IsSporadic .J1 ↥Q ∨
      IsSporadic .J2 ↥Q ∨ IsSporadic .J4 ↥Q ∨ IsSporadic .HS ↥Q ∨ IsSporadic .Ru ↥Q) →
    ¬ (∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) →
    IsSporadic .J1 ↥Q ∧ ∀ d ∈ D, d ^ 7 ∈ Subgroup.centralizer (Q : Set A)

namespace Star513

variable {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A}

theorem three_or_j1 (hst : Star513 Q R S B D) (hnot : ¬ D ≤ Subgroup.normalizer (R : Set A))
    (hTc : FactType513Aut) (hTp : FactType513Prime) (h36 : Vol2Native.A36StrongCat Q)
    (h314 : A314Statement S R Q) (hnr : ¬ IsRank2LieChar2 ↥Q) :
    (∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) ∨
      (IsSporadic .J1 ↥Q ∧ ∀ d ∈ D, d ^ 7 ∈ Subgroup.centralizer (Q : Set A)) := by
  have hthree : (IsAlt 7 ↥Q ∨ IsHat ↥Q (alternatingGroup (Fin 7)) ∨ IsSporadic .M22 ↥Q ∨
      IsHat ↥Q (NativeSporadic.Carrier .M22) ∨ IsSporadic .M23 ↥Q ∨ IsSporadic .J1 ↥Q ∨
      IsSporadic .J2 ↥Q ∨ IsSporadic .J4 ↥Q ∨ IsSporadic .HS ↥Q ∨ IsSporadic .Ru ↥Q) →
      (∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) ∨
        (IsSporadic .J1 ↥Q ∧ ∀ d ∈ D, d ^ 7 ∈ Subgroup.centralizer (Q : Set A)) := by
    intro hlist
    by_cases h3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)
    · exact Or.inl h3
    · exact Or.inr (hTp A Q R S B D hst hlist h3)
  have haut : ((∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      (IsPSL 2 p 1 ↥Q ∨ IsSL2 p ↥Q)) ∨ IsPSL 2 5 2 ↥Q ∨
      ∃ s : Bool, IsPSLEps3 s 5 1 ↥Q ∨ IsSLEps3 s 5 ↥Q) → False :=
    fun hlist => hnot (hTc A Q R S B D hst hlist)
  unfold A314Statement at h314
  rcases h314 with ⟨-, -, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, h3⟩ | ⟨-, h4, -⟩ | ⟨-, h5, -⟩ |
      ⟨-, -, -, h6⟩ | ⟨-, -, -, h7⟩ | ⟨-, h8, -⟩ | ⟨-, h9, -⟩ | ⟨-, -, h10⟩ | ⟨-, h11, -⟩ |
      ⟨-, -, h12, -⟩ | h13 | h14
  · exact (hnr (isRank2LieChar2_of_a314One h1)).elim
  · rcases h2 with h | h
    · exact hthree (Or.inl h)
    · exact hthree (Or.inr (Or.inl h))
  · rcases h3 with h | ⟨p, hp, hp5, hp8, h⟩
    · exact (haut (Or.inr (Or.inl h))).elim
    · exact (haut (Or.inl ⟨p, hp, hp5, hp8, Or.inl h⟩)).elim
  · exact (haut (Or.inr (Or.inr h4))).elim
  · rcases h5 with h | h
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inl h⟩))).elim
    · exact (haut (Or.inr (Or.inr ⟨true, Or.inr h⟩))).elim
  · rcases h6 with h | h
    · exact hthree (Or.inr (Or.inr (Or.inl h)))
    · exact hthree (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h8))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9)))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h11)))))))))
  · exact hthree (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr h12)))))))))
  · exact (false_of_nq hst hnot hTc h36 (Or.inl h13)).elim
  · exact (false_of_nq hst hnot hTc h36 (Or.inr h14)).elim

end Star513

@[expose] def Stmt5_1_13_type_j1_seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ → conjClosure Kh₁ T = Kh₁ →
    IsSporadic .J1 ↥(o2Img X Kh₁) →
    (∀ d ∈ o2Img X (D ⊓ X),
      d ^ 7 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    ¬ (∀ d ∈ o2Img X (D ⊓ X), ∃ k : ℕ,
      d ^ (3 ^ k) ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    False

theorem stmt5_1_13_type_j1_of (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h36 : Vol2Native.A36ForSQTKCat) (h510 : Stmt5_1_10)
    (hlie : Stmt5_1_13_lieC) (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hM23 : FactM23L34)
    (h312 : A312ForSQTK) (hTc : FactType513Aut) (hTp : FactType513Prime)
    (h7 : Stmt5_1_13_type_j1_seven) : Stmt5_1_13_type_j1 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hcl
  have hL24 := hc5.1
  obtain ⟨k, hk⟩ := h510.exists_fieldParam m.hyp m.nota
  have e := m.toEmb512 hk
  have heq : K₁ = oTwoUpper H := e.eq_of_isSimpleGroup (isSimpleGroup_of_lieModel_PSL2 hL24)
  obtain ⟨hst, hnot⟩ := m.star513 h37 h38 h510 heq hcl hL24
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36Q := Vol2Native.lemma_1_2_1_four_strong hloc h36 m.inH.2 m.hat.1
  have h314 := hc5.2.2.2
  rw [hcl] at h314
  obtain ⟨eH⟩ := modO2_mulEquiv m.hat.1
  have hnr : ¬ IsRank2LieChar2 ↥(modO2Image X Kh₁) := fun hR2 => by
    refine m.false_of_a314One hM hM23 h312 h510 hlie hL24 heq ?_
    rw [hcl]
    exact IsRank2LieChar2.of_mulEquiv eH.symm hR2
  rcases Star513.three_or_j1 hst hnot hTc hTp h36Q h314 hnr with h3 | ⟨hJ, h7'⟩
  · exact h3
  · by_contra hne
    exact h7 G T M L V H B D K₁ X Kh₁ n m hc5 hcl hJ h7' hne

end CFSG.Quasithin.H13
