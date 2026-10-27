module

public import CFSG.Quasithin.Vol2.Ch11SecSFacts4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3A
public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open CFSG.Open CFSG.QuasithinUnique.Setup.X6

variable {Q : Type} [Group Q]

structure ParabPair (S : Subgroup Q) (B : Fin 2 → Subgroup Q) : Prop where
  ne_top : ∀ j, B j ≠ ⊤
  not_le₀₁ : ¬ B 0 ≤ B 1
  not_le₁₀ : ¬ B 1 ≤ B 0
  classify : ∀ X : Subgroup Q, X ≠ ⊥ → ⁅X, X⁆ = X → S ≤ Subgroup.normalizer (X : Set Q) →
    X = B 0 ∨ X = B 1 ∨ X = ⊤
  top_not : ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤
  perfect : ∀ j, ⁅B j, B j⁆ = B j
  ne_bot : ∀ j, B j ≠ ⊥
  normalized : ∀ j, S ≤ Subgroup.normalizer (B j : Set Q)

namespace ParabPair

variable {S : Subgroup Q} {B : Fin 2 → Subgroup Q}

theorem le_card_of_isL24Sub [Finite Q] {X : Subgroup Q} (hX : IsL24Sub S X) :
    60 ≤ Nat.card ↥X := by
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := hX
  have h1 := (CFSG.pCore 2 ↥X).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, card_SL2_four hF] at h1
  rw [h1]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

theorem top_not_of_pCore [Finite Q] (hpc : CFSG.pCore 2 ↥(⊤ : Subgroup Q) = ⊥) :
    ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤ := by
  intro X hX hXt htop
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := htop
  have h1 := (CFSG.pCore 2 ↥(⊤ : Subgroup Q)).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, card_SL2_four hF, hpc, Subgroup.card_bot, mul_one,
    Subgroup.card_top] at h1
  have h2 := le_card_of_isL24Sub hX
  have h3 : Nat.card ↥X < Nat.card Q := by
    rw [← Subgroup.card_top (G := Q)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hXt)
  omega

theorem not_isL24Sub_top (h : ParabPair S B) {X : Subgroup Q} (hX : IsL24Sub S X)
    (hXt : X ≠ ⊤) : ¬ IsL24Sub S ⊤ :=
  h.top_not X hX hXt

theorem eq_or_eq_of_isL24Sub (h : ParabPair S B) {X : Subgroup Q} (hX : IsL24Sub S X) :
    X = B 0 ∨ X = B 1 ∨ X = ⊤ :=
  h.classify X hX.1 hX.2.1 hX.2.2.1

theorem parabTwo [Finite Q] (h : ParabPair S B) {B₁ B₂ B₃ : Subgroup Q} (h₁ : IsL24Sub S B₁)
    (h₂ : IsL24Sub S B₂) (h₃ : IsL24Sub S B₃) :
    (B₁ ≤ B₂ → B₁ = B₂) ∧ (B₁ = B₂ ∨ B₁ = B₃ ∨ B₂ = B₃) := by
  have key : ∀ X Y : Subgroup Q, IsL24Sub S X → IsL24Sub S Y → X ≤ Y → X = Y := by
    intro X Y hX hY hXY
    rcases h.eq_or_eq_of_isL24Sub hX with rfl | rfl | rfl <;>
      rcases h.eq_or_eq_of_isL24Sub hY with rfl | rfl | rfl
    · rfl
    · exact absurd hXY h.not_le₀₁
    · exact absurd hY (h.not_isL24Sub_top hX (h.ne_top 0))
    · exact absurd hXY h.not_le₁₀
    · rfl
    · exact absurd hY (h.not_isL24Sub_top hX (h.ne_top 1))
    · exact absurd hX (h.not_isL24Sub_top hY (h.ne_top 0))
    · exact absurd hX (h.not_isL24Sub_top hY (h.ne_top 1))
    · rfl
  refine ⟨key B₁ B₂ h₁ h₂, ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have hnt : ∀ X, IsL24Sub S X → X = B 0 ∨ X = B 1 := by
    intro X hX
    rcases h.eq_or_eq_of_isL24Sub hX with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exfalso
      subst h'
      rcases h.eq_or_eq_of_isL24Sub h₁ with h1 | h1 | h1
      · exact h.not_isL24Sub_top h₁ (h1 ▸ h.ne_top 0) hX
      · exact h.not_isL24Sub_top h₁ (h1 ▸ h.ne_top 1) hX
      · rcases h.eq_or_eq_of_isL24Sub h₂ with h2 | h2 | h2
        · exact h.not_isL24Sub_top h₂ (h2 ▸ h.ne_top 0) hX
        · exact h.not_isL24Sub_top h₂ (h2 ▸ h.ne_top 1) hX
        · exact h12 (h1.trans h2.symm)
  rcases hnt _ h₁ with e1 | e1 <;> rcases hnt _ h₂ with e2 | e2 <;>
    rcases hnt _ h₃ with e3 | e3
  all_goals first
    | exact h12 (e1.trans e2.symm)
    | exact h13 (e1.trans e3.symm)
    | exact h23 (e2.trans e3.symm)

omit [Group Q] in
theorem sup_perfect {G : Type*} [Group G] {X Y : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hY : ⁅Y, Y⁆ = Y) : ⁅X ⊔ Y, X ⊔ Y⁆ = X ⊔ Y := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · calc X ⊔ Y = ⁅X, X⁆ ⊔ ⁅Y, Y⁆ := by rw [hX, hY]
      _ ≤ ⁅X ⊔ Y, X ⊔ Y⁆ := sup_le (Subgroup.commutator_mono le_sup_left le_sup_left)
        (Subgroup.commutator_mono le_sup_right le_sup_right)

theorem parabGen (h : ParabPair S B) {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂)
    (h₁ : B₁ ≠ ⊥) (h₂ : B₂ ≠ ⊥) (hp₁ : ⁅B₁, B₁⁆ = B₁) (hp₂ : ⁅B₂, B₂⁆ = B₂)
    (hS₁ : S ≤ Subgroup.normalizer (B₁ : Set Q)) (hS₂ : S ≤ Subgroup.normalizer (B₂ : Set Q)) :
    B₁ ⊔ B₂ = ⊤ := by
  have hN : S ≤ Subgroup.normalizer ((B₁ ⊔ B₂ : Subgroup Q) : Set Q) :=
    (le_inf hS₁ hS₂).trans (Subgroup.inf_normalizer_le_normalizer_sup B₁ B₂)
  have hb : B₁ ⊔ B₂ ≠ ⊥ := fun e => h₁ (le_bot_iff.mp (e ▸ le_sup_left))
  have key : ∀ j : Fin 2, B₁ ⊔ B₂ ≠ B j := by
    intro j e
    have hl₁ : B₁ ≤ B j := e ▸ le_sup_left
    have hl₂ : B₂ ≤ B j := e ▸ le_sup_right
    have hnt : ∀ X : Subgroup Q, X ≤ B j → X ≠ ⊥ → ⁅X, X⁆ = X →
        S ≤ Subgroup.normalizer (X : Set Q) → X = B j := by
      intro X hXj hX1 hXp hXS
      rcases h.classify X hX1 hXp hXS with f | f | f
      · subst f
        fin_cases j
        · rfl
        · exact absurd hXj h.not_le₀₁
      · subst f
        fin_cases j
        · exact absurd hXj h.not_le₁₀
        · rfl
      · subst f
        exact absurd (eq_top_iff.mpr hXj) (h.ne_top j)
    exact hne ((hnt B₁ hl₁ h₁ hp₁ hS₁).trans (hnt B₂ hl₂ h₂ hp₂ hS₂).symm)
  rcases h.classify _ hb (sup_perfect hp₁ hp₂) hN with e | e | e
  · exact absurd e (key 0)
  · exact absurd e (key 1)
  · exact e

end ParabPair

theorem eq_bot_of_perfect_of_le_solvable [Finite Q] {X Y : Subgroup Q} (hXp : ⁅X, X⁆ = X)
    (hXY : X ≤ Y) (hY : Group.IsSolvable ↥Y) : X = ⊥ := by
  have hsol : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXY)
      (Subgroup.inclusion_injective hXY)
  rw [← perfectCore_eq_self_of_perfect hXp]
  exact (isSolvable_iff_perfectCore_eq_bot X).mp hsol

theorem parabPair_of_residual_of [Finite Q] {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {P : Fin 2 → Subgroup Q}
    (hres : ResidualOvergroupsAt Q S P) (hB : ∀ j, dInf (P j) ≠ ⊥)
    (hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤)
    (htop : ∀ X : Subgroup Q, IsL24Sub S X → X ≠ ⊤ → ¬ IsL24Sub S ⊤) :
    ParabPair S (fun j => dInf (P j)) := by
  obtain ⟨-, hSP, hmax, hsolv, hC2, -⟩ := hres
  have hcov : ∀ j, P j ⋖ ⊤ := fun j => (hmax (P j) (hSP j)).mpr ⟨j, rfl⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSs : Group.IsSolvable ↥S := by
    have := hS.2.1.isNilpotent
    infer_instance
  have hperf : ∀ j, ⁅dInf (P j), dInf (P j)⁆ = dInf (P j) := fun j =>
    Subgroup.isPerfect_iff.mp (dInf_isPerfect (P j))
  have hinc : ∀ i j : Fin 2, i ≠ j → ¬ dInf (P i) ≤ dInf (P j) := by
    intro i j hij hle
    apply hB i
    have h1 : dInf (P i) ≤ P i ⊓ P j := le_inf (dInf_le (P i)) (hle.trans (dInf_le (P j)))
    have h2 : P i ⊓ P j = P 0 ⊓ P 1 := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · rfl
      · exact inf_comm _ _
      · exact absurd rfl hij
    rw [h2] at h1
    exact eq_bot_of_perfect_of_le_solvable (hperf i) h1 hsolv
  refine ⟨fun j e => (hcov j).lt.ne (eq_top_iff.mpr (e ▸ dInf_le (P j))), hinc 0 1 (by decide),
    hinc 1 0 (by decide), ?_, htop, hperf, hB, fun j => ?_⟩
  swap
  · rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore]
    exact (hSP j).trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
  intro X hX1 hXp hSX
  have hcore : perfectCore (X ⊔ S) = X := perfectCore_sup_eq hXp hSs hSX
  by_cases htop' : X ⊔ S = ⊤
  · right; right
    have hXn : X.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop']
      exact sup_le Subgroup.le_normalizer hSX
    exact hN X hXn hXp hX1
  · have hns : ¬ Group.IsSolvable ↥(X ⊔ S) := fun hsol =>
      hX1 (eq_bot_of_perfect_of_le_solvable hXp le_sup_left hsol)
    obtain ⟨j, -, hdj⟩ := hC2 (X ⊔ S) le_sup_right htop' hns
    rw [CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hcore] at hdj
    fin_cases j
    · exact Or.inl hdj
    · exact Or.inr (Or.inl hdj)

theorem parabPair_of_residual [Finite Q] [IsSimpleGroup Q] {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {P : Fin 2 → Subgroup Q}
    (hres : ResidualOvergroupsAt Q S P) (hB : ∀ j, dInf (P j) ≠ ⊥) :
    ParabPair S (fun j => dInf (P j)) := by
  have hpc : CFSG.pCore 2 ↥(⊤ : Subgroup Q) = ⊥ := by
    have : IsSimpleGroup ↥(⊤ : Subgroup Q) := Subgroup.topEquiv.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥(⊤ : Subgroup Q)) with h | h
    · exact h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥(⊤ : Subgroup Q)) := CFSG.pCore_isPGroup
      rw [h] at hp
      have hQ : IsPGroup 2 Q := (hp.of_equiv Subgroup.topEquiv).of_equiv Subgroup.topEquiv
      have := hQ.isNilpotent
      have hQs : Group.IsSolvable ↥(⊤ : Subgroup Q) :=
        Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup Q).subtype)
          (⊤ : Subgroup Q).subtype_injective
      exact hB 0 (eq_bot_of_perfect_of_le_solvable
        (Subgroup.isPerfect_iff.mp (dInf_isPerfect (P 0))) le_top hQs)
  exact parabPair_of_residual_of hS hres hB
    (fun X _ _ hX1 => (IsSimpleGroup.eq_bot_or_eq_top_of_normal X).resolve_left hX1)
    (ParabPair.top_not_of_pCore hpc)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
