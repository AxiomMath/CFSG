module

public import CFSG.Quasithin.MS93.S34RLin
public import CFSG.Quasithin.MS93.S34RAsm
public import CFSG.Quasithin.MS93.SkAssembly

public section

namespace CFSG.Quasithin.MS93.S34D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

section Linear

theorem exists_mul_of_mem_sup {L N : Subgroup G} (hN : N ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ N) : ∃ ℓ ∈ L, ∃ n ∈ N, x = ℓ * n := by
  let S : Subgroup G :=
    { carrier := {y | ∃ ℓ ∈ L, ∃ n ∈ N, y = ℓ * n}
      one_mem' := ⟨1, L.one_mem, 1, N.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨ℓ₁, hℓ₁, n₁, hn₁, rfl⟩ ⟨ℓ₂, hℓ₂, n₂, hn₂, rfl⟩
        have hc : n₁ * ℓ₂ * n₁⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hN hn₁) ℓ₂).1 hℓ₂
        exact ⟨ℓ₁ * (n₁ * ℓ₂ * n₁⁻¹), L.mul_mem hℓ₁ hc, n₁ * n₂, N.mul_mem hn₁ hn₂, by group⟩
      inv_mem' := by
        rintro _ ⟨ℓ, hℓ, n, hn, rfl⟩
        have hc : n⁻¹ * ℓ⁻¹ * n⁻¹⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hn)) ℓ⁻¹).1 (L.inv_mem hℓ)
        exact ⟨n⁻¹ * ℓ⁻¹ * n⁻¹⁻¹, hc, n⁻¹, N.inv_mem hn, by group⟩ }
  have hle : L ⊔ N ≤ S := sup_le (fun ℓ hℓ => ⟨ℓ, hℓ, 1, N.one_mem, (mul_one ℓ).symm⟩)
    (fun n hn => ⟨1, L.one_mem, n, hn, (one_mul n).symm⟩)
  exact hle hx

variable [Finite G] {M T L : Subgroup G}

theorem le_sup_pCoreOf_of_le (h : PUHyp M T L) {M₁ T₁ : Subgroup G} (h₁ : PUHyp M₁ T₁ L)
    (hT : T₁ ≤ T) (hlin : T₁ ≤ L ⊔ pCoreOf 2 M) : T₁ ≤ L ⊔ pCoreOf 2 M₁ := by
  have hM₁M : M₁ ≤ M := by
    rw [h₁.eq_sup, h.eq_sup]
    exact sup_le_sup_left hT L
  have hQL : pCoreOf 2 M ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_le' M).trans h.le_normalizer
  have hinf : M₁ ⊓ pCoreOf 2 M ≤ pCoreOf 2 M₁ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer (hM₁M.trans (le_normalizer_pCoreOf M))) ?_
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right
  intro t ht
  obtain ⟨ℓ, hℓ, x, hx, rfl⟩ := exists_mul_of_mem_sup hQL (hlin ht)
  have hxM₁ : x ∈ M₁ := by
    have hℓ₁ : ℓ ∈ M₁ := h₁.L_le hℓ
    have h' : ℓ⁻¹ * (ℓ * x) ∈ M₁ := M₁.mul_mem (M₁.inv_mem hℓ₁) (h₁.le ht)
    simpa using h'
  exact Subgroup.mul_mem_sup hℓ (hinf ⟨hxM₁, hx⟩)

theorem le_linPart_of_le_sup (h : PUHyp M T L) {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (β : ↥(Uq M T L) →* Multiplicative (Fin 1 → ι → F))
    (hL : ∀ a ∈ L, ∃ γ : GL ι F, IsCoordAct β a (γ : Matrix ι ι F).mulVec)
    (hlin : T ≤ L ⊔ pCoreOf 2 M) : T ≤ S34R.linPart h β := by
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hX : L ⊔ pCoreOf 2 M ≤ coordGroup β ⊤ M hMV := by
    refine sup_le (fun a ha => ?_) (fun x hx => ?_)
    · obtain ⟨γ, hγ⟩ := hL a ha
      exact ⟨h.L_le ha, ⟨γ, Subgroup.mem_top γ⟩, hγ⟩
    · exact ⟨pCoreOf_le' M hx, (S34R.pCoreOf_le_linPart h β hx).2⟩
  intro t ht
  exact ⟨ht, (hX (hlin ht)).2⟩

theorem sl3Full_of_le_sup (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hlin : T ≤ L ⊔ pCoreOf 2 M) : IsSL3Full M T L := by
  obtain ⟨hX, hZU, n, F, _, _, α, hcard, hα, -, -, β, hβ, hβker, hβα⟩ := hU
  refine S34R.sl3Full_of_le_linPart h hcard hα hX hZU hβ hβker hβα
    (le_linPart_of_le_sup h β (fun a ha => ⟨(α ⟨a, ha⟩ : GL (Fin 3) F), ?_⟩) hlin)
  intro u v huv
  simpa [moduleAct] using hβα ⟨a, ha⟩ u v huv 0

theorem sp4Full_of_le_sup (h : PUHyp M T L) (hU : IsSp4U M T L)
    (hlin : T ≤ L ⊔ pCoreOf 2 M) : IsSp4Full M T L := by
  rcases hU with ⟨k, F, _, _, α, hk, hcard, hα, hLV, hZV, β, hβ, hβker, hβα⟩ | ⟨α, hα, hnat⟩
  · refine S34R.sp4Full_of_le_linPart h hk hcard hα hLV hZV hβ hβker hβα
      (le_linPart_of_le_sup h β (fun a ha => ⟨(α ⟨a, ha⟩ : GL (Fin 2 ⊕ Fin 2) F), ?_⟩) hlin)
    intro u v huv
    simpa [moduleAct] using hβα ⟨a, ha⟩ u v huv 0
  · exact ⟨1, ZMod 2, inferInstance, inferInstance, α, le_rfl, by simp, hα, hnat⟩

end Linear

section End

variable [Finite G]

@[expose] def EndConcl (T L : Subgroup G) : Prop :=
  ∃ (M₁ T₁ : Subgroup G) (h₁ : PUHyp M₁ T₁ L), T₁ ≤ T ∧ PUMin M₁ T₁ L ∧
    (critDist (puAmalgam h₁.le) = 2 ∨
      ((IsSL3U M₁ T₁ L → IsSL3Full M₁ T₁ L) ∧ (IsSp4U M₁ T₁ L → IsSp4Full M₁ T₁ L)))

variable {M T L : Subgroup G}

theorem endConcl_of_le_sup (hred : PUReduce) (h : PUHyp M T L)
    (hlin : T ≤ L ⊔ pCoreOf 2 M) : EndConcl T L := by
  obtain ⟨M₁, T₁, h₁, hT₁, hmin₁, -⟩ := exists_minimal_reduction hred h
  have hlin₁ := le_sup_pCoreOf_of_le h h₁ hT₁ (hT₁.trans hlin)
  exact ⟨M₁, T₁, h₁, hT₁, hmin₁,
    Or.inr ⟨fun hU => sl3Full_of_le_sup h₁ hU hlin₁, fun hU => sp4Full_of_le_sup h₁ hU hlin₁⟩⟩

theorem endConcl_of_charCore_good (hred : PUReduce) (h : PUHyp M T L)
    (hgood : (L ⊔ charCore T (T ⊓ (L ⊔ pCoreOf 2 M))) ⊓ pCoreOf 2 M ≤
      charCore T (T ⊓ (L ⊔ pCoreOf 2 M))) : EndConcl T L := by
  have hT₁T : charCore T (T ⊓ (L ⊔ pCoreOf 2 M)) ≤ T := charCore_le_self _ _
  obtain ⟨h₁, -⟩ := hred G M T L _ h hT₁T (charCore_characteristic T _) hgood
    (h.ne_bot_of_inf_le hgood)
  have hlin : charCore T (T ⊓ (L ⊔ pCoreOf 2 M)) ≤ L ⊔ pCoreOf 2 M :=
    (charCore_le _ _).trans inf_le_right
  obtain ⟨M₂, T₂, h₂, hT₂, hmin₂, hor⟩ :=
    endConcl_of_le_sup hred h₁ (le_sup_pCoreOf_of_le h h₁ hT₁T hlin)
  exact ⟨M₂, T₂, h₂, hT₂.trans hT₁T, hmin₂, hor⟩

end End

section Inputs

@[expose] def S34DEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    2 < critDist (puAmalgam h.le) → EndConcl T L

@[expose] def S34DEndNL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    2 < critDist (puAmalgam h.le) →
    ¬ (L ⊔ charCore T (T ⊓ (L ⊔ pCoreOf 2 M))) ⊓ pCoreOf 2 M ≤
      charCore T (T ⊓ (L ⊔ pCoreOf 2 M)) →
    EndConcl T L

theorem end_of_endNL (hred : PUReduce) (hNL : S34DEndNL) : S34DEnd := by
  intro G _ _ M T L h hb
  by_cases hgood : (L ⊔ charCore T (T ⊓ (L ⊔ pCoreOf 2 M))) ⊓ pCoreOf 2 M ≤
      charCore T (T ⊓ (L ⊔ pCoreOf 2 M))
  · exact endConcl_of_charCore_good hred h hgood
  · exact hNL G M T L h hb hgood

variable [Finite G] {L : Subgroup G}

theorem endConcl_of_desc (hred : PUReduce) (hdesc : S34R.S34RDesc) :
    ∀ (n : ℕ) (M T : Subgroup G), PUHyp M T L → Nat.card T = n → EndConcl T L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M T h hn
    obtain ⟨M₁, T₁, h₁, hT₁, hmin₁, -⟩ := exists_minimal_reduction hred h
    by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
    · exact ⟨M₁, T₁, h₁, hT₁, hmin₁, Or.inl hb₁⟩
    by_cases hgood : (IsSL3U M₁ T₁ L → IsSL3Full M₁ T₁ L) ∧ (IsSp4U M₁ T₁ L → IsSp4Full M₁ T₁ L)
    · exact ⟨M₁, T₁, h₁, hT₁, hmin₁, Or.inr hgood⟩
    have hpos := h₁.critDist_pos
    obtain ⟨m, hm⟩ := h₁.critDist_even
    have hb' : 2 < critDist (puAmalgam h₁.le) := by omega
    have hbad : (IsSL3U M₁ T₁ L ∧ ¬ IsSL3Full M₁ T₁ L) ∨
        (IsSp4U M₁ T₁ L ∧ ¬ IsSp4Full M₁ T₁ L) := by
      rcases not_and_or.1 hgood with h1 | h1
      · exact Or.inl (not_imp.1 h1)
      · exact Or.inr (not_imp.1 h1)
    obtain ⟨T', hT', hne, h'⟩ := hdesc G M₁ T₁ L h₁ hmin₁ hb' hbad
    have hlt : Nat.card T' < n :=
      hn ▸ lt_of_lt_of_le (Subgroup.card_lt_of_lt (lt_of_le_of_ne hT' hne))
        (Subgroup.card_le_of_le hT₁)
    obtain ⟨M₂, T₂, h₂, hT₂, hmin₂, hor⟩ := ih _ hlt (L ⊔ T') T' h' rfl
    exact ⟨M₂, T₂, h₂, hT₂.trans (hT'.trans hT₁), hmin₂, hor⟩

theorem end_of_desc (hred : PUReduce) (hdesc : S34R.S34RDesc) : S34DEnd :=
  fun _ _ _ M T _ h _ => endConcl_of_desc hred hdesc _ M T h rfl

end Inputs

end CFSG.Quasithin.MS93.S34D
