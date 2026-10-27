module

public import CFSG.Quasithin.Vol2.Ch3T325M
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem nonempty_sl_equiv_zmod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (n : ℕ) : Nonempty (Matrix.SpecialLinearGroup (Fin n) K ≃*
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  refine ⟨MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom) ?_ ?_⟩
  · ext A i j
    simp
  · ext A i j
    simp

theorem card_of_realizes_top {V : Type} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    (h : D.Realizes H ⊤ ⊥) : Nat.card V = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨-, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  rw [← Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩), Subgroup.card_top]

section Models

variable {G : Type} [Group G] {L V₀ V VM : Subgroup G} [IsMulCommutative ↥VM]
  [IsMulCommutative ↥V₀]

theorem model_facts {D : FFModel} (hD : D.Faithful) (hV₀V : V₀ ≤ V) (hVVM : V ≤ VM)
    (hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G))
    (h : D.Realizes (autOn L VM) (V₀.subgroupOf VM) ⊥) :
    Nonempty (↥(autOn L V) ≃* D.Gam) ∧ D.Realizes (autOn L V₀) ⊤ ⊥ := by
  obtain ⟨π, hπ⟩ := h
  have e1 : ↥(autOn L VM) ≃* D.Gam :=
    (MulEquiv.ofBijective π ⟨injective_of_faithful' hD hπ, hπ.1⟩).symm
  have hcent := inf_centralizer_le_of_faithful hD hLVM ⟨π, hπ⟩
  have heq : L ⊓ Subgroup.centralizer (V : Set G) = L ⊓ Subgroup.centralizer (VM : Set G) :=
    le_antisymm (le_inf inf_le_left ((inf_le_inf_left _ (Subgroup.centralizer_le hV₀V)).trans
      hcent)) (inf_le_inf_left _ (Subgroup.centralizer_le hVVM))
  obtain ⟨e2⟩ := nonempty_autOn_equiv hLV hLVM heq
  exact ⟨⟨e2.trans e1⟩, realizes_restrict (hV₀V.trans hVVM) hLV₀ hLVM ⟨π, hπ⟩⟩

theorem card_a7Four_sec
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    Nat.card (↥(FFModel.a7Four α).sec ⧸
      (FFModel.a7Four α).ker.subgroupOf (FFModel.a7Four α).sec) = 2 ^ 4 := by
  show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
    (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 2 ^ 4
  rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
    Nat.card_fin]

theorem list_of_d310 (hV₀V : V₀ ≤ V) (hVVM : V ≤ VM)
    (hLV₀ : L ≤ Subgroup.normalizer (V₀ : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hLVM : L ≤ Subgroup.normalizer (VM : Set G))
    (h : (∃ n, BinaryNaturalSL (autOn L VM) (V₀.subgroupOf VM) ⊥ 3 n) ∨
      (∃ n, BinaryNaturalSp4 (autOn L VM) (V₀.subgroupOf VM) ⊥ n) ∨
      AlternatingNatural (autOn L VM) (V₀.subgroupOf VM) ⊥ 6 ∨
      BinaryNaturalSL (autOn L VM) (V₀.subgroupOf VM) ⊥ 4 1 ∨
      BinaryNaturalSL (autOn L VM) (V₀.subgroupOf VM) ⊥ 5 1 ∨
      A7Four (autOn L VM) (V₀.subgroupOf VM) ⊥) :
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
        ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 3 n) ∨
      (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(autOn L V) ≃* ↥(StatedSp 2 K)) ∧
        ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSp4 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n) ∨
      (Nonempty (↥(autOn L V) ≃* alternatingGroup (Fin 6)) ∧
        ∃ _ : IsMulCommutative ↥V₀, AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 6) ∨
      (Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
        ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 4 1) ∨
      (Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
        ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 5 1) ∨
      (Nonempty (↥(autOn L V) ≃* alternatingGroup (Fin 7)) ∧ Nat.card V₀ = 2 ^ 4) := by
  rcases h with ⟨n, K, hF, hfin, hcard, hR⟩ | ⟨n, K, hF, hfin, hcard, hR⟩ | hR |
      ⟨K, hF, hfin, hcard, hR⟩ | ⟨K, hF, hfin, hcard, hR⟩ | ⟨α, hR⟩
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFModel.nat_faithful _) hV₀V hVVM hLV₀ hLV hLVM hR
    exact Or.inl ⟨n, K, hF, hfin, hcard, ⟨e.trans (specialLinearGroupEquivStatedSL 3 K).symm⟩,
      inferInstance, K, hF, hfin, hcard, hR'⟩
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFModel.nat_faithful _) hV₀V hVVM hLV₀ hLV hLVM hR
    exact Or.inr (Or.inl ⟨n, K, hF, hfin, hcard, ⟨e⟩, inferInstance, K, hF, hfin, hcard, hR'⟩)
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFC.altDn_faithful (by norm_num)) hV₀V hVVM hLV₀ hLV
      hLVM hR
    exact Or.inr (Or.inr (Or.inl ⟨⟨e⟩, inferInstance, hR'⟩))
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFModel.nat_faithful _) hV₀V hVVM hLV₀ hLV hLVM hR
    obtain ⟨e'⟩ := nonempty_sl_equiv_zmod_two (by rw [hcard, pow_one]) 4
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨(e.trans (specialLinearGroupEquivStatedSL 4 K).symm).trans e'⟩, inferInstance, K, hF,
        hfin, hcard, hR'⟩)))
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFModel.nat_faithful _) hV₀V hVVM hLV₀ hLV hLVM hR
    obtain ⟨e'⟩ := nonempty_sl_equiv_zmod_two (by rw [hcard, pow_one]) 5
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨(e.trans (specialLinearGroupEquivStatedSL 5 K).symm).trans e'⟩, inferInstance, K, hF,
        hfin, hcard, hR'⟩))))
  · obtain ⟨⟨e⟩, hR'⟩ := model_facts (FFC.a7Four_faithful α) hV₀V hVVM hLV₀ hLV hLVM hR
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨e⟩, ?_⟩))))
    rw [card_of_realizes_top hR', card_a7Four_sec]

end Models

end CFSG.Quasithin.H13.T325
