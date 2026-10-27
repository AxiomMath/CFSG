module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusTwoInv
public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusAlt
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Equiv

theorem conj_comm_iff {G : Type*} [Group G] (g h c : G) :
    (g⁻¹ * h * g) * c = c * (g⁻¹ * h * g) ↔ h * (g * c * g⁻¹) = (g * c * g⁻¹) * h := by
  constructor <;> intro H
  · calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [H]
      _ = (g * c * g⁻¹) * h := by group
  · calc (g⁻¹ * h * g) * c = g⁻¹ * (h * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * h) * g := by rw [H]
      _ = c * (g⁻¹ * h * g) := by group

theorem conj_sq_iff {G : Type*} [Group G] (g h : G) : (g⁻¹ * h * g) ^ 2 = 1 ↔ h ^ 2 = 1 := by
  rw [show g⁻¹ * h * g = g⁻¹ * h * g⁻¹⁻¹ by group, conj_pow, conj_eq_one_iff]

section Rows

set_option linter.unusedSectionVars false


theorem noComm_alt_six : ∀ s t : alternatingGroup (Fin 6), s ^ 3 = 1 → s ≠ 1 → t ^ 2 = 1 →
    t ≠ 1 → s * t ≠ t * s := by
  intro s t hs3 hs1 ht2 ht1 hst
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B₀' := finsetSubgroup b0Six b0Six_one b0Six_mul b0Six_inv with hB₀'
  have hB₀A : B₀' ≤ (alternatingGroup (Fin 6)) := fun x hx => b0Six_even x hx
  set B₀ := B₀'.subgroupOf (alternatingGroup (Fin 6)) with hB₀
  have hB₀card : Nat.card B₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀A).toEquiv, card_finsetSubgroup,
      b0Six_card]
  have h9 : (Nat.card (alternatingGroup (Fin 6))).factorization 3 = 2 := by
    rw [card_alt_six, show (360 : ℕ) = 3 ^ 2 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let T₀ : Sylow 3 (alternatingGroup (Fin 6)) := Sylow.ofCard B₀ (by rw [hB₀card, h9]; norm_num)
  have hs : IsPGroup 3 (Subgroup.zpowers s) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1, pow_one]
  obtain ⟨T, hT⟩ := hs.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) T T₀
  have hsT : s ∈ (T : Subgroup (alternatingGroup (Fin 6))) := hT (Subgroup.mem_zpowers s)
  have hgs : g * s * g⁻¹ ∈ B₀ := by
    have h1 : ((g • T : Sylow 3 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6))) = B₀ := by rw [hg]; rfl
    rw [Sylow.coe_subgroup_smul] at h1
    rw [← h1]
    exact ⟨s, hsT, rfl⟩
  have key := b0Six_noInv ((g * s * g⁻¹ : (alternatingGroup (Fin 6))) : Perm (Fin 6)) hgs
    (fun h => hs1 (by
      have h' : g * s * g⁻¹ = 1 := Subtype.ext h
      calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group))
    ((g * t * g⁻¹ : (alternatingGroup (Fin 6))) : Perm (Fin 6)) (Perm.mem_alternatingGroup.mp (g * t * g⁻¹).2)
    (by
      have : (g * t * g⁻¹) ^ 2 = 1 := by rw [conj_pow, ht2]; group
      exact congrArg Subtype.val this)
    (by
      have : (g * t * g⁻¹) * (g * s * g⁻¹) = (g * s * g⁻¹) * (g * t * g⁻¹) := by
        calc (g * t * g⁻¹) * (g * s * g⁻¹) = g * (t * s) * g⁻¹ := by group
          _ = g * (s * t) * g⁻¹ := by rw [hst]
          _ = (g * s * g⁻¹) * (g * t * g⁻¹) := by group
      exact congrArg Subtype.val this)
  apply ht1
  have h' : g * t * g⁻¹ = 1 := Subtype.ext key
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [h']; group

section Row

variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.false_of_ptFree (hcfg : OLCfg P L Q) (hinn : InnerThree ↥L) {Y : Type} [Group Y]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Y)
    (hY : ∀ s t : Y, s ^ 3 = 1 → s ≠ 1 → t ^ 2 = 1 → t ≠ 1 → s * t ≠ t * s) : False := by
  obtain ⟨s, t, hs3, hs1, ht2, ht1, hst⟩ := hcfg.exists_pt_pair hinn
  let π : ↥L →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hker : ∀ l : L, π l = 1 ↔ l ∈ Subgroup.center ↥L := by
    intro l
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) l = 1 := e.injective (by
        rw [map_one]; exact h)
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) l = 1 := (QuotientGroup.eq_one_iff _).mpr h
      show e ((QuotientGroup.mk' (Subgroup.center ↥L)) l) = 1
      rw [h1, map_one]
  refine hY (π s) (π t) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]; exact (hker _).mpr hs3
  · intro h; exact hs1 ((hker _).mp h)
  · rw [← map_pow]; exact (hker _).mpr ht2
  · intro h; exact ht1 ((hker _).mp h)
  · have h1 : π (s * t * s⁻¹ * t⁻¹) = 1 := (hker _).mpr hst
    simp only [map_mul, map_inv] at h1
    calc π s * π t = π s * π t * (π s)⁻¹ * (π t)⁻¹ * (π t * π s) := by group
      _ = π t * π s := by rw [h1, one_mul]


theorem OLCfg.isQuasisimple (hcfg : OLCfg P L Q) : IsQuasisimple ↥L :=
  IsQuasisimple.of_mulEquiv (equivThetaQuotOfBot hcfg.thetaL).symm hcfg.qsL

theorem olRow_four_A6 :
    OLRow (fun T _ => Sec4.IsExtOf T (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3))) := by
  intro X _ _ P L Q hcfg hext
  have hZ6 : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have htc := (Sec4.isTripleCover_iff_isExtOf hcfg.isQuasisimple hZ6).mpr hext
  have hinn : InnerThree ↥L := innerThree_of_range fun σ hσ =>
    Sec12.KS128NotHJTC.mem_range_conj_of_isTripleCover hcfg.perfL (Or.inl htc) hσ
  obtain ⟨-, ⟨e⟩⟩ := htc
  exact hcfg.false_of_ptFree hinn e noComm_alt_six

end Row

set_option maxRecDepth 100000 in
theorem v1Seven_iff : ∀ σ : Perm (Fin 7), Perm.sign σ = 1 →
    (σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ ∧ σ ^ 2 = 1 ↔ σ ∈ v1Seven) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem v2Seven_iff : ∀ σ : Perm (Fin 7), Perm.sign σ = 1 →
    (σ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * σ ∧ σ ^ 2 = 1 ↔ σ ∈ v2Seven) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cyc_mem_b0Seven : swap 0 1 * swap 1 2 ∈ b0Seven ∧ swap 3 4 * swap 4 5 ∈ b0Seven := by
  decide +kernel

theorem twoInvCent_alt_seven : TwoInvCent (alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T
  set B₀' := finsetSubgroup b0Seven b0Seven_one b0Seven_mul b0Seven_inv with hB₀'
  have hB₀A : B₀' ≤ (alternatingGroup (Fin 7)) := fun x hx => b0Seven_even x hx
  set B₀ := B₀'.subgroupOf (alternatingGroup (Fin 7)) with hB₀
  have hB₀card : Nat.card B₀ = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀A).toEquiv, card_finsetSubgroup,
      b0Seven_card]
  have h9 : (Nat.card (alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [card_alt_seven, show (2520 : ℕ) = 3 ^ 2 * 280 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let T₀ : Sylow 3 (alternatingGroup (Fin 7)) := Sylow.ofCard B₀ (by rw [hB₀card, h9]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) T₀ T
  have hT : (T : Subgroup (alternatingGroup (Fin 7))) = B₀.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set c₁ : (alternatingGroup (Fin 7)) := ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.mpr (by decide)⟩ with hc₁
  set c₂ : (alternatingGroup (Fin 7)) := ⟨swap 3 4 * swap 4 5, Perm.mem_alternatingGroup.mpr (by decide)⟩ with hc₂
  have hc₁B : c₁ ∈ B₀ := cyc_mem_b0Seven.1
  have hc₂B : c₂ ∈ B₀ := cyc_mem_b0Seven.2
  set V₁ := (finsetSubgroup v1Seven v1Seven_one v1Seven_mul v1Seven_inv).subgroupOf (alternatingGroup (Fin 7)) with hV₁
  set V₂ := (finsetSubgroup v2Seven v2Seven_one v2Seven_mul v2Seven_inv).subgroupOf (alternatingGroup (Fin 7)) with hV₂
  have hV₁iff : ∀ σ : (alternatingGroup (Fin 7)), σ ∈ V₁ ↔ σ * c₁ = c₁ * σ ∧ σ ^ 2 = 1 := by
    intro σ
    change (σ : Perm (Fin 7)) ∈ v1Seven ↔ _
    rw [← v1Seven_iff σ (Perm.mem_alternatingGroup.mp σ.2)]
    simp only [Subtype.ext_iff, Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one, hc₁]
  have hV₂iff : ∀ σ : (alternatingGroup (Fin 7)), σ ∈ V₂ ↔ σ * c₂ = c₂ * σ ∧ σ ^ 2 = 1 := by
    intro σ
    change (σ : Perm (Fin 7)) ∈ v2Seven ↔ _
    rw [← v2Seven_iff σ (Perm.mem_alternatingGroup.mp σ.2)]
    simp only [Subtype.ext_iff, Subgroup.coe_mul, SubgroupClass.coe_pow, OneMemClass.coe_one, hc₂]
  have hcardV : ∀ (F : Finset (Perm (Fin 7))) (h1 : (1 : Perm (Fin 7)) ∈ F)
      (hmul : ∀ a ∈ F, ∀ b ∈ F, a * b ∈ F) (hinv : ∀ a ∈ F, a⁻¹ ∈ F)
      (heven : ∀ x ∈ F, x ∈ (alternatingGroup (Fin 7))), F.card = 4 →
      Nat.card ((finsetSubgroup F h1 hmul hinv).subgroupOf (alternatingGroup (Fin 7))) = 4 := by
    intro F h1 hmul hinv heven hF
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => heven x hx)).toEquiv,
      card_finsetSubgroup, hF]
  have hR : ∀ (c : (alternatingGroup (Fin 7))) (V : Subgroup (alternatingGroup (Fin 7))), (∀ σ : (alternatingGroup (Fin 7)), σ ∈ V ↔ σ * c = c * σ ∧ σ ^ 2 = 1) →
      ∀ h : (alternatingGroup (Fin 7)), h ∈ V.map (MulAut.conj g).toMonoidHom ↔
        h * (g * c * g⁻¹) = (g * c * g⁻¹) * h ∧ h ^ 2 = 1 := by
    intro c V hV h
    rw [Subgroup.mem_map_equiv, hV]
    have : (MulAut.conj g).symm h = g⁻¹ * h * g := by
      rw [MulAut.conj_symm_apply]
    rw [this, conj_comm_iff, conj_sq_iff]
  have hmemT : ∀ c ∈ B₀, g * c * g⁻¹ ∈ (T : Subgroup (alternatingGroup (Fin 7))) := fun c hc => by
    rw [hT]
    exact ⟨c, hc, rfl⟩
  refine ⟨g * c₁ * g⁻¹, hmemT c₁ hc₁B, g * c₂ * g⁻¹, hmemT c₂ hc₂B,
    V₁.map (MulAut.conj g).toMonoidHom, V₂.map (MulAut.conj g).toMonoidHom, hR c₁ V₁ hV₁iff,
    hR c₂ V₂ hV₂iff, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcardV _ _ _ _ (fun x hx => v1Seven_even x hx) v1Seven_card
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcardV _ _ _ _ (fun x hx => v2Seven_even x hx) v2Seven_card
  · intro h12
    have hV : V₁ = V₂ := Subgroup.map_injective (MulAut.conj g).injective h12
    have hx : (⟨swap 3 4 * swap 5 6, Perm.mem_alternatingGroup.mpr (by decide)⟩ : (alternatingGroup (Fin 7))) ∈ V₁ :=
      v1Seven_mem
    rw [hV] at hx
    exact v1Seven_ne hx

section Row7


theorem olRow_four_A7 :
    OLRow (fun T _ => Sec4.IsExtOf T (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) := by
  intro X _ _ P L Q hcfg hext
  have hZ7 : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hqL : IsQuasisimple ↥L :=
    IsQuasisimple.of_mulEquiv (equivThetaQuotOfBot hcfg.thetaL).symm hcfg.qsL
  obtain ⟨h3, ⟨e⟩⟩ := (Sec4.isTripleCover_iff_isExtOf hqL hZ7).mpr hext
  exact hcfg.false_of_twoInvCent
    (twoInvCent_of_quotient le_rfl h3 (twoInvCent_alt_seven.of_mulEquiv e))

end Row7

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
