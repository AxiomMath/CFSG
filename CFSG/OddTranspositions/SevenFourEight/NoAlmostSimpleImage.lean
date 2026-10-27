module

public import CFSG.OddTranspositions.SevenFourEight.SubPairThreeTransp
public import CFSG.OddTranspositions.SevenFourEight.ImageSecondKind
import CFSG.OddTranspositions.SevenFourEight.PrimeOrder
import CFSG.OddTranspositions.SevenThreeConclusion
import CFSG.OddTranspositions.HalphaCard
import CFSG.Quasithin.Background.SimsG46Graph

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_almostSimpleCase_imageClass
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hnot3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hmin : SmallerTwoStar (Nat.card G))
    (hHns : ¬ Group.IsSolvable ↥(Halpha D hC.alpha)) : ¬ AlmostSimpleCase (↥(Halpha D hC.alpha) ⧸ CFSG.solvableRadical ↥(Halpha D hC.alpha)) (imageClass hC) := by
  classical
  rintro ⟨M₀, hM₀n, -, -, hM₀s, hCM₀, -, -, hcls⟩
  have := hM₀n
  have hL : LocalSecond D := localSecond_of_forall_secondKind hsecond
  obtain ⟨p, hp, hpA⟩ := exists_prime_orderOf_eq_AalphaStar hC hsecond
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨w, hw, hw3⟩ := sevenThree hC hrad hL hpA hnot3
    exact hw3 (hpA w hw)
  have hW1 : ∀ a ∈ hC.alpha, ∀ c ∈ hC.alpha, Commute a c → a = c :=
    sixSeven hC (QZ.faithfulOnBlocks_of_localSecond hC hrad hL)
      (fun u _ v _ w h => hsecond u w v h)
  have hconjD : ∀ a ∈ D, ∃ g : G, g * hC.d * g⁻¹ = a := by
    intro a ha
    obtain ⟨d₀, hd₀⟩ := hC.setup.isClass
    have h1 : IsConj d₀ hC.d := (Set.ext_iff.mp hd₀ hC.d).mp hC.hd
    have h2 : IsConj d₀ a := (Set.ext_iff.mp hd₀ a).mp ha
    exact isConj_iff.mp (h1.symm.trans h2)
  have hnorm : ∀ h : G, h * hC.d * h⁻¹ ∈ hC.alpha →
      ∀ z, z ∈ hC.alpha ↔ h * z * h⁻¹ ∈ hC.alpha := by
    intro h hh
    have hmem : h ∈ Subgroup.normalizer hC.alpha := by
      by_contra hn
      exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hn) hh
        ⟨hC.d, hC.d_mem_alpha, rfl⟩
    exact hmem
  have hkey : ∀ a ∈ D, ∀ c ∈ D, ¬ Commute a c → 3 ∣ orderOf (a * c) →
      ∀ g : G, g⁻¹ * a * g ∈ hC.alpha → g⁻¹ * c * g ∈ hC.alpha := by
    intro a _ c hc hac h3 g hga
    obtain ⟨h, hh⟩ := hconjD _ (hC.isBlock_alpha.subset hga)
    have hhα : h * hC.d * h⁻¹ ∈ hC.alpha := by
      rw [hh]
      exact hga
    have hk : (g * h) * hC.d * (g * h)⁻¹ = a := by
      calc (g * h) * hC.d * (g * h)⁻¹ = g * (h * hC.d * h⁻¹) * g⁻¹ := by group
        _ = a := by rw [hh]; group
    have hck : (g * h)⁻¹ * c * (g * h) ∈ hC.alpha := by
      by_contra hcα
      have hc'D : (g * h)⁻¹ * c * (g * h) ∈ D := by
        simpa using hC.setup.normal (g * h)⁻¹ c hc
      have hc'u : ¬ Commute ((g * h)⁻¹ * c * (g * h)) hC.d := by
        intro hcomm
        apply hac
        have h' := (Commute.conj_iff (g * h)).mpr hcomm.symm
        rwa [hk, show (g * h) * ((g * h)⁻¹ * c * (g * h)) * (g * h)⁻¹ = c by group] at h'
      have hc'A : (g * h)⁻¹ * c * (g * h) ∈ AalphaStar D hC.alpha := by
        rw [hC.AalphaStar_eq_diff_alpha]
        exact ⟨⟨hc'D, hc'u⟩, hcα⟩
      have hord : orderOf (hC.d * ((g * h)⁻¹ * c * (g * h))) = orderOf (a * c) := by
        rw [show hC.d * ((g * h)⁻¹ * c * (g * h)) = (g * h)⁻¹ * (a * c) * (g * h) by
          rw [← hk]; group]
        refine (SemiconjBy.orderOf_eq (g * h)⁻¹ ?_).symm
        unfold SemiconjBy
        group
      rw [hpA _ hc'A] at hord
      have h3p : 3 ∣ p := by
        rw [hord]
        exact h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
    have h' := (hnorm h hhα (h⁻¹ * (g⁻¹ * c * g) * h)).mp (by
      rw [show h⁻¹ * (g⁻¹ * c * g) * h = (g * h)⁻¹ * c * (g * h) by group]
      exact hck)
    rwa [show h * (h⁻¹ * (g⁻¹ * c * g) * h) * h⁻¹ = g⁻¹ * c * g by group] at h'
  obtain ⟨x, hx⟩ := imageClass_nonempty hC
  have hS := setup_quotient hC hHns
  have hsecΘ : ∀ a b t, IsTriangle (imageClass hC) a b t → orderOf (a * t * b) = 4 :=
    fun _ _ _ h => orderOf_eq_four_of_isTriangle_imageClass hC hL hHns h
  have hcardY : Nat.card ↥(M₀ ⊔ Subgroup.zpowers x) < Nat.card G :=
    (Subgroup.card_le_card_group _).trans_lt (card_quotient_Halpha_lt hC hrad)
  have h3Λ := threeTransp_conjSet_of_secondKind hS hsecΘ hM₀s hCM₀ hx (hcls x hx) hmin hcardY
  obtain ⟨hΛcls, hΛodd, hΛgen⟩ := hcls x hx
  have hSΛ : Setup ↥(M₀ ⊔ Subgroup.zpowers x) (conjSet M₀ x) := ⟨hΛcls, hΛodd, hΛgen⟩
  have hΛΘ : ∀ y ∈ conjSet M₀ x, y.1 ∈ imageClass hC := by
    rintro y ⟨m, -, hy⟩
    rw [hy]
    exact hS.normal m x hx
  have hM1 : M₀ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot M₀).mp inferInstance
  have hMK : M₀ ≤ M₀ ⊔ Subgroup.zpowers x := le_sup_left
  have hYns : ¬ Group.IsSolvable ↥(M₀ ⊔ Subgroup.zpowers x) := by
    intro hKs
    have : Group.IsSolvable M₀ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMK)
    exact not_commute_of_centralizer_eq_bot hCM₀ hM1 (IsSimpleGroup.comm_iff_isSolvable.mpr this)
  obtain ⟨a₁, ha₁, a₂, ha₂, hne, hc12⟩ := hSΛ.exists_commute_of_not_isSolvable hYns
  set Γ : SimpleGraph ↥(conjSet M₀ x) := SimpleGraph.fromRel fun a b : ↥(conjSet M₀ x) =>
    (a : ↥(M₀ ⊔ Subgroup.zpowers x)) * b ≠ b * a with hΓ
  have hconn : Γ.Connected := by
    refine (CFSG.Quasithin.SimsG4.connected_iff_transitive (conjSet M₀ x) hSΛ.nonempty
      (fun d hd => hSΛ.oddT.mul_self_eq_one hd) (fun g _ d hd => hSΛ.normal g d hd) ?_).mpr ?_
    · intro a ha b hb
      rcases hSΛ.oddT.2 a ha b hb with h | h
      · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
        · right
          rw [h1]
          exact odd_one
        · exact Or.inl h2
      · exact Or.inr h
    · intro a ha b hb
      obtain ⟨d₀, hd₀⟩ := hΛcls
      have ha' : IsConj d₀ a := by
        rw [hd₀] at ha
        exact ha
      have hb' : IsConj d₀ b := by
        rw [hd₀] at hb
        exact hb
      obtain ⟨c, hc⟩ := isConj_iff.mp (ha'.symm.trans hb')
      refine ⟨c, ?_, hc⟩
      rw [hΛgen]
      exact Subgroup.mem_top c
  obtain ⟨ℓ₁, hℓ₁, e₁⟩ := hΛΘ a₁ ha₁
  obtain ⟨g, hg⟩ := hconjD _ (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hℓ₁))
  have hP₁ : g⁻¹ * (ℓ₁ : G) * g ∈ hC.alpha := by
    rw [← hg, show g⁻¹ * (g * hC.d * g⁻¹) * g = hC.d by group]
    exact hC.d_mem_alpha
  have hstep : ∀ b c : ↥(conjSet M₀ x), Γ.Adj b c →
      ∀ ℓ ∈ DstarH hC, QuotientGroup.mk' _ ℓ = b.1.1 →
      ∀ ℓ' ∈ DstarH hC, QuotientGroup.mk' _ ℓ' = c.1.1 →
      g⁻¹ * (ℓ : G) * g ∈ hC.alpha → g⁻¹ * (ℓ' : G) * g ∈ hC.alpha := by
    intro b c hadj ℓ hℓ eb ℓ' hℓ' ec hP
    have hbc : ¬ Commute b.1 c.1 := by
      intro hcomm
      rw [hΓ, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact h hcomm.eq
      · exact h hcomm.eq.symm
    have hb2 := hSΛ.oddT.mul_self_eq_one b.2
    have hc2 := hSΛ.oddT.mul_self_eq_one c.2
    have ho3 : orderOf (b.1 * c.1) = 3 := by
      have hmem := h3Λ b.1 b.2 c.1 c.2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exfalso
        have e : c.1 = b.1⁻¹ := eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.mp h)
        exact hbc (by rw [e]; exact (Commute.refl _).inv_right)
      · exfalso
        exact hbc ((CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hb2 hc2).mpr
          (by rw [← h]; exact pow_orderOf_eq_one _))
      · exact h
    have hℓD := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hℓ)
    have hℓ'D := DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hℓ')
    have hnc : ¬ Commute (ℓ : G) (ℓ' : G) := by
      intro hcomm
      apply hbc
      have h2 := (commute_coe_iff_of_subgroup.mp hcomm).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥(Halpha D hC.alpha)))
      rw [eb, ec] at h2
      exact commute_coe_iff_of_subgroup.mp h2
    have h3 : 3 ∣ orderOf ((ℓ : G) * (ℓ' : G)) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.solvableRadical ↥(Halpha D hC.alpha)))
        (ℓ * ℓ')
      rwa [map_mul, eb, ec, ← Subgroup.coe_mul, Subgroup.orderOf_coe, ho3] at h
    exact hkey _ hℓD _ hℓ'D hnc h3 g hP
  have hwalk : ∀ (b c : ↥(conjSet M₀ x)) (W : Γ.Walk b c), b = c ∨
      ∀ ℓ ∈ DstarH hC, QuotientGroup.mk' _ ℓ = b.1.1 → g⁻¹ * (ℓ : G) * g ∈ hC.alpha →
      ∀ ℓ' ∈ DstarH hC, QuotientGroup.mk' _ ℓ' = c.1.1 → g⁻¹ * (ℓ' : G) * g ∈ hC.alpha := by
    intro b c W
    induction W with
    | nil => exact Or.inl rfl
    | @cons b m c hadj p ih =>
      right
      intro ℓ hℓ eb hP ℓ' hℓ' ec
      rcases ih with hmc | ih
      · subst hmc
        exact hstep _ _ hadj ℓ hℓ eb ℓ' hℓ' ec hP
      · obtain ⟨ℓm, hℓm, em⟩ := hΛΘ m.1 m.2
        exact ih ℓm hℓm em (hstep _ _ hadj ℓ hℓ eb ℓm hℓm em hP) ℓ' hℓ' ec
  obtain ⟨W⟩ := hconn.preconnected ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
  obtain ⟨ℓ₂, hℓ₂, e₂⟩ := hΛΘ a₂ ha₂
  rcases hwalk _ _ W with h | h
  · exact hne (congrArg Subtype.val h)
  have hP₂ := h ℓ₁ hℓ₁ e₁ hP₁ ℓ₂ hℓ₂ e₂
  have hcomm : Commute ℓ₁ ℓ₂ := by
    refine commute_of_commute_mk_of_ne_H hC hℓ₁ hℓ₂ ?_ ?_
    · rw [e₁, e₂]
      exact commute_coe_iff_of_subgroup.mpr hc12
    · rw [e₁, e₂]
      exact fun h12 => hne (Subtype.ext h12)
  have hcu : Commute hC.d (g⁻¹ * (ℓ₂ : G) * g) := by
    have h' := (Commute.conj_iff g⁻¹).mpr (commute_coe_iff_of_subgroup.mpr hcomm)
    rwa [inv_inv, ← hg, show g⁻¹ * (g * hC.d * g⁻¹) * g = hC.d by group] at h'
  have heq := hW1 _ hC.d_mem_alpha _ hP₂ hcu
  apply hne
  have hℓ : (ℓ₁ : G) = ℓ₂ := by
    rw [← hg, heq]
    group
  have h12 : a₁.1 = a₂.1 := by
    rw [← e₁, ← e₂, Subtype.ext hℓ]
  exact Subtype.ext h12

end CFSG.OddTranspositions

end
