module

public import CFSG.OddTranspositions.PartThree.Twelve.Three
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.Timmesfeld.RootSubgroupBasic
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem alpha_eq_singleton_of_rootBlock_eq_singleton (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC)
    (hsing : rootBlock (imageClass hC) s₀ = {s₀}) :
    hC.alpha = {hC.d} := by
  classical
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs₀ hne
  obtain ⟨x, β, hβ, hxβ⟩ := DstarH_nonempty hC
  set π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) with hπ
  have hxD : π x ∈ imageClass hC := ⟨x, ⟨β, hβ, hxβ⟩, rfl⟩
  obtain ⟨hb1x, -⟩ := rootBlock_input_of_mem hC hs₀ hxD hb1 hne
  have hsingx : rootBlock (imageClass hC) (π x) = {π x} := by
    obtain ⟨d₀, hd₀⟩ := imageClass_isClass hC
    have hs₀' : IsConj d₀ s₀ := by rw [hd₀] at hs₀; exact hs₀
    have hx' : IsConj d₀ (π x) := by rw [hd₀] at hxD; exact hxD
    obtain ⟨g, hg⟩ := isConj_iff.mp ((isConj_comm.mp hs₀').trans hx')
    rw [← hg, ← image_conj_rootBlock (imageClass_isNormalSet hC) g s₀, hsing,
      Set.image_singleton]
  have hsub := hb1x _ (isBlock_blockImage hC hinj hβ) ⟨x, hxβ, rfl⟩
  rw [hsingx] at hsub
  have hβx : β = {(x : G)} := by
    ext y
    constructor
    · intro hy
      have hyH : y ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hy⟩
      have h1 : π ⟨y, hyH⟩ = π x := hsub ⟨⟨y, hyH⟩, hy, rfl⟩
      exact congrArg Subtype.val (hinj ⟨β, hβ, hy⟩ ⟨β, hβ, hxβ⟩ h1)
    · rintro rfl
      exact hxβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff'.mp hβ.1
  have hα : hC.alpha = {g⁻¹ • (x : G)} := by
    rw [← Set.smul_set_singleton, ← hβx, hg, inv_smul_smul]
  have hd := hC.d_mem_alpha
  rw [hα] at hd ⊢
  rw [Set.mem_singleton_iff.mp hd]

section Helpers

variable {K : Type} [Group K]

theorem eq_one_of_mem_center_inf_commutator [Finite K]
    (hodd : Odd (Nat.card ↥(Subgroup.center K ⊓ commutator K))) {z : K}
    (hz : z ∈ Subgroup.center K ⊓ commutator K) (hz2 : z * z = 1) : z = 1 := by
  have h1 : orderOf z ∣ Nat.card ↥(Subgroup.center K ⊓ commutator K) := by
    rw [← Subgroup.orderOf_mk z hz]
    exact orderOf_dvd_natCard _
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h1
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := h1
    omega

end Helpers

@[expose] def IsRootTriple {X : Type} [Group X] (E : Set X) (s : X) : Prop :=
  ∃ y₁ ∈ E, ∃ y₂ ∈ E, ∃ y₃ ∈ E, y₁ ∉ rootBlock E s ∧ y₂ ∉ rootBlock E s ∧
    y₃ ∉ rootBlock E s ∧ Commute y₁ y₂ ∧ Commute y₁ y₃ ∧ Commute y₂ y₃ ∧ s = y₁ * y₂ * y₃

theorem mul_mem_commutator_of_mem_DstarH (hC : HypothesisC D) {x y : Halpha D hC.alpha}
    (hx : x ∈ DstarH hC) (hy : y ∈ DstarH hC) : x * y ∈ commutator (Halpha D hC.alpha) := by
  obtain ⟨d₀, hd₀⟩ := DstarH_isClass hC
  have hxy : IsConj x y := by
    rw [hd₀] at hx hy
    exact (isConj_comm.mp hx).trans hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right ((DstarH_isOddTransp hC).mul_self_eq_one hx)
  have e : x * (c * x * c⁻¹) = ⁅x⁻¹, c⁆ := by
    rw [commutatorElement_def, inv_inv, hxinv]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem mem_commutator_or_mul_mem_of_mem_DstarH (hC : HypothesisC D) {x : Halpha D hC.alpha}
    (hx : x ∈ DstarH hC) (h : Halpha D hC.alpha) :
    h ∈ commutator (Halpha D hC.alpha) ∨ x * h ∈ commutator (Halpha D hC.alpha) := by
  have hN : (commutator (Halpha D hC.alpha)).Normal := inferInstance
  have hx2 : x * x = 1 := (DstarH_isOddTransp hC).mul_self_eq_one hx
  have hmem : h ∈ Subgroup.closure (DstarH hC) := by
    rw [DstarH_closure_eq_top hC]
    exact Subgroup.mem_top h
  induction hmem using Subgroup.closure_induction with
  | mem y hy => exact Or.inr (mul_mem_commutator_of_mem_DstarH hC hx hy)
  | one => exact Or.inl (Subgroup.one_mem _)
  | mul a b _ _ ha hb =>
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Subgroup.mul_mem _ ha hb)
    · right
      have e : x * (a * b) = x * a * x⁻¹ * (x * b) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hN.conj_mem a ha x) hb
    · right
      rw [← mul_assoc]
      exact Subgroup.mul_mem _ ha hb
    · left
      have e : a * b = x⁻¹ * (x * a) * x⁻¹⁻¹ * (x⁻¹ * x⁻¹) * (x * b) := by group
      have hxx : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx2, inv_one]
      rw [e, hxx, mul_one]
      exact Subgroup.mul_mem _ (hN.conj_mem _ ha x⁻¹) hb
  | inv a _ ha =>
    rcases ha with ha | ha
    · exact Or.inl (Subgroup.inv_mem _ ha)
    · right
      have e : x * a⁻¹ = x * (x * a)⁻¹ * x⁻¹ * (x * x) := by group
      rw [e, hx2, mul_one]
      exact hN.conj_mem _ (Subgroup.inv_mem _ ha) x

theorem eq_of_mem_center_of_mul_self_eq_one (hC : HypothesisC D)
    (hodd : Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓
      commutator (Halpha D hC.alpha))))
    {z z' : Halpha D hC.alpha} (hz : z ∈ Subgroup.center (Halpha D hC.alpha))
    (hz' : z' ∈ Subgroup.center (Halpha D hC.alpha)) (h2 : z * z = 1) (h2' : z' * z' = 1)
    (h1 : z ≠ 1) (h1' : z' ≠ 1) : z = z' := by
  obtain ⟨x, hx⟩ := DstarH_nonempty hC
  have hout : ∀ w ∈ Subgroup.center (Halpha D hC.alpha), w * w = 1 → w ≠ 1 →
      x * w ∈ commutator (Halpha D hC.alpha) := fun w hw hw2 hw1 =>
    (mem_commutator_or_mul_mem_of_mem_DstarH hC hx w).resolve_left fun hwc =>
      hw1 (eq_one_of_mem_center_inf_commutator hodd ⟨hw, hwc⟩ hw2)
  have hmem : (x * z)⁻¹ * (x * z') ∈ commutator (Halpha D hC.alpha) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hout z hz h2 h1)) (hout z' hz' h2' h1')
  have e : (x * z)⁻¹ * (x * z') = z⁻¹ * z' := by group
  rw [e] at hmem
  have hcen : z⁻¹ * z' ∈ Subgroup.center (Halpha D hC.alpha) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hz) hz'
  have hsq : z⁻¹ * z' * (z⁻¹ * z') = 1 := by
    have hc : z' * z⁻¹ = z⁻¹ * z' :=
      Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) z'
    calc z⁻¹ * z' * (z⁻¹ * z') = z⁻¹ * (z' * z⁻¹) * z' := by group
      _ = z⁻¹ * z⁻¹ * (z' * z') := by rw [hc]; group
      _ = 1 := by rw [← mul_inv_rev, h2, h2', inv_one, one_mul]
  exact inv_mul_eq_one.mp (eq_one_of_mem_center_inf_commutator hodd ⟨hcen, hmem⟩ hsq)

theorem Halpha_le_centralizer_of_mem_alpha (hC : HypothesisC D) {a : G}
    (ha : a ∈ hC.alpha) : Halpha D hC.alpha ≤ Subgroup.centralizer {a} := by
  rw [Halpha, Subgroup.closure_le]
  rintro z ⟨γ, hγ, hzγ⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (hγ.2.2.2 a ha z hzγ).eq.symm

theorem d_mem_Halpha_of_isRootTriple (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC)
    (htri : IsRootTriple (imageClass hC) s₀)
    (hodd : Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓
      commutator (Halpha D hC.alpha)))) :
    hC.d ∈ Halpha D hC.alpha := by
  classical
  have hinj := injOn_mk_DstarH_of_rootBlock_ne hC hMZ hs₀ hne
  obtain ⟨x, hx, rfl⟩ := hs₀
  obtain ⟨_, ⟨b₁, hb₁, rfl⟩, _, ⟨b₂, hb₂, rfl⟩, _, ⟨b₃, hb₃, rfl⟩, hn₁, hn₂, hn₃, h12, h13,
    h23, hprod⟩ := htri
  set π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) with hπ
  obtain ⟨β, hβ, hxβ⟩ : ∃ β ∈ Dalpha D hC.alpha, (x : G) ∈ β := id hx
  have hsub : blockImage hC β ⊆ rootBlock (imageClass hC) (π x) :=
    hb1 _ (isBlock_blockImage hC hinj hβ) ⟨x, hxβ, rfl⟩
  have hbβ : ∀ b : Halpha D hC.alpha, π b ∉ rootBlock (imageClass hC) (π x) → (b : G) ∉ β :=
    fun b hb hbβ => hb (hsub ⟨b, hbβ, rfl⟩)
  have hc : ∀ {a b : Halpha D hC.alpha}, a ∈ DstarH hC → b ∈ DstarH hC →
      Commute (π a) (π b) → Commute a b := fun ha hb h =>
    commute_of_commute_mk_of_le_center hC hMZ ha hb h
  have hx₁ : Commute x b₁ := hc hx hb₁ (by
    rw [hprod]; exact ((Commute.refl _).mul_left h12.symm).mul_left h13.symm)
  have hx₂ : Commute x b₂ := hc hx hb₂ (by
    rw [hprod]; exact (h12.mul_left (Commute.refl _)).mul_left h23.symm)
  have hx₃ : Commute x b₃ := hc hx hb₃ (by
    rw [hprod]; exact (h13.mul_left h23).mul_left (Commute.refl _))
  have h₁₂ : Commute b₁ b₂ := hc hb₁ hb₂ h12
  have h₁₃ : Commute b₁ b₃ := hc hb₁ hb₃ h13
  have h₂₃ : Commute b₂ b₃ := hc hb₂ hb₃ h23
  have hD : ∀ {b : Halpha D hC.alpha}, b ∈ DstarH hC → (b : G) ∈ D :=
    fun hb => DalphaStar_subset hC.isBlock_alpha hb
  have hsq : ∀ {b : Halpha D hC.alpha}, b ∈ DstarH hC → b * b = 1 :=
    fun hb => (DstarH_isOddTransp hC).mul_self_eq_one hb
  have hxeq : x = b₁ * b₂ * b₃ := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq hx)
    have hzM : x⁻¹ * (b₁ * b₂ * b₃) ∈ Subgroup.center (Halpha D hC.alpha) := by
      apply hMZ
      apply (QuotientGroup.eq_one_iff _).mp
      change π (x⁻¹ * (b₁ * b₂ * b₃)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, ← hprod, inv_mul_cancel]
    have hzC : x⁻¹ * (b₁ * b₂ * b₃) ∈ commutator (Halpha D hC.alpha) := by
      have e : x⁻¹ * (b₁ * b₂ * b₃) = x * b₁ * (b₂ * b₃) := by rw [hxinv]; group
      rw [e]
      exact Subgroup.mul_mem _ (mul_mem_commutator_of_mem_DstarH hC hx hb₁)
        (mul_mem_commutator_of_mem_DstarH hC hb₂ hb₃)
    have hz2 : x⁻¹ * (b₁ * b₂ * b₃) * (x⁻¹ * (b₁ * b₂ * b₃)) = 1 := by
      refine CFSG.Timmesfeld.mul_self_eq_one_of_mem_closure (S := {x, b₁, b₂, b₃}) ?_ ?_ ?_
      · rintro p (rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl) -
        all_goals first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
      · rintro p (rfl | rfl | rfl | rfl)
        exacts [hsq hx, hsq hb₁, hsq hb₂, hsq hb₃]
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
          (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp)))
    exact inv_mul_eq_one.mp (eq_one_of_mem_center_inf_commutator hodd ⟨hzM, hzC⟩ hz2)
  have hdc : ∀ {b : Halpha D hC.alpha}, b ∈ DstarH hC → Commute (b : G) hC.d :=
    fun hb => (hC.DalphaStar_subset_commute hb).2
  have hcG : ∀ {a b : Halpha D hC.alpha}, Commute a b → Commute (a : G) (b : G) :=
    fun h => congrArg Subtype.val h.eq
  set S0 : Set G := {(x : G), (b₁ : G), (b₂ : G), (b₃ : G), hC.d} with hS0
  have hS0c : ∀ p ∈ S0, ∀ q ∈ S0, Commute p q := by
    have := hcG hx₁; have := hcG hx₂; have := hcG hx₃
    have := hcG h₁₂; have := hcG h₁₃; have := hcG h₂₃
    have := hdc hx; have := hdc hb₁; have := hdc hb₂; have := hdc hb₃
    rintro p (rfl | rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact Commute.refl _ | assumption | exact Commute.symm ‹_›
  have hS0sq : ∀ p ∈ S0, p * p = 1 := by
    rintro p (rfl | rfl | rfl | rfl | rfl)
    exacts [hC.setup.oddT.mul_self_eq_one (hD hx), hC.setup.oddT.mul_self_eq_one (hD hb₁),
      hC.setup.oddT.mul_self_eq_one (hD hb₂), hC.setup.oddT.mul_self_eq_one (hD hb₃),
      hC.setup.oddT.mul_self_eq_one hC.hd]
  obtain ⟨S, hS⟩ := (CFSG.Timmesfeld.isPGroup_closure_of_pairwise
    (fun p hp q hq _ => hS0c p hp q hq) hS0sq).exists_le_sylow
  have hmemS : ∀ p ∈ S0, p ∈ (S : Subgroup G) := fun p hp => hS (Subgroup.subset_closure hp)
  have hxS : (x : G) ∈ (S : Set G) ∩ D := ⟨hmemS _ (by simp [hS0]), hD hx⟩
  have hdS : hC.d ∈ (S : Set G) ∩ D := ⟨hmemS _ (by simp [hS0]), hC.hd⟩
  obtain ⟨g, hg, hgx⟩ := sylow_inter_D_transitive hC.setup.isClass hC.setup.oddT S hxS hdS
  have hgβ : (fun y => g * y * g⁻¹) '' β = hC.alpha := by
    have hcls : (fun y => g * y * g⁻¹) '' β ∈ blockClass hC.alpha := by
      obtain ⟨c, hcβ⟩ := mem_blockClass_iff.mp hβ.1
      refine mem_blockClass_iff.mpr ⟨g * c, ?_⟩
      rw [hcβ, Set.image_image]
      congr 1
      funext y
      group
    rcases eq_or_disjoint_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hcls
      (mem_blockClass_self _) with h | h
    · exact h
    · exact (Set.disjoint_left.mp h ⟨_, hxβ, hgx⟩ hC.d_mem_alpha).elim
  have hconj : ∀ {b : Halpha D hC.alpha}, b ∈ DstarH hC → (b : G) ∈ (S : Subgroup G) →
      (b : G) ∉ β → g * (b : G) * g⁻¹ ∈ Halpha D hC.alpha := by
    intro b hb hbS hbn
    have hbSD : (b : G) ∈ (S : Set G) ∩ D := ⟨hbS, hD hb⟩
    have hgb : g * (b : G) * g⁻¹ ∈ (S : Set G) ∩ D :=
      (Subgroup.mem_set_normalizer_iff.mp hg (b : G)).mp hbSD
    have hcomm : Commute (g * (b : G) * g⁻¹) hC.d :=
      hC.setup.oddT.commute_of_isPGroup S.isPGroup' hgb.2 hC.hd hgb.1 hdS.1
    have hnα : g * (b : G) * g⁻¹ ∉ hC.alpha := by
      intro hmem
      have hmem' : g * (b : G) * g⁻¹ ∈ (fun y => g * y * g⁻¹) '' β := by
        rw [hgβ]
        exact hmem
      obtain ⟨y, hy, hyb⟩ := hmem'
      have hyb' : y = (b : G) := by simpa using hyb
      exact hbn (hyb' ▸ hy)
    have hstar : g * (b : G) * g⁻¹ ∈ DalphaStar D hC.alpha := by
      rcases (Set.ext_iff.mp hC.eq_alpha_union _).mp hgb.2 with (h | h) | h
      · exact absurd h hnα
      · exact h
      · rw [hC.AalphaStar_eq_diff_alpha] at h
        exact absurd hcomm h.1.2
    exact Subgroup.subset_closure hstar
  have e : hC.d = g * (b₁ : G) * g⁻¹ * (g * (b₂ : G) * g⁻¹) * (g * (b₃ : G) * g⁻¹) := by
    rw [← hgx, hxeq]
    push_cast
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hconj hb₁ (hmemS _ (by simp [hS0])) (hbβ b₁ hn₁))
    (hconj hb₂ (hmemS _ (by simp [hS0])) (hbβ b₂ hn₂)))
    (hconj hb₃ (hmemS _ (by simp [hS0])) (hbβ b₃ hn₃))

theorem mem_center_of_mem_alpha (hC : HypothesisC D) (hdH : hC.d ∈ Halpha D hC.alpha)
    {a : G} (ha : a ∈ hC.alpha) :
    ∃ haH : a ∈ Halpha D hC.alpha,
      (⟨a, haH⟩ : Halpha D hC.alpha) ∈ Subgroup.center (Halpha D hC.alpha) := by
  obtain ⟨k, hk⟩ := isConj_iff.mp (hC.setup.isConj hC.hd (hC.isBlock_alpha.subset ha))
  have hkN : k ∈ Subgroup.normalizer hC.alpha := by
    by_contra hkN
    exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hkN) ha
      ⟨hC.d, hC.d_mem_alpha, hk⟩
  have haH : a ∈ Halpha D hC.alpha := by
    rw [← hk]
    exact (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_Halpha hC.setup.normal hkN) _).mp hdH
  refine ⟨haH, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp
    (Halpha_le_centralizer_of_mem_alpha hC ha h.2)

theorem mul_self_eq_one_and_ne_one_of_mem_alpha (hC : HypothesisC D) {b : G}
    (hb : b ∈ hC.alpha) (hbH : b ∈ Halpha D hC.alpha) :
    (⟨b, hbH⟩ : Halpha D hC.alpha) * ⟨b, hbH⟩ = 1 ∧ (⟨b, hbH⟩ : Halpha D hC.alpha) ≠ 1 := by
  have hbD := hC.isBlock_alpha.subset hb
  refine ⟨Subtype.ext (hC.setup.oddT.mul_self_eq_one hbD), fun h1 => ?_⟩
  have h2 := hC.setup.oddT.1 b hbD
  rw [show b = 1 from congrArg Subtype.val h1, orderOf_one] at h2
  omega

theorem alpha_eq_singleton_of_isRootTriple (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC)
    (htri : IsRootTriple (imageClass hC) s₀)
    (hodd : Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓
      commutator (Halpha D hC.alpha)))) :
    hC.alpha = {hC.d} := by
  have hdH := d_mem_Halpha_of_isRootTriple hC hMZ hs₀ hb1 hne htri hodd
  obtain ⟨hdH', hdZ⟩ := mem_center_of_mem_alpha hC hdH hC.d_mem_alpha
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hC.d_mem_alpha, fun a ha => ?_⟩
  obtain ⟨haH, haZ⟩ := mem_center_of_mem_alpha hC hdH ha
  obtain ⟨ha2, ha1⟩ := mul_self_eq_one_and_ne_one_of_mem_alpha hC ha haH
  obtain ⟨hd2, hd1⟩ := mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hdH'
  exact congrArg Subtype.val
    (eq_of_mem_center_of_mul_self_eq_one hC hodd haZ hdZ ha2 hd2 ha1 hd1)

theorem false_of_isRootTriple_of_notMem_commutator (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s₀ : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs₀ : s₀ ∈ imageClass hC)
    (hb1 : ∀ B, IsBlock (imageClass hC) B → s₀ ∈ B → B ⊆ rootBlock (imageClass hC) s₀)
    (hne : rootBlock (imageClass hC) s₀ ≠ imageClass hC)
    (htri : IsRootTriple (imageClass hC) s₀)
    (hodd : Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓
      commutator (Halpha D hC.alpha))))
    (hX : s₀ ∉ commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    False := by
  have hdH := d_mem_Halpha_of_isRootTriple hC hMZ hs₀ hb1 hne htri hodd
  obtain ⟨hdH', hdZ⟩ := mem_center_of_mem_alpha hC hdH hC.d_mem_alpha
  obtain ⟨hd2, hd1⟩ := mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hdH'
  obtain ⟨x, hx, rfl⟩ := hs₀
  have hxd : x * ⟨hC.d, hdH'⟩ ∈ commutator (Halpha D hC.alpha) :=
    (mem_commutator_or_mul_mem_of_mem_DstarH hC hx _).resolve_left fun hdc =>
      hd1 (eq_one_of_mem_center_inf_commutator hodd ⟨hdZ, hdc⟩ hd2)
  apply hX
  have hdM : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (⟨hC.d, hdH'⟩ : Halpha D hC.alpha) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (center_le_solvableRadical _ hdZ)
  have h1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (x * ⟨hC.d, hdH'⟩) ∈
      (commutator (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) := ⟨_, hxd, rfl⟩
  rw [map_commutator_eq] at h1
  rw [map_mul, hdM, mul_one] at h1
  rw [commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

section Multiplier

variable {K : Type} [Group K] [Finite K]

theorem commute_mk_of_mem_center {N : Subgroup K} [N.Normal] {x : K} {a b : K}
    (ha : ∃ c ∈ Subgroup.center K, (a : K ⧸ N) = (c : K ⧸ N) ∨ (a : K ⧸ N) = x * c)
    (hb : ∃ c ∈ Subgroup.center K, (b : K ⧸ N) = (c : K ⧸ N) ∨ (b : K ⧸ N) = x * c) :
    Commute (a : K ⧸ N) (b : K ⧸ N) := by
  have hcen : ∀ c ∈ Subgroup.center K, ∀ y : K ⧸ N, Commute (c : K ⧸ N) y := by
    intro c hc y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    change ((c * h : K) : K ⧸ N) = ((h * c : K) : K ⧸ N)
    rw [(Subgroup.mem_center_iff.mp hc h).symm]
  obtain ⟨c, hc, hac | hac⟩ := ha <;> obtain ⟨c', hc', hbc | hbc⟩ := hb <;> rw [hac, hbc]
  · exact hcen c hc _
  · exact hcen c hc _
  · exact (hcen c' hc' _).symm
  · exact ((Commute.refl _).mul_right (hcen c' hc' _).symm).mul_left (hcen c hc _)

theorem commutator_le_commutator_commutator {M : Subgroup K} [M.Normal]
    (hMZ : M ≤ Subgroup.center K) {x : K} (hx : x * x = 1)
    (hcos : ∀ h : K, h ∈ commutator K ∨ x * h ∈ commutator K)
    (hperf : ⁅commutator (K ⧸ M), commutator (K ⧸ M)⁆ = commutator (K ⧸ M)) :
    commutator K ≤ ⁅commutator K, commutator K⁆ := by
  set π := QuotientGroup.mk' M with hπ
  have hK' : (commutator K).map π = commutator (K ⧸ M) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M),
      commutator_def]
  have hK'' : (⁅commutator K, commutator K⁆).map π = (commutator K).map π := by
    rw [Subgroup.map_commutator, hK', hperf]
  have hdec : ∀ k ∈ commutator K, ∃ k₂ ∈ ⁅commutator K, commutator K⁆, k₂⁻¹ * k ∈ M := by
    intro k hk
    have : π k ∈ (⁅commutator K, commutator K⁆).map π := by
      rw [hK'']
      exact ⟨k, hk, rfl⟩
    obtain ⟨k₂, hk₂, he⟩ := this
    exact ⟨k₂, hk₂, (QuotientGroup.eq).mp he⟩
  obtain ⟨N, hN⟩ : ∃ N : Subgroup K, N = ⁅commutator K, commutator K⁆ := ⟨_, rfl⟩
  haveI : N.Normal := by rw [hN]; infer_instance
  rw [← hN] at hdec ⊢
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hform : ∀ a : K, ∃ c ∈ Subgroup.center K,
      (a : K ⧸ N) = (c : K ⧸ N) ∨ (a : K ⧸ N) = x * c := by
    intro a
    rcases hcos a with ha | ha
    · obtain ⟨k₂, hk₂, hm⟩ := hdec a ha
      refine ⟨k₂⁻¹ * a, hMZ hm, Or.inl ?_⟩
      rw [QuotientGroup.eq]
      have e : a⁻¹ * (k₂⁻¹ * a) = a⁻¹ * k₂⁻¹ * a⁻¹⁻¹ := by group
      rw [e]
      exact Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hk₂) _
    · obtain ⟨k₂, hk₂, hm⟩ := hdec _ ha
      refine ⟨k₂⁻¹ * (x * a), hMZ hm, Or.inr ?_⟩
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
      have e : a⁻¹ * (x * (k₂⁻¹ * (x * a))) = a⁻¹ * x * k₂⁻¹ * (a⁻¹ * x)⁻¹ := by
        rw [mul_inv_rev, inv_inv, hxinv]
        group
      rw [e]
      exact Subgroup.Normal.conj_mem inferInstance _ (Subgroup.inv_mem _ hk₂) _
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff]
  have e : ((⁅a, b⁆ : K) : K ⧸ N) = ⁅(a : K ⧸ N), (b : K ⧸ N)⁆ :=
    map_commutatorElement (QuotientGroup.mk' N) a b
  rw [e, commutatorElement_eq_one_iff_commute]
  exact commute_mk_of_mem_center (hform a) (hform b)

theorem odd_card_inf_commutator_of_multiplier {M : Subgroup K} [M.Normal]
    (hMZ : M ≤ Subgroup.center K) {x : K} (hx : x * x = 1)
    (hcos : ∀ h : K, h ∈ commutator K ∨ x * h ∈ commutator K)
    (hperf : ⁅commutator (K ⧸ M), commutator (K ⧸ M)⁆ = commutator (K ⧸ M))
    (hmult : ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* ↥(commutator (K ⧸ M))),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
        Odd (Nat.card φ.ker)) :
    Odd (Nat.card ↥(M ⊓ commutator K)) := by
  have hK' : (commutator K).map (QuotientGroup.mk' M) = commutator (K ⧸ M) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M),
      commutator_def]
  have hmem : ∀ k : ↥(commutator K),
      (QuotientGroup.mk' M).comp (commutator K).subtype k ∈ commutator (K ⧸ M) :=
    fun k => hK' ▸ ⟨k, k.2, rfl⟩
  let φ : ↥(commutator K) →* ↥(commutator (K ⧸ M)) :=
    ((QuotientGroup.mk' M).comp (commutator K).subtype).codRestrict _ hmem
  have hsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hK'] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : ∀ k, k ∈ φ.ker ↔ (k : K) ∈ M := by
    intro k
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcen : φ.ker ≤ Subgroup.center ↥(commutator K) := fun k hk =>
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hMZ ((hker k).mp hk)) g)
  have hcomm : φ.ker ≤ commutator ↥(commutator K) := by
    intro k _
    have h1 : (k : K) ∈ ⁅commutator K, commutator K⁆ :=
      commutator_le_commutator_commutator hMZ hx hcos hperf k.2
    rw [← Subgroup.map_subtype_commutator] at h1
    obtain ⟨k', hk', he⟩ := h1
    rwa [show k' = k from Subtype.ext he] at hk'
  have hodd := hmult _ φ hsurj hcen hcomm
  have e : φ.ker ≃ ↥(M ⊓ commutator K) :=
    { toFun := fun k => ⟨k.1.1, (hker k.1).mp k.2, k.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, (hker _).mpr z.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rwa [Nat.card_congr e] at hodd

end Multiplier

theorem odd_card_center_inf_commutator_of_multiplier (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hperf : ⁅commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))⁆ =
        commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (hmult : ∀ (Γ : Type) [Group Γ] [Finite Γ]
      (φ : Γ →* ↥(commutator (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))),
      Function.Surjective φ → φ.ker ≤ Subgroup.center Γ → φ.ker ≤ commutator Γ →
        Odd (Nat.card φ.ker)) :
    Odd (Nat.card ↥(Subgroup.center (Halpha D hC.alpha) ⊓ commutator (Halpha D hC.alpha))) := by
  obtain ⟨x, hx⟩ := DstarH_nonempty hC
  have h := odd_card_inf_commutator_of_multiplier hMZ
    ((DstarH_isOddTransp hC).mul_self_eq_one hx) (mem_commutator_or_mul_mem_of_mem_DstarH hC hx)
    hperf hmult
  rwa [le_antisymm hMZ (center_le_solvableRadical _)] at h

end CFSG.OddTranspositions.PartThree
