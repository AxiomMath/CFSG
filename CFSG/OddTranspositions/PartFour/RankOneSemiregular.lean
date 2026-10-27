module

public import CFSG.OddTranspositions.PartFour.RootLift
public import CFSG.OddTranspositions.PartFour.LineStabilizer

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem rankOneSemiregular_pCore_normal (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
  (CFSG.pCore_normal (G := Halpha D hC.alpha) (p := 2)).subgroupOf (rootLiftSubgroup hC S₀)

private theorem rankOneSemiregular_pCore_isPGroup (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    IsPGroup 2 ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)) :=
  (CFSG.pCore_isPGroup (G := Halpha D hC.alpha) (p := 2)).comap_subtype

private def rankOneSemiregular_F (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (wK : ↥(rootLiftSubgroup hC S₀)) : Subgroup ↥(rootLiftSubgroup hC S₀) :=
  ⁅(CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀), Subgroup.zpowers wK⁆

private def rankOneSemiregular_N (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (wK : ↥(rootLiftSubgroup hC S₀)) : Subgroup G :=
  ((rankOneSemiregular_F hC S₀ wK).map (rootLiftSubgroup hC S₀).subtype).map
    (Halpha D hC.alpha).subtype

private theorem rankOneSemiregular_N_le_Malpha (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (wK : ↥(rootLiftSubgroup hC S₀)) :
    rankOneSemiregular_N hC S₀ wK ≤ Malpha D hC.alpha := by
  intro x hx
  obtain ⟨xH, hxH, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hxH
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hxQ : xK ∈ (CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀) :=
    Subgroup.commutator_le_left (H₁ := (CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf
      (rootLiftSubgroup hC S₀)) (H₂ := Subgroup.zpowers wK) hxK
  exact Subgroup.mem_map.mpr
    ⟨(xK : Halpha D hC.alpha),
      CFSG.pCore_le_solvableRadical 2 (Halpha D hC.alpha) (Subgroup.mem_subgroupOf.mp hxQ), rfl⟩

private theorem rankOneSemiregular_F_commute (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)} (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    (hwK : wK ∈ rootLiftClass hC S₀)
    {x y : ↥(rootLiftSubgroup hC S₀)} (hx : x ∈ rankOneSemiregular_F hC S₀ wK)
    (hy : y ∈ rankOneSemiregular_F hC S₀ wK) : Commute x y := by
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hQKp := rankOneSemiregular_pCore_isPGroup hC S₀
  rw [rankOneSemiregular_F, Subgroup.commutator_def] at hx hy
  refine Asc72.commute_of_mem_closure ?_ hx hy
  rintro _ ⟨q, hq, t, ht, rfl⟩ _ ⟨q', hq', t', ht', rfl⟩
  exact OddTransp.commute_of_mem_commutator_self hS.oddT hS.normal hQKp hwK
    (Subgroup.commutator_mem_commutator hq ht)
    (Subgroup.commutator_mem_commutator hq' ht')

private theorem rankOneSemiregular_gen_sq_eq_one (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)} (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    (hwK : wK ∈ rootLiftClass hC S₀)
    {q : ↥(rootLiftSubgroup hC S₀)}
    (hq : q ∈ (CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀))
    {t : ↥(rootLiftSubgroup hC S₀)} (ht : t ∈ Subgroup.zpowers wK) :
    ⁅q, t⁆ * ⁅q, t⁆ = 1 := by
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hw2 : wK * wK = 1 := hS.oddT.mul_self_eq_one hwK
  rcases (mem_zpowers_of_mul_self hw2).mp ht with h1 | h2
  · rw [h1, commutatorElement_one_right, one_mul]
  · rw [h2]
    have hq' : q * wK * q⁻¹ ∈ rootLiftClass hC S₀ := hS.normal q wK hwK
    have h2 : (q * wK * q⁻¹) * (q * wK * q⁻¹) = 1 := hS.oddT.mul_self_eq_one hq'
    have h1 : Commute (q * wK * q⁻¹) wK := by
      simpa using OddTransp.commute_conj_of_mem hS.oddT hS.normal
        (rankOneSemiregular_pCore_isPGroup hC S₀) hwK hq (Subgroup.one_mem _)
    rw [commutatorElement_def, show wK⁻¹ = wK from inv_eq_of_mul_eq_one_right hw2]
    calc (q * wK * q⁻¹ * wK) * (q * wK * q⁻¹ * wK)
        = ((q * wK * q⁻¹) * wK) ^ 2 := by rw [pow_two]
      _ = (q * wK * q⁻¹) ^ 2 * wK ^ 2 := h1.mul_pow 2
      _ = 1 := by
        rw [show (q * wK * q⁻¹) ^ 2 = 1 by rw [pow_two]; exact h2,
          show wK ^ 2 = 1 by rw [pow_two]; exact hw2, mul_one]

private theorem rankOneSemiregular_F_sq_eq_one (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)} (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    (hwK : wK ∈ rootLiftClass hC S₀) {x : ↥(rootLiftSubgroup hC S₀)}
    (hx : x ∈ rankOneSemiregular_F hC S₀ wK) : x * x = 1 := by
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  rw [rankOneSemiregular_F, Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨q, hq, t, ht, rfl⟩ := hy
      exact rankOneSemiregular_gen_sq_eq_one hC hS hwK hq ht
  | one => rw [mul_one]
  | mul a b ha hb iha ihb =>
      have haF : a ∈ rankOneSemiregular_F hC S₀ wK := by
        rw [rankOneSemiregular_F, Subgroup.commutator_def]; exact ha
      have hbF : b ∈ rankOneSemiregular_F hC S₀ wK := by
        rw [rankOneSemiregular_F, Subgroup.commutator_def]; exact hb
      have hcomm : Commute a b := rankOneSemiregular_F_commute hC hS hwK haF hbF
      calc (a * b) * (a * b) = (a * b) ^ 2 := (pow_two _).symm
        _ = a ^ 2 * b ^ 2 := hcomm.mul_pow 2
        _ = 1 := by
          rw [show a ^ 2 = 1 by rw [pow_two]; exact iha,
            show b ^ 2 = 1 by rw [pow_two]; exact ihb, mul_one]
  | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]

private theorem rankOneSemiregular_exists_preimage (hC : HypothesisC D)
    (S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)))
    (wK : ↥(rootLiftSubgroup hC S₀)) {x : G} (hx : x ∈ rankOneSemiregular_N hC S₀ wK) :
    ∃ xK ∈ rankOneSemiregular_F hC S₀ wK, (xK : G) = x := by
  obtain ⟨xH, hxH, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨xK, hxK, rfl⟩ := Subgroup.mem_map.mp hxH
  exact ⟨xK, hxK, rfl⟩

private theorem rankOneSemiregular_sq_eq_one (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)} (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    (hwK : wK ∈ rootLiftClass hC S₀) {x : G} (hx : x ∈ rankOneSemiregular_N hC S₀ wK) :
    x * x = 1 := by
  obtain ⟨xK, hxK, hxval⟩ := rankOneSemiregular_exists_preimage hC S₀ wK hx
  have h := rankOneSemiregular_F_sq_eq_one hC hS hwK hxK
  rw [← hxval]
  simpa using congrArg (fun z : ↥(rootLiftSubgroup hC S₀) => (z : G)) h

private theorem rankOneSemiregular_exists_lift (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    {x : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hx : x ∈ S₀) :
    ∃ d : ↥(rootLiftSubgroup hC S₀), d ∈ rootLiftClass hC S₀ ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (d : Halpha D hC.alpha) = x := by
  obtain ⟨d, hd, rfl⟩ := hS₀ hx
  exact ⟨⟨d, Subgroup.subset_closure ⟨hd, hx⟩⟩, ⟨hd, hx⟩, rfl⟩

private theorem rankOneSemiregular_lift_mem_blockLine (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hVS₀ : Vmem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ⊆ S₀)
    {γ : Set G} (hγ : γ ∈ blockLine D hC.alpha β) (hγα : γ ≠ hC.alpha) {d : G} (hd : d ∈ γ) :
    ∃ dK : ↥(rootLiftSubgroup hC S₀), dK ∈ rootLiftClass hC S₀ ∧ (dK : G) = d ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (dK : Halpha D hC.alpha) ∈
        Vmem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
  have hγD : γ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hγ hγα
  let dH : Halpha D hC.alpha := ⟨d, Subgroup.subset_closure ⟨γ, hγD, hd⟩⟩
  have hdHD : dH ∈ DstarH hC := ⟨γ, hγD, hd⟩
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) dH ∈
      blockImage hC γ := ⟨dH, hd, rfl⟩
  have hV : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) dH ∈
      Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) :=
    blockImage_subset_Vmem h89 h113 hC hrad hW hn3 hMZ hβ hγ hγα hb hmem
  have hS : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) dH ∈ S₀ := hVS₀ hV
  exact ⟨⟨dH, Subgroup.subset_closure ⟨hdHD, hS⟩⟩, ⟨hdHD, hS⟩, rfl, hV⟩

private theorem rankOneSemiregular_not_commute_of_mem_Vmem (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK bK : ↥(rootLiftSubgroup hC S₀)} (hwK : wK ∈ rootLiftClass hC S₀)
    (hwnc : ¬ Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (wK : Halpha D hC.alpha))
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (bK : Halpha D hC.alpha)))
    {dK : ↥(rootLiftSubgroup hC S₀)}
    (hdV : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (dK : Halpha D hC.alpha) ∈
      Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (bK : Halpha D hC.alpha))) :
    ¬ Commute dK wK := by
  intro hc
  apply hwnc
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (wK : Halpha D hC.alpha) ∈ perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
          (dK : Halpha D hC.alpha)) :=
    mem_perpMem.mpr ⟨⟨(wK : Halpha D hC.alpha), hwK.1, rfl⟩,
      (hc.map ((QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp
        (rootLiftSubgroup hC S₀).subtype)).symm⟩
  rw [(mem_Vmem.mp hdV).2] at hmem
  exact (mem_perpMem.mp hmem).2

private theorem rankOneSemiregular_cimg_ne_alpha (hC : HypothesisC D)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    {x : G} (hxM : x ∈ Malpha D hC.alpha) : cimg x β ≠ hC.alpha := by
  intro hEq
  have hxH : x ∈ Halpha D hC.alpha := by
    obtain ⟨xH, -, hxval⟩ := Subgroup.mem_map.mp hxM
    rw [← hxval]; exact xH.2
  have hfix : cimg x⁻¹ hC.alpha = hC.alpha :=
    cimg_eq_self_of_mem_normalizer (Subgroup.inv_mem _
      (Halpha_le_normalizer_block D hC.alpha hxH))
  have hbα : (b : G) ∈ hC.alpha := by
    have hmem : x * (b : G) * x⁻¹ ∈ hC.alpha := by
      have h : x * (b : G) * x⁻¹ ∈ cimg x β := ⟨(b : G), hb, rfl⟩
      rwa [hEq] at h
    have h2 : x⁻¹ * (x * (b : G) * x⁻¹) * x ∈ hC.alpha := by
      have h : x⁻¹ * (x * (b : G) * x⁻¹) * x ∈ cimg x⁻¹ hC.alpha :=
        ⟨x * (b : G) * x⁻¹, hmem, by group⟩
      rwa [hfix] at h
    rwa [show x⁻¹ * (x * (b : G) * x⁻¹) * x = (b : G) by group] at h2
  have hαβ : hC.alpha = β :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha (mem_blockClass_self hC.alpha) hβ.1
      ⟨(b : G), hbα, hb⟩
  exact hβ.2.2.1 hαβ.symm

private theorem rankOneSemiregular_conj_eq_of_fixes (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {δ : Set G}
    (hδ : δ ∈ blockLine D hC.alpha β) (hδα : δ ≠ hC.alpha)
    {x : G} (hxM : x ∈ Malpha D hC.alpha) (hxfix : cimg x δ = δ) {d : G} (hd : d ∈ δ) :
    x * d * x⁻¹ = d := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  have hδD : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ hδα
  have hxd : x * d * x⁻¹ ∈ δ := by
    have h : x * d * x⁻¹ ∈ cimg x δ := ⟨d, hd, rfl⟩
    rwa [hxfix] at h
  obtain ⟨xH, hxR, hxval⟩ := Subgroup.mem_map.mp hxM
  let dH : H := ⟨d, Subgroup.subset_closure (subset_DalphaStar hδD hd)⟩
  have hcommR : xH * dH * xH⁻¹ * dH⁻¹ ∈ R := by
    have h1 : dH * xH * dH⁻¹ ∈ R :=
      (inferInstance : R.Normal).conj_mem xH hxR dH
    have h2 := R.mul_mem h1 (R.inv_mem hxR)
    simpa [mul_assoc] using R.inv_mem h2
  have hmemM : d⁻¹ * (x * d * x⁻¹) ∈ Malpha D hC.alpha := by
    refine Subgroup.mem_map.mpr ⟨dH⁻¹ * (xH * dH * xH⁻¹), ?_, ?_⟩
    · rw [show dH⁻¹ * (xH * dH * xH⁻¹) = dH⁻¹ * (xH * dH * xH⁻¹ * dH⁻¹) * dH by group]
      simpa using (inferInstance : R.Normal).conj_mem (xH * dH * xH⁻¹ * dH⁻¹) hcommR dH⁻¹
    · show ((dH⁻¹ * (xH * dH * xH⁻¹) : H) : G) = d⁻¹ * (x * d * x⁻¹)
      rw [← hxval]; rfl
  exact (eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns hδD hd hxd hmemM).symm

private theorem rankOneSemiregular_mem_center (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    {wK dK : ↥(rootLiftSubgroup hC S₀)}
    (hwK : wK ∈ rootLiftClass hC S₀) (hdK : dK ∈ rootLiftClass hC S₀)
    (hdw : ¬ Commute dK wK)
    {xK : ↥(rootLiftSubgroup hC S₀)} (hxF : xK ∈ rankOneSemiregular_F hC S₀ wK)
    (hxd : Commute xK dK) : xK ∈ Subgroup.center ↥(rootLiftSubgroup hC S₀) := by
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have htop := closure_insert_rootLiftClass_eq_top h113 hC hrad hn3 hHns hS₀ hgen hconj
    hwK hdK (fun h => hdw h.symm)
  refine Subgroup.mem_center_iff.mpr ?_
  intro g
  change Commute g xK
  have hg : g ∈ Subgroup.closure (insert dK {f | f ∈ rootLiftClass hC S₀ ∧ Commute f wK}) := by
    rw [htop]; exact Subgroup.mem_top g
  clear htop
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with rfl | hy
      · exact hxd.symm
      · exact OddTransp.commute_of_mem_commutator hS.oddT hS.normal
          (rankOneSemiregular_pCore_isPGroup hC S₀) hwK hy.1 hy.2 hxF
  | one => exact Commute.one_left xK
  | mul a b ha hb iha ihb => exact iha.mul_left ihb
  | inv a ha iha => exact iha.inv_left

private theorem rankOneSemiregular_fixes (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {bK wK : ↥(rootLiftSubgroup hC S₀)} (hb : (bK : G) ∈ β)
    (hwK : wK ∈ rootLiftClass hC S₀)
    (hVS₀ : Vmem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (bK : Halpha D hC.alpha))
        ⊆ S₀)
    (hwnc : ¬ Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (wK : Halpha D hC.alpha))
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (bK : Halpha D hC.alpha)))
    {x : G} (hxN : x ∈ rankOneSemiregular_N hC S₀ wK)
    {δ : Set G} (hδ : δ ∈ blockLine D hC.alpha β) (hδα : δ ≠ hC.alpha)
    (hxfix : cimg x δ = δ) :
    ∀ ε ∈ blockLine D hC.alpha β, cimg x ε = ε := by
  obtain ⟨xK, hxF, rfl⟩ := rankOneSemiregular_exists_preimage hC S₀ wK hxN
  have hxM : (xK : G) ∈ Malpha D hC.alpha := rankOneSemiregular_N_le_Malpha hC S₀ wK hxN
  obtain ⟨d, hd⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hδ.1
  obtain ⟨dK, hdK, rfl, hdV⟩ := rankOneSemiregular_lift_mem_blockLine h89 h113 hC hrad hW hn3
    hMZ hβ hb hVS₀ hδ hδα hd
  have hdw : ¬ Commute dK wK := rankOneSemiregular_not_commute_of_mem_Vmem hC hwK hwnc hdV
  have hxdG : (xK : G) * (dK : G) * (xK : G)⁻¹ = (dK : G) :=
    rankOneSemiregular_conj_eq_of_fixes h89 h113 hC hrad hW hn3 hHns hβ hδ hδα hxM hxfix hd
  have hxd : Commute xK dK := by
    have h1 : xK * dK * xK⁻¹ = dK := by
      apply Subtype.ext; apply Subtype.ext
      simpa using hxdG
    show xK * dK = dK * xK
    calc xK * dK = (xK * dK * xK⁻¹) * xK := by group
      _ = dK * xK := by rw [h1]
  have hcenter := rankOneSemiregular_mem_center h113 hC hrad hn3 hHns hS₀ hgen hconj hS
    hwK hdK hdw hxF hxd
  intro ε hε
  by_cases hεα : ε = hC.alpha
  · rw [hεα]
    exact cimg_eq_self_of_mem_normalizer
      (Halpha_le_normalizer_block D hC.alpha (xK : Halpha D hC.alpha).2)
  · obtain ⟨e, he⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hε.1
    obtain ⟨eK, heK, rfl, -⟩ := rankOneSemiregular_lift_mem_blockLine h89 h113 hC hrad hW hn3
      hMZ hβ hb hVS₀ hε hεα he
    have hxeG : (xK : G) * (eK : G) * (xK : G)⁻¹ = (eK : G) := by
      have hc : Commute xK eK := (Subgroup.mem_center_iff.mp hcenter eK).symm
      have h1 : (xK : G) * (eK : G) = (eK : G) * (xK : G) := by
        simpa using congrArg (fun z : ↥(rootLiftSubgroup hC S₀) => (z : G)) hc.eq
      calc (xK : G) * (eK : G) * (xK : G)⁻¹ = (eK : G) * (xK : G) * (xK : G)⁻¹ := by
            rw [h1]
        _ = (eK : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hclass : cimg (xK : G) ε ∈ blockClass hC.alpha := cimg_mem_blockClass_iff.mpr hε.1
    exact (eq_of_mem_of_mem_blockClass hC.isBlock_alpha hε.1 hclass
      ⟨(eK : G), he, (eK : G), he, hxeG⟩).symm

private theorem rankOneSemiregular_conj_class_eq (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀))
    {wK bK : ↥(rootLiftSubgroup hC S₀)}
    (hwK : wK ∈ rootLiftClass hC S₀) (hbK : bK ∈ rootLiftClass hC S₀)
    (hbw : ¬ Commute bK wK) :
    (fun y : ↥(rootLiftSubgroup hC S₀) => y * bK * y⁻¹) ''
        (rankOneSemiregular_F hC S₀ wK : Set ↥(rootLiftSubgroup hC S₀)) =
      (fun y : ↥(rootLiftSubgroup hC S₀) => y * bK * y⁻¹) ''
        ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀) :
          Set ↥(rootLiftSubgroup hC S₀)) := by
  haveI : ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hgen' : Subgroup.closure
      (insert wK {f | f ∈ rootLiftClass hC S₀ ∧ Commute f bK}) = ⊤ :=
    closure_insert_rootLiftClass_eq_top h113 hC hrad hn3 hHns hS₀ hgen hconj hbK hwK hbw
  have hthree := OddTransp.localQ_three (G := ↥(rootLiftSubgroup hC S₀))
    (D := rootLiftClass hC S₀)
    (Q := (CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀))
    hS.oddT hS.normal (rankOneSemiregular_pCore_isPGroup hC S₀) hS hbK hwK hbw hgen'
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨y, hyF, rfl⟩
    exact ⟨y, Subgroup.commutator_le_left (H₁ := (CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf
      (rootLiftSubgroup hC S₀)) (H₂ := Subgroup.zpowers wK) hyF, rfl⟩
  · rintro z ⟨y, hyQ, rfl⟩
    obtain ⟨y₁, hy₁Q, hy₁b, y₂, hy₂F, hy₂eq⟩ := hthree.2.1 y⁻¹
      (Subgroup.inv_mem _ hyQ)
    have hy_eq : y = y₂⁻¹ * y₁⁻¹ := by simpa using congrArg Inv.inv hy₂eq
    have h1 : y₁⁻¹ * bK * y₁ = bK := by
      calc y₁⁻¹ * bK * y₁ = bK * y₁⁻¹ * y₁ := by rw [hy₁b.inv_left.eq]
        _ = bK := by rw [mul_assoc, inv_mul_cancel, mul_one]
    refine ⟨y₂⁻¹, Subgroup.inv_mem _ hy₂F, ?_⟩
    rw [hy_eq]
    calc (y₂⁻¹ * bK * (y₂⁻¹)⁻¹) = y₂⁻¹ * bK * y₂ := by rw [inv_inv]
      _ = y₂⁻¹ * (y₁⁻¹ * bK * y₁) * y₂ := by rw [h1]
      _ = (y₂⁻¹ * y₁⁻¹) * bK * (y₂⁻¹ * y₁⁻¹)⁻¹ := by group

private theorem rankOneSemiregular_conj_mul_inv_mem_Malpha (hC : HypothesisC D)
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK bK : ↥(rootLiftSubgroup hC S₀)}
    {xK yK : ↥(rootLiftSubgroup hC S₀)} (hxK : xK ∈ rankOneSemiregular_F hC S₀ wK)
    (hyK : yK ∈ rankOneSemiregular_F hC S₀ wK) :
    ((xK : G) * (bK : G) * (xK : G)⁻¹)⁻¹ *
      ((yK : G) * (bK : G) * (yK : G)⁻¹) ∈ Malpha D hC.alpha := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  haveI : ((CFSG.pCore 2 H).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hxKR : (xK : H) ∈ R :=
    CFSG.pCore_le_solvableRadical 2 H (Subgroup.mem_subgroupOf.mp
      (Subgroup.commutator_le_left (H₁ := (CFSG.pCore 2 H).subgroupOf (rootLiftSubgroup hC S₀))
        (H₂ := Subgroup.zpowers wK) hxK))
  have hyKR : (yK : H) ∈ R :=
    CFSG.pCore_le_solvableRadical 2 H (Subgroup.mem_subgroupOf.mp
      (Subgroup.commutator_le_left (H₁ := (CFSG.pCore 2 H).subgroupOf (rootLiftSubgroup hC S₀))
        (H₂ := Subgroup.zpowers wK) hyK))
  have hcR : (xK : H) * (bK : H) * (xK : H)⁻¹ * (bK : H)⁻¹ ∈ R := by
    have h1 : (bK : H) * (xK : H) * (bK : H)⁻¹ ∈ R :=
      (inferInstance : R.Normal).conj_mem (xK : H) hxKR (bK : H)
    have h2 := R.mul_mem h1 (R.inv_mem hxKR)
    simpa [mul_assoc] using R.inv_mem h2
  have hc'R : (yK : H) * (bK : H) * (yK : H)⁻¹ * (bK : H)⁻¹ ∈ R := by
    have h1 : (bK : H) * (yK : H) * (bK : H)⁻¹ ∈ R :=
      (inferInstance : R.Normal).conj_mem (yK : H) hyKR (bK : H)
    have h2 := R.mul_mem h1 (R.inv_mem hyKR)
    simpa [mul_assoc] using R.inv_mem h2
  have hmemR : ((xK : H) * (bK : H) * (xK : H)⁻¹)⁻¹ *
      ((yK : H) * (bK : H) * (yK : H)⁻¹) ∈ R := by
    rw [show ((xK : H) * (bK : H) * (xK : H)⁻¹)⁻¹ *
        ((yK : H) * (bK : H) * (yK : H)⁻¹) =
      (bK : H)⁻¹ * (((xK : H) * (bK : H) * (xK : H)⁻¹ * (bK : H)⁻¹)⁻¹ *
        ((yK : H) * (bK : H) * (yK : H)⁻¹ * (bK : H)⁻¹)) * (bK : H) by group]
    simpa using (inferInstance : R.Normal).conj_mem _ (R.mul_mem (R.inv_mem hcR) hc'R) (bK : H)⁻¹
  exact Subgroup.mem_map.mpr ⟨((xK : H) * (bK : H) * (xK : H)⁻¹)⁻¹ *
    ((yK : H) * (bK : H) * (yK : H)⁻¹), hmemR, rfl⟩

private theorem rankOneSemiregular_conj_eq_of_cimg_eq (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)}
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {bK : ↥(rootLiftSubgroup hC S₀)} (hb : (bK : G) ∈ β)
    {x y : G} (hxN : x ∈ rankOneSemiregular_N hC S₀ wK)
    (hyN : y ∈ rankOneSemiregular_N hC S₀ wK) (hxy : cimg x β = cimg y β)
    {xK yK : ↥(rootLiftSubgroup hC S₀)} (hxK : xK ∈ rankOneSemiregular_F hC S₀ wK)
    (hyK : yK ∈ rankOneSemiregular_F hC S₀ wK) (hxval : (xK : G) = x)
    (hyval : (yK : G) = y) :
    xK * bK * xK⁻¹ = yK * bK * yK⁻¹ := by
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  haveI : ((CFSG.pCore 2 H).subgroupOf (rootLiftSubgroup hC S₀)).Normal :=
    rankOneSemiregular_pCore_normal hC S₀
  have hxM : x ∈ Malpha D hC.alpha := rankOneSemiregular_N_le_Malpha hC S₀ wK hxN
  have hxline : cimg x β ∈ blockLine D hC.alpha β :=
    cimg_mem_blockLine_of_mem_Malpha h113 hC hrad hn3 hβ
      (right_mem_blockLine hβ.1 hβ.2.1) hxM
  have hxD : cimg x β ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hxline
      (rankOneSemiregular_cimg_ne_alpha hC hβ hb hxM)
  have hxc : (xK : G) * (bK : G) * (xK : G)⁻¹ ∈ cimg x β := by
    have h : (xK : G) * (bK : G) * (xK : G)⁻¹ ∈ cimg (xK : G) β := ⟨(bK : G), hb, rfl⟩
    rw [hxval] at h ⊢
    exact h
  have hyc : (yK : G) * (bK : G) * (yK : G)⁻¹ ∈ cimg x β := by
    have h : (yK : G) * (bK : G) * (yK : G)⁻¹ ∈ cimg (yK : G) β := ⟨(bK : G), hb, rfl⟩
    rw [hyval, ← hxy] at h
    rw [hyval]
    exact h
  have hmemM : ((xK : G) * (bK : G) * (xK : G)⁻¹)⁻¹ *
      ((yK : G) * (bK : G) * (yK : G)⁻¹) ∈ Malpha D hC.alpha :=
    rankOneSemiregular_conj_mul_inv_mem_Malpha hC hxK hyK
  have hEq := eq_of_mem_of_inv_mul_mem_Malpha h89 h113 hC hrad hW hn3 hHns hxD hxc hyc hmemM
  apply Subtype.ext; apply Subtype.ext
  exact hEq

private theorem rankOneSemiregular_ncard_le (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {wK : ↥(rootLiftSubgroup hC S₀)} {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {bK : ↥(rootLiftSubgroup hC S₀)} (hb : (bK : G) ∈ β) :
    ((fun y : ↥(rootLiftSubgroup hC S₀) => y * bK * y⁻¹) ''
        (rankOneSemiregular_F hC S₀ wK : Set ↥(rootLiftSubgroup hC S₀))).ncard ≤
      ((fun x => cimg x β) '' (rankOneSemiregular_N hC S₀ wK : Set G)).ncard := by
  classical
  let K := ↥(rootLiftSubgroup hC S₀)
  let s : Set K := (fun y : K => y * bK * y⁻¹) '' (rankOneSemiregular_F hC S₀ wK : Set K)
  let u : Set (Set G) := (fun y : K => cimg (y : G) β) ''
    (rankOneSemiregular_F hC S₀ wK : Set K)
  let t : Set (Set G) := (fun x => cimg x β) '' (rankOneSemiregular_N hC S₀ wK : Set G)
  have hsub : u ⊆ t := by
    rintro S ⟨y, hyF, rfl⟩
    exact ⟨(y : G), Subgroup.mem_map.mpr ⟨(y : Halpha D hC.alpha),
      Subgroup.mem_map.mpr ⟨y, hyF, rfl⟩, rfl⟩, rfl⟩
  have hu : u.ncard ≤ t.ncard := Set.ncard_le_ncard hsub (Set.toFinite t)
  let g : ↥u → ↥s := fun S =>
    ⟨Classical.choose S.2 * bK * (Classical.choose S.2)⁻¹,
      ⟨Classical.choose S.2, (Classical.choose_spec S.2).1, rfl⟩⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨y, hyF, rfl⟩ := hz
    let hS : cimg (y : G) β ∈ u := ⟨y, hyF, rfl⟩
    refine ⟨⟨cimg (y : G) β, hS⟩, ?_⟩
    apply Subtype.ext
    let xK : K := Classical.choose hS
    have hxK : xK ∈ rankOneSemiregular_F hC S₀ wK := (Classical.choose_spec hS).1
    have hxy : cimg (xK : G) β = cimg (y : G) β := (Classical.choose_spec hS).2
    have hxN : (xK : G) ∈ rankOneSemiregular_N hC S₀ wK :=
      Subgroup.mem_map.mpr ⟨(xK : Halpha D hC.alpha),
        Subgroup.mem_map.mpr ⟨xK, hxK, rfl⟩, rfl⟩
    have hyN : (y : G) ∈ rankOneSemiregular_N hC S₀ wK :=
      Subgroup.mem_map.mpr ⟨(y : Halpha D hC.alpha),
        Subgroup.mem_map.mpr ⟨y, hyF, rfl⟩, rfl⟩
    exact rankOneSemiregular_conj_eq_of_cimg_eq h89 h113 hC hrad hW hn3 hHns hβ hb hxN hyN
      hxy hxK hyF rfl rfl
  have hs : s.ncard ≤ u.ncard := by
    have h := Nat.card_le_card_of_surjective g hsurj
    rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  exact hs.trans hu

private theorem rankOneSemiregular_orbit_subset (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hS : Setup ↥(rootLiftSubgroup hC S₀) (rootLiftClass hC S₀)) {n : ℕ} (hn : 0 < n)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {bK wK : ↥(rootLiftSubgroup hC S₀)} (hb : (bK : G) ∈ β)
    (hbK : bK ∈ rootLiftClass hC S₀) (hwK : wK ∈ rootLiftClass hC S₀)
    (hbw : ¬ Commute bK wK) :
    (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) ⊆
      (fun x => cimg x β) '' (rankOneSemiregular_N hC S₀ wK : Set G) := by
  let K := ↥(rootLiftSubgroup hC S₀)
  let tM : Set (Set G) := (fun x => cimg x β) '' (Malpha D hC.alpha : Set G)
  let tN : Set (Set G) := (fun x => cimg x β) '' (rankOneSemiregular_N hC S₀ wK : Set G)
  let sQ : Set K := (fun y : K => y * bK * y⁻¹) ''
    ((CFSG.pCore 2 (Halpha D hC.alpha)).subgroupOf (rootLiftSubgroup hC S₀) : Set K)
  let sF : Set K := (fun y : K => y * bK * y⁻¹) ''
    (rankOneSemiregular_F hC S₀ wK : Set K)
  have hcardM : sQ.ncard = tM.ncard := by
    have h := ncard_conj_rootLiftClass_eq h89 h113 hC hrad hW hn3 hHns hn hS₀ hinv hconj
      hord (d := bK) hbK (β := β) hβ
    simpa [sQ, tM] using h
  have hclass : sF = sQ := by
    have h := rankOneSemiregular_conj_class_eq h113 hC hrad hn3 hHns hS₀ hgen hconj hS
      hwK hbK hbw
    simpa [sF, sQ] using h
  have hle : sF.ncard ≤ tN.ncard :=
    rankOneSemiregular_ncard_le h89 h113 hC hrad hW hn3 hHns hβ hb (wK := wK) (bK := bK)
  have hleM : tM.ncard ≤ tN.ncard := by rw [← hcardM, ← hclass]; exact hle
  have hsub : tN ⊆ tM := by
    rintro S ⟨x, hx, rfl⟩
    exact ⟨x, rankOneSemiregular_N_le_Malpha hC S₀ wK hx, rfl⟩
  have hEq : tN = tM := Set.eq_of_subset_of_ncard_le hsub hleM (Set.toFinite tM)
  show tM ⊆ tN
  rw [hEq]

theorem exists_semiregular_of_rootLift (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {S₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hS₀ : S₀ ⊆ imageClass hC) {n : ℕ} (hn : 0 < n)
    (hinv : ∀ x ∈ S₀, ∀ y ∈ S₀, y * x * y⁻¹ ∈ S₀)
    (hgen : ∀ x ∈ S₀, ∀ y ∈ S₀, ¬ Commute x y →
      Subgroup.closure (insert y {z | z ∈ S₀ ∧ Commute z x}) = Subgroup.closure S₀)
    (hconj : ∀ x ∈ S₀, ∀ y ∈ S₀, ∃ g ∈ Subgroup.closure S₀, g * x * g⁻¹ = y)
    (hord : ∃ x ∈ S₀, ∃ y ∈ S₀, orderOf (x * y) = 2 ^ n + 1)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {b : Halpha D hC.alpha} (hb : (b : G) ∈ β)
    (hVS₀ : Vmem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ⊆ S₀)
    (hw : ∃ w ∈ S₀,
      ¬ Commute w (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)) :
    ∃ N : Subgroup G, N ≤ Malpha D hC.alpha ∧
      (∀ x ∈ N, ∀ ε ∈ blockLine D hC.alpha β, cimg (x * x) ε = ε) ∧
      (∀ x ∈ N, ∀ δ ∈ blockLine D hC.alpha β, δ ≠ hC.alpha → cimg x δ = δ →
        ∀ ε ∈ blockLine D hC.alpha β, cimg x ε = ε) ∧
      (fun x => cimg x β) '' (Malpha D hC.alpha : Set G) ⊆
        (fun x => cimg x β) '' (N : Set G) := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let K := rootLiftSubgroup hC S₀
  let DK := rootLiftClass hC S₀
  have hS : Setup K DK := setup_rootLiftClass h113 hC hrad hn3 hn hS₀ hinv hconj hord
  have hbD : b ∈ DstarH hC := ⟨β, hβ, hb⟩
  have hbS : QuotientGroup.mk' R b ∈ S₀ :=
    hVS₀ (mem_Vmem_self (D := imageClass hC) (u := QuotientGroup.mk' R b) ⟨b, hbD, rfl⟩)
  let bK : K := ⟨b, Subgroup.subset_closure ⟨hbD, hbS⟩⟩
  have hbDK : bK ∈ DK := ⟨hbD, hbS⟩
  obtain ⟨wbar, hwS, hwnc⟩ := hw
  obtain ⟨wK, hwDK, hmkw⟩ := rankOneSemiregular_exists_lift hC hS₀ hwS
  have hwnc' : ¬ Commute (QuotientGroup.mk' R (wK : H)) (QuotientGroup.mk' R (bK : H)) := by
    rw [show QuotientGroup.mk' R (wK : H) = wbar from hmkw,
      show QuotientGroup.mk' R (bK : H) = QuotientGroup.mk' R b from rfl]
    exact hwnc
  have hbw : ¬ Commute bK wK := by
    intro hc
    exact hwnc' ((hc.map ((QuotientGroup.mk' R).comp K.subtype)).symm)
  refine ⟨rankOneSemiregular_N hC S₀ wK, rankOneSemiregular_N_le_Malpha hC S₀ wK, ?_, ?_, ?_⟩
  · intro x hx ε hε
    rw [rankOneSemiregular_sq_eq_one hC hS hwDK hx, cimg_one]
  · intro x hx δ hδ hδα hxfix
    exact rankOneSemiregular_fixes h89 h113 hC hrad hW hn3 hMZ hHns hS₀ hgen hconj hS hβ
      (bK := bK) (wK := wK) hb hwDK hVS₀ hwnc' (x := x) hx hδ hδα hxfix
  · exact rankOneSemiregular_orbit_subset h89 h113 hC hrad hW hn3 hHns hS₀ hgen hconj hS
      hn hinv hord hβ hb hbDK hwDK hbw

end CFSG.OddTranspositions.PartFour
