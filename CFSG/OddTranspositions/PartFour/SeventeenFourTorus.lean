module

public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.OddTranspositions.PartFour.LineCount

import CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

private def seventeenFourTorus_orbit (hC : HypothesisC D) (β₀ : Set G) : Set (Set G) :=
  (fun x : G => cimg x β₀) '' (Malpha D hC.alpha : Set G)

private theorem seventeenFourTorus_exists_odd_lift {H : Type*} [Group H] [Finite H]
    (R : Subgroup H) [R.Normal] (g : H ⧸ R) :
    ∃ z : H, Odd (orderOf z) ∧ ∃ k : ℕ, QuotientGroup.mk' R z = g ^ (2 ^ k) := by
  obtain ⟨z₀, rfl⟩ := QuotientGroup.mk'_surjective R g
  obtain ⟨k, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z₀).ne'
  refine ⟨z₀ ^ (2 ^ k), ?_, k, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero k (by norm_num)) ⟨m, hN⟩, hN,
      Nat.mul_div_cancel_left m (pow_pos (by norm_num) k)]
    exact hm
  · rw [map_pow]

private theorem seventeenFourTorus_orbit_subset_Dalpha (hC : HypothesisC D) {β₀ : Set G}
    (hβ₀ : β₀ ∈ Dalpha D hC.alpha) :
    seventeenFourTorus_orbit hC β₀ ⊆ Dalpha D hC.alpha := by
  rintro β ⟨x, hx, rfl⟩
  exact conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ₀
    (Halpha_le_normalizer_block D hC.alpha (Subgroup.map_subtype_le _ hx))

private theorem seventeenFourTorus_blockImage_orbit_subset_Vmem (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha) {b₀ : Halpha D hC.alpha}
    (hb₀β₀ : (b₀ : G) ∈ β₀) :
    ∀ β ∈ seventeenFourTorus_orbit hC β₀,
      blockImage hC β ⊆ Vmem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b₀) := by
  intro β hβ z hz
  obtain ⟨x, hx, rfl⟩ := hβ
  rw [blockImage_cimg hC _ hx] at hz
  obtain ⟨c, hcβ₀, rfl⟩ := hz
  have hzD : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c ∈
      imageClass hC := ⟨c, ⟨β₀, hβ₀, hcβ₀⟩, rfl⟩
  refine mem_Vmem.mpr ⟨hzD, ?_⟩
  exact perpMem_mk_eq_of_mem h89 h113 hC hrad hW hn3 hMZ hβ₀ hcβ₀ hb₀β₀

private theorem seventeenFourTorus_dvd_card_of_perm {X : Type*} [Finite X]
    {n : ℕ} (σ : Equiv.Perm X) (hno : ∀ x, σ x ≠ x)
    (hcyc : ∀ i : ℕ, ∀ x : X, (σ ^ i) x = x → n ∣ i) : n ∣ Nat.card X := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  rw [Nat.card_eq_fintype_card]
  have hsupp : σ.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Equiv.Perm.mem_support]
    exact hno x
  have hsum : σ.cycleType.sum = Fintype.card X := by
    rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ]
  rw [← hsum]
  refine Multiset.dvd_sum ?_
  intro d hd
  have hd2 : 2 ≤ d := Equiv.Perm.two_le_of_mem_cycleType hd
  rw [Equiv.Perm.cycleType_def] at hd
  simp only [Multiset.mem_map, Finset.mem_val, Function.comp_apply] at hd
  obtain ⟨c, hc, hcd⟩ := hd
  have hcycOn : σ.IsCycleOn (c.support : Set X) :=
    Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hc
  have hdpos : 0 < c.support.card := by
    rw [hcd]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hdpos
  have hpow : (σ ^ c.support.card) x = x := hcycOn.pow_card_apply hx
  have := hcyc c.support.card x hpow
  simpa [hcd] using this

private theorem seventeenFourTorus_cimg_z_mem_orbit (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {v : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {b₀ : Halpha D hC.alpha} (hb₀ : b₀ ∈ DstarH hC)
    (hmkb₀ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b₀ = v)
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha) (hb₀β₀ : (b₀ : G) ∈ β₀)
    {z : Halpha D hC.alpha}
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) v) :
    ∀ S ∈ seventeenFourTorus_orbit hC β₀,
      cimg (z : G) S ∈ seventeenFourTorus_orbit hC β₀ := by
  have hzβ₀Φ : cimg (z : G) β₀ ∈ seventeenFourTorus_orbit hC β₀ := by
    have hmkconj : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        (z * b₀ * z⁻¹) = v := by
      rw [map_mul, map_mul, map_inv, hmkb₀, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hzD : cimg (z : G) β₀ ∈ Dalpha D hC.alpha :=
      conj_mem_Dalpha_of_mem_normalizer hC.setup.normal hβ₀
        (Halpha_le_normalizer_block D hC.alpha z.2)
    have hzmem : (z * b₀ * z⁻¹ : Halpha D hC.alpha) ∈
        {c : Halpha D hC.alpha | (c : G) ∈ cimg (z : G) β₀} := by
      change ((z * b₀ * z⁻¹ : Halpha D hC.alpha) : G) ∈
        (fun x : G => (z : G) * x * (z : G)⁻¹) '' β₀
      refine ⟨(b₀ : G), hb₀β₀, ?_⟩
      simp
    have hinter : (blockImage hC (cimg (z : G) β₀) ∩ blockImage hC β₀).Nonempty :=
      ⟨v, ⟨z * b₀ * z⁻¹, hzmem, hmkconj⟩, ⟨b₀, hb₀β₀, hmkb₀⟩⟩
    obtain ⟨x, hxM, hxeq⟩ :=
      exists_cimg_eq_of_blockImage_inter_nonempty h113 hC hrad hn3 hHns hzD hβ₀ hinter
    refine ⟨x⁻¹, (Malpha D hC.alpha).inv_mem hxM, ?_⟩
    calc cimg ((x : G)⁻¹) β₀
        = cimg ((x : G)⁻¹) (cimg (x : G) (cimg (z : G) β₀)) := by rw [hxeq]
      _ = cimg (z : G) β₀ := cimg_inv_cimg (x : G) (cimg (z : G) β₀)
  obtain ⟨y, hyM, hyeq⟩ := hzβ₀Φ
  change cimg y β₀ = cimg (z : G) β₀ at hyeq
  rintro S ⟨x, hxM, rfl⟩
  have hzxM : (z : G) * x * (z : G)⁻¹ ∈ Malpha D hC.alpha :=
    conj_mem_Malpha_of_mem_normalizer hC.setup.normal
      (Halpha_le_normalizer_block D hC.alpha z.2) hxM
  refine ⟨((z : G) * x * (z : G)⁻¹) * y, (Malpha D hC.alpha).mul_mem hzxM hyM, ?_⟩
  calc cimg (((z : G) * x * (z : G)⁻¹) * y) β₀
      = cimg ((z : G) * x * (z : G)⁻¹) (cimg y β₀) := cimg_mul _ _ _
    _ = cimg ((z : G) * x * (z : G)⁻¹) (cimg (z : G) β₀) := by rw [hyeq]
    _ = cimg (z : G) (cimg x β₀) := (cimg_cimg_conj (z : G) x β₀).symm

private theorem seventeenFourTorus_cimg_pCore_mem_orbit (hC : HypothesisC D) {β₀ : Set G}
    {q : Halpha D hC.alpha} (hq : q ∈ CFSG.pCore 2 (Halpha D hC.alpha)) :
    ∀ S ∈ seventeenFourTorus_orbit hC β₀,
      cimg (q : G) S ∈ seventeenFourTorus_orbit hC β₀ := by
  intro S hS
  obtain ⟨x, hxM, rfl⟩ := hS
  have hqM : (q : G) ∈ Malpha D hC.alpha :=
    Subgroup.mem_map.mpr ⟨q, CFSG.pCore_le_solvableRadical 2 (Halpha D hC.alpha) hq, rfl⟩
  have hqxM : (q : G) * x * (q : G)⁻¹ ∈ Malpha D hC.alpha :=
    (Malpha D hC.alpha).mul_mem
      ((Malpha D hC.alpha).mul_mem hqM hxM) ((Malpha D hC.alpha).inv_mem hqM)
  refine ⟨((q : G) * x * (q : G)⁻¹) * (q : G), (Malpha D hC.alpha).mul_mem hqxM hqM, ?_⟩
  calc cimg (((q : G) * x * (q : G)⁻¹) * (q : G)) β₀
      = cimg ((q : G) * x * (q : G)⁻¹) (cimg (q : G) β₀) := cimg_mul _ _ _
    _ = cimg (q : G) (cimg x β₀) := (cimg_cimg_conj (q : G) x β₀).symm

private theorem seventeenFourTorus_sup_mem_orbit (hC : HypothesisC D) {β₀ : Set G}
    {z : Halpha D hC.alpha}
    (hz : ∀ S ∈ seventeenFourTorus_orbit hC β₀,
      cimg (z : G) S ∈ seventeenFourTorus_orbit hC β₀)
    (hQ : ∀ q ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      ∀ S ∈ seventeenFourTorus_orbit hC β₀,
        cimg (q : G) S ∈ seventeenFourTorus_orbit hC β₀) :
    ∀ c ∈ CFSG.pCore 2 (Halpha D hC.alpha) ⊔ Subgroup.zpowers z,
      ∀ S ∈ seventeenFourTorus_orbit hC β₀,
        cimg (c : G) S ∈ seventeenFourTorus_orbit hC β₀ := by
  let H := Halpha D hC.alpha
  let Φ : Set (Set G) := seventeenFourTorus_orbit hC β₀
  let K : Subgroup H :=
    { carrier := {c : H | ∀ S ∈ Φ, cimg (c : G) S ∈ Φ}
      mul_mem' := by
        intro a b ha hb S hS
        change cimg ((a : G) * (b : G)) S ∈ Φ
        rw [cimg_mul]
        exact ha _ (hb S hS)
      one_mem' := by
        intro S hS
        simpa [cimg] using hS
      inv_mem' := by
        intro a ha S hS
        have hsub : (fun T => cimg (a : G) T) '' Φ ⊆ Φ := by
          rintro _ ⟨T, hT, rfl⟩
          exact ha T hT
        have heq : (fun T => cimg (a : G) T) '' Φ = Φ := by
          refine Set.eq_of_subset_of_ncard_le hsub ?_
          rw [Set.ncard_image_of_injective _ (cimg_injective (a : G))]
        have hS' : S ∈ (fun T => cimg (a : G) T) '' Φ := by
          rw [heq]
          exact hS
        obtain ⟨T, hT, hTS⟩ := hS'
        rw [← hTS]
        change cimg (a : G)⁻¹ (cimg (a : G) T) ∈ Φ
        rw [cimg_inv_cimg]
        exact hT }
  have hle : CFSG.pCore 2 H ⊔ Subgroup.zpowers z ≤ K :=
    sup_le hQ (Subgroup.zpowers_le.mpr hz)
  intro c hc S hS
  exact hle hc S hS

private theorem seventeenFourTorus_pCore_transitive_on_orbit (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha)
    {x y : Set G} (hx : x ∈ seventeenFourTorus_orbit hC β₀)
    (hy : y ∈ seventeenFourTorus_orbit hC β₀) :
    ∃ q ∈ CFSG.pCore 2 (Halpha D hC.alpha), cimg (q : G) x = y := by
  obtain ⟨x₀, hx₀M, rfl⟩ := hx
  obtain ⟨y₀, hy₀M, rfl⟩ := hy
  have hyxM : y₀ * x₀⁻¹ ∈ Malpha D hC.alpha :=
    (Malpha D hC.alpha).mul_mem hy₀M ((Malpha D hC.alpha).inv_mem hx₀M)
  have hxD : cimg x₀ β₀ ∈ Dalpha D hC.alpha :=
    seventeenFourTorus_orbit_subset_Dalpha hC hβ₀ ⟨x₀, hx₀M, rfl⟩
  obtain ⟨q, hqQ, hqeq⟩ :=
    exists_mem_pCore_cimg_eq h113 hC hrad hn3 hHns hxD hyxM
  refine ⟨q, hqQ, ?_⟩
  rw [hqeq]
  calc cimg ((y₀ * x₀⁻¹ : G)) (cimg x₀ β₀)
      = cimg (((y₀ * x₀⁻¹ : G) * (x₀ : G))) β₀ := (cimg_mul _ _ _).symm
    _ = cimg (y₀ : G) β₀ := by congr 1; group

private theorem seventeenFourTorus_exists_fixed_of_stable (hC : HypothesisC D) {β₀ : Set G}
    {z : Halpha D hC.alpha} (hzodd : Odd (orderOf z))
    (hstable : ∀ c ∈ CFSG.pCore 2 (Halpha D hC.alpha) ⊔ Subgroup.zpowers z,
      ∀ S ∈ seventeenFourTorus_orbit hC β₀,
        cimg (c : G) S ∈ seventeenFourTorus_orbit hC β₀)
    (htrans0 : ∀ x ∈ seventeenFourTorus_orbit hC β₀,
      ∀ y ∈ seventeenFourTorus_orbit hC β₀,
        ∃ q ∈ CFSG.pCore 2 (Halpha D hC.alpha), cimg (q : G) x = y) :
    ∃ β ∈ seventeenFourTorus_orbit hC β₀, cimg (z : G) β = β := by
  classical
  let H := Halpha D hC.alpha
  let Q : Subgroup H := CFSG.pCore 2 H
  let A : Subgroup H := Subgroup.zpowers z
  let H' : Subgroup H := Q ⊔ A
  let Φ : Set (Set G) := seventeenFourTorus_orbit hC β₀
  let φ : H' →* MulAut G := MulAut.conj.comp (H.subtype.comp H'.subtype)
  letI : MulAction H' G := MulAction.compHom G φ
  letI : MulAction H' (Set G) := Set.mulActionSet
  let P : SubMulAction H' (Set G) :=
    { carrier := Φ, smul_mem' := fun c S hS => hstable (c : H) c.2 S hS }
  haveI : Nonempty P := ⟨⟨β₀, ⟨1, (Malpha D hC.alpha).one_mem, by simp [cimg]⟩⟩⟩
  let Ssub : Subgroup H' := Q.subgroupOf H'; let Bsub : Subgroup H' := A.subgroupOf H'
  haveI : Ssub.Normal := (CFSG.pCore_normal (G := H) (p := 2)).subgroupOf H'
  have hSp : IsPGroup 2 Ssub := (CFSG.pCore_isPGroup (G := H) (p := 2)).comap_subtype
  have hBo : Odd (Nat.card Bsub) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ H')).toEquiv,
      Nat.card_zpowers]
    exact hzodd
  have hSB : Ssub ⊔ Bsub = ⊤ := (Subgroup.codisjoint_subgroupOf_sup Q A).eq_top
  have htrans : ∀ x y : P, ∃ s : Ssub, s.val • x = y := by
    intro x y
    obtain ⟨q, hqQ, hqeq⟩ := htrans0 x.1 x.2 y.1 y.2
    refine ⟨⟨⟨q, Subgroup.mem_sup_left hqQ⟩, Subgroup.mem_subgroupOf.mpr hqQ⟩, ?_⟩
    apply Subtype.ext
    change cimg (q : G) x.1 = y.1
    exact hqeq
  obtain ⟨β, hβfix⟩ :=
    CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints.exists_fixed
      Ssub Bsub hSp hBo hSB P htrans
  let b : Bsub := ⟨⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩,
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)⟩
  refine ⟨β.1, β.2, ?_⟩
  have h := congrArg Subtype.val (hβfix b)
  change cimg ((b.val : H') : G) β.1 = β.1 at h
  simpa using h

private theorem seventeenFourTorus_exists_fixed_in_orbit (h113 : PartThree.Theorem11_3)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {v : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {b₀ : Halpha D hC.alpha} (hb₀ : b₀ ∈ DstarH hC)
    (hmkb₀ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b₀ = v)
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha) (hb₀β₀ : (b₀ : G) ∈ β₀)
    {z : Halpha D hC.alpha} (hzodd : Odd (orderOf z))
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) v) :
    ∃ β ∈ seventeenFourTorus_orbit hC β₀, cimg (z : G) β = β := by
  have hzΦ := seventeenFourTorus_cimg_z_mem_orbit h113 hC hrad hn3 hHns hb₀ hmkb₀ hβ₀ hb₀β₀ hcomm
  have hQΦ : ∀ q ∈ CFSG.pCore 2 (Halpha D hC.alpha),
      ∀ S ∈ seventeenFourTorus_orbit hC β₀,
        cimg (q : G) S ∈ seventeenFourTorus_orbit hC β₀ := by
    intro q hq
    exact seventeenFourTorus_cimg_pCore_mem_orbit hC (β₀ := β₀) (q := q) hq
  have hstable := seventeenFourTorus_sup_mem_orbit hC hzΦ hQΦ
  exact seventeenFourTorus_exists_fixed_of_stable hC hzodd hstable
    (fun x hx y hy => seventeenFourTorus_pCore_transitive_on_orbit h113 hC hrad hn3 hHns hβ₀ hx hy)

private theorem seventeenFourTorus_perpMem_mk_eq_of_mem_orbit (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha) {b₀ : Halpha D hC.alpha}
    (hb₀β₀ : (b₀ : G) ∈ β₀)
    (hmkb₀ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b₀ = v)
    {β : Set G} (hβ : β ∈ seventeenFourTorus_orbit hC β₀) {b : Halpha D hC.alpha}
    (hb : (b : G) ∈ β) :
    perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v := by
  have hV := seventeenFourTorus_blockImage_orbit_subset_Vmem h89 h113 hC hrad hW hn3 hMZ
    hβ₀ hb₀β₀ β hβ
  have hmem : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈
      blockImage hC β := ⟨b, hb, rfl⟩
  have := (mem_Vmem.mp (hV hmem)).2
  rwa [hmkb₀] at this

private theorem seventeenFourTorus_commute_mk_of_mem_orbits (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hw : w ∈ imageClass hC) (hvw : Commute v w)
    {β₀ : Set G} (hβ₀ : β₀ ∈ Dalpha D hC.alpha) {b₀ : Halpha D hC.alpha}
    (hb₀β₀ : (b₀ : G) ∈ β₀)
    (hmkb₀ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b₀ = v)
    {γ₀ : Set G} (hγ₀ : γ₀ ∈ Dalpha D hC.alpha) {c₀ : Halpha D hC.alpha}
    (hc₀γ₀ : (c₀ : G) ∈ γ₀)
    (hmkc₀ : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c₀ = w)
    {β γ : Set G} (hβ : β ∈ seventeenFourTorus_orbit hC β₀)
    (hγ : γ ∈ seventeenFourTorus_orbit hC γ₀) {b c : Halpha D hC.alpha}
    (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ) :
    Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) := by
  have hβD := seventeenFourTorus_orbit_subset_Dalpha hC hβ₀ hβ
  have hmbV := seventeenFourTorus_perpMem_mk_eq_of_mem_orbit h89 h113 hC hrad hW hn3 hMZ
    hβ₀ hb₀β₀ hmkb₀ hβ hb
  have hmcV := seventeenFourTorus_perpMem_mk_eq_of_mem_orbit h89 h113 hC hrad hW hn3 hMZ
    hγ₀ hc₀γ₀ hmkc₀ hγ hc
  have hwb : w ∈ perpMem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
    rw [hmbV]
    exact mem_perpMem.mpr ⟨hw, hvw.symm⟩
  have hbw : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) w :=
    (mem_perpMem.mp hwb).2.symm
  have hbwperp : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈
      perpMem (imageClass hC) w :=
    mem_perpMem.mpr ⟨⟨b, ⟨β, hβD, hb⟩, rfl⟩, hbw⟩
  have hbc : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b ∈
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) := by
    rw [hmcV]
    exact hbwperp
  exact (mem_perpMem.mp hbc).2

private theorem seventeenFourTorus_mk_mem_lineMem_of_line (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {p : Set G} (hp : p ∈ blockLine D β γ \ {β, γ}) {d : Halpha D hC.alpha}
    (hd : (d : G) ∈ p) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈
      lineMem (imageClass hC) v w := by
  have hdLine : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ∈
      lineMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) :=
    mk_mem_lineMem h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc hp.1 hd
  have hlineEq : lineMem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      lineMem (imageClass hC) v w := by
    unfold lineMem
    rw [hβv, hγw]
  rwa [hlineEq] at hdLine

private theorem seventeenFourTorus_perp_ne_of_mem_line_diff (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {p : Set G} (hp : p ∈ blockLine D β γ \ {β, γ}) {d : Halpha D hC.alpha}
    (hd : (d : G) ∈ p) :
    perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ≠
        perpMem (imageClass hC) v ∧
      perpMem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ≠
        perpMem (imageClass hC) w := by
  have hpΛ : p ∈ blockLine D β γ := hp.1
  have hpnot : p ∉ ({β, γ} : Set (Set G)) := hp.2
  constructor
  · intro heq
    have hβΛ : β ∈ blockLine D β γ := left_mem_blockLine hβ.2.1
    have heq' : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) =
        perpMem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) := by
      rw [heq, ← hβv]
    have hpβ : p = β := eq_of_perpMem_mk_eq h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc
      hpΛ hβΛ hd hb heq'
    exact hpnot (by rw [hpβ]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
  · intro heq
    have hγβ : γ ∈ blockClass β := by
      rw [blockClass_eq_of_mem hβ.1]
      exact hγ.1
    have hγΛ : γ ∈ blockLine D β γ := right_mem_blockLine hγβ hγ.2.1
    have heq' : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) =
        perpMem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) := by
      rw [heq, ← hγw]
    have hpγ : p = γ := eq_of_perpMem_mk_eq h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc
      hpΛ hγΛ hd hc heq'
    exact hpnot (by rw [hpγ]; exact Set.mem_insert_iff.mpr (Or.inr rfl))

private theorem seventeenFourTorus_pow_eq_one_of_fixes (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {g' : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) = perpMem (imageClass hC) x →
        g' ^ i = 1)
    {z : Halpha D hC.alpha}
    (hmkz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z = g')
    {p : Set G} (hp : p ∈ blockLine D β γ \ {β, γ}) {d : Halpha D hC.alpha}
    (hd : (d : G) ∈ p) (i : ℕ) (hfix : cimg ((z : G) ^ i) p = p) : g' ^ i = 1 := by
  have hpD : p ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc hp.1
  have hdLine := seventeenFourTorus_mk_mem_lineMem_of_line h89 h113 hC hrad hW hn3 hMZ
    hβ hγ hb hc hbc hnebc hβv hγw hp hd
  have hne := seventeenFourTorus_perp_ne_of_mem_line_diff h89 h113 hC hrad hW hn3 hMZ
    hβ hγ hb hc hbc hnebc hβv hγw hp hd
  have hconjmem : ((z ^ i * d * (z ^ i)⁻¹ : Halpha D hC.alpha) : G) ∈ p := by
    rw [← hfix]
    exact ⟨(d : G), hd, by simp⟩
  have hperp := perpMem_mk_eq_of_mem h89 h113 hC hrad hW hn3 hMZ hpD hconjmem hd
  have hmkconj : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
      (z ^ i * d * (z ^ i)⁻¹) = g' ^ i *
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d * (g' ^ i)⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_pow, hmkz]
  have hmain : perpMem (imageClass hC)
      (g' ^ i * QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d * (g' ^ i)⁻¹) =
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) := by
    rwa [← hmkconj]
  exact hsemi _ hdLine hne.1 hne.2 i hmain

private theorem seventeenFourTorus_orderOf_dvd_of_fixes (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {g' : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) = perpMem (imageClass hC) x →
        g' ^ i = 1)
    {z : Halpha D hC.alpha}
    (hmkz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z = g')
    {p : Set G} (hp : p ∈ blockLine D β γ \ {β, γ}) (i : ℕ)
    (hfix : cimg ((z : G) ^ i) p = p) : orderOf g' ∣ i := by
  have hpD : p ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine_of_ne h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc hp.1
  have hpclassβ : p ∈ blockClass β := (mem_blockLine_iff.mp hp.1).1
  have hpclass : p ∈ blockClass hC.alpha := by
    rwa [blockClass_eq_of_mem hβ.1] at hpclassβ
  obtain ⟨d, hd⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hpclass
  let dH : Halpha D hC.alpha := ⟨d, Subgroup.subset_closure ⟨p, hpD, hd⟩⟩
  have hdH : (dH : G) ∈ p := hd
  have h1 := seventeenFourTorus_pow_eq_one_of_fixes h89 h113 hC hrad hW hn3 hMZ
    hβ hγ hb hc hbc hnebc hβv hγw hsemi hmkz hp hdH i hfix
  exact orderOf_dvd_iff_pow_eq_one.mpr h1

private theorem seventeenFourTorus_cimg_mem_line_diff (hC : HypothesisC D) {β γ : Set G}
    {z : Halpha D hC.alpha} (hzβ : cimg (z : G) β = β) (hzγ : cimg (z : G) γ = γ)
    {p : Set G} (hp : p ∈ blockLine D β γ \ {β, γ}) :
    cimg (z : G) p ∈ blockLine D β γ \ {β, γ} := by
  have hΛinv : (cimg (z : G)) '' blockLine D β γ = blockLine D β γ := by
    have h := blockLine_cimg hC.setup.normal (z : G) β γ
    rw [hzβ, hzγ] at h
    exact h.symm
  have hmem : cimg (z : G) p ∈ blockLine D β γ := by
    rw [← hΛinv]
    exact ⟨p, hp.1, rfl⟩
  refine ⟨hmem, ?_⟩
  intro hpc
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hpc
  apply hp.2
  rcases hpc with h | h
  · have hpβ : p = β := by
      calc p = cimg (z : G)⁻¹ (cimg (z : G) p) := (cimg_inv_cimg (z : G) p).symm
        _ = cimg (z : G)⁻¹ β := by rw [h]
        _ = cimg (z : G)⁻¹ (cimg (z : G) β) := by rw [hzβ]
        _ = β := cimg_inv_cimg (z : G) β
    rw [hpβ]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · have hpγ : p = γ := by
      calc p = cimg (z : G)⁻¹ (cimg (z : G) p) := (cimg_inv_cimg (z : G) p).symm
        _ = cimg (z : G)⁻¹ γ := by rw [h]
        _ = cimg (z : G)⁻¹ (cimg (z : G) γ) := by rw [hzγ]
        _ = γ := cimg_inv_cimg (z : G) γ
    rw [hpγ]
    exact Set.mem_insert_iff.mpr (Or.inr rfl)

private theorem seventeenFourTorus_mem_line_diff_of_cimg (hC : HypothesisC D) {β γ : Set G}
    {z : Halpha D hC.alpha} (hzβ : cimg (z : G) β = β) (hzγ : cimg (z : G) γ = γ)
    {p : Set G} (hp : cimg (z : G) p ∈ blockLine D β γ \ {β, γ}) :
    p ∈ blockLine D β γ \ {β, γ} := by
  have hΛinv : (cimg (z : G)) '' blockLine D β γ = blockLine D β γ := by
    have h := blockLine_cimg hC.setup.normal (z : G) β γ
    rw [hzβ, hzγ] at h
    exact h.symm
  have hpΛ : cimg (z : G) p ∈ blockLine D β γ := hp.1
  rw [← hΛinv] at hpΛ
  obtain ⟨q, hq, hqp⟩ := hpΛ
  have hqp' : q = p := cimg_injective (z : G) hqp
  rw [hqp'] at hq
  refine ⟨hq, ?_⟩
  intro hpc
  apply hp.2
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hpc ⊢
  rcases hpc with h | h
  · exact Or.inl (by rw [h, hzβ])
  · exact Or.inr (by rw [h, hzγ])

private theorem seventeenFourTorus_line_invariant (hC : HypothesisC D) {β γ : Set G}
    {z : Halpha D hC.alpha} (hzβ : cimg (z : G) β = β) (hzγ : cimg (z : G) γ = γ) :
    ∀ p : Set G, p ∈ blockLine D β γ \ {β, γ} ↔
      cimg (z : G) p ∈ blockLine D β γ \ {β, γ} := by
  intro p
  exact ⟨seventeenFourTorus_cimg_mem_line_diff hC hzβ hzγ,
    seventeenFourTorus_mem_line_diff_of_cimg hC hzβ hzγ⟩

private theorem seventeenFourTorus_dvd_of_line_core (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {g' : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) = perpMem (imageClass hC) x →
        g' ^ i = 1)
    {z : Halpha D hC.alpha}
    (hmkz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z = g')
    (hzβ : cimg (z : G) β = β) (hzγ : cimg (z : G) γ = γ)
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha)
    (hcard : (blockLine D β γ \ {β, γ}).ncard =
      (blockLine D hC.alpha δ).ncard - 2) :
    orderOf g' ∣ (blockLine D hC.alpha δ).ncard - 2 := by
  classical
  let Λ' : Set (Set G) := blockLine D β γ \ {β, γ}
  have hiff : ∀ p : Set G, cimg (z : G) p ∈ Λ' ↔ p ∈ Λ' :=
    fun p => (seventeenFourTorus_line_invariant hC hzβ hzγ p).symm
  let e : Equiv.Perm (Set G) :=
    { toFun := cimg (z : G)
      invFun := cimg (z : G)⁻¹
      left_inv := fun S => cimg_inv_cimg (z : G) S
      right_inv := fun S => cimg_cimg_inv (z : G) S }
  let π : Equiv.Perm Λ' := e.subtypePerm hiff
  have hπpow : ∀ (i : ℕ) (p : Λ'), ((π ^ i) p).1 = cimg ((z : G) ^ i) p.1 := by
    intro i
    induction i with
    | zero => intro p; simp [cimg]
    | succ i ih =>
      intro p
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply]
      change cimg (z : G) ((π ^ i) p).1 = cimg ((z : G) ^ (i + 1)) p.1
      rw [ih, pow_succ', cimg_mul]
  have hcyc : ∀ (i : ℕ) (p : Λ'), (π ^ i) p = p → orderOf g' ∣ i := by
    intro i p hp
    have hfix : cimg ((z : G) ^ i) p.1 = p.1 := by
      have := congrArg Subtype.val hp
      rwa [hπpow i p] at this
    exact seventeenFourTorus_orderOf_dvd_of_fixes h89 h113 hC hrad hW hn3 hMZ
      hβ hγ hb hc hbc hnebc hβv hγw hsemi hmkz p.2 i hfix
  by_cases hg'1 : g' = 1
  · rw [hg'1, orderOf_one]
    exact one_dvd _
  · have hno : ∀ p : Λ', π p ≠ p := by
      intro p hp
      have h1 := hcyc 1 p hp
      exact hg'1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
    have hdvd := seventeenFourTorus_dvd_card_of_perm π hno hcyc
    rwa [Nat.card_coe_set_eq, hcard] at hdvd

private theorem seventeenFourTorus_ncard_line_diff (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hβγne : β ≠ γ) {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) :
    (blockLine D β γ \ {β, γ}).ncard =
      (blockLine D hC.alpha δ).ncard - 2 := by
  have hγDβ : γ ∈ Dalpha D β :=
    mem_Dalpha_of_commute_mk h89 h113 hC hrad hW hn3 hMZ hβ hγ hb hc hbc hnebc
  have hβΛ : β ∈ blockLine D β γ := left_mem_blockLine hβ.2.1
  have hγβ : γ ∈ blockClass β := by
    rw [blockClass_eq_of_mem hβ.1]
    exact hγ.1
  have hγΛ : γ ∈ blockLine D β γ := right_mem_blockLine hγβ hγ.2.1
  have hpairsub : ({β, γ} : Set (Set G)) ⊆ blockLine D β γ := by
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hβΛ
    · exact hγΛ
  rw [Set.ncard_diff hpairsub (Set.toFinite _), Set.ncard_pair hβγne,
    ncard_blockLine_eq hC hβ.1 hγDβ hδ]

private theorem seventeenFourTorus_dvd_of_line (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    {β γ : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hγ : γ ∈ Dalpha D hC.alpha)
    (hβγne : β ≠ γ) {b c : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hc : (c : G) ∈ γ)
    (hbc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hnebc : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c))
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c) =
      perpMem (imageClass hC) w)
    {g' : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) = perpMem (imageClass hC) x →
        g' ^ i = 1)
    {z : Halpha D hC.alpha}
    (hmkz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z = g')
    (hzβ : cimg (z : G) β = β) (hzγ : cimg (z : G) γ = γ)
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) :
    orderOf g' ∣ (blockLine D hC.alpha δ).ncard - 2 := by
  have hcard := seventeenFourTorus_ncard_line_diff h89 h113 hC hrad hW hn3 hMZ
    hβ hγ hβγne hb hc hbc hnebc hδ
  exact seventeenFourTorus_dvd_of_line_core h89 h113 hC hrad hW hn3 hMZ
    hβ hγ hb hc hbc hnebc hβv hγw hsemi hmkz hzβ hzγ hδ hcard

private theorem seventeenFourTorus_nebc_and_ne (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    {β γ : Set G} (hβD : β ∈ Dalpha D hC.alpha) (hγD : γ ∈ Dalpha D hC.alpha)
    {bH cH : Halpha D hC.alpha} (hbHβ : (bH : G) ∈ β) (hcHγ : (cH : G) ∈ γ)
    (hβv : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH) =
      perpMem (imageClass hC) v)
    (hγw : perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH) =
      perpMem (imageClass hC) w) :
    perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH) ≠
        perpMem (imageClass hC)
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH) ∧ β ≠ γ := by
  have hnebc : perpMem (imageClass hC)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) bH) ≠
      perpMem (imageClass hC)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) cH) := by
    rw [hβv, hγw]
    exact hne
  refine ⟨hnebc, ?_⟩
  intro hEq
  have hbHγ : (bH : G) ∈ γ := by rw [← hEq]; exact hbHβ
  exact hnebc (perpMem_mk_eq_of_mem h89 h113 hC hrad hW hn3 hMZ hγD hbHγ hcHγ)

private theorem seventeenFourTorus_dvd_of_lift (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    {g' : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hg'v : ∀ x ∈ Vmem (imageClass hC) v, Commute g' x)
    (hg'w : ∀ x ∈ Vmem (imageClass hC) w, Commute g' x)
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) = perpMem (imageClass hC) x →
        g' ^ i = 1)
    {z : Halpha D hC.alpha} (hzodd : Odd (orderOf z))
    (hmkz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z = g')
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) :
    orderOf g' ∣ (blockLine D hC.alpha δ).ncard - 2 := by
  classical
  have hvmem : v ∈ imageClass hC := hv
  have hwmem : w ∈ imageClass hC := hw
  obtain ⟨b₀, hb₀, hmkb₀⟩ := hv
  obtain ⟨c₀, hc₀, hmkc₀⟩ := hw
  obtain ⟨β₀, hβ₀, hb₀β₀⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hb₀)
  obtain ⟨γ₀, hγ₀, hc₀γ₀⟩ := mem_DalphaStar_iff.mp ((mem_DstarH_iff hC).mp hc₀)
  have hcommzv : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) v := by
    rw [hmkz]
    exact hg'v v (mem_Vmem_self hvmem)
  have hcommzw : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) w := by
    rw [hmkz]
    exact hg'w w (mem_Vmem_self hwmem)
  obtain ⟨β, hβΦ, hzβ⟩ := seventeenFourTorus_exists_fixed_in_orbit h113 hC hrad hn3 hHns
    hb₀ hmkb₀ hβ₀ hb₀β₀ hzodd hcommzv
  obtain ⟨γ, hγΦ, hzγ⟩ := seventeenFourTorus_exists_fixed_in_orbit h113 hC hrad hn3 hHns
    hc₀ hmkc₀ hγ₀ hc₀γ₀ hzodd hcommzw
  have hβD := seventeenFourTorus_orbit_subset_Dalpha hC hβ₀ hβΦ
  have hγD := seventeenFourTorus_orbit_subset_Dalpha hC hγ₀ hγΦ
  obtain ⟨b, hbβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβD.1
  obtain ⟨c, hcγ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγD.1
  let bH : Halpha D hC.alpha := ⟨b, Subgroup.subset_closure ⟨β, hβD, hbβ⟩⟩
  let cH : Halpha D hC.alpha := ⟨c, Subgroup.subset_closure ⟨γ, hγD, hcγ⟩⟩
  have hbHβ : (bH : G) ∈ β := hbβ
  have hcHγ : (cH : G) ∈ γ := hcγ
  have hbc := seventeenFourTorus_commute_mk_of_mem_orbits h89 h113 hC hrad hW hn3 hMZ
    hwmem hvw hβ₀ hb₀β₀ hmkb₀ hγ₀ hc₀γ₀ hmkc₀ hβΦ hγΦ hbHβ hcHγ
  have hβv := seventeenFourTorus_perpMem_mk_eq_of_mem_orbit h89 h113 hC hrad hW hn3 hMZ
    hβ₀ hb₀β₀ hmkb₀ hβΦ hbHβ
  have hγw := seventeenFourTorus_perpMem_mk_eq_of_mem_orbit h89 h113 hC hrad hW hn3 hMZ
    hγ₀ hc₀γ₀ hmkc₀ hγΦ hcHγ
  obtain ⟨hnebc, hβγne⟩ := seventeenFourTorus_nebc_and_ne h89 h113 hC hrad hW hn3 hMZ
    hne hβD hγD hbHβ hcHγ hβv hγw
  exact seventeenFourTorus_dvd_of_line h89 h113 hC hrad hW hn3 hMZ
    hβD hγD hβγne hbHβ hcHγ hbc hnebc hβv hγw hsemi hmkz hzβ hzγ hδ

theorem dvd_ncard_blockLine_sub_two_of_torus (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {v w : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hv : v ∈ imageClass hC) (hw : w ∈ imageClass hC) (hvw : Commute v w)
    (hne : perpMem (imageClass hC) v ≠ perpMem (imageClass hC) w)
    {g : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hg : Odd (orderOf g))
    (hgv : ∀ x ∈ Vmem (imageClass hC) v, Commute g x)
    (hgw : ∀ x ∈ Vmem (imageClass hC) w, Commute g x)
    (hsemi : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g ^ i * x * (g ^ i)⁻¹) = perpMem (imageClass hC) x →
        g ^ i = 1)
    {δ : Set G} (hδ : δ ∈ Dalpha D hC.alpha) :
    orderOf g ∣ (blockLine D hC.alpha δ).ncard - 2 := by
  classical
  let H := Halpha D hC.alpha
  let R := CFSG.solvableRadical H
  let mk := QuotientGroup.mk' R
  obtain ⟨z, hzodd, k, hmkz⟩ := seventeenFourTorus_exists_odd_lift R g
  let g' : H ⧸ R := g ^ (2 ^ k)
  have hmkz' : mk z = g' := hmkz
  have hg'v : ∀ x ∈ Vmem (imageClass hC) v, Commute g' x := by
    intro x hx
    exact (hgv x hx).pow_left (2 ^ k)
  have hg'w : ∀ x ∈ Vmem (imageClass hC) w, Commute g' x := by
    intro x hx
    exact (hgw x hx).pow_left (2 ^ k)
  have hsemi' : ∀ x ∈ lineMem (imageClass hC) v w,
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) v →
      perpMem (imageClass hC) x ≠ perpMem (imageClass hC) w →
      ∀ i : ℕ, perpMem (imageClass hC) (g' ^ i * x * (g' ^ i)⁻¹) =
        perpMem (imageClass hC) x → g' ^ i = 1 := by
    intro x hx hxv hxw i hi
    have hi' : perpMem (imageClass hC)
        (g ^ (2 ^ k * i) * x * (g ^ (2 ^ k * i))⁻¹) = perpMem (imageClass hC) x := by
      simpa [g', pow_mul] using hi
    have h1 := hsemi x hx hxv hxw (2 ^ k * i) hi'
    simpa [g', pow_mul] using h1
  have hdvd := seventeenFourTorus_dvd_of_lift h89 h113 hC hrad hW hn3 hMZ hHns
    hv hw hvw hne hg'v hg'w hsemi' hzodd hmkz' hδ
  have hord : orderOf g' = orderOf g := by
    rw [show g' = g ^ (2 ^ k) from rfl, orderOf_pow]
    have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hg).pow_right k
    rw [hcop.gcd_eq_one, Nat.div_one]
  rwa [hord] at hdvd

end CFSG.OddTranspositions.PartFour
