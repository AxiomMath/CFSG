module

public import CFSG.OddTranspositions.PartThree.EightEight.ASFibres
public import CFSG.OddTranspositions.PartThree.EightEight.TransversalCover
import CFSG.OddTranspositions.PartThree.EightEight.WreathBlocks
import CFSG.OddTranspositions.PartThree.EightEight.Eighteen
import CFSG.OddTranspositions.PartThree.EightEight.StarConj
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightEight.ThirdCentralizer
import CFSG.OddTranspositions.PartThree.EightFive.Transitive

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem eq_mul_y_mul_e_of_coe_eq (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {x' z : Halpha D hC.alpha} (hx' : (x' : G) = x)
    (hz : (z : G) = (x * y * w) ^ n) :
    z = x' * ⟨y, Subgroup.subset_closure hy⟩ *
      ⟨x * y * (x * y * w) ^ n,
        Subgroup.subset_closure (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord)⟩ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hx', hz]
  exact (mul_mul_mul_mul_cancel_of_isTriangle hC.setup.oddT ht ((x * y * w) ^ n)).symm

private theorem commute_of_mk_eq_mk_x_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {x' p q : Halpha D hC.alpha} (hx' : (x' : G) = x)
    (hp : p ∈ DstarH hC)
    (hpx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x')
    (hq : q ∈ DstarH hC)
    (hqΔ : (q : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hqx : q ≠ x') (hc : Commute x' q) : Commute p q := by
  have hxΔ : x ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := self_mem_conjOrbit _ x
  have hx'Δ : (x' : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := by
    rw [hx']; exact hxΔ
  have hinj := injOn_mk_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
  have hne_mk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q := by
    rw [hpx]
    intro h
    exact hqx (hinj hx'Δ hqΔ h).symm
  have hc' : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q) := by
    simpa only [hpx] using hc.map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  exact commute_of_commute_mk_of_ne_mk hC hp hq hne_mk hc'

theorem commute_of_mk_eq_of_isTriangle (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {z d : Halpha D hC.alpha}
    (hz : (z : G) = (x * y * w) ^ n) (hd : d ∈ DstarH hC)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    Commute (d : G) x ∧ Commute (d : G) w ∧ Commute (d : G) y := by
  have hdc : ∀ a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x, Commute (d : G) a := by
    have h := (mem_starN_of_mk_eq h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
      ((mem_DstarH_iff hC).mp hd) hz hdz).1
    simp only [starSigma] at h
    rw [setOf_centSet_notMem_eq (D := D) hC.setup ht hn hord] at h
    exact h.2
  exact ⟨hdc x (self_mem_conjOrbit _ x), hdc w (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2,
    hdc y (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1⟩

private theorem commute_d_of_mk_eq_mk_x (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {x' z d p : Halpha D hC.alpha}
    (hx' : (x' : G) = x) (hz : (z : G) = (x * y * w) ^ n) (hd : d ∈ DstarH hC)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z)
    (hp : p ∈ DstarH hC)
    (hpx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x') :
    Commute d p ∧ Commute d x' := by
  have hxΔ : x ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := self_mem_conjOrbit _ x
  have hdx : Commute d x' := by
    apply Subtype.ext
    show (d : G) * (x' : G) = (x' : G) * (d : G)
    rw [hx']
    exact (commute_of_mk_eq_of_isTriangle h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hz hd
      hdz).1.eq
  have hdp : Commute d p := by
    have hne_dp : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d ≠
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p := by
      rw [hdz, hpx]
      have hxH : (⟨x, Subgroup.subset_closure hx⟩ : Halpha D hC.alpha) = x' :=
        Subtype.ext hx'.symm
      rw [← hxH]
      exact (mk_ne_of_mem_conjOrbit (a := ⟨x, Subgroup.subset_closure hx⟩) (z := z)
        h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hxΔ hz).symm
    have hc_dp : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) := by
      have hz_x : Commute z x' := by
        apply Subtype.ext
        show (z : G) * (x' : G) = (x' : G) * (z : G)
        rw [hx', hz]
        exact (IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord).2.2.1.eq
      simpa only [hdz, hpx] using hz_x.map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
    exact commute_of_commute_mk_of_ne_mk hC hd hp hne_dp hc_dp
  exact ⟨hdp, hdx⟩

private theorem commute_y_e_of_mk_eq_mk_x (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {x' p : Halpha D hC.alpha} (hx' : (x' : G) = x)
    (hp : p ∈ DstarH hC)
    (hpx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x') :
    Commute p ⟨y, Subgroup.subset_closure hy⟩ ∧
      Commute p ⟨x * y * (x * y * w) ^ n,
        Subgroup.subset_closure (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord)⟩ := by
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let eH : Halpha D hC.alpha :=
    ⟨x * y * (x * y * w) ^ n,
      Subgroup.subset_closure (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord)⟩
  have hxΔ : x ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := self_mem_conjOrbit _ x
  have hyΔ : y ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have heΔ : (eH : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
  have hcx_y : Commute x' yH := by
    apply Subtype.ext
    show (x' : G) * y = y * (x' : G)
    rw [hx']
    exact ht.2.2.2.2.1.eq
  have hcx_e : Commute x' eH := by
    apply Subtype.ext
    show (x' : G) * (eH : G) = (eH : G) * (x' : G)
    rw [hx']
    exact (commute_mul_mul_pow_left hC.setup.oddT hC.setup.normal ht hn hord).symm.eq
  have hy_ne : yH ≠ x' := by
    intro h
    apply ht.2.2.2.1
    have h' := congrArg Subtype.val h
    rw [hx'] at h'
    exact h'.symm
  have he_ne : eH ≠ x' := by
    intro h
    exact (mul_mul_pow_ne_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hxΔ hyΔ).1
      (by
        have h' := congrArg Subtype.val h
        rw [hx'] at h'
        exact h')
  exact ⟨commute_of_mk_eq_mk_x_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
      hx' hp hpx hy hyΔ hy_ne hcx_y,
    commute_of_mk_eq_mk_x_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
      hx' hp hpx (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord) heΔ he_ne hcx_e⟩

theorem conj_eq_conj_of_mk_eq_mk_x (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {x' z d : Halpha D hC.alpha} (hx' : (x' : G) = x)
    (hz : (z : G) = (x * y * w) ^ n) (hd : d ∈ DstarH hC)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z)
    {p : Halpha D hC.alpha} (hp : p ∈ DstarH hC)
    (hpx : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x') :
    z * p * z⁻¹ = x' * p * x'⁻¹ ∧ d * z * p * (d * z)⁻¹ = x' * p * x'⁻¹ := by
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let eH : Halpha D hC.alpha :=
    ⟨x * y * (x * y * w) ^ n,
      Subgroup.subset_closure (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord)⟩
  obtain ⟨hdp, hdx⟩ :=
    commute_d_of_mk_eq_mk_x h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hx' hz hd hdz hp hpx
  obtain ⟨hpy, hpe⟩ :=
    commute_y_e_of_mk_eq_mk_x h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hx' hp hpx
  have heq : z = x' * yH * eH :=
    eq_mul_y_mul_e_of_coe_eq hC ht hx hw hy hn hord hx' hz
  have hconj : z * p * z⁻¹ = x' * p * x'⁻¹ := by
    rw [heq]
    have hye : (yH * eH) * p * (yH * eH)⁻¹ = p :=
      Commute.mul_inv_cancel (hpy.mul_right hpe).symm
    calc (x' * yH * eH) * p * (x' * yH * eH)⁻¹
        = x' * ((yH * eH) * p * (yH * eH)⁻¹) * x'⁻¹ := by group
      _ = x' * p * x'⁻¹ := by rw [hye]
  refine ⟨hconj, ?_⟩
  have hdcomm : Commute d (x' * p * x'⁻¹) :=
    (hdx.mul_right hdp).mul_right hdx.inv_right
  calc d * z * p * (d * z)⁻¹ = d * (z * p * z⁻¹) * d⁻¹ := by group
    _ = d * (x' * p * x'⁻¹) * d⁻¹ := by rw [hconj]
    _ = x' * p * x'⁻¹ := by rw [hdcomm.eq]; group

private theorem mem_closure_of_mem_conjOrbit_of_subset (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {z : Halpha D hC.alpha}
    (hz : (z : G) = (x * y * w) ^ n) {C : Set (Halpha D hC.alpha)}
    (hsub : ∀ a : Halpha D hC.alpha,
      (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x → a ∈ C) :
    z ∈ Subgroup.closure C := by
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let eH : Halpha D hC.alpha :=
    ⟨x * y * (x * y * w) ^ n,
      Subgroup.subset_closure (mul_mul_pow_mem_DalphaStar hC ht hx hw hy hn hord)⟩
  have hxΔ : x ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x := self_mem_conjOrbit _ x
  have hyΔ : y ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    (mem_conjOrbit_of_third_kind hC.setup ht hn hord).1
  have heΔ : (eH : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x :=
    mul_mul_pow_mem_conjOrbit hC.setup ht hn hord
  have heq : z = xH * yH * eH :=
    eq_mul_y_mul_e_of_coe_eq hC ht hx hw hy hn hord rfl hz
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (hsub xH hxΔ))
    (Subgroup.subset_closure (hsub yH hyΔ))) (Subgroup.subset_closure (hsub eH heΔ))

theorem closure_conjOrbit_le_transversalGroup (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {z d : Halpha D hC.alpha}
    (hz : (z : G) = (x * y * w) ^ n) (hd : d ∈ DstarH hC)
    (hdz : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) z) :
    Subgroup.closure {a : Halpha D hC.alpha |
        (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x} ≤
      transversalGroup (DstarH hC) (d * z) ∧
    d * z ∈ transversalGroup (DstarH hC) (d * z) := by
  obtain ⟨-, -, -, hcommd, -, hall⟩ :=
    mul_mem_solvableRadical_and_commute h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
      ((mem_DstarH_iff hC).mp hd) hz hdz
  have hCsub : ∀ a : Halpha D hC.alpha,
      (a : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x →
        a ∈ {p | p ∈ DstarH hC ∧ Commute p (d * z)} := by
    intro a ha
    exact ⟨(mem_DstarH_iff hC).mpr
      (conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord ha), (hall a ha).symm⟩
  rw [transversalGroup]
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    intro a ha
    exact Subgroup.subset_closure (hCsub a ha)
  · have hdC : d ∈ {p | p ∈ DstarH hC ∧ Commute p (d * z)} := ⟨hd, hcommd.symm⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hdC)
      (mem_closure_of_mem_conjOrbit_of_subset hC ht hx hw hy hn hord hz hCsub)

end CFSG.OddTranspositions.PartThree.EightEight
