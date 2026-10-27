module

public import CFSG.OddTranspositions.PartThree.Nine.NineFiveX
import CFSG.OddTranspositions.PartThree.Nine.NineFiveGraph
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.GH74.Uniqueness.Section128Bender
import CFSG.GH74.Uniqueness.Bender.CentralizesCenterCard
import CFSG.GH74.Uniqueness.Bender.CentralizesCenterSq
import CFSG.GH74.Uniqueness.Bender.Sylow2OrderFour
import CFSG.GH74.Uniqueness.Bender.SuzukiAut
import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GH74.Uniqueness.Section5Prop53

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.GH74.Uniqueness.Bender (BenderType autCentralizer le_borel mem_autCentralizer_iff
  mem_rootCenter_iff rootCenter isBenderGroup_iff_exists_benderType)
open CFSG.GH74.Uniqueness (Sec128B.exists_sylow_mem_of_orderOf_eq_two
  Sec128B.mem_rootCenter_of_commute)

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem mem_Halpha_of_mem_commSet (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    {x : G} (hx : x ∈ commSet D hC.d) : x ∈ Halpha D hC.alpha :=
  Subgroup.subset_closure ((DalphaStar_eq_commSet hC h3.1).symm ▸ hx)

private theorem Halpha_eq_closure (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) :
    Halpha D hC.alpha = Subgroup.closure (commSet D hC.d) := by
  rw [Halpha, DalphaStar_eq_commSet hC h3.1]

open Classical in
private noncomputable def bar (hC : HypothesisC D) (x : G) :
    Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) :=
  if hx : x ∈ Halpha D hC.alpha then
    ((⟨x, hx⟩ : Halpha D hC.alpha) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))
  else 1

omit [Finite G] in
private theorem bar_of_mem (hC : HypothesisC D) {x : G} (hx : x ∈ Halpha D hC.alpha) :
    bar hC x =
      ((⟨x, hx⟩ : Halpha D hC.alpha) : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
  dif_pos hx

omit [Finite G] in
private theorem bar_mul (hC : HypothesisC D) {x y : G} (hx : x ∈ Halpha D hC.alpha)
    (hy : y ∈ Halpha D hC.alpha) : bar hC (x * y) = bar hC x * bar hC y := by
  rw [bar_of_mem hC hx, bar_of_mem hC hy, bar_of_mem hC (Subgroup.mul_mem _ hx hy)]
  rfl

omit [Finite G] in
private theorem bar_inv (hC : HypothesisC D) {x : G} (hx : x ∈ Halpha D hC.alpha) :
    bar hC x⁻¹ = (bar hC x)⁻¹ := by
  rw [bar_of_mem hC hx, bar_of_mem hC (Subgroup.inv_mem _ hx)]
  rfl

omit [Finite G] in
private theorem bar_one (hC : HypothesisC D) : bar hC 1 = 1 := by
  rw [bar_of_mem hC (Subgroup.one_mem _)]
  rfl

omit [Finite G] in
private theorem bar_pow (hC : HypothesisC D) {x : G} (hx : x ∈ Halpha D hC.alpha) (k : ℕ) :
    bar hC (x ^ k) = bar hC x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, bar_one]
  | succ k ih => rw [pow_succ, pow_succ, bar_mul hC (Subgroup.pow_mem _ hx k) hx, ih]

omit [Finite G] in
private theorem bar_eq_one_iff (hC : HypothesisC D) {x : G} (hx : x ∈ Halpha D hC.alpha) :
    bar hC x = 1 ↔ ∀ h ∈ Halpha D hC.alpha, Commute x h := by
  rw [bar_of_mem hC hx, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  exact ⟨fun hc h hh => (congrArg Subtype.val (hc ⟨h, hh⟩)).symm,
    fun hc h => Subtype.ext (hc h h.2).eq.symm⟩

omit [Finite G] in
private theorem commute_bar (hC : HypothesisC D) {x y : G} (hx : x ∈ Halpha D hC.alpha)
    (hy : y ∈ Halpha D hC.alpha) (hxy : Commute x y) : Commute (bar hC x) (bar hC y) := by
  show bar hC x * bar hC y = bar hC y * bar hC x
  rw [← bar_mul hC hx hy, ← bar_mul hC hy hx, hxy.eq]

private theorem bar_d (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) : bar hC hC.d = 1 :=
  (bar_eq_one_iff hC (d_mem_Halpha hC h3)).mpr fun _ hh =>
    (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hh)).symm

private theorem orderOf_bar (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {x : G}
    (hx : x ∈ commSet D hC.d) : orderOf (bar hC x) = 2 := by
  have hxH := mem_Halpha_of_mem_commSet hC h3 hx
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hx.1
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · rw [pow_two, ← bar_mul hC hxH hxH, hx2, bar_one]
  · have hxc := (bar_eq_one_iff hC hxH).mp h1
    have hlc : ∀ h ∈ Halpha D hC.alpha, Commute (hC.d * x) h := fun h hh =>
      (show Commute hC.d h from (Subgroup.mem_centralizer_singleton_iff.mp
        (PartThree.Halpha_le_centralizer_d hC hh)).symm).mul_left (hxc h hh)
    have hl2 : hC.d * x * (hC.d * x) = 1 := by
      calc hC.d * x * (hC.d * x) = hC.d * (x * hC.d) * x := by group
        _ = hC.d * (hC.d * x) * x := by rw [hx.2.1.eq]
        _ = hC.d * hC.d * (x * x) := by group
        _ = 1 := by rw [hu2, hx2, one_mul]
    have h1' := eq_one_of_mem_pResidualOf_of_commute hC h3 (mul_mem_of_mem_commSet hC h3 hx)
      hlc hl2
    exact hx.2.2 (by rw [eq_inv_of_mul_eq_one_right h1', hC.setup.oddT.inv_eq hC.hd])

private theorem eq_of_bar_eq (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {x y : G}
    (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : bar hC x = bar hC y) : x = y := by
  have hxH := mem_Halpha_of_mem_commSet hC h3 hx
  have hyH := mem_Halpha_of_mem_commSet hC h3 hy
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hx.1
  have hy2 : y * y = 1 := hC.setup.oddT.mul_self_eq_one hy.1
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hzc := (bar_eq_one_iff hC (Subgroup.mul_mem _ hxH hyH)).mp (by
    rw [bar_mul hC hxH hyH, ← hxy, ← bar_mul hC hxH hxH, hx2, bar_one])
  have hux : hC.d * x * (hC.d * y) = x * y := by
    calc hC.d * x * (hC.d * y) = hC.d * (x * hC.d) * y := by group
      _ = hC.d * (hC.d * x) * y := by rw [hx.2.1.eq]
      _ = x * y := by rw [← mul_assoc, hu2, one_mul]
  have hzL : x * y ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    rw [← hux]
    exact Subgroup.mul_mem _ (mul_mem_of_mem_commSet hC h3 hx) (mul_mem_of_mem_commSet hC h3 hy)
  have hcomm : x * y = y * x := by
    have h := (hzc x hxH).eq
    calc x * y = x * y * x * x := by rw [mul_assoc (x * y), hx2, mul_one]
      _ = x * (x * y) * x := by rw [h]
      _ = y * x := by rw [← mul_assoc, hx2, one_mul]
  have hz2 : x * y * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm]
      _ = 1 := by rw [← mul_assoc, hx2, one_mul, hy2]
  have hz := eq_one_of_mem_pResidualOf_of_commute hC h3 hzL hzc hz2
  calc x = x * (x * y) := by rw [hz, mul_one]
    _ = y := by rw [← mul_assoc, hx2, one_mul]

private theorem exists_bar_eq (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    {t : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)} (ht : orderOf t = 2) :
    ∃ x ∈ commSet D hC.d, bar hC x = t := by
  have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
    Subgroup.map_subtype_le _
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  obtain ⟨l, hlL, hl⟩ : ∃ l ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), bar hC l = t := by
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective t
    rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hh with hL | hL
    · exact ⟨h, hL, bar_of_mem hC hh⟩
    · refine ⟨hC.d * h, hL, ?_⟩
      rw [bar_mul hC (d_mem_Halpha hC h3) hh, bar_d hC h3, one_mul, bar_of_mem hC hh]
  have hlH := hLH hlL
  have hzc := (bar_eq_one_iff hC (Subgroup.mul_mem _ hlH hlH)).mp (by
    rw [bar_mul hC hlH hlH, hl, ← pow_two, ht2])
  have hzL := Subgroup.mul_mem _ hlL hlL
  obtain ⟨k, hk⟩ : ∃ k, orderOf (l * l) = k := ⟨_, rfl⟩
  have hkodd : Odd k := by
    rcases Nat.even_or_odd k with ⟨k', hk'⟩ | hodd
    · exfalso
      have hk0 : 0 < k := hk ▸ orderOf_pos _
      have hz' : (l * l) ^ k' = 1 := by
        refine eq_one_of_mem_pResidualOf_of_commute hC h3 (Subgroup.pow_mem _ hzL _)
          (fun h hh => (hzc h hh).pow_left k') ?_
        rw [← pow_add, ← hk', ← hk, pow_orderOf_eq_one]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega) hz'
    · exact hodd
  obtain ⟨r, hr⟩ := hkodd
  have hbar : bar hC (l ^ k) = t := by
    rw [bar_pow hC hlH, hl, hr, pow_succ, pow_mul, ht2, one_pow, one_mul]
  have ht'2 : l ^ k * l ^ k = 1 := by
    rw [← (Commute.refl l).mul_pow, ← hk, pow_orderOf_eq_one]
  have ht'1 : l ^ k ≠ 1 := fun h => by
    rw [h, bar_one] at hbar
    rw [← hbar, orderOf_one] at ht
    exact absurd ht (by decide)
  have hord : orderOf (l ^ k) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht'2) ht'1
  refine ⟨hC.d * l ^ k, mul_mem_commSet_of_orderOf_eq_two hC hH h3
    (Subgroup.pow_mem _ hlL k) hord, ?_⟩
  rw [bar_mul hC (d_mem_Halpha hC h3) (Subgroup.pow_mem _ hlH k), bar_d hC h3, one_mul, hbar]

private theorem commute_of_commute_bar (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {x y : G}
    (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d)
    (hxy : Commute (bar hC x) (bar hC y)) : Commute x y := by
  have hxH := mem_Halpha_of_mem_commSet hC h3 hx
  have hyH := mem_Halpha_of_mem_commSet hC h3 hy
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one hx.1
  have hy2 : y * y = 1 := hC.setup.oddT.mul_self_eq_one hy.1
  by_contra hne
  have hodd : Odd (orderOf (x * y)) := hC.setup.oddT.odd_of_not_commute hx.1 hy.1 hne
  have h2 : bar hC (x * y) ^ 2 = 1 := by
    rw [bar_mul hC hxH hyH, hxy.mul_pow, ← bar_pow hC hxH, ← bar_pow hC hyH, pow_two, pow_two,
      hx2, hy2, bar_one, one_mul]
  have h1 : bar hC (x * y) ^ orderOf (x * y) = 1 := by
    rw [← bar_pow hC (Subgroup.mul_mem _ hxH hyH), pow_orderOf_eq_one, bar_one]
  have hb1 : bar hC (x * y) = 1 := by
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [(Nat.coprime_two_left.mpr hodd).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hc := ((bar_eq_one_iff hC (Subgroup.mul_mem _ hxH hyH)).mp hb1 x hxH).eq
  apply hne
  have hy' : y = x * y * x := by rw [hc, ← mul_assoc, hx2, one_mul]
  calc x * y = x * (x * y * x) := by rw [← hy']
    _ = y * x := by rw [← mul_assoc, ← mul_assoc, hx2, one_mul]

private theorem ncard_commSet_d (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e) :
    (commSet D hC.d).ncard = (2 ^ n - 1) * ((2 ^ n) ^ i + 1) := by
  rw [← hB.ncard_involutions]
  refine Set.ncard_congr (fun x _ => bar hC x) (fun x hx => orderOf_bar hC h3 hx)
    (fun x y hx hy hxy => eq_of_bar_eq hC h3 hx hy hxy) fun t ht => ?_
  obtain ⟨x, hx, rfl⟩ := exists_bar_eq hC hH h3 ht
  exact ⟨x, hx, rfl⟩

private theorem ncard_commute (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e) {v : G}
    (hv : v ∈ commSet D hC.d) : {x | x ∈ commSet D hC.d ∧ Commute x v}.ncard = 2 ^ n - 1 := by
  rw [← hB.ncard_commuting_involutions (orderOf_bar hC h3 hv)]
  refine Set.ncard_congr (fun x _ => bar hC x) (fun x hx => ⟨orderOf_bar hC h3 hx.1, ?_⟩)
    (fun x y hx hy hxy => eq_of_bar_eq hC h3 hx.1 hy.1 hxy) fun t ht => ?_
  · exact (commute_bar hC (mem_Halpha_of_mem_commSet hC h3 hv)
      (mem_Halpha_of_mem_commSet hC h3 hx.1) hx.2.symm).eq
  · obtain ⟨x, hx, rfl⟩ := exists_bar_eq hC hH h3 ht.1
    exact ⟨x, ⟨hx, (commute_of_commute_bar hC h3 hv hx ht.2).symm⟩, rfl⟩

theorem exists_ncard_commSet_eq
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) :
    ∃ m j : ℕ, 2 ≤ m ∧ 1 ≤ j ∧ (commSet D hC.d).ncard = ((2 ^ m) ^ j + 1) * (2 ^ m - 1) ∧
      ∀ v ∈ commSet D hC.d,
        ({e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e v}).ncard = 2 ^ m := by
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  have hn : 2 ≤ n ∧ 1 ≤ i := by
    rcases hB.cases' with ⟨rfl, -, hn⟩ | ⟨rfl, -, a, ha, rfl⟩ | ⟨rfl, -, hn⟩ <;> omega
  refine ⟨n, i, hn.1, hn.2, by rw [ncard_commSet_d hC hH h3 hB, mul_comm], fun v hv => ?_⟩
  have hset : {e | e ∈ D ∧ Commute e hC.d} ∩ {e | e ∈ D ∧ Commute e v} =
      insert hC.d {x | x ∈ commSet D hC.d ∧ Commute x v} := by
    ext x
    constructor
    · rintro ⟨⟨hxD, hxu⟩, -, hxv⟩
      by_cases hx : x = hC.d
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hxD, hxu, hx⟩, hxv⟩
    · rintro (rfl | ⟨⟨hxD, hxu, -⟩, hxv⟩)
      · exact ⟨⟨hC.hd, Commute.refl _⟩, hC.hd, hv.2.1.symm⟩
      · exact ⟨⟨hxD, hxu⟩, hxD, hxv⟩
  rw [hset, Set.ncard_insert_of_notMem (fun h => h.1.2.2 rfl), ncard_commute hC hH h3 hB hv]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

omit [Finite G] in
private theorem conj_mem_commSet (hC : HypothesisC D) {p p' x : G} (g : G)
    (hp : g * p * g⁻¹ = p') (hx : x ∈ commSet D p) : g * x * g⁻¹ ∈ commSet D p' := by
  obtain ⟨hxD, hxp, hxne⟩ := hx
  refine ⟨hC.setup.conj_mem g hxD, ?_, fun h => hxne ?_⟩
  · rw [← hp]
    exact (Commute.conj_iff g).mpr hxp
  · rw [← hp] at h
    exact mul_left_cancel (mul_right_cancel h)

omit [Finite G] in
private theorem conj_mem_closure_commSet (hC : HypothesisC D) {p p' y : G} (g : G)
    (hp : g * p * g⁻¹ = p') (hy : y ∈ Subgroup.closure (commSet D p)) :
    g * y * g⁻¹ ∈ Subgroup.closure (commSet D p') := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (conj_mem_commSet hC g hp hx)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

omit [Finite G] in
private theorem conj_mem_centralizer_closure_commSet (hC : HypothesisC D) {p p' x : G} (g : G)
    (hp : g * p * g⁻¹ = p')
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (Subgroup.closure (commSet D p') : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hp' : g⁻¹ * p' * g⁻¹⁻¹ = p := by rw [← hp]; group
  have h := Subgroup.mem_centralizer_iff.mp hx _ (conj_mem_closure_commSet hC g⁻¹ hp' hy)
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * y := by group

private theorem self_mem_closure_commSet (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {p : G}
    (hp : p ∈ D) : p ∈ Subgroup.closure (commSet D p) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hp)
  have hu := d_mem_Halpha hC h3
  rw [Halpha_eq_closure hC h3] at hu
  have h := conj_mem_closure_commSet hC g hg hu
  rwa [hg] at h

private theorem commute_of_mem_centralizer_closure (hC : HypothesisC D)
    (h3 : Conclusion9_3 D hC) {p x e : G} (hp : p ∈ D)
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G)) (he : e ∈ D)
    (hep : Commute e p) : Commute x e := by
  have heC : e ∈ Subgroup.closure (commSet D p) := by
    by_cases h : e = p
    · rw [h]
      exact self_mem_closure_commSet hC h3 hp
    · exact Subgroup.subset_closure ⟨he, hep, h⟩
  exact (Subgroup.mem_centralizer_iff.mp hx e heC).symm

theorem eq_one_of_mem_centralizer_closure_commSet (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {v w : G} (hv : v ∈ D) (hw : w ∈ D) (hvw : v ≠ w)
    (hc : Commute v w) {x : G}
    (hxv : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G))
    (hxw : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D w) : Set G)) : x = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv)
  have hg' : g⁻¹ * v * g⁻¹⁻¹ = hC.d := by rw [← hg]; group
  have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ commSet D hC.d :=
    conj_mem_commSet hC g⁻¹ hg' ⟨hw, hc.symm, fun h => hvw h.symm⟩
  have hxu := conj_mem_centralizer_closure_commSet hC g⁻¹ hg' hxv
  have hxw' := conj_mem_centralizer_closure_commSet hC g⁻¹ rfl hxw
  have h1 : g⁻¹ * x * g⁻¹⁻¹ = 1 := by
    refine eq_one_of_commute_centSet hC hH (by rw [h3.1]; rintro a rfl b rfl; rfl)
      ((DalphaStar_eq_commSet hC h3.1).symm ▸ hw') (fun e he heu => ?_) fun e he hew => ?_
    · exact commute_of_mem_centralizer_closure hC h3 hC.hd hxu he heu
    · exact commute_of_mem_centralizer_closure hC h3 hw'.1 hxw' he hew
  calc x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem commute_of_mem_centralizer_closure_commSet (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {v w : G} (hv : v ∈ D) (hw : w ∈ D) (hvw : v ≠ w)
    (hc : Commute v w) {x y : G}
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G))
    (hy : y ∈ Subgroup.centralizer (Subgroup.closure (commSet D w) : Set G)) : Commute x y := by
  have hyv : y * v * y⁻¹ = v := by
    rw [(commute_of_mem_centralizer_closure hC h3 hw hy hv hc).eq, mul_inv_cancel_right]
  have hxw : x * w * x⁻¹ = w := by
    rw [(commute_of_mem_centralizer_closure hC h3 hv hx hw hc.symm).eq, mul_inv_cancel_right]
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G) := by
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact Subgroup.mul_mem _ hx
      (conj_mem_centralizer_closure_commSet hC y hyv (Subgroup.inv_mem _ hx))
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Subgroup.closure (commSet D w) : Set G) :=
    Subgroup.mul_mem _ (conj_mem_centralizer_closure_commSet hC x hxw hy) (Subgroup.inv_mem _ hy)
  have h := eq_one_of_mem_centralizer_closure_commSet hC hH h3 hv hw hvw hc h1 h2
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h, one_mul]

private theorem centralizer_d_le_normalizer (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) :
    Subgroup.centralizer ({hC.d} : Set G) ≤ Subgroup.normalizer (Halpha D hC.alpha : Set G) := by
  intro g hg
  have hgu : g * hC.d * g⁻¹ = hC.d := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hgu' : g⁻¹ * hC.d * g⁻¹⁻¹ = hC.d := by
    calc g⁻¹ * hC.d * g⁻¹⁻¹ = g⁻¹ * (g * hC.d * g⁻¹) * g⁻¹⁻¹ := by rw [hgu]
      _ = hC.d := by group
  refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
  rw [Halpha_eq_closure hC h3]
  refine ⟨conj_mem_closure_commSet hC g hgu, fun hh => ?_⟩
  have h' := conj_mem_closure_commSet hC g⁻¹ hgu' hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h'

private noncomputable def act (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) :
    Subgroup.centralizer ({hC.d} : Set G) →*
      MulAut (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
  (MulAut.mapQuotient (Subgroup.center (Halpha D hC.alpha))).comp
    ((Subgroup.normalizerMonoidHom (Halpha D hC.alpha)).comp
      (Subgroup.inclusion (centralizer_d_le_normalizer hC h3)))

private theorem act_bar (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    (g : Subgroup.centralizer ({hC.d} : Set G)) {x : G} (hx : x ∈ Halpha D hC.alpha) :
    act hC h3 g (bar hC x) = bar hC (g * x * (g : G)⁻¹) := by
  have hgx : (g : G) * x * (g : G)⁻¹ ∈ Halpha D hC.alpha :=
    (Subgroup.mem_normalizer_iff.mp (centralizer_d_le_normalizer hC h3 g.2) x).mp hx
  rw [bar_of_mem hC hx, bar_of_mem hC hgx]
  exact MulAut.mapQuotient_mk _ _ _

private theorem act_eq_conj (hC : HypothesisC D) (h3 : Conclusion9_3 D hC) {c : G}
    (hc : c ∈ Halpha D hC.alpha) (hcu : c ∈ Subgroup.centralizer ({hC.d} : Set G)) :
    act hC h3 ⟨c, hcu⟩ = MulAut.conj (bar hC c) := by
  ext t
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective t
  rw [← bar_of_mem hC hx, act_bar hC h3 _ hx]
  show bar hC (c * x * c⁻¹) = MulAut.conj (bar hC c) (bar hC x)
  rw [MulAut.conj_apply, bar_mul hC (Subgroup.mul_mem _ hc hx) (Subgroup.inv_mem _ hc),
    bar_mul hC hc hx, bar_inv hC hc]

omit [Finite G] in
private theorem mem_centralizer_d (hC : HypothesisC D) {v x : G} (hv : v ∈ commSet D hC.d)
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G)) :
    x ∈ Subgroup.centralizer ({hC.d} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx _
    (Subgroup.subset_closure ⟨hC.hd, hv.2.1.symm, fun h => hv.2.2 h.symm⟩)).symm

private theorem act_mem_autCentralizer (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e)
    (S : Sylow 2 (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) {p : G}
    (hp : p ∈ commSet D hC.d) (hpS : bar hC p ∈ (S : Subgroup _)) {x : G}
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G))
    (hxu : x ∈ Subgroup.centralizer ({hC.d} : Set G)) :
    act hC h3 ⟨x, hxu⟩ ∈ autCentralizer (rootCenter (S : Subgroup _)) := by
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  refine mem_autCentralizer_iff.mpr fun z hz => ?_
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  · have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc.center_sq z hz) hz1
    obtain ⟨y, hy, rfl⟩ := exists_bar_eq hC hH h3 hz2
    have hyp : Commute y p :=
      (commute_of_commute_bar hC h3 hp hy ((mem_rootCenter_iff.mp hz).2 _ hpS)).symm
    have hxy := commute_of_mem_centralizer_closure hC h3 hp.1 hx hy.1 hyp
    rw [act_bar hC h3 _ (mem_Halpha_of_mem_commSet hC h3 hy)]
    congr 1
    show x * y * x⁻¹ = y
    rw [hxy.eq, mul_inv_cancel_right]

private theorem mem_centralizer_Halpha_of_act_eq_one (hC : HypothesisC D)
    (h3 : Conclusion9_3 D hC) {g : G} (hgu : g ∈ Subgroup.centralizer ({hC.d} : Set G))
    (hg : act hC h3 ⟨g, hgu⟩ = 1) : g ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
  rw [Halpha_eq_closure hC h3, Subgroup.centralizer_closure]
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have h1 := congrArg (fun φ : MulAut _ => φ (bar hC y)) hg
  simp only [MulAut.one_apply] at h1
  rw [act_bar hC h3 _ (mem_Halpha_of_mem_commSet hC h3 hy)] at h1
  have hgu' : g * hC.d * g⁻¹ = hC.d := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgu, mul_inv_cancel_right]
  have hxy := eq_of_bar_eq hC h3 (conj_mem_commSet hC g hgu' hy) hy h1
  calc y * g = g * y * g⁻¹ * g := by rw [hxy]
    _ = g * y := by group

private theorem card_dvd_ncard_of_conj {F : Subgroup G} {X : Set G}
    (hX : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ ∈ X)
    (hfree : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ = x → f = 1) : Nat.card F ∣ X.ncard := by
  classical
  let _ : MulAction F X :=
    { smul := fun f x => ⟨f * x * (f : G)⁻¹, hX f f.2 x x.2⟩
      one_smul := fun x => Subtype.ext (show ((1 : F) : G) * x * ((1 : F) : G)⁻¹ = x by simp)
      mul_smul := fun f g x => Subtype.ext (show ((f * g : F) : G) * x * ((f * g : F) : G)⁻¹ =
          f * (g * x * (g : G)⁻¹) * (f : G)⁻¹ by simp only [Subgroup.coe_mul]; group) }
  have := Fintype.ofFinite F
  have := Fintype.ofFinite X
  have hsum : ∑ f : F, Fintype.card (MulAction.fixedBy X f) = Fintype.card X := by
    rw [Finset.sum_eq_single (1 : F)]
    · exact Fintype.card_congr
        (Equiv.subtypeUnivEquiv fun x => MulAction.mem_fixedBy.mpr (one_smul F x))
    · intro f _ hf
      refine Fintype.card_eq_zero_iff.mpr ⟨fun x => hf (Subtype.ext ?_)⟩
      exact hfree f f.2 x.1.1 x.1.2 (congrArg Subtype.val (MulAction.mem_fixedBy.mp x.2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group F X
  rw [hsum] at hB
  simp only [← Nat.card_eq_fintype_card] at hB
  rw [← Nat.card_coe_set_eq, hB]
  exact Dvd.intro_left _ rfl

private theorem eq_one_of_conj_eq_of_not_commute (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {p : G} (hp : p ∈ D) {x : G}
    (hx : x ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G)) {w : G}
    (hw : w ∈ D) (hwp : ¬ Commute w p) (hxw : x * w * x⁻¹ = w) : x = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hp)
  have hg' : g⁻¹ * p * g⁻¹⁻¹ = hC.d := by rw [← hg]; group
  have hx' := conj_mem_centralizer_closure_commSet hC g⁻¹ hg' hx
  rw [← Halpha_eq_closure hC h3] at hx'
  have hw'u : ¬ Commute (g⁻¹ * w * g⁻¹⁻¹) hC.d := by
    rw [← hg', Commute.conj_iff]
    exact hwp
  have hxw' : g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) * (g⁻¹ * x * g⁻¹⁻¹)⁻¹ = g⁻¹ * w * g⁻¹⁻¹ := by
    calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * w * g⁻¹⁻¹) * (g⁻¹ * x * g⁻¹⁻¹)⁻¹ =
        g⁻¹ * (x * w * x⁻¹) * g⁻¹⁻¹ := by group
      _ = g⁻¹ * w * g⁻¹⁻¹ := by rw [hxw]
  have h1 := eq_one_of_mem_centralizer_Halpha_of_conj_eq hC hH h3 hx' (hC.setup.conj_mem g⁻¹ hw)
    hw'u hxw'
  calc x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

private theorem act_comp_inclusion_injective (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {v : G} (hv : v ∈ commSet D hC.d)
    (hFu : Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G) ≤
      Subgroup.centralizer ({hC.d} : Set G)) :
    Function.Injective ((act hC h3).comp (Subgroup.inclusion hFu)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxE := mem_centralizer_Halpha_of_act_eq_one hC h3 (hFu x.2) hx
  rw [Halpha_eq_closure hC h3] at hxE
  exact Subtype.ext (eq_one_of_mem_centralizer_closure_commSet hC hH h3 hC.hd hv.1
    (fun h => hv.2.2 h.symm) hv.2.1.symm hxE x.2)

private theorem card_centralizer_closure_dvd_card_autCentralizer
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e) {v : G}
    (hv : v ∈ commSet D hC.d) :
    Nat.card (Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G)) ∣
      (2 ^ n) ^ i * (if i = 3 then 2 * (2 ^ n + 1) else 1) := by
  have hFu : Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G) ≤
      Subgroup.centralizer ({hC.d} : Set G) := fun x hx => mem_centralizer_d hC hv hx
  obtain ⟨S, hS⟩ := Sec128B.exists_sylow_mem_of_orderOf_eq_two (orderOf_bar hC h3 hv)
  rw [← hB.card_autCentralizer_rootCenter S,
    Nat.card_congr (MonoidHom.ofInjective (act_comp_inclusion_injective hC hH h3 hv hFu)).toEquiv]
  refine Subgroup.card_dvd_of_le ?_
  rintro _ ⟨x, rfl⟩
  exact act_mem_autCentralizer hC hH h3 hB S hv hS x.2 (hFu x.2)

private theorem card_centralizer_closure_dvd_ncard
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e) {v : G}
    (hv : v ∈ commSet D hC.d) :
    Nat.card (Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G)) ∣
      (2 ^ n) ^ i * (2 ^ n - 1) := by
  have hXcard : {x | x ∈ commSet D hC.d ∧ ¬ Commute x v}.ncard = (2 ^ n) ^ i * (2 ^ n - 1) := by
    have hsub : {x | x ∈ commSet D hC.d ∧ Commute x v} ⊆ commSet D hC.d := fun x hx => hx.1
    have hXeq : {x | x ∈ commSet D hC.d ∧ ¬ Commute x v} =
        commSet D hC.d \ {x | x ∈ commSet D hC.d ∧ Commute x v} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff]
      tauto
    have h := Set.ncard_sdiff_add_ncard_of_subset hsub
    rw [← hXeq, ncard_commSet_d hC hH h3 hB, ncard_commute hC hH h3 hB hv,
      show (2 ^ n - 1) * ((2 ^ n) ^ i + 1) = (2 ^ n) ^ i * (2 ^ n - 1) + (2 ^ n - 1) by ring] at h
    exact Nat.add_right_cancel h
  rw [← hXcard]
  refine card_dvd_ncard_of_conj (fun f hf x hx => ⟨conj_mem_commSet hC f ?_ hx.1,
    fun h => hx.2 ?_⟩) fun f hf x hx hfx =>
      eq_one_of_conj_eq_of_not_commute hC hH h3 hv.1 hf hx.1.1 hx.2 hfx
  · rw [Subgroup.mem_centralizer_singleton_iff.mp (mem_centralizer_d hC hv hf),
      mul_inv_cancel_right]
  · have hfv : f * v * f⁻¹ = v := by
      rw [(commute_of_mem_centralizer_closure hC h3 hv.1 hf hv.1 (Commute.refl v)).eq,
        mul_inv_cancel_right]
    rw [← hfv] at h
    exact (Commute.conj_iff f).mp h

private theorem coprime_ite_two_pow_sub_one {n i : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (if i = 3 then 2 * (2 ^ n + 1) else 1) (2 ^ n - 1) := by
  split_ifs
  · have hn1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : Nat.Coprime 2 (2 ^ n - 1) := Nat.coprime_two_left.mpr
      (Nat.Even.sub_odd hn1 (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one)
    have h3 : Nat.Coprime (2 ^ n + 1) (2 ^ n - 1) := by
      rw [show 2 ^ n + 1 = 2 + (2 ^ n - 1) by omega]
      exact Nat.coprime_add_self_left.mpr h2
    exact Nat.Coprime.mul_left h2 h3
  · exact Nat.coprime_one_left _

private theorem isPGroup_two_centralizer_closure_commSet
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {v : G}
    (hv : v ∈ commSet D hC.d) :
    IsPGroup 2 (Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G)) := by
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  have hn : 1 ≤ n := by
    rcases hB.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, rfl⟩ | ⟨-, -, hn⟩ <;> omega
  refine IsPGroup.of_card_dvd_pow (n := n * i) ?_
  have h := Nat.dvd_gcd (card_centralizer_closure_dvd_card_autCentralizer hC hH h3 hB hv)
    (card_centralizer_closure_dvd_ncard hC hH h3 hB hv)
  rwa [Nat.gcd_mul_left, (coprime_ite_two_pow_sub_one hn).gcd_eq_one, mul_one, ← pow_mul] at h

theorem isPGroup_two_centralizer_Halpha (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) :
    IsPGroup 2 (Subgroup.centralizer (Halpha D hC.alpha : Set G)) := by
  obtain ⟨v, hv, -⟩ := hC.hE
  have hFp := isPGroup_two_centralizer_closure_commSet hC hH h3 hv
  intro x
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv.1)
  have hx : (x : G) ∈ Subgroup.centralizer (Subgroup.closure (commSet D hC.d) : Set G) := by
    rw [← Halpha_eq_closure hC h3]
    exact x.2
  obtain ⟨k, hk⟩ := hFp ⟨g * x * g⁻¹, conj_mem_centralizer_closure_commSet hC g hg hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hk' : (g * x * g⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [conj_pow] at hk'
  simpa using hk'

theorem eq_one_or_eq_d_of_mul_self_eq_one (h87 : Theorem8_7)
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {f : G}
    (hf : f ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) (hf2 : f * f = 1) :
    f = 1 ∨ f = hC.d := by
  by_contra h
  obtain ⟨hf1, hfu⟩ := not_or.mp h
  obtain ⟨m, j, hm, hj, hk, hlam⟩ := exists_ncard_commSet_eq hC hH h3
  exact false_of_commSet_inter_subsingleton h87 hC h3.1 hH.solv rfl hm rfl hj hk hlam
    (subsingleton_commSet_inter_of_involution hC hH h3 hf hf2 hf1 hfu)

private theorem conj_injective_of_center_eq_bot {K : Type} [Group K]
    (h : Subgroup.center K = ⊥) : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun x => by
    have hx := congrArg (fun φ : MulAut K => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  rw [h, Subgroup.mem_bot] at hgZ
  exact hgZ

private theorem exists_mem_centralizer_closure_mul_self_eq (hC : HypothesisC D)
    (h3 : Conclusion9_3 D hC) {f : G} (hf : f ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G))
    (hff : f * f = hC.d) {p : G} (hp : p ∈ D) :
    ∃ fp ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G), fp * fp = p := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hp)
  rw [Halpha_eq_closure hC h3] at hf
  refine ⟨g * f * g⁻¹, conj_mem_centralizer_closure_commSet hC g hg hf, ?_⟩
  rw [← hg, ← hff]
  group

private theorem exists_mem_sylow_act_eq_conj (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e)
    (S : Sylow 2 (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) {p : G}
    (hp : p ∈ commSet D hC.d) (hpS : bar hC p ∈ (S : Subgroup _)) {fp : G}
    (hfp : fp ∈ Subgroup.centralizer (Subgroup.closure (commSet D p) : Set G))
    (hfp2 : fp * fp = p) : ∃ s ∈ (S : Subgroup _),
      act hC h3 ⟨fp, mem_centralizer_d hC hp hfp⟩ = MulAut.conj s ∧ s ^ 2 = bar hC p := by
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hpH := mem_Halpha_of_mem_commSet hC h3 hp
  have hpu : p ∈ Subgroup.centralizer ({hC.d} : Set G) := PartThree.Halpha_le_centralizer_d hC hpH
  have hp1 : bar hC p ≠ 1 := fun h => by
    have h2 := orderOf_bar hC h3 hp
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hsq : act hC h3 ⟨fp, mem_centralizer_d hC hp hfp⟩ ^ 2 = MulAut.conj (bar hC p) := by
    rw [← map_pow, pow_two, ← act_eq_conj hC h3 hpH hpu]
    exact congrArg _ (Subtype.ext hfp2)
  obtain ⟨s, hs, hseq⟩ := hB.exists_mem_eq_conj_of_sq_eq_conj S
    (act_mem_autCentralizer hC hH h3 hB S hp hpS hfp (mem_centralizer_d hC hp hfp))
    (hc.center_of_involution _ (le_borel _ hpS) (orderOf_bar hC h3 hp)) hp1 hsq
  refine ⟨s, hs, hseq, conj_injective_of_center_eq_bot hB.center_eq_bot ?_⟩
  rw [map_pow, ← hseq, hsq]

private theorem orderOf_eq_four_of_sq_eq_bar (hC : HypothesisC D) (h3 : Conclusion9_3 D hC)
    {s : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)} {p : G}
    (hp : p ∈ commSet D hC.d) (hsp : s ^ 2 = bar hC p) : orderOf s = 4 := by
  have h2 := orderOf_bar hC h3 hp
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, hsp]
    intro h
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hsp, ← h2, pow_orderOf_eq_one]

private theorem commute_conj_of_act_eq_conj (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {n i e : ℕ}
    (hB : BenderType (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) n i e)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ commSet D hC.d) (hwne : w ≠ v)
    (hwv : Commute w v) {fv fw : G}
    (hfv : fv ∈ Subgroup.centralizer (Subgroup.closure (commSet D v) : Set G))
    (hfw : fw ∈ Subgroup.centralizer (Subgroup.closure (commSet D w) : Set G))
    {sv sw : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)}
    (hsv : act hC h3 ⟨fv, mem_centralizer_d hC hv hfv⟩ = MulAut.conj sv)
    (hsw : act hC h3 ⟨fw, mem_centralizer_d hC hw hfw⟩ = MulAut.conj sw) {c : G}
    (hcH : c ∈ Halpha D hC.alpha) (hcv : Commute (bar hC c) (bar hC v)) :
    Commute (bar hC c * sv * (bar hC c)⁻¹) sw := by
  have hvH := mem_Halpha_of_mem_commSet hC h3 hv
  have hcu : c ∈ Subgroup.centralizer ({hC.d} : Set G) := PartThree.Halpha_le_centralizer_d hC hcH
  have hcv' : c * v * c⁻¹ = v := by
    have hcuu : c * hC.d * c⁻¹ = hC.d := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hcu, mul_inv_cancel_right]
    refine eq_of_bar_eq hC h3 (conj_mem_commSet hC c hcuu hv) hv ?_
    rw [bar_mul hC (Subgroup.mul_mem _ hcH hvH) (Subgroup.inv_mem _ hcH), bar_mul hC hcH hvH,
      bar_inv hC hcH, hcv.eq, mul_inv_cancel_right]
  have hcomm := commute_of_mem_centralizer_closure_commSet hC hH h3 hv.1 hw.1
    (fun h => hwne h.symm) hwv.symm (conj_mem_centralizer_closure_commSet hC c hcv' hfv) hfw
  have hkey : Commute (MulAut.conj (bar hC c * sv * (bar hC c)⁻¹)) (MulAut.conj sw) := by
    have h := (show Commute (⟨c, hcu⟩ * ⟨fv, mem_centralizer_d hC hv hfv⟩ * ⟨c, hcu⟩⁻¹ :
        Subgroup.centralizer ({hC.d} : Set G)) ⟨fw, mem_centralizer_d hC hw hfw⟩ from
      Subtype.ext hcomm).map (act hC h3)
    rw [map_mul, map_mul, map_inv, act_eq_conj hC h3 hcH hcu, hsv, hsw] at h
    rw [map_mul, map_mul, map_inv]
    exact h
  have h := hkey.eq
  rw [← map_mul, ← map_mul] at h
  exact conj_injective_of_center_eq_bot hB.center_eq_bot h

theorem mul_self_ne_d_of_mem_centralizer_Halpha
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) {f : G}
    (hf : f ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) : f * f ≠ hC.d := by
  intro hff
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  have hn : 2 ≤ n := by
    rcases hB.cases' with ⟨-, -, hn⟩ | ⟨-, -, a, ha, rfl⟩ | ⟨-, -, hn⟩ <;> omega
  obtain ⟨v, hv, -⟩ := hC.hE
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨w, ⟨hw, hwv⟩, hwne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := {x | x ∈ commSet D hC.d ∧ Commute x v})
    (by rw [ncard_commute hC hH h3 hB hv]; omega) v
  obtain ⟨S, hS⟩ := Sec128B.exists_sylow_mem_of_orderOf_eq_two (orderOf_bar hC h3 hv)
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hwS : bar hC w ∈ (S : Subgroup _) :=
    (mem_rootCenter_iff.mp (Sec128B.mem_rootCenter_of_commute hc (orderOf_bar hC h3 hv)
      (le_borel _ hS) (orderOf_bar hC h3 hw) (commute_bar hC (mem_Halpha_of_mem_commSet hC h3 hv)
        (mem_Halpha_of_mem_commSet hC h3 hw) hwv.symm).eq).1).1
  obtain ⟨fv, hfv, hfv2⟩ := exists_mem_centralizer_closure_mul_self_eq hC h3 hf hff hv.1
  obtain ⟨fw, hfw, hfw2⟩ := exists_mem_centralizer_closure_mul_self_eq hC h3 hf hff hw.1
  obtain ⟨sv, hsvS, hsv, hsv2⟩ := exists_mem_sylow_act_eq_conj hC hH h3 hB S hv hS hfv hfv2
  obtain ⟨sw, hswS, hsw, hsw2⟩ := exists_mem_sylow_act_eq_conj hC hH h3 hB S hw hwS hfw hfw2
  obtain ⟨cb, hcb, hncomm⟩ := hB.exists_conj_not_commute_of_sq_ne S hsvS hswS
    (orderOf_eq_four_of_sq_eq_bar hC h3 hv hsv2) (orderOf_eq_four_of_sq_eq_bar hC h3 hw hsw2)
    (by rw [hsv2, hsw2]; exact fun h => hwne (eq_of_bar_eq hC h3 hw hv h.symm))
  obtain ⟨⟨c, hcH⟩, rfl⟩ := QuotientGroup.mk_surjective cb
  rw [← bar_of_mem hC hcH] at hcb hncomm
  refine hncomm (commute_conj_of_act_eq_conj hC hH h3 hB hv hw hwne hwv hfv hfw hsv hsw hcH ?_)
  rw [← hsv2]
  exact Subgroup.mem_centralizer_singleton_iff.mp hcb

theorem centralizer_Halpha_eq_zpowers (h87 : Theorem8_7)
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) :
    Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d := by
  have hp := isPGroup_two_centralizer_Halpha hC hH h3
  refine le_antisymm (fun x hx => ?_) ?_
  · by_contra hxu
    obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
    rcases m with _ | m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact hxu (hm ▸ Subgroup.one_mem _)
    have hy2 : x ^ 2 ^ m * x ^ 2 ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hm, pow_orderOf_eq_one]
    have hy1 : x ^ 2 ^ m ≠ 1 := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      refine pow_ne_one_of_lt_orderOf (by omega) ?_
      rw [hm, pow_succ]
      omega
    rcases eq_one_or_eq_d_of_mul_self_eq_one h87 hC hH h3 (Subgroup.pow_mem _ hx _) hy2 with
      h | h
    · exact hy1 h
    rcases m with _ | m
    · rw [pow_zero, pow_one] at h
      exact hxu (h ▸ Subgroup.mem_zpowers _)
    apply mul_self_ne_d_of_mem_centralizer_Halpha hC hH h3 (Subgroup.pow_mem _ hx (2 ^ m))
    rw [← h, ← pow_add, ← two_mul, ← pow_succ']
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hh)

private theorem bar_mem_sylow_map (hC : HypothesisC D) (T : Sylow 2 (Halpha D hC.alpha)) {x : G}
    (hx : x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    bar hC x ∈ (T.mapSurjective (QuotientGroup.mk'_surjective
      (Subgroup.center (Halpha D hC.alpha))) : Subgroup _) := by
  obtain ⟨y, hy, rfl⟩ := hx
  show bar hC (y : G) ∈ _
  rw [bar_of_mem hC y.2, Sylow.coe_mapSurjective]
  exact Subgroup.mem_map_of_mem _ hy

private theorem mem_sylow_map_of_bar_mem (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (T : Sylow 2 (Halpha D hC.alpha)) {x : G}
    (hx : x ∈ commSet D hC.d) (hxT : bar hC x ∈ (T.mapSurjective (QuotientGroup.mk'_surjective
      (Subgroup.center (Halpha D hC.alpha))) : Subgroup _)) :
    x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  have hxH := mem_Halpha_of_mem_commSet hC h3 hx
  rw [bar_of_mem hC hxH, Sylow.coe_mapSurjective] at hxT
  have hmem : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈
      (T : Subgroup (Halpha D hC.alpha)) ⊔ Subgroup.center (Halpha D hC.alpha) := by
    have h : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈
        ((T : Subgroup (Halpha D hC.alpha)).map
          (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha)))).comap
          (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))) := hxT
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h
  have h2 : (⟨x, hxH⟩ : Halpha D hC.alpha) * ⟨x, hxH⟩ = 1 :=
    Subtype.ext (hC.setup.oddT.mul_self_eq_one hx.1)
  exact ⟨_, mem_sylow_of_mem_sup_center (oddCore_le_center_of_isBenderGroup hH.bender) T hmem h2,
    rfl⟩

private theorem act_mem_autCentralizer_of_mem_centralizer
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) (h4 : Conclusion9_4 D hC T S) {b : G}
    (hb : b ∈ Subgroup.centralizer ((S : Set G) ∩ D))
    (hbu : b ∈ Subgroup.centralizer ({hC.d} : Set G)) :
    act hC h3 ⟨b, hbu⟩ ∈ autCentralizer (rootCenter (T.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center (Halpha D hC.alpha))) : Subgroup _)) := by
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore
    (T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center (Halpha D hC.alpha))))
  refine mem_autCentralizer_iff.mpr fun z hz => ?_
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  · have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc.center_sq z hz) hz1
    obtain ⟨x, hx, rfl⟩ := exists_bar_eq hC hH h3 hz2
    have hxΔ : x ∈ (S : Set G) ∩ D := by
      rw [h4.1]
      exact ⟨mem_sylow_map_of_bar_mem hC hH h3 T hx (mem_rootCenter_iff.mp hz).1, hx.1⟩
    rw [act_bar hC h3 _ (mem_Halpha_of_mem_commSet hC h3 hx)]
    congr 1
    show b * x * b⁻¹ = x
    rw [(Subgroup.mem_centralizer_iff.mp hb x hxΔ).symm, mul_inv_cancel_right]

private theorem centralizer_inter_le_sylow_map_of_not_psu3
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) (h4 : Conclusion9_4 D hC T S)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (hU3 : ¬ ∃ n : ℕ, Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
      CFSG.Theory.Comparator.PSU3Model n)) :
    Subgroup.centralizer ((S : Set G) ∩ D) ≤
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  intro b hb
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  have hi : i ≠ 3 := by
    rintro rfl
    cases hB with
    | unitary n hn e => exact hU3 ⟨n, ⟨e⟩⟩
  have huT := d_mem_sylow_map hC h3 T
  have hbu : b ∈ Subgroup.centralizer ({hC.d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb _
      (by rw [h4.1]; exact ⟨huT, hC.hd⟩)).symm
  obtain ⟨r, hr, hbr⟩ := hB.exists_eq_conj_of_centralizes_center_of_ne_three hi _ _
    (mem_autCentralizer_iff.mp (act_mem_autCentralizer_of_mem_centralizer hC hH h3 T S h4 hb hbu))
  rw [Sylow.coe_mapSurjective] at hr
  obtain ⟨c, hcT, rfl⟩ := hr
  have hcu : (c : G) ∈ Subgroup.centralizer ({hC.d} : Set G) :=
    PartThree.Halpha_le_centralizer_d hC c.2
  have hgu : b * (c : G)⁻¹ ∈ Subgroup.centralizer ({hC.d} : Set G) :=
    Subgroup.mul_mem _ hbu (Subgroup.inv_mem _ hcu)
  have hg1 : act hC h3 ⟨b * (c : G)⁻¹, hgu⟩ = 1 := by
    rw [show (⟨b * (c : G)⁻¹, hgu⟩ : Subgroup.centralizer ({hC.d} : Set G)) =
      ⟨b, hbu⟩ * ⟨c, hcu⟩⁻¹ from rfl, map_mul, map_inv, hbr, act_eq_conj hC h3 c.2 hcu,
      bar_of_mem hC c.2]
    exact mul_inv_cancel _
  have hgE := mem_centralizer_Halpha_of_act_eq_one hC h3 hgu hg1
  rw [hCH] at hgE
  rw [show b = b * (c : G)⁻¹ * c by group]
  exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr huT hgE) ⟨c, hcT, rfl⟩

private theorem sylow_map_le_centralizer_inter (hC : HypothesisC D)
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (T : Sylow 2 (Halpha D hC.alpha))
    (S : Sylow 2 G) (h4 : Conclusion9_4 D hC T S) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      Subgroup.centralizer ((S : Set G) ∩ D) := by
  intro t ht
  obtain ⟨n, i, e, hB⟩ := isBenderGroup_iff_exists_benderType.mp hH.bender
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore
    (T.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center (Halpha D hC.alpha))))
  have htH : t ∈ Halpha D hC.alpha := Subgroup.map_subtype_le _ ht
  have huΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [h4.1]
    exact ⟨d_mem_sylow_map hC h3 T, hC.hd⟩
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hxT : x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [h4.1] at hx
    exact hx.1
  by_cases hxu : x = hC.d
  · rw [hxu]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC htH)).symm
  have hxD : x ∈ commSet D hC.d :=
    ⟨hx.2, sylow_inter_commute_of_setup hC.setup S hx.1 huΔ.1 hx.2 hC.hd hxu, hxu⟩
  have hxZ := hc.center_of_involution _ (le_borel _ (bar_mem_sylow_map hC T hxT))
    (orderOf_bar hC h3 hxD)
  have htx := (mem_rootCenter_iff.mp hxZ).2 _ (bar_mem_sylow_map hC T ht)
  have htu : t * hC.d * t⁻¹ = hC.d := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC htH),
      mul_inv_cancel_right]
  have hxH := mem_Halpha_of_mem_commSet hC h3 hxD
  have h1 := eq_of_bar_eq hC h3 (conj_mem_commSet hC t htu hxD) hxD (by
    rw [bar_mul hC (Subgroup.mul_mem _ htH hxH) (Subgroup.inv_mem _ htH), bar_mul hC htH hxH,
      bar_inv hC htH, htx, mul_inv_cancel_right])
  calc x * t = t * x * t⁻¹ * t := by rw [h1]
    _ = t * x := by group

theorem centralizer_inter_eq_sylow_map_of_not_psu3
    (hC : HypothesisC D) (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) (h4 : Conclusion9_4 D hC T S)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (hU3 : ¬ ∃ n : ℕ, Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃*
      CFSG.Theory.Comparator.PSU3Model n)) :
    Subgroup.centralizer ((S : Set G) ∩ D) =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
  le_antisymm (centralizer_inter_le_sylow_map_of_not_psu3 hC hH h3 T S h4 hCH hU3)
    (sylow_map_le_centralizer_inter hC hH h3 T S h4)

end CFSG.OddTranspositions.PartThree.Nine
