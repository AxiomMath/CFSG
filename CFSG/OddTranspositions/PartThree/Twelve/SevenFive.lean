module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartFour.LinePolar
import CFSG.OddTranspositions.PartThree.Nine.Setup
import CFSG.OddTranspositions.PartThree.Twelve.Seven
import CFSG.OddTranspositions.PartThree.Twelve.SevenClasses
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlane
import CFSG.OddTranspositions.PartFour.Fourteen.FivePlanePerp

public section

namespace CFSG.OddTranspositions.PartThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
private theorem conj_mem_commSet_pivot (hC : HypothesisC D) {g v x : G} (hg : g * v * g⁻¹ = hC.d)
    (hx : x ∈ commSet D v) : g * x * g⁻¹ ∈ commSet D hC.d := by
  rw [← hg]
  exact ⟨hC.setup.conj_mem g hx.1, (Commute.conj_iff g).2 hx.2.1,
    fun h => hx.2.2 (mul_left_cancel (mul_right_cancel h))⟩

namespace FiveChart

variable {hC : HypothesisC D} {n : ℕ}

omit [Finite G] in
theorem commute_of_orth {c : FiveChart hC n} {a y : G} (ha : a ∈ commSet D hC.d)
    (hy : y ∈ commSet D hC.d) (h : c.b (c.vec y) (c.vec a) = 0) : Commute y a := by
  by_cases hya : y = a
  · rw [hya]
  · exact (c.commute_iff y hy a ha hya).mpr h

omit [Finite G] in
theorem not_commute_of_ne_zero {c : FiveChart hC n} {y a : G} (hy : y ∈ commSet D hC.d)
    (ha : a ∈ commSet D hC.d) (hya : y ≠ a) (h : c.b (c.vec y) (c.vec a) ≠ 0) :
    ¬ Commute y a :=
  fun hc => h ((c.commute_iff y hy a ha hya).mp hc)

omit [Finite G] in
private theorem ne_of_vec_eq_or_eq_neg {c : FiveChart hC n} {w : Fin n → ZMod 5} {a y : G}
    (hvy : c.vec y = w ∨ c.vec y = -w) (hw : w ≠ c.vec a) (hw' : w ≠ -c.vec a) :
    y ≠ a := by
  intro h
  rw [h] at hvy
  rcases hvy with h1 | h1
  · exact hw h1.symm
  · exact hw' (by rw [h1]; exact (neg_neg w).symm)

omit [Finite G] in
theorem exists_commute_commute_ne (c : FiveChart hC n) (hn : 5 ≤ n) {a b : G}
    (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b) :
    ∃ y ∈ commSet D hC.d, Commute y a ∧ Commute y b ∧ y ≠ a ∧ y ≠ b := by
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hpp : c.b (c.vec a) (c.vec a) = 1 := c.norm_vec a ha
  have hqq : c.b (c.vec b) (c.vec b) = 1 := c.norm_vec b hb
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  have hqp : c.vec b ≠ c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inl h))
  have hqp' : c.vec b ≠ -c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inr h))
  obtain ⟨y₀, hy₀n, hy₀p, hy₀q⟩ :=
    FivePlane.exists_norm_one_perp_pair (b := c.b) c.hsym c.hnd hn hpp hqq hqp hqp'
  obtain ⟨y, hy, hvy⟩ := c.exists_vec y₀ hy₀n
  have hya : c.b (c.vec y) (c.vec a) = 0 := by
    rcases hvy with h | h
    · rw [h]; exact hy₀p
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y₀ (c.vec a)).trans (by rw [hy₀p]; exact neg_zero)
  have hyb : c.b (c.vec y) (c.vec b) = 0 := by
    rcases hvy with h | h
    · rw [h]; exact hy₀q
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y₀ (c.vec b)).trans (by rw [hy₀q]; exact neg_zero)
  refine ⟨y, hy, commute_of_orth ha hy hya, commute_of_orth hb hy hyb, ?_, ?_⟩
  · intro h
    rw [h] at hya
    rw [hpp] at hya
    exact (by decide : (1 : ZMod 5) ≠ 0) hya
  · intro h
    rw [h] at hyb
    rw [hqq] at hyb
    exact (by decide : (1 : ZMod 5) ≠ 0) hyb

omit [Finite G] in
theorem exists_commute_not_commute (c : FiveChart hC n) (hn : 5 ≤ n) {a b x : G}
    (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d) (hx : x ∈ commSet D hC.d)
    (hab : ¬ Commute a b) (hxa : Commute x a) (hxb : Commute x b) :
    ∃ y ∈ commSet D hC.d, Commute y a ∧ Commute y b ∧ ¬ Commute y x := by
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hxna : x ≠ a := by
    intro h
    rw [h] at hxb
    exact hab hxb
  have hxnb : x ≠ b := by
    intro h
    rw [h] at hxa
    exact hab hxa.symm
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  have hqp : c.vec b ≠ c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inl h))
  have hqp' : c.vec b ≠ -c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inr h))
  have hxp : c.b (c.vec x) (c.vec a) = 0 := (c.commute_iff x hx a ha hxna).mp hxa
  have hxq : c.b (c.vec x) (c.vec b) = 0 := (c.commute_iff x hx b hb hxnb).mp hxb
  obtain ⟨y₀, hy₀n, hy₀p, hy₀q, hxy₀, hy₀ne, hy₀ne'⟩ :=
    FivePlane.exists_perp_pair_not_perp (b := c.b) (p := c.vec a) (q := c.vec b) (x := c.vec x)
      c.hsym c.hnd hn (c.norm_vec a ha) (c.norm_vec b hb) hpq0 hqp hqp'
      (c.norm_vec x hx) hxp hxq
  obtain ⟨y, hy, hvy⟩ := c.exists_vec y₀ hy₀n
  have hyx : y ≠ x := by
    intro h
    rw [h] at hvy
    rcases hvy with h' | h'
    · exact hy₀ne h'.symm
    · exact hy₀ne' (by rw [h']; exact (neg_neg y₀).symm)
  have hya : c.b (c.vec y) (c.vec a) = 0 := by
    rcases hvy with h | h
    · rw [h]; exact hy₀p
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y₀ (c.vec a)).trans (by rw [hy₀p]; exact neg_zero)
  have hyb : c.b (c.vec y) (c.vec b) = 0 := by
    rcases hvy with h | h
    · rw [h]; exact hy₀q
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y₀ (c.vec b)).trans (by rw [hy₀q]; exact neg_zero)
  have hyxn : c.b (c.vec y) (c.vec x) ≠ 0 := by
    rcases hvy with h | h
    · rw [h]; rw [c.hsym y₀ (c.vec x)]; exact hxy₀
    · rw [h]
      have hval : c.b (-y₀) (c.vec x) = -(c.b (c.vec x) y₀) :=
        (LinearMap.map_neg₂ c.b y₀ (c.vec x)).trans (congrArg Neg.neg (c.hsym y₀ (c.vec x)))
      intro hc
      exact hxy₀ (neg_eq_zero.mp (hval.symm.trans hc))
  exact ⟨y, hy, commute_of_orth ha hy hya, commute_of_orth hb hy hyb,
    not_commute_of_ne_zero hy hx hyx hyxn⟩

omit [Finite G] in
private theorem mem_D_and_commute_of_mem_lineMem {a b z : G} (ha : a ∈ commSet D hC.d)
    (hb : b ∈ commSet D hC.d) (hz : z ∈ lineMem D a b) : z ∈ D ∧ Commute z hC.d := by
  have hdab : hC.d ∈ perpMem D a ∩ perpMem D b :=
    ⟨⟨hC.hd, ha.2.1.symm⟩, ⟨hC.hd, hb.2.1.symm⟩⟩
  exact ⟨hz.1, (hz.2 hdab).2.symm⟩

omit [Finite G] in
theorem pivot_not_mem_lineMem (c : FiveChart hC n) (hn : 5 ≤ n) {a b : G}
    (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b) :
    hC.d ∉ lineMem D a b := by
  obtain ⟨δ, hδ, hδa, hδb, hδa', hδb'⟩ := c.exists_commute_commute_ne hn ha hb hab
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hδ.1 hC.hd)
  have haδ : a ∈ commSet D δ := ⟨ha.1, hδa.symm, Ne.symm hδa'⟩
  have hbδ : b ∈ commSet D δ := ⟨hb.1, hδb.symm, Ne.symm hδb'⟩
  have hdδ : hC.d ∈ commSet D δ := ⟨hC.hd, hδ.2.1.symm, Ne.symm hδ.2.2⟩
  have ha' := conj_mem_commSet_pivot hC hg haδ
  have hb' := conj_mem_commSet_pivot hC hg hbδ
  have hd' := conj_mem_commSet_pivot hC hg hdδ
  have hab' : ¬ Commute (g * a * g⁻¹) (g * b * g⁻¹) := fun h => hab ((Commute.conj_iff g).mp h)
  have hd'a' : Commute (g * hC.d * g⁻¹) (g * a * g⁻¹) := (Commute.conj_iff g).mpr ha.2.1.symm
  have hd'b' : Commute (g * hC.d * g⁻¹) (g * b * g⁻¹) := (Commute.conj_iff g).mpr hb.2.1.symm
  obtain ⟨y', hy', hy'a', hy'b', hy'd'⟩ :=
    c.exists_commute_not_commute hn ha' hb' hd' hab' hd'a' hd'b'
  have hyg : g * (g⁻¹ * y' * g) * g⁻¹ = y' := by group
  have hyD : g⁻¹ * y' * g ∈ D := by simpa using hC.setup.conj_mem g⁻¹ hy'.1
  have hya : Commute (g⁻¹ * y' * g) a := by
    refine (Commute.conj_iff g).mp ?_
    rw [hyg]; exact hy'a'
  have hyb : Commute (g⁻¹ * y' * g) b := by
    refine (Commute.conj_iff g).mp ?_
    rw [hyg]; exact hy'b'
  have hyn : ¬ Commute (g⁻¹ * y' * g) hC.d := by
    intro h
    exact hy'd' (by rw [← hyg]; exact (Commute.conj_iff g).mpr h)
  intro hdL
  exact hyn (hdL.2 ⟨⟨hyD, hya⟩, ⟨hyD, hyb⟩⟩).2

omit [Finite G] in
theorem lineMem_subset_chart (c : FiveChart hC n) (hn : 5 ≤ n) {a b z : G}
    (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b)
    (hz : z ∈ lineMem D a b) :
    z ∈ commSet D hC.d ∧ ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b := by
  obtain ⟨hzD, hzc⟩ := mem_D_and_commute_of_mem_lineMem ha hb hz
  have hdnot := pivot_not_mem_lineMem c hn ha hb hab
  have hz' : z ∈ commSet D hC.d := ⟨hzD, hzc, fun h => hdnot (h ▸ hz)⟩
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  have hqp : c.vec b ≠ c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inl h))
  have hqp' : c.vec b ≠ -c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inr h))
  refine ⟨hz', ?_⟩
  refine FivePlane.mem_pair_of_forall_perp (b := c.b) (p := c.vec a) (q := c.vec b)
    (x := c.vec z) c.hsym c.hnd hn (c.norm_vec a ha) (c.norm_vec b hb) hpq0 hqp hqp' ?_
  intro y hy_norm hyp hyq
  obtain ⟨w, hw, hvw⟩ := c.exists_vec y hy_norm
  have hwa : Commute w a := by
    refine commute_of_orth (c := c) ha hw ?_
    rcases hvw with h | h
    · rw [h]; exact hyp
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y (c.vec a)).trans (by rw [hyp]; exact neg_zero)
  have hwb : Commute w b := by
    refine commute_of_orth (c := c) hb hw ?_
    rcases hvw with h | h
    · rw [h]; exact hyq
    · rw [h]
      exact (LinearMap.map_neg₂ c.b y (c.vec b)).trans (by rw [hyq]; exact neg_zero)
  have hcomm : Commute w z := (hz.2 ⟨⟨hw.1, hwa⟩, ⟨hw.1, hwb⟩⟩).2
  by_cases hwz : w = z
  · exfalso
    have hza : Commute z a := by rw [← hwz]; exact hwa
    have hzb : Commute z b := by rw [← hwz]; exact hwb
    obtain ⟨v, hv, hva, hvb, hvz⟩ := c.exists_commute_not_commute hn ha hb hz' hab hza hzb
    exact hvz ((hz.2 ⟨⟨hv.1, hva⟩, ⟨hv.1, hvb⟩⟩).2)
  · have hwz0 : c.b (c.vec w) (c.vec z) = 0 := (c.commute_iff w hw z hz' hwz).mp hcomm
    rw [c.hsym (c.vec w) (c.vec z)] at hwz0
    rcases hvw with h | h
    · rwa [h] at hwz0
    · rw [h] at hwz0
      have h2 : c.b (c.vec z) (-y) = -(c.b (c.vec z) y) := map_neg (c.b (c.vec z)) y
      exact neg_eq_zero.mp (h2.symm.trans hwz0)

omit [Finite G] in
private theorem ncard_chartSet_le (c : FiveChart hC n) {a b : G} (ha : a ∈ commSet D hC.d)
    (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b) :
    {z | z ∈ commSet D hC.d ∧ ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b}.ncard ≤
      if c.b (c.vec a) (c.vec b) ^ 2 = 1 then 5 else 3 := by
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  have hqp : c.vec b ≠ c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inl h))
  have hqp' : c.vec b ≠ -c.vec a :=
    fun h => habne.symm (c.eq_of_vec a ha b hb (Or.inr h))
  exact FivePlane.ncard_le_of_mem_pair (b := c.b) (p := c.vec a) (q := c.vec b)
    (S := {z | z ∈ commSet D hC.d ∧ ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b})
    (f := c.vec) c.hsym (c.norm_vec a ha) (c.norm_vec b hb) hpq0
    (fun z hz => ⟨c.norm_vec z hz.1, hz.2⟩)
    (fun z hz z' hz' h => c.eq_of_vec z hz.1 z' hz'.1 h)

private theorem orderOf_le_ncard_lineMem {a b : G} (ha : a ∈ commSet D hC.d)
    (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b) :
    orderOf (a * b) ≤ (lineMem D a b).ncard :=
  (orderOf_mul_le_ncard_inter_closure hC.setup.oddT
    (fun g _z hz => hC.setup.conj_mem g hz) ha.1 hb.1 hab).trans
    (Set.ncard_le_ncard inter_closure_subset_lineMem (Set.toFinite _))

theorem lineMem_eq (c : FiveChart hC n) (hn : 5 ≤ n) {a b : G} (ha : a ∈ commSet D hC.d)
    (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b) :
    lineMem D a b =
        {z | z ∈ commSet D hC.d ∧ ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b} ∧
      (lineMem D a b).ncard = orderOf (a * b) := by
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  have hLS : lineMem D a b ⊆
      {z | z ∈ commSet D hC.d ∧ ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b} :=
    fun z hz => lineMem_subset_chart c hn ha hb hab hz
  have hlow : orderOf (a * b) ≤ (lineMem D a b).ncard := orderOf_le_ncard_lineMem ha hb hab
  have hSle : {z | z ∈ commSet D hC.d ∧
        ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b}.ncard ≤ (lineMem D a b).ncard := by
    calc {z | z ∈ commSet D hC.d ∧
          ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b}.ncard
        ≤ (if c.b (c.vec a) (c.vec b) ^ 2 = 1 then 5 else 3) := ncard_chartSet_le c ha hb hab
      _ = orderOf (a * b) := (c.orderOf_mul a ha b hb habne hpq0).symm
      _ ≤ (lineMem D a b).ncard := hlow
  have hncard : (lineMem D a b).ncard = orderOf (a * b) := by
    refine le_antisymm ?_ hlow
    calc (lineMem D a b).ncard
        ≤ {z | z ∈ commSet D hC.d ∧
            ∃ l m : ZMod 5, c.vec z = l • c.vec a + m • c.vec b}.ncard :=
          Set.ncard_le_ncard hLS (Set.toFinite _)
      _ ≤ orderOf (a * b) :=
          (ncard_chartSet_le c ha hb hab).trans
            (le_of_eq (c.orderOf_mul a ha b hb habne hpq0).symm)
  exact ⟨(Set.subset_iff_eq_of_ncard_le hSle (Set.toFinite _)).mp hLS, hncard⟩

private theorem exists_smul_eq_iff {p q x v : Fin n → ZMod 5} {l m l' m' : ZMod 5}
    (hx : x = l • p + m • q) (hq : q = l' • p + m' • x) :
    (∃ r s : ZMod 5, v = r • p + s • q) ↔ ∃ r s : ZMod 5, v = r • p + s • x := by
  constructor
  · rintro ⟨r, s, rfl⟩
    refine ⟨r + s * l', s * m', ?_⟩
    rw [hq]
    module
  · rintro ⟨r, s, rfl⟩
    refine ⟨r + s * l, s * m, ?_⟩
    rw [hx]
    module

theorem not_commute_and_lineMem_eq (c : FiveChart hC n) (hn : 5 ≤ n) {a b x : G}
    (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d) (hab : ¬ Commute a b)
    (hx : x ∈ lineMem D a b) (hxa : x ≠ a) :
    ¬ Commute x a ∧ lineMem D a x = lineMem D a b := by
  obtain ⟨hx', hcomb⟩ := lineMem_subset_chart c hn ha hb hab hx
  obtain ⟨l, m, hl⟩ := hcomb
  have hxp : c.vec x ≠ c.vec a := fun h =>
    hxa (c.eq_of_vec x hx' a ha (Or.inl h.symm)).symm
  have hxp' : c.vec x ≠ -c.vec a := fun h => hxa (c.eq_of_vec x hx' a ha
    (Or.inr ((congrArg Neg.neg h).trans (neg_neg (c.vec a))).symm)).symm
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hpq0 : c.b (c.vec a) (c.vec b) ≠ 0 :=
    fun h => hab ((c.commute_iff a ha b hb habne).mpr h)
  obtain ⟨hpx, l', m', hq⟩ :=
    FivePlane.ne_zero_and_mem_pair_of_mem_pair (b := c.b) (p := c.vec a) (q := c.vec b)
      (x := c.vec x) c.hsym (c.norm_vec a ha) (c.norm_vec b hb) hpq0 (c.norm_vec x hx')
      hl hxp hxp'
  have hnc : ¬ Commute x a := by
    refine not_commute_of_ne_zero (c := c) hx' ha hxa ?_
    rw [c.hsym (c.vec x) (c.vec a)]
    exact hpx
  have hline : lineMem D a x = lineMem D a b := by
    have hxline := (lineMem_eq c hn ha hx' (fun h => hnc h.symm)).1
    have hbline := (lineMem_eq c hn ha hb hab).1
    rw [hxline, hbline]
    ext z
    simp only [Set.mem_setOf_eq]
    exact ⟨fun ⟨hz, h⟩ => ⟨hz, (exists_smul_eq_iff (v := c.vec z) hl hq).mpr h⟩,
      fun ⟨hz, h⟩ => ⟨hz, (exists_smul_eq_iff (v := c.vec z) hl hq).mp h⟩⟩
  exact ⟨hnc, hline⟩

private theorem exists_ncard_lineMem (c : FiveChart hC n) (hn : 5 ≤ n) {e : G}
    (he : e ∈ commSet D hC.d) {t : ZMod 5} (ht : t ≠ 0) :
    ∃ z ∈ commSet D hC.d, ¬ Commute e z ∧
      (lineMem D e z).ncard = if t ^ 2 = 1 then 5 else 3 := by
  obtain ⟨q, hqn, hqp, hqne, hqne'⟩ :=
    FivePlane.exists_norm_one_pairing (b := c.b) (p := c.vec e) c.hsym c.hnd hn
      (c.norm_vec e he) t
  obtain ⟨z, hz, hvz⟩ := c.exists_vec q hqn
  have hne : z ≠ e := ne_of_vec_eq_or_eq_neg hvz hqne hqne'
  have hpair0 : c.b (c.vec e) (c.vec z) ≠ 0 := by
    rcases hvz with h | h
    · rw [h, hqp]; exact ht
    · rw [h]
      have hval : c.b (c.vec e) (-q) = -t :=
        (map_neg (c.b (c.vec e)) q).trans (congrArg Neg.neg hqp)
      intro hc
      exact ht (neg_eq_zero.mp (hval.symm.trans hc))
  have hnc : ¬ Commute e z :=
    fun hc => hpair0 ((c.commute_iff e he z hz (Ne.symm hne)).mp hc)
  have hsq : c.b (c.vec e) (c.vec z) ^ 2 = t ^ 2 := by
    rcases hvz with h | h
    · rw [h, hqp]
    · have h1 : c.b (c.vec e) (c.vec z) = c.b (c.vec e) (-q) :=
        congrArg (fun v => c.b (c.vec e) v) h
      rw [h1]
      rw [map_neg (c.b (c.vec e)) q, hqp]
      ring
  refine ⟨z, hz, hnc, ?_⟩
  rw [(lineMem_eq c hn he hz hnc).2, c.orderOf_mul e he z hz (Ne.symm hne) hpair0, hsq]

private theorem not_commute_and_lineMem_eq_of_conj (c : FiveChart hC n) (hn : 5 ≤ n) {g a b c₀ : G}
    (ha' : g * a * g⁻¹ ∈ commSet D hC.d) (hb' : g * b * g⁻¹ ∈ commSet D hC.d)
    (hab' : ¬ Commute (g * a * g⁻¹) (g * b * g⁻¹))
    (hc₀ : c₀ ∈ lineMem D a b) (hc₀a : c₀ ≠ a) :
    ¬ Commute c₀ a ∧ lineMem D a c₀ = lineMem D a b := by
  have himg : lineMem D (g * a * g⁻¹) (g * b * g⁻¹) = (MulAut.conj g) '' lineMem D a b :=
    lineMem_conj (E := D) (fun g' _z hz => hC.setup.conj_mem g' hz) g a b
  have hc₀' : g * c₀ * g⁻¹ ∈ lineMem D (g * a * g⁻¹) (g * b * g⁻¹) := by
    rw [himg]
    exact ⟨c₀, hc₀, by rw [MulAut.conj_apply]⟩
  have hc₀'a : g * c₀ * g⁻¹ ≠ g * a * g⁻¹ := by
    intro h
    exact hc₀a (mul_left_cancel (mul_right_cancel h))
  obtain ⟨hnc, hline⟩ := not_commute_and_lineMem_eq c hn ha' hb' hab' hc₀' hc₀'a
  refine ⟨?_, ?_⟩
  · intro h
    exact hnc ((Commute.conj_iff g).mpr h)
  · have h1 : lineMem D (g * a * g⁻¹) (g * c₀ * g⁻¹) = (MulAut.conj g) '' lineMem D a c₀ :=
      lineMem_conj (E := D) (fun g' _z hz => hC.setup.conj_mem g' hz) g a c₀
    have himg1 : (MulAut.conj g) '' lineMem D a c₀ = (MulAut.conj g) '' lineMem D a b := by
      rw [← h1, ← himg]
      exact hline
    exact (Set.image_eq_image (f := MulAut.conj g) (MulAut.conj g).injective).mp himg1

end FiveChart

theorem lineMem_five (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC)) {v a b : G} (hv : v ∈ D)
    (ha : a ∈ commSet D v) (hb : b ∈ commSet D v) (hab : ¬ Commute a b) :
    (orderOf (a * b) = 3 ∨ orderOf (a * b) = 5) ∧ (lineMem D a b).ncard = orderOf (a * b) ∧
      ∀ c ∈ lineMem D a b, c ≠ a → ¬ Commute c a ∧ lineMem D a c = lineMem D a b := by
  obtain ⟨c⟩ := exists_fiveChart hC hMZ hα hk h5
  have hn : 5 ≤ k + 1 := by omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hv hC.hd)
  have ha' := conj_mem_commSet_pivot hC hg ha
  have hb' := conj_mem_commSet_pivot hC hg hb
  have habne : a ≠ b := fun h => hab (by rw [h])
  have hab' : ¬ Commute (g * a * g⁻¹) (g * b * g⁻¹) := fun h => hab ((Commute.conj_iff g).mp h)
  have habne' : g * a * g⁻¹ ≠ g * b * g⁻¹ := by
    intro h
    exact habne (mul_left_cancel (mul_right_cancel h))
  have hpq0' : c.b (c.vec (g * a * g⁻¹)) (c.vec (g * b * g⁻¹)) ≠ 0 :=
    fun h => hab' ((c.commute_iff (g * a * g⁻¹) ha' (g * b * g⁻¹) hb' habne').mpr h)
  have himg : lineMem D (g * a * g⁻¹) (g * b * g⁻¹) = (MulAut.conj g) '' lineMem D a b :=
    lineMem_conj (E := D) (fun g' _z hz => hC.setup.conj_mem g' hz) g a b
  have hord' : orderOf ((g * a * g⁻¹) * (g * b * g⁻¹)) = orderOf (a * b) := by
    rw [show (g * a * g⁻¹) * (g * b * g⁻¹) = (MulAut.conj g) (a * b) by
      rw [MulAut.conj_apply]; group]
    exact MulEquiv.orderOf_eq (MulAut.conj g) (a * b)
  have hncard : (lineMem D a b).ncard = orderOf (a * b) := by
    rw [← Set.ncard_image_of_injective (lineMem D a b) (MulAut.conj g).injective, ← himg,
      (FiveChart.lineMem_eq c hn ha' hb' hab').2, hord']
  have hord : orderOf (a * b) = 3 ∨ orderOf (a * b) = 5 := by
    have h := c.orderOf_mul (g * a * g⁻¹) ha' (g * b * g⁻¹) hb' habne' hpq0'
    rw [hord'] at h
    by_cases hb1 : c.b (c.vec (g * a * g⁻¹)) (c.vec (g * b * g⁻¹)) ^ 2 = 1
    · right; rw [h, if_pos hb1]
    · left; rw [h, if_neg hb1]
  exact ⟨hord, hncard, fun c₀ hc₀ hc₀a =>
    FiveChart.not_commute_and_lineMem_eq_of_conj c hn ha' hb' hab' hc₀ hc₀a⟩

theorem twelveSeven_five_exists (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC)) :
    (∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 3) ∧
      ∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = 5 := by
  obtain ⟨c⟩ := exists_fiveChart hC hMZ hα hk h5
  have hn : 5 ≤ k + 1 := by omega
  obtain ⟨e, heE⟩ := OddLocal.nonempty hC.hE
  have hz₀ : e ∈ commSet D hC.d := by
    rw [← Nine.DalphaStar_eq_commSet hC hα, hC.DalphaStar_alpha]
    exact heE
  obtain ⟨z₃, hz₃, hnc3, hline3⟩ := c.exists_ncard_lineMem hn hz₀ (t := 2) (by decide)
  obtain ⟨z₅, hz₅, hnc5, hline5⟩ := c.exists_ncard_lineMem hn hz₀ (t := 1) (by decide)
  have h3 : (lineMem D e z₃).ncard = 3 := by
    rw [hline3, if_neg (by decide : (2 : ZMod 5) ^ 2 ≠ 1)]
  have h5 : (lineMem D e z₅).ncard = 5 := by
    rw [hline5, if_pos (by decide : (1 : ZMod 5) ^ 2 = 1)]
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hz₀.1 hC.hd)
  have hmk : ∀ (z : G), z ∈ commSet D hC.d → ¬ Commute e z →
      ∃ w ∈ D, ¬ Commute w hC.d ∧ (lineMem D hC.d w).ncard = (lineMem D e z).ncard := by
    intro z hz hnez
    refine ⟨g * z * g⁻¹, hC.setup.conj_mem g hz.1, ?_, ?_⟩
    · intro h
      rw [← hg] at h
      exact hnez ((Commute.conj_iff g).mp h).symm
    · rw [← hg, lineMem_conj (E := D) (fun g' _z hz => hC.setup.conj_mem g' hz) g e z,
        Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hwD, hwnc, hwn⟩ := hmk z₃ hz₃ hnc3
    exact ⟨w, hwD, hwnc, by rw [hwn, h3]⟩
  · obtain ⟨w, hwD, hwnc, hwn⟩ := hmk z₅ hz₅ hnc5
    exact ⟨w, hwD, hwnc, by rw [hwn, h5]⟩

theorem fiveLines_of_isFiveReflectionModel (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d}) {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (h5 : IsFiveReflectionModel k ε π (imageClass hC)) : FiveLines D :=
  fun _ hv _ ha _ hb hab => lineMem_five hC hMZ hα hk h5 hv ha hb hab

end CFSG.OddTranspositions.PartThree

end
