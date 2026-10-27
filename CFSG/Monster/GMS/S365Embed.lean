module

public import CFSG.Monster.GMS.S365Facts
public import CFSG.Monster.GMS.S365Exists
public import CFSG.Monster.GMS.S365Normal
import CFSG.Sporadic.Co1.Module.Involutions
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Monster.GMS.Leech.OddLift
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Lifts

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ w : G}

theorem mem_leechQ_iff_isConj_mul
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q c : G}
    (hq : IsConj z₀ q) (hc : IsConj a c) (hcomm : c * q = q * c) :
    c ∈ leechQ q ↔ IsConj a (q * c) := by
  constructor
  · exact isConj_a_mul_of_mem I hG hq hc hcomm
  · intro h
    by_contra hnot
    exact hG.not_isConj (h.trans ((isConj_mul_iff I hG hq hc hcomm).2 hnot).symm)

theorem co1Act_co1Act_of_mul_self {r : Co1} (h : r * r = 1) (x : Fin 24 → ZMod 2) :
    co1Act r (co1Act r x) = x := by
  calc co1Act r (co1Act r x) = (co1Act r * co1Act r) x := (Module.End.mul_apply _ _ _).symm
    _ = co1Act (r * r) x := by rw [map_mul]
    _ = x := by rw [h, map_one, Module.End.one_apply]

theorem exists_good_lift
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (L : LeechSystem w) {c : G} (hcA : IsConj a c)
    (hcC : c ∈ Subgroup.centralizer ({w} : Set G)) (hcQ : c ∉ leechQ w)
    {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 2) (hR : ∃ p, v = p + co1Act (L.φ ⟨c, hcC⟩) p) :
    ∃ q ∈ leechQ w, L.vec q = v ∧ c * q = q * c ∧ c ∈ leechQ q ∧ c ∉ leechQ (q * w) := by
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hcC hcA hcQ
  have hr2 : L.φ ⟨c, hcC⟩ * L.φ ⟨c, hcC⟩ = 1 := L.φ_mul_self hcC hly.mul_self
  obtain ⟨pv, hpv⟩ := hR
  obtain ⟨p, hp, hpvec⟩ := L.vec_surj pv
  have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hp
  have hconj : c * p⁻¹ * c⁻¹ ∈ leechQ w := L.conj_mem' hcC (inv_mem hp)
  have hq₁Q : p * (c * p⁻¹ * c⁻¹) ∈ leechQ w := mul_mem hp hconj
  set q₁ : G := p * (c * p⁻¹ * c⁻¹) with hq₁
  have hvec : L.vec q₁ = v := by
    rw [hq₁, L.vec_mul p hp _ hconj, L.vec_conj' hcC (inv_mem hp), L.vec_inv hp, hpvec]
    exact hpv.symm
  have hfix : L.vec q₁ ∈ co1Fix (L.φ ⟨c, hly.mem_centralizer⟩) := by
    show co1Act (L.φ ⟨c, hcC⟩) (L.vec q₁) = L.vec q₁
    rw [hvec, hpv, map_add, co1Act_co1Act_of_mul_self hr2, add_comm]
  have hcomm : c * q₁ = q₁ * c := L.commute_of_vec_mem_co1Fix hI hly hq₁Q hfix
  have hq₁B : IsConj z₀ q₁ := isConj_of_mem_typeSet_two I hG hw L ⟨hq₁Q, hvec ▸ hv⟩
  have hq₁c : q₁ * c = p * c * p⁻¹ := by rw [hq₁]; group
  have hcA' : IsConj a (p * c * p⁻¹) := (isConj_conj_iff a p c).2 hcA
  refine ⟨q₁, hq₁Q, hvec, hcomm, ?_, ?_⟩
  · exact (mem_leechQ_iff_isConj_mul I hG hq₁B hcA hcomm).2 (by rw [hq₁c]; exact hcA')
  · intro hmem
    have hq₂Q : q₁ * w ∈ leechQ w := mul_mem hq₁Q L.z_mem
    have hvec₂ : L.vec (q₁ * w) = v := by rw [L.vec_mul_z hq₁Q, hvec]
    have hq₂B : IsConj z₀ (q₁ * w) := isConj_of_mem_typeSet_two I hG hw L ⟨hq₂Q, hvec₂ ▸ hv⟩
    have hcomm₂ : c * (q₁ * w) = q₁ * w * c := by
      calc c * (q₁ * w) = c * q₁ * w := (mul_assoc c q₁ w).symm
        _ = q₁ * c * w := by rw [hcomm]
        _ = q₁ * (c * w) := mul_assoc q₁ c w
        _ = q₁ * (w * c) := by rw [hcw]
        _ = q₁ * w * c := (mul_assoc q₁ w c).symm
    have h2A := isConj_a_mul_of_mem I hG hq₂B hcA hcomm₂ hmem
    have hc'Q : p * c * p⁻¹ ∉ leechQ w := L.conj_not_mem hpC hcQ
    have hc'C : p * c * p⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
      mul_mem (mul_mem hpC hcC) (inv_mem hpC)
    have hc'w : p * c * p⁻¹ * w = w * (p * c * p⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 hc'C
    have hB := (isConj_mul_iff I hG hw hcA' hc'w).2 hc'Q
    have e : q₁ * w * c = w * (p * c * p⁻¹) := by
      calc q₁ * w * c = q₁ * (w * c) := mul_assoc q₁ w c
        _ = q₁ * (c * w) := by rw [hcw]
        _ = q₁ * c * w := (mul_assoc q₁ c w).symm
        _ = p * c * p⁻¹ * w := by rw [hq₁c]
        _ = w * (p * c * p⁻¹) := hc'w
    rw [e] at h2A
    exact hG.not_isConj (h2A.trans hB.symm)

theorem exists_lift_K
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (L : LeechSystem w) {x y : G} (hl : IsLineTriple a x y)
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hyC : y ∈ Subgroup.centralizer ({w} : Set G))
    (hxyC : x * y ∈ Subgroup.centralizer ({w} : Set G)) (hxQ : x ∉ leechQ w) (hyQ : y ∉ leechQ w)
    (hxyQ : x * y ∉ leechQ w) {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 2)
    (hRx : ∃ p, v = p + co1Act (L.φ ⟨x, hxC⟩) p) (hRy : ∃ p, v = p + co1Act (L.φ ⟨y, hyC⟩) p)
    (hRxy : ∃ p, v = p + co1Act (L.φ ⟨x * y, hxyC⟩) p) :
    ∃ q ∈ leechQ w, L.vec q = v ∧ x * q = q * x ∧ y * q = q * y ∧ x ∈ leechQ q ∧
      y ∈ leechQ q := by
  obtain ⟨q₁, hq₁Q, hq₁v, hxc, hxq, hxq'⟩ := exists_good_lift I hG hw L hl.1 hxC hxQ hv hRx
  obtain ⟨q₂, hq₂Q, hq₂v, hyc, hyq, hyq'⟩ := exists_good_lift I hG hw L hl.2.1 hyC hyQ hv hRy
  obtain ⟨q₃, hq₃Q, hq₃v, hzc, hzq, hzq'⟩ := exists_good_lift I hG hw L hl.2.2 hxyC hxyQ hv hRxy
  have hq₂ : q₂ = q₁ ∨ q₂ = q₁ * w := L.eq_or_eq_mul_z hq₂Q hq₁Q (hq₂v.trans hq₁v.symm)
  have hq₃ : q₃ = q₁ ∨ q₃ = q₁ * w := L.eq_or_eq_mul_z hq₃Q hq₁Q (hq₃v.trans hq₁v.symm)
  have hww : w * w = 1 := L.z_mul_self
  have hq₁w : q₁ * w * w = q₁ := by rw [mul_assoc, hww, mul_one]
  rcases hq₂ with h2 | h2
  · rw [h2] at hyc hyq
    exact ⟨q₁, hq₁Q, hq₁v, hxc, hyc, hxq, hyq⟩
  · exfalso
    rw [h2] at hyq hyq'
    rw [hq₁w] at hyq'
    rcases hq₃ with h3 | h3
    · rw [h3] at hzq
      apply hyq'
      have := mul_mem (inv_mem hxq) hzq
      rwa [inv_mul_cancel_left] at this
    · rw [h3] at hzq
      apply hxq'
      have := mul_mem hzq (inv_mem hyq)
      rwa [mul_inv_cancel_right] at this

theorem mem_leechQ_of_mem_leechQ_four
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) {q : G} (hq : IsConj z₀ q) (hqQ : q ∈ leechQ w) (hqw : q ≠ w) :
    w ∈ leechQ q := by
  by_contra hwQ
  have hI := co1InvolutionFacts
  obtain ⟨Lq⟩ := exists_leechSystem_of_isConj hG hq
  obtain ⟨Lw⟩ := exists_leechSystem_of_isConj hG hw
  have hqC : q * w = w * q := Subgroup.mem_centralizer_singleton_iff.1 (Lw.mem_centralizer hqQ)
  have hwC : w ∈ Subgroup.centralizer ({q} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hqC.symm
  have hw2 : orderOf w = 2 := (orderOf_eq_of_isConj hw).symm.trans hG.2.1
  have hcard := card_centralizer_inf_of_mem_leechQ_four I.sls I.tableV I.leech hG hw hqQ hqw hq
  rw [inf_comm] at hcard
  obtain ⟨hle, -⟩ := Lq.involution_bounds hwC
  have hφ2 : orderOf (Lq.φ ⟨w, hwC⟩) = 2 := Lq.orderOf_φ hwC hw2 hwQ
  obtain ⟨hb, -⟩ := hI.1 _ hφ2
  have : 2 ^ 45 * 3 ^ 3 * 5 * 7 * 11 * 23 ≤ 2 * (2 ^ 37 * 3 ^ 5 * 5 ^ 2 * 7) :=
    le_trans (hcard ▸ hle) (Nat.mul_le_mul_left 2 hb)
  norm_num at this

theorem exists_embed
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hU : Co1FourU)
    (hw : IsConj z₀ w) {x y : G} (hl : IsLineTriple a x y) (hxy : x * y = y * x)
    (hxC : x ∈ Subgroup.centralizer ({w} : Set G)) (hyC : y ∈ Subgroup.centralizer ({w} : Set G))
    (hxQ : x ∉ leechQ w) (hyQ : y ∉ leechQ w) (hxyQ : x * y ∉ leechQ w) :
    ∃ q, IsConj z₀ q ∧ q ≠ w ∧ q ∈ leechQ w ∧ x ∈ leechQ q ∧ y ∈ leechQ q ∧ w ∈ leechQ q := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  have hI := co1InvolutionFacts
  have hxyC : x * y ∈ Subgroup.centralizer ({w} : Set G) := mul_mem hxC hyC
  have hlx := isLeechCentralLift_of_isConj I hG hw hxC hl.1 hxQ
  have hly := isLeechCentralLift_of_isConj I hG hw hyC hl.2.1 hyQ
  have hlxy := isLeechCentralLift_of_isConj I hG hw hxyC hl.2.2 hxyQ
  have hr : IsCo1TwoA (L.φ ⟨x, hxC⟩) := L.isCo1TwoA_phi hI hlx
  have hs : IsCo1TwoA (L.φ ⟨y, hyC⟩) := L.isCo1TwoA_phi hI hly
  have hrs : IsCo1TwoA (L.φ ⟨x * y, hxyC⟩) := L.isCo1TwoA_phi hI hlxy
  have hφ : L.φ ⟨x * y, hxyC⟩ = L.φ ⟨x, hxC⟩ * L.φ ⟨y, hyC⟩ := L.phi_mul hxC hyC
  have hφ' : L.φ ⟨y * x, mul_mem hyC hxC⟩ = L.φ ⟨y, hyC⟩ * L.φ ⟨x, hxC⟩ := L.phi_mul hyC hxC
  have hcomm : L.φ ⟨x, hxC⟩ * L.φ ⟨y, hyC⟩ = L.φ ⟨y, hyC⟩ * L.φ ⟨x, hxC⟩ := by
    rw [← hφ, ← hφ']
    congr 1
    exact Subtype.ext hxy
  rw [hφ] at hrs
  obtain ⟨v, hv4, hRx, hRy, hRxy⟩ := hU _ _ hr hs hcomm hrs
  rw [← hφ] at hRxy
  obtain ⟨q, hqQ, hqv, -, -, hxq, hyq⟩ :=
    exists_lift_K I hG hw L hl hxC hyC hxyC hxQ hyQ hxyQ hv4 hRx hRy hRxy
  have hqB : IsConj z₀ q := isConj_of_mem_typeSet_two I hG hw L ⟨hqQ, hqv ▸ hv4⟩
  have hqw : q ≠ w := by
    intro h
    have h0 : L.vec q = 0 := by rw [h]; exact L.vec_z
    exact Leech.ne_zero_of_mem_co1Orbit hv4 (hqv.symm.trans h0)
  exact ⟨q, hqB, hqw, hqQ, hxq, hyq, mem_leechQ_of_mem_leechQ_four I hG hw hqB hqQ hqw⟩

theorem mem_typeSet_two_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q : G}
    (hq : IsConj z₀ q) (L : LeechSystem q) {u : G} (hu : u ∈ leechQ q) (hB : IsConj z₀ u)
    (hne : u ≠ q) : u ∈ L.typeSet 2 := by
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hB).symm.trans hG.2.1)
  have hu1 : u ≠ 1 := ne_one_of_orderOf ((orderOf_eq_of_isConj hB).symm.trans hG.2.1)
  rcases L.mem_typeSet_zero_or_two hu hu1 hne hu2 with h | h
  · exact absurd (isConj_of_mem_typeSet_zero I hG hq L h)
      (fun hA => hG.not_isConj (hA.trans hB.symm))
  · exact h

end Lifts

section Conj

variable {G : Type} [Group G] {d₀ : B} {a z₀ : G}

structure Embedded (a z₀ q x y w : G) : Prop where
  line : IsLineTriple a x y
  q2B : IsConj z₀ q
  x_mem : x ∈ leechQ q
  y_mem : y ∈ leechQ q
  w_mem : w ∈ leechQ q
  w2B : IsConj z₀ w
  wq : w ≠ q
  wx2B : IsConj z₀ (w * x)
  wy2B : IsConj z₀ (w * y)
  wxy2B : IsConj z₀ (w * x * y)
  wxq : w * x ≠ q
  wyq : w * y ≠ q
  wxyq : w * x * y ≠ q

theorem Embedded.conj {q x y w : G} (h : Embedded a z₀ q x y w) (g : G) :
    Embedded a z₀ (g * q * g⁻¹) (g * x * g⁻¹) (g * y * g⁻¹) (g * w * g⁻¹) := by
  have e1 : g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
  have e2 : g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
  have e3 : g * w * g⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹) = g * (w * x * y) * g⁻¹ := by group
  refine ⟨isLineTriple_conj h.line g, (isConj_conj_iff z₀ g q).2 h.q2B,
    conj_mem_leechQ_conj h.x_mem, conj_mem_leechQ_conj h.y_mem, conj_mem_leechQ_conj h.w_mem,
    (isConj_conj_iff z₀ g w).2 h.w2B, fun hh => h.wq ((conj_eq_conj_iff g w q).1 hh), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [e1]; exact (isConj_conj_iff z₀ g _).2 h.wx2B
  · rw [e2]; exact (isConj_conj_iff z₀ g _).2 h.wy2B
  · rw [e3]; exact (isConj_conj_iff z₀ g _).2 h.wxy2B
  · rw [e1]; exact fun hh => h.wxq ((conj_eq_conj_iff g _ q).1 hh)
  · rw [e2]; exact fun hh => h.wyq ((conj_eq_conj_iff g _ q).1 hh)
  · rw [e3]; exact fun hh => h.wxyq ((conj_eq_conj_iff g _ q).1 hh)

theorem Embedded.fourPattern
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {q x y w : G} (h : Embedded a z₀ q x y w) (L : LeechSystem q) :
    FourPattern (L.vec x) (L.vec y) (L.vec w) := by
  have hxy : x * y ∈ leechQ q := (leechQ q).mul_mem h.x_mem h.y_mem
  have hwx : w * x ∈ leechQ q := (leechQ q).mul_mem h.w_mem h.x_mem
  have hwxy : w * x * y ∈ leechQ q := (leechQ q).mul_mem hwx h.y_mem
  have vxy : L.vec (x * y) = L.vec x + L.vec y := L.vec_mul x h.x_mem y h.y_mem
  have vwx : L.vec (w * x) = L.vec w + L.vec x := L.vec_mul w h.w_mem x h.x_mem
  have vwy : L.vec (w * y) = L.vec w + L.vec y := L.vec_mul w h.w_mem y h.y_mem
  have vwxy : L.vec (w * x * y) = L.vec w + L.vec x + L.vec y := by
    rw [L.vec_mul (w * x) hwx y h.y_mem, vwx]
  have t1 := mem_typeSet_zero_of_isConj I hG h.q2B L h.x_mem h.line.1
  have t2 := mem_typeSet_zero_of_isConj I hG h.q2B L h.y_mem h.line.2.1
  have t3 := mem_typeSet_zero_of_isConj I hG h.q2B L hxy h.line.2.2
  have t4 := mem_typeSet_two_of_isConj I hG h.q2B L h.w_mem h.w2B h.wq
  have t5 := mem_typeSet_two_of_isConj I hG h.q2B L hwx h.wx2B h.wxq
  have t6 := mem_typeSet_two_of_isConj I hG h.q2B L ((leechQ q).mul_mem h.w_mem h.y_mem) h.wy2B
    h.wyq
  have t7 := mem_typeSet_two_of_isConj I hG h.q2B L hwxy h.wxy2B h.wxyq
  have t3' : L.vec x + L.vec y ∈ co1Orbit 0 := by rw [← vxy]; exact t3.2
  have t5' : L.vec w + L.vec x ∈ co1Orbit 2 := by rw [← vwx]; exact t5.2
  have t6' : L.vec w + L.vec y ∈ co1Orbit 2 := by rw [← vwy]; exact t6.2
  have t7' : L.vec w + L.vec x + L.vec y ∈ co1Orbit 2 := by rw [← vwxy]; exact t7.2
  exact ⟨t1.2, t2.2, t3', t4.2, t5', t6', t7'⟩

theorem exists_conj_embedded
    [Finite G] (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hT : Co1FourT) {q x y w x' y' w' : G} (h : Embedded a z₀ q x y w)
    (h' : Embedded a z₀ q x' y' w') :
    ∃ g ∈ Subgroup.centralizer ({q} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧
      g * w * g⁻¹ ∈ cosetSet x' y' w' := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG h.q2B
  have hP := h.fourPattern I hG L
  have hP' := h'.fourPattern I hG L
  obtain ⟨g₀, hg₀x, hg₀y, hg₀w⟩ := hT _ _ _ _ _ _ hP hP'
  obtain ⟨gh, hgh⟩ := L.φ_surj g₀
  have hgC : (gh : G) ∈ Subgroup.centralizer ({q} : Set G) := gh.2
  obtain ⟨hx0', hy0', hxy0', hw4', hwx4', hwy4', hwxy4'⟩ := hP'
  obtain ⟨w₂, hw₂Q, hw₂v, hw₂c, hw₂4⟩ : ∃ w₂ ∈ leechQ q, L.vec w₂ = co1Act g₀ (L.vec w) ∧
      w₂ ∈ cosetSet x' y' w' ∧ L.vec w₂ ∈ co1Orbit 2 := by
    rcases hg₀w with e | e | e | e
    · exact ⟨w', h'.w_mem, e.symm, self_mem_cosetSet x' y' w', hw4'⟩
    · refine ⟨w' * x', (leechQ q).mul_mem h'.w_mem h'.x_mem, ?_,
        mem_cosetSet_iff.2 ⟨x', Or.inr (Or.inl rfl), rfl⟩, ?_⟩
      · rw [L.vec_mul w' h'.w_mem x' h'.x_mem, e]
      · rw [L.vec_mul w' h'.w_mem x' h'.x_mem]; exact hwx4'
    · refine ⟨w' * y', (leechQ q).mul_mem h'.w_mem h'.y_mem, ?_,
        mem_cosetSet_iff.2 ⟨y', Or.inr (Or.inr (Or.inl rfl)), rfl⟩, ?_⟩
      · rw [L.vec_mul w' h'.w_mem y' h'.y_mem, e]
      · rw [L.vec_mul w' h'.w_mem y' h'.y_mem]; exact hwy4'
    · have hwx : w' * x' ∈ leechQ q := (leechQ q).mul_mem h'.w_mem h'.x_mem
      refine ⟨w' * x' * y', (leechQ q).mul_mem hwx h'.y_mem, ?_,
        mem_cosetSet_iff.2 ⟨x' * y', Or.inr (Or.inr (Or.inr rfl)), by rw [mul_assoc]⟩, ?_⟩
      · rw [L.vec_mul (w' * x') hwx y' h'.y_mem, L.vec_mul w' h'.w_mem x' h'.x_mem, e]
      · rw [L.vec_mul (w' * x') hwx y' h'.y_mem, L.vec_mul w' h'.w_mem x' h'.x_mem]
        exact hwxy4'
  have hxv : L.vec ((gh : G) * x * (gh : G)⁻¹) = L.vec x' := by
    rw [L.vec_conj gh x h.x_mem, hgh, hg₀x]
  have hyv : L.vec ((gh : G) * y * (gh : G)⁻¹) = L.vec y' := by
    rw [L.vec_conj gh y h.y_mem, hgh, hg₀y]
  have hwv : L.vec ((gh : G) * w * (gh : G)⁻¹) = L.vec w₂ := by
    rw [L.vec_conj gh w h.w_mem, hgh, hw₂v]
  have hind : LinearIndependent (ZMod 2) fun i : Fin 3 => L.vec (![x', y', w₂] i) := by
    have e : (fun i : Fin 3 => L.vec (![x', y', w₂] i)) = ![L.vec x', L.vec y', L.vec w₂] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    have hne : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 0 → L.vec w₂ ≠ u := by
      intro u hu hh
      exact absurd (Leech.eq_of_mem_co1Orbit hw₂4 (hh ▸ hu)) (by decide)
    refine Leech.linearIndependent_fin_three (Leech.ne_zero_of_mem_co1Orbit hx0')
      (Leech.ne_zero_of_mem_co1Orbit hy0') (Leech.ne_zero_of_mem_co1Orbit hw₂4) ?_
      (fun hh => hne hx0' hh.symm) (fun hh => hne hy0' hh.symm) (fun hh => hne hxy0' hh.symm)
    intro hh
    rw [hh, CFSG.Sporadic.Co1.Module.vec_add_self] at hxy0'
    exact Leech.ne_zero_of_mem_co1Orbit hxy0' rfl
  obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq (a := ![(gh : G) * x * (gh : G)⁻¹,
      (gh : G) * y * (gh : G)⁻¹, (gh : G) * w * (gh : G)⁻¹]) (b := ![x', y', w₂])
    (fun i => by
      fin_cases i
      exacts [L.conj_mem gh h.x_mem, L.conj_mem gh h.y_mem, L.conj_mem gh h.w_mem])
    (fun i => by fin_cases i; exacts [h'.x_mem, h'.y_mem, hw₂Q])
    (fun i => by fin_cases i; exacts [hxv, hyv, hwv]) hind
  have h0 := hpa 0
  have h1 := hpa 1
  have h2 := hpa 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  refine ⟨p * (gh : G), mul_mem (L.mem_centralizer hp) hgC, ?_, ?_, ?_⟩
  · rw [← h0]
    group
  · rw [← h1]
    group
  · have : p * (gh : G) * w * (p * (gh : G))⁻¹ = w₂ := by rw [← h2]; group
    rw [this]
    exact hw₂c

end Conj

end S365

end CFSG.Monster.GMS
