module

public import CFSG.Monster.GMS.S365CentTrans
public import CFSG.Monster.GMS.S365CentDefs
public import CFSG.Monster.GMS.S365Root
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open CFSG.Sporadic.Co1.Module (bil₀)
open CFSG.Sporadic.Co1.Module.Pairs (bil₀_add_smul_fixed)

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_vec_eq_add'
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {w : G}
    (hw : IsConj z₀ w) (L : LeechSystem w) {u c : G} (hcA : IsConj a c) (hucA : IsConj a (u * c))
    (huQ : u ∈ leechQ w) (hcC : c ∈ Subgroup.centralizer ({w} : Set G)) (hcQ : c ∉ leechQ w)
    (huc : u * c = c * u) :
    InIm (L.φ ⟨c, hcC⟩) (L.vec u) := by
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hcC hcA hcQ
  have hucC : u * c ∈ Subgroup.centralizer ({w} : Set G) := mul_mem (L.mem_centralizer huQ) hcC
  have hucQ : u * c ∉ leechQ w := by
    intro h
    apply hcQ
    have := mul_mem (inv_mem huQ) h
    rwa [inv_mul_cancel_left] at this
  have hly₂ := isLeechCentralLift_of_isConj I hG hw hucC hucA hucQ
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hly.mul_self
  have hQ : c⁻¹ * (u * c) ∈ leechQ w := by
    have e : c⁻¹ * (u * c) = u := by
      rw [hci, ← mul_assoc, ← huc, mul_assoc, hly.mul_self, mul_one]
    rw [e]
    exact huQ
  obtain ⟨-, hft, -⟩ := L.central_lift_facts hI hly.mem_centralizer hly.orderOf_eq_two
    hly.not_mem hly.card
  obtain ⟨-, hfx, -⟩ := L.central_lift_facts hI hly₂.mem_centralizer hly₂.orderOf_eq_two
    hly₂.not_mem hly₂.card
  obtain ⟨p, hp, hpx⟩ := L.exists_conj_of_inv_mem hly.mem_centralizer hly₂.mem_centralizer
    hly.mul_self hly₂.mul_self hQ hft hfx
  have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hp
  rcases hpx with h1 | h2
  · refine ⟨L.vec p, ?_⟩
    have hxe : u = p * (c * p⁻¹ * c⁻¹) := by
      calc u = u * c * c⁻¹ := by group
        _ = p * c * p⁻¹ * c⁻¹ := by rw [← h1]
        _ = p * (c * p⁻¹ * c⁻¹) := by group
    have hconj : c * p⁻¹ * c⁻¹ ∈ leechQ w := L.conj_mem' hcC (inv_mem hp)
    calc L.vec u = L.vec (p * (c * p⁻¹ * c⁻¹)) := by rw [← hxe]
      _ = L.vec p + L.vec (c * p⁻¹ * c⁻¹) := L.vec_mul p hp _ hconj
      _ = L.vec p + co1Act (L.φ ⟨c, hcC⟩) (L.vec p⁻¹) := by rw [L.vec_conj' hcC (inv_mem hp)]
      _ = L.vec p + co1Act (L.φ ⟨c, hcC⟩) (L.vec p) := by rw [L.vec_inv hp]
  · exfalso
    have hpw : p * w * p⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hpC
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    set c' := p * c * p⁻¹ with hc'
    have hc'A : IsConj a c' := (isConj_conj_iff a p c).2 hcA
    have hc'Q : c' ∉ leechQ w := L.conj_not_mem hpC hcQ
    have hc'C : c' ∈ Subgroup.centralizer ({w} : Set G) :=
      mul_mem (mul_mem hpC hcC) (inv_mem hpC)
    have hc'w : c' * w = w * c' := Subgroup.mem_centralizer_singleton_iff.1 hc'C
    have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
    have hxy_eq : u * c = w * c' := by
      rw [← h2, ← hc'w]
      calc p * (c * w) * p⁻¹ = (p * c * p⁻¹) * (p * w * p⁻¹) := by group
        _ = c' * w := by rw [hpw]
    have hB : IsConj z₀ (u * c) := by
      rw [hxy_eq]
      exact (isConj_mul_iff I hG hw hc'A hc'w).2 hc'Q
    exact hG.not_isConj (hucA.trans hB.symm)

theorem Embedded.x_comm
    (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    x * q = q * x := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG h.q2B
  exact Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer h.x_mem)

theorem Embedded.y_comm
    (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    y * q = q * y := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG h.q2B
  exact Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer h.y_mem)

theorem Embedded.xy_comm
    (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    x * y * q = q * (x * y) :=
  ((show Commute x q from h.x_comm hG).mul_left (show Commute y q from h.y_comm hG)).eq

omit [Finite G] in
theorem Embedded.sq_q (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    q * q = 1 :=
  mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj h.q2B).symm.trans hG.2.1)

omit [Finite G] in
theorem Embedded.sq_w (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    w * w = 1 :=
  mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj h.w2B).symm.trans hG.2.1)

omit [Finite G] in
theorem Embedded.comm_xw (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    x * w = w * x := by
  have hxx : x * x = 1 := sq_of_isConj_a hG.1.1 h.line.1
  have hwx : w * x * (w * x) = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj h.wx2B).symm.trans hG.2.1)
  exact (mul_comm_of_mul_self_eq_one (h.sq_w hG) hxx hwx).symm

omit [Finite G] in
theorem Embedded.comm_yw (hG : GMSF1Type d₀ a z₀) {q x y w : G} (h : Embedded a z₀ q x y w) :
    y * w = w * y := by
  have hyy : y * y = 1 := sq_of_isConj_a hG.1.1 h.line.2.1
  have hwy : w * y * (w * y) = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj h.wy2B).symm.trans hG.2.1)
  exact (mul_comm_of_mul_self_eq_one (h.sq_w hG) hyy hwy).symm

theorem Embedded.q_mem_pivot
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) : q ∈ leechQ w :=
  mem_leechQ_of_mem_leechQ_four I hG h.q2B h.w2B h.w_mem h.wq

theorem Embedded.x_not_mem_pivot
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) : x ∉ leechQ w :=
  (isConj_mul_iff I hG h.w2B h.line.1 (h.comm_xw hG)).1 h.wx2B

theorem Embedded.y_not_mem_pivot
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) : y ∉ leechQ w :=
  (isConj_mul_iff I hG h.w2B h.line.2.1 (h.comm_yw hG)).1 h.wy2B

omit [Finite G] in
theorem Embedded.x_mem_centralizer_pivot (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) : x ∈ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 (h.comm_xw hG)

omit [Finite G] in
theorem Embedded.y_mem_centralizer_pivot (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) : y ∈ Subgroup.centralizer ({w} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 (h.comm_yw hG)

omit [Finite G] in
theorem comm_of_inIm
    {w q₁ q₂ : G} (L : LeechSystem w) {r : Co1} (hr : r * r = 1)
    (h₁ : q₁ ∈ leechQ w) (h₂ : q₂ ∈ leechQ w) (hv₁ : InIm r (L.vec q₁))
    (hv₂ : InIm r (L.vec q₂)) : q₁ * q₂ = q₂ * q₁ := by
  obtain ⟨p, hp⟩ := hv₁
  obtain ⟨p₂, hp₂⟩ := hv₂
  have hfix : r • L.vec q₂ = L.vec q₂ := by
    have h1 : co1Act r (L.vec q₂) = L.vec q₂ := by
      rw [hp₂, map_add, co1Act_co1Act_of_mul_self hr, add_comm]
    exact h1
  have hb : bil₀ (L.vec q₁) (L.vec q₂) = 0 := by
    rw [hp]
    exact bil₀_add_smul_fixed hfix p
  exact commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff h₁ h₂).2 hb)

theorem inIm_of_mem_leechQ_pair
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {w : G}
    (hw : IsConj z₀ w) (L : LeechSystem w) {q' c : G} (hq' : IsConj z₀ q') (hcA : IsConj a c)
    (hcQ' : c ∈ leechQ q') (hcomm : c * q' = q' * c) (hq'Q : q' ∈ leechQ w)
    (hcC : c ∈ Subgroup.centralizer ({w} : Set G)) (hcQ : c ∉ leechQ w) :
    InIm (L.φ ⟨c, hcC⟩) (L.vec q') :=
  exists_vec_eq_add' I hG hw L hcA (isConj_a_mul_of_mem I hG hq' hcA hcomm hcQ') hq'Q hcC hcQ
    hcomm.symm

theorem nonadj_data
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q q' x y w : G}
    (h : Embedded a z₀ q x y w) (h' : Embedded a z₀ q' x y w) (L : LeechSystem q)
    (hcomm : q' * q = q * q') (hnot : q' ∉ leechQ q) :
    ∃ s' : Co1, IsCo1TwoA s' ∧ InIm s' (L.vec x) ∧ InIm s' (L.vec y) ∧
      ∃ ht : q * q' ∈ Subgroup.centralizer ({q} : Set G), IsConj a (q * q') ∧
        L.φ ⟨q * q', ht⟩ = s' := by
  have hI := co1InvolutionFacts
  have hK := isKlein_of_isLineTriple hG.1.1 h.line
  have hq'sq := h'.sq_q hG
  have hxx : x * x = 1 := hK.sq_x
  have hyy : y * y = 1 := hK.sq_y
  have hq'C : q' ∈ Subgroup.centralizer ({q} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hxC : x ∈ Subgroup.centralizer ({q} : Set G) := L.mem_centralizer h.x_mem
  have hyC : y ∈ Subgroup.centralizer ({q} : Set G) := L.mem_centralizer h.y_mem
  have hqC : q ∈ Subgroup.centralizer ({q} : Set G) := L.mem_centralizer L.z_mem
  have ht₁C : q' * x ∈ Subgroup.centralizer ({q} : Set G) := mul_mem hq'C hxC
  have ht₂C : q' * y ∈ Subgroup.centralizer ({q} : Set G) := mul_mem hq'C hyC
  have hq'x : q' * x * x = q' := by rw [mul_assoc, hxx, mul_one]
  have hq'y : q' * y * y = q' := by rw [mul_assoc, hyy, mul_one]
  have ht₁Q : q' * x ∉ leechQ q := fun hm => hnot (hq'x ▸ mul_mem hm h.x_mem)
  have ht₂Q : q' * y ∉ leechQ q := fun hm => hnot (hq'y ▸ mul_mem hm h.y_mem)
  have hx'A : IsConj a (q' * x) :=
    isConj_a_mul_of_mem I hG h'.q2B h.line.1 (h'.x_comm hG) h'.x_mem
  have hy'A : IsConj a (q' * y) :=
    isConj_a_mul_of_mem I hG h'.q2B h.line.2.1 (h'.y_comm hG) h'.y_mem
  have hly₁ := isLeechCentralLift_of_isConj I hG h.q2B ht₁C hx'A ht₁Q
  have hly₂ := isLeechCentralLift_of_isConj I hG h.q2B ht₂C hy'A ht₂Q
  have hφq : ∀ u : G, u ∈ leechQ q → ∀ (hu : u ∈ Subgroup.centralizer ({q} : Set G)),
      L.φ ⟨q' * u, mul_mem hq'C hu⟩ = L.φ ⟨q', hq'C⟩ := by
    intro u hu huC
    rw [L.phi_mul hq'C huC, (L.φ_ker ⟨u, huC⟩).2 hu, mul_one]
  have hφ₁ : L.φ ⟨q' * x, ht₁C⟩ = L.φ ⟨q', hq'C⟩ := hφq x h.x_mem hxC
  have hφ₂ : L.φ ⟨q' * y, ht₂C⟩ = L.φ ⟨q', hq'C⟩ := hφq y h.y_mem hyC
  have hs'A : IsCo1TwoA (L.φ ⟨q', hq'C⟩) := by
    have := L.isCo1TwoA_phi hI hly₁
    rwa [hφ₁] at this
  have hxcomm₂ : x * (q' * y) = q' * y * x := by
    calc x * (q' * y) = (x * q') * y := (mul_assoc _ _ _).symm
      _ = (q' * x) * y := by rw [h'.x_comm hG]
      _ = q' * (x * y) := mul_assoc _ _ _
      _ = q' * (y * x) := by rw [hK.comm]
      _ = q' * y * x := (mul_assoc _ _ _).symm
  have hyx₂ : y * (q' * x) = q' * x * y := by
    calc y * (q' * x) = (y * q') * x := (mul_assoc _ _ _).symm
      _ = (q' * y) * x := by rw [h'.y_comm hG]
      _ = q' * (y * x) := mul_assoc _ _ _
      _ = q' * (x * y) := by rw [hK.comm]
      _ = q' * x * y := (mul_assoc _ _ _).symm
  have hxIm : InIm (L.φ ⟨q', hq'C⟩) (L.vec x) := by
    have hucA : IsConj a (x * (q' * y)) := by
      have e : x * (q' * y) = q' * (x * y) := by
        rw [← mul_assoc, h'.x_comm hG, mul_assoc]
      rw [e]
      exact isConj_a_mul_of_mem I hG h'.q2B h.line.2.2 (h'.xy_comm hG)
        (mul_mem h'.x_mem h'.y_mem)
    have := exists_vec_eq_add' I hG h.q2B L hy'A hucA h.x_mem ht₂C ht₂Q hxcomm₂
    rwa [hφ₂] at this
  have hyIm : InIm (L.φ ⟨q', hq'C⟩) (L.vec y) := by
    have hucA : IsConj a (y * (q' * x)) := by
      have e : y * (q' * x) = q' * (x * y) := by
        rw [← mul_assoc, h'.y_comm hG, mul_assoc, ← hK.comm]
      rw [e]
      exact isConj_a_mul_of_mem I hG h'.q2B h.line.2.2 (h'.xy_comm hG)
        (mul_mem h'.x_mem h'.y_mem)
    have := exists_vec_eq_add' I hG h.q2B L hx'A hucA h.y_mem ht₁C ht₁Q hyx₂
    rwa [hφ₁] at this
  have ht₁sq : q' * x * (q' * x) = 1 := mul_mul_self_eq_one hq'sq hxx (h'.x_comm hG).symm
  have hinv : (q' * x)⁻¹ * q' ∈ leechQ q := by
    have e : (q' * x)⁻¹ * q' = x⁻¹ := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    rw [e]
    exact inv_mem h.x_mem
  have hft : ∀ p ∈ leechQ q, L.vec p ∈ co1Fix (L.φ ⟨q' * x, ht₁C⟩) →
      q' * x * p = p * (q' * x) := fun p hp hfix => L.commute_of_vec_mem_co1Fix hI hly₁ hp hfix
  have hfx : ∀ p ∈ leechQ q, L.vec p ∈ co1Fix (L.φ ⟨q', hq'C⟩) → q' * p = p * q' := by
    intro p hp hfix
    have hfix₁ : L.vec p ∈ co1Fix (L.φ ⟨q' * x, ht₁C⟩) := by rw [hφ₁]; exact hfix
    have h1 := hft p hp hfix₁
    have h2 : x * p = p * x := by
      obtain ⟨v, hv⟩ := hxIm
      have hb : bil₀ (L.vec x) (L.vec p) = 0 := by
        rw [hv]
        exact bil₀_add_smul_fixed hfix v
      exact commutatorElement_eq_one_iff_mul_comm.1 ((L.comm_eq_one_iff h.x_mem hp).2 hb)
    calc q' * p = q' * x * x * p := by rw [hq'x]
      _ = q' * x * (x * p) := mul_assoc _ _ _
      _ = q' * x * (p * x) := by rw [h2]
      _ = q' * x * p * x := (mul_assoc _ _ _).symm
      _ = p * (q' * x) * x := by rw [h1]
      _ = p * (q' * x * x) := mul_assoc _ _ _
      _ = p * q' := by rw [hq'x]
  obtain ⟨p, hp, hpx⟩ := L.exists_conj_of_inv_mem (t := q' * x) (x := q') ht₁C hq'C ht₁sq hq'sq
    hinv hft hfx
  have hqq : p * q * p⁻¹ = q := by
    rw [L.extraspecial.central p hp]
    group
  rcases hpx with h1 | h2
  · exfalso
    have hA : IsConj a q' := by
      have := (isConj_conj_iff a p (q' * x)).2 hx'A
      rwa [h1] at this
    exact hG.not_isConj (hA.trans h'.q2B.symm)
  · have e : p * (q' * x * q) * p⁻¹ = (p * (q' * x) * p⁻¹) * q := by
      calc p * (q' * x * q) * p⁻¹ = (p * (q' * x) * p⁻¹) * (p * q * p⁻¹) := by group
        _ = (p * (q' * x) * p⁻¹) * q := by rw [hqq]
    have e2 : q' = (p * (q' * x) * p⁻¹) * q := by rw [← e]; exact h2.symm
    have hqq' : q * q' = p * (q' * x) * p⁻¹ := by
      rw [← hcomm]
      calc q' * q = (p * (q' * x) * p⁻¹) * q * q := by rw [← e2]
        _ = p * (q' * x) * p⁻¹ := by rw [mul_assoc, h.sq_q hG, mul_one]
    have ht'C : q * q' ∈ Subgroup.centralizer ({q} : Set G) := mul_mem hqC hq'C
    have hA : IsConj a (q * q') := by
      rw [hqq']
      exact (isConj_conj_iff a p (q' * x)).2 hx'A
    have hφ' : L.φ ⟨q * q', ht'C⟩ = L.φ ⟨q', hq'C⟩ := by
      rw [L.phi_mul hqC hq'C, (L.φ_ker ⟨q, hqC⟩).2 L.z_mem, one_mul]
    exact ⟨L.φ ⟨q', hq'C⟩, hs'A, hxIm, hyIm, ht'C, hA, hφ'⟩

theorem Embedded.adj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hNo : Co1NoPatternIm)
    {q q' x y w : G} (h : Embedded a z₀ q x y w) (h' : Embedded a z₀ q' x y w) :
    q' * q = q * q' ∧ q' ∈ leechQ q := by
  obtain ⟨Lw⟩ := exists_leechSystem_of_isConj hG h.w2B
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG h.q2B
  have hK := isKlein_of_isLineTriple hG.1.1 h.line
  have hqw := h.q_mem_pivot I hG
  have hq'w := h'.q_mem_pivot I hG
  have hxC := h.x_mem_centralizer_pivot hG
  have hxQ := h.x_not_mem_pivot I hG
  have hr2 : Lw.φ ⟨x, hxC⟩ * Lw.φ ⟨x, hxC⟩ = 1 := Lw.φ_mul_self hxC hK.sq_x
  have hIm : InIm (Lw.φ ⟨x, hxC⟩) (Lw.vec q) :=
    inIm_of_mem_leechQ_pair I hG h.w2B Lw h.q2B h.line.1 h.x_mem (h.x_comm hG) hqw hxC hxQ
  have hIm' : InIm (Lw.φ ⟨x, hxC⟩) (Lw.vec q') :=
    inIm_of_mem_leechQ_pair I hG h.w2B Lw h'.q2B h.line.1 h'.x_mem (h'.x_comm hG) hq'w hxC hxQ
  have hcomm : q' * q = q * q' := comm_of_inIm Lw hr2 hq'w hqw hIm' hIm
  refine ⟨hcomm, ?_⟩
  by_contra hnot
  obtain ⟨s', hs'A, hxIm, hyIm, ht'C, ht'A, hφt'⟩ := nonadj_data I hG h h' L hcomm hnot
  have ht'Q : q * q' ∉ leechQ q := fun hm => hnot (by
    have := mul_mem (inv_mem L.z_mem) hm
    rwa [inv_mul_cancel_left] at this)
  have ht'w : q * q' ∈ leechQ w := mul_mem hqw hq'w
  have ht'wc : q * q' * w = w * (q * q') :=
    Subgroup.mem_centralizer_singleton_iff.1 (Lw.mem_centralizer ht'w)
  have hwt'A : IsConj a (w * (q * q')) := isConj_a_mul_of_mem I hG h.w2B ht'A ht'wc ht'w
  have hwIm := exists_vec_eq_add' I hG h.q2B L ht'A hwt'A h.w_mem ht'C ht'Q ht'wc.symm
  rw [hφt'] at hwIm
  exact hNo s' hs'A _ _ _ (h.fourPattern I hG L) hxIm hyIm hwIm

omit [Finite G] in
theorem Embedded.klein_mem {q x y w c : G} (h : Embedded a z₀ q x y w) (hc : InKlein x y c) :
    c ∈ leechQ q := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact h.x_mem
  · exact h.y_mem
  · exact mul_mem h.x_mem h.y_mem

omit [Finite G] in
theorem InKlein.vec {q x y c : G} (L : LeechSystem q) (hx : x ∈ leechQ q) (hy : y ∈ leechQ q)
    (hc : InKlein x y c) : InK (L.vec x) (L.vec y) (L.vec c) := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl L.vec_one
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (L.vec_mul _ hx _ hy)))

omit [Finite G] in
theorem Embedded.wc_data {q x y w c : G} (h : Embedded a z₀ q x y w) (hc : InKlein x y c) :
    IsConj z₀ (w * c) ∧ w * c ≠ q := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact ⟨by rw [mul_one]; exact h.w2B, by rw [mul_one]; exact h.wq⟩
  · exact ⟨h.wx2B, h.wxq⟩
  · exact ⟨h.wy2B, h.wyq⟩
  · exact ⟨by rw [← mul_assoc]; exact h.wxy2B, by rw [← mul_assoc]; exact h.wxyq⟩

theorem ne_add_of_mem_o0
    {a b ω ν κ : Fin 24 → ZMod 2} (hP : FourPattern a b ω)
    (hκ : InK a b κ) (h : ν + a ∈ co1Orbit 0) : ν ≠ ω + κ := by
  intro he
  have ha : InK a b a := Or.inr (Or.inl rfl)
  have h2 : ν + a ∈ co1Orbit 2 := by
    rw [he, add_assoc]
    exact mem_o2_of_coset hP (CosetEq.add_klein (hκ.add ha))
  exact absurd (Leech.eq_of_mem_co1Orbit h h2) (by decide)

theorem Pat0.ne_add
    {a b ω ν κ : Fin 24 → ZMod 2} (hP : FourPattern a b ω) (hν : Pat0 a b ω ν)
    (hκ : InK a b κ) : ν ≠ ω + κ :=
  ne_add_of_mem_o0 hP hκ hν.2.1

theorem Embedded.pat0
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q q₁ x y w : G}
    (h : Embedded a z₀ q x y w) (h₁ : Embedded a z₀ q₁ x y w) (L : LeechSystem q)
    (hne : q₁ ≠ q) (hQ : q₁ ∈ leechQ q) :
    Pat0 (L.vec x) (L.vec y) (L.vec w) (L.vec q₁) := by
  have hP := h.fourPattern I hG L
  have hT1 : q₁ ∈ L.typeSet 2 := mem_typeSet_two_of_isConj I hG h.q2B L hQ h₁.q2B hne
  have hxyQ : x * y ∈ leechQ q := mul_mem h.x_mem h.y_mem
  have hA : ∀ c : G, IsConj a c → c ∈ leechQ q → c ∈ leechQ q₁ → c * q₁ = q₁ * c →
      L.vec q₁ + L.vec c ∈ co1Orbit 0 := by
    intro c hcA hcQ hcQ₁ hcc
    have hmem : q₁ * c ∈ leechQ q := mul_mem hQ hcQ
    have hT := mem_typeSet_zero_of_isConj I hG h.q2B L hmem
      (isConj_a_mul_of_mem I hG h₁.q2B hcA hcc hcQ₁)
    have := hT.2
    rwa [L.vec_mul q₁ hQ c hcQ] at this
  have hPx : L.vec q₁ + L.vec x ∈ co1Orbit 0 :=
    hA x h.line.1 h.x_mem h₁.x_mem (h₁.x_comm hG)
  have hPy : L.vec q₁ + L.vec y ∈ co1Orbit 0 :=
    hA y h.line.2.1 h.y_mem h₁.y_mem (h₁.y_comm hG)
  have hPxy : L.vec q₁ + L.vec x + L.vec y ∈ co1Orbit 0 := by
    have := hA (x * y) h.line.2.2 hxyQ (mul_mem h₁.x_mem h₁.y_mem) (h₁.xy_comm hG)
    rwa [L.vec_mul x h.x_mem y h.y_mem, ← add_assoc] at this
  have hW : ∀ c : G, InKlein x y c → L.vec q₁ + (L.vec w + L.vec c) ∈ co1Orbit 2 := by
    intro c hc
    have hcQ : c ∈ leechQ q := h.klein_mem hc
    have hcQ₁ : c ∈ leechQ q₁ := h₁.klein_mem hc
    obtain ⟨hB, hneq⟩ := h₁.wc_data hc
    obtain ⟨L₁⟩ := exists_leechSystem_of_isConj hG h₁.q2B
    have hwcQ₁ : w * c ∈ leechQ q₁ := mul_mem h₁.w_mem hcQ₁
    have hT : w * c ∈ L₁.typeSet 2 := mem_typeSet_two_of_isConj I hG h₁.q2B L₁ hwcQ₁ hB hneq
    have hB' : IsConj z₀ (w * c * q₁) :=
      isConj_of_mem_typeSet_two I hG h₁.q2B L₁ (L₁.mul_z_mem_typeSet hT)
    have hwcQ : w * c ∈ leechQ q := mul_mem h.w_mem hcQ
    have hQ' : w * c * q₁ ∈ leechQ q := mul_mem hwcQ hQ
    have hne' : w * c * q₁ ≠ q := by
      intro heq
      have hv : L.vec (w * c * q₁) = 0 := by rw [heq]; exact L.vec_z
      rw [L.vec_mul (w * c) hwcQ q₁ hQ, L.vec_mul w h.w_mem c hcQ] at hv
      have h1 : L.vec q₁ = L.vec w + L.vec c := by
        calc L.vec q₁ = (L.vec w + L.vec c) + ((L.vec w + L.vec c) + L.vec q₁) :=
              (vec_add_add_left _ _).symm
          _ = L.vec w + L.vec c := by rw [hv, add_zero]
      exact ne_add_of_mem_o0 hP (InKlein.vec L h.x_mem h.y_mem hc) hPx h1
    have hTq : w * c * q₁ ∈ L.typeSet 2 := mem_typeSet_two_of_isConj I hG h.q2B L hQ' hB' hne'
    have := hTq.2
    rw [L.vec_mul (w * c) hwcQ q₁ hQ, L.vec_mul w h.w_mem c hcQ] at this
    rwa [add_comm (L.vec q₁) _]
  refine ⟨hT1.2, hPx, hPy, hPxy, ?_, ?_, ?_, ?_⟩
  · have := hW 1 (Or.inl rfl)
    rwa [L.vec_one, add_zero] at this
  · have := hW x (Or.inr (Or.inl rfl))
    rwa [← add_assoc] at this
  · have := hW y (Or.inr (Or.inr (Or.inl rfl)))
    rwa [← add_assoc] at this
  · have := hW (x * y) (Or.inr (Or.inr (Or.inr rfl)))
    rwa [L.vec_mul x h.x_mem y h.y_mem, ← add_assoc, ← add_assoc] at this

theorem Embedded.mul
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hNo : Co1NoPatternIm)
    {q₁ q₂ x y w : G} (h₁ : Embedded a z₀ q₁ x y w) (h₂ : Embedded a z₀ q₂ x y w)
    (hne : q₁ ≠ q₂) : Embedded a z₀ (q₁ * q₂) x y w := by
  obtain ⟨hcomm, hQ⟩ := h₁.adj I hG hNo h₂
  obtain ⟨L₁⟩ := exists_leechSystem_of_isConj hG h₁.q2B
  have hP₁ := h₁.fourPattern I hG L₁
  have hpat := h₁.pat0 I hG h₂ L₁ hne.symm hQ
  have hq₂T : q₂ ∈ L₁.typeSet 2 := ⟨hQ, hpat.1⟩
  have hq₁q₂B : IsConj z₀ (q₁ * q₂) := by
    have hB := isConj_of_mem_typeSet_two I hG h₁.q2B L₁ (L₁.mul_z_mem_typeSet hq₂T)
    rwa [hcomm] at hB
  have hvec : L₁.vec (q₁ * q₂) = L₁.vec q₂ := by
    rw [← hcomm]
    exact L₁.vec_mul_z hQ
  have hQ₂w : q₂ ∈ leechQ w := h₂.q_mem_pivot I hG
  have hQ₁w : q₁ ∈ leechQ w := h₁.q_mem_pivot I hG
  have hne_klein : ∀ {c : G}, InKlein x y c → w * c ≠ q₁ * q₂ := by
    intro c hc heq
    have hcQ : c ∈ leechQ q₁ := h₁.klein_mem hc
    have := congrArg L₁.vec heq
    rw [L₁.vec_mul w h₁.w_mem c hcQ, hvec] at this
    exact Pat0.ne_add hP₁ hpat (InKlein.vec L₁ h₁.x_mem h₁.y_mem hc) this.symm
  have key : ∀ c : G, IsConj a c → c ∈ leechQ q₁ → c * q₁ = q₁ * c → c * q₂ = q₂ * c →
      L₁.vec q₂ + L₁.vec c ∈ co1Orbit 0 → c ∈ leechQ (q₁ * q₂) := by
    intro c hcA hc₁ hc₁c hc₂c hv
    have hcomm_c : c * (q₁ * q₂) = q₁ * q₂ * c := by
      calc c * (q₁ * q₂) = (c * q₁) * q₂ := (mul_assoc _ _ _).symm
        _ = (q₁ * c) * q₂ := by rw [hc₁c]
        _ = q₁ * (c * q₂) := mul_assoc _ _ _
        _ = q₁ * (q₂ * c) := by rw [hc₂c]
        _ = q₁ * q₂ * c := (mul_assoc _ _ _).symm
    refine (mem_leechQ_iff_isConj_mul I hG hq₁q₂B hcA hcomm_c).2 ?_
    have hT : q₂ * c ∈ L₁.typeSet 0 := (L₁.mul_mem_typeSet_iff hQ hc₁).2 hv
    have hA := isConj_of_mem_typeSet_zero I hG h₁.q2B L₁ (L₁.mul_z_mem_typeSet hT)
    have e : q₁ * q₂ * c = q₂ * c * q₁ := by
      calc q₁ * q₂ * c = q₂ * q₁ * c := by rw [hcomm]
        _ = q₂ * (q₁ * c) := mul_assoc _ _ _
        _ = q₂ * (c * q₁) := by rw [hc₁c]
        _ = q₂ * c * q₁ := (mul_assoc _ _ _).symm
    rw [e]
    exact hA
  have hw1 : q₁ * q₂ ≠ w := fun heq =>
    hne_klein (c := 1) (Or.inl rfl) (by rw [mul_one]; exact heq.symm)
  refine ⟨h₁.line, hq₁q₂B, ?_, ?_, ?_, h₁.w2B, fun heq => hw1 heq.symm, h₁.wx2B, h₁.wy2B,
    h₁.wxy2B, hne_klein (Or.inr (Or.inl rfl)), hne_klein (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
  · exact key x h₁.line.1 h₁.x_mem (h₁.x_comm hG) (h₂.x_comm hG) hpat.2.1
  · exact key y h₁.line.2.1 h₁.y_mem (h₁.y_comm hG) (h₂.y_comm hG) hpat.2.2.1
  · exact mem_leechQ_of_mem_leechQ_four I hG h₁.w2B hq₁q₂B (mul_mem hQ₁w hQ₂w) hw1
  · intro heq
    exact hne_klein (c := x * y) (Or.inr (Or.inr (Or.inr rfl))) (by rw [← mul_assoc]; exact heq)

end S365

end CFSG.Monster.GMS
