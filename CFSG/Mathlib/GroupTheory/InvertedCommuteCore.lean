module

public import Mathlib.GroupTheory.PGroup
import TauCeti.GroupTheory.Commutator

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

private lemma invCoreAux_inv_n (t : MulAut G) (ht : ∀ g, t (t g) = g) (g : G) :
    t (g * (t g)⁻¹) = (g * (t g)⁻¹)⁻¹ := by
  rw [map_mul, map_inv, ht, mul_inv_rev, inv_inv]

private lemma invCoreAux_commute_of_mem {x y z : G}
    (hx : Commute z x) (hy : Commute z y) :
    ∀ h ∈ Subgroup.closure {x, y}, Commute z h := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hx
    · exact hy
  | one => exact Commute.one_right z
  | mul a b _ _ iha ihb => exact iha.mul_right ihb
  | inv a _ iha => exact iha.inv_right

private lemma invCoreAux_commute_commutator {z a b : G}
    (ha : Commute z a) (hb : Commute z b) : Commute z ⁅a, b⁆ := by
  rw [commutatorElement_def]
  exact (((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right)

private lemma invCoreAux_conj_eq {u w : G} (h : Commute u w) : u * w * u⁻¹ = w := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma invCoreAux_t_eq (t : MulAut G) (g : G) :
    t g = (g * (t g)⁻¹)⁻¹ * g := by
  group

private lemma invCoreAux_commutator_mul_right {a w b : G}
    (hwa : Commute w a) (hwb : Commute w b) : ⁅a, w * b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr hwa.symm, one_mul]
  exact invCoreAux_conj_eq (invCoreAux_commute_commutator hwa hwb)

private lemma invCoreAux_commute_sq {x d u : G} (hux : Commute u x) (hud : Commute u d)
    (h : x⁻¹ * d * x = d⁻¹ * u) : Commute (x ^ 2) d := by
  have hxux : x⁻¹ * u * x = u := by
    rw [show x⁻¹ * u * x = x⁻¹ * (u * x) by group, hux.eq, ← mul_assoc,
      inv_mul_cancel, one_mul]
  have hconj : x⁻¹ * (x⁻¹ * d * x) * x = d := by
    rw [h]
    calc x⁻¹ * (d⁻¹ * u) * x
        = (x⁻¹ * d⁻¹ * x) * (x⁻¹ * u * x) := by group
      _ = (x⁻¹ * d * x)⁻¹ * u := by
            rw [hxux, show x⁻¹ * d⁻¹ * x = (x⁻¹ * d * x)⁻¹ by group]
      _ = (d⁻¹ * u)⁻¹ * u := by rw [h]
      _ = d := by
            rw [show (d⁻¹ * u)⁻¹ = u⁻¹ * d by group,
              show u⁻¹ * d * u = u⁻¹ * (d * u) by group, ← hud.eq]
            group
  have hxx : (x * x)⁻¹ * d * (x * x) = d := by
    rw [show (x * x)⁻¹ * d * (x * x) = x⁻¹ * (x⁻¹ * d * x) * x by group]
    exact hconj
  rw [pow_two, commute_iff_eq]
  have hh := congrArg (fun z => (x * x) * z) hxx
  simpa [mul_assoc] using hh.symm

omit [Fact (Nat.Prime p)] in
private lemma invCoreAux_x_eq (hpodd : Odd p) (x : G) :
    x = (x ^ 2) ^ ((p + 1) / 2) * (x ^ p)⁻¹ := by
  obtain ⟨m, hm⟩ := hpodd
  have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  rw [← pow_mul, h2, pow_succ]
  rw [show x ^ p * x * (x ^ p)⁻¹ = x ^ p * (x * (x ^ p)⁻¹) by group,
    (Commute.self_pow x p).inv_right.eq]
  group

private lemma invCoreAux_pow_sq {d : G} {k : ℕ} (hk : orderOf d = 2 * k + 1) :
    (d * d) ^ ((orderOf d + 1) / 2) = d := by
  have h2 : 2 * ((orderOf d + 1) / 2) = orderOf d + 1 := by omega
  rw [← pow_two, ← pow_mul, h2, pow_succ, pow_orderOf_eq_one, one_mul]

theorem commute_commutator_of_inv_of_le (hp2 : p ≠ 2) (hG : IsPGroup p G) (t : MulAut G)
    (ht : ∀ g, t (t g) = g) (hcen : ∀ g : G, g ^ p = 1 → g ∈ Subgroup.center G)
    {x y : G} (hx : t x = x⁻¹) (hy : t y = y⁻¹) (M : Subgroup G)
    (hpow : ∀ g ∈ Subgroup.closure {x, y}, g ^ p ∈ M)
    (hcomm : ∀ a ∈ Subgroup.closure {x, y}, ∀ b ∈ Subgroup.closure {x, y}, ⁅a, b⁆ ∈ M)
    (hM : ∀ g ∈ M, t g = g⁻¹ → Commute g x ∧ Commute g y) :
    Commute x ⁅x, y⁆ := by
  classical
  have hpprime : p.Prime := Fact.out
  have hpodd : Odd p := hpprime.odd_of_ne_two hp2
  have hxH : x ∈ Subgroup.closure {x, y} := Subgroup.subset_closure (by simp)
  have hyH : y ∈ Subgroup.closure {x, y} := Subgroup.subset_closure (by simp)
  have hxiH : x⁻¹ ∈ Subgroup.closure {x, y} := (Subgroup.closure _).inv_mem hxH
  have hyiH : y⁻¹ ∈ Subgroup.closure {x, y} := (Subgroup.closure _).inv_mem hyH
  set c : G := ⁅x, y⁆ with hc
  have hcH : c ∈ Subgroup.closure {x, y} := by
    rw [hc]
    exact Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hxH hyH)
  have hcM : c ∈ M := by
    rw [hc]
    exact hcomm x hxH y hyH
  have htc_eq : t c = ⁅x⁻¹, y⁻¹⁆ := by
    rw [hc, map_commutatorElement, hx, hy]
  have htcH : t c ∈ Subgroup.closure {x, y} := by
    rw [htc_eq]
    exact Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hxiH hyiH)
  have htcM : t c ∈ M := by
    rw [htc_eq]
    exact hcomm x⁻¹ hxiH y⁻¹ hyiH
  set d : G := ⁅x, c⁆ with hd
  have hdH : d ∈ Subgroup.closure {x, y} := by
    rw [hd]
    exact Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hxH hcH)
  have hdM : d ∈ M := by
    rw [hd]
    exact hcomm x hxH c hcH
  have htd_eq : t d = ⁅x⁻¹, t c⁆ := by
    rw [hd, map_commutatorElement, hx]
  have htdH : t d ∈ Subgroup.closure {x, y} := by
    rw [htd_eq]
    exact Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hxiH htcH)
  have htdM : t d ∈ M := by
    rw [htd_eq]
    exact hcomm x⁻¹ hxiH (t c) htcH
  set nc : G := c * (t c)⁻¹ with hnc
  set nd : G := d * (t d)⁻¹ with hnd
  have hncM : nc ∈ M := by
    rw [hnc]
    exact M.mul_mem hcM (M.inv_mem htcM)
  have hndM : nd ∈ M := by
    rw [hnd]
    exact M.mul_mem hdM (M.inv_mem htdM)
  have hnc_inv : t nc = nc⁻¹ := by
    rw [hnc]
    exact invCoreAux_inv_n t ht c
  have hnd_inv : t nd = nd⁻¹ := by
    rw [hnd]
    exact invCoreAux_inv_n t ht d
  obtain ⟨hncx, hncy⟩ := hM nc hncM hnc_inv
  obtain ⟨hndx, hndy⟩ := hM nd hndM hnd_inv
  have hxpM : x ^ p ∈ M := hpow x hxH
  have hxp_inv : t (x ^ p) = (x ^ p)⁻¹ := by
    rw [map_pow, hx, inv_pow]
  obtain ⟨hxpx, hxpy⟩ := hM (x ^ p) hxpM hxp_inv
  have hncH : ∀ h ∈ Subgroup.closure {x, y}, Commute nc h :=
    invCoreAux_commute_of_mem hncx hncy
  have hndH : ∀ h ∈ Subgroup.closure {x, y}, Commute nd h :=
    invCoreAux_commute_of_mem hndx hndy
  have hxpH : ∀ h ∈ Subgroup.closure {x, y}, Commute (x ^ p) h :=
    invCoreAux_commute_of_mem hxpx hxpy
  have htc_val : t c = nc⁻¹ * c := by
    rw [hnc]
    exact invCoreAux_t_eq t c
  have hxd' : x⁻¹ * c * (x⁻¹)⁻¹ * c⁻¹ = x⁻¹ * d⁻¹ * x := by
    rw [hd, commutatorElement_def]
    group
  have htd_val : t d = x⁻¹ * d⁻¹ * x := by
    rw [htd_eq, htc_val,
      invCoreAux_commutator_mul_right (hncH x hxH).inv_left.inv_right
        (hncH c hcH).inv_left,
      commutatorElement_def, hxd']
  have hnd_val : t d = nd⁻¹ * d := by
    rw [hnd]
    exact invCoreAux_t_eq t d
  have hxddx : x⁻¹ * d * x = d⁻¹ * nd := by
    have h1 : nd⁻¹ * d = x⁻¹ * d⁻¹ * x := by rw [← hnd_val, htd_val]
    have h2 := congrArg Inv.inv h1
    simpa [mul_inv_rev, inv_inv, mul_assoc] using h2.symm
  have hx2d : Commute (x ^ 2) d := invCoreAux_commute_sq hndx (hndH d hdH) hxddx
  have hxp_d : Commute (x ^ p) d := hxpH d hdH
  have hxd : Commute x d := by
    rw [invCoreAux_x_eq hpodd x]
    exact (hx2d.pow_left _).mul_left hxp_d.inv_left
  have hxdx : x⁻¹ * d * x = d := by
    rw [show x⁻¹ * d * x = x⁻¹ * (d * x) by group, ← hxd.eq]
    group
  have hnd_eq : nd = d * d := by
    have h : d⁻¹ * nd = d := by rw [← hxddx, hxdx]
    calc nd = d * (d⁻¹ * nd) := by group
      _ = d * d := by rw [h]
  have hodd : Odd (orderOf d) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hG) d
    rw [hk]
    exact hpodd.pow
  obtain ⟨kd, hkd⟩ := hodd
  have hd_pow : nd ^ ((orderOf d + 1) / 2) = d := by
    rw [hnd_eq]
    exact invCoreAux_pow_sq hkd
  have hdy : Commute d y := by
    rw [← hd_pow]
    exact (hndH y hyH).pow_left _
  have hdH_comm : ∀ h ∈ Subgroup.closure {x, y}, Commute d h :=
    invCoreAux_commute_of_mem hxd.symm hdy
  have hcd : Commute c d := (hdH_comm c hcH).symm
  have htable : ⁅x ^ p, y⁆ = c ^ p * d ^ p.choose 2 := by
    have h1 : Commute x ⁅x, ⁅x, y⁆⁆ := by
      rw [← hc, ← hd]
      exact hxd
    have h2 : Commute ⁅x, y⁆ ⁅x, ⁅x, y⁆⁆ := by
      rw [← hc, ← hd]
      exact hcd
    have h := TauCeti.commutatorElement_pow_left_of_commute (a := x) (b := y) h1 h2 p
    simpa [← hc, ← hd] using h
  have hzero : ⁅x ^ p, y⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hxpy
  have hmain : c ^ p * d ^ p.choose 2 = 1 := by
    rw [← htable, hzero]
  obtain ⟨m, hm⟩ := hpodd
  have h2dvd : 2 ∣ p - 1 := ⟨m, by omega⟩
  have hchoose : p.choose 2 = p * ((p - 1) / 2) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_assoc (k := 2) (n := p - 1) p h2dvd
  set j : ℕ := (p - 1) / 2 with hj
  set w : G := c * d ^ j with hw
  have hcdj : Commute c (d ^ j) := hcd.pow_right j
  have hwp : w ^ p = 1 := by
    have h1 : w ^ p = c ^ p * (d ^ j) ^ p := by rw [hw, hcdj.mul_pow p]
    have h2 : c ^ p * (d ^ j) ^ p = c ^ p * d ^ (j * p) := by rw [← pow_mul]
    have h3 : c ^ p * d ^ (j * p) = 1 := by
      rw [Nat.mul_comm j p, show p * j = p * ((p - 1) / 2) by rw [hj], ← hchoose]
      exact hmain
    rw [h1, h2, h3]
  have hw_center : w ∈ Subgroup.center G := hcen w hwp
  have hxw : Commute x w := (Subgroup.mem_center_iff.mp hw_center) x
  have hxwe : Commute x (w * (d ^ j)⁻¹) :=
    hxw.mul_right (hxd.pow_right j).inv_right
  have hc_eq : c = w * (d ^ j)⁻¹ := by
    rw [hw]
    group
  have hd1 : d = 1 := by
    rw [hd, hc_eq]
    exact commutatorElement_eq_one_iff_commute.mpr hxwe
  have hxc : Commute x c :=
    commutatorElement_eq_one_iff_commute.mp (by rw [← hd]; exact hd1)
  simpa [hc] using hxc

end CFSG.GroupTheory

end
