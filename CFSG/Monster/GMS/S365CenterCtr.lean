module

public import CFSG.Monster.GMS.S365CenterLin
public import CFSG.Monster.GMS.Leech.Forms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.Module (bil₀)
open scoped commutatorElement

namespace S365

section Center

variable {G : Type*} [Group G]

private theorem zmod2_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem mem_ext_of_central
    {u : G} (L : LeechSystem u) {x y t g₀ h : G} (hxQ : x ∈ leechQ u)
    (hyQ : y ∈ leechQ u) (htQ : t ∈ leechQ u) (hg₀x : g₀ * x = x * g₀) (hg₀y : g₀ * y = y * g₀)
    (hg₀t : g₀ * t = t * g₀) (hg₀u : g₀ * u ≠ u * g₀) (hhx : h * x = x * h) (hhy : h * y = y * h)
    (hht : h * t = t * h)
    (hcen : ∀ g : G, g * x = x * g → g * y = y * g → g * t = t * g → h * g = g * h) :
    h ∈ ({1, x, y, t, x * y, x * t, y * t, x * y * t} : Set G) := by
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hxQ)
  have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hyQ)
  have htu : t * u = u * t := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer htQ)
  have hhu : h * u = u * h := hcen u hxu.symm hyu.symm htu.symm
  have hhC : h ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hhu
  let e : Fin 3 → Fin 24 → ZMod 2 := ![L.vec x, L.vec y, L.vec t]
  have hperp : ∀ a : Fin 24 → ZMod 2, (∀ i, bil₀ a (e i) = 0) →
      ∃ v ∈ leechQ u, L.vec v = a ∧ h * v = v * h := by
    intro a ha
    obtain ⟨v, hvQ, hva⟩ := L.vec_surj a
    have hvx : v * x = x * v := commutatorElement_eq_one_iff_mul_comm.1
      ((L.comm_eq_one_iff hvQ hxQ).2 (by rw [hva]; exact ha 0))
    have hvy : v * y = y * v := commutatorElement_eq_one_iff_mul_comm.1
      ((L.comm_eq_one_iff hvQ hyQ).2 (by rw [hva]; exact ha 1))
    have hvt : v * t = t * v := commutatorElement_eq_one_iff_mul_comm.1
      ((L.comm_eq_one_iff hvQ htQ).2 (by rw [hva]; exact ha 2))
    exact ⟨v, hvQ, hva, hcen v hvx hvy hvt⟩
  have hfix : ∀ i, co1Act (L.φ ⟨h, hhC⟩) (e i) = e i := by
    intro i
    have key : ∀ q : G, q ∈ leechQ u → h * q = q * h →
        co1Act (L.φ ⟨h, hhC⟩) (L.vec q) = L.vec q := by
      intro q hq hhq
      rw [← L.vec_conj' hhC hq, mul_inv_eq_iff_eq_mul.2 hhq]
    fin_cases i
    · exact key x hxQ hhx
    · exact key y hyQ hhy
    · exact key t htQ hht
  have hW : ∀ v, (∀ i, bil₀ v (e i) = 0) → co1Act (L.φ ⟨h, hhC⟩) v = v := by
    intro v hv
    obtain ⟨q, hqQ, hqv, hhq⟩ := hperp v hv
    rw [← hqv, ← L.vec_conj' hhC hqQ, mul_inv_eq_iff_eq_mul.2 hhq]
  have hA1 : L.φ ⟨h, hhC⟩ = 1 := eq_one_of_fix_perp_three _ e hfix hW
  have hhQ : h ∈ leechQ u := (L.φ_ker ⟨h, hhC⟩).1 hA1
  have hvh : L.vec h ∈ Submodule.span (ZMod 2) (Set.range e) := by
    refine mem_of_forall_perp fun a ha => ?_
    have ha' : ∀ i, bil₀ a (e i) = 0 := fun i => ha _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨v, hvQ, hva, hhv⟩ := hperp a ha'
    rw [← hva]
    exact (L.comm_eq_one_iff hhQ hvQ).1 (commutatorElement_eq_one_iff_mul_comm.2 hhv)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hvh
  rw [Fin.sum_univ_three] at hc
  have hxyQ : x * y ∈ leechQ u := mul_mem hxQ hyQ
  have hxtQ : x * t ∈ leechQ u := mul_mem hxQ htQ
  have hytQ : y * t ∈ leechQ u := mul_mem hyQ htQ
  have hxytQ : x * y * t ∈ leechQ u := mul_mem hxyQ htQ
  have vxy : L.vec (x * y) = L.vec x + L.vec y := L.vec_mul x hxQ y hyQ
  have vxt : L.vec (x * t) = L.vec x + L.vec t := L.vec_mul x hxQ t htQ
  have vyt : L.vec (y * t) = L.vec y + L.vec t := L.vec_mul y hyQ t htQ
  have vxyt : L.vec (x * y * t) = L.vec x + L.vec y + L.vec t := by
    rw [L.vec_mul (x * y) hxyQ t htQ, vxy]
  have hex : ∃ e' ∈ ({1, x, y, t, x * y, x * t, y * t, x * y * t} : Set G),
      e' ∈ leechQ u ∧ g₀ * e' = e' * g₀ ∧ L.vec e' = L.vec h := by
    have hg₀xy : g₀ * (x * y) = x * y * g₀ := ((Commute.mul_right (show Commute g₀ x from hg₀x)
      (show Commute g₀ y from hg₀y))).eq
    have hg₀xt : g₀ * (x * t) = x * t * g₀ := ((Commute.mul_right (show Commute g₀ x from hg₀x)
      (show Commute g₀ t from hg₀t))).eq
    have hg₀yt : g₀ * (y * t) = y * t * g₀ := ((Commute.mul_right (show Commute g₀ y from hg₀y)
      (show Commute g₀ t from hg₀t))).eq
    have hg₀xyt : g₀ * (x * y * t) = x * y * t * g₀ :=
      ((Commute.mul_right (show Commute g₀ (x * y) from hg₀xy)
        (show Commute g₀ t from hg₀t))).eq
    rcases zmod2_cases' (c 0) with h0 | h0 <;> rcases zmod2_cases' (c 1) with h1 | h1 <;>
      rcases zmod2_cases' (c 2) with h2 | h2 <;> rw [h0, h1, h2] at hc <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hc
    · exact ⟨1, Or.inl rfl, one_mem _, by simp, by rw [L.vec_one, ← hc]⟩
    · exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inl rfl))), htQ, hg₀t, hc⟩
    · exact ⟨y, Or.inr (Or.inr (Or.inl rfl)), hyQ, hg₀y, hc⟩
    · exact ⟨y * t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), hytQ, hg₀yt,
        by rw [vyt]; exact hc⟩
    · exact ⟨x, Or.inr (Or.inl rfl), hxQ, hg₀x, hc⟩
    · exact ⟨x * t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hxtQ, hg₀xt,
        by rw [vxt]; exact hc⟩
    · exact ⟨x * y, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hxyQ, hg₀xy,
        by rw [vxy]; exact hc⟩
    · exact ⟨x * y * t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), hxytQ,
        hg₀xyt, by rw [vxyt]; exact hc⟩
  obtain ⟨e', he'mem, he'Q, hg₀e', hve'⟩ := hex
  rcases L.eq_or_eq_mul_z hhQ he'Q hve'.symm with hh | hh
  · rw [hh]
    exact he'mem
  · exfalso
    have hgh : h * g₀ = g₀ * h := hcen g₀ hg₀x hg₀y hg₀t
    rw [hh] at hgh
    apply hg₀u
    have h1 : e' * (u * g₀) = e' * (g₀ * u) := by
      calc e' * (u * g₀) = e' * u * g₀ := (mul_assoc _ _ _).symm
        _ = g₀ * (e' * u) := hgh
        _ = g₀ * e' * u := (mul_assoc _ _ _).symm
        _ = e' * g₀ * u := by rw [hg₀e']
        _ = e' * (g₀ * u) := mul_assoc _ _ _
    exact (mul_left_cancel h1).symm

end Center

end S365

end CFSG.Monster.GMS
