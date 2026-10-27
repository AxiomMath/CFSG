module

public import CFSG.Quasithin.EmptyFaithful.S143GB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Model

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem exists_singular_nonperp (h : OfourStruct X L₁ L₂ t) {q : W → ZMod 2}
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1)
    (hexp : ∀ w : W, w * w = 1) {v : W} (hv1 : v ≠ 1) (hvq : q v = 0) :
    ∃ x : W, q x = 0 ∧ q (v * x) = 1 := by
  obtain ⟨u₁, hu₁, u₂, hu₂, hv⟩ := h.exists_decomp_W v
  have hu₁1 : u₁ ≠ 1 := by
    intro he
    rw [he, one_mul] at hv
    have : q v = 1 := (hq v).mpr ⟨Or.inr (hv ▸ hu₂), hv1⟩
    rw [hvq] at this
    exact zero_ne_one this
  have hu₂1 : u₂ ≠ 1 := by
    intro he
    rw [he, mul_one] at hv
    have : q v = 1 := (hq v).mpr ⟨Or.inl (hv ▸ hu₁), hv1⟩
    rw [hvq] at this
    exact zero_ne_one this
  obtain ⟨y, hy, hy1, hyu⟩ := exists_mem_ne_of_card_four
    (S1417.card_of_actsAsNaturalL2 h.nat₂).2 u₂
  refine ⟨u₁ * y, q_eq_zero_of_mul h hq hu₁ hy hu₁1 hy1, ?_⟩
  have e : v * (u₁ * y) = u₂ * y := by
    rw [hv]
    calc u₁ * u₂ * (u₁ * y) = (u₁ * u₁) * (u₂ * y) := by
          calc u₁ * u₂ * (u₁ * y) = u₁ * (u₂ * u₁) * y := by group
            _ = u₁ * (u₁ * u₂) * y := by rw [mul_comm u₂ u₁]
            _ = (u₁ * u₁) * (u₂ * y) := by group
      _ = u₂ * y := by rw [hexp u₁, one_mul]
  rw [e]
  refine (hq _).mpr ⟨Or.inr ((commV L₂).mul_mem hu₂ hy), ?_⟩
  intro he
  apply hyu
  have h1 := mul_eq_one_iff_eq_inv.mp he
  rw [inv_eq_of_mul_eq_one_right (hexp y)] at h1
  exact h1.symm

end Model

section Counterexample

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_involution_not_mem_wOfU :
    ∃ u ∈ uOfL22 T M, u ∉ Hyp1281Two.wOfU T M ∧ u * u = 1 := by
  have h := c.h1281
  have hg := c.goodElt
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hUN := c.hUN
  let _ : CommGroup (UT T M) := c.tildeCommGroup
  obtain ⟨L₁, L₂, t₀, hS, hsing⟩ := exists_ofourStruct_of_plusType
    (W := UT T M) (q := q) (tilde_mul_self h) hq4 hq1 hq2 hq3
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  set v := tclsE hUN haU with hvdef
  have hvq : q v = 0 :=
    (hq5 v.1 v.2 ⟨a, hUN haU⟩ haU (tclsE_val hUN haU).symm).mpr (by rw [sq]; exact haa)
  have hv1 : v ≠ 1 := fun he => haZ ((tclsE_eq_one_iff hUN haU).mp he)
  obtain ⟨x, hxq, hvxq⟩ := exists_singular_nonperp hS hsing (tilde_mul_self h) hv1 hvq
  obtain ⟨w, hwU, hwx⟩ := mem_secImg.1 x.2
  have hw2 : (w : G) ^ 2 = 1 := (hq5 x.1 x.2 w hwU hwx).mp hxq
  have hw2' : (w : G) * (w : G) = 1 := by rw [← sq]; exact hw2
  refine ⟨(w : G), hwU, ?_, hw2'⟩
  intro hwW
  have hwa : a * (w : G) = (w : G) * a := Subgroup.mem_centralizer_iff.mp hwW.2 a haV
  have hxe : x = tclsE hUN hwU := Subtype.ext (hwx.symm.trans (tclsE_val hUN hwU).symm)
  have h2 : q (v * x) = 0 := by
    have hu : a * (w : G) ∈ uOfL22 T M := (uOfL22 T M).mul_mem haU hwU
    have e : v * x = tclsE hUN hu := by rw [hxe]; exact (tclsE_mul hUN haU hwU).symm
    rw [e]
    refine (hq5 _ _ ⟨a * (w : G), hUN hu⟩ hu (tclsE_val hUN hu).symm).mpr ?_
    rw [sq]
    calc a * (w : G) * (a * (w : G)) = a * ((w : G) * a) * (w : G) := by group
      _ = a * (a * (w : G)) * (w : G) := by rw [← hwa]
      _ = (a * a) * ((w : G) * (w : G)) := by group
      _ = 1 := by rw [haa, hw2', one_mul]
  rw [hvxq] at h2
  exact one_ne_zero h2

end Counterexample

end S143

end CFSG.Quasithin
