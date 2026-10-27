module

public import CFSG.Timmesfeld.Bridge.RootSetsRankOne

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem mem_of_mem_line (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D) {c f : G}
    (hcD : c ∈ D) (hf : f ∈ D) (h4 : orderOf (c * f) = 4) {a w' : G} (ha : a ∈ rootGroup D c)
    (hw' : w' ∈ rootGroup D ((c * f) ^ 2)) (hne : a ≠ 1 ∨ w' ≠ 1) : a * w' ∈ D := by
  have hD := h.root
  have hwD : (c * f) ^ 2 ∈ D := hD.sq_mem hcD hf h4
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hwD hw' (hne.resolve_left
      (not_not.2 ha1))).1
  by_cases hw1 : w' = 1
  · rw [hw1, mul_one]
    exact (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD ha ha1).1
  have haT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hcD ha ha1
  have hwT := mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hwD hw' hw1
  obtain ⟨-, h2, -⟩ := special_pair_rootSet h hc hs hcD hf h4
  obtain ⟨b, hb, hab⟩ := h2 a haT w' hwT
  rw [← hab, show a * (a * b) ^ 2 = (a * a) * b * a * b by rw [pow_two]; group,
    hD.mul_self_eq_one haT.1, one_mul]
  have := conj_mem_of_isClass h.isClass b haT.1
  rwa [hD.inv_eq hb.1] at this

end CFSG.Timmesfeld.Bridge
