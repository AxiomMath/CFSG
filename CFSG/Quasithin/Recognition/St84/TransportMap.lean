module

public import CFSG.GH74.QTGen4.DSGen4.Defs

public section

namespace CFSG.Quasithin

variable {A B : Type*} [Group A] [Group B]

theorem oTwoPrime_map (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    oTwoPrime (X.map f) = (oTwoPrime X).map f := by
  unfold oTwoPrime
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, n, hn⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, n, hf (by rw [map_pow, hn, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, n, hn⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, n, by rw [← map_pow, hn, map_one]⟩

theorem oTwoRes_map (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    oTwoRes (X.map f) = (oTwoRes X).map f := by
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, m, hm, hym⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, ⟨hx, m, hm, hf (by rw [map_pow, hym, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, m, hm, hxm⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hx, m, hm, by rw [← map_pow, hxm, map_one]⟩

end CFSG.Quasithin

namespace CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement

variable {A B : Type} [Group A] [Group B]

theorem FixFree.map_iff (f : A →* B) (hf : Function.Injective f) {K E : Subgroup A} {x : A} :
    FixFree (K.map f) (E.map f) (f x) ↔ FixFree K E x := by
  constructor
  · intro h e he hc
    have h1 : f e ∈ K.map f :=
      h (f e) (Subgroup.mem_map_of_mem f he) (by
        rw [← map_commutatorElement]
        exact Subgroup.mem_map_of_mem f hc)
    exact (Subgroup.mem_map_iff_mem hf).mp h1
  · intro h e he hc
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp he
    rw [← hfy] at hc ⊢
    rw [← map_commutatorElement] at hc
    exact Subgroup.mem_map_of_mem f (h y hy ((Subgroup.mem_map_iff_mem hf).mp hc))

theorem NatSec.map_iff (f : A →* B) (hf : Function.Injective f) {L K E : Subgroup A} :
    NatSec (L.map f) (K.map f) (E.map f) ↔ NatSec L K E := by
  constructor
  · intro h x hx hx3
    refine (FixFree.map_iff f hf).mp (h (f x) (Subgroup.mem_map_of_mem f hx) ?_)
    rw [orderOf_injective f hf x]
    exact hx3
  · intro h x hx hx3
    obtain ⟨y, hy, hfy⟩ := Subgroup.mem_map.mp hx
    rw [← hfy] at hx3 ⊢
    exact (FixFree.map_iff f hf).mpr (h y hy (by
      rw [← orderOf_injective f hf y]
      exact hx3))

end CFSG.GH74.QTGen4.DSGen4
