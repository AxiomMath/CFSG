module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29B2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29R8
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29J1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29J2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

section At

variable {G : Type} [Group G] [Finite G]

namespace S29

variable {H M S : Subgroup G}

theorem exists_sit29' (hA : F53Amalgam H M S) (h28 : Hss28At H M) (h26 : Hss26AAt H M)
    (hb : 1 < bMin H M) {α β : Geo H M} (hαβ : (graph (H ⊔ M) H M).Adj α β)
    (hv : vtype α = false) (hbα : bAt α = bMin H M) (hz : Zv β ≤ centerOf (stab β))
    (hmod : IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α)) :
    ∃ a₂ a₃ : Geo H M, Sit29 H M S α a₂ a₃ β := by
  have hvβ : vtype β = true := by
    have h := vtype_ne_of_adj hαβ
    rw [hv] at h
    cases hvb : vtype β
    · exact absurd hvb.symm h
    · rfl
  have hcard : (nbrs β).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact card_nbrs_true hA hvβ
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp hcard
  have hn : ∀ w, w ∈ nbrs β ↔ w = x ∨ w = y ∨ w = z := fun w => by rw [hs]; simp
  have hα : α ∈ nbrs β := hαβ.symm
  rcases (hn α).mp hα with rfl | rfl | rfl
  · exact ⟨y, z, hA, h28, h26, hb, hαβ, hv, hbα, hz, hmod, (hn y).mpr (Or.inr (Or.inl rfl)),
      (hn z).mpr (Or.inr (Or.inr rfl)), hxy, hxz, hyz⟩
  · exact ⟨x, z, hA, h28, h26, hb, hαβ, hv, hbα, hz, hmod, (hn x).mpr (Or.inl rfl),
      (hn z).mpr (Or.inr (Or.inr rfl)), hxy.symm, hyz, hxz⟩
  · exact ⟨x, y, hA, h28, h26, hb, hαβ, hv, hbα, hz, hmod, (hn x).mpr (Or.inl rfl),
      (hn y).mpr (Or.inr (Or.inl rfl)), hxz.symm, hyz.symm, hxy⟩

theorem Sit29.card_R_eq {α a₂ a₃ β : Geo H M} (hs : Sit29 H M S α a₂ a₃ β) :
    Nat.card ↥(Zv α ⊓ Zv a₂) = 4 := by
  rcases hs.card_R with h | h | h
  · exfalso
    have hR := hs.R_eq_right h
    by_cases hJ : thompsonJ (stab α ⊓ stab β) ≤ Qv β
    · exact step7 hs hR hJ
    · by_cases hb2 : bMin H M = 2
      · rw [step3 hs hb2] at h
        omega
      · exact step6 hs (by have := hs.b1; omega) hR hJ
  · exact h
  · exfalso
    by_cases hb2 : bMin H M = 2
    · rw [step3 hs hb2] at h
      omega
    · exact step5 hs (by have := hs.b1; omega) h

end S29

variable {H M S : Subgroup G}

end At

end F53.Stellmacher

end CFSG.Quasithin
