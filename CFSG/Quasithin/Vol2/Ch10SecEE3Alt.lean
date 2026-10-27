module

public import CFSG.Quasithin.Vol2.Ch10SecECase2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}

theorem card_of_alternatingNatural_five (h : AlternatingNatural H ⊤ ⊥ 5) :
    Nat.card V = Nat.card ↥(FFModel.altDn 5).sec := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨β, hβs, hβk, -⟩ := RealizesVia.coordSec altDn_five_ker hπ
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hβk u).mp hu
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  rw [← Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩), Subgroup.card_top]

theorem eq_zero_of_fix_cThree : ∀ x : Fin 5 → ZMod 2, isEven x → pact cThree x = x →
    pact cThree' x = x → x = 0 := by
  decide

theorem eq_one_of_alternatingNatural_five (h : AlternatingNatural H ⊤ ⊥ 5) {v : V}
    (hv : ∀ φ ∈ H, φ v = v) : v = 1 := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨β, -, hβk, hβe⟩ := RealizesVia.coordSec altDn_five_ker hπ
  set u : ↥(⊤ : Subgroup V) := ⟨v, Subgroup.mem_top _⟩ with hu
  have hfix : ∀ γ : ↥(alternatingGroup (Fin 5)),
      pact (γ : Equiv.Perm (Fin 5)) (Multiplicative.toAdd ((β u : ↥(FFModel.altDn 5).sec) :
        (FFModel.altDn 5).Amb)) =
        Multiplicative.toAdd ((β u : ↥(FFModel.altDn 5).sec) : (FFModel.altDn 5).Amb) := by
    intro γ
    have h1 := hβe γ u (Subgroup.mem_top _)
    have e : (⟨((π γ : ↥H) : MulAut V) (u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u :=
      Subtype.ext (hv _ (π γ).2)
    rw [e] at h1
    exact congrArg Multiplicative.toAdd h1.symm
  have h0 := eq_zero_of_fix_cThree _ (β u).2 (hfix ⟨cThree, cThree_mem_alt⟩)
    (hfix ⟨cThree', cThree'_mem_alt⟩)
  have h1 : β u = 1 := Subtype.ext (Multiplicative.toAdd.injective (h0.trans rfl))
  have h2 := (hβk u).mp h1
  rwa [Subgroup.mem_bot] at h2

end CFSG.Quasithin.Vol2.Ch10.SecE
