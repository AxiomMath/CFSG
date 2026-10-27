module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Mem
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open scoped Pointwise

@[expose] def actPt (t : List ℕ) (x : ℕ) : ℕ := t.getD x x

@[expose] def actSet (t : List ℕ) (T : Finset ℕ) : Finset ℕ := T.image (actPt t)

@[expose] def actSetSet (t : List ℕ) (X : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  X.image (actSet t)

theorem hact_pt (g : G24) (x : ℕ) : g • x = actPt (tab 24 g) x := rfl

theorem hact_set (g : G24) (T : Finset ℕ) : g • T = actSet (tab 24 g) T :=
  smul_finset_eq_image g T

theorem hact_setset (g : G24) (X : Finset (Finset ℕ)) : g • X = actSetSet (tab 24 g) X :=
  smul_finset_finset_eq_image g X

@[expose] def indTab {α : Type} [DecidableEq α] (act' : List ℕ → α → α) (L : List α)
    (t : List ℕ) : List ℕ :=
  L.map (fun x => L.idxOf (act' t x))

section Rho

variable {Z : Subgroup G24} {k : ℕ}

theorem card_dvd_range (ρ : ↥Z →* Equiv.Perm (Fin k)) (gl : List ↥Z) {L : List (List ℕ)}
    {par : List (ℕ × ℕ)} (h : EnumOK k (gl.map (fun z => tab k (ρ z))) L par) :
    L.length ∣ Nat.card ρ.range := by
  have h1 : EnumOK k ((gl.map ρ).map (tab k)) L par := by
    rw [List.map_map]
    exact h
  obtain ⟨-, hcard, -⟩ := enum_closure (Γ := Equiv.Perm (Fin k)) (tab k) tab_one_L tab_mul
    tab_injective (gl.map ρ) h1
  rw [← hcard]
  refine Subgroup.card_dvd_of_le ?_
  rw [Subgroup.closure_le]
  rintro _ hx
  obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨z, rfl⟩

@[expose] def wordElts (gens : List G24) (hg : ∀ x ∈ gens, x ∈ Z) (ws : List (List ℕ)) :
    List ↥Z :=
  ws.map (fun w => ⟨evalEltL gens w, evalEltL_mem gens hg w⟩)

theorem card_dvd_range_words {α : Type} [MulAction G24 α] [DecidableEq α]
    (act' : List ℕ → α → α) (hact : ∀ (g : G24) (x : α), g • x = act' (tab 24 g) x)
    (L : List α) (hnd : L.Nodup) (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) (gens : List G24)
    (hg : ∀ x ∈ gens, x ∈ Z) (gensT : List (List ℕ)) (hgT : gens.map (tab 24) = gensT)
    (ws : List (List ℕ)) (hws : ∀ w ∈ ws, ∀ l ∈ w, l < gens.length) {Lg : List (List ℕ)}
    {par : List (ℕ × ℕ)}
    (h : EnumOK L.length (ws.map (fun w => indTab act' L (wordTab 24 gensT w))) Lg par) :
    Lg.length ∣ Nat.card (listHom Z L hnd hZ).range := by
  refine card_dvd_range (par := par) (listHom Z L hnd hZ) (wordElts gens hg ws) ?_
  have h2 : (wordElts gens hg ws).map (fun z => tab L.length (listHom Z L hnd hZ z)) =
      ws.map (fun w => indTab act' L (wordTab 24 gensT w)) := by
    unfold wordElts
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro w hw
    simp only [Function.comp_apply]
    rw [tab_listHom act' hact Z L hnd hZ, tab_evalEltL gens w (hws w hw), hgT]
    rfl
  rw [h2]
  exact h

theorem card_ker_mul {H : Type} [Group H] (ρ : ↥Z →* H) :
    Nat.card Z = Nat.card ρ.range * Nat.card ρ.ker :=
  card_eq_range_mul_ker ρ

end Rho

end CFSG.Quasithin.A312M24
