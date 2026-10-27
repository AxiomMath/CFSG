module

public import CFSG.Quasithin.Background.A3Structure314Radical
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.A314

open CFSG.Assembly.LowTwoRank

theorem card_alt (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_isAlt {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] (h : IsAlt n X) :
    Nat.card X = n.factorial / 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_alt n hn]

theorem card_isAlt_five {X : Type} [Group X] (h : IsAlt 5 X) : Nat.card X = 60 := by
  rw [card_isAlt (by norm_num) h]
  norm_num [Nat.factorial]

theorem exists_noncomm_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => h a b }
  exact hp (IsSimpleGroup.prime_card (α := X))

theorem isAlt_facts {n : ℕ} (hn6 : 6 ≤ n) (hn7 : n ≤ 7) {X : Type} [Group X] [Finite X]
    (h : IsAlt n X) : IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ Nat.card X ≠ 60 := by
  have hcard : Nat.card X = n.factorial / 2 := card_isAlt (by omega) h
  have hs : IsSimpleGroup X := by
    obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    exact e.isSimpleGroup
  have hn : n = 6 ∨ n = 7 := by omega
  rcases hn with rfl | rfl
  · have : Nat.card X = 360 := by rw [hcard]; norm_num [Nat.factorial]
    refine ⟨hs, exists_noncomm_of_simple hs ?_, by omega⟩
    rw [this]
    norm_num
  · have : Nat.card X = 2520 := by rw [hcard]; norm_num [Nat.factorial]
    refine ⟨hs, exists_noncomm_of_simple hs ?_, by omega⟩
    rw [this]
    norm_num

theorem card_ne_sixty_of_isAlt_six {X : Type} [Group X] (h : IsAlt 6 X) : Nat.card X ≠ 60 := by
  rw [card_isAlt (by norm_num) h]
  norm_num [Nat.factorial]

theorem solvable_of_isElemAbelianOfRank {p n : ℕ} {V : Type} [Group V]
    (h : IsElemAbelianOfRank p n V) : Group.IsSolvable V := by
  obtain ⟨e⟩ := h
  refine Group.isSolvable_of_comm fun a b => e.injective ?_
  rw [map_mul, map_mul, mul_comm]

theorem solvable_of_isExtraspecial2 {m : ℕ} {V : Type} [Group V] [Finite V]
    (h : IsExtraspecial2 m V) : Group.IsSolvable V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.1
  have hp : IsPGroup 2 V := CFSG.IsExtraspecial.isPGroup 2 V
  have : Group.IsNilpotent V := hp.isNilpotent
  infer_instance

theorem solvable_of_isZ4Cubed {V : Type} [Group V] (h : IsZ4Cubed V) : Group.IsSolvable V := by
  obtain ⟨e⟩ := h
  refine Group.isSolvable_of_comm fun a b => e.injective ?_
  rw [map_mul, map_mul, mul_comm]

theorem solvable_of_isZ4StarExtra2 {V : Type} [Group V] [Finite V] (h : IsZ4StarExtra2 V) :
    Group.IsSolvable V := by
  obtain ⟨Z, E, -, hZc, hE, hZX, hZE, -⟩ := h
  have hZn : Z.Normal := Subgroup.normal_of_le_center hZX
  have hZs : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (by
      have := Subgroup.mem_center_iff.mp (hZX b.2) (a : V)
      exact this)
  have hEs : Group.IsSolvable ↥E := solvable_of_isExtraspecial2 hE
  let f : ↥E →* V ⧸ Z := (QuotientGroup.mk' Z).comp E.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective Z y
    have hv : v ∈ Z ⊔ E := by rw [hZE]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hv
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' Z b = QuotientGroup.mk' Z v
    have ha1 : QuotientGroup.mk' Z a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [← hab, map_mul, ha1, one_mul]
  have : Group.IsSolvable (V ⧸ Z) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient Z

theorem solvable_pCore_two (X : Type) [Group X] [Finite X] :
    Group.IsSolvable ↥(CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 X) := (CFSG.pCore_isPGroup (G := X) (p := 2)).isNilpotent
  infer_instance

theorem excl_simple {X : Type} [Group X] [Finite X] {V : Subgroup X} [V.Normal]
    (hV : Group.IsSolvable ↥V) (hs : IsSimpleGroup (X ⧸ V)) (hna : ∃ a b : X ⧸ V, a * b ≠ b * a)
    (hn : Nat.card (X ⧸ V) ≠ 60) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  have h := solvableRadical_eq_of_simple hV hs hna
  let e : X ⧸ CFSG.solvableRadical X ≃* X ⧸ V := QuotientGroup.quotientMulEquivOfEq h
  apply hn
  rw [← Nat.card_congr e.toEquiv, card_isAlt (by norm_num) hA]
  norm_num [Nat.factorial]

theorem excl_simple_self {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hna : ∃ a b : X, a * b ≠ b * a) (hn : Nat.card X ≠ 60)
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  let e : X ⧸ (⊥ : Subgroup X) ≃* X := QuotientGroup.quotientBot
  have hs' : IsSimpleGroup (X ⧸ (⊥ : Subgroup X)) := e.isSimpleGroup
  have hna' : ∃ a b : X ⧸ (⊥ : Subgroup X), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact excl_simple (V := ⊥) (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _) hs' hna'
    (by rw [Nat.card_congr e.toEquiv]; exact hn) hA

theorem excl_hat {X : Type} [Group X] [Finite X] {V : Subgroup X} [V.Normal]
    (hV : Group.IsSolvable ↥V) {S : Type} [Group S] (hHat : IsHat (X ⧸ V) S)
    (hS : Finite S → Nat.card S ≠ 60) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  obtain ⟨hq, -, ⟨eS⟩⟩ := hHat
  obtain ⟨e⟩ := solvableRadical_quotient_equiv hV hq
  have hfin : Finite S := Finite.of_equiv _ eS.toEquiv
  apply hS hfin
  rw [← Nat.card_congr (e.trans eS).toEquiv, card_isAlt (by norm_num) hA]
  norm_num [Nat.factorial]

theorem excl_hat_self {X : Type} [Group X] [Finite X] {S : Type} [Group S] (hHat : IsHat X S)
    (hS : Finite S → Nat.card S ≠ 60) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  let e : X ⧸ (⊥ : Subgroup X) ≃* X := QuotientGroup.quotientBot
  have hHat' : IsHat (X ⧸ (⊥ : Subgroup X)) S := IsHat.of_mulEquiv e.symm hHat
  exact excl_hat (V := ⊥) (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _) hHat' hS hA

theorem excl_ext {X : Type} [Group X] [Finite X] {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → Group.IsSolvable V)
    (hPY : ∀ (Y : Type) [Group Y] [Finite Y], PY Y →
      IsSimpleGroup Y ∧ (∃ a b : Y, a * b ≠ b * a) ∧ Nat.card Y ≠ 60)
    (h : IsExt X PV PY) (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  obtain ⟨hs, hna, hn⟩ := hPY _ hpy
  exact excl_simple (hPV _ hpv) hs hna hn hA

theorem excl_ext_hat {X : Type} [Group X] [Finite X] {PV : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → Group.IsSolvable V) {S : Type} [Group S]
    (hS : Finite S → Nat.card S ≠ 60) (h : IsExt X PV (fun Y _ => IsHat Y S))
    (hA : IsAlt 5 (X ⧸ CFSG.solvableRadical X)) : False := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  exact excl_hat (hPV _ hpv) hpy hS hA

end CFSG.Quasithin.A314
