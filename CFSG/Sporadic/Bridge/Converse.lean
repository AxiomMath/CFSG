module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.ON
public import CFSG.Milestones.FAM_Th_simplicity
public import CFSG.Sporadic.B
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.Sporadic.Bridge

open CFSG.Blueprint.NativeSporadic CFSG.Open

private theorem finite_simple_of {G : Type*} [Group G]
    (h : Finite G ∧ Nontrivial G ∧ IsSimpleGroup G) : Finite G ∧ IsSimpleGroup G :=
  ⟨h.1, h.2.2⟩

theorem carrier_finite_simple_of_ne_M :
    ∀ s : TauCeti.SporadicName, s ≠ .M →
    Finite (Carrier s) ∧ IsSimpleGroup (Carrier s)
  | .M11, _ => finite_simple_of Sporadic.Mathieu.fam_m11_simplicity
  | .M12, _ => finite_simple_of Sporadic.Mathieu.fam_m12_simplicity
  | .M22, _ => finite_simple_of Sporadic.Mathieu.fam_m22_simplicity
  | .M23, _ => finite_simple_of Sporadic.Mathieu.fam_m23_simplicity
  | .M24, _ => finite_simple_of Sporadic.Mathieu.fam_m24_simplicity
  | .J1, _ => finite_simple_of Sporadic.J1.fam_j1_simplicity
  | .J2, _ => finite_simple_of Sporadic.J2.fam_j2_simplicity
  | .J3, _ => finite_simple_of Sporadic.J3.fam_j3_simplicity
  | .J4, _ => finite_simple_of Sporadic.J4.fam_j4_simplicity
  | .HS, _ => finite_simple_of Sporadic.HS.fam_hs_simplicity
  | .McL, _ => finite_simple_of Sporadic.McL.fam_mcl_simplicity
  | .He, _ => finite_simple_of Sporadic.He.fam_he_simplicity
  | .Ru, _ => finite_simple_of Sporadic.Ru.fam_ru_simplicity
  | .Suz, _ => finite_simple_of Sporadic.Suz.fam_suz_simplicity
  | .ONan, _ => finite_simple_of Sporadic.ON.fam_on_simplicity
  | .Co1, _ => finite_simple_of Sporadic.Co1.fam_co1_simplicity
  | .Co2, _ => finite_simple_of Sporadic.Co2.fam_co2_simplicity
  | .Co3, _ => finite_simple_of Sporadic.Co3.fam_co3_simplicity
  | .Fi22, _ => ⟨inferInstanceAs (Finite Fi22), Sporadic.Fi22.isSimpleGroup_Fi22⟩
  | .Fi23, _ => ⟨inferInstanceAs (Finite Fi23), Sporadic.Fi23.isSimpleGroup_Fi23⟩
  | .Fi24Prime, _ => ⟨inferInstanceAs (Finite Fi24prime), Sporadic.Fi24.isSimpleGroup_Fi24prime⟩
  | .HN, _ => finite_simple_of Sporadic.HN.fam_hn_simplicity
  | .Ly, _ => finite_simple_of Sporadic.Ly.fam_ly_simplicity
  | .Th, _ => ⟨inferInstanceAs (Finite Th), Milestones.fam_th_simplicity⟩
  | .B, _ => ⟨inferInstanceAs (Finite B), Sporadic.B.fam_b_simplicity⟩
  | .M, hs => absurd rfl hs

theorem carrier_M_finite_simple (hcard : Nat.card MonsterY443Derived = monsterOrder)
    (hsimple : IsSimpleGroup MonsterY443Derived) :
    Finite (Carrier .M) ∧ IsSimpleGroup (Carrier .M) := by
  have hfin : Finite MonsterY443Derived :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num [monsterOrder])
  exact ⟨Finite.of_equiv _ Y443.commutatorMulEquiv.symm.toEquiv,
    Y443.commutatorMulEquiv.isSimpleGroup⟩

theorem carrier_finite_simple
    (hcard : Nat.card MonsterY443Derived = monsterOrder)
    (hsimple : IsSimpleGroup MonsterY443Derived) (s : TauCeti.SporadicName) :
    Finite (Carrier s) ∧ IsSimpleGroup (Carrier s) := by
  by_cases hs : s = .M
  · subst hs
    exact carrier_M_finite_simple hcard hsimple
  · exact carrier_finite_simple_of_ne_M s hs

theorem finite_simple_of_sporadicRep
    (hcard : Nat.card MonsterY443Derived = monsterOrder)
    (hsimple : IsSimpleGroup MonsterY443Derived) (G : Type) [Group G] (hrep : SporadicRep G) :
    Finite G ∧ IsSimpleGroup G := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  obtain ⟨h1, h2⟩ := carrier_finite_simple hcard hsimple s
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, e.isSimpleGroup⟩

theorem tauCeti_finite_simple
    (hcard : Nat.card MonsterY443Derived = monsterOrder)
    (hsimple : IsSimpleGroup MonsterY443Derived) (s : TauCeti.SporadicName) :
    Finite s.Group ∧ IsSimpleGroup s.Group := by
  obtain ⟨e⟩ := nonempty_carrier_mulEquiv_group s
  obtain ⟨h1, h2⟩ := carrier_finite_simple hcard hsimple s
  exact ⟨Finite.of_equiv _ e.toEquiv, e.symm.isSimpleGroup⟩

end CFSG.Sporadic.Bridge
