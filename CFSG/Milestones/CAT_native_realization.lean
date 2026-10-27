module

public import CFSG.Blueprint.NativeSporadicReps
public import CFSG.LieType.Catalog.Realization
public import CFSG.Monster.Generated.FiniteSimple
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.HN
public import CFSG.Sporadic.Ly
public import CFSG.Milestones.FAM_Th_simplicity
public import CFSG.Sporadic.B

public section

namespace CFSG.Milestones

theorem cat_native_realization_cyclic (p : ℕ) [Fact p.Prime] :
    Finite (Multiplicative (ZMod p)) ∧ IsSimpleGroup (Multiplicative (ZMod p)) :=
  ⟨inferInstance, isSimpleGroup_of_prime_card (by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])⟩

theorem cat_native_realization_alternating (n : ℕ) (hn : 5 ≤ n) :
    Finite (alternatingGroup (Fin n)) ∧ IsSimpleGroup (alternatingGroup (Fin n)) := by
  exact ⟨inferInstance, alternatingGroup.isSimpleGroup (by simpa using hn)⟩

theorem cat_native_realization_lie
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (h : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f) :
    ∃ (G : Type) (_ : Group G), Finite G ∧ Nontrivial G ∧ IsSimpleGroup G ∧
      CFSG.Blueprint.LieModel G t n p f :=
  CFSG.LieType.Catalog.exists_lieModel_finite_simple t n p f h

open CFSG.Blueprint.NativeSporadic in
theorem native_carrier_finite_simple_of_ne_B
    (s : TauCeti.SporadicName) (hs : s ≠ .B) :
    Finite (nativeCarrier s) ∧ Nontrivial (nativeCarrier s) ∧ IsSimpleGroup (nativeCarrier s) :=
  match s, hs with
  | .M11, _ => Sporadic.Mathieu.fam_m11_simplicity
  | .M12, _ => Sporadic.Mathieu.fam_m12_simplicity
  | .M22, _ => Sporadic.Mathieu.fam_m22_simplicity
  | .M23, _ => Sporadic.Mathieu.fam_m23_simplicity
  | .M24, _ => Sporadic.Mathieu.fam_m24_simplicity
  | .J1, _ => Sporadic.J1.fam_j1_simplicity
  | .J2, _ => Sporadic.J2.fam_j2_simplicity
  | .J3, _ => Sporadic.J3.fam_j3_simplicity
  | .J4, _ => Sporadic.J4.fam_j4_simplicity
  | .HS, _ => Sporadic.HS.fam_hs_simplicity
  | .McL, _ => Sporadic.McL.fam_mcl_simplicity
  | .He, _ => Sporadic.He.fam_he_simplicity
  | .Ru, _ => Sporadic.Ru.fam_ru_simplicity
  | .Suz, _ => Sporadic.Suz.fam_suz_simplicity
  | .ONan, _ => Sporadic.ON.fam_on_simplicity
  | .Co1, _ => Sporadic.Co1.fam_co1_simplicity
  | .Co2, _ => Sporadic.Co2.fam_co2_simplicity
  | .Co3, _ => Sporadic.Co3.fam_co3_simplicity
  | .Fi22, _ => ⟨inferInstanceAs (Finite Blueprint.NativeSporadic.Fi22),
      Sporadic.Fi22.isSimpleGroup_Fi22.toNontrivial, Sporadic.Fi22.isSimpleGroup_Fi22⟩
  | .Fi23, _ => ⟨inferInstanceAs (Finite Blueprint.NativeSporadic.Fi23),
      Sporadic.Fi23.isSimpleGroup_Fi23.toNontrivial, Sporadic.Fi23.isSimpleGroup_Fi23⟩
  | .Fi24Prime, _ => ⟨inferInstanceAs (Finite Blueprint.NativeSporadic.Fi24prime),
      Sporadic.Fi24.isSimpleGroup_Fi24prime.toNontrivial, Sporadic.Fi24.isSimpleGroup_Fi24prime⟩
  | .HN, _ => Sporadic.HN.fam_hn_simplicity
  | .Ly, _ => Sporadic.Ly.fam_ly_simplicity
  | .Th, _ => ⟨inferInstanceAs (Finite Blueprint.NativeSporadic.Th),
      fam_th_simplicity.toNontrivial, fam_th_simplicity⟩
  | .B, hs => absurd rfl hs
  | .M, _ =>
      ⟨Monster.Generated.generated_rational_group_finite_simple.2.2,
        Monster.Generated.generated_rational_group_finite_simple.1,
        Monster.Generated.generated_rational_group_finite_simple.2.1⟩

theorem cat_native_realization_cyclic' (p : ℕ) (hp : p.Prime) :
    Finite (Multiplicative (ZMod p)) ∧ Nontrivial (Multiplicative (ZMod p)) ∧
      IsSimpleGroup (Multiplicative (ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := (cat_native_realization_cyclic p).2
  exact ⟨(cat_native_realization_cyclic p).1, h.toNontrivial, h⟩

theorem cat_native_realization_alternating' (n : ℕ) (hn : 5 ≤ n) :
    Finite (alternatingGroup (Fin n)) ∧ Nontrivial (alternatingGroup (Fin n)) ∧
      IsSimpleGroup (alternatingGroup (Fin n)) := by
  have h := (cat_native_realization_alternating n hn).2
  exact ⟨(cat_native_realization_alternating n hn).1, h.toNontrivial, h⟩

open CFSG.Blueprint.NativeSporadic in
theorem cat_native_realization_sporadic
    (s : TauCeti.SporadicName) :
    Finite (nativeCarrier s) ∧ Nontrivial (nativeCarrier s) ∧ IsSimpleGroup (nativeCarrier s) := by
  by_cases hs : s = .B
  · subst hs
    exact ⟨inferInstanceAs (Finite Blueprint.NativeSporadic.B),
      Sporadic.B.fam_b_simplicity.toNontrivial, Sporadic.B.fam_b_simplicity⟩
  · exact native_carrier_finite_simple_of_ne_B s hs

open CFSG.Blueprint.NativeSporadic in
theorem cat_native_realization :
    (∀ p : ℕ, p.Prime → Finite (Multiplicative (ZMod p)) ∧ Nontrivial (Multiplicative (ZMod p)) ∧
      IsSimpleGroup (Multiplicative (ZMod p))) ∧
    (∀ n : ℕ, 5 ≤ n → Finite (alternatingGroup (Fin n)) ∧ Nontrivial (alternatingGroup (Fin n)) ∧
      IsSimpleGroup (alternatingGroup (Fin n))) ∧
    (∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f →
      ∃ (G : Type) (_ : Group G), Finite G ∧ Nontrivial G ∧ IsSimpleGroup G ∧
        CFSG.Blueprint.LieModel G t n p f) ∧
    (∀ s : TauCeti.SporadicName, Finite (nativeCarrier s) ∧ Nontrivial (nativeCarrier s) ∧
      IsSimpleGroup (nativeCarrier s)) :=
  ⟨cat_native_realization_cyclic', cat_native_realization_alternating', cat_native_realization_lie,
    cat_native_realization_sporadic⟩

end CFSG.Milestones
