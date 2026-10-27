module

public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.FischerOddCore.Fi24Stab

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.Sporadic.Fi24 (R D24 tR)

theorem dvd_of_odd_of_dvd_eight_mul {a n : ℕ} (ha : Odd a) (h : a ∣ 8 * n) : a ∣ n := by
  have hc : Nat.Coprime a 8 := by
    have : Nat.Coprime a (2 ^ 3) := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 ha)
    simpa using this
  exact hc.dvd_of_dvd_mul_left h

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_conj_fix {r x : G} (h : r * x * r⁻¹ = x) : x * r = r * x := by
  calc x * r = r * x * r⁻¹ * r := by rw [h]
    _ = r * x := by group

omit [Finite G] in
theorem oddCore_inf_comm {A B : Subgroup G} (h : CFSG.oddCore ↥(A ⊓ B) = ⊥) :
    CFSG.oddCore ↥(B ⊓ A) = ⊥ := by
  rw [inf_comm]
  exact h

theorem card_oddCore_dvd_gcd {E : Set G} (hE : ∀ g x : G, x ∈ E → g * x * g⁻¹ ∈ E) {r : G}
    (hstab : ∀ x ∈ E, x * r = r * x →
      CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥) :
    Nat.card (CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G))) ∣
      Nat.gcd (Nat.card {x : E // r * x * r⁻¹ = x}) (Nat.card G) := by
  refine Nat.dvd_gcd (card_oddCore_dvd hE (fun x => r * x * r⁻¹ = x)
    (fun x h => commute_of_conj_fix h) hstab
    fun v _ x h => conj_fix_of_commute (Subgroup.mem_centralizer_singleton_iff.1 v.2) h) ?_
  exact (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)

theorem oddCore_centralizer_of_gcd_dvd_eight {E : Set G}
    (hE : ∀ g x : G, x ∈ E → g * x * g⁻¹ ∈ E) {r : G}
    (hstab : ∀ x ∈ E, x * r = r * x →
      CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥)
    (hq : Nat.gcd (Nat.card {x : E // r * x * r⁻¹ = x}) (Nat.card G) ∣ 8) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G)) = ⊥ := by
  have h := (card_oddCore_dvd_gcd hE hstab).trans hq
  have h1 := dvd_of_odd_of_dvd_eight_mul
    (odd_card_oddCore (G := ↥(Subgroup.centralizer ({r} : Set G)))) (n := 1) (by simpa using h)
  rw [← Subgroup.card_eq_one]
  exact Nat.dvd_one.1 h1

theorem oddCore_centralizer_of_fourth_derived_fixed {E : Set G}
    (hE : ∀ g x : G, x ∈ E → g * x * g⁻¹ ∈ E) {r : G}
    (hstab : ∀ x ∈ E, x * r = r * x →
      CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥)
    (hq : Nat.gcd (Nat.card {x : E // r * x * r⁻¹ = x}) (Nat.card G) ∣ 8 * 63 ∨
      Nat.gcd (Nat.card {x : E // r * x * r⁻¹ = x}) (Nat.card G) ∣ 8 * 87)
    {k : ℕ} (w : Fin k → ↥(Subgroup.centralizer ({r} : Set G)))
    (hw : ∀ i, w i ∈ derivedSeries ↥(Subgroup.centralizer ({r} : Set G)) 4) {m : ℕ}
    (hfix : Nat.card {x : E // r * x * r⁻¹ = x ∧
      ∀ i, (w i : G) * x * (w i : G)⁻¹ = x} = 2 ^ m) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G)) = ⊥ := by
  have hcom : ∀ c : Subgroup.centralizer ({r} : Set G), (c : G) * r = r * c := fun c =>
    Subgroup.mem_centralizer_singleton_iff.1 c.2
  let act : MulAction (Subgroup.centralizer ({r} : Set G)) {x : E // r * x * r⁻¹ = x} :=
    { smul := fun c x => ⟨⟨(c : G) * x * (c : G)⁻¹, hE _ _ x.1.2⟩,
        conj_fix_of_commute (hcom c) x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        show (1 : G) * ((x : E) : G) * (1 : G)⁻¹ = ((x : E) : G)
        simp
      mul_smul := fun c d x => by
        apply Subtype.ext
        apply Subtype.ext
        show (((c : G) * (d : G) : G)) * ((x : E) : G) * ((c : G) * (d : G))⁻¹ =
          (c : G) * ((d : G) * ((x : E) : G) * (d : G)⁻¹) * (c : G)⁻¹
        group }
  have hfree : ∀ v ∈ CFSG.oddCore (Subgroup.centralizer ({r} : Set G)),
      ∀ ω : {x : E // r * x * r⁻¹ = x}, v • ω = ω → v = 1 := by
    intro v hv ω hvω
    have h : (v : G) * ω * (v : G)⁻¹ = ω :=
      congrArg (fun y : {x : E // r * x * r⁻¹ = x} => ((y : E) : G)) hvω
    exact eq_one_of_mem_oddCore_of_fix (hstab ω ω.1.2 (commute_of_conj_fix ω.2)) hv h
  have hodd := odd_card_oddCore (G := Subgroup.centralizer ({r} : Set G))
  have hcard : Nat.card (CFSG.oddCore (Subgroup.centralizer ({r} : Set G))) ∣ 63 ∨
      Nat.card (CFSG.oddCore (Subgroup.centralizer ({r} : Set G))) ∣ 87 := by
    rcases hq with h | h
    · exact Or.inl (dvd_of_odd_of_dvd_eight_mul hodd ((card_oddCore_dvd_gcd hE hstab).trans h))
    · exact Or.inr (dvd_of_odd_of_dvd_eight_mul hodd ((card_oddCore_dvd_gcd hE hstab).trans h))
  have e : {ω : {x : E // r * x * r⁻¹ = x} // ∀ i, w i • ω = ω} ≃
      {x : E // r * x * r⁻¹ = x ∧ ∀ i, (w i : G) * x * (w i : G)⁻¹ = x} :=
    { toFun := fun ω => ⟨ω.1.1, ω.1.2, fun i =>
        congrArg (fun y : {x : E // r * x * r⁻¹ = x} => ((y : E) : G)) (ω.2 i)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun i => Subtype.ext (Subtype.ext (x.2.2 i))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfix' : Nat.card {ω : {x : E // r * x * r⁻¹ = x} // ∀ i, w i • ω = ω} = 2 ^ m := by
    rw [Nat.card_congr e, hfix]
  exact
    CFSG.ComponentClassification.LiteratureLocal.small_odd_semiregular_core_fourth_derived_fixed_set
      (CFSG.oddCore_normal (G := Subgroup.centralizer ({r} : Set G))) hfree hcard w hw hfix'

end Generic

theorem card_R_eq :
    Nat.card R = 2510411418381323442585600 := Fi24.card_R

theorem fi24_hstab
    {r : R} (hr : orderOf r = 2) : ∀ x ∈ D24, x * r = r * x →
    CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥ := by
  intro x hx hxr
  have hrx : r * x * r⁻¹ = x := by rw [← hxr, mul_inv_cancel_right]
  exact @oddCore_inf_comm R inferInstance _ _
    (CTUC_Fi24_involution_point_stabilizers_odd_core_trivial r hr x hx hrx)

theorem fi24_oddCore_of_count
    {r : R} (hr : orderOf r = 2)
    (hq : Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ :=
  @oddCore_centralizer_of_gcd_dvd_eight R inferInstance inferInstance D24
    (fun g _ hx => Fi24.conj_mem_D24 g hx) r (fi24_hstab hr) (by rw [card_R_eq]; exact hq)

theorem fi24_oddCore_of_wit
    {r : R} (hr : orderOf r = 2)
    (hq : Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 63 ∨
      Nat.gcd (Nat.card {x : D24 // r * x * r⁻¹ = x}) 2510411418381323442585600 ∣ 8 * 87)
    {k : ℕ} (w : Fin k → ↥(Subgroup.centralizer ({r} : Set R)))
    (hw : ∀ i, w i ∈ derivedSeries ↥(Subgroup.centralizer ({r} : Set R)) 4) {m : ℕ}
    (hfix : Nat.card {x : D24 // r * x * r⁻¹ = x ∧
      ∀ i, (w i : R) * x * (w i : R)⁻¹ = x} = 2 ^ m) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set R)) = ⊥ :=
  @oddCore_centralizer_of_fourth_derived_fixed R inferInstance inferInstance D24
    (fun g _ hx => Fi24.conj_mem_D24 g hx) r (fi24_hstab hr) (by rw [card_R_eq]; exact hq) k w
    hw m hfix

end CFSG.Sporadic.FischerOddCore
