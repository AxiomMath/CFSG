module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem exists_conj_of_mem_sup {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G))
    {m z z' : G} (hz : z ∈ centerOf A) (hm : m ∈ A ⊔ C) (hmz : m * z * m⁻¹ = z') :
    ∃ c ∈ C, c * z * c⁻¹ = z' := by
  have hm' : m ∈ (↑(A ⊔ C) : Set G) := hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A C hC] at hm'
  obtain ⟨a, ha, c, hc, rfl⟩ := hm'
  refine ⟨c, hc, ?_⟩
  have hcz : c * z * c⁻¹ ∈ centerOf A := conj_mem_centerOf (hC hc) hz
  have h1 : a * (c * z * c⁻¹) = (c * z * c⁻¹) * a :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcz).2) a ha
  rw [← hmz]
  calc c * z * c⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by rw [h1]; group
    _ = a * c * z * (a * c)⁻¹ := by group

theorem exists_fixed_of_odd_ncard {T : Subgroup G} (hT : IsPGroup 2 T) {X : Set G}
    (hodd : Odd X.ncard) (hinv : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    ∃ x ∈ X, ∀ t ∈ T, t * x * t⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : X.Finite := Set.finite_of_ncard_pos (by obtain ⟨k, hk⟩ := hodd; omega)
  have : Finite ↥X := hfin.to_subtype
  let act : MulAction ↥T ↥X :=
    { smul := fun t x => ⟨t * x * t⁻¹, hinv t t.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : T) : G) * (x : G) * ((1 : T) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        show ((s * t : T) : G) * (x : G) * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * (x : G) * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  have hmod := hT.card_modEq_card_fixedPoints ↥X
  have hcard : Nat.card ↥X = X.ncard := Nat.card_coe_set_eq X
  have hne : Nonempty (MulAction.fixedPoints ↥T ↥X) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Nat.card (MulAction.fixedPoints ↥T ↥X) = 0 := Nat.card_of_isEmpty
    rw [h0, hcard] at hmod
    obtain ⟨k, hk⟩ := hodd
    have := Nat.modEq_zero_iff_dvd.mp hmod
    omega
  obtain ⟨⟨x, hx⟩, hxfix⟩ := hne
  refine ⟨x, hx, fun t ht => ?_⟩
  have := congrArg Subtype.val (hxfix ⟨t, ht⟩)
  exact this

end CFSG.Quasithin.H13.Sec53F
