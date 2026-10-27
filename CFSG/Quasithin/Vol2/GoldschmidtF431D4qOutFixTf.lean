module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem card_le_card_ker_mul {Q Z : Subgroup G} (hZQ : Z ≤ Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z) {w : G}
    (hw : w ∈ Q) :
    ∃ φ : ↥Q →* ↥Z, (∀ x : ↥Q, φ x = 1 ↔ (x : G) * w = w * x) ∧
      Nat.card Q ≤ Nat.card φ.ker * Nat.card Z := by
  have hmul : ∀ x y : ↥Q, ⁅((x * y : ↥Q) : G), w⁆ = ⁅(x : G), w⁆ * ⁅(y : G), w⁆ := by
    intro x y
    have hc : ((y : G) * w * (y : G)⁻¹) = ⁅(y : G), w⁆ * w := by
      rw [commutatorElement_def]
      group
    have hcx : (x : G) * ⁅(y : G), w⁆ = ⁅(y : G), w⁆ * (x : G) :=
      (hZc _ (hcomm y y.2 w hw) x x.2).symm
    have hzz : ⁅(y : G), w⁆ * ⁅(x : G), w⁆ = ⁅(x : G), w⁆ * ⁅(y : G), w⁆ :=
      hZc _ (hcomm y y.2 w hw) _ (hZQ (hcomm x x.2 w hw))
    calc ⁅((x * y : ↥Q) : G), w⁆ = (x : G) * ((y : G) * w * (y : G)⁻¹) * (x : G)⁻¹ * w⁻¹ := by
          rw [commutatorElement_def]
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
      _ = (x : G) * (⁅(y : G), w⁆ * w) * (x : G)⁻¹ * w⁻¹ := by rw [hc]
      _ = ((x : G) * ⁅(y : G), w⁆) * (w * (x : G)⁻¹ * w⁻¹) := by group
      _ = (⁅(y : G), w⁆ * (x : G)) * (w * (x : G)⁻¹ * w⁻¹) := by rw [hcx]
      _ = ⁅(y : G), w⁆ * ⁅(x : G), w⁆ := by rw [commutatorElement_def (x : G) w]; group
      _ = ⁅(x : G), w⁆ * ⁅(y : G), w⁆ := hzz
  let φ : ↥Q →* ↥Z :=
    { toFun := fun x => ⟨⁅(x : G), w⁆, hcomm x x.2 w hw⟩
      map_one' := by
        refine Subtype.ext ?_
        simp [commutatorElement_def]
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  refine ⟨φ, fun x => ?_, ?_⟩
  · constructor
    · intro h
      have h1 : ⁅(x : G), w⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_def] at h1
      calc (x : G) * w = ((x : G) * w * (x : G)⁻¹ * w⁻¹) * (w * (x : G)) := by group
        _ = w * (x : G) := by rw [h1, one_mul]
    · intro h
      refine Subtype.ext ?_
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one]
      rw [commutatorElement_def, h]
      group
  · have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ Nat.card Z :=
      Nat.card_le_card_of_injective (fun z : φ.range => (z : ↥Z)) Subtype.val_injective
    rw [← h1]
    exact Nat.mul_le_mul_left _ h2

end Generic

theorem six_mul_lt_two_pow (e : ℕ) : 6 * e < 2 ^ (4 * e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : 1 ≤ 2 ^ (4 * e) := Nat.one_le_two_pow
    have h2 : 2 ^ (4 * (e + 1)) = 16 * 2 ^ (4 * e) := by
      rw [show 4 * (e + 1) = 4 * e + 4 by ring, pow_add]
      ring
    omega

section Tf


variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {f e : ℕ} (hf : 1 ≤ f) (hfe : f = 2 * e)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include hf hfe hK hσ hδ in
theorem card_Tg_lt {S2 : Subgroup (K ≃+* K)} {T : Subgroup (MulAut (Cm σ))}
    (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S2, α = MulAut.conj u *
      fieldActor σ δ') (Q Z : Subgroup (Cm σ)) (hQU : Q ≤ Ust σ) (hZQ : Z ≤ Q)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z) (hZc : ∀ z ∈ Z, ∀ x ∈ Q, z * x = x * z)
    (hQZ : (2 ^ f) ^ 8 * Nat.card Z ≤ Nat.card Q) {w : Cm σ} (hw : w ∈ Q) :
    Nat.card (Tg σ δ T) <
      Nat.card ↥(T ⊓ Subgroup.centralizer ({(MulAut.conj w : MulAut (Cm σ))} :
        Set (MulAut (Cm σ)))) := by
  have hf' := hf
  subst hfe
  have he : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (6 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 6 * e) hK6
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hS2 : Nat.card S2 ≤ 6 * e :=
    Nat.le_of_dvd (by omega) (hAut ▸ Subgroup.card_subgroup_dvd_card S2)
  have hTg := card_Tg σ δ hf' hK hσ hT
  have hUg := card_Ug σ δ he hK hσ hδ
  obtain ⟨φ, hφ1, hφ2⟩ := card_le_card_ker_mul hZQ hcomm hZc hw
  have hq : 0 < 2 ^ (2 * e) := Nat.two_pow_pos _
  have hker : (2 ^ (2 * e)) ^ 8 ≤ Nat.card φ.ker := by
    have h1 : (2 ^ (2 * e)) ^ 8 * Nat.card Z ≤ Nat.card φ.ker * Nat.card Z := hQZ.trans hφ2
    exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hinj : Nat.card φ.ker ≤ Nat.card ↥(T ⊓ Subgroup.centralizer
      ({(MulAut.conj w : MulAut (Cm σ))} : Set (MulAut (Cm σ)))) := by
    refine Nat.card_le_card_of_injective (fun c : φ.ker => (⟨MulAut.conj ((c.1 : ↥Q) : Cm σ),
      ?_, ?_⟩ : ↥(T ⊓ Subgroup.centralizer ({(MulAut.conj w : MulAut (Cm σ))} :
        Set (MulAut (Cm σ)))))) ?_
    · exact (hT _).2 ⟨((c.1 : ↥Q) : Cm σ), hQU c.1.2, 1, S2.one_mem,
        by rw [fieldActor_one, mul_one]⟩
    · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff.1 hh, ← map_mul, ← map_mul]
      exact congrArg MulAut.conj ((hφ1 c.1).1 c.2).symm
    · intro a b hab
      have h1 := conj_injective σ (congrArg (fun x : ↥(T ⊓ Subgroup.centralizer
        ({(MulAut.conj w : MulAut (Cm σ))} : Set (MulAut (Cm σ)))) => (x : MulAut (Cm σ))) hab)
      exact Subtype.ext (Subtype.ext h1)
  have hsq : 6 * e < (2 ^ (2 * e)) ^ 2 := by
    rw [← pow_mul]
    have := six_mul_lt_two_pow e
    rwa [show 2 * e * 2 = 4 * e by ring]
  calc Nat.card (Tg σ δ T) = (2 ^ (2 * e)) ^ 6 * Nat.card S2 := by rw [hTg, hUg]
    _ < (2 ^ (2 * e)) ^ 6 * (2 ^ (2 * e)) ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt hS2 hsq) (by positivity)
    _ = (2 ^ (2 * e)) ^ 8 := by ring
    _ ≤ Nat.card φ.ker := hker
    _ ≤ _ := hinj

end Tf

end CFSG.Quasithin.H13.F431.D4q.Out
