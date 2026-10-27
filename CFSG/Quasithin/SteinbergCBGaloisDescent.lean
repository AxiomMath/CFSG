module

public import CFSG.Quasithin.SteinbergCBGDDescent

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

@[expose] noncomputable def frobAut (p : ℕ) [Fact p.Prime] (Fbar : Type*) [Field Fbar]
    [Algebra (ZMod p) Fbar] [IsAlgClosure (ZMod p) Fbar] : Fbar ≃+* Fbar :=
  letI : CharP Fbar p := charP_of_injective_algebraMap (algebraMap (ZMod p) Fbar).injective p
  letI : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed (ZMod p)
  frobeniusEquiv Fbar p

variable {p : ℕ} [hp : Fact p.Prime]

theorem frobAut_apply {Fbar : Type*} [Field Fbar] [Algebra (ZMod p) Fbar]
    [IsAlgClosure (ZMod p) Fbar] (x : Fbar) : frobAut p Fbar x = x ^ p := rfl

variable {K : Type*} [Field K] {σ : K ≃+* K} {X : Type*} [Group X] {d : ℕ}

theorem exists_entries_fixF [Fintype X] (hK : ∀ x : K, ∃ n, 1 ≤ n ∧ x ∈ fixF σ n)
    (ρ : X →* GL (Fin d) K) :
    ∃ n, 1 ≤ n ∧ ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) K) i j ∈ fixF σ n := by
  classical
  obtain ⟨n, hn, hS⟩ := exists_fixF_of_finset hK
    (Finset.univ.image fun t : X × Fin d × Fin d => (ρ t.1 : Matrix (Fin d) (Fin d) K) t.2.1 t.2.2)
  exact ⟨n, hn, fun g i j => hS _ (Finset.mem_image.2 ⟨(g, i, j), Finset.mem_univ _, rfl⟩)⟩

theorem realizable_of_entries {ρ : X →* GL (Fin d) K} {E : Subfield K}
    (h : ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) K) i j ∈ E) : Realizable ρ E :=
  ⟨1, fun g i j => by simpa using h g i j⟩

theorem traceField_le_of_entries {ρ : X →* GL (Fin d) K} {E : Subfield K}
    (h : ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) K) i j ∈ E) : traceField ρ ≤ E :=
  (realizable_of_entries h).traceField_le

theorem traceField_le_eqLocus {ρ : X →* GL (Fin d) K} {τ : K ≃+* K}
    (h : ∀ g, τ (Matrix.trace (ρ g : Matrix (Fin d) (Fin d) K)) =
      Matrix.trace (ρ g : Matrix (Fin d) (Fin d) K)) :
    ∀ x ∈ traceField ρ, τ x = x := by
  have hle : traceField ρ ≤ RingHom.eqLocusField (τ : K →+* K) (RingHom.id K) := by
    rw [traceField, Subfield.closure_le]
    rintro _ ⟨g, rfl⟩
    exact RingHom.mem_eqLocusField.2 (h g)
  intro x hx
  exact RingHom.mem_eqLocusField.1 (hle hx)


theorem realizable_iff_exists_hom {ρ : X →* GL (Fin d) K} {E : Subfield K} :
    Realizable ρ E ↔ ∃ ρ₀ : X →* GL (Fin d) E,
      RepIso ((Matrix.GeneralLinearGroup.map E.subtype).comp ρ₀) ρ := by
  constructor
  · rintro ⟨P, hP⟩
    have hinj : Function.Injective fun N : Matrix (Fin d) (Fin d) E => N.map E.subtype :=
      Matrix.map_injective Subtype.val_injective
    let M : X → Matrix (Fin d) (Fin d) E := fun g => Matrix.of fun i j => ⟨_, hP g i j⟩
    have hM : ∀ g, (M g).map E.subtype = ((P * ρ g * P⁻¹ : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) := fun g => by
      ext i j
      rfl
    have hmul : ∀ g h, M (g * h) = M g * M h := by
      intro g h
      apply hinj
      change (M (g * h)).map E.subtype = (M g * M h).map E.subtype
      rw [Matrix.map_mul, hM, hM, hM, ← Units.val_mul]
      congr 1
      rw [map_mul]
      group
    have hone : M 1 = 1 := by
      apply hinj
      change (M 1).map E.subtype = (1 : Matrix (Fin d) (Fin d) E).map E.subtype
      rw [hM, map_one, mul_one, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _)
        (map_one _)]
    let ρ₀ : X →* GL (Fin d) E :=
      { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
          by rw [← hmul, inv_mul_cancel, hone]⟩
        map_one' := Units.ext hone
        map_mul' := fun g h => Units.ext (hmul g h) }
    refine ⟨ρ₀, P⁻¹, fun g => ?_⟩
    have hg : Matrix.GeneralLinearGroup.map E.subtype (ρ₀ g) = P * ρ g * P⁻¹ := Units.ext (hM g)
    rw [MonoidHom.comp_apply, hg]
    group
  · rintro ⟨ρ₀, Q, hQ⟩
    refine ⟨Q⁻¹, fun g i j => ?_⟩
    have h : Q⁻¹ * ρ g * Q⁻¹⁻¹ = Matrix.GeneralLinearGroup.map E.subtype (ρ₀ g) := by
      rw [hQ g, MonoidHom.comp_apply]
      group
    rw [h, Matrix.GeneralLinearGroup.map_apply]
    exact (ρ₀ g i j).2

variable [CharP K p] [IsAlgClosed K]

theorem repIso_twist_iff (hσ : ∀ x, σ x = x ^ p) {ρ : X →* GL (Fin d) K}
    {e : ℕ} (he : 1 ≤ e) (hK : traceField ρ = fixF σ e)
    (hreal : Realizable ρ (traceField ρ)) (i : ℤ) :
    RepIso (twistRep (σ ^ i) ρ) ρ ↔ (e : ℤ) ∣ i := by
  rw [← zpow_fix_iff hσ he i, ← hK]
  constructor
  · intro h
    apply traceField_le_eqLocus
    intro g
    rw [← trace_twistRep]
    exact (h.trace_eq g).symm
  · intro h
    exact hreal.repIso_twistRep h

theorem fixF_le_iff (hσ : ∀ x, σ x = x ^ p) {e m : ℕ} (he : 1 ≤ e) :
    fixF σ e ≤ fixF σ m ↔ e ∣ m := by
  constructor
  · intro h
    have := (zpow_fix_iff hσ he (m : ℤ)).1 fun x hx => by
      rw [zpow_natCast]
      exact mem_fixF.1 (h hx)
    exact Int.natCast_dvd_natCast.1 this
  · exact fixF_le_of_dvd

theorem mem_fixF_of_isAlgClosure {Fbar : Type*} [Field Fbar] [Algebra (ZMod p) Fbar]
    [IsAlgClosure (ZMod p) Fbar] [CharP Fbar p] [IsAlgClosed Fbar] {τ : Fbar ≃+* Fbar}
    (hτ : ∀ x, τ x = x ^ p) (x : Fbar) : ∃ n, 1 ≤ n ∧ x ∈ fixF τ n := by
  have : Algebra.IsAlgebraic (ZMod p) Fbar := IsAlgClosure.isAlgebraic
  have hx : IsIntegral (ZMod p) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hx
  have hfin : Finite (IntermediateField.adjoin (ZMod p) {x}) := Module.finite_of_finite (ZMod p)
  have : Finite (IntermediateField.adjoin (ZMod p) {x}).toSubfield := hfin
  obtain ⟨n, hn, -, hE⟩ := exists_eq_fixF hτ (IntermediateField.adjoin (ZMod p) {x}).toSubfield
  refine ⟨n, hn, ?_⟩
  rw [← hE]
  exact IntermediateField.mem_adjoin_simple_self (ZMod p) x

theorem finite_field_galois_descent {Fbar : Type*} [Field Fbar] [Algebra (ZMod p) Fbar]
    [IsAlgClosure (ZMod p) Fbar] {X : Type*} [Group X] [Finite X] {d : ℕ} (hd : 1 ≤ d)
    (ρ : X →* GL (Fin d) Fbar) (hρ : IsIrredRep ρ) :
    (∀ m : ℕ, 1 ≤ m → ∃! E : Subfield Fbar, Nat.card E = p ^ m) ∧
    (∀ (i : ℤ) (P : GL (Fin d) Fbar),
      RepIso (twistRep (frobAut p Fbar ^ i) (conjRep P ρ)) (twistRep (frobAut p Fbar ^ i) ρ)) ∧
    (∀ E : Subfield Fbar, Realizable ρ E ↔ ∃ ρ₀ : X →* GL (Fin d) E,
      RepIso ((Matrix.GeneralLinearGroup.map E.subtype).comp ρ₀) ρ) ∧
    (∃ E : Subfield Fbar, Finite E ∧ Realizable ρ E) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ E : Subfield Fbar, Nat.card E = p ^ m →
      (Realizable ρ E ↔ RepIso (twistRep (frobAut p Fbar ^ (m : ℤ)) ρ) ρ)) ∧
    ∃ e : ℕ, 1 ≤ e ∧ Nat.card (traceField ρ) = p ^ e ∧
      RepIso (twistRep (frobAut p Fbar ^ (e : ℤ)) ρ) ρ ∧
      (∀ e' : ℕ, 1 ≤ e' → RepIso (twistRep (frobAut p Fbar ^ (e' : ℤ)) ρ) ρ → e ≤ e') ∧
      (∀ i : ℤ, RepIso (twistRep (frobAut p Fbar ^ i) ρ) ρ ↔ (e : ℤ) ∣ i) ∧
      (∀ E : Subfield Fbar, Realizable ρ E ↔ traceField ρ ≤ E) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ En : Subfield Fbar, Nat.card En = p ^ n → Realizable ρ En →
        ∀ m : ℕ, 1 ≤ m → ∀ Em : Subfield Fbar, Nat.card Em = p ^ m →
          (Realizable ρ Em ↔ RepIso (twistRep (frobAut p Fbar ^ (m : ℤ)) ρ) ρ) ∧
          (RepIso (twistRep (frobAut p Fbar ^ (m : ℤ)) ρ) ρ ↔
            RepIso (twistRep (frobAut p Fbar ^ (Nat.gcd m n : ℤ)) ρ) ρ) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : CharP Fbar p := charP_of_injective_algebraMap (algebraMap (ZMod p) Fbar).injective p
  have : IsAlgClosed Fbar := IsAlgClosure.isAlgClosed (ZMod p)
  set σ := frobAut p Fbar with hσdef
  have hσ : ∀ x, σ x = x ^ p := frobAut_apply
  have hK := mem_fixF_of_isAlgClosure (p := p) hσ
  obtain ⟨n0, hn0, hent⟩ := exists_entries_fixF hK ρ
  have htrle : traceField ρ ≤ fixF σ n0 := traceField_le_of_entries hent
  have := finite_fixF hσ hn0
  have : Finite (traceField ρ) :=
    Finite.Set.subset ((fixF σ n0 : Subfield Fbar) : Set Fbar) htrle
  obtain ⟨e, he, hcard, hKe⟩ := exists_eq_fixF hσ (traceField ρ)
  have hentK : ∀ g i j, (ρ g : Matrix (Fin d) (Fin d) Fbar) i j ∈ fixF σ (e * n0) :=
    fun g i j => fixF_le_of_dvd (dvd_mul_left n0 e) (hent g i j)
  have hrealK : Realizable ρ (traceField ρ) := by
    rw [hKe]
    exact realizable_of_traceField_le hσ hd hρ he hn0 hKe.le hentK
  have hreal_iff : ∀ E : Subfield Fbar, Realizable ρ E ↔ traceField ρ ≤ E :=
    fun E => ⟨fun h => h.traceField_le, fun h => hrealK.mono h⟩
  have htw := repIso_twist_iff (ρ := ρ) hσ he hKe hrealK
  have h2 : ∀ m : ℕ, 1 ≤ m → ∀ E : Subfield Fbar, Nat.card E = p ^ m →
      (Realizable ρ E ↔ RepIso (twistRep (σ ^ (m : ℤ)) ρ) ρ) := by
    intro m hm E hE
    rw [eq_fixF_of_card hσ hm hE, hreal_iff, hKe, fixF_le_iff hσ he, htw,
      Int.natCast_dvd_natCast]
  refine ⟨fun m hm => ⟨fixF σ m, card_fixF hσ hm, fun E hE => eq_fixF_of_card hσ hm hE⟩,
    fun i P => ((repIso_conjRep P ρ).twist _).symm, fun E => realizable_iff_exists_hom,
    ⟨fixF σ n0, finite_fixF hσ hn0, realizable_of_entries hent⟩, h2,
    e, he, hcard, (htw e).2 dvd_rfl, fun e' he' h => ?_, htw, hreal_iff, ?_⟩
  · exact Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.1 ((htw e').1 h))
  · intro n hn En hEn hrealn m hm Em hEm
    refine ⟨h2 m hm Em hEm, ?_⟩
    have hen : e ∣ n := by
      have := (h2 n hn En hEn).1 hrealn
      exact Int.natCast_dvd_natCast.1 ((htw n).1 this)
    rw [htw, htw, Int.natCast_dvd_natCast, Int.natCast_dvd_natCast, Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨h, hen⟩, fun h => h.1⟩

end CFSG.Quasithin.SteinbergCB.GDescent
