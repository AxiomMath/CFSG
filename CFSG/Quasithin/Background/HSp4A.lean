module

public import CFSG.Quasithin.Background.HSp4M

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose tau coe_tau lam
  coe_lam radical mem_unipotent_iff eq_sym2 tau_congr lam_zero unitri)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

theorem card_le_two_mul_of_mul_mem {G : Type*} [Group G] {A H : Subgroup G} [Finite A]
    (hHA : H ≤ A) (h : ∀ x ∈ A, ∀ y ∈ A, x ∉ H → y ∉ H → x * y ∈ H) :
    Nat.card A ≤ 2 * Nat.card H := by
  classical
  have : Finite H := Finite.of_injective (Subgroup.inclusion hHA)
    (Subgroup.inclusion_injective hHA)
  by_cases hs : ∃ s ∈ A, s ∉ H
  · obtain ⟨s, hsA, hs⟩ := hs
    let f : A → H ⊕ H := fun x =>
      if hx : (x : G) ∈ H then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨s * x, h s hsA x x.2 hs hx⟩
    have hf : Function.Injective f := by
      intro x x' hxx'
      by_cases hx : (x : G) ∈ H <;> by_cases hx' : (x' : G) ∈ H <;>
        simp [f, hx, hx'] at hxx' <;>
        first
        | exact Subtype.ext hxx'
        | exact Subtype.ext (congrArg Subtype.val hxx')
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at this
    omega
  · push Not at hs
    have : Nat.card A ≤ Nat.card H := Nat.card_le_card_of_injective
      (fun x : A => (⟨x, hs x x.2⟩ : H)) (fun x y hxy => Subtype.ext
        (congrArg (fun z : H => (z : G)) hxy))
    omega

theorem mQuot_le_of_card_le {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hBA : B ≤ A) {k : ℕ} (h : Nat.card A ≤ 2 ^ k * Nat.card B) :
    E3.mQuot A B ≤ k := by
  rw [E3.card_eq_two_pow_mul hA hBA] at h
  have := Nat.le_of_mul_le_mul_right h Nat.card_pos
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

@[expose] def restrictPerm {V : Type*} [CommGroup V] (P : Subgroup (MulAut V)) (W : Subgroup V)
    (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) : P →* Equiv.Perm W where
  toFun g :=
    { toFun := fun w => ⟨(g : MulAut V) w, hW g g.2 w w.2⟩
      invFun := fun w => ⟨(g : MulAut V)⁻¹ w, hW g⁻¹ (P.inv_mem g.2) w w.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem card_modEq_card_inf_fixV {V : Type*} [CommGroup V] [Finite V]
    {P : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) {W : Subgroup V}
    (hW : ∀ g ∈ P, ∀ w ∈ W, g w ∈ W) : Nat.card W ≡ Nat.card ↥(W ⊓ fixV P) [MOD p] := by
  let _ : MulAction P W := MulAction.compHom W (restrictPerm P W hW)
  have h := IsPGroup.card_modEq_card_fixedPoints (α := W) hP
  have hset : Nat.card (MulAction.fixedPoints P W) = Nat.card ↥(W ⊓ fixV P) := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun w => ⟨(w.1 : V), w.1.2, fun x hx => by
          have := w.2 ⟨x, hx⟩
          exact congrArg Subtype.val this⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun g => by
          apply Subtype.ext
          exact v.2.2 g g.2⟩
        left_inv := fun w => by ext; rfl
        right_inv := fun v => by ext; rfl }
  rw [hset] at h
  exact h

variable {K : Type} [Field K]

@[expose] def lev (g : StatedSp 2 K) : K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₁

theorem coe_tau_mul_lam {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (a : K) :
    (((tau hC * lam a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks (unitri a) (C * (unitri (-a))ᵀ) 0 (unitri (-a))ᵀ := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_tau, coe_lam, fromBlocks_multiply]
  simp

theorem unipotent_facts {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single ι₀ 1 =
        Pi.single ι₀ 1 ∧
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single ι₁ 1 = lev g • Pi.single ι₀ 1 + Pi.single ι₁ 1 ∧
      (lev g = 0 → g ∈ radical K) := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.1 hg
  have hlev : lev (tau hC * lam a) = a := by
    rw [lev, coe_tau_mul_lam]
    simp [unitri]
  refine ⟨?_, ?_, fun h0 => ?_⟩
  · rw [coe_tau_mul_lam]
    ext i
    rw [Matrix.mulVec_single_one]
    rcases i with i | i <;> fin_cases i <;> simp [unitri]
  · rw [coe_tau_mul_lam, hlev]
    ext i
    rw [Matrix.mulVec_single_one]
    rcases i with i | i <;> fin_cases i <;> simp [unitri]
  · rw [hlev] at h0
    rw [h0, lam_zero, mul_one]
    exact ⟨C, hC, rfl⟩

theorem lev_mul {g g' : StatedSp 2 K} (hg : g ∈ unipotent 2 K) (hg' : g' ∈ unipotent 2 K) :
    lev (g * g') = lev g + lev g' := by
  obtain ⟨h0, h1, -⟩ := unipotent_facts hg
  obtain ⟨-, h1', -⟩ := unipotent_facts hg'
  obtain ⟨-, h1'', -⟩ := unipotent_facts ((unipotent 2 K).mul_mem hg hg')
  have e : ((g * g' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * (g' : GL (Fin 2 ⊕ Fin 2) K) := rfl
  rw [e, Units.val_mul, ← Matrix.mulVec_mulVec, h1', Matrix.mulVec_add, Matrix.mulVec_smul,
    h0, h1] at h1''
  have := congrFun h1'' ι₀
  simp at this
  linear_combination -this

theorem radical_fix {g : StatedSp 2 K} (hg : g ∈ radical K) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single ι₀ 1 =
        Pi.single ι₀ 1 ∧
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single ι₁ 1 = Pi.single ι₁ 1 := by
  obtain ⟨C, hC, rfl⟩ := hg
  rw [coe_tau]
  constructor <;> ext i <;> rw [Matrix.mulVec_single_one] <;>
    rcases i with i | i <;> fin_cases i <;> simp

@[expose] def radA (g : StatedSp 2 K) : K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₂

@[expose] def radB (g : StatedSp 2 K) : K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₀ ι₃

@[expose] def radD (g : StatedSp 2 K) : K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ι₁ ι₃

theorem eq_upSp_of_mem_radical {g : StatedSp 2 K} (hg : g ∈ radical K) :
    g = upSp (sym2_transpose (radA g) (radB g) (radD g)) := by
  obtain ⟨C, hC, rfl⟩ := hg
  have h1 : radA (tau hC) = C 0 0 := by rw [radA, coe_tau]; simp
  have h2 : radB (tau hC) = C 0 1 := by rw [radB, coe_tau]; simp
  have h3 : radD (tau hC) = C 1 1 := by rw [radD, coe_tau]; simp
  rw [h1, h2, h3]
  exact tau_congr _ _ (eq_sym2 hC)

theorem rad_mul {g g' : StatedSp 2 K} (hg : g ∈ radical K) (hg' : g' ∈ radical K) :
    radA (g * g') = radA g + radA g' ∧ radB (g * g') = radB g + radB g' ∧
      radD (g * g') = radD g + radD g' := by
  have e : ∀ x y : StatedSp 2 K, ((x * y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      (x : GL (Fin 2 ⊕ Fin 2) K) * (y : GL (Fin 2 ⊕ Fin 2) K) := fun _ _ => rfl
  obtain ⟨C, hC, rfl⟩ := hg
  obtain ⟨E, hE, rfl⟩ := hg'
  simp only [radA, radB, radD, e, Units.val_mul, coe_tau, fromBlocks_multiply]
  simp [add_comm]

theorem radB_eq_of_radA_radD {g g' : StatedSp 2 K} (hg : g ∈ radical K) (hg' : g' ∈ radical K)
    (ha : radA g = radA g') (hb : radB g = radB g') (hd : radD g = radD g') : g = g' := by
  rw [eq_upSp_of_mem_radical hg, eq_upSp_of_mem_radical hg']
  simp only [ha, hb, hd]

theorem fix_conj_iff (h g : StatedSp 2 K) (u : StdMod (Fin 2 ⊕ Fin 2) K) :
    natAut (StatedSp 2 K) (h⁻¹ * g * h) u = u ↔
      natAut (StatedSp 2 K) g (natAut (StatedSp 2 K) h u) = natAut (StatedSp 2 K) h u := by
  rw [map_mul, map_mul, map_inv]
  change (natAut (StatedSp 2 K) h)⁻¹ (natAut (StatedSp 2 K) g (natAut (StatedSp 2 K) h u)) = u ↔
    _
  constructor
  · intro e
    rw [← MulAut.apply_inv_self _ (natAut (StatedSp 2 K) h)
      (natAut (StatedSp 2 K) g (natAut (StatedSp 2 K) h u)), e]
  · intro e
    rw [e, MulAut.inv_apply_self]

variable [CharP K 2] [Finite K]

theorem exists_conj_le_unipotent {Y : Subgroup (StatedSp 2 K)} (hY : IsPGroup 2 Y) :
    ∃ h : StatedSp 2 K, ∀ y ∈ Y, h⁻¹ * y * h ∈ unipotent 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨S, hS⟩, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFour.unique_symplectic_four_Sylow_center
      (K := K) (Nat.card K) rfl
  obtain ⟨P, hYP⟩ := hY.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (StatedSp 2 K) S P
  refine ⟨h, fun y hy => ?_⟩
  have hyP : y ∈ (P : Subgroup (StatedSp 2 K)) := hYP hy
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyP
  obtain ⟨b, hb, hby⟩ := hyP
  rw [← hby, MulAut.smul_def, MulAut.conj_apply, ← hS]
  simpa [mul_assoc] using hb

omit [CharP K 2] in
theorem mem_radical_of_fix {X : Subgroup (StatedSp 2 K)} (ρ : StatedSp 2 K →* StatedSp 2 K)
    (h : StatedSp 2 K) (hXU : ∀ x ∈ X, h⁻¹ * ρ x * h ∈ unipotent 2 K)
    (hP : ∀ D : Subgroup (StatedSp 2 K), D ≤ X → Nat.card X ≤ Nat.card K * Nat.card D →
      ∀ v : StdMod (Fin 2 ⊕ Fin 2) K, (∀ g ∈ D, natAut (StatedSp 2 K) (ρ g) v = v) →
        ∀ g ∈ X, natAut (StatedSp 2 K) (ρ g) v = v) :
    ∀ x ∈ X, h⁻¹ * ρ x * h ∈ radical K := by
  have hconj : ∀ x y : StatedSp 2 K, h⁻¹ * ρ (x * y) * h = (h⁻¹ * ρ x * h) * (h⁻¹ * ρ y * h) :=
    fun x y => by rw [map_mul]; group
  let φ : X →* Multiplicative K :=
    { toFun := fun x => Multiplicative.ofAdd (lev (h⁻¹ * ρ x * h))
      map_one' := by
        have e : h⁻¹ * ρ ((1 : X) : StatedSp 2 K) * h = 1 := by
          rw [OneMemClass.coe_one, map_one, mul_one, inv_mul_cancel]
        rw [e]
        simp [lev]
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, hconj, lev_mul (hXU x x.2) (hXU y y.2), ofAdd_add] }
  set D := φ.ker.map X.subtype with hD
  have hDX : D ≤ X := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcard : Nat.card X ≤ Nat.card K * Nat.card D := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card φ.range ≤ Nat.card K := by
      calc Nat.card φ.range ≤ Nat.card (Multiplicative K) := Finite.card_subtype_le _
        _ = Nat.card K := rfl
    have h3 : Nat.card D = Nat.card φ.ker :=
      Subgroup.card_map_of_injective X.subtype_injective
    rw [h3, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  set v := natAut (StatedSp 2 K) h (Multiplicative.ofAdd (Pi.single ι₁ (1 : K))) with hv
  have hDv : ∀ g ∈ D, natAut (StatedSp 2 K) (ρ g) v = v := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : lev (h⁻¹ * ρ x * h) = 0 := by
      have := (MonoidHom.mem_ker).mp hx
      exact congrArg Multiplicative.toAdd this
    obtain ⟨-, h1, -⟩ := unipotent_facts (hXU x x.2)
    rw [hx0, zero_smul, zero_add] at h1
    rw [hv, ← fix_conj_iff]
    exact congrArg Multiplicative.ofAdd h1
  have hXv := hP D hDX hcard v hDv
  intro x hx
  have h1 := (fix_conj_iff h (ρ x) _).mpr (hXv x hx)
  obtain ⟨-, h2, h3⟩ := unipotent_facts (hXU x hx)
  apply h3
  have h4 : ((h⁻¹ * ρ x * h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single ι₁ (1 : K) =
      Pi.single ι₁ 1 := congrArg Multiplicative.toAdd h1
  rw [h2] at h4
  have := congrFun h4 ι₀
  simpa using this

omit [Finite K] in
theorem tauSp_mulVec_of_mem_radical {g : StatedSp 2 K} (hg : g ∈ radical K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    (((tauSp g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      v + Pi.single ι₀ (radD g * v ι₁ + (radA g * radD g + radB g ^ 2) * v ι₂ + radA g * v ι₃) +
        Pi.single ι₁ (radA g * v ι₂) + Pi.single ι₃ (radD g * v ι₂) := by
  conv_lhs => rw [eq_upSp_of_mem_radical hg]
  exact tauSp_upSp_mulVec _ _ _ v

theorem false_of_fix (Â : Subgroup (StatedSp 2 K)) (hsq : ∀ x ∈ Â, x * x = 1)
    (hcard : Nat.card K < Nat.card Â)
    (hP₁ : ∀ D : Subgroup (StatedSp 2 K), D ≤ Â → Nat.card Â ≤ Nat.card K * Nat.card D →
      ∀ v : StdMod (Fin 2 ⊕ Fin 2) K, (∀ g ∈ D, natAut (StatedSp 2 K) g v = v) →
        ∀ g ∈ Â, natAut (StatedSp 2 K) g v = v)
    (hP₂ : ∀ D : Subgroup (StatedSp 2 K), D ≤ Â → Nat.card Â ≤ Nat.card K * Nat.card D →
      ∀ v : StdMod (Fin 2 ⊕ Fin 2) K, (∀ g ∈ D, natAut (StatedSp 2 K) (tauSp g) v = v) →
        ∀ g ∈ Â, natAut (StatedSp 2 K) (tauSp g) v = v) : False := by
  have hpg : IsPGroup 2 Â := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hsq x x.2)⟩
  obtain ⟨h, hh⟩ := exists_conj_le_unipotent hpg
  have hR := mem_radical_of_fix (MonoidHom.id _) h hh fun D hD hc v hv => hP₁ D hD hc v hv
  simp only [MonoidHom.id_apply] at hR
  obtain ⟨h', hh'⟩ := exists_conj_le_unipotent (hpg.map tauSp)
  have hR' := mem_radical_of_fix tauSp h' (fun x hx => hh' _ ⟨x, hx, rfl⟩) fun D hD hc v hv =>
    hP₂ D hD hc v hv
  set a : StatedSp 2 K → K := fun x => radA (h⁻¹ * x * h) with ha
  set b : StatedSp 2 K → K := fun x => radB (h⁻¹ * x * h) with hb
  set d : StatedSp 2 K → K := fun x => radD (h⁻¹ * x * h) with hd
  have hτg : ∀ x ∈ Â, ∀ u : StdMod (Fin 2 ⊕ Fin 2) K,
      natAut (StatedSp 2 K) (tauSp x) (natAut (StatedSp 2 K) (tauSp h) u) =
          natAut (StatedSp 2 K) (tauSp h) u ↔
        Multiplicative.toAdd u + Pi.single ι₀ (d x * Multiplicative.toAdd u ι₁ +
          (a x * d x + b x ^ 2) * Multiplicative.toAdd u ι₂ + a x * Multiplicative.toAdd u ι₃) +
          Pi.single ι₁ (a x * Multiplicative.toAdd u ι₂) +
          Pi.single ι₃ (d x * Multiplicative.toAdd u ι₂) = Multiplicative.toAdd u := by
    intro x hx u
    rw [← fix_conj_iff, ← map_inv, ← map_mul, ← map_mul]
    rw [show natAut (StatedSp 2 K) (tauSp (h⁻¹ * x * h)) u =
      Multiplicative.ofAdd ((((tauSp (h⁻¹ * x * h) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd u) from rfl,
      tauSp_mulVec_of_mem_radical (hR x hx)]
    constructor
    · intro e
      exact congrArg Multiplicative.toAdd e
    · intro e
      exact congrArg Multiplicative.ofAdd e
  obtain ⟨x₀, hx₀, hx₀ad⟩ : ∃ x₀ ∈ Â, a x₀ ≠ 0 ∨ d x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun x : Â => b x) := by
      intro x y hxy
      have e := radB_eq_of_radA_radD (hR x x.2) (hR y y.2)
        (((hcon x x.2).1).trans ((hcon y y.2).1).symm) hxy
        (((hcon x x.2).2).trans ((hcon y y.2).2).symm)
      apply Subtype.ext
      have := congrArg (fun z => h * z * h⁻¹) e
      simpa [mul_assoc] using this
    have h1 := Nat.card_le_card_of_injective _ hinj
    omega
  set M : StatedSp 2 K := (tauSp h)⁻¹ * h' with hM
  have hfix' : ∀ x ∈ Â, ∀ i ∈ ({ι₀, ι₁} : Set (Fin 2 ⊕ Fin 2)),
      natAut (StatedSp 2 K) (tauSp x) (natAut (StatedSp 2 K) (tauSp h)
        (natAut (StatedSp 2 K) M (Multiplicative.ofAdd (Pi.single i 1)))) =
      natAut (StatedSp 2 K) (tauSp h)
        (natAut (StatedSp 2 K) M (Multiplicative.ofAdd (Pi.single i 1))) := by
    intro x hx i hi
    have e : natAut (StatedSp 2 K) (tauSp h) (natAut (StatedSp 2 K) M
        (Multiplicative.ofAdd (Pi.single i 1))) =
        natAut (StatedSp 2 K) h' (Multiplicative.ofAdd (Pi.single i 1)) := by
      rw [hM, map_mul, map_inv]
      change natAut (StatedSp 2 K) (tauSp h) ((natAut (StatedSp 2 K) (tauSp h))⁻¹
        (natAut (StatedSp 2 K) h' _)) = _
      rw [MulAut.apply_inv_self]
    rw [e, ← fix_conj_iff]
    obtain ⟨f0, f1⟩ := radical_fix (hR' x hx)
    rcases hi with rfl | rfl
    · exact congrArg Multiplicative.ofAdd f0
    · exact congrArg Multiplicative.ofAdd f1
  set w₀ : Fin 2 ⊕ Fin 2 → K :=
    ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single ι₀ 1
    with hw₀
  set w₁ : Fin 2 ⊕ Fin 2 → K :=
    ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single ι₁ 1
    with hw₁
  have hlin : ∀ x ∈ Â, ∀ w : Fin 2 ⊕ Fin 2 → K, (natAut (StatedSp 2 K) (tauSp x)
      (natAut (StatedSp 2 K) (tauSp h) (Multiplicative.ofAdd w)) =
        natAut (StatedSp 2 K) (tauSp h) (Multiplicative.ofAdd w)) ↔
      (d x * w ι₁ + (a x * d x + b x ^ 2) * w ι₂ + a x * w ι₃ = 0 ∧ a x * w ι₂ = 0 ∧
        d x * w ι₂ = 0) := by
    intro x hx w
    rw [hτg x hx]
    simp only [toAdd_ofAdd]
    constructor
    · intro e
      exact ⟨by simpa using congrFun e ι₀, by simpa using congrFun e ι₁,
        by simpa using congrFun e ι₃⟩
    · rintro ⟨e0, e1, e3⟩
      rw [e0, e1, e3]
      simp
  have hw₀fix : ∀ x ∈ Â, d x * w₀ ι₁ + (a x * d x + b x ^ 2) * w₀ ι₂ + a x * w₀ ι₃ = 0 ∧
      a x * w₀ ι₂ = 0 ∧ d x * w₀ ι₂ = 0 := fun x hx =>
    (hlin x hx w₀).mp (hfix' x hx ι₀ (by simp))
  have hw₁fix : ∀ x ∈ Â, d x * w₁ ι₁ + (a x * d x + b x ^ 2) * w₁ ι₂ + a x * w₁ ι₃ = 0 ∧
      a x * w₁ ι₂ = 0 ∧ d x * w₁ ι₂ = 0 := fun x hx =>
    (hlin x hx w₁).mp (hfix' x hx ι₁ (by simp))
  have hz : ∀ w : Fin 2 ⊕ Fin 2 → K, a x₀ * w ι₂ = 0 → d x₀ * w ι₂ = 0 → w ι₂ = 0 := by
    intro w e1 e3
    rcases hx₀ad with h0 | h0
    · exact (mul_eq_zero.mp e1).resolve_left h0
    · exact (mul_eq_zero.mp e3).resolve_left h0
  have hw₀2 := hz w₀ (hw₀fix x₀ hx₀).2.1 (hw₀fix x₀ hx₀).2.2
  have hw₁2 := hz w₁ (hw₁fix x₀ hx₀).2.1 (hw₁fix x₀ hx₀).2.2
  have hMinj : ∀ y : Fin 2 ⊕ Fin 2 → K,
      ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y = 0 → y = 0 := by
    intro y hy
    have := congrArg (fun z => (((M⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ z) hy
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
      Matrix.one_mulVec] at this
    exact this
  obtain ⟨w, hw0, hwι₀, hwι₂, hwfix⟩ : ∃ w : Fin 2 ⊕ Fin 2 → K, w ≠ 0 ∧ w ι₀ = 0 ∧ w ι₂ = 0 ∧
      ∀ x ∈ Â, d x * w ι₁ + a x * w ι₃ = 0 := by
    by_cases hc : w₁ ι₀ = 0 ∧ w₀ ι₀ = 0
    · refine ⟨w₀, fun h0 => ?_, hc.2, hw₀2, fun x hx => ?_⟩
      · have := hMinj _ h0
        have := congrFun this ι₀
        simp at this
      · have := (hw₀fix x hx).1
        rw [hw₀2] at this
        linear_combination this
    · refine ⟨w₁ ι₀ • w₀ - w₀ ι₀ • w₁, fun h0 => hc ?_, by simp; ring, by simp [hw₀2, hw₁2],
        fun x hx => ?_⟩
      · have h1 : ((M : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            (w₁ ι₀ • Pi.single ι₀ 1 - w₀ ι₀ • Pi.single ι₁ 1) = 0 := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hw₀, ← hw₁]
          exact h0
        have h2 := hMinj _ h1
        have e0 := congrFun h2 ι₀
        have e1 := congrFun h2 ι₁
        simp at e0 e1
        exact ⟨e0, e1⟩
      · have e0 := (hw₀fix x hx).1
        have e1 := (hw₁fix x hx).1
        rw [hw₀2] at e0
        rw [hw₁2] at e1
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination w₁ ι₀ * e0 - w₀ ι₀ * e1
  have hw13 : w ι₁ ≠ 0 ∨ w ι₃ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0
    funext i
    rcases i with i | i <;> fin_cases i
    · exact hwι₀
    · exact hcon.1
    · exact hwι₂
    · exact hcon.2
  have hconj : ∀ x y : StatedSp 2 K, h⁻¹ * (x * y) * h = (h⁻¹ * x * h) * (h⁻¹ * y * h) :=
    fun x y => by group
  let ψ : Â →* Multiplicative (K × K) :=
    { toFun := fun x => Multiplicative.ofAdd (a x, d x)
      map_one' := by
        have e : h⁻¹ * ((1 : Â) : StatedSp 2 K) * h = 1 := by
          rw [OneMemClass.coe_one, mul_one, inv_mul_cancel]
        simp only [ha, hd, e]
        simp [radA, radD]
      map_mul' := fun x y => by
        simp only [ha, hd, Subgroup.coe_mul, hconj]
        obtain ⟨h1, -, h3⟩ := rad_mul (hR x x.2) (hR y y.2)
        rw [h1, h3]
        rfl }
  set D := ψ.ker.map Â.subtype with hD
  have hDÂ : D ≤ Â := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcardD : Nat.card Â ≤ Nat.card K * Nat.card D := by
    have h1 := ψ.ker.card_mul_index
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card ψ.range ≤ Nat.card K := by
      by_cases h3 : w ι₃ = 0
      · have hw1 := hw13.resolve_right (not_not.mpr h3)
        refine Nat.card_le_card_of_injective (fun p => (Multiplicative.toAdd p.1).1) ?_
        rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩ hxy
        have ex := hwfix x x.2
        have ey := hwfix y y.2
        rw [h3, mul_zero, add_zero] at ex ey
        have hdx := (mul_eq_zero.mp ex).resolve_right hw1
        have hdy := (mul_eq_zero.mp ey).resolve_right hw1
        apply Subtype.ext
        change Multiplicative.ofAdd (a x, d x) = Multiplicative.ofAdd (a y, d y)
        rw [hdx, hdy]
        exact congrArg (fun z => Multiplicative.ofAdd (z, (0 : K))) hxy
      · refine Nat.card_le_card_of_injective (fun p => (Multiplicative.toAdd p.1).2) ?_
        rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩ hxy
        have ex := hwfix x x.2
        have ey := hwfix y y.2
        change d x = d y at hxy
        have hax : a x = a y := by
          have : (a x - a y) * w ι₃ = 0 := by linear_combination ex - ey - w ι₁ * hxy
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h3)
        apply Subtype.ext
        change Multiplicative.ofAdd (a x, d x) = Multiplicative.ofAdd (a y, d y)
        rw [hax, hxy]
    have h3 : Nat.card D = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective Â.subtype_injective
    rw [h3, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  have hDfix : ∀ i ∈ ({ι₁, ι₃} : Set (Fin 2 ⊕ Fin 2)), ∀ g ∈ D,
      natAut (StatedSp 2 K) (tauSp g) (natAut (StatedSp 2 K) (tauSp h)
        (Multiplicative.ofAdd (Pi.single i 1))) =
      natAut (StatedSp 2 K) (tauSp h) (Multiplicative.ofAdd (Pi.single i 1)) := by
    rintro i hi _ ⟨x, hx, rfl⟩
    simp only [Subgroup.coe_subtype]
    have hx0 : a x = 0 ∧ d x = 0 := by
      have := congrArg Multiplicative.toAdd ((MonoidHom.mem_ker).mp hx)
      exact Prod.ext_iff.mp this
    rw [hlin x x.2, hx0.1, hx0.2]
    rcases hi with rfl | rfl <;> simp
  have hfix1 := hP₂ D hDÂ hcardD _ (hDfix ι₁ (by simp)) x₀ hx₀
  have hfix3 := hP₂ D hDÂ hcardD _ (hDfix ι₃ (by simp)) x₀ hx₀
  rw [hlin x₀ hx₀] at hfix1 hfix3
  simp at hfix1 hfix3
  rcases hx₀ad with h0 | h0
  · exact h0 hfix3
  · exact h0 hfix1

omit [Finite K] in
theorem pairHom_inl_eq {g : StatedSp 2 K} {v : StdMod (Fin 2 ⊕ Fin 2) K}
    (h : natAut (StatedSp 2 K) g v = v) :
    pairHom (StatedSp 2 K) tauSp g ((v, 1) : PairMod (Fin 2 ⊕ Fin 2) K) = (v, 1) :=
  Prod.ext h (map_one (natAut (StatedSp 2 K) (tauSp g)))

omit [Finite K] in
theorem pairHom_inr_eq {g : StatedSp 2 K} {v : StdMod (Fin 2 ⊕ Fin 2) K}
    (h : natAut (StatedSp 2 K) (tauSp g) v = v) :
    pairHom (StatedSp 2 K) tauSp g ((1, v) : PairMod (Fin 2 ⊕ Fin 2) K) = (1, v) :=
  Prod.ext (map_one (natAut (StatedSp 2 K) g)) h

theorem preserves_V₁ {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hpg : IsPGroup 2 A) (hsq : ∀ x ∈ A, x * x = 1)
    (hfixc : ∀ B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), B ≤ A →
      Nat.card A ≤ 2 * Nat.card B → fixV B = fixV A) :
    ∀ x ∈ A, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  have hfa : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hsA, hs⟩ := hcon
  have hs2 := (map_V₁_eq_or (hAN hsA)).resolve_left hs
  set A₀ := A ⊓ pairSub (Fin 2 ⊕ Fin 2) K with hA₀
  have hmem : ∀ x ∈ A, x ∈ pairSub (Fin 2 ⊕ Fin 2) K ↔
      (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
    intro x hx
    constructor
    · intro hxs
      obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hxs
      exact map_V₁_pairAut a b
    · intro h1
      obtain ⟨a, b, rfl⟩ := exists_pairAut (hAN hx) h1
      exact pairAut_mem_pairSub a b
  have hidx : Nat.card A ≤ 2 * Nat.card A₀ := by
    refine card_le_two_mul_of_mul_mem inf_le_left fun x hx y hy hx' hy' => ⟨A.mul_mem hx hy, ?_⟩
    have hx1 : x ∉ pairSub (Fin 2 ⊕ Fin 2) K := fun h => hx' ⟨hx, h⟩
    have hy1 : y ∉ pairSub (Fin 2 ⊕ Fin 2) K := fun h => hy' ⟨hy, h⟩
    have hxV := (map_V₁_eq_or (hAN hx)).resolve_left fun h => hx1 ((hmem x hx).mpr h)
    have hyV := (map_V₁_eq_or (hAN hy)).resolve_left fun h => hy1 ((hmem y hy).mpr h)
    have hxV2 : (V₂ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
      rw [← hxV, Subgroup.map_map]
      have : x.toMonoidHom.comp x.toMonoidHom = MonoidHom.id _ := by
        refine MonoidHom.ext fun v => ?_
        change (x * x) v = v
        rw [hsq x hx]
        rfl
      rw [this, Subgroup.map_id]
    refine (hmem _ (A.mul_mem hx hy)).mpr ?_
    have : (x * y).toMonoidHom = x.toMonoidHom.comp y.toMonoidHom := rfl
    rw [this, ← Subgroup.map_map, hyV, hxV2]
  have hfix0 : fixV A₀ = fixV A := hfixc A₀ inf_le_left hidx
  have hpg0 : IsPGroup 2 A₀ := hpg.to_le inf_le_left
  have hinv : ∀ g ∈ A₀, ∀ w ∈ V₁ (Fin 2 ⊕ Fin 2) K, g w ∈ V₁ (Fin 2 ⊕ Fin 2) K := by
    intro g hg w hw
    obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hg.2
    rw [mem_V₁] at hw ⊢
    rw [pairAut_apply, hw, map_one]
  have hmod := card_modEq_card_inf_fixV hpg0 hinv
  have hV₁ : Nat.card (V₁ (Fin 2 ⊕ Fin 2) K) = 2 ^ (4 * n) := by
    have e : Nat.card (V₁ (Fin 2 ⊕ Fin 2) K) = Nat.card (StdMod (Fin 2 ⊕ Fin 2) K) :=
      Nat.card_congr
        { toFun := fun v => v.1.1
          invFun := fun u => ⟨(u, 1), mem_V₁.mpr rfl⟩
          left_inv := fun v => Subtype.ext (Prod.ext rfl (mem_V₁.mp v.2).symm)
          right_inv := fun u => rfl }
    rw [e, card_stdMod, hK, Fintype.card_sum, Fintype.card_fin, ← pow_mul]
    congr 1
    ring
  have hne : ∃ v ∈ V₁ (Fin 2 ⊕ Fin 2) K ⊓ fixV A₀, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : V₁ (Fin 2 ⊕ Fin 2) K ⊓ fixV A₀ = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr hcon
    rw [hbot, Subgroup.card_bot, hV₁] at hmod
    have h2 : 2 ^ (4 * n) % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨v, ⟨hv1, hvf⟩, hv⟩ := hne
  rw [hfix0] at hvf
  exact hv (eq_one_of_fix_of_map_V₂ hs2 hv1 (hvf s hsA))

theorem exists_card_le {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hAN : A ≤ pairNormSp K)
    (hsq : ∀ x ∈ A, x * x = 1)
    (hAsub : ∀ x ∈ A, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K) :
    ∃ c : ℕ, Nat.card A ≤ c * Nat.card ↥(A ⊓ pairSp K) ∧
      c * Nat.card K ≤ 2 ^ (2 * n - 1) ∧ c * Nat.card K < 2 ^ (2 * n) := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  set H := A ⊓ pairSp K with hH
  have hdec : ∀ x ∈ A, ∃ a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), x = pairAut a b :=
    fun x hx => exists_pairAut (hAN hx) (hAsub x hx)
  let E₁ : Subgroup (MulAut (StdMod (Fin 2 ⊕ Fin 2) K)) :=
    { carrier := {a | ∃ b, pairAut a b ∈ A}
      one_mem' := ⟨1, A.one_mem⟩
      mul_mem' := fun {a a'} ⟨b, hb⟩ ⟨b', hb'⟩ => ⟨b * b', A.mul_mem hb hb'⟩
      inv_mem' := fun {a} ⟨b, hb⟩ => ⟨b⁻¹, by rw [← pairAut_inv]; exact A.inv_mem hb⟩ }
  have hE₁N : E₁ ≤ natNorm (StatedSp 2 K) := fun a ⟨b, hb⟩ => fst_mem_natNorm (hAN hb)
  have hE₁sq : ∀ a ∈ E₁, a ^ 2 = 1 := by
    rintro a ⟨b, hb⟩
    have := hsq _ hb
    rw [pairAut_mul] at this
    rw [sq]
    exact (pairAut_injective (this.trans pairAut_one.symm)).1
  have hlinH : ∀ a b, pairAut a b ∈ A → IsSemilinear a (RingEquiv.refl K) →
      pairAut a b ∈ H := by
    intro a b hab hlin
    obtain ⟨B, -, hB⟩ := eq_pairHom_of_linear (hAN hab) (hsq _ hab) hlin
    exact ⟨hab, hB ▸ pairHom_mem_pairImg _ _ B⟩
  have huniq : ∀ a b b', pairAut a b ∈ A → pairAut a b' ∈ A → b = b' := by
    intro a b b' hb hb'
    have hm : pairAut 1 (b⁻¹ * b') ∈ A := by
      have := A.mul_mem (A.inv_mem hb) hb'
      rwa [pairAut_inv, pairAut_mul, inv_mul_cancel] at this
    obtain ⟨B, -, hB⟩ := eq_pairHom_of_linear (hAN hm) (hsq _ hm) isSemilinear_one
    rw [pairHom_apply] at hB
    obtain ⟨h1, h2⟩ := pairAut_injective hB
    have hB1 : B = 1 := natAut_injective (StatedSp 2 K) (by rw [← h1, map_one])
    rw [hB1, map_one, map_one] at h2
    exact (inv_mul_eq_one.mp h2)
  have hE₁A : Nat.card A ≤ Nat.card E₁ := by
    choose fa fb hfab using hdec
    refine Nat.card_le_card_of_injective (fun x => ⟨fa x x.2, fb x x.2, (hfab x x.2) ▸ x.2⟩) ?_
    intro x y hxy
    have e : fa x x.2 = fa y y.2 := congrArg Subtype.val hxy
    apply Subtype.ext
    rw [hfab x x.2, hfab y y.2, e]
    have hx := hfab x x.2 ▸ x.2
    have hy := hfab y y.2 ▸ y.2
    rw [e] at hx
    rw [huniq _ _ _ hx hy]
  have hHE : Nat.card ↥(E₁ ⊓ linSub) ≤ Nat.card H := by
    refine Nat.card_le_card_of_injective (fun e => ⟨pairAut e.1 (Classical.choose e.2.1),
      hlinH _ _ (Classical.choose_spec e.2.1) e.2.2⟩) ?_
    intro e e' hee'
    have := congrArg Subtype.val hee'
    exact Subtype.ext (pairAut_injective this).1
  rcases Nat.lt_or_ge n 2 with h1 | h2
  ·
    have hn1 : n = 1 := by omega
    subst hn1
    have h01 : ∀ c : K, c = 0 ∨ c = 1 := by
      intro c
      by_contra hc
      push Not at hc
      have hinj : Function.Injective (![0, 1, c] : Fin 3 → K) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [eq_comm, zero_ne_one]
      have := Nat.card_le_card_of_injective _ hinj
      rw [hK, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      omega
    have hlinall : ∀ a : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), a ∈ linSub := by
      intro a c v
      rcases h01 c with rfl | rfl
      · rw [zero_smul, toAddMap_zero, RingEquiv.refl_apply, zero_smul]
      · rw [one_smul, RingEquiv.refl_apply, one_smul]
    have hEl : E₁ ⊓ linSub = E₁ := inf_eq_left.mpr fun a _ => hlinall a
    refine ⟨1, ?_, by rw [hK]; norm_num, by rw [hK]; norm_num⟩
    calc Nat.card A ≤ Nat.card E₁ := hE₁A
      _ = Nat.card ↥(E₁ ⊓ linSub) := by rw [hEl]
      _ ≤ 1 * Nat.card H := by rw [one_mul]; exact hHE
  · have hE₁2 := card_le_two_mul_card_inf_linSub hasScalarCommutant_statedSp (by omega) hK hE₁N
      hE₁sq
    refine ⟨2, by omega, ?_, ?_⟩
    · rw [hK, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · rw [hK, ← pow_succ']
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem false_of_card_le {n : ℕ}
    {A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hsq : ∀ x ∈ A, x * x = 1)
    (hcardA' : 2 ^ (2 * n) ≤ Nat.card A)
    (hfixc : ∀ B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), B ≤ A →
      Nat.card A ≤ 2 ^ (2 * n - 1) * Nat.card B → fixV B = fixV A)
    {c : ℕ} (hcA : Nat.card A ≤ c * Nat.card ↥(A ⊓ pairSp K))
    (hc1 : c * Nat.card K ≤ 2 ^ (2 * n - 1)) (hc2 : c * Nat.card K < 2 ^ (2 * n)) : False := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  set H := A ⊓ pairSp K with hH
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hcA
      have := Nat.card_pos (α := A)
      omega
    · exact h
  set Â := H.comap (pairHom (StatedSp 2 K) tauSp) with hÂ
  have hpairinj : Function.Injective (pairHom (StatedSp 2 K) tauSp) := by
    rw [injective_iff_map_eq_one]
    intro B hB
    rw [pairHom_apply] at hB
    have := (pairAut_injective (hB.trans pairAut_one.symm)).1
    exact natAut_injective (StatedSp 2 K) (by rw [this, map_one])
  have hHmap : Â.map (pairHom (StatedSp 2 K) tauSp) = H :=
    Subgroup.map_comap_eq_self (fun x hx => hx.2)
  have hcardÂ : Nat.card Â = Nat.card H := by
    rw [← hHmap]
    exact (Subgroup.card_map_of_injective hpairinj).symm
  have hfixH : fixV H = fixV A := hfixc H inf_le_left (by
    calc Nat.card A ≤ c * Nat.card H := hcA
      _ ≤ 2 ^ (2 * n - 1) * Nat.card H :=
        Nat.mul_le_mul_right _ ((Nat.le_mul_of_pos_right c hq1).trans hc1))
  have hDfix : ∀ D : Subgroup (StatedSp 2 K), D ≤ Â →
      Nat.card Â ≤ Nat.card K * Nat.card D →
      fixV (D.map (pairHom (StatedSp 2 K) tauSp)) = fixV H := by
    intro D hD hcD
    have hDA : D.map (pairHom (StatedSp 2 K) tauSp) ≤ A := by
      rintro _ ⟨g, hg, rfl⟩
      exact (hD hg).1
    rw [hfixH]
    refine hfixc _ hDA ?_
    rw [Subgroup.card_map_of_injective hpairinj]
    calc Nat.card A ≤ c * Nat.card Â := by rw [hcardÂ]; exact hcA
      _ ≤ c * (Nat.card K * Nat.card D) := Nat.mul_le_mul_left c hcD
      _ = (c * Nat.card K) * Nat.card D := by ring
      _ ≤ 2 ^ (2 * n - 1) * Nat.card D := Nat.mul_le_mul_right _ hc1
  have hfixÂ : ∀ D : Subgroup (StatedSp 2 K), D ≤ Â →
      Nat.card Â ≤ Nat.card K * Nat.card D →
      ∀ x : PairMod (Fin 2 ⊕ Fin 2) K, (∀ g ∈ D, pairHom (StatedSp 2 K) tauSp g x = x) →
        ∀ g ∈ Â, pairHom (StatedSp 2 K) tauSp g x = x := by
    intro D hD hcD x hx g hg
    have hxD : x ∈ fixV (D.map (pairHom (StatedSp 2 K) tauSp)) := by
      rintro _ ⟨g', hg', rfl⟩
      exact hx g' hg'
    rw [hDfix D hD hcD, ← hHmap] at hxD
    exact hxD _ ⟨g, hg, rfl⟩
  refine false_of_fix Â ?_ ?_ ?_ ?_
  · intro x hx
    apply hpairinj
    rw [map_mul, map_one]
    exact hsq _ hx.1
  · by_contra hcon
    push Not at hcon
    have : c * Nat.card Â ≤ c * Nat.card K := Nat.mul_le_mul_left c hcon
    rw [hcardÂ] at this
    omega
  · intro D hD hcD v hv g hg
    exact congrArg Prod.fst (hfixÂ D hD hcD (v, 1) (fun g' hg' => pairHom_inl_eq (hv g' hg')) g hg)
  · intro D hD hcD v hv g hg
    exact congrArg Prod.snd (hfixÂ D hD hcD (1, v) (fun g' hg' => pairHom_inr_eq (hv g' hg')) g hg)

theorem not_mem_aSet {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K)
    (A : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) : A ∉ E3.aSet (2 * n) X := by
  intro hA
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  obtain ⟨hAX, -, hAel, hAc⟩ := id hA
  have hAN : A ≤ pairNormSp K := hAX.trans hXN
  have hpg := E3.isPGroup_of_isElemAbelian2 hAel
  have hrk : 2 * n ≤ rk ↥A := by
    have := E3.le_mQuot_bot_of_mem_aSet hA
    rwa [mQuot_bot_eq_rk] at this
  have hcardA : Nat.card A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hpg
  have hcardA' : 2 ^ (2 * n) ≤ Nat.card A := by
    rw [hcardA]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  have hfixc : ∀ B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), B ≤ A →
      Nat.card A ≤ 2 ^ (2 * n - 1) * Nat.card B → fixV B = fixV A := by
    intro B hBA hB
    refine hAc B hBA ?_
    have := mQuot_le_of_card_le hpg hBA hB
    omega
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hAel.2 x hx
  have hAsub := preserves_V₁ hn hK hAN hpg hsq fun B hBA hB => hfixc B hBA (hB.trans
    (Nat.mul_le_mul_right _ (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega))))
  obtain ⟨c, hcA, hc1, hc2⟩ := exists_card_le hn hK hAN hsq hAsub
  exact false_of_card_le hsq hcardA' hfixc hcA hc1 hc2

theorem aParam_lt {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hXN : X ≤ pairNormSp K) :
    E3.aParam X < 2 * n := by
  unfold E3.aParam
  split_ifs
  · by_cases hne : {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty}.Nonempty
    · have hle : sSup {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty} ≤ 2 * n - 1 := by
        refine csSup_le hne ?_
        rintro k ⟨-, A, hA⟩
        by_contra hk
        push Not at hk
        exact not_mem_aSet hn hK hXN A (E3.aSet_anti (by omega) X hA)
      omega
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
      exact Nat.mul_pos (by norm_num) hn
  · omega

end Sp4

end H

end CFSG.Quasithin
