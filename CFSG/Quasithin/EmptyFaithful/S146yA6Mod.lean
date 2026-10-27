module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.A6Mod

open Equiv

abbrev A6 := alternatingGroup (Fin 6)

@[expose] def aP : Perm (Fin 6) := c[0, 1, 2]
@[expose] def a'P : Perm (Fin 6) := c[3, 4, 5]
@[expose] def hP : Perm (Fin 6) := c[0, 3, 1, 4] * c[2, 5]

theorem sign_aP : Perm.sign aP = 1 := by decide
theorem sign_a'P : Perm.sign a'P = 1 := by decide
theorem sign_hP : Perm.sign hP = 1 := by decide

@[expose] def a : A6 := ⟨aP, Perm.mem_alternatingGroup.mpr sign_aP⟩
@[expose] def a' : A6 := ⟨a'P, Perm.mem_alternatingGroup.mpr sign_a'P⟩
@[expose] def h : A6 := ⟨hP, Perm.mem_alternatingGroup.mpr sign_hP⟩

theorem a_cube : a ^ 3 = 1 := by
  apply Subtype.ext; show aP ^ 3 = 1; decide
theorem a'_cube : a' ^ 3 = 1 := by
  apply Subtype.ext; show a'P ^ 3 = 1; decide
theorem a_comm : a * a' = a' * a := by
  apply Subtype.ext; show aP * a'P = a'P * aP; decide
theorem h_a : h * a * h⁻¹ = a' := by
  apply Subtype.ext; show hP * aP * hP⁻¹ = a'P; decide
theorem h_a' : h * a' * h⁻¹ = a⁻¹ := by
  apply Subtype.ext; show hP * a'P * hP⁻¹ = aP⁻¹; decide

theorem a_sq : a ^ 2 = a⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, a_cube]
theorem a'_sq : a' ^ 2 = a'⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, a'_cube]

theorem pow_mod_three_a (n : ℕ) : a ^ (n % 3) = a ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, a_cube, one_pow, mul_one]
theorem pow_mod_three_a' (n : ℕ) : a' ^ (n % 3) = a' ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, a'_cube, one_pow, mul_one]

@[expose] def thetaE : Multiplicative (Fin 3) × Multiplicative (Fin 3) →* A6 where
  toFun p := a ^ ((Multiplicative.toAdd p.1 : Fin 3) : ℕ) * a' ^ ((Multiplicative.toAdd p.2 : Fin 3) : ℕ)
  map_one' := by simp
  map_mul' p q := by
    have hc : Commute a a' := a_comm
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Fin.val_add]
    rw [pow_mod_three_a, pow_mod_three_a', pow_add, pow_add]
    have h1 : a' ^ ((Multiplicative.toAdd p.2 : Fin 3) : ℕ) * a ^ ((Multiplicative.toAdd q.1 : Fin 3) : ℕ) =
        a ^ ((Multiplicative.toAdd q.1 : Fin 3) : ℕ) * a' ^ ((Multiplicative.toAdd p.2 : Fin 3) : ℕ) :=
      (hc.pow_pow ((Multiplicative.toAdd q.1 : Fin 3) : ℕ) ((Multiplicative.toAdd p.2 : Fin 3) : ℕ)).eq.symm
    simp only [mul_assoc]
    rw [← mul_assoc (a' ^ ((Multiplicative.toAdd p.2 : Fin 3) : ℕ)), h1]
    simp only [mul_assoc]

section Mod

variable {M : Type} [Group M] [Finite M]

@[expose] def fixSub (φ : MulAut M) : Subgroup M where
  carrier := {m | φ m = m}
  one_mem' := map_one φ
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv, hx]

omit [Finite M] in
theorem mem_fixSub {φ : MulAut M} {m : M} : m ∈ fixSub φ ↔ φ m = m := Iff.rfl

omit [Finite M] in
theorem fixSub_inv (φ : MulAut M) : fixSub φ⁻¹ = fixSub φ := by
  ext m
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro h
    have := congrArg φ h
    rw [MulAut.apply_inv_self] at this
    exact this.symm
  · intro h
    have := congrArg (fun x => φ⁻¹ x) h
    simp only [MulAut.inv_apply_self] at this
    exact this.symm

omit [Finite M] in
theorem card_fixSub_conj (ψ φ : MulAut M) : Nat.card (fixSub (ψ * φ * ψ⁻¹)) = Nat.card (fixSub φ) := by
  refine Nat.card_congr ⟨fun m => ⟨ψ⁻¹ m.1, ?_⟩, fun m => ⟨ψ m.1, ?_⟩, ?_, ?_⟩
  · have h := m.2
    rw [mem_fixSub, MulAut.mul_apply, MulAut.mul_apply] at h
    rw [mem_fixSub]
    have := congrArg (fun x => ψ⁻¹ x) h
    simp only [MulAut.inv_apply_self] at this
    exact this
  · have h := m.2
    rw [mem_fixSub] at h
    rw [mem_fixSub, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h]
  · intro m; apply Subtype.ext; simp
  · intro m; apply Subtype.ext; simp

end Mod

section Burn

variable {M : Type} [Group M] [Finite M]

abbrev Θ := Multiplicative (Fin 3) × Multiplicative (Fin 3)

theorem nine_dvd_sum_fixSub (ρ : A6 →* MulAut M) :
    9 ∣ ∑ p : Θ, Nat.card (fixSub (ρ (thetaE p))) := by
  classical
  let ρ' : Θ →* MulAut M := ρ.comp thetaE
  let : MulAction Θ M := MulAction.compHom M ρ'
  have : Fintype M := Fintype.ofFinite M
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Θ M
  have hcard : Fintype.card Θ = 9 := by simp [Θ]
  have hterm : ∀ p : Θ, Nat.card (fixSub (ρ (thetaE p))) = Fintype.card (MulAction.fixedBy M p) := by
    intro p
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun m => Iff.rfl))
  simp only [hterm]
  rw [hb, hcard]
  exact Dvd.intro_left _ rfl

end Burn

section Sum

variable {M : Type} [Group M] [Finite M]

@[expose] noncomputable def fc (ρ : A6 →* MulAut M) (g : A6) : ℕ := Nat.card (fixSub (ρ g))

omit [Finite M] in
theorem fc_inv (ρ : A6 →* MulAut M) (g : A6) : fc ρ g⁻¹ = fc ρ g := by
  unfold fc
  rw [map_inv, fixSub_inv]

omit [Finite M] in
theorem fc_one (ρ : A6 →* MulAut M) : fc ρ 1 = Nat.card M := by
  unfold fc
  have : fixSub (ρ 1) = ⊤ := by
    ext m
    simp [mem_fixSub]
  rw [this, Subgroup.card_top]

theorem thetaE_apply (i j : Fin 3) :
    thetaE (Multiplicative.ofAdd i, Multiplicative.ofAdd j) = a ^ (i : ℕ) * a' ^ (j : ℕ) := rfl

omit [Finite M] in
theorem sum_fc_eq (ρ : A6 →* MulAut M) :
    ∑ p : Θ, Nat.card (fixSub (ρ (thetaE p))) =
      Nat.card M + 2 * (fc ρ a + fc ρ a' + fc ρ (a * a') + fc ρ (a * a'⁻¹)) := by
  have hc : Commute a a' := a_comm
  rw [Fintype.sum_prod_type]
  have h3 : ∀ f : Multiplicative (Fin 3) → ℕ, ∑ i : Multiplicative (Fin 3), f i =
      f (Multiplicative.ofAdd 0) + f (Multiplicative.ofAdd 1) + f (Multiplicative.ofAdd 2) := by
    intro f
    exact Fin.sum_univ_three (fun i : Fin 3 => f (Multiplicative.ofAdd i))
  simp only [h3]
  have e22 : a ^ 2 * a' ^ 2 = (a * a')⁻¹ := by
    rw [a_sq, a'_sq, mul_inv_rev, hc.inv_inv.eq]
  have e21 : a ^ 2 * a' = (a * a'⁻¹)⁻¹ := by
    rw [a_sq, mul_inv_rev, inv_inv]
    exact hc.inv_left.eq
  have e12 : a * a' ^ 2 = a * a'⁻¹ := by rw [a'_sq]
  have t00 : thetaE (Multiplicative.ofAdd 0, Multiplicative.ofAdd 0) = 1 := by
    have : (Multiplicative.ofAdd (0 : Fin 3), Multiplicative.ofAdd (0 : Fin 3)) = (1 : Θ) := rfl
    rw [this, map_one]
  have t01 : thetaE (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1) = a' := by
    rw [thetaE_apply]; simp
  have t02 : thetaE (Multiplicative.ofAdd 0, Multiplicative.ofAdd 2) = a'⁻¹ := by
    rw [thetaE_apply, ← a'_sq]; simp
  have t10 : thetaE (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0) = a := by
    rw [thetaE_apply]; simp
  have t11 : thetaE (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1) = a * a' := by
    rw [thetaE_apply]; simp
  have t12 : thetaE (Multiplicative.ofAdd 1, Multiplicative.ofAdd 2) = a * a'⁻¹ := by
    rw [thetaE_apply, ← e12]; simp
  have t20 : thetaE (Multiplicative.ofAdd 2, Multiplicative.ofAdd 0) = a⁻¹ := by
    rw [thetaE_apply, ← a_sq]; simp
  have t21 : thetaE (Multiplicative.ofAdd 2, Multiplicative.ofAdd 1) = (a * a'⁻¹)⁻¹ := by
    rw [thetaE_apply, ← e21]; simp
  have t22 : thetaE (Multiplicative.ofAdd 2, Multiplicative.ofAdd 2) = (a * a')⁻¹ := by
    rw [thetaE_apply, ← e22]; simp
  rw [t00, t01, t02, t10, t11, t12, t20, t21, t22]
  change fc ρ 1 + fc ρ a' + fc ρ a'⁻¹ + (fc ρ a + fc ρ (a * a') + fc ρ (a * a'⁻¹)) +
    (fc ρ a⁻¹ + fc ρ (a * a'⁻¹)⁻¹ + fc ρ (a * a')⁻¹) = _
  rw [fc_one, fc_inv, fc_inv, fc_inv, fc_inv]
  ring

end Sum

section F2

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem fc_dvd (ρ : A6 →* MulAut M) (g : A6) : fc ρ g ∣ Nat.card M :=
  Subgroup.card_subgroup_dvd_card _

theorem fc_modEq_three (ρ : A6 →* MulAut M) {g : A6} (hg : g ^ 3 = 1) :
    Nat.card M ≡ fc ρ g [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H : Subgroup (MulAut M) := Subgroup.zpowers (ρ g)
  have hpow : ρ g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hH : IsPGroup 3 H := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have h1 := hH.card_modEq_card_fixedPoints M
  have h2 : Nat.card (MulAction.fixedPoints H M) = fc ρ g := by
    unfold fc
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [mem_fixSub, MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨ρ g, Subgroup.mem_zpowers _⟩
    · intro h x
      have hst : ρ g ∈ MulAction.stabilizer (MulAut M) m := by
        rw [MulAction.mem_stabilizer_iff]
        exact h
      have := Subgroup.zpowers_le.mpr hst x.2
      exact (MulAction.mem_stabilizer_iff.mp this)
  rw [h2] at h1
  exact h1

theorem ne_one_a : a ≠ 1 := by
  intro h
  have : aP = 1 := congrArg Subtype.val h
  revert this; decide
theorem ne_one_aa' : a * a' ≠ 1 := by
  intro h
  have : aP * a'P = 1 := congrArg Subtype.val h
  revert this; decide
theorem a_commute : Commute a a' := a_comm

theorem cube_aa' : (a * a') ^ 3 = 1 := by
  rw [a_commute.mul_pow, a_cube, a'_cube, one_mul]
omit [Finite M] in
theorem fc_conj (ρ : A6 →* MulAut M) (k g : A6) : fc ρ (k * g * k⁻¹) = fc ρ g := by
  unfold fc
  rw [map_mul, map_mul, map_inv]
  exact card_fixSub_conj _ _

omit [Finite M] in
theorem fc_a' (ρ : A6 →* MulAut M) : fc ρ a' = fc ρ a := by
  have := fc_conj ρ h a
  rwa [h_a] at this

omit [Finite M] in
theorem fc_aa'inv (ρ : A6 →* MulAut M) : fc ρ (a * a'⁻¹) = fc ρ (a * a') := by
  have h1 := fc_conj ρ h (a * a')
  have h2 : h * (a * a') * h⁻¹ = (a * a'⁻¹)⁻¹ := by
    calc h * (a * a') * h⁻¹ = (h * a * h⁻¹) * (h * a' * h⁻¹) := by group
      _ = a' * a⁻¹ := by rw [h_a, h_a']
      _ = (a * a'⁻¹)⁻¹ := by simp [mul_inv_rev]
  rw [h2, fc_inv] at h1
  exact h1

omit [Finite M] in
theorem injective_of_nontrivial {ρ : A6 →* MulAut M} (hρ : ∃ g, ρ g ≠ 1) : Function.Injective ρ := by
  have : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with hk | hk
  · exact (MonoidHom.ker_eq_bot_iff ρ).mp hk
  · exfalso
    obtain ⟨g, hg⟩ := hρ
    apply hg
    have : g ∈ ρ.ker := by rw [hk]; trivial
    exact this

theorem fc_lt {ρ : A6 →* MulAut M} (hρ : ∃ g, ρ g ≠ 1) {g : A6} (hg : g ≠ 1) :
    fc ρ g < Nat.card M := by
  have hinj := injective_of_nontrivial hρ
  by_contra hcon
  push Not at hcon
  have hle : fc ρ g ≤ Nat.card M := Nat.card_le_card_of_injective (Subgroup.subtype (fixSub (ρ g)))
    Subtype.val_injective
  have heq : Nat.card (fixSub (ρ g)) = Nat.card M := le_antisymm hle hcon
  have htop : fixSub (ρ g) = ⊤ := Subgroup.eq_top_of_card_eq _ heq
  apply hg
  apply hinj
  rw [map_one]
  refine MulEquiv.ext fun m => ?_
  have : m ∈ fixSub (ρ g) := by rw [htop]; trivial
  exact this

theorem fc_val16 {ρ : A6 →* MulAut M} (hρ : ∃ g, ρ g ≠ 1) (hM : Nat.card M = 16) {g : A6}
    (hg1 : g ≠ 1) (hg3 : g ^ 3 = 1) : fc ρ g = 1 ∨ fc ρ g = 4 := by
  have hd := fc_dvd ρ g
  have hm := fc_modEq_three ρ hg3
  have hlt := fc_lt hρ hg1
  rw [hM] at hd hm hlt
  have hle : fc ρ g ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  generalize fc ρ g = f at *
  unfold Nat.ModEq at hm
  interval_cases f <;> simp_all

theorem fc_val32 {ρ : A6 →* MulAut M} (hρ : ∃ g, ρ g ≠ 1) (hM : Nat.card M = 32) {g : A6}
    (hg1 : g ≠ 1) (hg3 : g ^ 3 = 1) : fc ρ g = 2 ∨ fc ρ g = 8 := by
  have hd := fc_dvd ρ g
  have hm := fc_modEq_three ρ hg3
  have hlt := fc_lt hρ hg1
  rw [hM] at hd hm hlt
  have hle : fc ρ g ≤ 32 := Nat.le_of_dvd (by norm_num) hd
  generalize fc ρ g = f at *
  unfold Nat.ModEq at hm
  interval_cases f <;> simp_all

theorem F2_16 (ρ : A6 →* MulAut M) (hρ : ∃ g, ρ g ≠ 1) (hM : Nat.card M = 16) :
    (fc ρ a = 4 ∧ fc ρ (a * a') = 1) ∨ (fc ρ a = 1 ∧ fc ρ (a * a') = 4) := by
  have h9 := nine_dvd_sum_fixSub ρ
  rw [sum_fc_eq, fc_a', fc_aa'inv, hM] at h9
  have v1 := fc_val16 hρ hM ne_one_a a_cube.symm.symm
  have v2 := fc_val16 hρ hM ne_one_aa' cube_aa'
  omega

theorem F2_32 (ρ : A6 →* MulAut M) (hρ : ∃ g, ρ g ≠ 1) (hM : Nat.card M = 32) :
    (fc ρ a = 8 ∧ fc ρ (a * a') = 2) ∨ (fc ρ a = 2 ∧ fc ρ (a * a') = 8) := by
  have h9 := nine_dvd_sum_fixSub ρ
  rw [sum_fc_eq, fc_a', fc_aa'inv, hM] at h9
  have v1 := fc_val32 hρ hM ne_one_a a_cube
  have v2 := fc_val32 hρ hM ne_one_aa' cube_aa'
  omega

end F2

section Sub

variable {P : Type} [Group P] [Finite P]

@[expose] def Inv (ρ : A6 →* MulAut P) (V : Subgroup P) : Prop := ∀ g, ∀ v ∈ V, ρ g v ∈ V

omit [Finite P] in
theorem Inv.inv_mem {ρ : A6 →* MulAut P} {V : Subgroup P} (hV : Inv ρ V) (g : A6) {v : P}
    (hv : v ∈ V) : (ρ g)⁻¹ v ∈ V := by
  have := hV g⁻¹ v hv
  rwa [map_inv] at this

@[expose] noncomputable def restrictRep (ρ : A6 →* MulAut P) (V : Subgroup P) (hV : Inv ρ V) :
    A6 →* MulAut ↥V where
  toFun g :=
    { toFun := fun v => ⟨ρ g v, hV g v v.2⟩
      invFun := fun v => ⟨(ρ g)⁻¹ v, hV.inv_mem g v.2⟩
      left_inv := fun v => Subtype.ext (MulAut.inv_apply_self P (ρ g) v.1)
      right_inv := fun v => Subtype.ext (MulAut.apply_inv_self P (ρ g) v.1)
      map_mul' := fun x y => Subtype.ext (map_mul (ρ g) x.1 y.1) }
  map_one' := by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    simp
  map_mul' := fun g₁ g₂ => by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    simp

omit [Finite P] in
theorem restrictRep_apply (ρ : A6 →* MulAut P) (V : Subgroup P) (hV : Inv ρ V) (g : A6) (v : V) :
    ((restrictRep ρ V hV g v : V) : P) = ρ g v := rfl

@[expose] noncomputable def fcs (ρ : A6 →* MulAut P) (g : A6) (V : Subgroup P) : ℕ :=
  Nat.card ↥(V ⊓ fixSub (ρ g))

omit [Finite P] in
theorem fc_restrict (ρ : A6 →* MulAut P) (V : Subgroup P) (hV : Inv ρ V) (g : A6) :
    fc (restrictRep ρ V hV) g = fcs ρ g V := by
  unfold fc fcs
  refine Nat.card_congr ⟨fun m => ⟨m.1.1, m.1.2, ?_⟩, fun m => ⟨⟨m.1, m.2.1⟩, ?_⟩, ?_, ?_⟩
  · have h := m.2
    rw [mem_fixSub] at h
    show ρ g m.1.1 = m.1.1
    exact congrArg Subtype.val h
  · rw [mem_fixSub]
    exact Subtype.ext (m.2.2)
  · intro m; rfl
  · intro m; rfl

end Sub

section CP

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem normal_of_comm' (hcomm : ∀ x y : P, x * y = y * x) (H : Subgroup P) : H.Normal where
  conj_mem n hn g := by
    have : g * n * g⁻¹ = n := by rw [hcomm g n]; group
    rwa [this]

omit [Finite P] in
theorem card_sup_mul_card_inf (hcomm : ∀ x y : P, x * y = y * x) (C₁ C₂ : Subgroup P) :
    Nat.card ↥(C₁ ⊔ C₂) * Nat.card ↥(C₁ ⊓ C₂) = Nat.card C₁ * Nat.card C₂ := by
  have : C₂.Normal := normal_of_comm' hcomm C₂
  have h1 := Subgroup.relIndex_mul_card (H := C₂) (K := C₁ ⊔ C₂)
  rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := C₂) (K := C₁)
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite P] in
theorem fcs_mono (ρ : A6 →* MulAut P) (g : A6) {X Y : Subgroup P} (h : X ≤ Y) [Finite P] :
    fcs ρ g X ≤ fcs ρ g Y :=
  Nat.card_le_card_of_injective (Subgroup.inclusion (inf_le_inf_right _ h)) (Subgroup.inclusion_injective _)

omit [Finite P] in
theorem fcs_sup_mul (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x ^ 2 = 1)
    (ρ : A6 →* MulAut P) {g : A6} (hg : g ^ 3 = 1) {X₁ X₂ : Subgroup P} (h₁ : Inv ρ X₁)
    (h₂ : Inv ρ X₂) :
    fcs ρ g (X₁ ⊔ X₂) * fcs ρ g (X₁ ⊓ X₂) = fcs ρ g X₁ * fcs ρ g X₂ := by
  let : CommGroup P := { ‹Group P› with mul_comm := hcomm }
  have hφ3 : ρ g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  have hφ3' : ∀ y : P, ρ g (ρ g (ρ g y)) = y := fun y => by
    have := congrArg (fun ψ : MulAut P => ψ y) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have : X₂.Normal := normal_of_comm' hcomm X₂
  let π : P → P := fun w => w * ρ g w * ρ g (ρ g w)
  have hπmul : ∀ y z : P, π (y * z) = π y * π z := by
    intro y z
    simp only [π, map_mul]
    ac_rfl
  have hπfix : ∀ y : P, ρ g (π y) = π y := by
    intro y
    simp only [π, map_mul, hφ3']
    ac_rfl
  have hπmem : ∀ {X : Subgroup P}, Inv ρ X → ∀ {y : P}, y ∈ X → π y ∈ X ⊓ fixSub (ρ g) := by
    intro X hX y hy
    exact ⟨X.mul_mem (X.mul_mem hy (hX g y hy)) (hX g _ (hX g y hy)), hπfix y⟩
  have key1 : (X₁ ⊔ X₂) ⊓ fixSub (ρ g) = (X₁ ⊓ fixSub (ρ g)) ⊔ (X₂ ⊓ fixSub (ρ g)) := by
    refine le_antisymm ?_ (le_inf (sup_le_sup inf_le_left inf_le_left) (sup_le inf_le_right inf_le_right))
    intro v hv
    obtain ⟨hvs, hvf⟩ := Subgroup.mem_inf.mp hv
    have hvf' : ρ g v = v := hvf
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hvs
    have hπv : π v = v := by
      have h2 := hsq v
      simp only [π, hvf']
      calc v * v * v = v ^ 2 * v := by rw [pow_two]
        _ = v := by rw [h2, one_mul]
    rw [← hπv, ← hyz, hπmul]
    exact Subgroup.mul_mem_sup (hπmem h₁ hy) (hπmem h₂ hz)
  have key2 : (X₁ ⊓ X₂) ⊓ fixSub (ρ g) = (X₁ ⊓ fixSub (ρ g)) ⊓ (X₂ ⊓ fixSub (ρ g)) := by
    ext v
    simp only [Subgroup.mem_inf]
    tauto
  unfold fcs
  rw [key1, key2]
  exact card_sup_mul_card_inf hcomm _ _

end CP

section Classes

@[expose] def cP : Perm (Fin 6) := swap 3 4
@[expose] def dP : Perm (Fin 6) := swap 0 3 * swap 1 4 * swap 2 5

theorem sign_cP : Perm.sign cP = -1 := by decide
theorem sign_dP : Perm.sign dP = -1 := by decide
theorem cP_comm : cP * aP = aP * cP := by decide
theorem dP_comm : dP * (aP * a'P) = (aP * a'P) * dP := by decide
theorem cycleType_aP : aP.cycleType = {3} := by
  have h : aP.support.card = 3 := by decide
  exact card_support_eq_three_iff.mp h
theorem cycleType_a'P : a'P.cycleType = {3} := by
  have h : a'P.support.card = 3 := by decide
  exact card_support_eq_three_iff.mp h
theorem cycleType_bP : (aP * a'P).cycleType = {3, 3} := by
  have hd : Perm.Disjoint aP a'P := show ∀ x : Fin 6, aP x = x ∨ a'P x = x by decide
  rw [hd.cycleType_mul, cycleType_aP, cycleType_a'P]
  rfl

theorem cycleType_of_order_three {y : Perm (Fin 6)} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y.cycleType = {3} ∨ y.cycleType = {3, 3} := by
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hall : ∀ n ∈ y.cycleType, n = 3 := by
    intro n hn
    have h1 := Perm.dvd_of_mem_cycleType hn
    rw [hord] at h1
    have h2 := Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · omega
    · exact h
  have hsum := Perm.sum_cycleType_le y
  have hne : y.cycleType ≠ 0 := fun h => hy1 (Perm.cycleType_eq_zero.mp h)
  have hrep : y.cycleType = Multiset.replicate (Multiset.card y.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr hall
  have hcard : Multiset.card y.cycleType = 1 ∨ Multiset.card y.cycleType = 2 := by
    have hpos : 0 < Multiset.card y.cycleType :=
      Multiset.card_pos.mpr hne
    have hs : y.cycleType.sum = 3 * Multiset.card y.cycleType := by
      conv_lhs => rw [hrep]
      simp [Multiset.sum_replicate]
      ring
    simp only [Fintype.card_fin] at hsum
    omega
  rcases hcard with h | h
  · left; rw [hrep, h]; rfl
  · right; rw [hrep, h]; rfl

theorem sign_mul_eq_one {k c : Perm (Fin 6)} (hc : Perm.sign c = -1) (hk : ¬ Perm.sign k = 1) :
    Perm.sign (k * c) = 1 := by
  rcases Int.units_eq_one_or (Perm.sign k) with h | h
  · exact absurd h hk
  · rw [map_mul, h, hc]; decide

theorem exists_conj_a_or_b (y : A6) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    (∃ k : A6, k * a * k⁻¹ = y) ∨ (∃ k : A6, k * (a * a') * k⁻¹ = y) := by
  have hy3' : (y : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3
    simpa using this
  have hy1' : (y : Perm (Fin 6)) ≠ 1 := fun h => hy1 (Subtype.ext h)
  rcases cycleType_of_order_three hy3' hy1' with h | h
  · left
    have hc : IsConj aP (y : Perm (Fin 6)) :=
      Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_aP, h])
    obtain ⟨k, hk⟩ := isConj_iff.mp hc
    by_cases hs : Perm.sign k = 1
    · exact ⟨⟨k, Perm.mem_alternatingGroup.mpr hs⟩, Subtype.ext hk⟩
    · refine ⟨⟨k * cP, Perm.mem_alternatingGroup.mpr (sign_mul_eq_one sign_cP hs)⟩, Subtype.ext ?_⟩
      show k * cP * aP * (k * cP)⁻¹ = y
      have : cP * aP * cP⁻¹ = aP := by rw [cP_comm]; group
      calc k * cP * aP * (k * cP)⁻¹ = k * (cP * aP * cP⁻¹) * k⁻¹ := by group
        _ = y := by rw [this]; exact hk
  · right
    have hc : IsConj (aP * a'P) (y : Perm (Fin 6)) :=
      Perm.isConj_iff_cycleType_eq.mpr (by rw [cycleType_bP, h])
    obtain ⟨k, hk⟩ := isConj_iff.mp hc
    by_cases hs : Perm.sign k = 1
    · exact ⟨⟨k, Perm.mem_alternatingGroup.mpr hs⟩, Subtype.ext hk⟩
    · refine ⟨⟨k * dP, Perm.mem_alternatingGroup.mpr (sign_mul_eq_one sign_dP hs)⟩, Subtype.ext ?_⟩
      show k * dP * (aP * a'P) * (k * dP)⁻¹ = y
      have : dP * (aP * a'P) * dP⁻¹ = aP * a'P := by rw [dP_comm]; group
      calc k * dP * (aP * a'P) * (k * dP)⁻¹ = k * (dP * (aP * a'P) * dP⁻¹) * k⁻¹ := by group
        _ = y := by rw [this]; exact hk

end Classes

section Lattice

variable {P : Type} [Group P] [Finite P]

omit [Finite P] in
theorem fcs_conj (ρ : A6 →* MulAut P) {V : Subgroup P} (hV : Inv ρ V) (k g : A6) :
    fcs ρ (k * g * k⁻¹) V = fcs ρ g V := by
  rw [← fc_restrict ρ V hV, ← fc_restrict ρ V hV]
  exact fc_conj _ _ _

omit [Finite P] in
theorem ρ_apply_twist {ρ : A6 →* MulAut P} {τ : MulAut P} {σ : MulAut A6}
    (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g)) (g : A6) (x : P) : ρ (σ g) (τ x) = τ (ρ g x) := by
  have := congrArg (fun ψ : MulAut P => ψ (τ x)) (hτ g)
  simp only [MulAut.mul_apply, MulAut.inv_apply_self] at this
  exact this.symm

omit [Finite P] in
theorem fcs_twist {ρ : A6 →* MulAut P} {τ : MulAut P} {σ : MulAut A6}
    (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g)) (V₁ : Subgroup P) (g : A6) :
    fcs ρ (σ g) (V₁.map τ.toMonoidHom) = fcs ρ g V₁ := by
  unfold fcs
  refine Nat.card_congr ⟨fun m => ⟨τ⁻¹ m.1, ?_⟩, fun m => ⟨τ m.1, ?_⟩, ?_, ?_⟩
  · obtain ⟨hm1, hm2⟩ := Subgroup.mem_inf.mp m.2
    obtain ⟨w, hw, hwm⟩ := Subgroup.mem_map.mp hm1
    have hwm' : τ w = m.1 := hwm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hwm']
      simpa using hw
    · rw [mem_fixSub]
      have h1 : ρ (σ g) m.1 = m.1 := hm2
      rw [← hwm'] at h1 ⊢
      rw [MulAut.inv_apply_self]
      rw [ρ_apply_twist hτ] at h1
      exact τ.injective h1
  · obtain ⟨hm1, hm2⟩ := Subgroup.mem_inf.mp m.2
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨m.1, hm1, rfl⟩, ?_⟩
    rw [mem_fixSub, ρ_apply_twist hτ]
    have h2 : ρ g m.1 = m.1 := hm2
    rw [h2]
  · intro m; apply Subtype.ext; simp
  · intro m; apply Subtype.ext; simp

theorem F2_sub (ρ : A6 →* MulAut P) {V : Subgroup P} (hV : Inv ρ V)
    (hnt : ∃ g, ∃ v ∈ V, ρ g v ≠ v) :
    (Nat.card V = 16 → (fcs ρ a V = 4 ∧ fcs ρ (a * a') V = 1) ∨
        (fcs ρ a V = 1 ∧ fcs ρ (a * a') V = 4)) ∧
      (Nat.card V = 32 → (fcs ρ a V = 8 ∧ fcs ρ (a * a') V = 2) ∨
        (fcs ρ a V = 2 ∧ fcs ρ (a * a') V = 8)) := by
  obtain ⟨g, v, hv, hne⟩ := hnt
  have hρ : ∃ g, restrictRep ρ V hV g ≠ 1 := by
    refine ⟨g, fun h => hne ?_⟩
    have := congrArg (fun ψ : MulAut ↥V => (ψ ⟨v, hv⟩ : P)) h
    simpa [restrictRep_apply] using this
  have e1 := fc_restrict ρ V hV a
  have e2 := fc_restrict ρ V hV (a * a')
  constructor
  · intro h
    have := F2_16 (restrictRep ρ V hV) hρ h
    rwa [e1, e2] at this
  · intro h
    have := F2_32 (restrictRep ρ V hV) hρ h
    rwa [e1, e2] at this

omit [Finite P] in
theorem swap_rel (ρ : A6 →* MulAut P) {τ : MulAut P} {σ : MulAut A6}
    (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g)) {V₁ : Subgroup P} (hV₁ : Inv ρ V₁)
    (hV₂ : Inv ρ (V₁.map τ.toMonoidHom)) {x₀ : A6} (hx3 : x₀ ^ 3 = 1) (hx1 : x₀ ≠ 1)
    (hnc : ∀ k : A6, k * x₀ * k⁻¹ ≠ σ x₀) :
    fcs ρ (a * a') (V₁.map τ.toMonoidHom) = fcs ρ a V₁ ∨
      fcs ρ a (V₁.map τ.toMonoidHom) = fcs ρ (a * a') V₁ := by
  have hσ3 : (σ x₀) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hσ1 : σ x₀ ≠ 1 := fun h => hx1 (σ.injective (by rw [h, map_one]))
  have key := fcs_twist hτ V₁ x₀
  rcases exists_conj_a_or_b x₀ hx3 hx1 with ⟨k₁, hk₁⟩ | ⟨k₁, hk₁⟩ <;>
    rcases exists_conj_a_or_b (σ x₀) hσ3 hσ1 with ⟨k₂, hk₂⟩ | ⟨k₂, hk₂⟩
  · exfalso
    apply hnc (k₂ * k₁⁻¹)
    calc (k₂ * k₁⁻¹) * x₀ * (k₂ * k₁⁻¹)⁻¹ = (k₂ * k₁⁻¹) * (k₁ * a * k₁⁻¹) * (k₂ * k₁⁻¹)⁻¹ := by
          rw [hk₁]
      _ = k₂ * a * k₂⁻¹ := by group
      _ = σ x₀ := hk₂
  · left
    rw [← hk₂, fcs_conj ρ hV₂, ← hk₁, fcs_conj ρ hV₁] at key
    exact key
  · right
    rw [← hk₂, fcs_conj ρ hV₂, ← hk₁, fcs_conj ρ hV₁] at key
    exact key
  · exfalso
    apply hnc (k₂ * k₁⁻¹)
    calc (k₂ * k₁⁻¹) * x₀ * (k₂ * k₁⁻¹)⁻¹ = (k₂ * k₁⁻¹) * (k₁ * (a * a') * k₁⁻¹) * (k₂ * k₁⁻¹)⁻¹ := by
          rw [hk₁]
      _ = k₂ * (a * a') * k₂⁻¹ := by group
      _ = σ x₀ := hk₂

omit [Finite P] in
theorem fcs_pos (ρ : A6 →* MulAut P) (g : A6) (V : Subgroup P) [Finite P] : 0 < fcs ρ g V :=
  Nat.card_pos

theorem fcs_le_card (ρ : A6 →* MulAut P) (g : A6) (V : Subgroup P) : fcs ρ g V ≤ Nat.card V :=
  Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)

theorem count_arg (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x ^ 2 = 1)
    (ρ : A6 →* MulAut P) {g : A6} (hg : g ^ 3 = 1) {W W' Y : Subgroup P} (hW : Inv ρ W)
    (hW' : Inv ρ W') (hY : Inv ρ Y) (hYle : Y ≤ W ⊔ W') {b s : ℕ} (hbs : b = 4 * s) (hs : 0 < s)
    (hYb : fcs ρ g Y = b) (hWb : fcs ρ g W = b) (hW's : fcs ρ g W' = s)
    (hcardW : Nat.card W ≤ 32)
    (hL1 : ∀ X : Subgroup P, X ≤ W → Inv ρ X → Nat.card W < 16 * Nat.card X → X = W)
    (hcard : Nat.card Y = Nat.card W) : Y = W := by
  have hYWinv : Inv ρ (Y ⊓ W) := fun h v hv => ⟨hY h v hv.1, hW h v hv.2⟩
  have hsupinv : ∀ {X₁ X₂ : Subgroup P}, Inv ρ X₁ → Inv ρ X₂ → Inv ρ (X₁ ⊔ X₂) := by
    intro X₁ X₂ h₁ h₂ h v hv
    have : X₂.Normal := normal_of_comm' hcomm X₂
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (h₁ h y hy) (h₂ h z hz)
  have cp1 := fcs_sup_mul hcomm hsq ρ hg hY hW
  have cp2 := fcs_sup_mul hcomm hsq ρ hg hW hW'
  have hmono : fcs ρ g (Y ⊔ W) ≤ fcs ρ g (W ⊔ W') := fcs_mono ρ g (sup_le hYle le_sup_left)
  have hi : 1 ≤ fcs ρ g (W ⊓ W') := fcs_pos ρ g _
  rw [hYb, hWb] at cp1
  rw [hWb, hW's] at cp2
  by_contra hne
  have hproper : Y ⊓ W ≠ W := by
    intro h
    apply hne
    have hWY : W ≤ Y := by rw [← h]; exact inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hWY (by rw [hcard])).symm
  have hlt : Nat.card (Y ⊓ W : Subgroup P) * 16 ≤ Nat.card W := by
    by_contra hcon
    push Not at hcon
    exact hproper (hL1 _ inf_le_right hYWinv (by omega))
  have hf2 : fcs ρ g (Y ⊓ W) ≤ 2 := by
    have := fcs_le_card ρ g (Y ⊓ W)
    omega
  have h1 : b * b ≤ fcs ρ g (W ⊔ W') * fcs ρ g (Y ⊓ W) := by
    calc b * b = fcs ρ g (Y ⊔ W) * fcs ρ g (Y ⊓ W) := cp1.symm
      _ ≤ _ := Nat.mul_le_mul_right _ hmono
  have h2 : b * b * fcs ρ g (W ⊓ W') ≤ b * s * fcs ρ g (Y ⊓ W) := by
    calc b * b * fcs ρ g (W ⊓ W') ≤ fcs ρ g (W ⊔ W') * fcs ρ g (Y ⊓ W) * fcs ρ g (W ⊓ W') :=
          Nat.mul_le_mul_right _ h1
      _ = (fcs ρ g (W ⊔ W') * fcs ρ g (W ⊓ W')) * fcs ρ g (Y ⊓ W) := by ring
      _ = b * s * fcs ρ g (Y ⊓ W) := by rw [cp2]
  have hbpos : 0 < b := by omega
  have h3 : b * fcs ρ g (W ⊓ W') ≤ s * fcs ρ g (Y ⊓ W) := by
    have : b * (b * fcs ρ g (W ⊓ W')) ≤ b * (s * fcs ρ g (Y ⊓ W)) := by
      calc b * (b * fcs ρ g (W ⊓ W')) = b * b * fcs ρ g (W ⊓ W') := by ring
        _ ≤ b * s * fcs ρ g (Y ⊓ W) := h2
        _ = b * (s * fcs ρ g (Y ⊓ W)) := by ring
    exact Nat.le_of_mul_le_mul_left this hbpos
  subst hbs
  nlinarith

theorem pick (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x ^ 2 = 1)
    (ρ : A6 →* MulAut P) {g : A6} (hg : g ^ 3 = 1) {V₁ V₂ Y : Subgroup P} (hV₁ : Inv ρ V₁)
    (hV₂ : Inv ρ V₂) (hY : Inv ρ Y) (hYle : Y ≤ V₁ ⊔ V₂) {b s : ℕ} (hbs : b = 4 * s) (hs : 0 < s)
    (hYb : fcs ρ g Y = b)
    (hV : (fcs ρ g V₁ = b ∧ fcs ρ g V₂ = s) ∨ (fcs ρ g V₁ = s ∧ fcs ρ g V₂ = b))
    (hcard₁ : Nat.card V₁ ≤ 32) (hcard₂ : Nat.card V₂ ≤ 32)
    (hL1₁ : ∀ X : Subgroup P, X ≤ V₁ → Inv ρ X → Nat.card V₁ < 16 * Nat.card X → X = V₁)
    (hL1₂ : ∀ X : Subgroup P, X ≤ V₂ → Inv ρ X → Nat.card V₂ < 16 * Nat.card X → X = V₂)
    (hYcard₁ : Nat.card Y = Nat.card V₁) (hYcard₂ : Nat.card Y = Nat.card V₂) :
    Y = V₁ ∨ Y = V₂ := by
  rcases hV with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact count_arg hcomm hsq ρ hg hV₁ hV₂ hY hYle hbs hs hYb h1 h2 hcard₁ hL1₁ hYcard₁
  · right
    exact count_arg hcomm hsq ρ hg hV₂ hV₁ hY (by rwa [sup_comm]) hbs hs hYb h2 h1 hcard₂ hL1₂ hYcard₂

omit [Finite P] in
theorem Inv.twist {ρ : A6 →* MulAut P} {τ : MulAut P} {σ : MulAut A6}
    (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g)) {V : Subgroup P} (hV : Inv ρ V) :
    Inv ρ (V.map τ.toMonoidHom) := by
  intro h v hv
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
  have := ρ_apply_twist hτ (σ.symm h) w
  rw [MulEquiv.apply_symm_apply] at this
  exact Subgroup.mem_map.mpr ⟨_, hV _ w hw, this.symm⟩

omit [Finite P] in
theorem L1_twist {ρ : A6 →* MulAut P} {τ : MulAut P} {σ : MulAut A6}
    (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g)) {V₁ : Subgroup P}
    (hL1₁ : ∀ X : Subgroup P, X ≤ V₁ → Inv ρ X → Nat.card V₁ < 16 * Nat.card X → X = V₁) :
    ∀ X : Subgroup P, X ≤ V₁.map τ.toMonoidHom → Inv ρ X →
      Nat.card (V₁.map τ.toMonoidHom) < 16 * Nat.card X → X = V₁.map τ.toMonoidHom := by
  intro X hXle hXinv hcard
  set X' : Subgroup P := X.map τ.symm.toMonoidHom with hX'
  have hX'le : X' ≤ V₁ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (hXle hx)
    have : τ.symm x = w := by rw [← hwx]; simp
    show τ.symm x ∈ V₁
    rw [this]; exact hw
  have hX'inv : Inv ρ X' := by
    intro g v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
    have h1 := ρ_apply_twist hτ g (τ.symm x)
    rw [MulEquiv.apply_symm_apply] at h1
    refine Subgroup.mem_map.mpr ⟨ρ (σ g) x, hXinv _ x hx, ?_⟩
    show τ.symm (ρ (σ g) x) = ρ g (τ.symm x)
    rw [h1]; simp
  have hc1 : Nat.card X' = Nat.card X := Subgroup.card_map_of_injective τ.symm.injective
  have hc2 : Nat.card (V₁.map τ.toMonoidHom) = Nat.card V₁ := Subgroup.card_map_of_injective τ.injective
  have hX'eq := hL1₁ X' hX'le hX'inv (by rw [hc1, ← hc2]; exact hcard)
  have : X = X'.map τ.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨τ.symm x, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, by simp⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hy
      simpa using hx'
  rw [this, hX'eq]

theorem lattice_two (hcomm : ∀ x y : P, x * y = y * x) (hsq : ∀ x : P, x ^ 2 = 1)
    (ρ : A6 →* MulAut P) {τ : MulAut P} {σ : MulAut A6} (hτ : ∀ g, τ * ρ g * τ⁻¹ = ρ (σ g))
    {x₀ : A6} (hx3 : x₀ ^ 3 = 1) (hx1 : x₀ ≠ 1) (hnc : ∀ k : A6, k * x₀ * k⁻¹ ≠ σ x₀)
    {V₁ Y : Subgroup P} (hV₁ : Inv ρ V₁) (hY : Inv ρ Y)
    (hcard : Nat.card V₁ = 16 ∨ Nat.card V₁ = 32) (hYcard : Nat.card Y = Nat.card V₁)
    (hnt₁ : ∃ g, ∃ v ∈ V₁, ρ g v ≠ v) (hntY : ∃ g, ∃ v ∈ Y, ρ g v ≠ v)
    (hL1₁ : ∀ X : Subgroup P, X ≤ V₁ → Inv ρ X → Nat.card V₁ < 16 * Nat.card X → X = V₁)
    (hYle : Y ≤ V₁ ⊔ V₁.map τ.toMonoidHom) :
    V₁ ≠ V₁.map τ.toMonoidHom ∧ (Y = V₁ ∨ Y = V₁.map τ.toMonoidHom) := by
  have hV₂ : Inv ρ (V₁.map τ.toMonoidHom) := hV₁.twist hτ
  have hcard₂ : Nat.card (V₁.map τ.toMonoidHom) = Nat.card V₁ :=
    Subgroup.card_map_of_injective τ.injective
  have hnt₂ : ∃ g, ∃ v ∈ V₁.map τ.toMonoidHom, ρ g v ≠ v := by
    obtain ⟨g, v, hv, hne⟩ := hnt₁
    refine ⟨σ g, τ v, Subgroup.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [ρ_apply_twist hτ]
    exact fun h => hne (τ.injective h)
  have hswap := swap_rel ρ hτ hV₁ hV₂ hx3 hx1 hnc
  obtain ⟨b, s, hbs, hs, hbb⟩ : ∃ b s : ℕ, b = 4 * s ∧ 0 < s ∧
      ((Nat.card V₁ = 16 ∧ b = 4 ∧ s = 1) ∨ (Nat.card V₁ = 32 ∧ b = 8 ∧ s = 2)) := by
    rcases hcard with h | h
    · exact ⟨4, 1, rfl, by norm_num, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨8, 2, rfl, by norm_num, Or.inr ⟨h, rfl, rfl⟩⟩
  have hF2 : ∀ V : Subgroup P, Inv ρ V → (∃ g, ∃ v ∈ V, ρ g v ≠ v) → Nat.card V = Nat.card V₁ →
      (fcs ρ a V = b ∧ fcs ρ (a * a') V = s) ∨ (fcs ρ a V = s ∧ fcs ρ (a * a') V = b) := by
    intro V hV hnt hc
    obtain ⟨hf16, hf32⟩ := F2_sub ρ hV hnt
    rcases hbb with ⟨h16, rfl, rfl⟩ | ⟨h32, rfl, rfl⟩
    · exact hf16 (hc.trans h16)
    · exact hf32 (hc.trans h32)
  have h1 := hF2 V₁ hV₁ hnt₁ rfl
  have h2 := hF2 _ hV₂ hnt₂ hcard₂
  have hY2 := hF2 Y hY hntY hYcard
  have hcard32 : Nat.card V₁ ≤ 32 := by rcases hcard with h | h <;> omega
  have hopp : fcs ρ a V₁ ≠ fcs ρ a (V₁.map τ.toMonoidHom) := by
    rcases h1 with ⟨e1, e1'⟩ | ⟨e1, e1'⟩ <;> rcases h2 with ⟨e2, e2'⟩ | ⟨e2, e2'⟩ <;>
      rcases hswap with e3 | e3 <;> omega
  refine ⟨fun h => hopp (by rw [← h]), ?_⟩
  rcases hY2 with ⟨ya, ya'⟩ | ⟨ya, ya'⟩
  · refine pick hcomm hsq ρ a_cube hV₁ hV₂ hY hYle hbs hs ya ?_ hcard32 (by omega) hL1₁ (L1_twist hτ hL1₁) hYcard
      (hYcard.trans hcard₂.symm)
    rcases h1 with ⟨e1, e1'⟩ | ⟨e1, e1'⟩ <;> rcases h2 with ⟨e2, e2'⟩ | ⟨e2, e2'⟩
    · exact absurd (e1.trans e2.symm) hopp
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
    · exact absurd (e1.trans e2.symm) hopp
  · refine pick hcomm hsq ρ cube_aa' hV₁ hV₂ hY hYle hbs hs ya' ?_ hcard32 (by omega) hL1₁ (L1_twist hτ hL1₁) hYcard
      (hYcard.trans hcard₂.symm)
    rcases h1 with ⟨e1, e1'⟩ | ⟨e1, e1'⟩ <;> rcases h2 with ⟨e2, e2'⟩ | ⟨e2, e2'⟩
    · exact absurd (e1.trans e2.symm) hopp
    · exact Or.inr ⟨e1', e2'⟩
    · exact Or.inl ⟨e1', e2'⟩
    · exact absurd (e1.trans e2.symm) hopp

end Lattice

end CFSG.Quasithin.A6Mod
