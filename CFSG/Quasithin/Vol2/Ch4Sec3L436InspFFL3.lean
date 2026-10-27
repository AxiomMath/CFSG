module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4A318
public import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.H13.Ch4.FFL3

open Matrix

theorem card_modEq_card_fixed {W : Type*} [Finite W] (σ : Equiv.Perm W) {p : ℕ}
    [Fact p.Prime] (hσ : σ ^ p = 1) :
    Nat.card W ≡ Nat.card {w // σ w = w} [MOD p] := by
  let Kz := Subgroup.zpowers σ
  have hK : IsPGroup p Kz := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (σ ^ k) ^ p ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hσ,
      _root_.one_zpow]
  have hset : MulAction.fixedPoints Kz W = {w | σ w = w} := by
    ext v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hv
      exact hv ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hv g
      have hle : Kz ≤ MulAction.stabilizer (Equiv.Perm W) v := by
        rw [Subgroup.zpowers_le]
        exact hv
      exact hle g.2
  have hmod := hK.card_modEq_card_fixedPoints W
  rw [hset] at hmod
  exact hmod

section SL3

variable {F : Type} [Field F] [Finite F]

theorem card_sl3 :
    Nat.card (SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  have := Fintype.ofFinite F
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_three, Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := Fintype.card F
  have h1 : 1 ≤ q := by omega
  have h2 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by
    zify [h1, h2, h3, h4, h5]
    ring
  rw [e, Nat.mul_div_cancel_left _ (by omega)]

@[expose] def fixSub (R : Subgroup (SpecialLinearGroup (Fin 3) F)) : Submodule F (Fin 3 → F) where
  carrier := {v | ∀ r ∈ R, (r : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v}
  add_mem' := fun {v w} hv hw r hr => by rw [mulVec_add, hv r hr, hw r hr]
  zero_mem' := fun r _ => mulVec_zero _
  smul_mem' := fun c v hv r hr => by rw [mulVec_smul, hv r hr]

theorem card_submodule (W : Submodule F (Fin 3 → F)) :
    Nat.card W = Nat.card F ^ Module.finrank F W := by
  have := Fintype.ofFinite F
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := W)]

@[expose] noncomputable def vecPerm : SpecialLinearGroup (Fin 3) F →* Equiv.Perm (Fin 3 → F) where
  toFun g :=
    { toFun := fun v => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      invFun := fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      left_inv := fun v => by
        show (g⁻¹).1 *ᵥ (g.1 *ᵥ v) = v
        rw [mulVec_mulVec]
        show (g⁻¹ * g).1 *ᵥ v = v
        rw [inv_mul_cancel]
        exact one_mulVec v
      right_inv := fun v => by
        show g.1 *ᵥ ((g⁻¹).1 *ᵥ v) = v
        rw [mulVec_mulVec]
        show (g * g⁻¹).1 *ᵥ v = v
        rw [mul_inv_cancel]
        exact one_mulVec v }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Equiv.Perm.mul_apply, mulVec_mulVec]

omit [Finite F] in
theorem vecPerm_apply (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) :
    vecPerm g v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v :=
  rfl

theorem dvd_pow_sub_one_of_modEq {p q a b : ℕ} (hq : 0 < q) (hpq : Nat.Coprime p q)
    (hba : b ≤ a) (h : q ^ a ≡ q ^ b [MOD p]) : p ∣ q ^ (a - b) - 1 := by
  have hle : q ^ b ≤ q ^ a := Nat.pow_le_pow_right hq hba
  have hdvd : p ∣ q ^ a - q ^ b := (Nat.modEq_iff_dvd' hle).mp h.symm
  have hfac : q ^ a - q ^ b = q ^ b * (q ^ (a - b) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hba]
  rw [hfac] at hdvd
  exact (Nat.Coprime.pow_right b hpq).dvd_of_dvd_mul_left hdvd

variable [CharP F 2]

theorem false_of_normalizes {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {x : SpecialLinearGroup (Fin 3) F} (hx : orderOf x = p)
    {R : Subgroup (SpecialLinearGroup (Fin 3) F)} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥)
    (hxR : x ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F))) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  set q := Nat.card F with hq
  have hqm : q = 2 ^ (m : ℕ) := by rw [hq, Nat.card_eq_fintype_card, hm]
  have hq0 : 0 < q := Nat.card_pos
  have hcop : Nat.Coprime p q := by
    rw [hqm]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hq1 : ¬ p ∣ q ^ 1 - 1 := by
    intro h
    apply hpq
    refine h.trans ?_
    rw [pow_one]
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have h1 : 1 ≤ q := hq0
      zify [h1, Nat.one_le_pow 2 q hq0]
      ring
    rw [this]
    exact dvd_mul_right _ _
  have hsmall : ∀ k, 0 < k → k ≤ 2 → ¬ p ∣ q ^ k - 1 := by
    intro k hk0 hk2
    interval_cases k
    · exact hq1
    · exact hpq
  set σ := vecPerm x with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  set C₀ := fixSub (Subgroup.zpowers x) with hC₀
  have hmemC₀ : ∀ v, v ∈ C₀ ↔ σ v = v := by
    intro v
    constructor
    · intro hv
      exact hv x (Subgroup.mem_zpowers x)
    · intro hv r hr
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      have hfix : ∀ g ∈ Subgroup.zpowers x, vecPerm g v = v := by
        intro g hg
        have hle : Subgroup.zpowers x ≤
            (MulAction.stabilizer (Equiv.Perm (Fin 3 → F)) v).comap vecPerm := by
          rw [Subgroup.zpowers_le]
          exact hv
        exact hle hg
      exact hfix _ ⟨k, rfl⟩
  have hC₀bot : C₀ = ⊥ := by
    have hmod := card_modEq_card_fixed σ hσp
    have e1 : Nat.card {w // σ w = w} = Nat.card C₀ :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => (hmemC₀ v).symm)
    rw [e1, card_submodule, Nat.card_fun, Nat.card_fin, ← hq] at hmod
    have hj : Module.finrank F C₀ ≤ 3 := by
      have := Submodule.finrank_le C₀
      simpa using this
    by_contra hne
    have hj0 : Module.finrank F C₀ ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
    rcases Nat.lt_or_ge (Module.finrank F C₀) 3 with hlt | hge
    · exact hsmall (3 - Module.finrank F C₀) (by omega) (by omega)
        (dvd_pow_sub_one_of_modEq hq0 hcop hj hmod)
    ·
      have htop : C₀ = ⊤ := Submodule.eq_top_of_finrank_eq (by
        have : Module.finrank F (Fin 3 → F) = 3 := by simp
        omega)
      have hx1 : x = 1 := by
        apply Subtype.ext
        ext i j
        have h := (hmemC₀ (Pi.single j 1)).mp (htop ▸ Submodule.mem_top)
        rw [vecPerm_apply, mulVec_single_one] at h
        have := congrFun h i
        simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
      rw [hx1, orderOf_one] at hx
      exact hp.one_lt.ne hx
  set W := fixSub R with hW
  have hWbot : W ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR' : IsPGroup 2 (R.map vecPerm) := hR.map vecPerm
    have hmod := hR'.card_modEq_card_fixedPoints (Fin 3 → F)
    have hset : MulAction.fixedPoints (R.map vecPerm) (Fin 3 → F) = (W : Set (Fin 3 → F)) := by
      ext v
      rw [MulAction.mem_fixedPoints]
      constructor
      · intro hv r hr
        exact hv ⟨vecPerm r, r, hr, rfl⟩
      · rintro hv ⟨g, r, hr, rfl⟩
        exact hv r hr
    rw [hset] at hmod
    change Nat.card (Fin 3 → F) ≡ Nat.card W [MOD 2] at hmod
    rw [card_submodule, Nat.card_fun, Nat.card_fin, ← hq] at hmod
    intro hbot
    rw [hbot, finrank_bot, pow_zero, hqm] at hmod
    have h2 : 2 ∣ (2 ^ (m : ℕ)) ^ 3 := dvd_pow (dvd_pow_self 2 m.ne_zero) (by norm_num)
    have h3 := Nat.mod_eq_zero_of_dvd h2
    unfold Nat.ModEq at hmod
    omega
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext i j
    have h : (r : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 = Pi.single j 1 :=
      (htop ▸ Submodule.mem_top : Pi.single j 1 ∈ W) r hr
    rw [mulVec_single_one] at h
    have := congrFun h i
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hgW : ∀ g ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 3) F)),
      ∀ v ∈ W, vecPerm g v ∈ W := by
    intro g hg v hv r hr
    have hr' : g⁻¹ * r * g ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * r * g)).mpr (by group; exact hr)
    have e : (r : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (g : Matrix (Fin 3) (Fin 3) F) *ᵥ
          (((g⁻¹ * r * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
      rw [mulVec_mulVec, mulVec_mulVec]
      have e1 : (g : Matrix (Fin 3) (Fin 3) F) *
          ((g⁻¹ * r * g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((g * (g⁻¹ * r * g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := rfl
      have e2 : g * (g⁻¹ * r * g) = r * g := by group
      rw [e1, e2]
      rfl
    rw [vecPerm_apply, e, hv _ hr']
  have hσW : ∀ v, v ∈ W ↔ σ v ∈ W := by
    intro v
    refine ⟨hgW x hxR v, fun hv => ?_⟩
    have h1 := hgW x⁻¹ (inv_mem hxR) _ hv
    rwa [hσ, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Equiv.Perm.one_apply] at h1
  set σW : Equiv.Perm W := σ.subtypePerm (fun v => (hσW v).symm) with hσWdef
  have hσWp : σW ^ p = 1 := by
    rw [hσWdef, Equiv.Perm.subtypePerm_pow]
    ext w
    simp [hσp]
  have hfix1 : Nat.card {w // σW w = w} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨0, ?_⟩⟩⟩
    · have ha : ((a : W) : Fin 3 → F) ∈ C₀ := (hmemC₀ _).mpr (congrArg Subtype.val a.2)
      have hb : ((b : W) : Fin 3 → F) ∈ C₀ := (hmemC₀ _).mpr (congrArg Subtype.val b.2)
      rw [hC₀bot, Submodule.mem_bot] at ha hb
      exact Subtype.ext (ha.trans hb.symm)
    · apply Subtype.ext
      show σ 0 = 0
      rw [hσ, vecPerm_apply, mulVec_zero]
  have hmod := card_modEq_card_fixed σW hσWp
  rw [hfix1, card_submodule, ← hq] at hmod
  have hk0 : Module.finrank F W ≠ 0 := fun h => hWbot (Submodule.finrank_eq_zero.mp h)
  have hk3 : Module.finrank F W < 3 := by
    have hle : Module.finrank F W ≤ 3 := by
      have := Submodule.finrank_le W
      simpa using this
    refine lt_of_le_of_ne hle fun h3 => hWtop (Submodule.eq_top_of_finrank_eq ?_)
    have : Module.finrank F (Fin 3 → F) = 3 := by simp
    omega
  have h1 : q ^ Module.finrank F W ≡ q ^ 0 [MOD p] := by rwa [pow_zero]
  have := dvd_pow_sub_one_of_modEq hq0 hcop (Nat.zero_le _) h1
  rw [Nat.sub_zero] at this
  exact hsmall _ (by omega) (by omega) this

omit [CharP F 2] in
theorem two_le_pRank_sl3 {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1) :
    2 ≤ CFSG.pRank p (SpecialLinearGroup (Fin 3) F) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by rw [Nat.card_units]; exact hpF)
  set Θ := CFSG.RankThree.PartOne.torusTwoHom (n := 3) le_rfl F with hΘ
  have hωp : ω ^ p = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  refine CFSG.RankThree.PartOne.two_le_pRank_of_two_elements hp (e₁ := Θ (ω, 1))
    (e₂ := Θ (1, ω)) ((Commute.all (ω, 1) (1, ω)).map Θ) ?_ ?_ ?_
  · rw [← map_pow]
    have : ((ω, 1) : Fˣ × Fˣ) ^ p = 1 := by ext <;> simp [hωp]
    rw [this, map_one]
  · rw [← map_pow]
    have : ((1, ω) : Fˣ × Fˣ) ^ p = 1 := by ext <;> simp [hωp]
    rw [this, map_one]
  · intro i j hij
    rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    have hpair : ((ω, 1) : Fˣ × Fˣ) ^ i * ((1, ω) : Fˣ × Fˣ) ^ j = (ω ^ i, ω ^ j) := by
      ext <;> simp
    rw [hpair] at hij
    have hmat := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F)) hij
    have h0 := congrFun₂ hmat 0 0
    have h2 := congrFun₂ hmat 2 2
    simp [hΘ, CFSG.RankThree.PartOne.torusTwoHom, CFSG.RankThree.PartOne.torusTwo,
      CFSG.RankThree.PartOne.torusTwoMat] at h0 h2
    have h1 : ω ^ i = 1 := Units.ext (by simpa using h0)
    have h3 : ω ^ j = 1 := by
      have : ((ω ^ j)⁻¹ : Fˣ) = 1 := Units.ext (by simpa using h2)
      exact inv_eq_one.mp this
    have h1' := orderOf_dvd_iff_zpow_eq_one.mpr h1
    have h3' := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rw [hω] at h1' h3'
    exact ⟨h1', h3'⟩

end SL3

theorem dvd_two_pow_sub_one_iff {p : ℕ} (a : ℕ) :
    p ∣ 2 ^ a - 1 ↔ orderOf (2 : ZMod p) ∣ a := by
  rw [CFSG.SL2MinimalFaithful.Zsigmondy.dvd_pow_sub_one_iff (by norm_num : 0 < 2) a,
    orderOf_dvd_iff_pow_eq_one]
  norm_num

theorem dvd_two_pow_sub_one_of {p n m : ℕ} (hn : 1 ≤ n) (hpn : p ∣ 2 ^ n - 1)
    (hpm : p ∣ 2 ^ (2 * m) - 1)
    (hr : n = 3 ∨ ∃ r : ℕ, r ∣ 2 ^ (2 * n) - 1 ∧ (∀ k, 0 < k → k < 2 * n → ¬ r ∣ 2 ^ k - 1) ∧
      (r ∣ 2 ^ (2 * m) - 1 ∨ r ∣ 2 ^ (3 * m) - 1)) : p ∣ 2 ^ m - 1 := by
  rw [dvd_two_pow_sub_one_iff] at hpn hpm ⊢
  rcases hr with rfl | ⟨r, hr1, hprim, hr2⟩
  · rcases (Nat.dvd_prime Nat.prime_three).mp hpn with hd | hd
    · rw [hd]
      exact one_dvd _
    · rw [hd] at hpm ⊢
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hpm
  ·
    have hord : ∀ k, r ∣ 2 ^ k - 1 → 2 * n ∣ k := by
      intro k hk
      rw [dvd_two_pow_sub_one_iff] at hk
      have hr1' := (dvd_two_pow_sub_one_iff (p := r) (2 * n)).mp hr1
      have hpos : 0 < orderOf (2 : ZMod r) := Nat.pos_of_dvd_of_pos hr1' (by omega)
      have hle : orderOf (2 : ZMod r) ≤ 2 * n := Nat.le_of_dvd (by omega) hr1'
      have he : orderOf (2 : ZMod r) = 2 * n := by
        refine le_antisymm hle (not_lt.mp fun hlt => hprim _ hpos hlt ?_)
        exact (dvd_two_pow_sub_one_iff _).mpr dvd_rfl
      rwa [he] at hk
    rcases hr2 with h | h
    · have h2 := hord _ h
      exact hpn.trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2)
    · have h2n : 2 * n ∣ 3 * m := hord _ h
      have h1 : 2 * orderOf (2 : ZMod p) ∣ 3 * m := (Nat.mul_dvd_mul_left 2 hpn).trans h2n
      have h2 : 2 * orderOf (2 : ZMod p) ∣ 4 * m := by
        have := Nat.mul_dvd_mul_left 2 hpm
        rwa [← mul_assoc] at this
      have h3 : 2 * orderOf (2 : ZMod p) ∣ 4 * m - 3 * m := Nat.dvd_sub h2 h1
      rw [show 4 * m - 3 * m = m by omega] at h3
      exact (Dvd.intro_left 2 rfl).trans h3

section SL2

variable {F' : Type} [Field F']

@[expose] noncomputable def diagHom : F'ˣ →* SpecialLinearGroup (Fin 2) F' where
  toFun μ := ⟨!![(μ : F'), 0; 0, ((μ⁻¹ : F'ˣ) : F')], by simp [det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' μ ν := by
    apply Subtype.ext
    show !![((μ * ν : F'ˣ) : F'), 0; 0, (((μ * ν)⁻¹ : F'ˣ) : F')] =
      !![(μ : F'), 0; 0, ((μ⁻¹ : F'ˣ) : F')] * !![(ν : F'), 0; 0, ((ν⁻¹ : F'ˣ) : F')]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagHom_apply_zero (μ : F'ˣ) :
    ((diagHom μ : SpecialLinearGroup (Fin 2) F') : Matrix (Fin 2) (Fin 2) F') 0 0 = μ := rfl

theorem diagHom_injective : Function.Injective (diagHom (F' := F')) := by
  intro μ ν h
  refine Units.ext ?_
  rw [← diagHom_apply_zero μ, h, diagHom_apply_zero]

theorem diagHom_conj_unipotent (μ : F'ˣ) (t : F') :
    diagHom μ * CFSG.SL2MinimalFaithful.unipotent t * (diagHom μ)⁻¹ =
      CFSG.SL2MinimalFaithful.unipotent ((μ : F') * μ * t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  show !![(μ : F'), 0; 0, ((μ⁻¹ : F'ˣ) : F')] * !![1, t; 0, 1] =
    !![1, (μ : F') * μ * t; 0, 1] * !![(μ : F'), 0; 0, ((μ⁻¹ : F'ˣ) : F')]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

@[expose] def rootGroup : Subgroup (SpecialLinearGroup (Fin 2) F') :=
  (CFSG.SL2MinimalFaithful.unipotentHom (F := F')).range

theorem diagHom_mem_normalizer (μ : F'ˣ) :
    diagHom μ ∈
      Subgroup.normalizer (rootGroup (F' := F') : Set (SpecialLinearGroup (Fin 2) F')) := by
  have key : ∀ ν : F'ˣ, ∀ h ∈ rootGroup (F' := F'),
      diagHom ν * h * (diagHom ν)⁻¹ ∈ rootGroup := by
    rintro ν _ ⟨t, rfl⟩
    refine ⟨Multiplicative.ofAdd ((ν : F') * ν * t.toAdd), ?_⟩
    exact (diagHom_conj_unipotent ν t.toAdd).symm
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key μ h, fun hh => ?_⟩
  have := key μ⁻¹ _ hh
  rw [map_inv, inv_inv] at this
  simpa [mul_assoc] using this

variable [CharP F' 2]

theorem isPGroup_rootGroup : IsPGroup 2 (rootGroup (F' := F')) := by
  rintro ⟨_, t, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, sq, ← map_mul]
  show CFSG.SL2MinimalFaithful.unipotent (t.toAdd + t.toAdd) = 1
  rw [CharTwo.add_self_eq_zero, CFSG.SL2MinimalFaithful.unipotent_zero]

omit [CharP F' 2] in
theorem rootGroup_ne_bot : rootGroup (F' := F') ≠ ⊥ := by
  intro h
  have hmem : CFSG.SL2MinimalFaithful.unipotentHom (Multiplicative.ofAdd (1 : F')) ∈
      rootGroup (F' := F') := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := CFSG.SL2MinimalFaithful.unipotentHom_injective
    (hmem.trans (map_one CFSG.SL2MinimalFaithful.unipotentHom).symm)
  exact one_ne_zero (congrArg Multiplicative.toAdd this)

end SL2

theorem false_of_sl3 {G : Type} [Group G] [Finite G] {L K : Subgroup G} {n m p : ℕ}
    (hn : 2 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (e : ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) (hLq : CFSG.IsQuasisimple ↥L)
    (hKL : K ≤ L) (hK : IsPSL 2 2 n ↥K) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hcase : CFSG.Open.pRank p L ≤ 1 ∨
      (p = 3 ∧ ∃ (S : Type) (_ : Group S) (φ : ↥L →* S), Function.Surjective φ ∧
        (∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) ∧
        ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
          IsPSLEps3q s q S)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hm1 : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hF] at h2
    by_contra h0
    have : m = 0 := by omega
    subst this
    norm_num at h2
  have : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have hcardK : Nat.card ↥K = 2 ^ n * (4 ^ n - 1) :=
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hK
  obtain ⟨-, F', _, _, hF', ⟨eK⟩⟩ := hK
  have : CharP F' 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF'
  let eK' : ↥K ≃* SpecialLinearGroup (Fin 2) F' :=
    eK.trans ((CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 2 F').trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL F'))
  let ψ : ↥L ≃* SpecialLinearGroup (Fin 3) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  let θ : SpecialLinearGroup (Fin 2) F' →* SpecialLinearGroup (Fin 3) F :=
    ψ.toMonoidHom.comp ((Subgroup.inclusion hKL).comp eK'.symm.toMonoidHom)
  have hθ : Function.Injective θ :=
    ψ.injective.comp ((Subgroup.inclusion_injective hKL).comp eK'.symm.injective)
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := F'ˣ) p
    (by rw [Nat.card_units, hF']; exact hpn)
  have hx : orderOf (θ (diagHom μ)) = p := by
    rw [orderOf_injective θ hθ, orderOf_injective _ diagHom_injective, hμ]
  have hR : IsPGroup 2 ((rootGroup (F' := F')).map θ) := isPGroup_rootGroup.map θ
  have hR1 : (rootGroup (F' := F')).map θ ≠ ⊥ := by
    intro h
    exact rootGroup_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ hθ).mp h)
  have hxR : θ (diagHom μ) ∈ Subgroup.normalizer
      (((rootGroup (F' := F')).map θ : Subgroup _) : Set (SpecialLinearGroup (Fin 3) F)) :=
    Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ (diagHom_mem_normalizer μ))
  have hpq2 : p ∣ Nat.card F ^ 2 - 1 := by
    by_contra h
    exact false_of_normalizes hp hp2 h hx hR hR1 hxR
  have hpq : p ∣ Nat.card F - 1 := by
    rw [hF] at hpq2 ⊢
    rw [← pow_mul, mul_comm] at hpq2
    refine dvd_two_pow_sub_one_of (by omega) hpn hpq2 ?_
    by_cases hn3 : n = 3
    · exact Or.inl hn3
    right
    obtain ⟨r, hr, hrdvd, hprim⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * n) (by omega) (by omega)
    refine ⟨r, hrdvd, hprim, ?_⟩
    have hcardL : Nat.card ↥L =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr ψ.toEquiv, card_sl3]
    have hdvd : r ∣ Nat.card ↥L := by
      have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
      have h1 : r ∣ 2 ^ n * (4 ^ n - 1) := Dvd.dvd.mul_left (by rwa [h4]) _
      exact (hcardK ▸ h1).trans (Subgroup.card_dvd_of_le hKL)
    rw [hcardL, hF] at hdvd
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
      have h2 := Nat.dvd_sub h1 hrdvd
      rw [Nat.sub_sub_self Nat.one_le_two_pow] at h2
      omega
    have hcop : Nat.Coprime r ((2 ^ m) ^ 3) :=
      Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _
        ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
    have h2 := hcop.dvd_of_dvd_mul_left hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h2 with h | h
    · left
      rwa [← pow_mul, mul_comm] at h
    · right
      rwa [← pow_mul, mul_comm] at h
  have hrank : 2 ≤ CFSG.Open.pRank p L := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt ψ,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact two_le_pRank_sl3 hp hpq
  rcases hcase with h | ⟨rfl, S, _, φ, hφ, hker, s, q, -, hS⟩
  · omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3
    (by rw [Nat.card_units]; exact hpq)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    omega
  let z : SpecialLinearGroup (Fin 3) F :=
    ⟨scalar (Fin 3) (ω : F), by
      rw [scalar_apply, det_diagonal, Fin.prod_const, ← Units.val_pow_eq_pow_val, hω3,
        Units.val_one]⟩
  have hzc : ∀ g : SpecialLinearGroup (Fin 3) F, z * g = g * z := fun g => by
    apply Subtype.ext
    show scalar (Fin 3) (ω : F) * (g : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (ω : F)
    exact (scalar_commute (ω : F) (fun _ => Commute.all _ _) _)
  have hz3 : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (scalar (Fin 3) (ω : F)) ^ 3 = 1
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hω3, Units.val_one, map_one]
    · intro h1
      apply hω1
      have := congrArg (fun g : SpecialLinearGroup (Fin 3) F =>
        (g : Matrix (Fin 3) (Fin 3) F) 0 0) h1
      exact Units.ext (by simpa [z] using this)
  set z' := ψ.symm z with hz'
  have hz'c : ∀ l : ↥L, z' * l = l * z' := fun l => by
    apply ψ.injective
    rw [map_mul, map_mul, hz', MulEquiv.apply_symm_apply]
    exact hzc (ψ l)
  have : IsSimpleGroup S := L436.isSimpleGroup_of_isPSLEps3q hS
  have hSperf : Group.IsPerfect S := by
    rw [Group.isPerfect_def]
    have hL := Group.isPerfect_def.mp hLq.1
    rw [commutator_def] at hL ⊢
    rw [← Subgroup.map_top_of_surjective φ hφ, ← Subgroup.map_commutator, hL]
  have hφz : φ z' = 1 := L436.eq_one_of_forall_commute hSperf fun y => by
    obtain ⟨l, rfl⟩ := hφ y
    rw [← map_mul, ← map_mul, hz'c l]
  have h3 := hker z' hφz
  rw [hz', MulEquiv.orderOf_eq, hz3] at h3
  exact h3 dvd_rfl

end CFSG.Quasithin.H13.Ch4.FFL3
