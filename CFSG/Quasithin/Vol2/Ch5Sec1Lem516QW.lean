module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Semi
public import CFSG.Quasithin.Vol2.Ch5ModulesNat
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QLine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Offender
open scoped IsMulCommutative MatrixGroups Matrix Pointwise commutatorElement
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL)

variable {G : Type} [Group G]

theorem mem_normalizer_normalizer {K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    t ∈ Subgroup.normalizer ((Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hx) (Subgroup.inv_mem _ ht)
  · intro hx
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hx) ht
    simpa [mul_assoc] using this

@[expose] noncomputable def avgOn {N D : Subgroup G} [IsMulCommutative ↥N] [Fintype ↥D]
    (hD : D ≤ Subgroup.normalizer (N : Set G)) : ↥N →* ↥N where
  toFun x := ∏ δ : ↥D, conjAct N ⟨δ, hD δ.2⟩ x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    exact Finset.prod_mul_distrib

theorem avgOn_apply {N D : Subgroup G} [IsMulCommutative ↥N] [Fintype ↥D]
    (hD : D ≤ Subgroup.normalizer (N : Set G)) (x : ↥N) :
    avgOn hD x = ∏ δ : ↥D, conjAct N ⟨δ, hD δ.2⟩ x := rfl

theorem avgOn_of_mem_centralizer {N D : Subgroup G} [IsMulCommutative ↥N] [Fintype ↥D]
    (hD : D ≤ Subgroup.normalizer (N : Set G)) (h2 : ∀ x : ↥N, x * x = 1)
    (hodd : Odd (Fintype.card ↥D)) {x : ↥N} (hx : (x : G) ∈ Subgroup.centralizer (D : Set G)) :
    avgOn hD x = x := by
  have hfix : ∀ δ : ↥D, conjAct N ⟨δ, hD δ.2⟩ x = x := fun δ => by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show (δ : G) * x * (δ : G)⁻¹ = x
    rw [Subgroup.mem_centralizer_iff.mp hx δ δ.2, mul_inv_cancel_right]
  rw [avgOn_apply]
  simp only [hfix]
  rw [Finset.prod_const, Finset.card_univ]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, sq, h2, one_pow, one_mul]

theorem avgOn_conj {N D : Subgroup G} [IsMulCommutative ↥N] [Fintype ↥D]
    (hD : D ≤ Subgroup.normalizer (N : Set G)) (δ₁ : ↥D) (x : ↥N) :
    avgOn hD (conjAct N ⟨δ₁, hD δ₁.2⟩ x) = avgOn hD x := by
  rw [avgOn_apply, avgOn_apply]
  have e : ∀ δ : ↥D, conjAct N ⟨(δ : G), hD δ.2⟩ (conjAct N ⟨δ₁, hD δ₁.2⟩ x) =
      conjAct N ⟨((δ * δ₁ : ↥D) : G), hD (δ * δ₁).2⟩ x := by
    intro δ
    rw [← MulAut.mul_apply, ← map_mul]
    rfl
  simp only [e]
  exact Equiv.prod_comp (Equiv.mulRight δ₁) (fun δ => conjAct N ⟨(δ : G), hD δ.2⟩ x)

theorem exists_ne_zero_ne_one_of_two_lt_card {F : Type*} [Field F] [Finite F]
    (hF : 2 < Nat.card F) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  by_contra hall
  push Not at hall
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [hall x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 := Finset.card_le_two (a := (0 : F)) (b := 1)
  omega

theorem eq_one_of_mem_of_odd [Finite G] {D T : Subgroup G} (hD : Odd (Nat.card D))
    (hT : IsPGroup 2 T) {x : G} (hxD : x ∈ D) (hxT : x ∈ T) : x = 1 := by
  have hT' : Nat.card ↥(D ⊓ T) = 1 := by
    have h1 : Nat.card ↥(D ⊓ T) ∣ Nat.card D := Subgroup.card_dvd_of_le inf_le_left
    have h2 : IsPGroup 2 ↥(D ⊓ T) := hT.to_le inf_le_right
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk] at h1 ⊢
    cases k with
    | zero => rfl
    | succ k =>
      exfalso
      have h3 : 2 ∣ Nat.card D := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1
      exact (Nat.not_even_iff_odd.mpr hD) (even_iff_two_dvd.mpr h3)
  have := Subgroup.eq_bot_of_card_eq _ hT'
  have hx : x ∈ D ⊓ T := ⟨hxD, hxT⟩
  rw [this, Subgroup.mem_bot] at hx
  exact hx

theorem Semi516.mem_centralizer_of_linear_line {F : Type} [Field F] [CharP F 2] {W : Subgroup G}
    (e : ↥W ≃* Multiplicative (Fin 1 → F)) {t : G} (ht : t ∈ Subgroup.normalizer (W : Set G))
    {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (hlin : IsSemilinearWith (Semi516.act e t ht) (1 : F ≃+* F)) :
    t ∈ Subgroup.centralizer (W : Set G) := by
  set p := Semi516.act e t ht with hp
  set c : F := p (fun _ => 1) 0 with hc
  have hsc : ∀ x, p x = c • x := by
    intro x
    have hx : x = x 0 • (fun _ : Fin 1 => (1 : F)) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp
    have h1 : p (x 0 • fun _ => 1) = x 0 • p (fun _ => 1) := hlin (x 0) _
    rw [← hx] at h1
    rw [h1]
    funext i
    rw [Fin.fin_one_eq_zero i]
    simp only [Pi.smul_apply, smul_eq_mul, hc]
    ring
  have hpow : ∀ m : ℕ, ∀ v, (p ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Equiv.Perm.mul_apply, hsc, ih, smul_smul, pow_succ]
  have hpk : p ^ 2 ^ k = 1 := by
    rw [hp, ← Semi516.act_pow e ht]
    exact (Semi516.act_eq_one_iff e _).mpr (by rw [htk]; exact Subgroup.one_mem _)
  have hck : c ^ 2 ^ k = 1 := by
    have h1 := hpow (2 ^ k) (fun _ => 1)
    rw [hpk, Equiv.Perm.one_apply] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at h2
    exact h2.symm
  have hc1 : c = 1 := Semi516.eq_one_of_pow_two_pow_eq_one hck
  rw [← Semi516.act_eq_one_iff e ht]
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.one_apply]
  show p x = x
  rw [hsc, hc1, one_smul]

namespace QCoord

variable {L N S : Subgroup G} {F : Type} [Field F] {ψ : ↥(autOn L N) ≃* SL(2, F)}
  {Y : ↥N →* Multiplicative (Fin 2 → F)}

theorem not_le_centralizer (_hc : QCoord L N S F ψ Y) :
    ¬ L ≤ Subgroup.centralizer (N : Set G) := by
  intro hL
  obtain ⟨g, hgL, hg⟩ := mem_autOn_iff.mp (ψ.symm (unipSL 1)).2
  have h1 : ψ.symm (unipSL 1) = 1 := by
    apply Subtype.ext
    rw [← hg]
    ext w
    rw [conjAct_apply_coe]
    show (g : G) * w * (g : G)⁻¹ = w
    rw [← Subgroup.mem_centralizer_iff.mp (hL hgL) w w.2, mul_inv_cancel_right]
  have h2 : unipSL (1 : F) = 1 := by
    rw [← ψ.apply_symm_apply (unipSL 1), h1, map_one]
  have h3 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h2
  simp [coe_unipSL] at h3

end QCoord

structure QuotCtx (T L D R N : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (ψ : ↥(autOn L N) ≃* SL(2, F)) (Y : ↥N →* Multiplicative (Fin 2 → F)) : Prop where
  setting : Setting516 T L D R
  two_le : 2 ≤ n
  le_R : N ≤ R
  le_normalizer : L ⊔ T ≤ Subgroup.normalizer (N : Set G)
  nat : IsNatQuotCh5 L N n
  card : Nat.card F = 2 ^ n
  coord : QCoord L N (T ⊓ L) F ψ Y
  lift : ∀ y : F, ∃ p : ↥N, (p : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
    Y p = Multiplicative.ofAdd ![y, 0]

namespace QuotCtx

variable {T L D R N : Subgroup G} {n : ℕ} {F : Type} [Field F]
  {ψ : ↥(autOn L N) ≃* SL(2, F)} {Y : ↥N →* Multiplicative (Fin 2 → F)}
  (h : QuotCtx T L D R N n F ψ Y)
include h

abbrev P (_h : QuotCtx T L D R N n F ψ Y) : Subgroup G :=
  N ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)

abbrev W (_h : QuotCtx T L D R N n F ψ Y) : Subgroup G :=
  ⁅N ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G), borelL T L⁆

theorem L_le : L ≤ Subgroup.normalizer (N : Set G) := le_sup_left.trans h.le_normalizer

theorem T_le : T ≤ Subgroup.normalizer (N : Set G) := le_sup_right.trans h.le_normalizer

theorem N_le_T : N ≤ T := h.le_R.trans h.setting.le_T

theorem comm : IsMulCommutative ↥N := h.nat.2.1

theorem sq_eq_one (x : G) (hx : x ∈ N) : x ^ 2 = 1 :=
  h.setting.reduced.2.2.1.2 x (h.le_R hx)

theorem T_le_normalizer_inf : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  fun _ ht => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer ht, h.setting.le_normalizer ht⟩

theorem T_le_normalizer_borel :
    T ≤ Subgroup.normalizer ((borelL T L : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.setting.le_normalizer ht,
    mem_normalizer_normalizer (h.T_le_normalizer_inf ht)⟩

theorem borel_le_normalizer_P : borelL T L ≤ Subgroup.normalizer (h.P : Set G) := fun _ hb =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.L_le (Subgroup.mem_inf.mp hb).1,
    F7.normalizer_le_normalizer_centralizer _ (Subgroup.mem_inf.mp hb).2⟩

theorem T_le_normalizer_P : T ≤ Subgroup.normalizer (h.P : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨h.T_le ht,
    F7.normalizer_le_normalizer_centralizer _ (h.T_le_normalizer_inf ht)⟩

theorem W_le_P : h.W ≤ h.P :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp h.borel_le_normalizer_P

theorem W_le_N : h.W ≤ N := h.W_le_P.trans inf_le_left

theorem T_le_normalizer_W : T ≤ Subgroup.normalizer (h.W : Set G) :=
  le_normalizer_commutator_of h.T_le_normalizer_P h.T_le_normalizer_borel

theorem borel_le_normalizer_W : borelL T L ≤ Subgroup.normalizer (h.W : Set G) :=
  le_normalizer_commutator_of h.borel_le_normalizer_P Subgroup.le_normalizer

theorem D_le_L : D ≤ L := h.setting.hall.1.trans inf_le_left

theorem D_le_normalizer : D ≤ Subgroup.normalizer (N : Set G) := h.D_le_L.trans h.L_le

theorem D_le_borel : D ≤ borelL T L := h.setting.hall.1

theorem D_le_normalizer_inf : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  h.D_le_borel.trans inf_le_right

theorem sup_eq_borel [Finite G] : D ⊔ (T ⊓ L) = borelL T L :=
  sup_eq_of_isHall_isSylow h.setting.hall
    (A4.isSylowTwoOf_mono h.setting.sylow (Hyp5_0_1.inf_le_borel T L) inf_le_left)

theorem exists_mul_of_mem_borel [Finite G] {b : G} (hb : b ∈ borelL T L) :
    ∃ δ ∈ D, ∃ s ∈ T ⊓ L, δ * s = b := by
  have hb' : b ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
    rw [h.sup_eq_borel]
    exact hb
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) h.D_le_normalizer_inf] at hb'
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hb'
  exact ⟨δ, hδ, s, hs, rfl⟩

theorem exists_mul_of_mem_borel' [Finite G] {b : G} (hb : b ∈ borelL T L) :
    ∃ s ∈ T ⊓ L, ∃ δ ∈ D, s * δ = b := by
  have hb' : b ∈ (((T ⊓ L) ⊔ D : Subgroup G) : Set G) := by
    rw [sup_comm, h.sup_eq_borel]
    exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) D h.D_le_normalizer_inf] at hb'
  obtain ⟨s, hs, δ, hδ, rfl⟩ := hb'
  exact ⟨s, hs, δ, hδ, rfl⟩

theorem decomp [Finite G] {x : G} (hx : x ∈ T ⊔ D) : ∃ t ∈ T, ∃ δ ∈ D, t * δ = x := by
  have hx' : x ∈ ((T ⊔ borelL T L : Subgroup G) : Set G) := sup_le_sup_left h.D_le_borel T hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T (borelL T L) h.T_le_normalizer_borel] at hx'
  obtain ⟨t, ht, b, hb, rfl⟩ := hx'
  obtain ⟨s, hs, δ, hδ, rfl⟩ := h.exists_mul_of_mem_borel' hb
  exact ⟨t * s, T.mul_mem ht (Subgroup.mem_inf.mp hs).1, δ, hδ, by group⟩

theorem inf_centralizer_le [Finite G] : (L ⊔ T) ⊓ Subgroup.centralizer (N : Set G) ≤ T :=
  h.setting.sup_inf_centralizer_le h.le_normalizer h.coord.not_le_centralizer

theorem eq_one_of_mem_centralizer [Finite G] {w : G} (hw : w ∈ h.W)
    (hwC : w ∈ Subgroup.centralizer (L : Set G)) : w = 1 := by
  classical
  have := h.comm
  have := Fintype.ofFinite ↥D
  have hDN := h.D_le_normalizer
  have hker : h.W ≤ (avgOn hDN).ker.map N.subtype := by
    rw [Subgroup.commutator_le]
    intro p hp b hb
    obtain ⟨δ, hδ, s, hs, rfl⟩ := h.exists_mul_of_mem_borel hb
    have hpN : p ∈ N := (Subgroup.mem_inf.mp hp).1
    have hpS : p ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hp).2
    have hsp : s * p = p * s := Subgroup.mem_centralizer_iff.mp hpS s hs
    have hsp' : s * p⁻¹ = p⁻¹ * s := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hsp, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨⟨p, hpN⟩ * (conjAct N ⟨δ, hDN hδ⟩ ⟨p, hpN⟩)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, avgOn_conj hDN ⟨δ, hδ⟩,
        mul_inv_cancel]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe]
      have e1 : p * (δ * s) * p⁻¹ * (δ * s)⁻¹ = p * δ * (s * p⁻¹) * s⁻¹ * δ⁻¹ := by group
      rw [commutatorElement_def, e1, hsp']
      group
  obtain ⟨w', hw', rfl⟩ := hker hw
  have h2 : ∀ x : ↥N, x * x = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_mul, ← sq]
    exact h.sq_eq_one x x.2)
  have hodd : Odd (Fintype.card ↥D) := by
    rw [← Nat.card_eq_fintype_card]
    exact h.setting.hall.2.1
  have hcD : (w' : G) ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd =>
      Subgroup.mem_centralizer_iff.mp hwC d (h.D_le_L hd)
  have hfix := avgOn_of_mem_centralizer hDN h2 hodd hcD
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw'
  rw [← hfix, hw']
  rfl

theorem snd_eq_zero (p : ↥N) (hp : (p : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) :
    (Multiplicative.toAdd (Y p)) 1 = 0 :=
  (h.coord.snd_eq_zero_iff inf_le_right p).mpr fun s hs => by
    rw [Subgroup.mem_centralizer_iff.mp hp s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem exists_mem_W [Finite G] [CharP F 2] (y : F) :
    ∃ w : ↥N, (w : G) ∈ h.W ∧ Y w = Multiplicative.ofAdd ![y, 0] := by
  have hF0 : Nat.card F ≠ 0 := by
    rw [h.card]
    positivity
  have : Finite F := Nat.finite_of_card_ne_zero hF0
  have hF2 : 2 < Nat.card F := by
    rw [h.card]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_two_lt_card hF2
  obtain ⟨δ, hδ, hδc⟩ := h.coord.exists_mem_D h.inf_centralizer_le h.setting.sylow
    h.setting.hall hc0
  have h1c : 1 + c ≠ 0 := fun h0 => hc1 (by
    have := eq_neg_of_add_eq_zero_right h0
    rwa [CharTwo.neg_eq] at this)
  obtain ⟨p, hpS, hp⟩ := h.lift (y / (1 + c))
  have hδB : δ ∈ borelL T L := h.setting.hall.1 hδ
  have hδL : δ ∈ L := (Subgroup.mem_inf.mp hδB).1
  have hδS : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hδB).2
  have hl := h.coord.toAdd_Y_line hδL hδS p (h.snd_eq_zero p hpS)
  rw [hδc, hp] at hl
  refine ⟨p * (((autHom h.coord.le_normalizer ⟨δ, hδL⟩ : ↥(autOn L N)) : MulAut ↥N) p)⁻¹,
    ?_, ?_⟩
  · have hmem : ⁅(p : G), δ⁆ ∈ h.W :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨p.2, hpS⟩) hδB
    convert hmem using 1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, autHom_apply_coe, commutatorElement_def]
    group
  · apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hl, hp]
    funext i
    fin_cases i
    · simp only [toAdd_ofAdd, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      have e : y / (1 + c) + -(c * (y / (1 + c))) = (1 + c) * (y / (1 + c)) := by
        rw [← neg_mul, CharTwo.neg_eq]
        ring
      rw [e]
      field_simp
    · simp

@[expose] noncomputable def coordHom (h : QuotCtx T L D R N n F ψ Y) :
    ↥h.W →* Multiplicative (Fin 1 → F) where
  toFun w := Multiplicative.ofAdd fun _ =>
    (Multiplicative.toAdd (Y (Subgroup.inclusion h.W_le_N w))) 0
  map_one' := by
    simp only [map_one, toAdd_one, Pi.zero_apply]
    rfl
  map_mul' a b := by
    simp only [map_mul, toAdd_mul, Pi.add_apply]
    rfl

theorem coordHom_apply (w : ↥h.W) :
    Multiplicative.toAdd (h.coordHom w) =
      fun _ => (Multiplicative.toAdd (Y (Subgroup.inclusion h.W_le_N w))) 0 := rfl

theorem coordHom_bijective [Finite G] [CharP F 2] : Function.Bijective h.coordHom := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro w hw
    have h0 : (Multiplicative.toAdd (Y (Subgroup.inclusion h.W_le_N w))) 0 = 0 := by
      have := congrFun (congrArg Multiplicative.toAdd hw) 0
      rw [coordHom_apply] at this
      exact this
    have h1 := h.snd_eq_zero (Subgroup.inclusion h.W_le_N w) (h.W_le_P w.2).2
    have hY : Y (Subgroup.inclusion h.W_le_N w) = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hC := (h.coord.ker _).mp hY
    exact Subtype.ext (h.eq_one_of_mem_centralizer w.2 hC)
  · intro v
    obtain ⟨w, hwW, hw⟩ := h.exists_mem_W ((Multiplicative.toAdd v) 0)
    refine ⟨⟨w, hwW⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [coordHom_apply]
    funext i
    rw [Fin.fin_one_eq_zero i]
    have : Subgroup.inclusion h.W_le_N ⟨(w : G), hwW⟩ = w := rfl
    rw [this, hw]
    simp

@[expose] noncomputable def coord1 [Finite G] [CharP F 2] (h : QuotCtx T L D R N n F ψ Y) :
    ↥h.W ≃* Multiplicative (Fin 1 → F) :=
  MulEquiv.ofBijective h.coordHom h.coordHom_bijective

theorem toAdd_coord1 [Finite G] [CharP F 2] (w : ↥h.W) :
    Multiplicative.toAdd (h.coord1 w) =
      fun _ => (Multiplicative.toAdd (Y (Subgroup.inclusion h.W_le_N w))) 0 := rfl

theorem act_eq_smul [Finite G] [CharP F 2] {b : G} (hb : b ∈ borelL T L) (x : Fin 1 → F) :
    Semi516.act h.coord1 b (h.borel_le_normalizer_W hb) x =
      (ψ (autHom h.coord.le_normalizer ⟨b, (Subgroup.mem_inf.mp hb).1⟩) :
        Matrix (Fin 2) (Fin 2) F) 0 0 • x := by
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hb).1
  have hbS : b ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hb).2
  rw [Semi516.act, Semi516.coordPerm_apply]
  obtain ⟨w, hw⟩ : ∃ w, w = h.coord1.symm (Multiplicative.ofAdd x) := ⟨_, rfl⟩
  rw [← hw]
  have hx0 : (Multiplicative.toAdd (Y (Subgroup.inclusion h.W_le_N w))) 0 = x 0 := by
    have h1 : Multiplicative.toAdd (h.coord1 w) = x := by
      rw [hw, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have := congrFun h1 0
    rwa [toAdd_coord1] at this
  have hconj : Subgroup.inclusion h.W_le_N (conjAct h.W ⟨b, h.borel_le_normalizer_W hb⟩ w) =
      ((autHom h.coord.le_normalizer ⟨b, hbL⟩ : ↥(autOn L N)) : MulAut ↥N)
        (Subgroup.inclusion h.W_le_N w) := by
    apply Subtype.ext
    rw [autHom_apply_coe]
    exact conjAct_apply_coe _ _
  have hl := h.coord.toAdd_Y_line hbL hbS (Subgroup.inclusion h.W_le_N w)
    (h.snd_eq_zero _ (h.W_le_P w.2).2)
  rw [toAdd_coord1, hconj, hl]
  funext i
  rw [Fin.fin_one_eq_zero i]
  simp only [Pi.smul_apply, smul_eq_mul, hx0]

theorem hyp [Finite G] [CharP F 2] : Semi516.Hyp h.coord1 T (borelL T L) D where
  one_le := le_rfl
  isPGroup := h.setting.isPGroup
  odd := h.setting.hall.2.1
  le_T := h.W_le_N.trans h.N_le_T
  T_le := h.T_le_normalizer_W
  B_le := h.borel_le_normalizer_W
  T_le_B := h.T_le_normalizer_borel
  D_le := h.D_le_borel
  decomp := fun _ hx => h.decomp hx
  scalar := fun _ hb => ⟨_, h.act_eq_smul hb⟩
  surj := fun c hc => by
    obtain ⟨δ, hδ, hδc⟩ := h.coord.exists_mem_D h.inf_centralizer_le h.setting.sylow
      h.setting.hall hc
    refine ⟨δ, hδ, fun x => ?_⟩
    rw [h.act_eq_smul (h.D_le_borel hδ), ← hδc]
  linear := fun t ht hlin => by
    obtain ⟨k, hk⟩ := h.setting.isPGroup ⟨t, ht⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Semi516.mem_centralizer_of_linear_line h.coord1 (h.T_le_normalizer_W ht) htk hlin
  faithful := by
    rw [eq_bot_iff]
    intro δ hδ
    obtain ⟨hδD, hδC⟩ := Subgroup.mem_inf.mp hδ
    rw [Subgroup.mem_bot]
    have hδB := h.D_le_borel hδD
    have hδL : δ ∈ L := (Subgroup.mem_inf.mp hδB).1
    have hδS : δ ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hδB).2
    have h1 : Semi516.act h.coord1 δ (h.borel_le_normalizer_W hδB) = 1 :=
      (Semi516.act_eq_one_iff _ _).mpr hδC
    have h00 : (ψ (autHom h.coord.le_normalizer ⟨δ, hδL⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
      have h2 := h.act_eq_smul hδB (fun _ => 1)
      rw [h1, Equiv.Perm.one_apply] at h2
      have h3 := congrFun h2 0
      simp only [Pi.smul_apply, smul_eq_mul, mul_one] at h3
      exact h3.symm
    have hu := eq_unipSL_of_upper (h.coord.upper hδL hδS) h00
    have hmem : ((autHom h.coord.le_normalizer ⟨δ, hδL⟩ : ↥(autOn L N)) : MulAut ↥N) ∈
        autOn (T ⊓ L) N := (h.coord.sylow _).mpr ⟨_, hu⟩
    have hδT : δ ∈ T := mem_of_conjAct_mem_autOn h.inf_centralizer_le
      ⟨δ, h.coord.le_normalizer hδL⟩ (Subgroup.mem_sup_left hδL) hmem
    exact eq_one_of_mem_of_odd h.setting.hall.2.1 h.setting.isPGroup hδD hδT

theorem le_four [Finite G] [CharP F 2] (hW : IsElemAbelian 2 h.W)
    (hq : qhatInt (T ⊔ D) h.W hW ≤ 2) : n ≤ 4 := by
  have hF0 : Nat.card F ≠ 0 := by
    rw [h.card]
    positivity
  have : Finite F := Nat.finite_of_card_ne_zero hF0
  by_contra hn
  push Not at hn
  have hcard : Nat.card h.W = 2 ^ n := by
    rw [Nat.card_congr h.coord1.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_pi]
    simp [h.card]
  have h16 : 16 < Nat.card h.W := by
    rw [hcard]
    calc 16 < 2 ^ 5 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact absurd hq (not_le.mpr (h.hyp.two_lt_qhatInt hW h16))

end QuotCtx

end CFSG.Quasithin.H13
