module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OrthFix
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Sub
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516R
public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL diagSL coe_diagSL diagSL_conj
  unipSL_mul_self)

variable {G : Type} [Group G]

@[expose] def xFiveCh6 (T L : Subgroup G) : Subgroup G :=
  Subgroup.closure
    {x | x ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧ orderOf x = 5}

theorem xFiveCh6_le (T L : Subgroup G) :
    xFiveCh6 T L ≤ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem xFiveCh6_eq_oTwoUpper (T L : Subgroup G) : xFiveCh6 T L = oTwoUpper (xFiveCh6 T L) := by
  refine le_antisymm ?_ (oTwoUpper_le _)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) (by rw [hx.2]; decide)

theorem mem_normalizer_inf_ch6 {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hA y, hB y]

theorem le_normalizer_xFiveCh6 {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ≤ Subgroup.normalizer (xFiveCh6 T L : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ xFiveCh6 T L, t * x * t⁻¹ ∈ xFiveCh6 T L := by
    intro t ht x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      obtain ⟨⟨hyL, hyN⟩, hy5⟩ := hy
      have htN : t ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
        mem_normalizer_inf_ch6 (Subgroup.le_normalizer ht) (hTL ht)
      refine ⟨⟨(Subgroup.mem_normalizer_iff.mp (hTL ht) y).mp hyL,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hyN) (Subgroup.inv_mem _ htN)⟩, ?_⟩
      have := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective y
      rw [← hy5, ← this]
      rfl
    | one => simp
    | mul a b _ _ iha ihb =>
      have := Subgroup.mul_mem _ iha ihb
      simpa [mul_assoc] using this
    | inv a _ iha =>
      have := Subgroup.inv_mem _ iha
      simpa [mul_assoc] using this
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have := key t⁻¹ (T.inv_mem ht) _ hx
  simpa [mul_assoc] using this

theorem conjAct_eq_one_iff_ch6 {W : Subgroup G} (g : ↥(Subgroup.normalizer (W : Set G))) :
    conjAct W g = 1 ↔ (g : G) ∈ Subgroup.centralizer (W : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

variable [Finite G] {T M L V : Subgroup G}

namespace Hyp611

theorem isSylowTwoOf_inf_ch6 (h : Hyp611 G T M L V 4) : IsSylowTwoOf (T ⊓ L) L :=
  A4.isSylowTwoOf_inf_normal (h.toHyp5_0_1.isSylowTwoOf le_sup_right) le_sup_left
    h.toHyp5_0_1.sup_le_normalizer

theorem sup_inf_centralizer_le_T_ch6 (h : Hyp611 G T M L V 4) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
  (h.toHyp5_0_1.sup_inf_centralizer_le_pCoreOf h.sup_le_normalizer h.module.2.2).trans
    (by rw [← h.centralizer_eq]; exact inf_le_left)

theorem omega_le_of_omegaOne_le_ch6 (h : Hyp611 G T M L V 4)
    (hVΩ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ V) : quasithinOmegaOneCenter T ≤ V := by
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := by rw [← h.centralizer_eq]; exact inf_le_left
  have hc := h.toHyp5_0_1.charTwo_sup
  have hZ : centerOf T ≤ centerOf (pCoreOf 2 (L ⊔ T)) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
      Subgroup.centralizer_le hQT hx.2
    exact ⟨hc ⟨(le_sup_right : T ≤ L ⊔ T) hx.1, hxC⟩, hxC⟩
  refine le_trans ?_ hVΩ
  exact Subgroup.closure_mono fun x hx => ⟨hZ hx.1, hx.2⟩

theorem xFiveCh6_le_centralizer_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    (hVΩ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) ≤ V) :
    xFiveCh6 T L ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hS := h.isSylowTwoOf_inf_ch6
  have hZV := h.omega_le_of_omegaOne_le_ch6 hVΩ
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun z hz => Subgroup.centralizer_le inf_le_left
      ((quasithinOmegaOneCenter_le_inf T).trans inf_le_right hz)
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hDm : Subgroup.zpowers x ≤ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hx.1
  have hcard : Nat.card (Subgroup.zpowers x) = 2 ^ 2 + 1 := by
    rw [Nat.card_zpowers, hx.2]; norm_num
  have hk := orthKernelFact G L V (T ⊓ L) (Subgroup.zpowers x) 2
    (show IsOrthCh5 L V (2 * 2) from horth) hS hDm hcard
  show x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (hk ⟨hZV hz, hZC hz⟩) x
    (Subgroup.mem_zpowers x)).symm

theorem coe_diagSL_pow_ch6 {F : Type} [Field F] {μ : F} (hμ : μ ≠ 0) (k : ℕ) :
    (((diagSL hμ) ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![μ ^ k, 0; 0, μ⁻¹ ^ k] := by
  induction k with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_diagSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem exists_delta_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ (2 * 2) ∧
      ∃ δ : ↥L →* SL(2, F), Function.Surjective δ ∧
        (∀ ℓ : ↥L, δ ℓ = 1 ↔ (ℓ : G) ∈ Subgroup.centralizer (V : Set G)) ∧
        (∀ ℓ : ↥L, (∃ b : F, δ ℓ = unipSL b) ↔ (ℓ : G) ∈ T) ∧
        (∀ ℓ : ↥L, (ℓ : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) →
          (δ ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) := by
  have hS := h.isSylowTwoOf_inf_ch6
  have hLV := h.L_le_normalizer
  have hC := h.sup_inf_centralizer_le_T_ch6
  obtain ⟨F, _, _, _, hF, ψ, Y, -, -, -, -, hP⟩ :=
    (show IsOrthCh5 L V (2 * 2) from horth).exists_sylowCoord hS
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF,
    ψ.toMonoidHom.comp (autHom hLV), ?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨ℓN, hℓL, hℓ⟩ := mem_autOn_iff.mp (ψ.symm g).2
    refine ⟨⟨ℓN, hℓL⟩, ?_⟩
    show ψ (autHom hLV ⟨ℓN, hℓL⟩) = g
    have : autHom hLV ⟨ℓN, hℓL⟩ = ψ.symm g := Subtype.ext hℓ
    rw [this, MulEquiv.apply_symm_apply]
  · intro ℓ
    constructor
    · intro h1
      apply mem_centralizer_of_autHom_eq_one hLV
      exact ψ.injective (by rw [map_one]; exact h1)
    · intro h1
      show ψ (autHom hLV ℓ) = 1
      have : autHom hLV ℓ = 1 := by
        apply Subtype.ext
        exact (conjAct_eq_one_iff_ch6 (W := V) ⟨(ℓ : G), hLV ℓ.2⟩).mpr h1
      rw [this, map_one]
  · intro ℓ
    constructor
    · rintro ⟨b, hb⟩
      have hmem : ((autHom hLV ℓ : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V :=
        (hP _).mpr ⟨b, hb⟩
      exact mem_of_conjAct_mem_autOn hC ⟨ℓ, hLV ℓ.2⟩ ((le_sup_left : L ≤ L ⊔ T) ℓ.2) hmem
    · intro hℓT
      exact (hP _).mp (mem_autOn_iff.mpr ⟨⟨ℓ, hLV ℓ.2⟩, ⟨hℓT, ℓ.2⟩, rfl⟩)
  · intro ℓ hℓN
    exact upper_of_mem_normalizer ψ hP (autHom hLV ℓ) (by
      have := conjAct_mem_normalizer_autOn (K := T ⊓ L) (W := V) ⟨(ℓ : G), hLV ℓ.2⟩ hℓN
      exact this)

theorem exists_orderOf_five_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) :
    ∃ x : G, x ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ∧ orderOf x = 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, hF, δ, hδs, hδk, hδT, -⟩ := h.exists_delta_ch6 horth
  have hFu : Nat.card Fˣ = 15 := by rw [Nat.card_units, hF]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 5 (by rw [hFu]; norm_num)
  set ζ : F := (u : F) with hζ
  have hζ0 : ζ ≠ 0 := u.ne_zero
  have hζ5 : ζ ^ 5 = 1 := by
    rw [hζ, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hζk : ∀ k : ℕ, ζ ^ 2 ^ k ≠ 1 := by
    intro k hk
    have h1 : u ^ 2 ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk)
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at hdvd
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hdvd)
    omega
  obtain ⟨ℓ, hℓ⟩ := hδs (diagSL hζ0)
  have hconj : ∀ (m : ↥L) (μ : F) (hμ : μ ≠ 0), δ m = diagSL hμ →
      ∀ t ∈ T ⊓ L, (m : G) * t * (m : G)⁻¹ ∈ T ⊓ L := by
    intro m μ hμ hm t ht
    have hmt : (m : G) * t * (m : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem m.2 ht.2) (L.inv_mem m.2)
    refine ⟨?_, hmt⟩
    obtain ⟨b, hb⟩ := (hδT ⟨t, ht.2⟩).mpr ht.1
    have e : δ ⟨_, hmt⟩ = unipSL (μ ^ 2 * b) := by
      have : (⟨(m : G) * t * (m : G)⁻¹, hmt⟩ : ↥L) = m * ⟨t, ht.2⟩ * m⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hm, hb, diagSL_conj]
    exact (hδT ⟨_, hmt⟩).mp ⟨_, e⟩
  have hℓN : (ℓ : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem (hconj ℓ ζ hζ0 hℓ)
  have hℓ5 : δ (ℓ ^ 5) = 1 := by
    rw [map_pow, hℓ]
    apply Subtype.ext
    rw [coe_diagSL_pow_ch6, hζ5, inv_pow, hζ5, inv_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hℓ5O : ((ℓ ^ 5 : ↥L) : G) ∈ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le h.L_le_normalizer h.module.2.2
      ⟨(ℓ ^ 5).2, (hδk _).mp hℓ5⟩
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hℓ5O⟩
  have hk' : ((ℓ : G) ^ 5) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨(ℓ : G) ^ 2 ^ k, ⟨L.pow_mem ℓ.2 _, Subgroup.pow_mem _ hℓN _⟩, ?_⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, mul_comm, pow_mul]; exact hk'
  · intro h1
    have h2 : δ (ℓ ^ 2 ^ k) = 1 := by
      have : ℓ ^ 2 ^ k = 1 := Subtype.ext (by simpa using h1)
      rw [this, map_one]
    rw [map_pow, hℓ] at h2
    have h3 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h2
    simp only [coe_diagSL_pow_ch6] at h3
    exact hζk k (by simpa using h3)

theorem relIndex_xFiveCh6_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4) :
    (xFiveCh6 T L ⊓ T).relIndex (xFiveCh6 T L) = 5 ∧
      ((xFiveCh6 T L ⊓ T).subgroupOf (xFiveCh6 T L)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, hF, δ, -, -, hδT, hδN⟩ := h.exists_delta_ch6 horth
  set X := xFiveCh6 T L with hXdef
  have hXL : X ≤ L := (xFiveCh6_le T L).trans inf_le_left
  let B5 : Subgroup ↥L :=
    { carrier := {ℓ | (δ ℓ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (δ ℓ : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 5 = 1}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨e1, e2⟩ := upper_mul ha.1 hb.1
        refine ⟨by rw [map_mul]; exact e1, by rw [map_mul, e2, mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        obtain ⟨e1, e2⟩ := upper_inv ha.1
        have hd := upper_det ha.1
        refine ⟨by rw [map_inv]; exact e1, ?_⟩
        rw [map_inv, e2]
        have h1 : ((δ a : Matrix (Fin 2) (Fin 2) F) 0 0 *
            (δ a : Matrix (Fin 2) (Fin 2) F) 1 1) ^ 5 = 1 := by rw [hd, one_pow]
        rw [mul_pow, ha.2, one_mul] at h1
        exact h1 }
  have hXB : ∀ x : G, ∀ hx : x ∈ X, (⟨x, hXL hx⟩ : ↥L) ∈ B5 := by
    have hle : X ≤ B5.map L.subtype := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      have hx5 : x ^ 5 = 1 := hx.2 ▸ pow_orderOf_eq_one x
      refine ⟨⟨x, hx.1.1⟩, ⟨hδN ⟨x, hx.1.1⟩ hx.1.2, ?_⟩, rfl⟩
      have h5 : δ ⟨x, hx.1.1⟩ ^ 5 = 1 := by
        rw [← map_pow]
        have : (⟨x, hx.1.1⟩ : ↥L) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
        rw [this, map_one]
      have := (upper_pow (hδN ⟨x, hx.1.1⟩ hx.1.2) 5).2
      rw [h5] at this
      simpa using this.symm
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hle hx
    have : y = ⟨x, hXL hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hne : ∀ x : ↥X, (δ ⟨x, hXL x.2⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro x h0
    have := (hXB x x.2).2
    rw [h0, zero_pow (by norm_num)] at this
    exact zero_ne_one this
  let ε : ↥X →* Fˣ :=
    { toFun := fun x => Units.mk0 _ (hne x)
      map_one' := by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_one]
        have : (⟨((1 : ↥X) : G), hXL (1 : ↥X).2⟩ : ↥L) = 1 := rfl
        rw [this, map_one]
        rfl
      map_mul' := fun x y => by
        apply Units.ext
        simp only [Units.val_mk0, Units.val_mul]
        have : (⟨((x * y : ↥X) : G), hXL (x * y).2⟩ : ↥L) =
            ⟨x, hXL x.2⟩ * ⟨y, hXL y.2⟩ := rfl
        rw [this, map_mul]
        exact (upper_mul (hXB x x.2).1 (hXB y y.2).1).2 }
  have hεv : ∀ x : ↥X, ((ε x : Fˣ) : F) = (δ ⟨x, hXL x.2⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    fun x => rfl
  have hker : ε.ker = (X ⊓ T).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx
      have h1 : (δ ⟨x, hXL x.2⟩ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
        rw [← hεv, hx, Units.val_one]
      refine ⟨x.2, (hδT ⟨x, hXL x.2⟩).mp ⟨_, eq_unipSL_of_upper (hXB x x.2).1 h1⟩⟩
    · rintro ⟨-, hxT⟩
      obtain ⟨b, hb⟩ := (hδT ⟨x, hXL x.2⟩).mpr hxT
      apply Units.ext
      rw [hεv, hb, Units.val_one]
      simp [coe_unipSL]
  obtain ⟨x₀, hx₀, hx₀5⟩ := h.exists_orderOf_five_ch6 horth
  have hx₀X : x₀ ∈ X := Subgroup.subset_closure ⟨hx₀, hx₀5⟩
  have hε₀ : ε ⟨x₀, hx₀X⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨x₀, hx₀X⟩ : ↥X) ∈ (X ⊓ T).subgroupOf X := by
      rw [← hker]; exact h1
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨x₀, hmem.2⟩
    have hk' : x₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd := orderOf_dvd_of_pow_eq_one hk'
    rw [hx₀5] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hdvd
    omega
  have h5R : IsPGroup 5 ε.range := by
    rintro ⟨u, x, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    apply Units.ext
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, Units.val_pow_eq_pow_val,
      hεv, Units.val_one]
    exact (hXB x x.2).2
  have hFu : Nat.card Fˣ = 15 := by rw [Nat.card_units, hF]; norm_num
  have hcard : Nat.card ε.range = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 5)).mp h5R
    have hdvd : Nat.card ε.range ∣ 15 := hFu ▸ Subgroup.card_subgroup_dvd_card ε.range
    rw [hj] at hdvd ⊢
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have : 5 ^ 2 ∣ 15 := (pow_dvd_pow 5 (by omega)).trans hdvd
      norm_num at this
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply hε₀
      have hR : ε.range = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hj, pow_zero])
      have : ε ⟨x₀, hx₀X⟩ ∈ ε.range := ⟨_, rfl⟩
      rw [hR, Subgroup.mem_bot] at this
      exact this
    have : j = 1 := by omega
    rw [this, pow_one]
  refine ⟨?_, ?_⟩
  · show ((X ⊓ T).subgroupOf X).index = 5
    rw [← hker, Subgroup.index_ker, hcard]
  · rw [← hker]
    exact MonoidHom.normal_ker ε

theorem ringAut_eq_one_of_fix_five_ch6 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * 2)) (σ : RingAut F) {c : F} (hc5 : c ^ 5 = 1) (hc1 : c ≠ 1)
    (hσc : σ c = c) : σ = 1 := by
  have := Fintype.ofFinite F
  obtain ⟨j, hj⟩ := exists_eq_pow_two_pow hF σ
  have h16 : ∀ x : F, x ^ 2 ^ 4 = x := fun x => by
    have : Fintype.card F = 2 ^ 4 := by rw [← Nat.card_eq_fintype_card, hF]
    rw [← this]
    exact FiniteField.pow_card x
  have hred : ∀ x : F, x ^ 2 ^ j = x ^ 2 ^ (j % 4) := by
    intro x
    have hj4 : j = 4 * (j / 4) + j % 4 := (Nat.div_add_mod j 4).symm
    conv_lhs => rw [hj4, pow_add, pow_mul]
    rw [iter_two_pow_eq_self (h16 x)]
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc5
  have hcr : c ^ 2 ^ (j % 4) = c := by rw [← hred, ← hj]; exact hσc
  have hr : j % 4 = 0 := by
    have hlt : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hm : j % 4
    · rfl
    · exfalso; apply hc1
      have : c * (c - 1) = 0 := by linear_combination hcr
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
    · exfalso; apply hc1
      have h2 : c ^ 2 = 1 := by linear_combination hc5 - c * hcr
      have h4 : c ^ 4 = 1 := by linear_combination (c ^ 2 + 1) * h2
      calc c = c ^ 2 ^ 2 := hcr.symm
        _ = c ^ 4 := by norm_num
        _ = 1 := h4
    · exfalso; apply hc1
      have h3 : c ^ 3 = c := by linear_combination hcr - c ^ 3 * hc5
      have h2 : c ^ 2 = 1 := by
        have : c * (c ^ 2 - 1) = 0 := by linear_combination h3
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0)
      linear_combination hc5 - (c ^ 3 + c) * h2
  ext x
  rw [hj, hred, hr, pow_zero, pow_one]
  rfl

theorem le_sup_of_orderOf_five_ch6 (h : Hyp611 G T M L V 4) (horth : IsOrthCh5 L V 4)
    {R : Subgroup G} {d : G} (hd : d ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hd5 : orderOf d = 5) (hRT : R ≤ T) (hdR : d ∈ Subgroup.normalizer (R : Set G)) :
    R ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G)) := by
  have hS := h.isSylowTwoOf_inf_ch6
  have hC := h.sup_inf_centralizer_le_T_ch6
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.L_le_normalizer
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := h.T_le_normalizer
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.toHyp5_0_1.T_le_normalizer
  have hT : IsPGroup 2 T := h.sylow.1
  have hV' : IsOrthCh5 L V (2 * 2) := horth
  obtain ⟨F, _, _, _, hF, ψ, Y, hYinj, -, hYsurj, -, hP, -, -⟩ := hV'.exists_lineCoord hS
  set xd := autHom hLV ⟨d, hd.1⟩ with hxd
  have hxdN : (xd : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    conjAct_mem_normalizer_autOn ⟨d, hLV hd.1⟩ hd.2
  have hxd10 := upper_of_mem_normalizer ψ hP xd hxdN
  set c := (ψ xd : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have h5 : ψ xd ^ 5 = 1 := by
    rw [hxd, ← map_pow, ← map_pow]
    have : (⟨d, hd.1⟩ : ↥L) ^ 5 = 1 := Subtype.ext (by
      simpa using (hd5 ▸ pow_orderOf_eq_one d : d ^ 5 = 1))
    rw [this, map_one, map_one]
  have hc5 : c ^ 5 = 1 := by
    have h2 := (upper_pow hxd10 5).2
    rw [h5] at h2
    simpa using h2.symm
  have hc1 : c ≠ 1 := by
    intro hc1
    have hU := eq_unipSL_of_upper hxd10 hc1
    have h2 : ψ xd * ψ xd = 1 := by rw [hU]; exact unipSL_mul_self _
    have h4 : ψ xd = 1 := by
      calc ψ xd = ψ xd ^ 5 * ((ψ xd * ψ xd) * (ψ xd * ψ xd))⁻¹ := by group
        _ = 1 := by rw [h5, h2]; group
    have h6 : xd = 1 := ψ.injective (h4.trans (map_one ψ).symm)
    have hdC := mem_centralizer_of_autHom_eq_one hLV h6
    have hdT : d ∈ T := hC ⟨(le_sup_left : L ≤ L ⊔ T) hd.1, hdC⟩
    obtain ⟨k, hk⟩ := hT ⟨d, hdT⟩
    have hk' : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hd5] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hdvd
    omega
  intro r hr
  have hrT := hRT hr
  set τ : Subgroup.normalizer ((autOn L V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    ⟨conjAct V ⟨r, hTV hrT⟩, conjAct_mem_normalizer_autOn ⟨r, hTV hrT⟩ (hTL hrT)⟩ with hτ
  have hτP : (τ : MulAut ↥V) ∈
      Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
    conjAct_mem_normalizer_autOn ⟨r, hTV hrT⟩
      (mem_normalizer_inf_ch6 (Subgroup.le_normalizer hrT) (hTL hrT))
  obtain ⟨hh0, σ, hh, hασ, hσN⟩ :=
    exists_upper_of_normalizes (n := 2 * 2) (by omega) hF ψ hP τ hτP
  have hrdL : r * d * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL hrT) d).mp hd.1
  have hrd : r * d * r⁻¹ * d⁻¹ ∈ T ⊓ L := by
    refine Subgroup.mem_inf.mpr ⟨hRT ?_, mul_mem hrdL (inv_mem (Subgroup.mem_inf.mp hd).1)⟩
    have h1 : d * r⁻¹ * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hdR r⁻¹).mp (inv_mem hr)
    have h2 := mul_mem hr h1
    have e : r * (d * r⁻¹ * d⁻¹) = r * d * r⁻¹ * d⁻¹ := by group
    rwa [e] at h2
  set xrd := autHom hLV ⟨r * d * r⁻¹, hrdL⟩ with hxrd
  have hxrd' : (xrd : MulAut ↥V) = (τ : MulAut ↥V) * xd * (τ : MulAut ↥V)⁻¹ := by
    rw [hxrd, hxd]
    change conjAct V ⟨r * d * r⁻¹, _⟩ = conjAct V ⟨r, hTV hrT⟩ * conjAct V ⟨d, _⟩ *
      (conjAct V ⟨r, hTV hrT⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hψrd : ψ xrd = hh0 * Matrix.SpecialLinearGroup.map σ.toRingHom (ψ xd) * hh0⁻¹ := by
    have : xrd = (autOn L V).normalizerMonoidHom τ xd := by
      apply Subtype.ext
      rw [hxrd', Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [this, hασ]
  obtain ⟨e1, e2⟩ := upper_conj_map σ hh hxd10
  rw [← hψrd] at e1 e2
  rw [← hc] at e2
  have hxeq : xrd * xd⁻¹ = autHom hLV ⟨r * d * r⁻¹ * d⁻¹, hrd.2⟩ := by
    rw [hxrd, hxd, ← map_inv, ← map_mul]
    rfl
  have hmem : ((xrd * xd⁻¹ : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V := by
    rw [hxeq]
    exact mem_autOn_iff.mpr ⟨⟨r * d * r⁻¹ * d⁻¹, hLV hrd.2⟩, hrd, rfl⟩
  obtain ⟨b, hb⟩ := (hP _).mp hmem
  rw [map_mul, map_inv] at hb
  obtain ⟨f1, f2⟩ := upper_inv hxd10
  obtain ⟨g1, g2⟩ := upper_mul e1 f1
  have h00 : ((ψ xrd * (ψ xd)⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    rw [hb]
    simp [coe_unipSL]
  rw [g2, e2, f2] at h00
  have hdet := upper_det hxd10
  rw [← hc] at hdet
  have hσc : σ c = c := by
    have hx11 : (ψ xd : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
    exact mul_right_cancel₀ hx11 (h00.trans hdet.symm)
  have hσ1 : σ = 1 := ringAut_eq_one_of_fix_five_ch6 hF σ hc5 hc1 hσc
  obtain ⟨k, hk⟩ := hT ⟨r, hrT⟩
  have hrk : (⟨r, hTV hrT⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hτk : τ ^ 2 ^ k = 1 := by
    apply Subtype.ext
    change (conjAct V ⟨r, hTV hrT⟩) ^ 2 ^ k = 1
    rw [← map_pow, hrk, map_one]
  set e := ψ.symm hh0 with he
  have hconj : ∀ y : ↥(autOn L V), (autOn L V).normalizerMonoidHom τ y = e * y * e⁻¹ := by
    intro y
    apply ψ.injective
    rw [hασ, hσ1, map_mul, map_mul, map_inv, he, MulEquiv.apply_symm_apply]
    congr 2
  set z : MulAut ↥V := ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V) with hz
  have hzc : ∀ y : ↥(autOn L V), z * (y : MulAut ↥V) = (y : MulAut ↥V) * z := by
    intro y
    have h1 := congrArg Subtype.val (hconj y)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hz]
    calc ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V) * (y : MulAut ↥V) =
        ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ *
          ((τ : MulAut ↥V) * (y : MulAut ↥V) * (τ : MulAut ↥V)⁻¹) * (τ : MulAut ↥V) := by group
      _ = ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (((e : ↥(autOn L V)) : MulAut ↥V) *
          (y : MulAut ↥V) * ((e : ↥(autOn L V)) : MulAut ↥V)⁻¹) * (τ : MulAut ↥V) := by
            rw [h1]
      _ = (y : MulAut ↥V) * (((e : ↥(autOn L V)) : MulAut ↥V)⁻¹ * (τ : MulAut ↥V)) := by group
  have hτN : (τ : MulAut ↥V) ^ 2 ^ k = 1 := congrArg Subtype.val hτk
  have hez : Commute ((e : ↥(autOn L V)) : MulAut ↥V) z := (hzc e).symm
  have hτez : (τ : MulAut ↥V) = ((e : ↥(autOn L V)) : MulAut ↥V) * z := by
    rw [hz]
    group
  have heN : ((e : ↥(autOn L V)) : MulAut ↥V) ^ 2 ^ k * z ^ 2 ^ k = 1 := by
    rw [← hez.mul_pow, ← hτez, hτN]
  have heN1 : e ^ 2 ^ k = 1 := by
    have hcent : ψ (e ^ 2 ^ k) ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, eq_inv_of_mul_eq_one_left heN]
      exact ((Commute.pow_left (hzc y) (2 ^ k)).inv_left).eq.symm
    exact ψ.injective ((eq_one_of_mem_center hcent).trans (map_one ψ).symm)
  have hzN : z ^ 2 ^ k = 1 := by
    have h1 : ((e : ↥(autOn L V)) : MulAut ↥V) ^ 2 ^ k = 1 := by
      rw [← Subgroup.coe_pow, heN1, Subgroup.coe_one]
    rw [h1, one_mul] at heN
    exact heN
  have hV1 : ∃ v : ↥V, v ≠ 1 := by
    obtain ⟨w, hw⟩ := hYsurj !![1, 0; 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, Matrix.transpose_apply])
    refine ⟨w, fun hw1 => ?_⟩
    rw [hw1, map_one, toAdd_one] at hw
    have := congrFun (congrFun hw 0) 0
    simp at this
  have hz1 : z = 1 := by
    let M : Subgroup ↥V :=
      { carrier := {v | z v = v}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_mul, ha, hb]
        one_mem' := map_one z
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rw [map_inv, ha] }
    have hQ : IsPGroup 2 (Subgroup.zpowers z) := by
      rintro ⟨g, hg⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzN, one_zpow]
    have htop : (⊤ : Subgroup ↥V) ≠ ⊥ := by
      obtain ⟨v₀, hv₀⟩ := hV1
      intro htb
      have : v₀ ∈ (⊥ : Subgroup ↥V) := htb ▸ Subgroup.mem_top v₀
      exact hv₀ (Subgroup.mem_bot.mp this)
    obtain ⟨v, -, hv1, hv⟩ := exists_fixed_of_two hQ (M := ⊤)
      (fun v _ => sq_eq_one_of_coord hYinj v) htop (fun _ _ _ _ => Subgroup.mem_top _)
    have hM : M ≠ ⊥ := by
      intro hbot
      have hvM : v ∈ M := hv z (Subgroup.mem_zpowers z)
      rw [hbot] at hvM
      exact hv1 (Subgroup.mem_bot.mp hvM)
    have hLM : ∀ x ∈ autOn L V, ∀ v ∈ M, x v ∈ M := by
      intro x hx v hv
      have hzx := hzc ⟨x, hx⟩
      have hv' : z v = v := hv
      show z (x v) = x v
      calc z (x v) = (z * x) v := rfl
        _ = (x * z) v := by rw [hzx]
        _ = x (z v) := rfl
        _ = x v := by rw [hv']
    have hMtop := hV'.eq_top_of_invariant hS M hM hLM
    refine MulEquiv.ext fun v => ?_
    have hvM : v ∈ M := by
      rw [hMtop]
      exact Subgroup.mem_top v
    rw [MulAut.one_apply]
    exact hvM
  have hτe : (τ : MulAut ↥V) = ((e : ↥(autOn L V)) : MulAut ↥V) := by
    rw [hτez, hz1, mul_one]
  have hhN : hh0 ^ 2 ^ k = 1 := by
    have := congrArg ψ heN1
    rw [map_pow, map_one, he, MulEquiv.apply_symm_apply] at this
    exact this
  have hh00 : (hh0 : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_pow_two_pow_eq_one (f := k)
    have := (upper_pow hh (2 ^ k)).2
    rw [hhN] at this
    simpa using this.symm
  have hU := eq_unipSL_of_upper hh hh00
  have heP : ((e : ↥(autOn L V)) : MulAut ↥V) ∈ autOn (T ⊓ L) V :=
    (hP e).mpr ⟨(hh0 : Matrix (Fin 2) (Fin 2) F) 0 1, by
      rw [he, MulEquiv.apply_symm_apply]
      exact hU⟩
  rw [← hτe] at heP
  obtain ⟨p, hp, hpτ⟩ := mem_autOn_iff.mp heP
  have hcent := inv_mul_mem_centralizer (p := p) (c := ⟨r, hTV hrT⟩) hpτ
  have hcent' : (p : G)⁻¹ * r ∈ Subgroup.centralizer (V : Set G) := by
    simpa using hcent
  have hpr : (p : G)⁻¹ * r ∈ T := mul_mem (inv_mem hp.1) hrT
  have hrp : r = (p : G) * ((p : G)⁻¹ * r) := by group
  rw [hrp]
  exact mul_mem ((le_sup_left : T ⊓ L ≤ (T ⊓ L) ⊔ (T ⊓ Subgroup.centralizer (V : Set G))) hp)
    ((le_sup_right : T ⊓ Subgroup.centralizer (V : Set G) ≤ _) ⟨hpr, hcent'⟩)

end Hyp611

end CFSG.Quasithin.H13
