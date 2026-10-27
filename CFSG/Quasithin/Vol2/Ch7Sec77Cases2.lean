module

public import CFSG.Quasithin.Vol2.Ch7Sec77Cases1
public import CFSG.Quasithin.Vol2.Ch7Sec77ParWeyl
public import CFSG.Quasithin.EmptyFaithful.SBc17Norm

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem coprime_six_of_odd {n : ℕ} (hn : Odd n) : Nat.Coprime (2 ^ n - 1) 6 := by
  obtain ⟨m, rfl⟩ := hn
  have hx : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hx1 : 1 ≤ 4 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have e : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by rw [pow_succ, pow_mul]; ring
  rw [e, show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
  constructor
  · rw [Nat.coprime_two_right, Nat.odd_iff]
    omega
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_c27SL3_odd (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (h36 : A36ForSQTK) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L) {n : ℕ} {F : Type} [Field F] [Fintype F]
    (hFc : Fintype.card F = 2 ^ n) (hn : Odd n) (hn3 : 3 ≤ n)
    (eF : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hP : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
      (fsuV T I : Set G))))) (autOn (fsuM T L ⊓ H ⊓ K) (omegaOneCenterOf (pCoreOf 2
      (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hQN := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨h1a, h1b, -⟩, -, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  obtain ⟨ys, hysP, ws, hwsX, hord, hwsP, hwy⟩ :=
    sl3ParabolicWeylFact_holds (MulAut ↥V') _ _ F n hFc (by omega) ⟨eF⟩ hP
  obtain ⟨gy, hgyMK, hgys⟩ := Setup.mem_autOn_iff.mp hysP
  obtain ⟨gw, hgwK, hgws⟩ := Setup.mem_autOn_iff.mp hwsX
  set y : G := (gy : G) with hydef
  set w : G := (gw : G) with hwdef
  have hyK : y ∈ K := hgyMK.2
  have hyM : y ∈ fsuM T L := hgyMK.1.1
  obtain ⟨a, ha⟩ := CFSG.Quasithin.H.BlkW.exists_odd_pow y
  set u : G := y ^ 2 ^ a with hudef
  have huK : u ∈ K := K.pow_mem hyK _
  have huM : u ∈ fsuM T L := (fsuM T L).pow_mem hyM _
  have huN : u ∈ Subgroup.normalizer (V' : Set G) := Subgroup.pow_mem _ gy.2 _
  have hus : conjAct V' ⟨u, huN⟩ = ys ^ 2 ^ a := by
    rw [← hgys, ← map_pow]
    rfl
  set Y := Subgroup.zpowers u with hYdef
  have hYM : Y ≤ fsuM T L := (Subgroup.zpowers_le).mpr huM
  have hYo : Odd (Nat.card Y) := by rw [hYdef, Nat.card_zpowers]; exact ha
  have hu0 : u ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G) := by
    have h1 := C.conf.hHG (hKH huK)
    rwa [C.hVp] at h1
  have hYz : Y ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    (Subgroup.zpowers_le).mpr (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)) hu0)
  have hidx := S.relIndex_le_three hYM hYo (vec_mem a1) vec_a1_ne_one hYz
  have hu6 : u ^ 6 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    set B := (Y ⊓ Subgroup.centralizer (fsuV T I : Set G)).subgroupOf Y with hB
    have hBn : B.Normal := by
      have : IsMulCommutative ↥Y := isMulCommutative_zpowers u
      exact Subgroup.normal_of_isMulCommutative B
    have h1 := Subgroup.pow_index_mem B (⟨u, Subgroup.mem_zpowers u⟩ : ↥Y)
    have hi : B.index ∣ 6 := by
      have h2 : B.index = (Y ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex Y := rfl
      have h3 : B.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      rw [h2] at h3 ⊢
      interval_cases hm : (Y ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex Y
      · exact absurd rfl h3
      · norm_num
      · exfalso
        have h4 := Subgroup.relIndex_dvd_card (H := Y ⊓ Subgroup.centralizer (fsuV T I : Set G))
          (K := Y)
        rw [hm] at h4
        exact (Nat.not_even_iff_odd.mpr hYo) (even_iff_two_dvd.mpr h4)
      · norm_num
    obtain ⟨k, hk⟩ := hi
    have h5 : (⟨u, Subgroup.mem_zpowers u⟩ : ↥Y) ^ 6 ∈ B := by
      rw [hk, pow_mul]
      exact B.pow_mem h1 _
    exact (Subgroup.mem_subgroupOf.mp h5).2
  set v : G := u ^ 18 with hvdef
  have hvK : v ∈ K := K.pow_mem huK _
  have hvM : v ∈ fsuM T L := (fsuM T L).pow_mem huM _
  have hvV : v ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [hvdef, show (18 : ℕ) = 6 * 3 from rfl, pow_mul]
    exact Subgroup.pow_mem _ hu6 _
  have hvo : Odd (orderOf v) := Odd.of_dvd_nat ha (orderOf_pow_dvd 18)
  have hco : Nat.Coprime (orderOf ys) (18 * 2 ^ a) := by
    rw [hord]
    have h6 := coprime_six_of_odd hn
    have h18 : Nat.Coprime (2 ^ n - 1) 18 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : (18 : ℕ) ∣ 6 * 6 * 6)
        ((h6.mul_right h6).mul_right h6)
    exact h18.mul_right (Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_right
      (by norm_num : (2 : ℕ) ∣ 6) h6))
  have hvs : conjAct V' ⟨v, Subgroup.pow_mem _ huN _⟩ = ys ^ (18 * 2 ^ a) := by
    have e1 : (⟨v, Subgroup.pow_mem _ huN _⟩ : ↥(Subgroup.normalizer (V' : Set G))) =
        ⟨u, huN⟩ ^ 18 := rfl
    rw [e1, map_pow, hus, ← pow_mul, mul_comm]
  have hvs1 : conjAct V' ⟨v, Subgroup.pow_mem _ huN _⟩ ≠ 1 := by
    rw [hvs]
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf ys = 1 := Nat.Coprime.eq_one_of_dvd hco h1
    rw [hord] at h2
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  have hv1 : v ≠ 1 := by
    intro h
    apply hvs1
    have e1 : (⟨v, Subgroup.pow_mem _ huN _⟩ : ↥(Subgroup.normalizer (V' : Set G))) = 1 :=
      Subtype.ext h
    rw [e1, map_one]
  have hB1 : Subgroup.zpowers v ≠ ⊥ := by
    intro h
    apply hv1
    have h' := Subgroup.mem_zpowers v
    rw [h, Subgroup.mem_bot] at h'
    exact h'
  have hN := S.normalizer_le h443 ((Subgroup.zpowers_le).mpr hvM) ((Subgroup.zpowers_le).mpr hvV)
    hB1 (isMulCommutative_zpowers v) (by rw [Nat.card_zpowers]; exact hvo)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hwy
  have hwK : w ∈ K := hgwK
  have hwN : w ∈ Subgroup.normalizer (V' : Set G) := gw.2
  set c₁ : G := w * u * w⁻¹ * (u ^ (i : ℤ))⁻¹ with hc₁
  have hc₁K : c₁ ∈ K := K.mul_mem (K.mul_mem (K.mul_mem hwK huK) (K.inv_mem hwK))
    (K.inv_mem (K.zpow_mem huK _))
  have hc₁N : c₁ ∈ Subgroup.normalizer (V' : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hwN huN) (Subgroup.inv_mem _ hwN))
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ huN _))
  have hc₁V : c₁ ∈ Subgroup.centralizer (V' : Set G) := by
    refine (Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G)) le_rfl ⟨c₁, hc₁N⟩).mp ?_
    have e1 : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer (V' : Set G))) =
        gw * ⟨u, huN⟩ * gw⁻¹ * (⟨u, huN⟩ ^ (i : ℤ))⁻¹ := rfl
    change conjAct V' ⟨c₁, hc₁N⟩ = 1
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow, hgws, hus]
    have h2 : ws * ys ^ 2 ^ a * ws⁻¹ = (ys ^ i) ^ 2 ^ a := by rw [hi, conj_pow]
    rw [h2]
    group
  have hc₁Z : c₁ ∈ oTwoZIn K := inf_centralizer_le_oTwoZIn_of_c27 h1b ⟨hc₁K, hc₁V⟩
  have hc₁3 : c₁ ^ 3 ∈ pCoreOf 2 K := by
    have hHs : SQTKGroup ↥H := C.hypC23.sqtk
    exact pow_three_mem_of_central hHs (h36 _ (SQTKHyp.of_sqtkGroup ↥H hHs)) hK hKq hc₁K
      (fun z hz => by
        rw [commutatorElement_def]
        exact commutator_mem_of_mem_oTwoZIn hc₁Z hz)
  have hwv : w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹ ∈ pCoreOf 2 K := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
    have hmemK : w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹ ∈ K := K.mul_mem (K.mul_mem (K.mul_mem hwK hvK)
      (K.inv_mem hwK)) (K.inv_mem (K.zpow_mem hvK _))
    have hcen : π ⟨c₁, hc₁K⟩ ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      refine Subgroup.mem_center_iff.mpr fun x => ?_
      obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) x
      have h1 := commutator_mem_of_mem_oTwoZIn hc₁Z k.2
      have h2 : (k * ⟨c₁, hc₁K⟩ * k⁻¹ * (⟨c₁, hc₁K⟩ : ↥K)⁻¹ : ↥K) ∈ CFSG.pCore 2 ↥K := by
        obtain ⟨x', hx', hxx'⟩ := h1
        have e2 : x' = k * ⟨c₁, hc₁K⟩ * k⁻¹ * (⟨c₁, hc₁K⟩ : ↥K)⁻¹ := Subtype.ext hxx'
        rw [← e2]
        exact hx'
      have h3 : π (k * ⟨c₁, hc₁K⟩ * k⁻¹ * (⟨c₁, hc₁K⟩ : ↥K)⁻¹) = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h2
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
      calc π k * π ⟨c₁, hc₁K⟩
          = (π k * π ⟨c₁, hc₁K⟩ * (π k)⁻¹ * (π ⟨c₁, hc₁K⟩)⁻¹) * (π ⟨c₁, hc₁K⟩ * π k) := by
            group
        _ = π ⟨c₁, hc₁K⟩ * π k := by rw [h3, one_mul]
    have hc3 : π ⟨c₁, hc₁K⟩ ^ 3 = 1 := by
      rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨x', hx', hxx'⟩ := hc₁3
      have e2 : x' = (⟨c₁, hc₁K⟩ : ↥K) ^ 3 :=
        Subtype.ext (by rw [show (x' : G) = c₁ ^ 3 from hxx']; simp)
      rw [← e2]
      exact hx'
    have hwu : (⟨w * u * w⁻¹, K.mul_mem (K.mul_mem hwK huK) (K.inv_mem hwK)⟩ : ↥K) =
        ⟨c₁, hc₁K⟩ * ⟨u, huK⟩ ^ (i : ℤ) := by
      apply Subtype.ext
      simp [hc₁]
    have hwv' : (⟨w * v * w⁻¹, K.mul_mem (K.mul_mem hwK hvK) (K.inv_mem hwK)⟩ : ↥K) =
        (⟨w * u * w⁻¹, K.mul_mem (K.mul_mem hwK huK) (K.inv_mem hwK)⟩ : ↥K) ^ 18 := by
      apply Subtype.ext
      simp [hvdef, conj_pow]
    have h1 : π (⟨w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹, hmemK⟩ : ↥K) = 1 := by
      have e2 : (⟨w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹, hmemK⟩ : ↥K) =
          ⟨w * v * w⁻¹, K.mul_mem (K.mul_mem hwK hvK) (K.inv_mem hwK)⟩ *
            (⟨v, hvK⟩ ^ (i : ℤ))⁻¹ := rfl
      have e3 : (⟨v, hvK⟩ : ↥K) = ⟨u, huK⟩ ^ 18 := rfl
      rw [e2, map_mul, map_inv, hwv', hwu, e3, map_pow, map_mul, map_zpow, map_zpow, map_pow]
      have hcomm : Commute (π ⟨c₁, hc₁K⟩) (π ⟨u, huK⟩ ^ (i : ℤ)) :=
        (Subgroup.mem_center_iff.mp hcen _).symm
      rw [hcomm.mul_pow, show (18 : ℕ) = 3 * 6 from rfl, pow_mul (π ⟨c₁, hc₁K⟩), hc3, one_pow,
        one_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (i : ℤ),
        mul_inv_cancel]
    have h2 : (⟨w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹, hmemK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1
    exact coe_mem_pCoreOf h2
  obtain ⟨o, ho, how⟩ := exists_mem_normalizer_of_conj_le (A := Subgroup.zpowers v) (g := w)
    (by rw [Nat.card_zpowers]; exact hvo) (pCoreOf_isPGroup 2 K)
    ((Subgroup.zpowers_le).mpr (le_normalizer_pCoreOf 2 K hvK)) (le_normalizer_pCoreOf 2 K hwK)
    (by
      intro b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have e2 : w * v ^ j * w⁻¹ = ((w * v * w⁻¹ * (v ^ (i : ℤ))⁻¹) * v ^ (i : ℤ)) ^ j := by
        rw [← conj_zpow]
        group
      rw [e2]
      exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hwv)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) _))) _)
  have hwM : w ∈ fsuM T L := by
    have h1 : o * w ∈ fsuM T L := hN how
    have h2 : o⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (C.pCoreOf_le_fsuM hK ho)
    have h3 := (fsuM T L).mul_mem h2 h1
    simpa using h3
  exact hwsP (Setup.mem_autOn_iff.mpr ⟨gw, ⟨⟨hwM, hKH hwK⟩, hwK⟩, hgws⟩)

theorem c27SL3_card_two (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (h36 : A36ForSQTK) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L)
    (h : C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
      Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
        (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) := by
  obtain ⟨⟨n, F, hFf, hFt, hn1, hFc, ⟨eF⟩⟩, hP, -⟩ := h
  rcases Nat.even_or_odd n with hev | hod
  · exact (C.false_of_c27SL3_even hC27 h443 hC24a hC24b hF hK hKq hKM hFc hev eF hP.1).elim
  · by_cases h3 : 3 ≤ n
    · exact (C.false_of_c27SL3_odd hC27 h443 hC24a hC24b h36 hF hK hKq hKM hFc hod h3 eF hP).elim
    · have hn : n = 1 := by
        obtain ⟨m, rfl⟩ := hod
        omega
      subst hn
      exact ⟨F, hFf, hFt, by simpa using hFc, ⟨eF⟩⟩

theorem c27Cases_rest2 (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (h36 : A36ForSQTK) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L) :
    C27A7a H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27A7b H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27ExcA7 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27A6Sp4 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27G2 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      (C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
          (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
          Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
            (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∨
      C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) := by
  rcases C.c27Cases_rest hC27 h443 hC24a hC24b hF hK hKq hKM with
    h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact (C.false_of_c27Alt hC27 h443 hC24a hC24b hF hK hKq hKM h).elim
  · exact (C.false_of_c27Hat6 h443 hC24a hF hK hKq hKM h).elim
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h, C.c27SL3_card_two hC27 h443 hC24a hC24b h36 hF hK hKq hKM h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
