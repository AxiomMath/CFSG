module

public import CFSG.Quasithin.H13.NQS1312E
public import CFSG.Quasithin.H13.NQS1312F

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

@[expose] def k2c : List ℕ := [62, 13, 12, 4, 39, 36]

theorem wordMat_k2 : wordMat [4, 3, 4, 3, 4, 4, 1, 3] = k2c := by decide +kernel

theorem k2c_spec : mul6 k2c (mul6 k2c k2c) = id6 ∧ (∃ v < 64, vapp k2c v ≠ v ∧ vapp k2c v < 64) ∧
    mul6 kc k2c = mul6 k2c kc ∧ vapp k2c 15 = 59 ∧ vapp k2c 52 = 15 := by
  decide +kernel

theorem vecOf_fiftynine : vecOf 59 = vecOf 15 + vecOf 52 := by
  rw [← vecOf_xor]
  exact congrArg vecOf (by decide)

noncomputable abbrev k2GL : GL (Fin 6) (ZMod 2) := rho6 (wordElem [4, 3, 4, 3, 4, 4, 1, 3])

theorem k2GL_mem_J6 : k2GL ∈ J6 := ⟨_, rfl⟩

theorem coe_k2GL : (k2GL : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat k2c := by
  rw [coe_rho6_wordElem, wordMat_k2]

theorem pow_three_eq_one_of_codes {κ : GL (Fin 6) (ZMod 2)} {f : List ℕ}
    (hf : (κ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat f) (h3 : mul6 f (mul6 f f) = id6)
    (hv : ∃ v < 64, vapp f v ≠ v ∧ vapp f v < 64) : κ ^ 3 = 1 ∧ κ ≠ 1 := by
  refine ⟨Units.ext ?_, fun h1 => ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_one, hf, pow_three, ← colMat_mul6, ← colMat_mul6, h3,
      colMat_id6]
  · obtain ⟨v, hv64, hvne, hvlt⟩ := hv
    have h2 := glLin_vecOf_of_coe hf v
    rw [h1, map_one] at h2
    exact hvne (vecOf_injective hvlt hv64 h2.symm)

theorem kGL_spec : kGL ^ 3 = 1 ∧ kGL ≠ 1 :=
  pow_three_eq_one_of_codes coe_kGL kc_order.1 ⟨1, by norm_num, by decide +kernel⟩

theorem k2GL_spec : k2GL ^ 3 = 1 ∧ k2GL ≠ 1 :=
  pow_three_eq_one_of_codes coe_k2GL k2c_spec.1 k2c_spec.2.1

theorem kGL_mul_k2GL : kGL * k2GL = k2GL * kGL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_kGL, coe_k2GL, ← colMat_mul6, ← colMat_mul6,
    k2c_spec.2.2.1]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_eq_pow_mod_three {M : Type*} [Monoid M] {κ : M} (h : κ ^ 3 = 1) (n : ℕ) :
    κ ^ n = κ ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h, one_pow, one_mul]

theorem mem_normalizer_of_map_le {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom ≤ X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

variable {V : Subgroup G} [IsElementaryAbelian 2 V] {Φ : Additive V ≃ₗ[ZMod 2] W6}

omit [Finite G] in
theorem mem_centralizer_of_tau {n : G} (hn : n ∈ normalizer (V : Set G))
    (h : tau Φ ⟨n, hn⟩ = 1) : n ∈ centralizer (V : Set G) :=
  tau_eq_one_iff.1 h

omit [Finite G] in
theorem exists_orderOf_three_tau {L : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G))) {κ : GL (Fin 6) (ZMod 2)}
    (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1) {l : G} (hl : l ∈ L) (hlκ : tau Φ ⟨l, hLV hl⟩ = κ) :
    ∃ (y : G) (hy : y ∈ L), orderOf y = 3 ∧ tau Φ ⟨y, hLV hy⟩ = κ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpow : ∀ (y : G) (hy : y ∈ L) (n : ℕ),
      tau Φ ⟨y ^ n, hLV (L.pow_mem hy n)⟩ = (tau Φ ⟨y, hLV hy⟩) ^ n := by
    intro y hy n
    rw [← map_pow]
    rfl
  have hl3C : l ^ 3 ∈ L ⊓ centralizer (V : Set G) := by
    refine ⟨L.pow_mem hl 3, mem_centralizer_of_tau (Φ := Φ) (hLV (L.pow_mem hl 3)) ?_⟩
    rw [hpow l hl, hlκ, hκ3]
  obtain ⟨a, ha⟩ := hCL ⟨l ^ 3, hl3C⟩
  have ha' : (l ^ 3) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hy₀3 : (l ^ 2 ^ a) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, ha']
  have hy₀L : l ^ 2 ^ a ∈ L := L.pow_mem hl _
  have hτy₀ : tau Φ ⟨l ^ 2 ^ a, hLV hy₀L⟩ = κ ^ (2 ^ a % 3) := by
    rw [hpow l hl, hlκ, pow_eq_pow_mod_three hκ3]
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by
    have h3 : ¬ 3 ∣ 2 ^ a := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    omega
  have hne : ∀ (y : G) (hy : y ∈ L), tau Φ ⟨y, hLV hy⟩ = κ → y ≠ 1 := by
    intro y hy hyκ h1
    apply hκ1
    rw [← hyκ]
    have : (⟨y, hLV hy⟩ : normalizer (V : Set G)) = 1 := Subtype.ext h1
    rw [this, map_one]
  rcases hmod with h | h
  · have hτ : tau Φ ⟨l ^ 2 ^ a, hLV hy₀L⟩ = κ := by rw [hτy₀, h, pow_one]
    exact ⟨_, hy₀L, orderOf_eq_prime hy₀3 (hne _ hy₀L hτ), hτ⟩
  · have hyL : (l ^ 2 ^ a) ^ 2 ∈ L := L.pow_mem hy₀L 2
    have hτ : tau Φ ⟨(l ^ 2 ^ a) ^ 2, hLV hyL⟩ = κ := by
      rw [hpow _ hy₀L, hτy₀, h, ← pow_mul]
      calc κ ^ (2 * 2) = κ ^ 3 * κ := by rw [← pow_succ]
        _ = κ := by rw [hκ3, one_mul]
    refine ⟨_, hyL, orderOf_eq_prime ?_ (hne _ hyL hτ), hτ⟩
    rw [← pow_mul, mul_comm, pow_mul, hy₀3, one_pow]

theorem exists_e9 {T L : Subgroup G} {z : G} (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hF : QTU3InternalFrame T L V z)
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j) :
    ∃ (k₁ : G) (hk₁ : k₁ ∈ L) (x : G) (hx : x ∈ L), orderOf k₁ = 3 ∧ orderOf x = 3 ∧
      x * k₁ = k₁ * x ∧ tau Φ ⟨k₁, hF.2.2.2.2.2.2.1 hk₁⟩ = kGL ∧
      tau Φ ⟨x, hF.2.2.2.2.2.2.1 hx⟩ = k2GL := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLV : L ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.1
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
    rw [(u3_internal_frame_kernel hLV hU3 hF).1]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨l₁, hl₁, hl₁τ⟩ := hΦLs kGL kGL_mem_J6
  obtain ⟨l₂, hl₂, hl₂τ⟩ := hΦLs k2GL k2GL_mem_J6
  obtain ⟨y₁, hy₁L, hy₁3, hy₁τ⟩ :=
    exists_orderOf_three_tau hLV hCL kGL_spec.1 kGL_spec.2 hl₁ (tau_eq_iff.2 hl₁τ)
  obtain ⟨y₂, hy₂L, hy₂3, hy₂τ⟩ :=
    exists_orderOf_three_tau hLV hCL k2GL_spec.1 k2GL_spec.2 hl₂ (tau_eq_iff.2 hl₂τ)
  set D := L ⊓ centralizer (V : Set G) with hD
  set Y := zpowers y₁ ⊔ D with hY
  have hYL : Y ≤ L := sup_le (zpowers_le.2 hy₁L) inf_le_left
  have hDn : ∀ g ∈ L, ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun g hg d hd =>
    ⟨L.mul_mem (L.mul_mem hg hd.1) (L.inv_mem hg),
      (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (hLV hg)) d).1 hd.2⟩
  have hc : y₂ * y₁ * y₂⁻¹ * y₁⁻¹ ∈ D := by
    have hmem : y₂ * y₁ * y₂⁻¹ * y₁⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hy₂L hy₁L) (L.inv_mem hy₂L)) (L.inv_mem hy₁L)
    refine ⟨hmem, mem_centralizer_of_tau (Φ := Φ) (hLV hmem) ?_⟩
    have h1 : (⟨y₂ * y₁ * y₂⁻¹ * y₁⁻¹, hLV hmem⟩ : normalizer (V : Set G)) =
        ⟨y₂, hLV hy₂L⟩ * ⟨y₁, hLV hy₁L⟩ * ⟨y₂, hLV hy₂L⟩⁻¹ * ⟨y₁, hLV hy₁L⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hy₁τ, hy₂τ, ← kGL_mul_k2GL]
    group
  have hy₂N : y₂ ∈ normalizer (Y : Set G) := by
    refine mem_normalizer_of_map_le ?_
    rw [hY, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_zpowers, zpowers_le]
      have : (MulAut.conj y₂).toMonoidHom y₁ = (y₂ * y₁ * y₂⁻¹ * y₁⁻¹) * y₁ := by
        simp [MulAut.conj_apply]
      rw [this]
      exact Y.mul_mem (mem_sup_right hc) (mem_sup_left (mem_zpowers y₁))
    · rintro _ ⟨d, hd, rfl⟩
      exact mem_sup_right (hDn y₂ hy₂L d hd)
  have hY3 : 3 ∣ Nat.card Y := by
    have := orderOf_dvd_natCard (⟨y₁, mem_sup_left (mem_zpowers y₁)⟩ : Y)
    rwa [Subgroup.orderOf_mk, hy₁3] at this
  have hy₂3' : y₂ ^ 3 = 1 := hy₂3 ▸ pow_orderOf_eq_one y₂
  obtain ⟨a, haY, ha3, hy₂a⟩ := exists_orderOf_three_commute hY3 hy₂3' hy₂N
  have haL : a ∈ L := hYL haY
  set P : Subgroup G := ((zpowers kGL).comap (tau Φ)).map (normalizer (V : Set G)).subtype
    with hP
  have hYP : Y ≤ P := by
    refine sup_le (zpowers_le.2 ⟨⟨y₁, hLV hy₁L⟩, ?_, rfl⟩) fun d hd => ⟨⟨d, hLV hd.1⟩, ?_, rfl⟩
    · change tau Φ ⟨y₁, hLV hy₁L⟩ ∈ zpowers kGL
      rw [hy₁τ]
      exact mem_zpowers _
    · change tau Φ ⟨d, hLV hd.1⟩ ∈ zpowers kGL
      rw [tau_eq_one_iff.2 hd.2]
      exact one_mem _
  have haτ : tau Φ ⟨a, hLV haL⟩ ∈ zpowers kGL := by
    obtain ⟨n, hn, hna⟩ := hYP haY
    have : n = ⟨a, hLV haL⟩ := Subtype.ext hna
    rw [← this]
    exact hn
  have haτ1 : tau Φ ⟨a, hLV haL⟩ ≠ 1 := by
    intro h1
    have haD : a ∈ D := ⟨haL, tau_eq_one_iff.1 h1⟩
    obtain ⟨m, hm⟩ := hCL ⟨a, haD⟩
    have h2 : a ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [ha3] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hcases : tau Φ ⟨a, hLV haL⟩ = kGL ∨ tau Φ ⟨a, hLV haL⟩ = kGL ^ 2 := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 haτ
    have hk3 : orderOf kGL = 3 := orderOf_eq_prime kGL_spec.1 kGL_spec.2
    rw [← zpow_mod_orderOf, hk3] at hn
    have h0 : 0 ≤ n % (3 : ℕ) := Int.emod_nonneg _ (by norm_num)
    have h3 : n % (3 : ℕ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    have : n % (3 : ℕ) = 0 ∨ n % (3 : ℕ) = 1 ∨ n % (3 : ℕ) = 2 := by omega
    rcases this with h | h | h
    · rw [h, zpow_zero] at hn
      exact absurd hn.symm haτ1
    · rw [h, zpow_one] at hn
      exact Or.inl hn.symm
    · rw [h] at hn
      exact Or.inr (by rw [← hn]; rfl)
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  rcases hcases with h | h
  · exact ⟨a, haL, y₂, hy₂L, ha3, hy₂3, hy₂a, h, hy₂τ⟩
  · have ha2L : a ^ 2 ∈ L := L.pow_mem haL 2
    have hτ2 : tau Φ ⟨a ^ 2, hLV ha2L⟩ = kGL := by
      have h1 : (⟨a ^ 2, hLV ha2L⟩ : normalizer (V : Set G)) = ⟨a, hLV haL⟩ ^ 2 := rfl
      rw [h1, map_pow, h, ← pow_mul]
      calc kGL ^ (2 * 2) = kGL ^ 3 * kGL := by rw [← pow_succ]
        _ = kGL := by rw [kGL_spec.1, one_mul]
    have ha21 : a ^ 2 ≠ 1 := by
      intro h1
      apply kGL_spec.2
      rw [← hτ2]
      have : (⟨a ^ 2, hLV ha2L⟩ : normalizer (V : Set G)) = 1 := Subtype.ext h1
      rw [this, map_one]
    refine ⟨a ^ 2, ha2L, y₂, hy₂L, orderOf_eq_prime ?_ ha21, hy₂3, ?_, hτ2, hy₂τ⟩
    · rw [← pow_mul, mul_comm, pow_mul, ha3', one_pow]
    · exact (Commute.pow_right hy₂a 2).eq

@[expose] noncomputable def lineSub (Φ : Additive V ≃ₗ[ZMod 2] W6) : Subgroup G :=
  closure ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G)

@[expose] noncomputable def lineH (Φ : Additive V ≃ₗ[ZMod 2] W6) : Subgroup G :=
  centralizer ({ptOf Φ (vecOf 15), ptOf Φ (vecOf 52)} : Set G)

@[expose] noncomputable def lineN (Φ : Additive V ≃ₗ[ZMod 2] W6) : Subgroup G :=
  normalizer (lineSub Φ : Set G)

omit [Finite G] in
theorem lineSub_le : lineSub Φ ≤ V := by
  rw [lineSub, closure_le]
  rintro _ (rfl | rfl)
  exacts [ptOf_mem _, ptOf_mem _]

omit [Finite G] in
theorem centralizer_lineSub : centralizer (lineSub Φ : Set G) = lineH Φ := by
  rw [lineSub, lineH, centralizer_closure]

omit [Finite G] in
theorem lineH_le_lineN : lineH Φ ≤ lineN Φ := by
  rw [← centralizer_lineSub, lineN]
  exact centralizer_le_normalizer_self _

omit [Finite G] in
theorem lineN_le_normalizer_lineH : lineN Φ ≤ normalizer (lineH Φ : Set G) := by
  rw [← centralizer_lineSub, lineN]
  exact normalizer_le_normalizer_centralizer _

omit [Finite G] in
theorem mem_lineH_of_tau_k {k₁ : G} (hk₁ : k₁ ∈ normalizer (V : Set G))
    (hτ : tau Φ ⟨k₁, hk₁⟩ = kGL) : k₁ ∈ lineH Φ := by
  have hk := tau_eq_iff.1 hτ
  rw [lineH, mem_centralizer_iff]
  rintro _ (rfl | rfl)
  · have h := conj_ptOf hk₁ hk (vecOf 15)
    rw [glLin_vecOf_of_coe coe_kGL, (kc_fix_iff 15 (by norm_num)).2 (by norm_num)] at h
    calc ptOf Φ (vecOf 15) * k₁ = k₁ * ptOf Φ (vecOf 15) * k₁⁻¹ * k₁ := by rw [h]
      _ = k₁ * ptOf Φ (vecOf 15) := by group
  · have h := conj_ptOf hk₁ hk (vecOf 52)
    rw [glLin_vecOf_of_coe coe_kGL, (kc_fix_iff 52 (by norm_num)).2 (by norm_num)] at h
    calc ptOf Φ (vecOf 52) * k₁ = k₁ * ptOf Φ (vecOf 52) * k₁⁻¹ * k₁ := by rw [h]
      _ = k₁ * ptOf Φ (vecOf 52) := by group

theorem mem_lineN_of_tau_k2 {x : G} (hx : x ∈ normalizer (V : Set G))
    (hτ : tau Φ ⟨x, hx⟩ = k2GL) : x ∈ lineN Φ := by
  have hk := tau_eq_iff.1 hτ
  refine mem_normalizer_of_map_le ?_
  rw [lineSub, MonoidHom.map_closure, closure_le]
  rintro _ ⟨w, hw, rfl⟩
  change x * w * x⁻¹ ∈ lineSub Φ
  rcases hw with rfl | rfl
  · rw [conj_ptOf hx hk, glLin_vecOf_of_coe coe_k2GL, k2c_spec.2.2.2.1, vecOf_fiftynine,
      ptOf_add]
    exact mul_mem (subset_closure (Set.mem_insert _ _))
      (subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [conj_ptOf hx hk, glLin_vecOf_of_coe coe_k2GL, k2c_spec.2.2.2.2]
    exact subset_closure (Set.mem_insert _ _)

omit [Finite G] in
theorem not_mem_lineH_of_tau_k2 {x : G} (hx : x ∈ normalizer (V : Set G))
    (hτ : tau Φ ⟨x, hx⟩ = k2GL) : x ∉ lineH Φ := by
  intro hxH
  have hk := tau_eq_iff.1 hτ
  have h := conj_ptOf hx hk (vecOf 15)
  rw [glLin_vecOf_of_coe coe_k2GL, k2c_spec.2.2.2.1] at h
  have hc : x * ptOf Φ (vecOf 15) * x⁻¹ = ptOf Φ (vecOf 15) := by
    have := (mem_centralizer_iff.1 hxH) _ (Set.mem_insert _ _)
    rw [← this]
    group
  rw [hc] at h
  have := vecOf_injective (by norm_num) (by norm_num) (ptOf_injective h)
  omega

omit [Finite G] in
theorem ptOf_fifteen_ne_one : ptOf Φ (vecOf 15) ≠ 1 := by
  intro h
  have h0 : vecOf 15 = (0 : W6) := ptOf_injective (h.trans ptOf_zero.symm)
  have := vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
    (h0.trans vecOf_zero.symm)
  norm_num at this

omit [Finite G] in
theorem lineSub_ne_bot : lineSub Φ ≠ ⊥ := by
  intro h
  apply ptOf_fifteen_ne_one (Φ := Φ)
  have : ptOf Φ (vecOf 15) ∈ lineSub Φ := subset_closure (Set.mem_insert _ _)
  rw [h, mem_bot] at this
  exact this

omit [Finite G] in
theorem isPGroup_lineSub : IsPGroup 2 (lineSub Φ) :=
  (IsElementaryAbelian.isPGroup 2 V).to_le lineSub_le

theorem isSQTKIn_lineN {T L : Subgroup G} (hH : QTH13 G T L) : IsSQTKIn (lineN Φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hH.simple
  have hloc := (qtkeCore_of_cat hH.nonabelian hH.qtke).1
  refine InternalSec.sqtkGroup_of_localSQTK hloc fun h0 => lineSub_ne_bot (Φ := Φ) ?_
  have hle : lineSub Φ ≤ pCoreOf 2 (lineN Φ) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      isPGroup_lineSub
  rw [h0] at hle
  exact le_bot_iff.1 hle

theorem charTwo_lineH
    {T L : Subgroup G} {z : G} (hH : QTH13 G T L) (hF : QTU3InternalFrame T L V z)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s) :
    CharTwo (lineH Φ) := by
  have hTV : T ≤ normalizer (V : Set G) := hF.2.2.2.2.2.2.2.1
  have hVT : V ≤ T := hF.2.1
  have huT : ptOf Φ (vecOf 15) ∈ T ⊓ centralizer (T : Set G) := by
    refine ⟨hVT (ptOf_mem _), mem_centralizer_iff.2 fun t ht => ?_⟩
    obtain ⟨s, hs, hst⟩ := hΦT t ht
    obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
    have h1 := conj_ptOf (hTV ht) hst (vecOf 15)
    rw [glLin_vecOf_of_coe (coe_s0GL hi), s0c_fix_fifteen _ (by
      rw [s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; exact hi)]
      exact List.getElem_mem _)] at h1
    calc t * ptOf Φ (vecOf 15) = t * ptOf Φ (vecOf 15) * t⁻¹ * t := by group
      _ = ptOf Φ (vecOf 15) * t := by rw [h1]
  have hN : CharTwo (lineN Φ) := by
    refine charTwo_normalizer_of_inf_center hH.qtke.2.1 (isSylowTwoOf_top hH.sylow)
      isPGroup_lineSub fun h0 => ptOf_fifteen_ne_one (Φ := Φ) ?_
    have : ptOf Φ (vecOf 15) ∈ lineSub Φ ⊓ (T ⊓ centralizer (T : Set G)) :=
      ⟨subset_closure (Set.mem_insert _ _), huT⟩
    rw [h0, mem_bot] at this
    exact this
  exact CharTwo.of_normal hN lineH_le_lineN
    ((normal_subgroupOf_iff_le_normalizer lineH_le_lineN).2 lineN_le_normalizer_lineH)

end CFSG.Quasithin.H13.U3.NLine
