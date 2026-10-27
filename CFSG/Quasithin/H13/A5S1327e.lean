module

public import CFSG.Quasithin.H13.A5S1327d
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem InK4_conj_of_fix4 : ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → InK4 τ →
    InK4 (σ * τ * σ⁻¹) := by
  decide +kernel

theorem InK4_of_conj_InD : ∀ σ τ : Equiv.Perm (Fin 5), InD σ → τ 4 = 4 → τ ^ 3 = 1 → τ ≠ 1 →
    InD (τ * σ * τ⁻¹) → InD (τ ^ 2 * σ * (τ ^ 2)⁻¹) → InK4 σ := by
  decide +kernel

theorem pow_twelve_of_fix4 : ∀ σ : Equiv.Perm (Fin 5), σ 4 = 4 → σ ^ 12 = 1 := by
  decide +kernel

theorem cube_of_fix4_of_odd {σ : Equiv.Perm (Fin 5)} (h4 : σ 4 = 4) {n : ℕ} (hn : Odd n)
    (h : σ ^ n = 1) : σ ^ 3 = 1 := by
  refine eq_one_of_pow_coprime (m := 4) (n := n) ?_ ?_ ?_
  · rw [← pow_mul]
    exact pow_twelve_of_fix4 σ h4
  · rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  · exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hn)

theorem fix_of_fix_cube {Q : Type*} [Group Q] (a : Q) (hgen : ∀ q : Q, q ∈ Subgroup.zpowers a)
    {n : ℕ} (ha : a ^ 3 ^ n = 1) (ha3 : a ^ 3 ≠ 1) (φ : Q →* Q) (hφ3 : φ (a ^ 3) = a ^ 3)
    {b : ℕ} (hφ2 : ∀ q, (⇑φ)^[2 ^ b] q = q) : φ a = a := by
  obtain ⟨m, hm⟩ := hgen (φ a)
  set c := a ^ (m - 1) with hc
  have hφa : φ a = a * c := by
    rw [← hm, hc, ← zpow_one_add]
    congr 1
    ring
  have hc3 : c ^ 3 = 1 := by
    have h1 : (φ a) ^ 3 = a ^ 3 := by rw [← map_pow, hφ3]
    rw [hφa] at h1
    have hcomm : Commute a c := (Commute.refl a).zpow_right (m - 1)
    rw [hcomm.mul_pow] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha)
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    apply ha3
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact (Nat.pow_dvd_pow 3 (show k ≤ 1 by omega)).trans (by norm_num)
  have h9 : (9 : ℤ) ∣ (orderOf a : ℤ) := by
    rw [hk]
    have : (9 : ℕ) ∣ 3 ^ k := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 3 hk2
    exact_mod_cast this
  have hc3' : a ^ (3 * (m - 1)) = 1 := by
    have e : a ^ (3 * (m - 1)) = c ^ (3 : ℤ) := by
      rw [mul_comm, zpow_mul, ← hc]
    rw [e, zpow_ofNat, hc3]
  have hdvd : (orderOf a : ℤ) ∣ 3 * (m - 1) := orderOf_dvd_iff_zpow_eq_one.mpr hc3'
  have h3 : (3 : ℤ) ∣ m - 1 := by
    have := h9.trans hdvd
    omega
  obtain ⟨j, hj⟩ := h3
  have hcj : c = (a ^ 3) ^ j := by
    rw [hc, hj, ← zpow_natCast, ← zpow_mul]
    norm_num
  have hφc : φ c = c := by rw [hcj, map_zpow, hφ3]
  have hiter : ∀ i : ℕ, (⇑φ)^[i] a = a * c ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hφc, hφa, pow_succ', mul_assoc]
  have h2 : c ^ 2 ^ b = 1 := by
    have := hiter (2 ^ b)
    rw [hφ2] at this
    exact (mul_left_cancel (this.symm.trans (mul_one a).symm))
  have hc1 : c = 1 := eq_one_of_pow_coprime hc3 h2 (Nat.Coprime.pow_right b (by norm_num))
  rw [hφa, hc1, mul_one]

@[expose] def conjInHom {G : Type*} [Group G] (K : Subgroup G) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) : ↥K →* ↥K where
  toFun k := ⟨r * k * r⁻¹, (Subgroup.mem_normalizer_iff.mp hr k).mp k.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjInHom_apply_coe {G : Type*} [Group G] (K : Subgroup G) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((conjInHom K hr k : ↥K) : G) = r * k * r⁻¹ := rfl

theorem conjInHom_iterate_coe {G : Type*} [Group G] (K : Subgroup G) {r : G}
    (hr : r ∈ Subgroup.normalizer (K : Set G)) (n : ℕ) (k : ↥K) :
    (((⇑(conjInHom K hr))^[n] k : ↥K) : G) = r ^ n * k * (r ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', conjInHom_apply_coe, ih, pow_succ']
    group

theorem conj_fix_of_cyclic {G : Type*} [Group G] {K P : Subgroup G} (hPK : P ≤ K)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) {y r : G} (hyK : y ∈ K)
    (hKy : ∀ k ∈ K, ∃ i : ℤ, ∃ q ∈ P, k = y ^ i * q) {n : ℕ} (hyn : y ^ 3 ^ n ∈ P)
    (hy3 : y ^ 3 ∉ P) (hr : r ∈ Subgroup.normalizer (K : Set G))
    (hrP : r ∈ Subgroup.normalizer (P : Set G)) {b : ℕ} (hrb : r ^ 2 ^ b = 1)
    (hfix : (r * y ^ 3 * r⁻¹)⁻¹ * y ^ 3 ∈ P) : (r * y * r⁻¹)⁻¹ * y ∈ P := by
  set P' := P.subgroupOf K with hP'
  have hn : P'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
  set π := QuotientGroup.mk' P' with hπ
  have hπeq : ∀ a c : ↥K, π a = π c ↔ ((a : G))⁻¹ * c ∈ P := by
    intro a c
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rfl
  have hπone : ∀ a : ↥K, π a = 1 ↔ (a : G) ∈ P := by
    intro a
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  set c := conjInHom K hr with hc
  have hle : P' ≤ P'.comap c := by
    intro k hk
    show (c k : G) ∈ P
    rw [hc, conjInHom_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp hrP k).mp hk
  set φ := QuotientGroup.map P' P' c hle with hφ
  have hφmk : ∀ k : ↥K, φ (π k) = π (c k) := fun k => QuotientGroup.map_mk P' P' c hle k
  set yK : ↥K := ⟨y, hyK⟩ with hyKdef
  set yb := π yK with hyb
  have hgen : ∀ q : ↥K ⧸ P', q ∈ Subgroup.zpowers yb := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective P' q
    obtain ⟨i, q₀, hq₀, hk⟩ := hKy k k.2
    have hq₀K : q₀ ∈ K := hPK hq₀
    have e : k = yK ^ i * ⟨q₀, hq₀K⟩ := Subtype.ext (by rw [hk]; simp [hyKdef])
    refine ⟨i, ?_⟩
    show yb ^ i = π k
    rw [e, map_mul, map_zpow, (hπone ⟨q₀, hq₀K⟩).2 hq₀, mul_one]
  have ha : yb ^ 3 ^ n = 1 := by
    rw [hyb, ← map_pow, hπone]
    simpa [hyKdef] using hyn
  have ha3 : yb ^ 3 ≠ 1 := by
    rw [hyb, ← map_pow, Ne, hπone]
    simpa [hyKdef] using hy3
  have hφ3 : φ (yb ^ 3) = yb ^ 3 := by
    rw [hyb, ← map_pow, hφmk, hπeq]
    rw [hc, conjInHom_apply_coe]
    simpa [hyKdef] using hfix
  have hφ2 : ∀ q, (⇑φ)^[2 ^ b] q = q := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective P' q
    have hit : ∀ i : ℕ, (⇑φ)^[i] (π k) = π ((⇑c)^[i] k) := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply', ih, hφmk, Function.iterate_succ_apply']
    show (⇑φ)^[2 ^ b] (π k) = π k
    rw [hit]
    congr 1
    apply Subtype.ext
    rw [hc, conjInHom_iterate_coe, hrb]
    group
  have hfixy := fix_of_fix_cube yb hgen ha ha3 φ hφ3 hφ2
  rw [hyb, hφmk, hπeq, hc, conjInHom_apply_coe] at hfixy
  simpa [hyKdef] using hfixy

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_F (h331 : Stmt3_3_1)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ∃ F : ↥H →* Equiv.Perm (Fin 3),
      (∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G)) ∧
      Function.Surjective F ∧
      (∀ (t : G) (ht : t ∈ T), F ⟨t, hH.1.1 ht⟩ ^ 2 = 1) ∧
      (∀ (k : G) (hk : k ∈ oTwoUpper H), F ⟨k, oTwoUpper_le H hk⟩ ^ 3 = 1) := by
  classical
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := hUred.2.1
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  obtain ⟨eS3⟩ := hS3
  have e3 : ↥(autI hUel H) ≃* Equiv.Perm (Fin 3) := eS3
  set f : ↥H →* MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
    convHom hUel H hHN with hf
  have hfmem : ∀ h : ↥H, f h ∈ autI hUel H := fun h => convI_mem_autI hUel h.2 (hHN h.2)
  set F : ↥H →* Equiv.Perm (Fin 3) :=
    e3.toMonoidHom.comp (f.codRestrict (autI hUel H) hfmem) with hFdef
  have hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G) := by
    intro h
    have e1 : F h = 1 ↔ f h = 1 := by
      have : F h = e3 (f.codRestrict (autI hUel H) hfmem h) := rfl
      rw [this, MulEquiv.map_eq_one_iff]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [e1]
    have : f h = convI hUel ⟨h, hHN h.2⟩ := rfl
    rw [this]
    exact convI_eq_one_iff hUel _
  refine ⟨F, hF1, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨g, hgH, hg⟩ := (mem_autI hUel).1 (e3.symm σ).2
    refine ⟨⟨g, hgH⟩, ?_⟩
    have e : f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩ = e3.symm σ := by
      apply Subtype.ext
      exact hg
    have : F ⟨g, hgH⟩ = e3 (f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩) := rfl
    rw [this, e, MulEquiv.apply_symm_apply]
  · intro t ht
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨t, ht⟩
    have hb' : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ b = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hb)
    refine perm3_sq_of_two_pow (k := b) ?_
    rw [← map_pow, hb', map_one]
  · intro k hk
    obtain ⟨a, ha⟩ := hpow k hk
    refine perm3_cube_of_prime_pow (a := a) hp hp2 ?_
    rw [← map_pow]
    refine (hF1 _).2 ?_
    exact hO2U ha

theorem exists_gen (h331 : Stmt3_3_1)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {F : ↥H →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFsurj : Function.Surjective F) (hFT : ∀ (t : G) (ht : t ∈ T), F ⟨t, hH.1.1 ht⟩ ^ 2 = 1)
    (hFL : ∀ (k : G) (hk : k ∈ oTwoUpper H), F ⟨k, oTwoUpper_le H hk⟩ ^ 3 = 1) :
    ∃ (y : G) (hy : y ∈ oTwoUpper H), Odd (orderOf y) ∧ F ⟨y, oTwoUpper_le H hy⟩ ≠ 1 ∧
      oTwoUpper H ≤ Subgroup.zpowers y ⊔ pCoreOf 2 H := by
  classical
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨-, -, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hZU : quasithinOmegaOneCenter T ≤ S.UH H := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  set LH := oTwoUpper H with hLH
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  obtain ⟨l, hl, hFl⟩ : ∃ (l : G) (hl : l ∈ LH), F ⟨l, hLHH hl⟩ ≠ 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨γ, hγ⟩ := perm3_exists_sq_ne_one
    obtain ⟨⟨h, hh⟩, hhγ⟩ := hFsurj γ
    have hh' : h ∈ ((LH ⊔ T : Subgroup G) : Set G) := by rw [← hHeq]; exact hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left LH T hTLH] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    have e : (⟨k * t, hh⟩ : ↥H) = ⟨k, hLHH hk⟩ * ⟨t, hTH ht⟩ := rfl
    rw [e, map_mul, hne k hk, one_mul] at hhγ
    exact hγ (hhγ ▸ hFT t ht)
  obtain ⟨e, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  set y := l ^ 2 ^ e with hy
  have hyL : y ∈ LH := LH.pow_mem hl _
  have hyo : Odd (orderOf y) := by
    have : orderOf y = m := by
      rw [hy, orderOf_pow' l (pow_ne_zero _ two_ne_zero), hlm, Nat.gcd_mul_right_left]
      exact Nat.mul_div_cancel_left m (pow_pos two_pos e)
    rw [this]
    exact hm
  have hFy : F ⟨y, hLHH hyL⟩ ≠ 1 := by
    intro h1
    have e1 : (⟨y, hLHH hyL⟩ : ↥H) = ⟨l, hLHH hl⟩ ^ 2 ^ e := rfl
    rw [e1, map_pow] at h1
    exact hFl (eq_one_of_pow_coprime (hFL l hl) h1 (Nat.Coprime.pow_right e (by norm_num)))
  refine ⟨y, hyL, hyo, hFy, ?_⟩
  have hcover : LH ≤ Subgroup.zpowers y ⊔ (H ⊓ Subgroup.centralizer (S.UH H : Set G)) := by
    intro k hk
    have hmem : ∀ j : ℕ, F ⟨k, hLHH hk⟩ = F ⟨y, hLHH hyL⟩ ^ j →
        k ∈ Subgroup.zpowers y ⊔ (H ⊓ Subgroup.centralizer (S.UH H : Set G)) := by
      intro j hj
      have hyj : y ^ j ∈ H := H.pow_mem (hLHH hyL) j
      have hmemH : (y ^ j)⁻¹ * k ∈ H := H.mul_mem (H.inv_mem hyj) (hLHH hk)
      have hc : (y ^ j)⁻¹ * k ∈ H ⊓ Subgroup.centralizer (S.UH H : Set G) := by
        refine ⟨hmemH, (hF1 ⟨_, hmemH⟩).1 ?_⟩
        have e1 : (⟨(y ^ j)⁻¹ * k, hmemH⟩ : ↥H) =
            (⟨y, hLHH hyL⟩ ^ j)⁻¹ * ⟨k, hLHH hk⟩ := rfl
        rw [e1, map_mul, map_inv, map_pow, hj, inv_mul_cancel]
      have e2 : k = y ^ j * ((y ^ j)⁻¹ * k) := by group
      rw [e2]
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) j) hc
    rcases perm3_cyclic _ _ hFy (hFL y hyL) (hFL k hk) with h1 | h1 | h1
    · exact hmem 0 (by rw [h1, pow_zero])
    · exact hmem 1 (by rw [h1, pow_one])
    · exact hmem 2 h1
  have h2 : twoResidual H ≤ Subgroup.zpowers y ⊔ kerIn (H ⊓ M) H := by
    rw [twoResidual_eq_oTwoUpper']
    exact hcover.trans (sup_le_sup_left (hMP.inf_centralizer_le_kerIn hUred hHU) _)
  have h3 := hMP.twoResidual_le_sup_pCoreOf hsolv
    (Subgroup.zpowers_le.mpr (hLHH hyL)) h2
  rwa [twoResidual_eq_oTwoUpper'] at h3

theorem false_of_cube_not_mem (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {F : ↥H →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFL : ∀ (k : G) (hk : k ∈ oTwoUpper H), F ⟨k, oTwoUpper_le H hk⟩ ^ 3 = 1)
    {y : G} (hyL : y ∈ oTwoUpper H) (hyo : Odd (orderOf y))
    (hFy : F ⟨y, oTwoUpper_le H hyL⟩ ≠ 1)
    (hLyP : ∀ k ∈ oTwoUpper H, ∃ i : ℤ, ∃ q ∈ pCoreOf 2 H ⊓ oTwoUpper H, k = y ^ i * q)
    (hx : y ^ 3 ∉ pCoreOf 2 H) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  set U := S.UH H with hUdef
  set LH := oTwoUpper H with hLH
  set P := pCoreOf 2 H ⊓ LH with hP
  set J := H ⊓ Subgroup.centralizer (U : Set G) with hJ
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHLH : H ≤ Subgroup.normalizer (LH : Set G) := le_normalizer_oTwoUpper H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans hHLH
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (U : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hHO2 : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO2 hh, hHLH hh⟩
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHN hh⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hPT : P ≤ T := inf_le_left.trans hO2T
  have hPLH : P ≤ LH := inf_le_right
  have hyH : y ∈ H := hLHH hyL
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  have h2P : ∀ k ∈ LH, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ P := by
    rintro k hk ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hpow k hk
    exact ⟨mem_of_two_pow_of_prime_pow hp hp2 hb ha, hk⟩
  have hloc : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q →
      L ⊔ T ≤ Subgroup.normalizer (Q : Set G) → Subgroup.normalizer (Q : Set G) ≤ M := by
    intro Q hQ1 hQ2 hLTQ
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨Q, hQ1, hQ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (Q : Set G)))
    have hM'M := S.uniqueM.2 M' ⟨hM', hLTQ.trans hM'le⟩
    rw [hM, ← hM'M]
    exact hM'le
  set X := oTwoUpper J with hX
  have hXJ : X ≤ J := oTwoUpper_le J
  have hXH : X ≤ H := hXJ.trans inf_le_left
  have hXLH : X ≤ LH := oTwoUpper_mono inf_le_left
  have hHX : H ≤ Subgroup.normalizer (X : Set G) :=
    hHJ.trans (normalizer_le_normalizer_oTwoUpper J)
  have hJM : J ≤ M :=
    (hMP.inf_centralizer_le_kerIn hUred hHU).trans (kerIn_le.trans inf_le_right)
  have hXM : X ≤ M := hXJ.trans hJM
  have hXz : ∀ w ∈ X, w * S.z * w⁻¹ = S.z := by
    intro w hw
    have hwz := Subgroup.mem_centralizer_iff.mp
      (Subgroup.centralizer_le hZU (hXJ hw).2) S.z S.z_mem_omegaOneCenter
    rw [← hwz]
    group
  have hV1 : S.V1 ≠ ⊥ := by
    intro h
    have := S.card_V1
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := by
    intro w hw
    refine S.mem_normalizer_V_of h1222 (hXM hw) hV1 S.V1_le_V ?_
    rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
    calc w * S.z = w * S.z * w⁻¹ * w := by group
      _ = S.z * w := by rw [hXz w hw]
  have hxJ : y ^ 3 ∈ J := by
    refine ⟨H.pow_mem hyH 3, (hF1 ⟨_, H.pow_mem hyH 3⟩).1 ?_⟩
    have e : (⟨y ^ 3, H.pow_mem hyH 3⟩ : ↥H) = ⟨y, hyH⟩ ^ 3 := rfl
    rw [e, map_pow]
    exact hFL y hyL
  have hxX : y ^ 3 ∈ X := by
    refine mem_oTwoUpper_of_odd hxJ ?_
    exact Odd.of_dvd_nat hyo (orderOf_pow_dvd 3)
  have hx1 : y ^ 3 ≠ 1 := by
    intro h
    apply hx
    rw [h]
    exact (pCoreOf 2 H).one_mem
  by_cases hXCV : X ≤ Subgroup.centralizer (V : Set G)
  ·
    set B := L ⊓ Subgroup.centralizer (V : Set G) with hB
    have hBT : B ≤ T := by
      intro b hb
      refine S.pCoreOf_LT_le_T ?_
      rw [← S.cLT]
      exact ⟨Subgroup.mem_sup_left hb.1, hb.2⟩
    have hBX : B ≤ Subgroup.normalizer (X : Set G) := (hBT.trans hTH).trans hHX
    set Y := X ⊔ B with hY
    have hYX : oTwoUpper Y = X := by
      apply le_antisymm
      · refine oTwoUpper_le_of_pow_mem fun w hw => ?_
        have hw' : w ∈ ((X ⊔ B : Subgroup G) : Set G) := hw
        rw [Subgroup.coe_mul_of_right_le_normalizer_left X B hBX] at hw'
        obtain ⟨a, ha, b, hb, rfl⟩ := hw'
        obtain ⟨k, hk⟩ := S.isPGroup_T ⟨b, hBT hb⟩
        have hk' : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        obtain ⟨a', ha', he⟩ := pow_mem_mul_of_normalizes ha (hBX hb) (2 ^ k)
        rw [hk', mul_one] at he
        exact ⟨k, he ▸ ha'⟩
      · refine (Subgroup.closure_le _).mpr fun w hw => ?_
        exact mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hw)) hw.2
    have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
      intro l hl
      have hlN : l ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le hl
      refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
      have hk' : k ∈ ((X ⊔ B : Subgroup G) : Set G) := hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X B hBX] at hk'
      obtain ⟨a, ha, b, hb, rfl⟩ := hk'
      have haN : a ∈ Subgroup.normalizer (V : Set G) := hXV ha
      have hc : l * a * l⁻¹ * a⁻¹ ∈ B := by
        refine ⟨?_, ?_⟩
        · have h1 : a * l⁻¹ * a⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hXM ha) l⁻¹).mp (L.inv_mem hl)
          have e : l * a * l⁻¹ * a⁻¹ = l * (a * l⁻¹ * a⁻¹) := by group
          rw [e]
          exact L.mul_mem hl h1
        · have hcN : l * a * l⁻¹ * a⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
            Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN haN)
              (Subgroup.inv_mem _ hlN)) (Subgroup.inv_mem _ haN)
          refine S.frame.mem_centralizer_of_rho ⟨_, hcN⟩ ?_
          have e : (⟨l * a * l⁻¹ * a⁻¹, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
              ⟨l, hlN⟩ * ⟨a, haN⟩ * (⟨l, hlN⟩)⁻¹ * (⟨a, haN⟩)⁻¹ := rfl
          rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
            S.frame.rho_eq_one_of_mem ⟨a, haN⟩ (hXCV ha)]
          group
      have hlb : l * b * l⁻¹ ∈ B := by
        refine ⟨L.mul_mem (L.mul_mem hl hb.1) (L.inv_mem hl), ?_⟩
        exact (Subgroup.mem_normalizer_iff.mp
          (B6.le_normalizer_centralizer S.frame.L_le hl) b).mp hb.2
      have e : l * (a * b) * l⁻¹ = (l * a * l⁻¹ * a⁻¹) * a * (l * b * l⁻¹) := by group
      rw [e]
      exact Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ha))
        (Subgroup.mem_sup_right hlb)
    have hLX : L ≤ Subgroup.normalizer (X : Set G) := by
      rw [← hYX]
      exact hLY.trans (normalizer_le_normalizer_oTwoUpper Y)
    have hFX : CharTwo X :=
      CharTwo.of_normal hF hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)
    have hO2X : pCoreOf 2 X ≠ ⊥ := by
      intro h
      apply hx1
      have hC : y ^ 3 ∈ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
        rw [h, Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Subgroup.mem_bot.mp hg, one_mul, mul_one]
      have := hFX ⟨hxX, hC⟩
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hNO : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 X
    have hle := hloc _ hO2X (pCoreOf_isPGroup 2 X)
      (sup_le (hLX.trans hNO) ((hTH.trans hHX).trans hNO))
    exact hH.2.1 ((hHX.trans hNO).trans hle)
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hFy3 : orderOf (F ⟨y, hyH⟩) = 3 := orderOf_eq_prime (hFL y hyL) hFy
    obtain ⟨w, hwJ, hwo, hwV⟩ : ∃ w, w ∈ J ∧ Odd (orderOf w) ∧
        w ∉ Subgroup.centralizer (V : Set G) := by
      by_contra hne
      push Not at hne
      exact hXCV ((Subgroup.closure_le _).mpr fun w hw => hne w hw.1 hw.2)
    have hwX : w ∈ X := mem_oTwoUpper_of_odd hwJ hwo
    have hwN : w ∈ Subgroup.normalizer (V : Set G) := hXV hwX
    set τ := S.frame.ρ ⟨w, hwN⟩ with hτ
    have hτ4 : τ 4 = 4 := S.rho_four_of_conj_z hwN (hXz w hwX)
    have hτ1 : τ ≠ 1 := fun h => hwV (S.frame.mem_centralizer_of_rho _ h)
    have hτ3 : τ ^ 3 = 1 := by
      refine cube_of_fix4_of_odd hτ4 hwo ?_
      rw [hτ, ← map_pow]
      have e : (⟨w, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ orderOf w = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [e, map_one]
    have hXTH : X ⊔ T ≤ H := sup_le hXH hTH
    have hsylXT : IsSylowTwoOf T (X ⊔ T) := isSylowTwoOf_of_le S.h13.sylow le_sup_right
    set R := pCoreOf 2 (X ⊔ T) with hR
    have hRT : R ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsylXT
    have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 _
    have hXTR : X ⊔ T ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 _
    have hRR1 : R ≤ S.frame.R1 := by
      intro r hr
      have hrT := hRT hr
      refine (S.frame.mem_R1 hrT).2 ?_
      have hwXT : w ∈ X ⊔ T := Subgroup.mem_sup_left hwX
      have h1 : w * r * w⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hXTR hwXT) r).mp hr
      have h2 : w ^ 2 * r * (w ^ 2)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (hXTR ((X ⊔ T).pow_mem hwXT 2)) r).mp hr
      have hrN := S.frame.T_le hrT
      have hD1 := S.frame.T_D ⟨_, S.frame.T_le (hRT h1)⟩ (hRT h1)
      have hD2 := S.frame.T_D ⟨_, S.frame.T_le (hRT h2)⟩ (hRT h2)
      have e1 : (⟨w * r * w⁻¹, S.frame.T_le (hRT h1)⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨w, hwN⟩ * ⟨r, hrN⟩ * (⟨w, hwN⟩)⁻¹ := rfl
      have e2 : (⟨w ^ 2 * r * (w ^ 2)⁻¹, S.frame.T_le (hRT h2)⟩ :
          ↥(Subgroup.normalizer (V : Set G))) =
          ⟨w, hwN⟩ ^ 2 * ⟨r, hrN⟩ * (⟨w, hwN⟩ ^ 2)⁻¹ := Subtype.ext (by simp)
      rw [e1, map_mul, map_mul, map_inv] at hD1
      rw [e2, map_mul, map_mul, map_inv, map_pow] at hD2
      exact InK4_of_conj_InD _ _ (S.frame.T_D ⟨r, hrN⟩ hrT) hτ4 hτ3 hτ1 hD1 hD2
    have hXTL : X ⊔ T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
      refine sup_le (fun a ha => A4.mem_normalizer_of_conj_mem fun s hs => ?_) (fun t ht => ?_)
      · have haN := hXV ha
        have hsN := S.frame.T_le hs.1
        have hasL : a * s * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hXM ha) s).mp hs.2
        have hasN : a * s * a⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hsN) (Subgroup.inv_mem _ haN)
        refine ⟨S.mem_T_of_InK4 ⟨_, hasN⟩ (Subgroup.mem_sup_left hasL) ?_, hasL⟩
        have e : (⟨a * s * a⁻¹, hasN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨a, haN⟩ * ⟨s, hsN⟩ * (⟨a, haN⟩)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv]
        exact InK4_conj_of_fix4 _ _ (S.rho_four_of_conj_z haN (hXz a ha))
          (S.InK4_of_mem_TL ⟨s, hsN⟩ hs)
      · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, S.T_le_NL ht⟩
    have hTLR : T ⊓ L ≤ R :=
      le_pCoreOf_of_le_normalizer (inf_le_left.trans le_sup_right) hXTL
        (S.isPGroup_T.to_le inf_le_left)
    have hVR : V ≤ R :=
      le_pCoreOf_of_le_normalizer (S.V_le_T.trans le_sup_right) (sup_le hXV S.frame.T_le)
        S.isPGroup_V
    have hJR : thompsonJ R ≤ R ⊓ Subgroup.centralizer (V : Set G) :=
      iSup₂_le fun A hA => le_inf hA.1
        (S.frame.le_centralizer_of_isMaxElemAbelian_le_R1 S.elemAbelian_V hVR hRR1 hA)
    have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRT.trans S.T_le_NL
    set O := (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) with hO
    have hOR : O ≤ R := by
      rintro g ⟨hg, hgC⟩
      have hg' : g ∈ ((L ⊔ R : Subgroup G) : Set G) := hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L R hRL] at hg'
      obtain ⟨l, hl, r, hr, rfl⟩ := hg'
      have hlN := S.frame.L_le hl
      have hrN := S.frame.T_le (hRT hr)
      have hlrN : l * r ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hlN hrN
      have h1 : S.frame.ρ ⟨l * r, hlrN⟩ = 1 := S.frame.rho_eq_one_of_mem _ hgC
      have e : (⟨l * r, hlrN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨l, hlN⟩ * ⟨r, hrN⟩ := rfl
      rw [e, map_mul] at h1
      have h2 : S.frame.ρ ⟨l, hlN⟩ = (S.frame.ρ ⟨r, hrN⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hr4 : InK4 (S.frame.ρ ⟨r, hrN⟩) := (S.frame.mem_R1 (hRT hr)).1 (hRR1 hr)
      have hl4 : InK4 (S.frame.ρ ⟨l, hlN⟩) := by
        rw [h2]
        exact mem_K4Frame.mp (K4Frame.inv_mem (mem_K4Frame.mpr hr4))
      have hlT : l ∈ T := S.mem_T_of_InK4 ⟨l, hlN⟩ (Subgroup.mem_sup_left hl) hl4
      exact R.mul_mem (hTLR ⟨hlT, hl⟩) hr
    have hJO : thompsonJ R ≤ O :=
      le_inf ((thompsonJ_le_self R).trans le_sup_right) (hJR.trans inf_le_right)
    have hJeq : thompsonJ R = thompsonJ O := thompsonJ_eq_of_le hJO hOR
    have hLTLR : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ R : Subgroup G) : Set G) := by
      refine sup_le (fun l hl => Subgroup.le_normalizer (Subgroup.mem_sup_left hl))
        (fun t ht => A4.mem_normalizer_of_conj_mem fun k hk => ?_)
      have hk' : k ∈ ((L ⊔ R : Subgroup G) : Set G) := hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L R hRL] at hk'
      obtain ⟨l, hl, r, hr, rfl⟩ := hk'
      have e : t * (l * r) * t⁻¹ = (t * l * t⁻¹) * (t * r * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp (S.T_le_NL ht) l).mp hl)
        ((Subgroup.mem_normalizer_iff.mp (hXTR (Subgroup.mem_sup_right ht)) r).mp hr)
    have hLTO : L ⊔ T ≤ Subgroup.normalizer (O : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hLTLR hg, B6.le_normalizer_centralizer S.reduced.2.1 hg⟩
    have hJne : thompsonJ R ≠ ⊥ := by
      intro hJ0
      obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian R
      have hA1 : A = ⊥ := le_bot_iff.mp ((GammaExtra.le_thompsonJ hA).trans hJ0.le)
      have h16 := hA.2.2 V hVR S.elemAbelian_V
      rw [S.card_V, hA1, Subgroup.card_bot] at h16
      omega
    have hNJ : Subgroup.normalizer (thompsonJ R : Set G) ≤ M := by
      refine hloc _ hJne (GammaExtra.isPGroup_thompsonJ hR2) ?_
      rw [hJeq]
      exact hLTO.trans (GammaExtra.normalizer_le_normalizer_thompsonJ O)
    have hp3 : p = 3 := by
      obtain ⟨a, ha⟩ := hpow y hyL
      have h1 : F ⟨y, hyH⟩ ^ p ^ a = 1 := by
        rw [← map_pow]
        exact (hF1 _).2 (hO2U ha)
      have h3 : 3 ∣ p ^ a := by
        rw [← hFy3]
        exact orderOf_dvd_of_pow_eq_one h1
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)).symm
    have hP_R : P ≤ R :=
      le_pCoreOf_of_le_normalizer (hPT.trans le_sup_right) (hXTH.trans hHP) hP2
    obtain ⟨a, ha⟩ := hpow y hyL
    rw [hp3] at ha
    have hyP : y ^ 3 ^ a ∈ P := ⟨ha, LH.pow_mem hyL _⟩
    have hy3P : y ^ 3 ∉ P := fun h => hx h.1
    have hyR : ∀ r ∈ R, y⁻¹ * r * y ∈ R := by
      intro r hr
      have hr' : r⁻¹ ∈ R := R.inv_mem hr
      have hrT : r⁻¹ ∈ T := hRT hr'
      have hrH : r⁻¹ ∈ H := hTH hrT
      obtain ⟨b, hb⟩ := hR2 ⟨r⁻¹, hr'⟩
      have hb' : r⁻¹ ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have hfix : (r⁻¹ * y ^ 3 * r⁻¹⁻¹)⁻¹ * y ^ 3 ∈ P := by
        refine h2P _ ?_ ?_
        · refine hXLH ?_
          have h1 : r⁻¹ * y ^ 3 * r⁻¹⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp (hHX hrH) _).mp hxX
          exact X.mul_mem (X.inv_mem h1) hxX
        · have hmem : (r⁻¹ * y ^ 3 * r⁻¹⁻¹)⁻¹ * y ^ 3 ∈ R := by
            have e : (r⁻¹ * y ^ 3 * r⁻¹⁻¹)⁻¹ * y ^ 3 =
                r⁻¹ * ((y ^ 3)⁻¹ * r⁻¹⁻¹ * ((y ^ 3)⁻¹)⁻¹) := by group
            rw [e]
            refine R.mul_mem hr' ?_
            have hxXT : (y ^ 3)⁻¹ ∈ X ⊔ T := Subgroup.mem_sup_left (X.inv_mem hxX)
            exact (Subgroup.mem_normalizer_iff.mp (hXTR hxXT) r⁻¹⁻¹).mp (R.inv_mem hr')
          obtain ⟨c, hc⟩ := hR2 ⟨_, hmem⟩
          exact ⟨c, by simpa using congrArg Subtype.val hc⟩
      have hγ := conj_fix_of_cyclic hPLH (hLHH.trans hHP) hyL hLyP hyP hy3P (hTLH hrT)
        (hHP hrH) hb' hfix
      have e : y⁻¹ * r * y = r * ((r⁻¹ * y * r⁻¹⁻¹)⁻¹ * y) := by group
      rw [e]
      exact R.mul_mem hr (hP_R hγ)
    have hyNR : y ∈ Subgroup.normalizer (R : Set G) := by
      have h1 : y⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
        A4.mem_normalizer_of_conj_mem fun r hr => by simpa using hyR r hr
      simpa using Subgroup.inv_mem _ h1
    have hHR : H ≤ Subgroup.normalizer (R : Set G) := by
      refine hHeq.le.trans (sup_le (fun k hk => ?_) (fun t ht => hXTR (Subgroup.mem_sup_right ht)))
      obtain ⟨i, q, hq, rfl⟩ := hLyP k hk
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hyNR i) (Subgroup.le_normalizer (hP_R hq))
    exact hH.2.1 ((hHR.trans (GammaExtra.normalizer_le_normalizer_thompsonJ R)).trans hNJ)

theorem centralizer_UH_le_pCoreOf (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    H ⊓ Subgroup.centralizer (S.UH H : Set G) ≤ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  set U := S.UH H with hUdef
  set LH := oTwoUpper H with hLH
  set P := pCoreOf 2 H ⊓ LH with hP
  set J := H ⊓ Subgroup.centralizer (U : Set G) with hJ
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHLH : H ≤ Subgroup.normalizer (LH : Set G) := le_normalizer_oTwoUpper H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans hHLH
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (U : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hHO2 : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO2 hh, hHLH hh⟩
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHN hh⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hO2T : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hPT : P ≤ T := inf_le_left.trans hO2T
  have hPLH : P ≤ LH := inf_le_right
  have hLHM : ¬ LH ≤ M := fun h => hH.2.1 (hHeq ▸ sup_le h S.T_le_NL)
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  have h2P : ∀ k ∈ LH, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ P := by
    rintro k hk ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hpow k hk
    exact ⟨mem_of_two_pow_of_prime_pow hp hp2 hb ha, hk⟩
  obtain ⟨F, hF1, hFsurj, hFT, hFL⟩ := S.exists_F h331 hH hsolv hS3
  obtain ⟨y, hyL, hyo, hFy, hLy⟩ := S.exists_gen h331 hH hHZ hsolv hF1 hFsurj hFT hFL
  have hyH : y ∈ H := hLHH hyL
  have hLyP : ∀ k ∈ LH, ∃ i : ℤ, ∃ q ∈ P, k = y ^ i * q := by
    intro k hk
    have hk' : k ∈ ((Subgroup.zpowers y ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hLy hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((Subgroup.zpowers_le.mpr hyH).trans hHO2)] at hk'
    obtain ⟨a, ha, q, hq, rfl⟩ := hk'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨i, q, ⟨hq, ?_⟩, rfl⟩
    have e : q = (y ^ i)⁻¹ * (y ^ i * q) := by group
    rw [e]
    exact LH.mul_mem (LH.inv_mem (LH.zpow_mem hyL i)) hk
  have hFy3 : orderOf (F ⟨y, hyH⟩) = 3 := orderOf_eq_prime (hFL y hyL) hFy
  have hx : y ^ 3 ∈ pCoreOf 2 H := by
    by_contra hx
    exact S.false_of_cube_not_mem h331 h1222 hH hHZ hsolv hF1 hFL hyL hyo hFy hLyP hx
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := pCoreOf_isPGroup 2 H ⟨_, hx⟩
    have hc' : (y ^ 3) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have hco : (y ^ 3) ^ orderOf y = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime hc' hco (Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hyo))
  have hJT : J ≤ T := by
    intro j hj
    have hjH : j ∈ H := hj.1
    have hj' : j ∈ ((LH ⊔ T : Subgroup G) : Set G) := by rw [← hHeq]; exact hjH
    rw [Subgroup.coe_mul_of_right_le_normalizer_left LH T hTLH] at hj'
    obtain ⟨k, hk, t, ht, rfl⟩ := hj'
    obtain ⟨i, q, hq, rfl⟩ := hLyP k hk
    have hqtT : q * t ∈ T := T.mul_mem (hPT hq) ht
    have hyiH : y ^ i ∈ H := H.zpow_mem hyH i
    have e : (⟨y ^ i * q * t, hjH⟩ : ↥H) = ⟨y, hyH⟩ ^ i * ⟨q * t, hTH hqtT⟩ :=
      Subtype.ext (by simp [mul_assoc])
    have hF1j := (hF1 ⟨_, hjH⟩).2 hj.2
    rw [e, map_mul, map_zpow] at hF1j
    have hFqt := hFT _ hqtT
    have hi1 : F ⟨y, hyH⟩ ^ i = 1 := by
      have e1 : F ⟨y, hyH⟩ ^ i = (F ⟨q * t, hTH hqtT⟩)⁻¹ := eq_inv_of_mul_eq_one_left hF1j
      refine eq_one_of_pow_coprime (m := 2) (n := 3) ?_ ?_ (by norm_num)
      · rw [e1, inv_pow, hFqt, inv_one]
      · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hFL y hyL, one_zpow]
    have h3i : (3 : ℤ) ∣ i := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr hi1
      rw [hFy3] at this
      exact_mod_cast this
    obtain ⟨j', rfl⟩ := h3i
    have hyi : y ^ (3 * j') = 1 := by rw [zpow_mul, zpow_ofNat, hy3, one_zpow]
    rw [hyi, one_mul]
    exact hqtT
  exact le_pCoreOf_of_le_normalizer inf_le_left hHJ (S.isPGroup_T.to_le hJT)

theorem quotient_pCore_equiv_S3 (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (↥H ⧸ CFSG.Open.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨F, hF1, hFsurj, -, -⟩ := S.exists_F h331 hH hsolv hS3
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hH.1.1
  obtain ⟨hUO, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hker : CFSG.Open.pCore 2 ↥H = F.ker := by
    ext h
    rw [MonoidHom.mem_ker, hF1]
    constructor
    · intro hh
      exact hO2U ⟨h, hh, rfl⟩
    · intro hh
      obtain ⟨h', hh', he⟩ := S.centralizer_UH_le_pCoreOf h331 h1222 hH hHZ hsolv hS3 ⟨h.2, hh⟩
      have e : h' = h := Subtype.ext he
      rw [← e]
      exact hh'
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)⟩

end Setting

end CFSG.Quasithin.H13.A5
