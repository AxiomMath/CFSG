module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4311Set
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA

public section

namespace CFSG.Quasithin.H13.Ch4.Setting4311

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G}
  {t : G} {m : ℕ} {F : Type} [Field F] [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)}
  {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)} {W' : Submodule F (Fin 3 → F)}
  {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G}

omit [Fintype F] in
theorem le_commutator_sup_centralizer' {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

omit [Finite G] [Fintype F] in
theorem eq_one_of_sq_eq_one {ν : Fˣ} (hν : Odd (orderOf ν)) (h : ν ^ 2 = 1) : ν = 1 := by
  have hd : orderOf ν ∣ 2 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · rw [h2] at hν
    exact absurd hν (by decide)

variable (s : Setting4311 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y)
include s

theorem charP : CharP F 2 :=
  charP_of_card_eq_prime_pow (by rw [s.card_F])

theorem ZS_le_U : ZS ≤ u4311 I K := by
  rw [s.ZS_eq]
  exact inf_le_left.trans s.V_le

theorem K₂_le_K : K₂ ≤ K := by
  rw [s.K₂_eq]
  exact (perfectCore_le _).trans inf_le_left

theorem K₂_le_centralizer : K₂ ≤ Subgroup.centralizer (ZS : Set G) := by
  rw [s.K₂_eq]
  exact (perfectCore_le _).trans inf_le_right

theorem K₂_perfect : ⁅K₂, K₂⁆ = K₂ := by
  rw [s.K₂_eq]
  exact perfectCore_perfect _

theorem T_le_normalizer_ZS : T ≤ Subgroup.normalizer (ZS : Set G) := by
  intro x hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := s.sk.base.hyp.normal (s.sk.base.hyp.T_le hx)
  have hxH : T ⊓ H ⊓ L = T ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr (s.sk.L_le_K.trans (le_of_mem_cComp s.sk.cComp))]
  rw [s.ZS_eq]
  refine mem_normalizer_inf (s.sk.T_le_normalizer_v432 hx) ?_
  rw [hxH]
  exact A4.mem_normalizer_centralizer (mem_normalizer_inf (Subgroup.le_normalizer hx) hxL)

theorem S_le_normalizer_K₂ : T ⊓ H ≤ Subgroup.normalizer (K₂ : Set G) := by
  intro x hx
  rw [s.K₂_eq]
  exact normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf (s.sk.S_le_normalizer hx)
    (A4.mem_normalizer_centralizer (s.T_le_normalizer_ZS hx.1)))

theorem α_zpow (j : ℤ) :
    α ⟨y ^ j, Subgroup.zpow_mem _ s.y_mem j⟩ =
      specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor (μ ^ j)) := by
  have h : (⟨y ^ j, Subgroup.zpow_mem _ s.y_mem j⟩ : ↥K) = ⟨y, s.y_mem⟩ ^ j := by
    apply Subtype.ext
    simp
  rw [h, map_zpow, s.α_y, ← map_zpow, ← map_zpow]

theorem eq_one_of_α_eq_one {y' : G} (hy' : y' ∈ Subgroup.zpowers y) (hyK : y' ∈ K)
    (h : α ⟨y', hyK⟩ = 1) : y' = 1 := by
  have h1 : (⟨y', hyK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← s.modO2.2]
    exact h
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, h1⟩
  have ha' : y' ^ 2 ^ a = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : ↥K) : G)) ha
    simpa using this
  have hd1 : orderOf y' ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have hd2 : orderOf y' ∣ orderOf y := orderOf_dvd_of_mem_zpowers hy'
  have hcop : Nat.Coprime (2 ^ a) (orderOf y) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr s.y_odd)
  have h1' : orderOf y' = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact orderOf_eq_one_iff.mp h1'

theorem odd_orderOf_μ_zpow (j : ℤ) : Odd (orderOf (μ ^ j)) := by
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by have := s.two_le; omega⟩)
      odd_one
  have hd : orderOf (μ ^ j) ∣ orderOf μ :=
    orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers μ j)
  rw [s.μ_order] at hd
  exact Odd.of_dvd_nat hodd hd

theorem sq_ne_one_of_ne_one {j : ℤ} (hy : y ^ j ≠ 1) : (μ ^ j) ^ 2 ≠ 1 := by
  intro h2
  apply hy
  have h1 := eq_one_of_sq_eq_one (s.odd_orderOf_μ_zpow j) h2
  refine s.eq_one_of_α_eq_one (Subgroup.zpow_mem_zpowers y j) (Subgroup.zpow_mem _ s.y_mem j) ?_
  rw [s.α_zpow, h1, map_one, map_one]

theorem orderOf_y : orderOf y = 2 ^ m - 1 := by
  have hyK := s.y_mem
  have h1 : orderOf (α ⟨y, hyK⟩) = orderOf μ := by
    rw [s.α_y, MulEquiv.orderOf_eq, orderOf_injective SL3Pt.tor SL3Pt.tor_injective]
  rw [← s.μ_order, ← h1]
  apply le_antisymm
  · apply Nat.le_of_dvd (orderOf_pos _)
    apply orderOf_dvd_of_pow_eq_one
    have hpow := pow_orderOf_eq_one (α ⟨y, hyK⟩)
    rw [← map_pow] at hpow
    have h2 : y ^ orderOf (α ⟨y, hyK⟩) ∈ K := Subgroup.pow_mem _ hyK _
    have h3 : (⟨y, hyK⟩ : ↥K) ^ orderOf (α ⟨y, hyK⟩) = ⟨y ^ orderOf (α ⟨y, hyK⟩), h2⟩ := by
      apply Subtype.ext
      simp
    rw [h3] at hpow
    exact s.eq_one_of_α_eq_one (Subgroup.npow_mem_zpowers y _) h2 hpow
  · apply Nat.le_of_dvd (orderOf_pos _)
    have h4 := orderOf_map_dvd α ⟨y, hyK⟩
    have h5 : orderOf (⟨y, hyK⟩ : ↥K) = orderOf y := (Subgroup.orderOf_coe _).symm
    rw [h5] at h4
    exact h4

theorem card_Y : Nat.card ↥(Subgroup.zpowers y) = 2 ^ m - 1 := by
  rw [Nat.card_zpowers, s.orderOf_y]

theorem Y_le_K : Subgroup.zpowers y ≤ K := (Subgroup.zpowers_le).mpr s.y_mem

theorem β_conj_zpow (j : ℤ) (u v : ↥(u4311 I K)) (huv : (v : G) = y ^ j * u * (y ^ j)⁻¹) :
    Multiplicative.toAdd (β v) =
      ((SL3Pt.tor (μ ^ j) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (β u) := by
  have h := s.β_act ⟨y ^ j, Subgroup.zpow_mem _ s.y_mem j⟩ u v (by simpa using huv)
  rw [h, s.α_zpow, specialLinearGroupEquivStatedSL_coe]

theorem Y_le_normalizer_ZS : Subgroup.zpowers y ≤ Subgroup.normalizer (ZS : Set G) := by
  rw [Subgroup.zpowers_le]
  apply mem_normalizer_of_map_conj_le
  rintro _ ⟨z, hz, rfl⟩
  have hzU := s.ZS_le_U hz
  have hyU := s.K_U s.y_mem
  let v : ↥(u4311 I K) := ⟨y * z * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyU z).mp hzU⟩
  have h1 := s.β_conj_zpow 1 ⟨z, hzU⟩ v (by simp [v])
  obtain ⟨c, hc⟩ := (s.ZS_iff ⟨z, hzU⟩).mp hz
  have h2 : (v : G) ∈ ZS := by
    refine (s.ZS_iff v).mpr ⟨c * ((μ ^ (1 : ℤ))⁻¹ : Fˣ) ^ 2, ?_⟩
    rw [h1, hc, Matrix.mulVec_smul, SL3Pt.tor_mulVec_e0, smul_smul, mul_comm]
  exact h2

theorem Y_le_normalizer_K₂ : Subgroup.zpowers y ≤ Subgroup.normalizer (K₂ : Set G) := by
  intro x hx
  rw [s.K₂_eq]
  exact normalizer_le_normalizer_perfectCore _ (mem_normalizer_inf
    (Subgroup.le_normalizer (s.Y_le_K hx))
    (A4.mem_normalizer_centralizer (s.Y_le_normalizer_ZS hx)))

theorem Y_faithful {y' : G} (hy' : y' ∈ Subgroup.zpowers y)
    (hc : ∀ z ∈ ZS, y' * z * y'⁻¹ = z) : y' = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
  obtain ⟨z₀, hz₀⟩ := s.β_bij.2 (Multiplicative.ofAdd ![1, 0, 0])
  have hz₀Z : (z₀ : G) ∈ ZS := (s.ZS_iff z₀).mpr ⟨1, by rw [hz₀, toAdd_ofAdd, one_smul]⟩
  have h1 := s.β_conj_zpow j z₀ z₀ (hc z₀ hz₀Z).symm
  rw [hz₀, toAdd_ofAdd, SL3Pt.tor_mulVec_e0] at h1
  have h2 : ((((μ ^ j)⁻¹ : Fˣ) : F) ^ 2 - 1) • (![1, 0, 0] : Fin 3 → F) = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : (((μ ^ j)⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    have := congrFun h2 0
    simpa [sub_eq_zero] using this
  by_contra hne
  apply s.sq_ne_one_of_ne_one hne
  have h4 : ((μ ^ j)⁻¹) ^ 2 = 1 := Units.ext (by simpa using h3)
  rw [inv_pow, inv_eq_one] at h4
  exact h4

theorem Y_fpf_U {y' : G} (hy' : y' ∈ Subgroup.zpowers y) (hy1 : y' ≠ 1) {u : G}
    (hu : u ∈ u4311 I K) (hfix : y' * u * y'⁻¹ = u) : u = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
  have h1 := s.β_conj_zpow j ⟨u, hu⟩ ⟨u, hu⟩ hfix.symm
  have h2 := SL3Pt.eq_zero_of_tor_mulVec (s.sq_ne_one_of_ne_one hy1) h1.symm
  have h3 : β ⟨u, hu⟩ = β 1 := by
    rw [map_one]
    exact Multiplicative.toAdd.injective h2
  exact congrArg (fun x : ↥(u4311 I K) => (x : G)) (s.β_bij.1 h3)

theorem Y_fpf_Q {y' : G} (hy' : y' ∈ Subgroup.zpowers y) (hy1 : y' ≠ 1) {q : G}
    (hq : q ∈ q4311 I K) (hfix : y' * q * y'⁻¹ * q⁻¹ ∈ u4311 I K) : q ∈ u4311 I K := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
  obtain ⟨hKQ, -, β₂, -, hβ₂k, hβ₂a⟩ := s.dualQ
  have hyK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
  let v : ↥(q4311 I K) := ⟨y ^ j * q * (y ^ j)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hKQ hyK) q).mp hq⟩
  have hvq : β₂ v = β₂ ⟨q, hq⟩ := by
    have hmem : v * (⟨q, hq⟩ : ↥(q4311 I K))⁻¹ ∈ β₂.ker := by
      rw [hβ₂k, Subgroup.mem_subgroupOf]
      exact hfix
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hmem
    exact hmem
  have hzero : ∀ i, Multiplicative.toAdd (β₂ ⟨q, hq⟩) i = 0 := by
    intro i
    have h1 := hβ₂a ⟨y ^ j, hyK⟩ ⟨q, hq⟩ v (by simp [v]) i
    rw [hvq, s.α_zpow] at h1
    have hmat : moduleAct true ((specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor (μ ^ j)) :
        ↥(StatedSL 3 F)) : GL (Fin 3) F) =
        ((SL3Pt.tor (μ ^ j)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      simp only [moduleAct, ↓reduceIte]
      rw [← Subgroup.coe_inv, ← map_inv,
        specialLinearGroupEquivStatedSL_coe, SL3Pt.tor_inv_transpose]
    rw [hmat] at h1
    have hne : ((μ ^ j)⁻¹) ^ 2 ≠ 1 := by
      rw [inv_pow, Ne, inv_eq_one]
      exact s.sq_ne_one_of_ne_one hy1
    exact SL3Pt.eq_zero_of_tor_mulVec hne h1.symm
  have h3 : β₂ ⟨q, hq⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    exact hzero i
  have h4 : (⟨q, hq⟩ : ↥(q4311 I K)) ∈ β₂.ker := h3
  rw [hβ₂k, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem α_mem_stE0 {k : G} (hk : k ∈ K₂) : α ⟨k, s.K₂_le_K hk⟩ ∈ stE0 F := by
  rw [← s.K₂_map]
  exact ⟨⟨k, s.K₂_le_K hk⟩, hk, rfl⟩

@[expose] noncomputable def αK₂ : ↥K₂ →* ↥(stE0 F) :=
  (α.comp (Subgroup.inclusion s.K₂_le_K)).codRestrict (stE0 F) (fun k => s.α_mem_stE0 k.2)

theorem coe_αK₂ (k : ↥K₂) : ((s.αK₂ k : ↥(stE0 F)) : ↥(StatedSL 3 F)) =
    α ⟨k, s.K₂_le_K k.2⟩ := rfl

@[expose] noncomputable def levi : ↥K₂ →* SL(2, F) :=
  (Vol2.KGNat.leviHom F).comp ((stE0Equiv F).toMonoidHom.comp s.αK₂)

theorem αK₂_surjective : Function.Surjective s.αK₂ := by
  rintro ⟨x, hx⟩
  rw [← s.K₂_map] at hx
  obtain ⟨⟨k, hkK⟩, hk, rfl⟩ := hx
  exact ⟨⟨k, hk⟩, rfl⟩

theorem levi_surjective : Function.Surjective s.levi :=
  Vol2.KGNat.leviHom_surjective.comp ((stE0Equiv F).surjective.comp s.αK₂_surjective)

theorem ker_levi : s.levi.ker = CFSG.pCore 2 ↥K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  apply le_antisymm
  · try with_reducible rfl
    refine CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker _) fun w => ?_
    have hw : s.levi w = 1 := w.2
    have hrad : ((stE0Equiv F (s.αK₂ w) : ↥(Vol2.KGNat.stabE0 F)) :
        Matrix.SpecialLinearGroup (Fin 3) F) ∈ Vol2.Ch11.SecS.C11P9A.rad1 F :=
      ⟨_, hw, rfl⟩
    have hsq := Vol2.Ch11.SecS.C11P9A.sq_eq_one_of_mem_rad1 hrad
    have hsq' : s.αK₂ ((w : ↥K₂) ^ 2) = 1 := by
      rw [map_pow]
      apply (stE0Equiv F).injective
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, hsq]
      rfl
    have hα1 : α ⟨((w : ↥K₂) ^ 2 : ↥K₂), s.K₂_le_K ((w : ↥K₂) ^ 2).2⟩ = 1 := by
      have := congrArg Subtype.val hsq'
      rw [coe_αK₂] at this
      exact this
    have hker : (⟨((w : ↥K₂) ^ 2 : ↥K₂), s.K₂_le_K ((w : ↥K₂) ^ 2).2⟩ : ↥K) ∈
        CFSG.pCore 2 ↥K := by
      rw [← s.modO2.2]
      exact hα1
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup ⟨_, hker⟩
    refine ⟨a + 1, Subtype.ext (Subtype.ext ?_)⟩
    have ha' := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => ((x : ↥K) : G)) ha
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at ha' ⊢
    rw [pow_succ', pow_mul]
    exact ha'
  ·
    have hN : ((CFSG.pCore 2 ↥K₂).map s.levi).Normal :=
      (CFSG.pCore_normal : (CFSG.pCore 2 ↥K₂).Normal).map _ s.levi_surjective
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥K₂).map s.levi) :=
      (CFSG.pCore_isPGroup).map s.levi
    have h := Vol2.KGNat.eq_bot_of_normal_isPGroup_SL2 hP
    rw [Subgroup.map_eq_bot_iff] at h
    exact h

theorem commutator_Y_mem {k y' : G} (hk : k ∈ K₂) (hy' : y' ∈ Subgroup.zpowers y) :
    y' * k * y'⁻¹ * k⁻¹ ∈ pCoreOf 2 K₂ := by
  have hyN := s.Y_le_normalizer_K₂ hy'
  have hck : y' * k * y'⁻¹ ∈ K₂ := (Subgroup.mem_normalizer_iff.mp hyN k).mp hk
  have hw : y' * k * y'⁻¹ * k⁻¹ ∈ K₂ := K₂.mul_mem hck (K₂.inv_mem hk)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
  have hlev : s.levi ⟨y ^ j * k * (y ^ j)⁻¹, hck⟩ = s.levi ⟨k, hk⟩ := by
    set B := stE0Equiv F (s.αK₂ ⟨k, hk⟩) with hBdef
    have hB := SL3Pt.leviHom_conj_tor (μ ^ j) B
    show (Vol2.KGNat.leviHom F) ((stE0Equiv F) (s.αK₂ ⟨_, hck⟩)) = (Vol2.KGNat.leviHom F) B
    rw [← hB]
    congr 1
    have hyK : y ^ j ∈ K := Subgroup.zpow_mem _ s.y_mem j
    have e1 : (⟨y ^ j * k * (y ^ j)⁻¹, s.K₂_le_K hck⟩ : ↥K) =
        ⟨y ^ j, hyK⟩ * ⟨k, s.K₂_le_K hk⟩ * (⟨y ^ j, hyK⟩)⁻¹ := rfl
    have hconj : α ⟨y ^ j * k * (y ^ j)⁻¹, s.K₂_le_K hck⟩ =
        specialLinearGroupEquivStatedSL 3 F (SL3Pt.tor (μ ^ j) *
          (B : Matrix.SpecialLinearGroup (Fin 3) F) * (SL3Pt.tor (μ ^ j))⁻¹) := by
      rw [e1, map_mul, map_mul, map_inv, s.α_zpow, map_mul, map_mul, map_inv, hBdef,
        slE_stE0Equiv, s.coe_αK₂]
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_stE0Equiv, s.coe_αK₂, hconj, specialLinearGroupEquivStatedSL_coe]
  have h1 : (⟨y ^ j * k * (y ^ j)⁻¹ * k⁻¹, hw⟩ : ↥K₂) ∈ s.levi.ker := by
    rw [MonoidHom.mem_ker]
    have e2 : (⟨y ^ j * k * (y ^ j)⁻¹ * k⁻¹, hw⟩ : ↥K₂) =
        ⟨y ^ j * k * (y ^ j)⁻¹, hck⟩ * (⟨k, hk⟩ : ↥K₂)⁻¹ := rfl
    rw [e2, map_mul, map_inv, hlev, mul_inv_cancel]
  rw [s.ker_levi] at h1
  exact (mem_pCoreOf_iff' _).mpr h1

theorem y_ne_one : y ≠ 1 := by
  intro h
  have h1 := s.orderOf_y
  rw [h, orderOf_one] at h1
  have h2 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) s.two_le
  omega

theorem q4311_inf_centralizer_Y :
    q4311 I K ⊓ Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨hq, hqC⟩
  have hyq : y * q * y⁻¹ = q := by
    have := Subgroup.mem_centralizer_iff.mp hqC y (Subgroup.mem_zpowers y)
    rw [this, mul_inv_cancel_right]
  have hqU : q ∈ u4311 I K := s.Y_fpf_Q (Subgroup.mem_zpowers y) s.y_ne_one hq (by
    rw [hyq, mul_inv_cancel]
    exact Subgroup.one_mem _)
  rw [Subgroup.mem_bot]
  exact s.Y_fpf_U (Subgroup.mem_zpowers y) s.y_ne_one hqU hyq

theorem q4311_eq_commutator : q4311 I K = ⁅q4311 I K, Subgroup.zpowers y⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKQ, -⟩ := s.dualQ
  have hYQ : Subgroup.zpowers y ≤ Subgroup.normalizer ((q4311 I K : Subgroup G) : Set G) :=
    s.Y_le_K.trans hKQ
  have hsolv : Group.IsSolvable ↥(q4311 I K) := by
    have := (isPGroup_q4311 I K).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers y)) (Nat.card ↥(q4311 I K)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_q4311 I K)
    rw [ha, s.card_Y]
    refine Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr ?_)
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by have := s.two_le; omega⟩) odd_one
  have h1 := le_commutator_sup_centralizer' hYQ hsolv hcop
  rw [s.q4311_inf_centralizer_Y, sup_bot_eq] at h1
  refine le_antisymm h1 ?_
  rw [Subgroup.commutator_le]
  intro q hq x hx
  have hx' : x * q⁻¹ * x⁻¹ ∈ q4311 I K :=
    (Subgroup.mem_normalizer_iff.mp (hYQ hx) q⁻¹).mp (Subgroup.inv_mem _ hq)
  rw [commutatorElement_def]
  have := Subgroup.mul_mem _ hq hx'
  simpa [mul_assoc] using this

end CFSG.Quasithin.H13.Ch4.Setting4311
