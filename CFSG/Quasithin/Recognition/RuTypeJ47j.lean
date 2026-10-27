module

public import CFSG.Quasithin.Recognition.RuTypeJ47i
public import CFSG.Quasithin.Recognition.RuTypeJ44c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Sigma47

section Sylow

variable {X : Type*} [Group X] [Finite X]

@[expose] noncomputable def zpowersSylow {p : ℕ} [hp : Fact p.Prime] {K : Subgroup X}
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x : X} (hx : x ∈ K) (hxp : orderOf x = p) : Sylow p K := by
  have hle : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).mpr hx
  have hcard : Nat.card ((Subgroup.zpowers x).subgroupOf K) = p := by
    rw [card_subgroupOf_of_le hle, Nat.card_zpowers, hxp]
  have h1 : IsPGroup p ((Subgroup.zpowers x).subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have h2 : ¬ p ∣ ((Subgroup.zpowers x).subgroupOf K).index := by
    intro hdvd
    apply hK
    have h := Subgroup.card_mul_index ((Subgroup.zpowers x).subgroupOf K)
    rw [hcard] at h
    rw [← h, pow_two]
    exact Nat.mul_dvd_mul_left p hdvd
  exact h1.toSylow h2

omit [Finite X] in
theorem coe_zpowersSylow {p : ℕ} [hp : Fact p.Prime] {K : Subgroup X}
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x : X} (hx : x ∈ K) (hxp : orderOf x = p) :
    ((zpowersSylow hK hx hxp : Sylow p K) : Subgroup K) = (Subgroup.zpowers x).subgroupOf K :=
  rfl

theorem relIndex_normalizer_zpowers_modEq_one {p : ℕ} [hp : Fact p.Prime] {K : Subgroup X}
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x : X} (hx : x ∈ K) (hxp : orderOf x = p) :
    (K ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set X)).relIndex K ≡ 1 [MOD p] := by
  have hle : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).mpr hx
  have h0 := card_sylow_modEq_one p K
  rw [(zpowersSylow hK hx hxp).card_eq_index_normalizer] at h0
  have h : (Subgroup.normalizer (((Subgroup.zpowers x).subgroupOf K : Subgroup K) :
      Set K)).index ≡ 1 [MOD p] := h0
  have e : Subgroup.normalizer (((Subgroup.zpowers x).subgroupOf K : Subgroup K) : Set K) =
      (Subgroup.normalizer (Subgroup.zpowers x : Set X)).subgroupOf K :=
    (Subgroup.subgroupOf_normalizer_eq hle).symm
  rw [e] at h
  have e2 : (K ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set X)).relIndex K =
      ((Subgroup.normalizer (Subgroup.zpowers x : Set X)).subgroupOf K).index := by
    rw [Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  rw [e2]
  exact h

theorem exists_conj_zpowers {p : ℕ} [hp : Fact p.Prime] {K : Subgroup X}
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x y : X} (hx : x ∈ K) (hy : y ∈ K) (hxp : orderOf x = p)
    (hyp : orderOf y = p) : ∃ g ∈ K, y ∈ Subgroup.zpowers (g * x * g⁻¹) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K (zpowersSylow hK hx hxp) (zpowersSylow hK hy hyp)
  have hy' : (⟨y, hy⟩ : K) ∈ ((g • zpowersSylow hK hx hxp : Sylow p K) : Subgroup K) := by
    rw [hg, coe_zpowersSylow, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  rw [Sylow.coe_subgroup_smul, coe_zpowersSylow, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    at hy'
  rw [Subgroup.mem_subgroupOf] at hy'
  refine ⟨g, g.2, ?_⟩
  have e : (((MulAut.conj g)⁻¹ • (⟨y, hy⟩ : K) : K) : X) = (g : X)⁻¹ * y * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rw [e] at hy'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [conj_zpow, hk]
  group

theorem exists_conj_mem_of_sylow {p : ℕ} [hp : Fact p.Prime] {K S : Subgroup X} (hSK : S ≤ K)
    (hS : IsPGroup p S) (hidx : ¬ p ∣ S.relIndex K) {y : X} (hy : y ∈ K) (hyp : y ^ p = 1) :
    ∃ g ∈ K, (g : X)⁻¹ * y * g ∈ S := by
  have hS' : IsPGroup p (S.subgroupOf K) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  set P := hS'.toSylow hidx
  have hzp : IsPGroup p (Subgroup.zpowers (⟨y, hy⟩ : K)) := by
    have h1 : orderOf (⟨y, hy⟩ : K) ∣ p ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hyp))
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P Q
  have hy' : (⟨y, hy⟩ : K) ∈ ((g • P : Sylow p K) : Subgroup K) := by
    rw [hg]
    exact hQ (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
  refine ⟨g, g.2, ?_⟩
  have hP : ((P : Sylow p K) : Subgroup K) = S.subgroupOf K := IsPGroup.toSylow_coe _ _
  rw [hP, Subgroup.mem_subgroupOf] at hy'
  have e : (((MulAut.conj g)⁻¹ • (⟨y, hy⟩ : K) : K) : X) = (g : X)⁻¹ * y * g := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
    simp
  rwa [e] at hy'

omit [Finite X] in
theorem relIndex_mul_card_of_le {H K : Subgroup X} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  rw [Subgroup.relIndex, ← card_subgroupOf_of_le h]
  exact Subgroup.index_mul_card _

end Sylow

namespace Sigma47

theorem eq_one_of_comm_of_pow_five : ∀ σ c : SigmaL2F4, σ ^ 5 = 1 → σ ≠ 1 → c * σ = σ * c →
    c * c = 1 → c = 1 := by
  decide +kernel

end Sigma47

namespace RuDataM

variable {G : Type} [Group G] [Finite G] {M : RuDataM G}

theorem phiG_ne_one_of_pow_five (M : RuDataM G) {w : G} (hwH : w ∈ ruH M.T) (hw5 : w ^ 5 = 1)
    (hw1 : w ≠ 1) : M.phiG w ≠ 1 := by
  intro h
  have h1 := M.pow_eq_one_of_mem_Q ((M.phiG_eq_one_iff hwH).mp h)
  apply hw1
  have := (pow_gcd_eq_one (a := w)).mpr ⟨hw5, h1⟩
  rwa [show Nat.gcd 5 2048 = 1 by norm_num, pow_one] at this

theorem not_comm_of_pow_five (M : RuDataM G) {x i : G} (hxH : x ∈ ruH M.T) (hx5 : x ^ 5 = 1)
    (hx1 : x ≠ 1) (hiH : i ∈ ruH M.T) (hi2 : i * i = 1) (hi1 : M.phiG i ≠ 1) : x * i ≠ i * x := by
  intro hxi
  apply hi1
  refine eq_one_of_comm_of_pow_five (M.phiG x) (M.phiG i) ?_
    (M.phiG_ne_one_of_pow_five hxH hx5 hx1) ?_ ?_
  · rw [← M.phiG_pow hxH, hx5]; exact M.phiG_one47
  · rw [← M.phiG_mul hiH hxH, ← M.phiG_mul hxH hiH, hxi]
  · rw [← M.phiG_mul hiH hiH, hi2]; exact M.phiG_one47

namespace Conf47

variable (C : Conf47 M)

attribute [local instance] fact_prime_five

theorem F1_le_normalizer_Q : C.F1 ≤ Subgroup.normalizer (ruQ M.T : Set G) := fun _ hf =>
  mem_normalizer_of_conj_mem fun _ hq => M.conj_mem_Q (C.F1_le_H hf) hq

theorem card_F1_sup_Q : Nat.card ↥(C.F1 ⊔ ruQ M.T) = 2 ^ 13 * 5 := by
  have h := card_sup_mul_inf_of_normalizes C.F1_le_normalizer_Q
  rw [C.card_F1_inf_Q, C.card_F1, M.toRuData.card_Q] at h
  norm_num at h ⊢
  omega

theorem index_F1_sup_Q : (C.F1.subgroupOf (C.F1 ⊔ ruQ M.T)).index = 2 := by
  have h := relIndex_mul_card_of_le (le_sup_left : C.F1 ≤ C.F1 ⊔ ruQ M.T)
  rw [C.card_F1_sup_Q, C.card_F1] at h
  rw [← Subgroup.relIndex]
  norm_num at h
  omega

theorem mem_F1_of_mem_sup {x : G} (hx : x ∈ C.F1 ⊔ ruQ M.T) (hx5 : x ^ 5 = 1) : x ∈ C.F1 := by
  have h2 := Subgroup.sq_mem_of_index_two C.index_F1_sup_Q ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at h2
  have h2' : x ^ 2 ∈ C.F1 := by simpa using h2
  have e : (x ^ 2) ^ 3 = x := by
    rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ, hx5, one_mul]
  rw [← e]
  exact pow_mem h2' 3

theorem conj_mem_F1_of_mem_Q {q f : G} (hq : q ∈ ruQ M.T) (hf : f ∈ C.F1) :
    q * f * q⁻¹ ∈ C.F1 := by
  have hN := Subgroup.normal_of_index_eq_two C.index_F1_sup_Q
  have h := hN.conj_mem ⟨f, Subgroup.mem_sup_left hf⟩ (by rw [Subgroup.mem_subgroupOf]; exact hf)
    ⟨q, Subgroup.mem_sup_right hq⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem mem_F1_of_powOfG {w : G} (hwH : w ∈ ruH M.T) (hw5 : w ^ 5 = 1)
    (h : PowOfG (M.phiG C.b) (M.phiG w)) : w ∈ C.F1 := by
  obtain ⟨k, hk⟩ := h
  have hbk : C.b ^ (k : ℕ) ∈ ruH M.T := pow_mem C.b_mem_H _
  have hq : (C.b ^ (k : ℕ))⁻¹ * w ∈ ruQ M.T := by
    rw [← M.phiG_eq_one_iff (mul_mem (inv_mem hbk) hwH), M.phiG_mul (inv_mem hbk) hwH,
      M.phiG_inv hbk, M.phiG_pow C.b_mem_H, hk, inv_mul_cancel]
  have hmem : w ∈ C.F1 ⊔ ruQ M.T := by
    have e : w = C.b ^ (k : ℕ) * ((C.b ^ (k : ℕ))⁻¹ * w) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (pow_mem C.b_mem _)) (Subgroup.mem_sup_right hq)
  exact C.mem_F1_of_mem_sup hmem hw5

noncomputable abbrev NF1 : Subgroup G :=
  C.F1 ⊓ Subgroup.normalizer (Subgroup.zpowers C.b : Set G)

noncomputable abbrev SF1 : Subgroup G := C.NF1 ⊓ Subgroup.centralizer ({C.u} : Set G)

omit [Finite G] in
theorem not_dvd_card_F1 : ¬ 5 ^ 2 ∣ Nat.card C.F1 := by
  rw [C.card_F1]
  norm_num

omit [Finite G] in
theorem zpowers_b_le_NF1 : Subgroup.zpowers C.b ≤ C.NF1 :=
  (Subgroup.zpowers_le).mpr ⟨C.b_mem, Subgroup.le_normalizer (Subgroup.mem_zpowers C.b)⟩

theorem mem_normalizer_of_conj_pow {g : G} (h : ∃ k : ℕ, g * C.b * g⁻¹ = C.b ^ k) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers C.b : Set G) := by
  obtain ⟨k, hk⟩ := h
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← conj_zpow, hk, ← zpow_natCast, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

theorem iEl_mem_SF1 (p : ℕ) : C.iEl p ∈ C.SF1 :=
  ⟨⟨C.iEl_mem p, C.mem_normalizer_of_conj_pow (C.iEl_norm p)⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (C.iEl_comm p)⟩

noncomputable def iFun (p : Fin 16) : C.SF1 := ⟨C.iEl p, C.iEl_mem_SF1 p⟩

theorem iFun_injective : Function.Injective C.iFun := fun p q h =>
  Fin.ext (C.iEl_inj p p.2 q q.2 (congrArg Subtype.val h))

theorem sixteen_le_card_SF1 : 16 ≤ Nat.card C.SF1 := by
  have h := Nat.card_le_card_of_injective C.iFun C.iFun_injective
  simpa using h

omit [Finite G] in
theorem SF1_inf_zpowers : C.SF1 ⊓ Subgroup.zpowers C.b = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨-, hyu⟩, hyb⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_bot]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyb
  have hu : C.u * C.b ^ k * C.u⁻¹ = (C.b ^ k)⁻¹ := by
    rw [← conj_zpow, C.u_inv_b, inv_zpow]
  have hc : C.u * C.b ^ k * C.u⁻¹ = C.b ^ k := by
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hyu]
    group
  rw [hc] at hu
  have h2 : (C.b ^ k) ^ 2 = 1 := by
    rw [pow_two]
    calc C.b ^ k * C.b ^ k = C.b ^ k * (C.b ^ k)⁻¹ := by rw [← hu]
      _ = 1 := mul_inv_cancel _
  have h5 : (C.b ^ k) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, C.b_pow_five, one_zpow]
  have := (pow_gcd_eq_one (a := C.b ^ k)).mpr ⟨h2, h5⟩
  rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this

theorem card_NF1_dvd :
    Nat.card C.NF1 ∣ 160 := by
  have h1 := Subgroup.card_dvd_of_le (inf_le_left : C.NF1 ≤ C.F1)
  have h2 := Subgroup.card_dvd_of_le (inf_le_right : C.NF1 ≤ _)
  rw [C.card_F1] at h1
  rw [card_normalizer_B5 C.b_mem_H C.orderOf_b] at h2
  have := Nat.dvd_gcd h1 h2
  norm_num at this
  exact this

theorem card_NF1 :
    Nat.card C.NF1 = 80 := by
  have hmod := relIndex_normalizer_zpowers_modEq_one C.not_dvd_card_F1 C.b_mem C.orderOf_b
  have hmul := relIndex_mul_card_of_le (inf_le_left : C.NF1 ≤ C.F1)
  rw [C.card_F1] at hmul
  have hdvd := C.card_NF1_dvd
  have h16 : 16 ≤ Nat.card C.NF1 :=
    C.sixteen_le_card_SF1.trans (Subgroup.card_le_of_le inf_le_left)
  have hmod' : C.NF1.relIndex C.F1 % 5 = 1 := hmod
  norm_num at hmul
  have key : ∀ n r : ℕ, r * n = 20480 → n ∣ 160 → 16 ≤ n → r % 5 = 1 → n = 80 := by
    intro n r h1 h2 h3 h4
    have hn : n ≤ 160 := Nat.le_of_dvd (by norm_num) h2
    interval_cases n <;> omega
  exact key _ _ hmul hdvd h16 hmod'

theorem card_SF1 :
    Nat.card C.SF1 = 16 := by
  have hnorm : C.SF1 ≤ Subgroup.normalizer (Subgroup.zpowers C.b : Set G) :=
    fun _ hx => hx.1.2
  have h := card_sup_mul_inf_of_normalizes hnorm
  rw [C.SF1_inf_zpowers, Subgroup.card_bot, mul_one, Nat.card_zpowers, C.orderOf_b] at h
  have hle : C.SF1 ⊔ Subgroup.zpowers C.b ≤ C.NF1 := sup_le inf_le_left C.zpowers_b_le_NF1
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h, C.card_NF1] at hdvd
  have h16 := C.sixteen_le_card_SF1
  have hle16 : Nat.card C.SF1 ≤ 16 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  omega

theorem exists_iEl_eq
    {s : G} (hs : s ∈ C.SF1) : ∃ p < 16, C.iEl p = s := by
  have hcard : Nat.card (Fin 16) = Nat.card C.SF1 := by rw [C.card_SF1, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  have hsurj := (Function.Injective.bijective_of_nat_card_le C.iFun_injective hcard.ge).2
  obtain ⟨p, hp⟩ := hsurj ⟨s, hs⟩
  exact ⟨p, p.2, congrArg Subtype.val hp⟩

theorem isPGroup_SF1 :
    IsPGroup 2 C.SF1 :=
  IsPGroup.of_card (n := 4) (by rw [C.card_SF1]; norm_num)

theorem relIndex_SF1 :
    C.SF1.relIndex C.NF1 = 5 := by
  have h := relIndex_mul_card_of_le (inf_le_left : C.SF1 ≤ C.NF1)
  rw [C.card_SF1, C.card_NF1] at h
  have h' : C.SF1.relIndex C.NF1 * 16 = 5 * 16 := h.trans (by norm_num)
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

theorem exists_conj_of_norm
    {x : G} (hxF : x ∈ C.F1) (hxo : orderOf x = 5) (hux : ∃ k : ℕ, C.u * x * C.u⁻¹ = x ^ k) :
    ∃ g ∈ C.F1, g * C.u = C.u * g ∧ ∃ k : ℕ, (g * C.b * g⁻¹) ^ k = x := by
  have hx5 : x ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxo; norm_num at hxo
  obtain ⟨f, hfF, hfx⟩ := exists_conj_zpowers C.not_dvd_card_F1 C.b_mem hxF C.orderOf_b hxo
  obtain ⟨m, hm⟩ := exists_pow_of_mem_zpowers hfx
  have hfb5 : (f * C.b * f⁻¹) ^ 5 = 1 := by rw [conj_pow, C.b_pow_five]; group
  obtain ⟨r, hr⟩ := exists_pow_pow_eq hfb5 (show (f * C.b * f⁻¹) ^ m ≠ 1 by rw [hm]; exact hx1)
  rw [hm] at hr
  obtain ⟨k, hk⟩ := hux
  have hu'N : f⁻¹ * C.u * f ∈ C.NF1 := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hfF) C.u_mem) hfF,
      C.mem_normalizer_of_conj_pow ?_⟩
    refine ⟨m * k * r, ?_⟩
    calc f⁻¹ * C.u * f * C.b * (f⁻¹ * C.u * f)⁻¹ =
          f⁻¹ * (C.u * (f * C.b * f⁻¹) * C.u⁻¹) * f := by group
      _ = f⁻¹ * (C.u * x * C.u⁻¹) ^ r * f := by rw [← hr, conj_pow]
      _ = f⁻¹ * ((f * C.b * f⁻¹) ^ m) ^ (k * r) * f := by rw [hk, ← pow_mul, hm]
      _ = C.b ^ (m * k * r) := by
          rw [← pow_mul, conj_pow, show m * (k * r) = m * k * r by ring]
          group
  have hu'2 : (f⁻¹ * C.u * f) ^ 2 = 1 := by
    rw [pow_two]
    calc f⁻¹ * C.u * f * (f⁻¹ * C.u * f) = f⁻¹ * (C.u * C.u) * f := by group
      _ = 1 := by rw [C.u_mul_self]; group
  obtain ⟨n, hnN, hnS⟩ := exists_conj_mem_of_sylow (inf_le_left : C.SF1 ≤ C.NF1) C.isPGroup_SF1
    (by rw [C.relIndex_SF1]; norm_num) hu'N hu'2
  obtain ⟨p, hp, hpe⟩ := C.exists_iEl_eq hnS
  have hfn : f * n ∈ C.F1 := mul_mem hfF hnN.1
  have hconj : n⁻¹ * (f⁻¹ * C.u * f) * n = (f * n)⁻¹ * C.u * (f * n) := by group
  have hi2 : C.iEl p * C.iEl p = 1 := by
    rw [hpe, hconj]
    calc (f * n)⁻¹ * C.u * (f * n) * ((f * n)⁻¹ * C.u * (f * n)) =
          (f * n)⁻¹ * (C.u * C.u) * (f * n) := by group
      _ = 1 := by rw [C.u_mul_self]; group
  have hfnH : f * n ∈ ruH M.T := C.F1_le_H hfn
  have hz : (f * n) * M.z * (f * n)⁻¹ = M.z := by
    rw [(M.Z_comm_H M.z_mem_Z hfnH).symm]
    group
  have hun : (f * n)⁻¹ * C.u * (f * n) = C.u := by
    rcases C.iEl_inv p hp hi2 with h | h | h | h <;> rw [hpe, hconj] at h
    · exfalso
      have hu1 : C.u = 1 := by
        calc C.u = (f * n) * ((f * n)⁻¹ * C.u * (f * n)) * (f * n)⁻¹ := by group
          _ = 1 := by rw [h]; group
      apply C.b_ne_inv
      rw [← C.u_inv_b, hu1]
      group
    · exfalso
      apply C.u_ne_z
      calc C.u = (f * n) * ((f * n)⁻¹ * C.u * (f * n)) * (f * n)⁻¹ := by group
        _ = M.z := by rw [h, hz]
    · exact h
    · exfalso
      apply C.conj_u_ne (f * n)⁻¹ (inv_mem hfn)
      rw [inv_inv]
      exact h
  refine ⟨f * n, hfn, ?_, ?_⟩
  · calc (f * n) * C.u = (f * n) * ((f * n)⁻¹ * C.u * (f * n)) := by rw [hun]
      _ = C.u * (f * n) := by group
  ·
    have hnb : n * C.b * n⁻¹ ∈ Subgroup.zpowers C.b :=
      (Subgroup.mem_normalizer_iff.mp hnN.2 C.b).mp (Subgroup.mem_zpowers C.b)
    obtain ⟨e, he⟩ := exists_pow_of_mem_zpowers hnb
    have hg : (f * n) * C.b * (f * n)⁻¹ = (f * C.b * f⁻¹) ^ e := by
      rw [conj_pow, he]
      group
    have hg1 : (f * C.b * f⁻¹) ^ e ≠ 1 := by
      rw [← hg]
      intro h1
      apply C.b_ne_inv
      have hb1 : C.b = 1 := by
        calc C.b = (f * n)⁻¹ * ((f * n) * C.b * (f * n)⁻¹) * (f * n) := by group
          _ = 1 := by rw [h1]; group
      rw [hb1, inv_one]
    obtain ⟨e', he'⟩ := exists_pow_pow_eq hfb5 hg1
    refine ⟨e' * m, ?_⟩
    rw [hg, ← pow_mul, show e * (e' * m) = e * e' * m by ring, pow_mul, pow_mul, he', hm]

theorem exists_mem_F1_conj :
    ∃ w : G, w ^ 5 = 1 ∧ w ≠ 1 ∧ w * C.b = C.b * w ∧ C.j * w * C.j⁻¹ ∈ C.F1 := by
  obtain ⟨D⟩ := C.nonempty_fives
  have hzu : M.z * C.u = C.u * M.z := C.u_comm_z.symm
  have hρ5 : ∀ w : G, w * C.u = C.u * w → w ^ 5 = 1 → w ≠ 1 →
      C.rhoU w ^ 5 = 1 ∧ C.rhoU w ≠ 1 := by
    intro w hw hw5 hw1
    refine ⟨by rw [← C.rhoU_pow hw, hw5, C.rhoU_one], fun h => hw1 ?_⟩
    have h1 := C.pow_eq_one_of_rhoU hw h
    have := (pow_gcd_eq_one (a := w)).mpr ⟨hw5, h1⟩
    rwa [show Nat.gcd 5 2048 = 1 by norm_num, pow_one] at this
  have hρconj : ∀ g w : G, g * C.u = C.u * g → w * C.u = C.u * w →
      C.rhoU (g * w * g⁻¹) = C.rhoU g * C.rhoU w * (C.rhoU g)⁻¹ := by
    intro g w hg hw
    unfold rhoU
    rw [show C.j * (g * w * g⁻¹) * C.j⁻¹ =
        (C.j * g * C.j⁻¹) * (C.j * w * C.j⁻¹) * (C.j * g * C.j⁻¹)⁻¹ by group,
      M.phiG_mul (mul_mem (C.jconj_mem_H hg) (C.jconj_mem_H hw)) (inv_mem (C.jconj_mem_H hg)),
      M.phiG_mul (C.jconj_mem_H hg) (C.jconj_mem_H hw), M.phiG_inv (C.jconj_mem_H hg)]
  have hρz : C.rhoU M.z = M.phiG C.u := by unfold rhoU; rw [C.j_conj_z]
  obtain ⟨d, hd⟩ : ∃ d, d = M.phiG C.u := ⟨_, rfl⟩
  have hd2 : d * d = 1 := by
    rw [hd, ← M.phiG_mul C.u_mem_H C.u_mem_H, C.u_mul_self]
    exact M.phiG_one47
  have hd1 : d ≠ 1 := by rw [hd]; exact C.phiG_u_ne_one
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 = C.j⁻¹ * C.b * C.j := ⟨_, rfl⟩
  have hjw0 : C.j * w0 * C.j⁻¹ = C.b := by rw [hw0]; group
  have hw0u : w0 * C.u = C.u * w0 := by
    have hbz := C.b_comm_z
    calc w0 * C.u = C.j⁻¹ * (C.b * (C.j * C.u * C.j⁻¹)) * C.j := by rw [hw0]; group
      _ = C.j⁻¹ * (C.b * M.z) * C.j := by rw [C.j_conj_u]
      _ = C.j⁻¹ * (M.z * C.b) * C.j := by rw [hbz]
      _ = C.j⁻¹ * (C.j * C.u * C.j⁻¹ * C.b) * C.j := by rw [C.j_conj_u]
      _ = C.u * w0 := by rw [hw0]; group
  have hw05 : w0 ^ 5 = 1 := by
    rw [hw0, show C.j⁻¹ * C.b * C.j = C.j⁻¹ * C.b * C.j⁻¹⁻¹ by group, conj_pow, C.b_pow_five]
    group
  have hw01 : w0 ≠ 1 := fun h => C.b_ne_inv (by
    have : C.b = 1 := by rw [← hjw0, h]; group
    rw [this, inv_one])
  have hρw0 : C.rhoU w0 = M.phiG C.b := by unfold rhoU; rw [hjw0]
  obtain ⟨h15, h11⟩ := hρ5 D.bu D.bu_comm D.bu_pow D.bu_ne
  obtain ⟨h25, h21⟩ := hρ5 D.bu' D.bu'_comm D.bu'_pow D.bu'_ne
  obtain ⟨h05, h01⟩ := hρ5 w0 hw0u hw05 hw01
  have hNBu : NormBy d (C.rhoU D.bu) := by
    refine ⟨4, ?_⟩
    show d * C.rhoU D.bu * d⁻¹ = C.rhoU D.bu ^ 4
    rw [hd, ← hρz, ← hρconj M.z D.bu hzu D.bu_comm, D.z_inv_bu,
      show D.bu⁻¹ = D.bu ^ 4 by
        calc D.bu⁻¹ = D.bu ^ 5 * D.bu⁻¹ := by rw [D.bu_pow, one_mul]
          _ = D.bu ^ 4 := by group,
      C.rhoU_pow D.bu_comm]
  have hNBu' : NormBy d (C.rhoU D.bu') := by
    obtain ⟨k, hk⟩ := D.z_norm_bu'
    obtain ⟨k', hk'⟩ := powOfG_pow (C.rhoU D.bu') k h25
    refine ⟨k', ?_⟩
    rw [hd, ← hρz, ← hρconj M.z D.bu' hzu D.bu'_comm, hk, C.rhoU_pow D.bu'_comm, hk']
  have hNb : NormBy d (M.phiG C.b) := by
    refine ⟨4, ?_⟩
    show d * M.phiG C.b * d⁻¹ = M.phiG C.b ^ 4
    rw [hd, ← M.phiG_conj C.u_mem_H C.b_mem_H, C.u_inv_b,
      show C.b⁻¹ = C.b ^ 4 by
        calc C.b⁻¹ = C.b ^ 5 * C.b⁻¹ := by rw [C.b_pow_five, one_mul]
          _ = C.b ^ 4 := by group,
      M.phiG_pow C.b_mem_H]
  have hNw0 : NormBy d (C.rhoU w0) := by rw [hρw0]; exact hNb
  rcases powOf_of_two_classes hd2 hd1 h15 h11 hNBu h25 h21 hNBu' D.not_powOfG_bu h05 h01 hNw0
    with h | h
  ·
    have h' := powOfG_symm h15 h01 h
    rw [hρw0] at h'
    exact ⟨D.bu, D.bu_pow, D.bu_ne, D.bu_comm_b, C.mem_F1_of_powOfG (C.jconj_mem_H D.bu_comm)
      (by rw [conj_pow, D.bu_pow]; group) h'⟩
  ·
    exfalso
    have h' := powOfG_symm h25 h01 h
    rw [hρw0] at h'
    obtain ⟨x, hx⟩ : ∃ x, x = C.j * D.bu' * C.j⁻¹ := ⟨_, rfl⟩
    have hxH : x ∈ ruH M.T := by rw [hx]; exact C.jconj_mem_H D.bu'_comm
    have hx5 : x ^ 5 = 1 := by rw [hx, conj_pow, D.bu'_pow]; group
    have hx1 : x ≠ 1 := by
      intro h1
      apply D.bu'_ne
      calc D.bu' = C.j⁻¹ * x * C.j := by rw [hx]; group
        _ = 1 := by rw [h1]; group
    have hxo : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    have hxF : x ∈ C.F1 := C.mem_F1_of_powOfG hxH hx5 (by rw [hx]; exact h')
    have hux : ∃ k : ℕ, C.u * x * C.u⁻¹ = x ^ k := by
      obtain ⟨k, hk⟩ := D.z_norm_bu'
      refine ⟨k, ?_⟩
      rw [← C.j_conj_z, hx, conj_pow, ← hk]
      group
    have hxu : C.u * x * C.u⁻¹ = x⁻¹ :=
      inv_of_normalizes_zpowers C.u_mul_self hx5 hux (fun h => M.not_comm_of_pow_five hxH hx5
        hx1 C.u_mem_H C.u_mul_self C.phiG_u_ne_one h.symm)
    have hzx : M.z * x = x * M.z := M.Z_comm_H M.z_mem_Z hxH
    have htx : C.t * x * C.t⁻¹ = x⁻¹ := by
      show C.u * M.z * x * (C.u * M.z)⁻¹ = x⁻¹
      calc C.u * M.z * x * (C.u * M.z)⁻¹ = C.u * (M.z * x) * M.z⁻¹ * C.u⁻¹ := by group
        _ = C.u * x * C.u⁻¹ := by rw [hzx]; group
        _ = x⁻¹ := hxu
    have hK := card_P5_inf_centralizer hxH hxo C.isConj_t C.t_mul_self htx
    obtain ⟨c, -, hc5, -, hcgen⟩ := exists_gen_of_card_five hK
    obtain ⟨g, hgF, hgu, kk, hkk⟩ := C.exists_conj_of_norm hxF hxo hux
    have hgH : g ∈ ruH M.T := C.F1_le_H hgF
    have hgz : g * M.z = M.z * g := (M.Z_comm_H M.z_mem_Z hgH).symm
    have hgt : g * C.t = C.t * g := by
      show g * (C.u * M.z) = C.u * M.z * g
      calc g * (C.u * M.z) = (g * C.u) * M.z := by group
        _ = C.u * (g * M.z) := by rw [hgu]; group
        _ = C.u * M.z * g := by rw [hgz]; group
    have hbtt := D.bt_comm
    obtain ⟨w1, hw1⟩ : ∃ w1, w1 = C.j * D.bt * C.j⁻¹ := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2, w2 = g * D.bt * g⁻¹ := ⟨_, rfl⟩
    have hw1t : w1 * C.t = C.t * w1 := by
      have hjt := C.j_comm_t
      have hjit : C.j⁻¹ * C.t = C.t * C.j⁻¹ :=
        (Commute.inv_left (show Commute C.j C.t from hjt)).eq
      calc w1 * C.t = C.j * D.bt * (C.j⁻¹ * C.t) := by rw [hw1]; group
        _ = C.j * (D.bt * C.t) * C.j⁻¹ := by rw [hjit]; group
        _ = (C.j * C.t) * D.bt * C.j⁻¹ := by rw [hbtt]; group
        _ = C.t * w1 := by rw [hjt, hw1]; group
    have hw2t : w2 * C.t = C.t * w2 := by
      have hgit : g⁻¹ * C.t = C.t * g⁻¹ := (Commute.inv_left (show Commute g C.t from hgt)).eq
      calc w2 * C.t = g * D.bt * (g⁻¹ * C.t) := by rw [hw2]; group
        _ = g * (D.bt * C.t) * g⁻¹ := by rw [hgit]; group
        _ = (g * C.t) * D.bt * g⁻¹ := by rw [hbtt]; group
        _ = C.t * w2 := by rw [hgt, hw2]; group
    have hw1x : w1 * x = x * w1 := by
      rw [hw1, hx]
      calc C.j * D.bt * C.j⁻¹ * (C.j * D.bu' * C.j⁻¹) = C.j * (D.bt * D.bu') * C.j⁻¹ := by
            group
        _ = C.j * (D.bu' * D.bt) * C.j⁻¹ := by rw [D.bu'_comm_bt]
        _ = C.j * D.bu' * C.j⁻¹ * (C.j * D.bt * C.j⁻¹) := by group
    have hw2x : w2 * x = x * w2 := by
      have hc : Commute w2 (g * C.b * g⁻¹) := by
        show w2 * (g * C.b * g⁻¹) = g * C.b * g⁻¹ * w2
        rw [hw2]
        calc g * D.bt * g⁻¹ * (g * C.b * g⁻¹) = g * (D.bt * C.b) * g⁻¹ := by group
          _ = g * (C.b * D.bt) * g⁻¹ := by rw [D.b_comm_bt]
          _ = g * C.b * g⁻¹ * (g * D.bt * g⁻¹) := by group
      rw [← hkk]
      exact (hc.pow_right kk).eq
    have hw15 : w1 ^ 5 = 1 := by rw [hw1, conj_pow, D.bt_pow]; group
    have hw25 : w2 ^ 5 = 1 := by rw [hw2, conj_pow, D.bt_pow]; group
    have hw11 : w1 ≠ 1 := by
      intro h1
      apply D.bt_ne
      calc D.bt = C.j⁻¹ * w1 * C.j := by rw [hw1]; group
        _ = 1 := by rw [h1]; group
    have hw21 : w2 ≠ 1 := by
      intro h1
      apply D.bt_ne
      calc D.bt = g⁻¹ * w2 * g := by rw [hw2]; group
        _ = 1 := by rw [h1]; group
    have hw1K : w1 ∈ P5 x ⊓ Subgroup.centralizer ({C.t} : Set G) :=
      ⟨mem_P5_of_pow_five hxH hxo (mem_G5.mpr hw1x) hw15,
        Subgroup.mem_centralizer_singleton_iff.mpr hw1t⟩
    have hw2K : w2 ∈ P5 x ⊓ Subgroup.centralizer ({C.t} : Set G) :=
      ⟨mem_P5_of_pow_five hxH hxo (mem_G5.mpr hw2x) hw25,
        Subgroup.mem_centralizer_singleton_iff.mpr hw2t⟩
    obtain ⟨a1, ha1⟩ := hcgen w1 hw1K
    obtain ⟨a2, ha2⟩ := hcgen w2 hw2K
    obtain ⟨a3, ha3⟩ := exists_pow_pow_eq hc5 (show c ^ a1 ≠ 1 by rw [ha1]; exact hw11)
    rw [ha1] at ha3
    have hw12 : w1 ^ (a3 * a2) = w2 := by rw [pow_mul, ha3, ha2]
    have hgct : D.ct * g * D.ct⁻¹ ∈ C.F1 := by
      have hτQ : D.τ⁻¹ ∈ ruQ M.T := inv_mem D.τ_mem.1
      have h1 : D.τ⁻¹ * g * D.τ⁻¹⁻¹ ∈ C.F1 := C.conj_mem_F1_of_mem_Q hτQ hgF
      have hτu : D.τ⁻¹ * C.t * D.τ = C.u := by
        show D.τ⁻¹ * (C.u * M.z) * D.τ = C.u
        rw [← D.τ_conj]
        group
      have h2 : (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.u = C.u * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by
        calc (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.u = D.τ⁻¹ * g * D.τ⁻¹⁻¹ * (D.τ⁻¹ * C.t * D.τ) := by
              rw [hτu]
          _ = D.τ⁻¹ * (g * C.t) * D.τ := by group
          _ = D.τ⁻¹ * (C.t * g) * D.τ := by rw [hgt]
          _ = (D.τ⁻¹ * C.t * D.τ) * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by group
          _ = C.u * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) := by rw [hτu]
      have h3 := C.conj_mem_F1 _ h1 h2
      have e : D.ct * g * D.ct⁻¹ = C.j * (D.τ⁻¹ * g * D.τ⁻¹⁻¹) * C.j⁻¹ := by
        unfold Fives.ct
        group
      rw [e]
      exact h3
    have hgctH : D.ct * g * D.ct⁻¹ ∈ ruH M.T := C.F1_le_H hgct
    have hgN : NormBy (D.rhoT g) (M.phiG C.b) := by
      obtain ⟨k, hk⟩ := C.F1_norm _ hgct
      rw [M.phiG_conj hgctH C.b_mem_H] at hk
      have hk1 : D.rhoT g * M.phiG C.b * (D.rhoT g)⁻¹ = M.phiG C.b ^ k := hk
      obtain ⟨k', hk'⟩ := powOfG_pow (M.phiG C.b) k
        (by rw [← M.phiG_pow C.b_mem_H, C.b_pow_five]; exact M.phiG_one47)
      exact ⟨k', by rw [hk1, hk']⟩
    have hgd : D.rhoT g * d = d * D.rhoT g := by
      have hcz : (D.ct * g * D.ct⁻¹) * C.u = C.u * (D.ct * g * D.ct⁻¹) := by
        rw [← D.ct_conj_z]
        calc D.ct * g * D.ct⁻¹ * (D.ct * M.z * D.ct⁻¹) = D.ct * (g * M.z) * D.ct⁻¹ := by group
          _ = D.ct * (M.z * g) * D.ct⁻¹ := by rw [hgz]
          _ = D.ct * M.z * D.ct⁻¹ * (D.ct * g * D.ct⁻¹) := by group
      show M.phiG (D.ct * g * D.ct⁻¹) * d = d * M.phiG (D.ct * g * D.ct⁻¹)
      rw [hd, ← M.phiG_mul hgctH C.u_mem_H, ← M.phiG_mul C.u_mem_H hgctH, hcz]
    obtain ⟨hσ5, hσ1⟩ := D.rhoT_bt_props
    have hσN : NormBy d (D.rhoT D.bt) := by
      refine ⟨4, ?_⟩
      show d * D.rhoT D.bt * d⁻¹ = D.rhoT D.bt ^ 4
      rw [hd, ← D.rhoT_z, ← D.rhoT_conj C.z_comm_t D.bt_comm, D.z_inv_bt,
        show D.bt⁻¹ = D.bt ^ 4 by
          calc D.bt⁻¹ = D.bt ^ 5 * D.bt⁻¹ := by rw [D.bt_pow, one_mul]
            _ = D.bt ^ 4 := by group,
        D.rhoT_pow D.bt_comm]
    have hb5 : M.phiG C.b ^ 5 = 1 := by
      rw [← M.phiG_pow C.b_mem_H, C.b_pow_five]; exact M.phiG_one47
    have hb1 : M.phiG C.b ≠ 1 :=
      M.phiG_ne_one_of_pow_five C.b_mem_H C.b_pow_five (fun h => by
        have := C.orderOf_b
        rw [h, orderOf_one] at this
        norm_num at this)
    have hgσ : NormBy (D.rhoT g) (D.rhoT D.bt) :=
      normBy_of_normBy_of_comm hd2 hd1 hb5 hb1 hNb hσ5 hσ1 hσN hgd hgN
    have hρw2 : D.rhoT w2 = D.rhoT g * D.rhoT D.bt * (D.rhoT g)⁻¹ := by
      rw [hw2, D.rhoT_conj hgt D.bt_comm]
    have hP1 : PowOfG (D.rhoT D.bt) (D.rhoT w2) := by
      obtain ⟨k, hk⟩ := hgσ
      exact ⟨k, by rw [hρw2, hk]⟩
    have hw1ρ5 : D.rhoT w1 ^ 5 = 1 := by rw [← D.rhoT_pow hw1t, hw15, D.rhoT_one]
    have hP2 : PowOfG (D.rhoT w1) (D.rhoT w2) := by
      rw [← hw12, D.rhoT_pow hw1t]
      exact powOfG_pow _ _ hw1ρ5
    have hρw2_1 : D.rhoT w2 ≠ 1 := by
      intro h1
      have hQ := (D.rhoT_eq_one_iff hw2t).mp h1
      have h2 := M.pow_eq_one_of_mem_Q hQ
      rw [conj_pow] at h2
      apply hw21
      have h3 : w2 ^ 2048 = 1 := by
        calc w2 ^ 2048 = D.ct⁻¹ * (D.ct * w2 ^ 2048 * D.ct⁻¹) * D.ct := by group
          _ = 1 := by rw [h2]; group
      have := (pow_gcd_eq_one (a := w2)).mpr ⟨hw25, h3⟩
      rwa [show Nat.gcd 5 2048 = 1 by norm_num, pow_one] at this
    have hP3 := powOfG_symm hw1ρ5 hρw2_1 hP2
    have hfin := powOfG_trans hσ5 hP1 hP3
    rw [hw1] at hfin
    exact D.not_powOfG_bt hfin

end Conf47

end RuDataM

end CFSG.Quasithin.RuType
