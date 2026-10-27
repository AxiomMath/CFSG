module

public import CFSG.Quasithin.H13.L32NLem14333c
public import CFSG.Quasithin.Background.G25Count
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L14333

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem x_comm_V1 {v : G} (hv : v ∈ fsuV1 T V) : x * v * x⁻¹ = v := by
  rcases c.eq_of_mem_V1 hv with rfl | rfl
  · group
  · exact c.x_z

theorem mem_V1_of_comm {v : G} (hv : v ∈ V) (hx : x * v * x⁻¹ = v) : v ∈ fsuV1 T V := by
  obtain ⟨_, S⟩ := c.setting
  have hb2 : b * b = 1 := S.mul_self_V c.b_mem
  have haV₂ := c.ctx.aV₂
  have hab : a ≠ b := fun h => c.b_nmem (h ▸ haV₂)
  rcases S.mem_V c.b_mem c.b_nmem hv with hv2 | hv2
  · rcases c.ctx.V₂_cases v hv2 with h | ⟨e, he, rfl⟩
    · exact h
    · exfalso
      have h1 : x * (a * e) * x⁻¹ = b * e := by
        rw [show x * (a * e) * x⁻¹ = (x * a * x⁻¹) * (x * e * x⁻¹) by group, c.x_a,
          c.x_comm_V1 he]
      rw [h1] at hx
      exact hab (mul_right_cancel hx).symm
  · exfalso
    have hv' : v = b * (b * v) := by rw [← mul_assoc, hb2, one_mul]
    rcases c.ctx.V₂_cases _ hv2 with h | ⟨e, he, h⟩
    · rw [hv'] at hx
      have h1 : x * (b * (b * v)) * x⁻¹ = a * b * (b * v) := by
        rw [show x * (b * (b * v)) * x⁻¹ = (x * b * x⁻¹) * (x * (b * v) * x⁻¹) by group,
          c.x_b, c.x_comm_V1 h]
      rw [h1] at hx
      have : a = 1 := by
        have := mul_right_cancel hx
        exact mul_right_cancel (this.trans (one_mul b).symm)
      exact c.ctx.a1 (this ▸ one_mem _)
    · rw [hv', h] at hx
      have h1 : x * (b * (a * e)) * x⁻¹ = a * b * (b * e) := by
        rw [show x * (b * (a * e)) * x⁻¹ = (x * b * x⁻¹) * (x * a * x⁻¹) * (x * e * x⁻¹) by
          group, c.x_b, c.x_a, c.x_comm_V1 he, mul_assoc]
      rw [h1] at hx
      have h2 : a * e = b * (a * e) := by
        calc a * e = a * (b * b) * e := by rw [hb2, mul_one]
          _ = a * b * (b * e) := by group
          _ = b * (a * e) := hx
      have : b = 1 := mul_right_cancel (h2.symm.trans (one_mul _).symm)
      exact c.b_nmem (this ▸ one_mem _)

theorem x_le_normalizer_P : Subgroup.zpowers x ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
  Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 L c.x_mem)

theorem P_le_centralizer : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨_, S⟩ := c.setting
  rw [← S.cent_eq]
  exact inf_le_right

theorem P_le_H : pCoreOf 2 L ≤ l32nH T V := by
  have hc : ∀ q ∈ pCoreOf 2 L, ∀ w ∈ fsuV1 T V, q * w * q⁻¹ = w := fun q hq w hw => by
    have := Subgroup.mem_centralizer_iff.mp (c.P_le_centralizer hq) w (Subgroup.mem_inf.mp hw).1
    rw [← this]
    group
  exact le_normalizer_of_conj_mem fun q hq w hw => by rw [hc q hq w hw]; exact hw

theorem mem_zU_of_comm (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {p : G}
    (hp : p ∈ pCoreOf 2 L) (hx : x * p * x⁻¹ = p) : p ∈ centerOf (fsuU T V) := by
  obtain ⟨hP, hcard⟩ := c.pCoreOf_eq hyp
  have hVe : V = conjClosure (fsuV1 T V) L := hyp.V_eq
  have hPab : ∀ u ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, u * w = w * u := hP ▸ c.X_comm
  have hsqV : ∀ u ∈ pCoreOf 2 L, u * u ∈ V := hP ▸ c.sq_mem_V_of_X
  have hdP : d ∈ pCoreOf 2 L := hP ▸ le_conjClosure _ L c.d_mem
  have hO1 : ∀ u ∈ pCoreOf 2 L, u * u = 1 → u ∈ V := fun u hu hu1 =>
    mem_of_mul_self_eq_one hPab (hP ▸ c.V_le_X hVe) (fun v hv => c.mul_self_V hv) hsqV
      (hP ▸ c.exists_sq hVe) (by rw [hcard, c.card_V]) hu hu1
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := c.vZ ▸ inf_le_right
  have hpV : p * p ∈ V := hsqV p hp
  have hpx : x * (p * p) * x⁻¹ = p * p := by
    rw [show x * (p * p) * x⁻¹ = (x * p * x⁻¹) * (x * p * x⁻¹) by group, hx]
  rcases c.eq_of_mem_V1 (c.mem_V1_of_comm hpV hpx) with h1 | h1
  · exact hV1Z (c.mem_V1_of_comm (hO1 p hp h1) hx)
  ·
    have hpd : p * d⁻¹ ∈ pCoreOf 2 L := mul_mem hp (inv_mem hdP)
    have hpd1 : (p * d⁻¹) * (p * d⁻¹) = 1 := by
      have hc := hPab _ (inv_mem hdP) _ hp
      calc (p * d⁻¹) * (p * d⁻¹) = p * (d⁻¹ * p) * d⁻¹ := by group
        _ = p * (p * d⁻¹) * d⁻¹ := by rw [hc]
        _ = (p * p) * (d * d)⁻¹ := by group
        _ = 1 := by rw [h1, c.d_sq, mul_inv_cancel]
    have hpdx : x * (p * d⁻¹) * x⁻¹ = p * d⁻¹ := by
      rw [show x * (p * d⁻¹) * x⁻¹ = (x * p * x⁻¹) * (x * d * x⁻¹)⁻¹ by group, hx, c.x_comm_d]
    have h2 := hV1Z (c.mem_V1_of_comm (hO1 _ hpd hpd1) hpdx)
    have : p = (p * d⁻¹) * d := by group
    rw [this]
    exact mul_mem h2 c.d_mem

theorem isPGroup_x : IsPGroup 3 ↥(Subgroup.zpowers x) := by
  have h := orderOf_dvd_of_pow_eq_one c.x_cube
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])

theorem U_le_K : fsuU T V ≤ K := by
  rw [c.U_eq]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((pCoreOf_le 2 K).trans Subgroup.le_normalizer)

theorem exists_mul_of_coprime {Y : Subgroup G}
    (hxY : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime 3 (Nat.card Y)) {p : G} (hp : p ∈ Y) :
    ∃ q ∈ ⁅Y, Subgroup.zpowers x⁆, ∃ r ∈ Y, x * r * x⁻¹ = r ∧ q * r = p := by
  have hprod := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_product 3
    Nat.prime_three (Subgroup.zpowers x) Y c.isPGroup_x hxY hcop
  have hp' : p ∈ CFSG.SignalizerFunctor.Helpers.subgroupProduct ⁅Y, Subgroup.zpowers x⁆
      (Y ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    rw [hprod]
    exact hp
  obtain ⟨q, hq, r, hr, hqr⟩ := Set.mem_mul.mp hp'
  have hr' := Subgroup.mem_inf.mp hr
  have hrx : x * r * x⁻¹ = r := by
    have := Subgroup.mem_centralizer_iff.mp hr'.2 x (Subgroup.mem_zpowers x)
    rw [this]
    group
  exact ⟨q, hq, r, hr'.1, hrx, hqr⟩

theorem coprime_three (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {Y : Subgroup G}
    (hY : Y ≤ pCoreOf 2 L) : Nat.Coprime 3 (Nat.card Y) := by
  obtain ⟨-, hcard⟩ := c.pCoreOf_eq hyp
  have hdvd : Nat.card Y ∣ 2 ^ 6 := by
    rw [show (2 : ℕ) ^ 6 = 64 by norm_num, ← hcard]
    exact Subgroup.card_dvd_of_le hY
  exact Nat.Coprime.coprime_dvd_right hdvd (by norm_num)

theorem P_le_K (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    pCoreOf 2 L ≤ K := by
  have hle : ⁅pCoreOf 2 L, Subgroup.zpowers x⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro p hp y hy
    have hyK : y ∈ K := (Subgroup.zpowers_le.mpr c.x_mem_K) hy
    have h1 : p * y * p⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (c.K_norm (c.P_le_H hp)) y).mp hyK
    rw [commutatorElement_def]
    exact K.mul_mem h1 (K.inv_mem hyK)
  intro p hp
  obtain ⟨q, hq, r, hr, hrx, rfl⟩ :=
    c.exists_mul_of_coprime c.x_le_normalizer_P (c.coprime_three hyp le_rfl) hp
  exact K.mul_mem (hle hq) (c.U_le_K (Subgroup.mem_inf.mp (c.mem_zU_of_comm hyp hr hrx)).1)

theorem P_inf_Q_le (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    pCoreOf 2 L ⊓ pCoreOf 2 (l32nH T V) ≤ V ⊔ centerOf (fsuU T V) := by
  set Y := pCoreOf 2 L ⊓ pCoreOf 2 (l32nH T V) with hY
  have hxY : Subgroup.zpowers x ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 L c.x_mem, le_normalizer_pCoreOf 2 _ c.x_mem_H⟩)
  have hcomm : ⁅Y, Subgroup.zpowers x⁆ ≤ fsuU T V ⊓ pCoreOf 2 L := by
    refine le_inf ?_ ?_
    · refine le_trans ?_ c.KQ
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr c.x_mem_K) inf_le_right
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hxY).trans inf_le_left
  intro p hp
  obtain ⟨q, hq, r, hr, hrx, rfl⟩ :=
    c.exists_mul_of_coprime hxY (c.coprime_three hyp inf_le_left) hp
  have hq' := hcomm hq
  refine Subgroup.mul_mem _ (c.mem_sup_of_comm hq'.1 fun v hv => ?_)
    (Subgroup.mem_sup_right (c.mem_zU_of_comm hyp (Subgroup.mem_inf.mp hr).1 hrx))
  exact (Subgroup.mem_centralizer_iff.mp (c.P_le_centralizer hq'.2) v hv).symm

theorem sup_zU_le_P (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    V ⊔ centerOf (fsuU T V) ≤ pCoreOf 2 L := by
  obtain ⟨hP, -⟩ := c.pCoreOf_eq hyp
  rw [hP]
  exact sup_le (c.V_le_X hyp.V_eq) (le_conjClosure _ L)

theorem card_K : Nat.card K = Nat.card ↥(K ⊓ pCoreOf 2 (l32nH T V)) * 60 := by
  have hKH : K ≤ l32nH T V := le_of_mem_cComp c.comp
  have hφ : ∀ h : ↥(l32nH T V), imgHom D h = 1 ↔ (h : G) ∈ pCoreOf 2 (l32nH T V) := by
    intro h
    rw [← MonoidHom.mem_ker, imgHom_ker, Subgroup.mem_subgroupOf, c.q_eq]
  rw [card_eq_card_inf_mul_card_range (imgHom D) hφ hKH, MonoidHom.range_comp,
    Subgroup.inclusion_range, c.card_kd]

theorem pCoreOf_K_eq (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    pCoreOf 2 K = fsuU T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 K with hR
  set Q := pCoreOf 2 (l32nH T V) with hQ
  set P := pCoreOf 2 L with hPdef
  have hKH : K ≤ l32nH T V := le_of_mem_cComp c.comp
  have hRK : R ≤ K := pCoreOf_le 2 K
  have hKR : K ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 K
  have hUR : fsuU T V ≤ R := by
    rw [c.U_eq]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hKR
  have hRU : ⁅R, K⁆ ≤ fsuU T V := c.U_eq.ge
  have hRQ : R ≤ Q := le_pCoreOf_of_le_normalizer 2 (hRK.trans hKH)
    (c.K_norm.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hKQ : K ⊓ Q = R := by
    refine le_antisymm (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)) (le_inf hRK hRQ)
    exact fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 _ (hKH hk)⟩
  have hPK := c.P_le_K hyp
  obtain ⟨-, hPcard⟩ := c.pCoreOf_eq hyp
  have hPR : P ⊓ R = V ⊔ centerOf (fsuU T V) := le_antisymm
    ((inf_le_inf_left P hRQ).trans (c.P_inf_Q_le hyp))
    (le_inf (c.sup_zU_le_P hyp) ((sup_le c.ctx.V_U inf_le_left).trans hUR))
  have hPRn : P ≤ Subgroup.normalizer (R : Set G) := hPK.trans hKR
  have hcPR : Nat.card ↥(P ⊔ R) * 16 = 64 * Nat.card R := by
    have h := L32NSet14.card_sup_mul_card_inf hPRn
    rwa [hPR, c.card_sup_zU, hPcard] at h
  have hcK : Nat.card K = Nat.card R * 60 := by rw [c.card_K, hKQ]
  have hUK : fsuU T V ≤ K := c.U_le_K
  have hUn : ((fsuU T V).subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hKH.trans (l32nH_le_normalizer_fsuU T V))
  let π := QuotientGroup.mk' ((fsuU T V).subgroupOf K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Z : Subgroup (↥K ⧸ (fsuU T V).subgroupOf K) := (R.subgroupOf K).map π with hZ
  have hcen : ∀ r ∈ R, ∀ k : ↥K, ∀ (hr : r ∈ K), π k * π ⟨r, hr⟩ = π ⟨r, hr⟩ * π k := by
    intro r hrR k hr
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hRU (Subgroup.commutator_mem_commutator (inv_mem hrR) (inv_mem k.2))
    simpa [commutatorElement_def, mul_assoc] using this
  have hZc : Z ≤ Subgroup.center _ := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    obtain ⟨k, rfl⟩ := hπ e
    exact hcen r (Subgroup.mem_subgroupOf.mp hr) k r.2
  have hZp : IsPGroup 2 Z :=
    (A4.isPGroup_subgroupOf_of_le hRK (pCoreOf_isPGroup 2 K)).map π
  set S₀ := (P ⊔ R).subgroupOf K with hS₀
  have hPRK : P ⊔ R ≤ K := sup_le hPK hRK
  have hcardS₀ : Nat.card S₀ = Nat.card ↥(P ⊔ R) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPRK).toEquiv
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K).exists_card_eq
  have hk' : Nat.card R = 2 ^ k := hk
  have hPR4 : Nat.card ↥(P ⊔ R) = 2 ^ (k + 2) := by
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
    rw [hk'] at hcPR
    omega
  have hS₀2 : IsPGroup 2 S₀ := IsPGroup.of_card (n := k + 2) (hcardS₀.trans hPR4)
  have hidx : S₀.index = 15 := by
    have h := Subgroup.card_mul_index S₀
    rw [hcardS₀, hPR4, hcK, hk', pow_add] at h
    have hpos : 0 < 2 ^ k := by positivity
    have : 2 ^ k * (4 * S₀.index) = 2 ^ k * 60 := by rw [← h]; ring
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega
  have hker : π.ker ≤ S₀ := by
    rw [QuotientGroup.ker_mk']
    intro u hu
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (hUR (Subgroup.mem_subgroupOf.mp hu)))
  have hPsyl : IsPGroup 2 (S₀.map π) := hS₀2.map π
  have hidx' : ¬ 2 ∣ (S₀.map π).index := by
    rw [Subgroup.index_map_eq S₀ hπ hker, hidx]
    norm_num
  let PS : Sylow 2 (↥K ⧸ (fsuU T V).subgroupOf K) := hPsyl.toSylow hidx'
  have hPab : ∀ u ∈ P, ∀ w ∈ P, u * w = w * u := by
    obtain ⟨hP, -⟩ := c.pCoreOf_eq hyp
    intro u hu w hw
    rw [hPdef, hP] at hu hw
    exact c.X_comm u hu w hw
  have hab : ∀ e ∈ S₀.map π, ∀ f ∈ S₀.map π, e * f = f * e := by
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right P R hPRn
    have hdec : ∀ s ∈ S₀, ∃ p ∈ P, ∃ r ∈ R, ((s : ↥K) : G) = p * r := by
      intro s hs
      have hs' : ((s : ↥K) : G) ∈ ((P ⊔ R : Subgroup G) : Set G) := Subgroup.mem_subgroupOf.mp hs
      rw [hset] at hs'
      obtain ⟨p, hp, r, hr, h⟩ := Set.mem_mul.mp hs'
      exact ⟨p, hp, r, hr, h.symm⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    obtain ⟨p, hp, r, hr, hs'⟩ := hdec s hs
    obtain ⟨p', hp', r', hr', ht'⟩ := hdec t ht
    have es : s = ⟨p, hPK hp⟩ * ⟨r, hRK hr⟩ := Subtype.ext hs'
    have et : t = ⟨p', hPK hp'⟩ * ⟨r', hRK hr'⟩ := Subtype.ext ht'
    rw [es, et, map_mul, map_mul]
    have c1 := hcen r hr ⟨p', hPK hp'⟩ (hRK hr)
    have c2 := hcen r' hr' ⟨p, hPK hp⟩ (hRK hr')
    have c3 := hcen r hr ⟨r', hRK hr'⟩ (hRK hr)
    have c4 : π ⟨p, hPK hp⟩ * π ⟨p', hPK hp'⟩ = π ⟨p', hPK hp'⟩ * π ⟨p, hPK hp⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hPab p hp p' hp')
    calc π ⟨p, hPK hp⟩ * π ⟨r, hRK hr⟩ * (π ⟨p', hPK hp'⟩ * π ⟨r', hRK hr'⟩)
        = π ⟨p, hPK hp⟩ * (π ⟨r, hRK hr⟩ * π ⟨p', hPK hp'⟩) * π ⟨r', hRK hr'⟩ := by group
      _ = π ⟨p, hPK hp⟩ * (π ⟨p', hPK hp'⟩ * π ⟨r, hRK hr⟩) * π ⟨r', hRK hr'⟩ := by rw [c1]
      _ = (π ⟨p, hPK hp⟩ * π ⟨p', hPK hp'⟩) * (π ⟨r, hRK hr⟩ * π ⟨r', hRK hr'⟩) := by group
      _ = (π ⟨p', hPK hp'⟩ * π ⟨p, hPK hp⟩) * (π ⟨r', hRK hr'⟩ * π ⟨r, hRK hr⟩) := by
          rw [c4, ← c3]
      _ = π ⟨p', hPK hp'⟩ * (π ⟨p, hPK hp⟩ * π ⟨r', hRK hr'⟩) * π ⟨r, hRK hr⟩ := by group
      _ = π ⟨p', hPK hp'⟩ * (π ⟨r', hRK hr'⟩ * π ⟨p, hPK hp⟩) * π ⟨r, hRK hr⟩ := by rw [c2]
      _ = π ⟨p', hPK hp'⟩ * π ⟨r', hRK hr'⟩ * (π ⟨p, hPK hp⟩ * π ⟨r, hRK hr⟩) := by group
  have hcommP : (Z.subgroupOf (PS : Subgroup (↥K ⧸ (fsuU T V).subgroupOf K))) ⊓
      commutator ↥(PS : Subgroup (↥K ⧸ (fsuU T V).subgroupOf K)) = ⊥ := by
    have hbot : commutator ↥(PS : Subgroup (↥K ⧸ (fsuU T V).subgroupOf K)) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u _
      rw [Subgroup.mem_centralizer_iff]
      intro w _
      apply Subtype.ext
      have hPSeq : (PS : Subgroup (↥K ⧸ (fsuU T V).subgroupOf K)) = S₀.map π :=
        IsPGroup.toSylow_coe hPsyl hidx'
      have hu : (u : ↥K ⧸ (fsuU T V).subgroupOf K) ∈ S₀.map π := hPSeq ▸ u.2
      have hw : (w : ↥K ⧸ (fsuU T V).subgroupOf K) ∈ S₀.map π := hPSeq ▸ w.2
      exact hab _ hw _ hu
    rw [hbot, inf_bot_eq]
  have hZE := CFSG.ComponentClassification.AschbacherToolkit.central_sylow_commutator_eq_bot PS
    hZc hZp hcommP
  have hEper : commutator (↥K ⧸ (fsuU T V).subgroupOf K) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective π hπ, ← Subgroup.map_commutator,
      commutator_top_eq_top c.comp]
  rw [hEper, inf_top_eq] at hZE
  refine le_antisymm ?_ hUR
  intro r hr
  have hmem : π ⟨r, hRK hr⟩ ∈ Z := ⟨⟨r, hRK hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  rw [hZE, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem isSylowTwoOf_PU (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    QuasithinUnique.IsSylowTwoOf (pCoreOf 2 L ⊔ fsuU T V) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRU := c.pCoreOf_K_eq hyp
  have hPK := c.P_le_K hyp
  have hUK := c.U_le_K
  obtain ⟨-, hPcard⟩ := c.pCoreOf_eq hyp
  have hPU : pCoreOf 2 L ⊓ fsuU T V = V ⊔ centerOf (fsuU T V) := le_antisymm
    ((inf_le_inf_left _ (fsuU_le_pCoreOf c.ctx)).trans (c.P_inf_Q_le hyp))
    (le_inf (c.sup_zU_le_P hyp) (sup_le c.ctx.V_U inf_le_left))
  have hPUn : pCoreOf 2 L ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    c.P_le_H.trans (l32nH_le_normalizer_fsuU T V)
  have hc := L32NSet14.card_sup_mul_card_inf hPUn
  rw [hPU, c.card_sup_zU, hPcard, c.card_U] at hc
  have hcard : Nat.card ↥(pCoreOf 2 L ⊔ fsuU T V) = 2 ^ 8 := by omega
  have hle : pCoreOf 2 L ⊔ fsuU T V ≤ K := sup_le hPK hUK
  refine ⟨hle, IsPGroup.of_card hcard, ?_⟩
  have hcK : Nat.card K = 64 * 60 := by
    rw [c.card_K]
    have hKQ : K ⊓ pCoreOf 2 (l32nH T V) = fsuU T V := by
      refine le_antisymm (hRU ▸ le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)) (le_inf hUK (fsuU_le_pCoreOf c.ctx))
      exact fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 _ (le_of_mem_cComp c.comp hk)⟩
    rw [hKQ, c.card_U]
  have h := Subgroup.card_mul_index ((pCoreOf 2 L ⊔ fsuU T V).subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard, hcK] at h
  have : ((pCoreOf 2 L ⊔ fsuU T V).subgroupOf K).index = 15 := by omega
  rw [this]
  norm_num

end Ctx

end L14333

end CFSG.Quasithin.H13
