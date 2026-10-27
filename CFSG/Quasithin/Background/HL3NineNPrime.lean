module

public import CFSG.Quasithin.Background.HL3NineNorm
public import CFSG.Quasithin.Background.HSL3PairTorus
public import CFSG.Quasithin.Background.E1Sec7
public import CFSG.Quasithin.Background.HTriSolv

public section

namespace CFSG.Quasithin

namespace H

namespace L3Nine

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SU3 Tri CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

section Group

variable {G : Type*} [Group G]

theorem mem_of_mul_mem {N : Subgroup G} {b s : G}
    (hsN : s ∈ Subgroup.normalizer (N : Set G)) {k j : ℕ} (hk : Odd k) (hb : b ^ k = 1)
    (hs : s ^ 2 ^ j = 1) (hbs : b * s ∈ N) : b ∈ N := by
  have hpow : ∀ m : ℕ, b ^ m * s ^ m ∈ N := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hsm : (s ^ m)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
        Subgroup.inv_mem _ (Subgroup.pow_mem _ hsN m)
      have hconj : (s ^ m)⁻¹ * (b * s) * (s ^ m)⁻¹⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp hsm _).mp hbs
      have e : b ^ (m + 1) * s ^ (m + 1) =
          (b ^ m * s ^ m) * ((s ^ m)⁻¹ * (b * s) * (s ^ m)⁻¹⁻¹) := by group
      rw [e]
      exact N.mul_mem ih hconj
  have h1 : b ^ 2 ^ j ∈ N := by
    have := hpow (2 ^ j)
    rwa [hs, mul_one] at this
  have hcop : Nat.Coprime k (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hk)
  have hg : ((Nat.gcd k (2 ^ j) : ℕ) : ℤ) =
      k * Nat.gcdA k (2 ^ j) + 2 ^ j * Nat.gcdB k (2 ^ j) := by
    have := Nat.gcd_eq_gcd_ab k (2 ^ j)
    push_cast at this ⊢
    exact this
  rw [hcop, Nat.cast_one] at hg
  have e : b = (b ^ k) ^ Nat.gcdA k (2 ^ j) * (b ^ 2 ^ j) ^ Nat.gcdB k (2 ^ j) := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add]
    push_cast
    rw [← hg, zpow_one]
  rw [e, hb, _root_.one_zpow, one_mul]
  exact N.zpow_mem h1 _

theorem permute_inf [Finite G] {B S N X : Subgroup G} (hSX : S ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set G) * S = S * B) :
    ((B ⊓ N : Subgroup G) : Set G) * ((S ⊓ N : Subgroup G) : Set G) =
      ((S ⊓ N : Subgroup G) : Set G) * ((B ⊓ N : Subgroup G) : Set G) := by
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have hub : u * b ∈ (S : Set G) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubN : u * b ∈ N := N.mul_mem hu.2 hb.2
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  have hb'N : b' ∈ N := mem_of_mul_mem (hXN (hSX hs)) hBodd hb'k hsj (hbs' ▸ hubN)
  have hsN : s ∈ N := by
    have e : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
    rw [e]
    exact N.mul_mem (N.inv_mem hb'N) hubN
  exact ⟨b', ⟨hb', hb'N⟩, s, ⟨hs, hsN⟩, hbs⟩

end Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem odd_orderOf_of_rhoT (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    {m : ℕ}
    (hm : Odd m) (h : rhoT hK A ^ m = 1) : Odd (orderOf A) := by
  rw [← map_pow] at h
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h
  have hdd : d * bar n d = 1 := by
    have h1 := congrArg (fun Y : HMod n K => mat Y 0 0) (congrArg (fun f => f (e00 hK)) h)
    simp only [MulAut.one_apply, mat_rhoT, hd, tw, mat_pt, rk1_apply] at h1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.smul_apply, rk1_apply] using h1
  have hpow : A ^ (m * (2 ^ n + 1)) = 1 := by
    apply Units.ext
    rw [pow_mul, Units.val_pow_eq_pow_val, hd, smul_pow, one_pow, Units.val_one]
    have : d ^ (2 ^ n + 1) = 1 := by
      rw [pow_succ, ← bar_apply, mul_comm]
      exact hdd
    rw [this, one_smul]
  have hodd : Odd (m * (2 ^ n + 1)) :=
    hm.mul ((Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one)
  exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hpow)

theorem le_of_permutes (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (HMod n K))} (hX1 : img hK ≤ X) (hX2 : X ≤ norm hK)
    {Y B S : Subgroup (MulAut (HMod n K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (HMod n K))) * S = S * B) : c ≤ 2 * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    nlinarith
  set N₁ := linImg hK with hN₁
  have hXN₁ : X ≤ Subgroup.normalizer (N₁ : Set (MulAut (HMod n K))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact conj_mem_linImg hn hK (hX2 hx)
    · intro hr
      have := conj_mem_linImg hn hK (inv_mem (hX2 hx)) hr
      rwa [show x⁻¹ * (x * r * x⁻¹) * x⁻¹⁻¹ = r by group] at this
  have hperm := permute_inf hS.le hXN₁ hBodd hS.isPGroup hBS
  set B₁ := B ⊓ N₁ with hB₁
  set S₁ := S ⊓ N₁ with hS₁
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := fun a ha b hb => hBab a ha.1 b hb.1
  have hB₁odd : Odd (Nat.card B₁) := Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
  have hS₁p : IsPGroup 2 S₁ := hS.isPGroup.to_le inf_le_left
  have hsolv := isSolvable_sup_of_permute hB₁ab hB₁odd hS₁p hperm
  set R := (B₁ ⊔ S₁).comap (rhoT hK) with hR
  have hRsolv : Group.IsSolvable ↥R := by
    let φ : ↥R →* ↥(B₁ ⊔ S₁) :=
      MonoidHom.codRestrict ((rhoT hK).comp R.subtype) (B₁ ⊔ S₁) fun r => r.2
    have hcomm : ∀ a b : ↥φ.ker, a * b = b * a := by
      intro a b
      have ha : rhoT hK ((a : ↥R) : GL (Fin 3) K) = 1 := congrArg Subtype.val a.2
      have hb : rhoT hK ((b : ↥R) : GL (Fin 3) K) = 1 := congrArg Subtype.val b.2
      obtain ⟨da, hda⟩ := scalar_of_rhoT_eq_one hK ha
      obtain ⟨db, hdb⟩ := scalar_of_rhoT_eq_one hK hb
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, hda, hdb]
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul,
        mul_comm]
    have : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_comm hcomm
    exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])
  set ρ' := (rho hK).rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective _
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀syl : IsSylowIn 2 ((LinearFlag.unitriangular 3 K).map ρ') ⊤ := by
    have h := isSylowIn_top P₀
    rw [hP₀] at h
    exact E1.isSylowIn_two_map_top hρ's h
  have hLnX : ((img hK).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hSL := hS.inf_normal hX1 hLnX
  have hSL' : IsSylowIn 2 ((S ⊓ img hK).subgroupOf (img hK)) ⊤ := by
    rw [← E1.isSylowIn_map_of_injective (img hK).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hSL
  let Q₁ : Sylow 2 ↥(img hK) := hSL'.isPGroup.toSylow (by
    have := hSL'.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this)
  let Q₂ : Sylow 2 ↥(img hK) := hU₀syl.isPGroup.toSylow (by
    have := hU₀syl.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq ↥(img hK) Q₂ Q₁
  obtain ⟨g₀, hg₀⟩ := hρ's l
  have hconj : ∀ u ∈ LinearFlag.unitriangular 3 K, rho hK (g₀ * u * g₀⁻¹) ∈ S := by
    intro u hu
    have h1 : ρ' (g₀ * u * g₀⁻¹) ∈ (Q₁ : Subgroup ↥(img hK)) := by
      rw [← hl, LinearFlag.coe_sylow_smul]
      refine ⟨ρ' u, ⟨u, hu, rfl⟩, ?_⟩
      change l * ρ' u * l⁻¹ = ρ' (g₀ * u * g₀⁻¹)
      rw [← hg₀, map_mul, map_mul, map_inv]
    have h2 : ρ' (g₀ * u * g₀⁻¹) ∈ (S ⊓ img hK).subgroupOf (img hK) := h1
    exact (Subgroup.mem_subgroupOf.mp h2).1
  set c₀ := SpecialLinearGroup.toGL g₀ with hc₀
  set R' := R.map (MulAut.conj c₀⁻¹).toMonoidHom with hR'
  have hUR' : uni3 K ≤ R' := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨c₀ * SpecialLinearGroup.toGL u * c₀⁻¹, ?_, ?_⟩
    · change rhoT hK (c₀ * SpecialLinearGroup.toGL u * c₀⁻¹) ∈ B₁ ⊔ S₁
      have e0 : SpecialLinearGroup.toGL (g₀ * u * g₀⁻¹) =
          c₀ * SpecialLinearGroup.toGL u * c₀⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      have e : rhoT hK (c₀ * SpecialLinearGroup.toGL u * c₀⁻¹) = rho hK (g₀ * u * g₀⁻¹) := by
        change _ = rhoT hK (SpecialLinearGroup.toGL (g₀ * u * g₀⁻¹))
        rw [e0]
      rw [e]
      exact le_sup_right (a := B₁) ⟨hconj u hu, img_le_linImg hK ⟨_, rfl⟩⟩
    · change c₀⁻¹ * (c₀ * SpecialLinearGroup.toGL u * c₀⁻¹) * c₀⁻¹⁻¹ = SpecialLinearGroup.toGL u
      group
  have hR'solv : Group.IsSolvable ↥R' := by
    have := hRsolv
    exact Group.isSolvable_of_surjective
      (f := (R.equivMapOfInjective (MulAut.conj c₀⁻¹).toMonoidHom
        (MulAut.conj c₀⁻¹).injective).toMonoidHom) (MulEquiv.surjective _)
  have htri : R' ≤ borGL 3 K := le_borGL_three_of_solvable hK4 hR'solv hUR'
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (HMod n K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (HMod n K)) ∈ B := hYB y.2
  have hy2n : (y : MulAut (HMod n K)) ^ (2 * n) ∈ B₁ :=
    ⟨B.pow_mem hyB _, pow_mem_linImg hn hK (hX2 (hBX hyB))⟩
  obtain ⟨A, hA⟩ := hy2n.2
  have hAR : A ∈ R := by
    change rhoT hK A ∈ B₁ ⊔ S₁
    rw [hA]
    exact le_sup_left (b := S₁) hy2n
  have hA' : c₀⁻¹ * A * c₀ ∈ borGL 3 K :=
    htri ⟨A, hAR, by
      change c₀⁻¹ * A * c₀⁻¹⁻¹ = c₀⁻¹ * A * c₀
      rw [inv_inv]⟩
  have hyodd : Odd (orderOf ((y : MulAut (HMod n K)) ^ (2 * n))) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hyB))
      (orderOf_pow_dvd _)
  have hAodd : Odd (orderOf A) := odd_orderOf_of_rhoT hn hK hyodd (by
    rw [hA]
    exact pow_orderOf_eq_one _)
  have hA'odd : Odd (orderOf (c₀⁻¹ * A * c₀)) := by
    have e : c₀⁻¹ * A * c₀ = (MulAut.conj c₀⁻¹).toMonoidHom A := by
      change _ = c₀⁻¹ * A * c₀⁻¹⁻¹
      rw [inv_inv]
    rw [e, orderOf_injective _ (MulAut.conj c₀⁻¹).injective]
    exact hAodd
  have h1 := pow_card_sub_one_eq_one hA' hA'odd
  have h2 : A ^ (Nat.card K - 1) = 1 := by
    have e : c₀⁻¹ * A * c₀ = c₀⁻¹ * A * c₀⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, conj_eq_one_iff] at h1
    exact h1
  have hypow : (y : MulAut (HMod n K)) ^ (2 * n * (Nat.card K - 1)) = 1 := by
    rw [pow_mul, ← hA, ← map_pow, h2, map_one]
  have hdvd : 2 ^ c - 1 ∣ 2 * n * (2 ^ (2 * n) - 1) := by
    rw [← hyo, ← SU3.card_eq_two_pow hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) (by omega) le_rfl hdvd

theorem nPrime_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (HMod n K))} (hX1 : img hK ≤ X) (hX2 : X ≤ norm hK) :
    E3.nPrime X ≤ 2 * n := by
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

theorem conj_mem_unitriangular (hK : Nat.card K = (2 ^ n) ^ 2)
    {b : SpecialLinearGroup (Fin 3) K}
    (hb : rho hK b ∈ Subgroup.normalizer
      (((LinearFlag.unitriangular 3 K).map (rho hK) : Subgroup (MulAut (HMod n K))) :
        Set (MulAut (HMod n K))))
    {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ LinearFlag.unitriangular 3 K) :
    b * u * b⁻¹ ∈ LinearFlag.unitriangular 3 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : rho hK (b * u * b⁻¹) ∈ (LinearFlag.unitriangular 3 K).map (rho hK) := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hb _).mp ⟨u, hu, rfl⟩
  obtain ⟨u', hu', hu'e⟩ := h1
  set z := u'⁻¹ * (b * u * b⁻¹) with hz
  have hzk : rho hK z = 1 := by rw [hz, map_mul, map_inv, hu'e, inv_mul_cancel]
  have hzs : z ∈ LinearFlag.scalars 3 K := mem_scalars_of_rho_eq_one hK hzk
  have hzc : ∀ m, m * z = z * m := Subgroup.mem_center_iff.mp (LinearFlag.scalars_le_center 3 K hzs)
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨c', hc', hzc'⟩ := LinearFlag.mem_scalars.mp hzs
    have h : ((z ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((1 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, hzc', Matrix.SpecialLinearGroup.coe_one, ← map_pow,
        ← Units.val_pow_eq_pow_val, hc', Units.val_one, map_one]
    exact Subtype.ext h
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hUp : IsPGroup 2 (LinearFlag.unitriangular 3 K) := by
    rw [← hP₀]
    exact P₀.isPGroup'
  obtain ⟨k, hk⟩ := hUp.exists_card_eq
  have hpk : ∀ v ∈ LinearFlag.unitriangular 3 K, v ^ 2 ^ k = 1 := fun v hv => by
    rw [← hk]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hv)
  have hbu : (b * u * b⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hpk u hu, mul_one, mul_inv_cancel]
  have he : b * u * b⁻¹ = u' * z := by rw [hz, mul_inv_cancel_left]
  have hz2 : z ^ 2 ^ k = 1 := by
    have h := hbu
    rw [he, (show Commute u' z from hzc u').mul_pow, hpk u' hu', one_mul] at h
    exact h
  have hz1 : z = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hz3) (orderOf_dvd_of_pow_eq_one hz2))
  rw [he, hz1, mul_one]
  exact hu'

theorem le_nPrime (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (HMod n K))} (hX1 : img hK ≤ X) (hX2 : X ≤ norm hK) :
    2 * n ≤ E3.nPrime X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  set U₀ := LinearFlag.unitriangular 3 K with hU₀
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  set ρ' := (rho hK).rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := MonoidHom.rangeRestrict_surjective _
  have hU₀syl : IsSylowIn 2 (U₀.map ρ') ⊤ := by
    have h := isSylowIn_top P₀
    rw [hP₀] at h
    exact E1.isSylowIn_two_map_top hρ's h
  set V₀ := U₀.map (rho hK) with hV₀
  have hV₀L : V₀ ≤ img hK := Subgroup.map_le_range _ _
  have hV₀p : IsPGroup 2 V₀ := by
    rw [hV₀, hU₀, ← hP₀]
    exact P₀.isPGroup'.map _
  obtain ⟨S, hS, hVS⟩ := exists_isSylowIn_ge 2 (hV₀L.trans hX1) hV₀p
  have hSV : S ⊓ img hK = V₀ := by
    refine le_antisymm ?_ (le_inf hVS hV₀L)
    let Q₂ : Sylow 2 ↥(img hK) := hU₀syl.isPGroup.toSylow (by
      have := hU₀syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
    have hp : IsPGroup 2 ((S ⊓ img hK).subgroupOf (img hK)) :=
      hS.isPGroup.to_inf_left.comap_of_injective _ (img hK).subtype_injective
    have hle : (Q₂ : Subgroup ↥(img hK)) ≤ (S ⊓ img hK).subgroupOf (img hK) := by
      rintro _ ⟨u, hu, rfl⟩
      exact ⟨hVS ⟨u, hu, rfl⟩, (ρ' u).2⟩
    have heq := Q₂.is_maximal' hp hle
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥(img hK)) ∈ (S ⊓ img hK).subgroupOf (img hK) := hx
    rw [heq] at hx'
    obtain ⟨u, hu, hux⟩ := hx'
    exact ⟨u, hu, congrArg Subtype.val hux⟩
  have hSN : ∀ s ∈ S, s ∈ Subgroup.normalizer (V₀ : Set (MulAut (HMod n K))) := by
    intro s hs
    rw [← hSV, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x,
      Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) x]
  have hNU : ∀ b, rho hK b ∈ Subgroup.normalizer (V₀ : Set (MulAut (HMod n K))) →
      b ∈ LinearFlag.upperTriangular 3 K := by
    intro b hb
    rw [← LinearFlag.normalizer_unitriangular, Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact conj_mem_unitriangular hK hb
    · intro h
      have hb' : rho hK b⁻¹ ∈ Subgroup.normalizer (V₀ : Set (MulAut (HMod n K))) := by
        rw [map_inv]
        exact Subgroup.inv_mem _ hb
      have := conj_mem_unitriangular hK hb' h
      rwa [show b⁻¹ * (b * u * b⁻¹) * b⁻¹⁻¹ = u by group] at this
  set B := ((rho hK).comp (SL3Pair.torusHom K)).range with hB
  have hSB : (S : Set (MulAut (HMod n K))) * B ⊆ B * S := by
    rintro _ ⟨s, hs, _, ⟨p, rfl⟩, rfl⟩
    have h1 : s * rho hK (SL3Pair.torusHom K p) * s⁻¹ ∈ img hK :=
      (Subgroup.mem_normalizer_iff.mp (hX2 (hS.le hs)) _).mp ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := h1
    have hbN : rho hK b ∈ Subgroup.normalizer (V₀ : Set (MulAut (HMod n K))) := by
      rw [hb]
      have htN : rho hK (SL3Pair.torusHom K p) ∈
          Subgroup.normalizer (V₀ : Set (MulAut (HMod n K))) := by
        apply Subgroup.le_normalizer_map
        refine ⟨SL3Pair.torusHom K p, ?_, rfl⟩
        rw [SetLike.mem_coe, LinearFlag.normalizer_unitriangular]
        exact SL3Pair.torusHom_mem_upperTriangular p
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hSN s hs) htN)
        (Subgroup.inv_mem _ (hSN s hs))
    obtain ⟨p', u, hu, hbe⟩ := SL3Pair.exists_torus_mul (hNU b hbN)
    refine ⟨rho hK (SL3Pair.torusHom K p'), ⟨p', rfl⟩, rho hK u * s,
      S.mul_mem (hVS ⟨u, hu, rfl⟩) hs, ?_⟩
    change rho hK (SL3Pair.torusHom K p') * (rho hK u * s) =
      s * rho hK (SL3Pair.torusHom K p)
    rw [← mul_assoc, ← map_mul, ← hbe, hb]
    group
  have hBS : (B : Set (MulAut (HMod n K))) * S = S * B := SL3Pair.mul_comm_of_subset hSB
  have hBX : B ≤ X := by
    refine le_trans ?_ hX1
    rw [hB, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm p q]
  have hq : Odd ((2 ^ n) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.one_le_two_pow))
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩) odd_one
  have hBodd : Odd (Nat.card B) := by
    have h1 : Nat.card B ∣ Nat.card (Kˣ × Kˣ) := by
      rw [hB, MonoidHom.range_eq_map]
      exact (Subgroup.card_map_dvd _ _).trans (by rw [Subgroup.card_top])
    rw [Nat.card_prod, Nat.card_units, hK] at h1
    exact Odd.of_dvd_nat (hq.mul hq) h1
  set φ : Kˣ →* MulAut (HMod n K) :=
    (rho hK).comp ((SL3Pair.torusHom K).comp (MonoidHom.inl Kˣ Kˣ)) with hφ
  have hφi : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have hs := mem_scalars_of_rho_eq_one hK ht
    obtain ⟨c', -, hc'⟩ := LinearFlag.mem_scalars.mp hs
    have h0 := congrFun (congrFun hc' 0) 0
    have h1 := congrFun (congrFun hc' 1) 1
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, SL3Pair.coe_torusHom,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.scalar_apply] at h0 h1
    apply Units.ext
    rw [h0, Units.val_one]
    simpa using h1.symm
  have hYB : φ.range ≤ B := by
    rintro _ ⟨t, rfl⟩
    exact ⟨(t, 1), rfl⟩
  have hYc : Nat.card φ.range = 2 ^ (2 * n) - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv, Nat.card_units,
      SU3.card_eq_two_pow hK]
  have hYcyc : IsCyclic φ.range :=
    isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  exact E3.le_nPrime hYB hBX hYcyc hYc hBab hBodd hS hBS

theorem nPrime_eq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {X : Subgroup (MulAut (HMod n K))} (hX1 : img hK ≤ X) (hX2 : X ≤ norm hK) :
    E3.nPrime X = 2 * n :=
  le_antisymm (nPrime_le hn hK hX1 hX2) (le_nPrime hn hK hX1 hX2)

end L3Nine

theorem H42_L3Nine_nPrime {V : Type*} [CommGroup V] [Finite V] {L M : Subgroup (MulAut V)}
    {n : ℕ} (hn : 1 ≤ n) (hL : BinaryNineTensor L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : E3.nPrime M = 2 * n := by
  obtain ⟨K, _, _, _, hK, hreal⟩ := hL
  have hK' : Nat.card K = (2 ^ n) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨e, h1, h2⟩ := L3Nine.exists_transport hK' hreal hLM hMN
  rw [← nPrime_map_congrHom e M]
  exact L3Nine.nPrime_eq hn hK' h1 h2

end H

end CFSG.Quasithin
