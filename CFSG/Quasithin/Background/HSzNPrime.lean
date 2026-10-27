module

public import CFSG.Quasithin.Background.HSz
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.LieType.SteinbergBRSuzukiNormalizer

public section

namespace CFSG.Quasithin

namespace H

namespace Sz

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree Matrix CFSG.ShultStronglyClosedTI
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Matrix LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K]

theorem le_mParam [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Subgroup (MulAut (StdMod (Fin 4) K))}
    (hXN : X ≤ natNorm (suzukiGroup a K)) : 2 * (2 * a + 1) ≤ E3.mParam X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut (StdMod (Fin 4) K)), t.2,
      (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro k ⟨s, hsX, hs2, rfl⟩
    rw [rkIdx_fixV_of_involution ha hK (hXN hsX) hs2]
  · have hV : Nat.card (StdMod (Fin 4) K) = 2 ^ (4 * (2 * a + 1)) := by
      change Nat.card (Fin 4 → K) = _
      rw [Nat.card_fun, hK, Nat.card_fin, ← pow_mul, mul_comm]
    rw [rk, hV, padicValNat.prime_pow]
    omega

section Ovoid

variable [Finite K]

theorem smul_infty_of_mem_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {e : suzukiGroup a K}
    (he : e ∈ suzukiU a K) : e • suzukiInfty K = suzukiInfty K := by
  have h := suzukiB_le_stabilizer hK (le_sup_left (b := suzukiT a K) he)
  exact MulAction.mem_stabilizer_iff.mp h

theorem eq_infty_of_smul_eq
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {e : suzukiGroup a K}
    (he : e ∈ suzukiU a K) (he1 : e ≠ 1) {y : ℙ K (Fin 4 → K)} (hy : y ∈ suzukiOmega a K)
    (hey : e • y = y) : y = suzukiInfty K := by
  by_contra hne
  exact CFSG.LieType.SteinbergBR.smul_ne_of_mem_conj_suzukiU hK (g := 1) (by simpa using he) he1
    hy (by simpa using hne) hey

theorem fix_infty_of_commute
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {e x : suzukiGroup a K}
    (he : e ∈ suzukiU a K) (he1 : e ≠ 1) (hx : e * x = x * e) : x ∈ suzukiB a K := by
  rw [← (suzuki_ovoid_stabilizer hK).1, MulAction.mem_stabilizer_iff]
  refine eq_infty_of_smul_eq hK he he1
    (suzuki_smul_mem_suzukiOmega hK x (suzukiInfty_mem_suzukiOmega a K)) ?_
  rw [← mul_smul, hx, mul_smul, smul_infty_of_mem_suzukiU hK he]

theorem fix_infty_of_normalizes
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {O : Subgroup (suzukiGroup a K)}
    (hOU : O ≤ suzukiU a K) (hO1 : O ≠ ⊥) {x : suzukiGroup a K}
    (hx : x ∈ Subgroup.normalizer (O : Set (suzukiGroup a K))) : x ∈ suzukiB a K := by
  obtain ⟨o, ho1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO1
  have h1 : x⁻¹ * (o : suzukiGroup a K) * x ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) o).mp o.2
    simpa using this
  rw [← (suzuki_ovoid_stabilizer hK).1, MulAction.mem_stabilizer_iff]
  refine eq_infty_of_smul_eq hK (hOU o.2) (fun h => ho1 (Subtype.ext h))
    (suzuki_smul_mem_suzukiOmega hK x (suzukiInfty_mem_suzukiOmega a K)) ?_
  have e : (o : suzukiGroup a K) = x * (x⁻¹ * o * x) * x⁻¹ := by group
  rw [e, mul_smul, mul_smul, inv_smul_smul, smul_infty_of_mem_suzukiU hK (hOU h1)]

end Ovoid

section Borel

variable [Finite K]

theorem card_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiU a K) = 2 ^ (2 * (2 * a + 1)) := by
  rw [(suzuki_unipotent_structure hK).2.1, ← pow_mul, mul_comm]

theorem isPGroup_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : IsPGroup 2 (suzukiU a K) :=
  IsPGroup.of_card (card_suzukiU hK)

theorem suzukiB_le_normalizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
  sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)

theorem le_suzukiB_of_permute
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {B₀ : Subgroup (suzukiGroup a K)} (hab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x)
    (hodd : Odd (Nat.card B₀))
    (hperm : (B₀ : Set (suzukiGroup a K)) * (suzukiU a K : Set (suzukiGroup a K)) =
      (suzukiU a K : Set (suzukiGroup a K)) * B₀) :
    B₀ ≤ suzukiB a K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  set U := suzukiU a K with hU
  have hUp := isPGroup_suzukiU hK
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 := card_suzukiU (a := a) hK
    rw [← hU, h, Subgroup.card_bot] at h1
    have : 1 < 2 ^ (2 * (2 * a + 1)) := Nat.one_lt_two_pow (by omega)
    omega
  have hsolv := Tri.isSolvable_sup_of_permute hab hodd hUp hperm
  have hE2 : ∀ e ∈ suzukiZ0 a K, e * e = 1 := by
    intro e he
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 he
    rw [suzukiSElt_mul hK, ← suzukiSElt_zero_zero (a := a) hK]
    congr 1
    · ring
    · rw [zero_pow (pow_ne_zero _ two_ne_zero), zero_mul, add_zero]
      linear_combination v * h2
  have hE4 : 4 ≤ Nat.card (suzukiZ0 a K) := by
    have hinj : Function.Injective fun v : K => suzukiSElt a K 0 v := fun v w h =>
      (suzukiSElt_inj.mp h).2
    have h1 : Nat.card K ≤ Nat.card (suzukiZ0 a K) :=
      Nat.card_le_card_of_injective (fun v => ⟨suzukiSElt a K 0 v,
        (mem_suzukiZ0_iff hK).2 ⟨v, rfl⟩⟩) fun v w h => hinj (congrArg Subtype.val h)
    rw [hK] at h1
    omega
  have hC : ∀ e ∈ suzukiZ0 a K, e ≠ 1 → ∀ x : suzukiGroup a K,
      e * x = x * e → x ∈ Subgroup.normalizer (U : Set (suzukiGroup a K)) := fun e he he1 x hx =>
    suzukiB_le_normalizer hK (fix_infty_of_commute hK (suzukiZ0_le_suzukiU he) he1 hx)
  have hP := Tri.pCore_ne_bot_of_solvable hsolv le_sup_right hUp hU1 suzukiZ0_le_suzukiU
    (suzuki_unipotent_structure hK).2.2.2.2.1 hE2 hE4 hC
  set R := B₀ ⊔ U with hR
  set O := (CFSG.pCore 2 ↥R).map R.subtype with hO
  have hO1 : O ≠ ⊥ := by
    rw [hO, Ne, Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective]
    exact hP
  have hOp : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2) (G := ↥R)).map R.subtype
  have hRN := Tri.le_normalizer_pCore_map R
  have hOU : O ≤ U := by
    have hsup := hOp.to_sup_of_normal_left' hUp ((le_sup_right : U ≤ R).trans hRN)
    obtain ⟨Usyl, hUsyl⟩ := SuzukiModel.exists_sylow_eq_suzukiU (a := a) hK
    have heq := Usyl.is_maximal' hsup (hUsyl.le.trans le_sup_right)
    rw [hUsyl] at heq
    exact le_sup_left.trans heq.le
  intro b hb
  exact fix_infty_of_normalizes hK hOU hO1 (hRN (le_sup_left (b := U) hb))

theorem pow_eq_one_of_mem_suzukiB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : suzukiGroup a K}
    (hb : b ∈ suzukiB a K) (hodd : Odd (orderOf b)) : b ^ (2 ^ (2 * a + 1) - 1) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨-, -, hTcard, hTN, -, hBUT, -⟩ := suzuki_borel_structure hK
  have hb' : b ∈ (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) := by
    rw [← hBUT]
    exact hb
  obtain ⟨u, hu, t, ht, rfl⟩ := hb'
  have hpow : ∀ k : ℕ, ∃ u' ∈ suzukiU a K, (u * t) ^ k = u' * t ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | succ k ih =>
      obtain ⟨u', hu', he⟩ := ih
      refine ⟨u' * (t ^ k * u * (t ^ k)⁻¹), Subgroup.mul_mem _ hu' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTN (Subgroup.pow_mem _ ht k)) u).mp hu
      · rw [pow_succ, he, pow_succ]
        group
  have htq : t ^ (2 ^ (2 * a + 1) - 1) = 1 := by
    rw [← hTcard]
    have h1 : (⟨t, ht⟩ : ↥(suzukiT a K)) ^ Nat.card ↥(suzukiT a K) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  obtain ⟨u', hu', he⟩ := hpow (2 ^ (2 * a + 1) - 1)
  rw [htq, mul_one] at he
  obtain ⟨j, hj⟩ := isPGroup_suzukiU hK ⟨u', hu'⟩
  have hu'j : u' ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (orderOf (u * t)) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  have h1 : orderOf ((u * t) ^ (2 ^ (2 * a + 1) - 1)) ∣ orderOf (u * t) := orderOf_pow_dvd _
  have h2 : orderOf ((u * t) ^ (2 ^ (2 * a + 1) - 1)) ∣ 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by rw [he]; exact hu'j)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

end Borel

section Norm

variable [Finite K]

theorem eq_one_of_smul_one_mem
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {s : suzukiGroup a K} {c : K}
    (hs : (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = c • 1) :
    c = 1 := by
  have h := det_suzukiGroup s
  rw [hs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
  exact eq_one_of_pow_two_pow_eq_one hK 2 (by norm_num [h])

theorem mem_natImage_of_two_pow
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : MulAut (StdMod (Fin 4) K)} (hg : g ∈ natNorm (suzukiGroup a K)) {j : ℕ}
    (hgj : g ^ 2 ^ j = 1) : g ∈ natImage (suzukiGroup a K) := by
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hcop : Nat.Coprime (2 ^ j) (Nat.card (Outer (suzukiGroup a K))) := by
    obtain ⟨-, hdvd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
    have h2 : Nat.Coprime (2 ^ j) (2 * a + 1) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr (odd_two_mul_add_one a))
    exact h2.coprime_dvd_right hdvd
  have hin : conjHom (suzukiGroup a K) ⟨g, hg⟩ ∈ inner (suzukiGroup a K) := by
    refine mem_inner_of_pow_eq_one (k := 2 ^ j) ?_ hcop
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(natNorm (suzukiGroup a K))) ^ 2 ^ j = 1 := Subtype.ext hgj
    rw [this, map_one]
  obtain ⟨s, hs⟩ := hin
  obtain ⟨c, hc⟩ := exists_smul_of_conjHom_eq hasScalarCommutant _ s hs.symm
  set S : Matrix (Fin 4) (Fin 4) K :=
    (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hS
  have hpow : ∀ (k : ℕ) (w : Fin 4 → K), toAddMap (g ^ k) w = c ^ k • ((S ^ k) *ᵥ w) := by
    intro k
    induction k with
    | zero => intro w; simp [toAddMap_one]
    | succ k ih =>
      intro w
      rw [pow_succ, toAddMap_mul, hc, ih, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec]
      simp only [pow_succ]
  have hM : (c ^ 2 ^ j) • (S ^ 2 ^ j) = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    have h1 := hpow (2 ^ j) v
    rw [hgj, toAddMap_one] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact h1.symm
  have hdet : (c ^ 2 ^ j) ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_pow, Fintype.card_fin, Matrix.det_one, hS, det_suzukiGroup,
      one_pow, mul_one] at h1
    exact h1
  have hc1 : c = 1 := eq_one_of_pow_two_pow_eq_one hK (j + 2) (by
    rw [pow_add, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
    exact hdet)
  refine ⟨s, toAddMap_injective fun v => ?_⟩
  rw [hc, hc1, one_smul, toAddMap_natAut]

end Norm

section Scalar

abbrev scalHom : Kˣ →* GL (Fin 4) K :=
  Units.map (Matrix.scalar (Fin 4) : K →+* Matrix (Fin 4) (Fin 4) K).toMonoidHom

theorem coe_scalHom (u : Kˣ) :
    ((scalHom u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = (u : K) • 1 := by
  rw [Units.coe_map]
  change Matrix.scalar (Fin 4) (u : K) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem scalHom_commute (u : Kˣ) (g : GL (Fin 4) K) : Commute (scalHom u) g := by
  change scalHom u * g = g * scalHom u
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_scalHom, Matrix.smul_mul, Matrix.mul_smul, one_mul,
    mul_one]

end Scalar

section Lin

variable [Finite K]

theorem exists_scalHom_mul (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : GL (Fin 4) K}
    (hA : matAut A ∈ natNorm (suzukiGroup a K)) :
    ∃ u : Kˣ, ∃ s : suzukiGroup a K, A = scalHom u * (s : GL (Fin 4) K) := by
  obtain ⟨s, c, hc⟩ := exists_smul_of_linear ha hK hA (isSemilinear_matAut A)
  have hM : (A : Matrix (Fin 4) (Fin 4) K) =
      c • (((s : suzukiGroup a K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, ← hc v, toAddMap_matAut]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := A.mul_inv
    rw [hM, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 c hc0, s, Units.ext ?_⟩
  rw [Units.val_mul, coe_scalHom, hM, Units.val_mk0, Matrix.smul_mul, one_mul]

end Lin

section Upper

variable [Finite K]

theorem le_of_permutes (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {X : Subgroup (MulAut (StdMod (Fin 4) K))}
    (hX1 : natImage (suzukiGroup a K) ≤ X) (hX2 : X ≤ natNorm (suzukiGroup a K))
    {Y B S : Subgroup (MulAut (StdMod (Fin 4) K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (StdMod (Fin 4) K))) * S = S * B) : c ≤ 2 * a + 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  have hBN : B ≤ natNorm (suzukiGroup a K) := hBX.trans hX2
  have hSL : S ≤ natImage (suzukiGroup a K) := fun s hs => by
    obtain ⟨j, hj⟩ := hS.isPGroup ⟨s, hs⟩
    exact mem_natImage_of_two_pow ha hK (hX2 (hS.le hs)) (congrArg Subtype.val hj)
  have hperm : ((B ⊓ linSub : Subgroup (MulAut (StdMod (Fin 4) K))) :
      Set (MulAut (StdMod (Fin 4) K))) * S = S * (B ⊓ linSub : Subgroup _) := by
    apply SL3Pair.mul_comm_of_subset
    rintro _ ⟨u, hu, b, hb, rfl⟩
    have hub : u * b ∈ (S : Set (MulAut (StdMod (Fin 4) K))) * B := Set.mul_mem_mul hu hb.1
    rw [← hBS] at hub
    obtain ⟨b', hb', s, hs, hbs⟩ := hub
    have hbs' : b' * s = u * b := hbs
    have hb'L : b' ∈ linSub := by
      have e : b' = u * b * s⁻¹ := by rw [← hbs']; group
      rw [e]
      exact linSub.mul_mem (linSub.mul_mem (natImage_le_linSub _ (hSL hu)) hb.2)
        (linSub.inv_mem (natImage_le_linSub _ (hSL hs)))
    exact ⟨b', ⟨hb', hb'L⟩, s, hs, hbs⟩
  set ν := natAut (suzukiGroup a K) with hν
  have hνinj : Function.Injective ν := natAut_injective _
  have hLnX : ((natImage (suzukiGroup a K)).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hSyl : IsSylowIn 2 S (natImage (suzukiGroup a K)) := by
    have h := hS.inf_normal hX1 hLnX
    rwa [inf_eq_left.mpr hSL] at h
  set U' := S.comap ν with hU'
  have hU'map : U'.map ν = S := Subgroup.map_comap_eq_self hSL
  have htopmap : (⊤ : Subgroup (suzukiGroup a K)).map ν = natImage (suzukiGroup a K) := by
    rw [← MonoidHom.range_eq_map]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective hνinj, hU'map, htopmap]
    exact hSyl
  let P' : Sylow 2 (suzukiGroup a K) := hU'syl.isPGroup.toSylow (by
    have := hU'syl.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨Usyl, hUsyl⟩ := SuzukiModel.exists_sylow_eq_suzukiU (a := a) hK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P' Usyl
  have hgU : U'.map (MulAut.conj g).toMonoidHom = suzukiU a K := by
    rw [← hUsyl, ← hg]
    rfl
  set c₀ := ν g with hc₀
  set U₁ := (suzukiU a K).map ν with hU₁def
  have hU₁ : S.map (MulAut.conj c₀).toMonoidHom = U₁ := by
    rw [hU₁def, ← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * ν x * c₀⁻¹ = ν (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := natImage_le_linSub _ ⟨g, rfl⟩
  have hc₀N : c₀ ∈ natNorm (suzukiGroup a K) := Subgroup.le_normalizer ⟨g, rfl⟩
  have hB₁L : B₁ ≤ linSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact linSub.mul_mem (linSub.mul_mem hc₀L hb.2) (linSub.inv_mem hc₀L)
  have hB₁N : B₁ ≤ natNorm (suzukiGroup a K) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (natNorm _).mul_mem ((natNorm _).mul_mem hc₀N (hBN hb.1)) ((natNorm _).inv_mem hc₀N)
  have hB₁ab : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx.1 y hy.1]
  have hperm₁ : (B₁ : Set (MulAut (StdMod (Fin 4) K))) * (U₁ : Set (MulAut (StdMod (Fin 4) K))) =
      (U₁ : Set (MulAut (StdMod (Fin 4) K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm, Set.image_mul]
  set UG := (suzukiU a K).map (suzukiGroup a K).subtype with hUG
  have hU₁eq : U₁ = UG.map matHom := by
    rw [hU₁def, hUG, Subgroup.map_map]
    rfl
  set B₂ := B₁.comap matHom with hB₂
  have hB₂map : B₂.map matHom = B₁ := Subgroup.map_comap_eq_self (by
    intro z hz
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hz)
    exact ⟨A, rfl⟩)
  have hperm₂ : (B₂ : Set (GL (Fin 4) K)) * (UG : Set (GL (Fin 4) K)) =
      (UG : Set (GL (Fin 4) K)) * B₂ := by
    apply (Set.image_injective.mpr (matHom_injective (ι := Fin 4) (K := K)))
    rw [Set.image_mul, Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, hB₂map, ← hU₁eq,
      hperm₁]
  have hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x := fun x hx y hy =>
    matHom_injective (by rw [map_mul, map_mul]; exact hB₁ab _ hx _ hy)
  have hB₂k : ∀ x ∈ B₂, x ^ Nat.card B₂ = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B₂ hx)
  have hB₂odd : Odd (Nat.card B₂) := by
    have h2 : Nat.card B₂ = Nat.card B₁ := by
      rw [← hB₂map]
      exact (Subgroup.card_map_of_injective matHom_injective).symm
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linSub) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    have h4 : Nat.card ↥(B ⊓ linSub) ∣ Nat.card B := Subgroup.card_dvd_of_le inf_le_left
    rw [h2, h3]
    exact Odd.of_dvd_nat hBodd h4
  set Zc : Subgroup (GL (Fin 4) K) := (scalHom (K := K)).range with hZc
  have hZcomm : ∀ z ∈ Zc, ∀ x : GL (Fin 4) K, Commute z x := by
    rintro _ ⟨u, rfl⟩ x
    exact scalHom_commute u x
  have hZcN : Zc.Normal := ⟨fun z hz x => by
    rw [(hZcomm z hz x).symm.eq, mul_inv_cancel_right]
    exact hz⟩
  set B₃ := (B₂ ⊔ Zc).comap (suzukiGroup a K).subtype with hB₃
  have hB₃mem : ∀ x : suzukiGroup a K,
      x ∈ B₃ ↔ ∃ b ∈ B₂, ∃ z ∈ Zc, b * z = (x : GL (Fin 4) K) := fun x =>
    Subgroup.mem_sup_of_normal_right
  have hB₃ab : ∀ x ∈ B₃, ∀ y ∈ B₃, x * y = y * x := by
    intro x hx y hy
    obtain ⟨b₁, hb₁, z₁, hz₁, e₁⟩ := (hB₃mem x).1 hx
    obtain ⟨b₂, hb₂, z₂, hz₂, e₂⟩ := (hB₃mem y).1 hy
    apply Subtype.ext
    change (x : GL (Fin 4) K) * y = y * x
    rw [← e₁, ← e₂]
    have hb : Commute b₁ b₂ := hB₂ab b₁ hb₁ b₂ hb₂
    have h : Commute (b₁ * z₁) (b₂ * z₂) :=
      (hb.mul_right (hZcomm z₂ hz₂ b₁).symm).mul_left
        ((hZcomm z₁ hz₁ b₂).mul_right (hZcomm z₁ hz₁ z₂))
    exact h.eq
  have hB₃k : ∀ x ∈ B₃, x ^ Nat.card B₂ = 1 := by
    intro x hx
    obtain ⟨b, hb, z, hz, e⟩ := (hB₃mem x).1 hx
    obtain ⟨u, rfl⟩ := hz
    have h1 : ((x ^ Nat.card B₂ : suzukiGroup a K) : GL (Fin 4) K) = scalHom (u ^ Nat.card B₂) := by
      rw [SubmonoidClass.coe_pow, ← e, (scalHom_commute u b).symm.mul_pow, hB₂k b hb, one_mul,
        map_pow]
    have h2 : ((u ^ Nat.card B₂ : Kˣ) : K) = 1 :=
      eq_one_of_smul_one_mem hK (s := x ^ Nat.card B₂) (by rw [h1, coe_scalHom])
    have hu : u ^ Nat.card B₂ = 1 := Units.ext h2
    apply Subtype.ext
    rw [h1, hu, map_one]
    rfl
  have hB₃odd : Odd (Nat.card B₃) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥B₃) 2 (even_iff_two_dvd.mp hev)
    have h1 : (t : suzukiGroup a K) ^ Nat.card B₂ = 1 := hB₃k t t.2
    have h2 : orderOf (t : suzukiGroup a K) ∣ Nat.card B₂ := orderOf_dvd_of_pow_eq_one h1
    rw [Subgroup.orderOf_coe, ht] at h2
    exact (Nat.not_even_iff_odd.mpr hB₂odd) (even_iff_two_dvd.mpr h2)
  have hperm₃ : (B₃ : Set (suzukiGroup a K)) * (suzukiU a K : Set (suzukiGroup a K)) =
      (suzukiU a K : Set (suzukiGroup a K)) * B₃ := by
    apply SL3Pair.mul_comm_of_subset
    rintro _ ⟨u, hu, x, hx, rfl⟩
    obtain ⟨b, hb, z, hz, e⟩ := (hB₃mem x).1 hx
    have hub : (u : GL (Fin 4) K) * b ∈ (UG : Set (GL (Fin 4) K)) * B₂ :=
      Set.mul_mem_mul ⟨u, hu, rfl⟩ hb
    rw [← hperm₂] at hub
    obtain ⟨b', hb', w, ⟨u', hu', rfl⟩, hbw⟩ := hub
    refine ⟨u * x * u'⁻¹, (hB₃mem _).2 ⟨b', hb', z, hz, ?_⟩, u', hu', inv_mul_cancel_right _ _⟩
    have hbw' : b' * (u' : GL (Fin 4) K) = u * b := hbw
    have hc : (u' : GL (Fin 4) K) * z = z * u' := (hZcomm z hz _).symm.eq
    change b' * z = (u : GL (Fin 4) K) * x * (u' : GL (Fin 4) K)⁻¹
    calc b' * z = b' * u' * z * (u' : GL (Fin 4) K)⁻¹ := by
          rw [mul_assoc b', hc, ← mul_assoc, mul_inv_cancel_right]
      _ = u * b * z * (u' : GL (Fin 4) K)⁻¹ := by rw [hbw']
      _ = u * x * (u' : GL (Fin 4) K)⁻¹ := by rw [← e, mul_assoc (u : GL (Fin 4) K) b z]
  have hB₃B : B₃ ≤ suzukiB a K := le_suzukiB_of_permute ha hK hB₃ab hB₃odd hperm₃
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hz)
    have hA2 : A ∈ B₂ := hz
    obtain ⟨u, s, hAs⟩ := exists_scalHom_mul ha hK (hB₁N hz)
    have hs3 : s ∈ B₃ := by
      rw [hB₃mem]
      refine ⟨A, hA2, scalHom u⁻¹, ⟨u⁻¹, rfl⟩, ?_⟩
      rw [hAs, (scalHom_commute u _).eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hsodd : Odd (orderOf s) := Odd.of_dvd_nat hB₃odd (Subgroup.orderOf_dvd_natCard B₃ hs3)
    have hs1 := pow_eq_one_of_mem_suzukiB hK (hB₃B hs3) hsodd
    have hu1 : u ^ (Nat.card K - 1) = 1 := by
      rw [← Nat.card_units]
      exact pow_card_eq_one'
    have hA1 : A ^ (Nat.card K - 1) = 1 := by
      rw [hAs, (scalHom_commute u _).mul_pow, ← map_pow, hu1, map_one, one_mul, hK,
        ← SubmonoidClass.coe_pow, hs1]
      rfl
    rw [← matHom_apply, ← map_pow, hA1, map_one]
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (StdMod (Fin 4) K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (StdMod (Fin 4) K)) ∈ B := hYB y.2
  obtain ⟨σ, hσ⟩ := exists_semilinear (hasScalarCommutant (a := a)) (hBN hyB)
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  set m := orderOf σ with hm
  have hmn : m ∣ 2 * a + 1 := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two (by omega) hK
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := orderOf_pos σ
  have hym : (y : MulAut (StdMod (Fin 4) K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h' := hσ.pow m
    rw [hm, pow_orderOf_eq_one] at h'
    exact h'
  have hypow : (y : MulAut (StdMod (Fin 4) K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (StdMod (Fin 4) K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ (2 * a + 1) - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hX1 : natImage (suzukiGroup a K) ≤ X)
    (hX2 : X ≤ natNorm (suzukiGroup a K)) : E3.nPrime X ≤ 2 * a + 1 := by
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun x hx y hy => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes ha hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end Upper

section Lower

variable [Finite K]

theorem le_nPrime (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hX1 : natImage (suzukiGroup a K) ≤ X)
    (hX2 : X ≤ natNorm (suzukiGroup a K)) : 2 * a + 1 ≤ E3.nPrime X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 4) K)) := MulEquiv.finite_left
  have : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  set ν := natAut (suzukiGroup a K) with hν
  have hνinj : Function.Injective ν := natAut_injective _
  obtain ⟨-, hTab, hTcard, hTN, -, -, -, -⟩ := suzuki_borel_structure hK
  obtain ⟨Usyl, hUsyl⟩ := SuzukiModel.exists_sylow_eq_suzukiU (a := a) hK
  have hU₁p : IsPGroup 2 ((suzukiU a K).map ν) := (isPGroup_suzukiU hK).map ν
  have hU₁X : (suzukiU a K).map ν ≤ X := (Subgroup.map_le_range _ _).trans hX1
  obtain ⟨S, hS, hU₁S⟩ := exists_isSylowIn_ge 2 hU₁X hU₁p
  have hSL : S ≤ natImage (suzukiGroup a K) := fun s hs => by
    obtain ⟨j, hj⟩ := hS.isPGroup ⟨s, hs⟩
    exact mem_natImage_of_two_pow ha hK (hX2 (hS.le hs)) (congrArg Subtype.val hj)
  have hSeq : S = (suzukiU a K).map ν := by
    have hp : IsPGroup 2 (S.comap ν) := hS.isPGroup.comap_of_injective ν hνinj
    have hle : (Usyl : Subgroup (suzukiGroup a K)) ≤ S.comap ν := by
      rw [hUsyl]
      intro u hu
      exact hU₁S ⟨u, hu, rfl⟩
    have h1 := Usyl.is_maximal' hp hle
    rw [hUsyl] at h1
    calc S = (S.comap ν).map ν := (Subgroup.map_comap_eq_self hSL).symm
      _ = (suzukiU a K).map ν := by rw [h1]
  have hT₁X : (suzukiT a K).map ν ≤ X := (Subgroup.map_le_range _ _).trans hX1
  have hT₁ab : ∀ x ∈ (suzukiT a K).map ν, ∀ y ∈ (suzukiT a K).map ν, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hTab x hx y hy]
  have hT₁card : Nat.card ((suzukiT a K).map ν) = 2 ^ (2 * a + 1) - 1 := by
    rw [Subgroup.card_map_of_injective hνinj, hTcard]
  have hT₁odd : Odd (Nat.card ((suzukiT a K).map ν)) := by
    rw [hT₁card]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hT₁cyc : IsCyclic ((suzukiT a K).map ν) := by
    have := SuzukiModel.isCyclic_suzukiT (a := a) (K := K)
    exact isCyclic_of_surjective ((suzukiT a K).equivMapOfInjective ν hνinj).toMonoidHom
      (MulEquiv.surjective _)
  have hTU : (suzukiT a K : Set (suzukiGroup a K)) * (suzukiU a K : Set (suzukiGroup a K)) =
      (suzukiU a K : Set (suzukiGroup a K)) * (suzukiT a K : Set (suzukiGroup a K)) :=
    Subgroup.set_mul_normalizer_comm _ _ fun _ hx => hTN hx
  have hBS : (((suzukiT a K).map ν : Subgroup (MulAut (StdMod (Fin 4) K))) :
      Set (MulAut (StdMod (Fin 4) K))) * S = S * ((suzukiT a K).map ν : Subgroup _) := by
    rw [hSeq, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hTU, Set.image_mul]
  exact E3.le_nPrime le_rfl hT₁X hT₁cyc hT₁card hT₁ab hT₁odd hS hBS

theorem nPrime_eq (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {X : Subgroup (MulAut (StdMod (Fin 4) K))} (hX1 : natImage (suzukiGroup a K) ≤ X)
    (hX2 : X ≤ natNorm (suzukiGroup a K)) : E3.nPrime X = 2 * a + 1 :=
  le_antisymm (nPrime_le ha hK hX1 hX2) (le_nPrime ha hK hX1 hX2)

end Lower

end Sz

theorem H3_Sz_nPrime {V : Type*} [CommGroup V] [Finite V]
    {L M : Subgroup (MulAut V)} {n : ℕ} (hL : BinaryNaturalSz L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : E3.nPrime M = n := by
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hL
  obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLM hMN
  rw [← nPrime_map_congrHom e M]
  exact Sz.nPrime_eq ha hK h1 h2

theorem H3_Sz_mParam {V : Type*} [CommGroup V] [Finite V]
    {L M : Subgroup (MulAut V)} {n : ℕ} (hL : BinaryNaturalSz L ⊤ ⊥ n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut V))) : 2 * n ≤ E3.mParam M ∧ 3 ≤ n := by
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hL
  obtain ⟨e, -, h2⟩ := exists_transport_natural hreal hLM hMN
  refine ⟨?_, by omega⟩
  rw [← mParam_map_congrHom e M]
  exact Sz.le_mParam ha hK h2

end H

end CFSG.Quasithin
