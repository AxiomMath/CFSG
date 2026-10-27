module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base8
public import CFSG.Quasithin.Background.HSp4PairNPrime
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base3
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base4
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base7
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base19
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base20
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base21
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open scoped Pointwise

variable {K : Type} [Field K]

local notation "I4" => (Fin 2 ⊕ Fin 2)

theorem permute_lin_Sp4 [Finite K] [CharP K 2] {B S : Subgroup (MulAut (StdMod I4 K))}
    (hBN : B ≤ natNorm (StatedSp 2 K)) (hSN : S ≤ natNorm (StatedSp 2 K))
    (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set (MulAut (StdMod I4 K))) * S = S * B) :
    ((B ⊓ linSub : Subgroup (MulAut (StdMod I4 K))) : Set (MulAut (StdMod I4 K))) *
        ((S ⊓ natImage (StatedSp 2 K) : Subgroup (MulAut (StdMod I4 K))) :
          Set (MulAut (StdMod I4 K))) =
      ((S ⊓ natImage (StatedSp 2 K) : Subgroup (MulAut (StdMod I4 K))) :
          Set (MulAut (StdMod I4 K))) *
        ((B ⊓ linSub : Subgroup (MulAut (StdMod I4 K))) : Set (MulAut (StdMod I4 K))) := by
  classical
  have hΓ := Sp4.hasScalarCommutant_statedSp (K := K)
  have : Finite (MulAut (StdMod I4 K)) := MulEquiv.finite_left
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linSub := natImage_le_linSub _ hu.2
  have hub : u * b ∈ (S : Set (MulAut (StdMod I4 K))) * B := Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linSub := linSub.mul_mem huL hb.2
  let φ := fieldHom hΓ
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hσ1 : φ ⟨b', hBN hb'⟩ = 1 := by
    have h1 : φ ⟨b', hBN hb'⟩ * φ ⟨s, hSN hs⟩ = 1 := by
      rw [← map_mul]
      have hm : u * b ∈ natNorm (StatedSp 2 K) := by
        rw [← hbs']
        exact (natNorm _).mul_mem (hBN hb') (hSN hs)
      have : (⟨b', hBN hb'⟩ * ⟨s, hSN hs⟩ : ↥(natNorm (StatedSp 2 K))) = ⟨u * b, hm⟩ :=
        Subtype.ext hbs'
      rw [this]
      exact (fieldHom_eq_one_iff hΓ _).mpr hubL
    have h2 : φ ⟨b', hBN hb'⟩ ^ Nat.card B = 1 := by
      rw [← map_pow]
      have : (⟨b', hBN hb'⟩ : ↥(natNorm (StatedSp 2 K))) ^ Nat.card B = 1 :=
        Subtype.ext (by simpa using hb'k)
      rw [this, map_one]
    have h3 : φ ⟨b', hBN hb'⟩ ^ 2 ^ j = 1 := by
      have h4 : φ ⟨s, hSN hs⟩ ^ 2 ^ j = 1 := by
        rw [← map_pow]
        have : (⟨s, hSN hs⟩ : ↥(natNorm (StatedSp 2 K))) ^ 2 ^ j = 1 :=
          Subtype.ext (by simpa using hsj)
        rw [this, map_one]
      rw [eq_inv_of_mul_eq_one_left h1, inv_pow, h4, inv_one]
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
  have hb'L : b' ∈ linSub := (fieldHom_eq_one_iff hΓ _).mp hσ1
  have hse : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  have hsL : s ∈ linSub := by
    rw [hse]
    exact linSub.mul_mem (linSub.inv_mem hb'L) hubL
  obtain ⟨Bs, σ, D, -, hx⟩ := Sp4.exists_eq_of_mem_natNorm (hSN hs)
  have hσ : σ = RingEquiv.refl K := (Sp4.isSemilinear_of_eq hx).unique (mem_linSub.mp hsL)
  subst hσ
  have hsI := Sp4.eq_natAut_of_pow_two_pow (fun v => hx v) hsj
  refine ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, ?_⟩, hbs⟩
  rw [hsI]
  exact ⟨Bs, rfl⟩

theorem le_of_permutes_Sp4 [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {X : Subgroup (MulAut (StdMod I4 K))}
    (hX1 : natImage (StatedSp 2 K) ≤ X) (hX2 : X ≤ natNorm (StatedSp 2 K))
    {Y B S : Subgroup (MulAut (StdMod I4 K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (StdMod I4 K))) * S = S * B) : c ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod I4 K)) := MulEquiv.finite_left
  have hΓ := Sp4.hasScalarCommutant_statedSp (K := K)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hBN : B ≤ natNorm (StatedSp 2 K) := hBX.trans hX2
  have hSN : S ≤ natNorm (StatedSp 2 K) := hS.le.trans hX2
  have hperm := permute_lin_Sp4 hBN hSN hBodd hS.isPGroup hBS
  set ρ := natAut (StatedSp 2 K) with hρ
  have hρinj : Function.Injective ρ := natAut_injective _
  have hρrange : ρ.range = natImage (StatedSp 2 K) := rfl
  have hLnX : ((natImage (StatedSp 2 K)).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ natImage (StatedSp 2 K)).comap ρ with hU'
  have hU'map : U'.map ρ = S ⊓ natImage (StatedSp 2 K) :=
    Subgroup.map_comap_eq_self (by rw [hρrange]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup ↥(StatedSp 2 K)).map ρ = natImage (StatedSp 2 K) := by
    rw [← MonoidHom.range_eq_map, hρrange]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective hρinj, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 ↥(StatedSp 2 K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨P₀, hP₀⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSp 2 K) P' P₀
  have hgU : U'.map (MulAut.conj g).toMonoidHom = unipotent 2 K := by
    rw [← hP₀, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := ρ g with hc₀
  have hU₁ : (S ⊓ natImage (StatedSp 2 K)).map (MulAut.conj c₀).toMonoidHom =
      (unipotent 2 K).map ρ := by
    rw [← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * ρ x * c₀⁻¹ = ρ (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := natImage_le_linSub _ ⟨g, rfl⟩
  have hB₁L : B₁ ≤ linSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact linSub.mul_mem (linSub.mul_mem hc₀L hb.2) (linSub.inv_mem hc₀L)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  have hB₁odd : Odd (Nat.card B₁) := by
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linSub) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    rw [h3]
    exact Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
  set Uq := (unipotent 2 K).map (StatedSp 2 K).subtype with hUq
  have hU₁' : (unipotent 2 K).map ρ = Uq.map matHom := by
    rw [hUq, Subgroup.map_map]
    rfl
  have hperm₁ : (B₁ : Set (MulAut (StdMod I4 K))) * (Uq.map matHom :
      Subgroup (MulAut (StdMod I4 K))) =
      (Uq.map matHom : Subgroup (MulAut (StdMod I4 K))) * B₁ := by
    rw [← hU₁', ← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  set B₂ := B₁.comap (matHom (ι := I4) (K := K)) with hB₂
  have hB₂map : B₂.map matHom = B₁ := Subgroup.map_comap_eq_self (fun x hx => by
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hx)
    exact ⟨A, rfl⟩)
  have hperm₂ : (B₂ : Set (GL I4 K)) * (Uq : Set (GL I4 K)) = (Uq : Set (GL I4 K)) * B₂ := by
    have h1 := hperm₁
    rw [← hB₂map, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul] at h1
    exact Set.image_injective.mpr matHom_injective h1
  set B₃ := B₂.map (Sp4.reGL K) with hB₃
  set U₃ := Uq.map (Sp4.reGL K) with hU₃
  have hU₃U : U₃ ≤ Tri.uniGL 4 K := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact Sp4.reGL_mem_uniGL hu
  have hU₃N : ∀ a b c d : K, Tri.spN a b c d ∈ U₃ := by
    intro a b c d
    obtain ⟨u, hu, hue⟩ := Sp4.exists_reGL_eq_spN a b c d
    exact ⟨_, ⟨u, hu, rfl⟩, hue⟩
  have hB₂ab : ∀ a ∈ B₂, ∀ b ∈ B₂, a * b = b * a := fun a ha b hb => matHom_injective (by
    rw [map_mul, map_mul]
    exact hB₁ab _ ha _ hb)
  have hB₃ab : ∀ a ∈ B₃, ∀ b ∈ B₃, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hB₂ab a ha b hb]
  have hB₂card : Nat.card B₂ = Nat.card B₁ := by
    have := Subgroup.card_map_of_injective (K := B₂) (matHom_injective (ι := I4) (K := K))
    rw [hB₂map] at this
    exact this.symm
  have hB₃odd : Odd (Nat.card B₃) := by
    rw [hB₃, Subgroup.card_map_of_injective Sp4.reGL_injective, hB₂card]
    exact hB₁odd
  have hB₃U : (B₃ : Set (GL (Fin 4) K)) * (U₃ : Set (GL (Fin 4) K)) =
      (U₃ : Set (GL (Fin 4) K)) * B₃ := by
    rw [hB₃, hU₃, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm₂, Set.image_mul]
  have htri := Tri.triangular_sp4 hK4 hU₃U hU₃N hB₃ab hB₃odd hB₃U
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    obtain ⟨A, hA, rfl⟩ : z ∈ B₂.map matHom := by rw [hB₂map]; exact hz
    have hAB : Sp4.reGL K A ∈ B₃ := ⟨A, hA, rfl⟩
    have hAodd : Odd (orderOf (Sp4.reGL K A)) :=
      Odd.of_dvd_nat hB₃odd (Subgroup.orderOf_dvd_natCard B₃ hAB)
    have h1 := Tri.pow_card_sub_one_eq_one (htri hAB) hAodd
    rw [← map_pow] at h1
    have h2 : A ^ (Nat.card K - 1) = 1 := Sp4.reGL_injective (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (StdMod I4 K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (StdMod I4 K)) ∈ B := hYB y.2
  set σ := fieldHom hΓ (⟨y, hBN hyB⟩ : ↥(natNorm (StatedSp 2 K))) with hσ
  set m := orderOf σ with hm
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have hmn : m ∣ n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := orderOf_pos σ
  have hym : (y : MulAut (StdMod I4 K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : fieldHom hΓ (⟨y, hBN hyB⟩ ^ m : ↥(natNorm (StatedSp 2 K))) = 1 := by
      rw [map_pow, ← hσ, hm, pow_orderOf_eq_one]
    exact (fieldHom_eq_one_iff hΓ _).mp h1
  have hypow : (y : MulAut (StdMod I4 K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (StdMod I4 K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ n - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le_Sp4 [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (StdMod I4 K))} (hX1 : natImage (StatedSp 2 K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSp 2 K)) : E3.nPrime X ≤ n := by
  have : Finite (MulAut (StdMod I4 K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes_Sp4 hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
