module

public import CFSG.Quasithin.Background.HSL3PairNPrime

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type} [Field K]


@[expose] noncomputable def rho3 :
    Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (StdMod (Fin 3) K) :=
  matHom.comp Matrix.SpecialLinearGroup.toGL

theorem rho3_injective : Function.Injective (rho3 (K := K)) := fun _ _ h =>
  Matrix.SpecialLinearGroup.toGL_injective (matHom_injective h)

theorem range_rho3 : (rho3 (K := K)).range = natImage (StatedSL 3 K) := by
  rw [rho3, MonoidHom.range_comp, natImage_eq_map, statedSL_eq_range_toGL]

theorem permute_lin_SL3 [Finite K] [CharP K 2] {B S : Subgroup (MulAut (StdMod (Fin 3) K))}
    (hBN : B ≤ natNorm (StatedSL 3 K)) (hSN : S ≤ natNorm (StatedSL 3 K))
    (hBodd : Odd (Nat.card B)) (hS : IsPGroup 2 S)
    (hBS : (B : Set (MulAut (StdMod (Fin 3) K))) * S = S * B) :
    ((B ⊓ linSub : Subgroup (MulAut (StdMod (Fin 3) K))) : Set (MulAut (StdMod (Fin 3) K))) *
        ((S ⊓ natImage (StatedSL 3 K) : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) =
      ((S ⊓ natImage (StatedSL 3 K) : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) *
        ((B ⊓ linSub : Subgroup (MulAut (StdMod (Fin 3) K))) :
          Set (MulAut (StdMod (Fin 3) K))) := by
  classical
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linSub := natImage_le_linSub _ hu.2
  have hub : u * b ∈ (S : Set (MulAut (StdMod (Fin 3) K))) * B := Set.mul_mem_mul hu.1 hb.1
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
      have hm : u * b ∈ natNorm (StatedSL 3 K) := by
        rw [← hbs']
        exact (natNorm _).mul_mem (hBN hb') (hSN hs)
      have : (⟨b', hBN hb'⟩ * ⟨s, hSN hs⟩ : ↥(natNorm (StatedSL 3 K))) = ⟨u * b, hm⟩ :=
        Subtype.ext hbs'
      rw [this]
      exact (fieldHom_eq_one_iff hΓ _).mpr hubL
    have h2 : φ ⟨b', hBN hb'⟩ ^ Nat.card B = 1 := by
      rw [← map_pow]
      have : (⟨b', hBN hb'⟩ : ↥(natNorm (StatedSL 3 K))) ^ Nat.card B = 1 :=
        Subtype.ext (by simpa using hb'k)
      rw [this, map_one]
    have h3 : φ ⟨b', hBN hb'⟩ ^ 2 ^ j = 1 := by
      have h4 : φ ⟨s, hSN hs⟩ ^ 2 ^ j = 1 := by
        rw [← map_pow]
        have : (⟨s, hSN hs⟩ : ↥(natNorm (StatedSL 3 K))) ^ 2 ^ j = 1 :=
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
  obtain ⟨g, rfl⟩ := exists_matAut_of_mem_linSub hsL
  have hgj : g ^ 2 ^ j = 1 := matHom_injective (by
    rw [map_pow, map_one]
    exact hsj)
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hgj
    simp only [Units.val_pow_eq_pow_val, Matrix.det_pow, Units.val_one, Matrix.det_one] at h1
    exact SL3Pair.eq_one_of_pow_two_pow h1
  have hsI : matAut g ∈ natImage (StatedSL 3 K) := by
    rw [natImage_eq_map]
    exact ⟨g, SL3Pair.mem_statedSL_iff.mpr hdet, rfl⟩
  exact ⟨b', ⟨hb', hb'L⟩, matAut g, ⟨hs, hsI⟩, hbs⟩

theorem le_of_permutes_SL3 [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {X : Subgroup (MulAut (StdMod (Fin 3) K))}
    (hX1 : natImage (StatedSL 3 K) ≤ X) (hX2 : X ≤ natNorm (StatedSL 3 K))
    {Y B S : Subgroup (MulAut (StdMod (Fin 3) K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (StdMod (Fin 3) K))) * S = S * B) : c ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hΓ := hasScalarCommutant_statedSL (K := K) (by norm_num : 2 ≤ 3)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hBN : B ≤ natNorm (StatedSL 3 K) := hBX.trans hX2
  have hSN : S ≤ natNorm (StatedSL 3 K) := hS.le.trans hX2
  have hperm := permute_lin_SL3 hBN hSN hBodd hS.isPGroup hBS
  have hLnX : ((natImage (StatedSL 3 K)).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ natImage (StatedSL 3 K)).comap rho3 with hU'
  have hU'map : U'.map rho3 = S ⊓ natImage (StatedSL 3 K) :=
    Subgroup.map_comap_eq_self (by rw [range_rho3]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map rho3 =
      natImage (StatedSL 3 K) := by
    rw [← MonoidHom.range_eq_map, range_rho3]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective rho3_injective, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 3) K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨P₀, hP₀⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) K) P' P₀
  have hgU : U'.map (MulAut.conj g).toMonoidHom = LinearFlag.unitriangular 3 K := by
    rw [← hP₀, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := rho3 g with hc₀
  have hU₁ : (S ⊓ natImage (StatedSL 3 K)).map (MulAut.conj c₀).toMonoidHom =
      (Tri.uni3 K).map matHom := by
    rw [Tri.uni3, Subgroup.map_map, ← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * rho3 x * c₀⁻¹ = rho3 (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := isSemilinear_matAut _
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
  have hperm₁ : (B₁ : Set (MulAut (StdMod (Fin 3) K))) * ((Tri.uni3 K).map matHom :
      Subgroup (MulAut (StdMod (Fin 3) K))) =
      ((Tri.uni3 K).map matHom : Subgroup (MulAut (StdMod (Fin 3) K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  set B₂ := B₁.comap (matHom (ι := Fin 3) (K := K)) with hB₂
  have hB₂map : B₂.map matHom = B₁ := Subgroup.map_comap_eq_self (fun x hx => by
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hx)
    exact ⟨A, rfl⟩)
  have hB₂ab : ∀ a ∈ B₂, ∀ b ∈ B₂, a * b = b * a := fun a ha b hb => matHom_injective (by
    rw [map_mul, map_mul]
    exact hB₁ab _ ha _ hb)
  have hB₂odd : Odd (Nat.card B₂) := by
    have := Subgroup.card_map_of_injective (K := B₂) (matHom_injective (ι := Fin 3) (K := K))
    rw [hB₂map] at this
    rw [← this]
    exact hB₁odd
  have hB₂U : (B₂ : Set (GL (Fin 3) K)) * (Tri.uni3 K : Set (GL (Fin 3) K)) =
      (Tri.uni3 K : Set (GL (Fin 3) K)) * B₂ := by
    have h1 := hperm₁
    rw [← hB₂map, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul] at h1
    exact Set.image_injective.mpr matHom_injective h1
  have htri := Tri.triangular_three hK4 hB₂ab hB₂odd hB₂U
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    obtain ⟨A, hA, rfl⟩ : z ∈ B₂.map matHom := by rw [hB₂map]; exact hz
    have hAodd : Odd (orderOf A) := Odd.of_dvd_nat hB₂odd (Subgroup.orderOf_dvd_natCard B₂ hA)
    rw [← map_pow, SL3Pair.pow_eq_one_of_mem_borGL (htri hA) hAodd, map_one]
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (StdMod (Fin 3) K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (StdMod (Fin 3) K)) ∈ B := hYB y.2
  set σ := fieldHom hΓ (⟨y, hBN hyB⟩ : ↥(natNorm (StatedSL 3 K))) with hσ
  set m := orderOf σ with hm
  have hmn : m ∣ n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
    have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := by
    have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
    exact orderOf_pos σ
  have hym : (y : MulAut (StdMod (Fin 3) K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : fieldHom hΓ (⟨y, hBN hyB⟩ ^ m : ↥(natNorm (StatedSL 3 K))) = 1 := by
      rw [map_pow, ← hσ, hm, pow_orderOf_eq_one]
    exact (fieldHom_eq_one_iff hΓ _).mp h1
  have hypow : (y : MulAut (StdMod (Fin 3) K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (StdMod (Fin 3) K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ n - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le_SL3 [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (StdMod (Fin 3) K))} (hX1 : natImage (StatedSL 3 K) ≤ X)
    (hX2 : X ≤ natNorm (StatedSL 3 K)) : E3.nPrime X ≤ n := by
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes_SL3 hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
