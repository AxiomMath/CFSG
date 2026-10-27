module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base4
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base3
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

namespace K5

variable {K : Type} [Field K]

theorem le_of_permutes [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (W6 K))} (hX1 : diagSL K ≤ X) (hX2 : X ≤ normD K)
    {Y B S : Subgroup (MulAut (W6 K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (W6 K))) * S = S * B) : c ≤ 2 * n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  have hBN : B ≤ normD K := hBX.trans hX2
  have hSN : S ≤ normD K := hS.le.trans hX2
  have hperm := permute_lin hBN hSN hBodd hS.isPGroup hBS
  have hLnX : ((diagSL K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ diagSL K).comap dgRho with hU'
  have hU'map : U'.map dgRho = S ⊓ diagSL K :=
    Subgroup.map_comap_eq_self (by rw [range_dgRho]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map dgRho =
      diagSL K := by
    rw [← MonoidHom.range_eq_map, range_dgRho]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective dgRho_injective, hU'map, htopmap]
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
  set c₀ := dgRho g with hc₀
  have hU₁ : (S ⊓ diagSL K).map (MulAut.conj c₀).toMonoidHom =
      (Tri.uni3 K).map (matHom.comp dgHom) := by
    rw [Tri.uni3, Subgroup.map_map, ← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * dgRho x * c₀⁻¹ = dgRho (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := dgSub_le_linSub (matAut_dgHom_mem_dgSub _)
  have hc₀N : c₀ ∈ normD K := Subgroup.le_normalizer (dgRho_mem_diagSL g)
  have hB₁L : B₁ ≤ linSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact linSub.mul_mem (linSub.mul_mem hc₀L hb.2) (linSub.inv_mem hc₀L)
  have hB₁N : B₁ ≤ normD K := by
    rintro _ ⟨b, hb, rfl⟩
    exact (normD K).mul_mem ((normD K).mul_mem hc₀N (hBN hb.1)) ((normD K).inv_mem hc₀N)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  have hB₁odd : Odd (Nat.card B₁) := by
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linSub) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    rw [h3]
    exact Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
  have hperm₁ : (B₁ : Set (MulAut (W6 K))) * ((Tri.uni3 K).map (matHom.comp dgHom) :
      Subgroup (MulAut (W6 K))) =
      ((Tri.uni3 K).map (matHom.comp dgHom) : Subgroup (MulAut (W6 K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  have hz := fun z (hz : z ∈ B₁) => pow_eq_one_of_lin hn hK hB₁N hB₁L hB₁ab hB₁odd hperm₁ hz
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (W6 K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (W6 K)) ∈ B := hYB y.2
  set σ := semiHom (⟨y, hBN hyB⟩ : ↥(normD K)) with hσ
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
  have hym : (y : MulAut (W6 K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : semiHom (⟨y, hBN hyB⟩ ^ m : ↥(normD K)) = 1 := by
      rw [map_pow, ← hσ, hm, pow_orderOf_eq_one]
    exact (semiHom_eq_one_iff _).mp h1
  have hypow : (y : MulAut (W6 K)) ^ (m * (Nat.card K ^ 2 - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (W6 K)) ^ m * c₀⁻¹) ^ (Nat.card K ^ 2 - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ (2 * n) - 1) := by
    rw [← hyo, mul_comm 2 n, pow_mul, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0
    (le_trans (Nat.le_of_dvd (by omega) hmn) (by omega)) hdvd

theorem nPrime_le [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (W6 K))} (hX1 : diagSL K ≤ X) (hX2 : X ≤ normD K) :
    E3.nPrime X ≤ 2 * n := by
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end K5

theorem factNPrimeTwoNat_holds : FactNPrimeTwoNat := by
  intro G _ _ L U n hU hn hLU h2 X hLX hXN
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ := exists_model_X hU hLU h2 hXN
  rw [← nPrime_map_congrHom Φ]
  refine K5.nPrime_le hn hK ?_ hX
  rw [← hL]
  exact Subgroup.map_mono (autI_mono hU hLX)

end CFSG.Quasithin.Vol2.Ch11.SecB
