module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base16
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base15

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2]


@[expose] noncomputable def reI (K : Type) [Field K] : GL Ix3 K →* GL (Fin 6) K :=
  Units.map (Matrix.reindexAlgEquiv K K e6).toMonoidHom

omit [CharP K 2] in
theorem coe_reI (g : GL Ix3 K) :
    ((reI K g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.reindex e6 e6 (g : Matrix Ix3 Ix3 K) := rfl

omit [CharP K 2] in
theorem reI_injective : Function.Injective (reI K) := by
  intro g h hgh
  apply Units.ext
  have := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hgh
  simp only [coe_reI] at this
  exact (Matrix.reindex e6 e6).injective this

theorem reI_g2Mat (g : ↥(cayleyGroup K)) : reI K (g2Mat g) = g2Six g := rfl

theorem isScalG2_reI [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {A : GL Ix3 K}
    (hAN : matHom A ∈ natNorm (g2Gam K)) : IsScalG2 (reI K A) := by
  obtain ⟨c, g, hc, hAg⟩ := exists_smul_of_mem_linSub hK hn hAN (isSemilinear_matAut A)
  refine ⟨c, g, hc, ?_⟩
  have hA : (A : Matrix Ix3 Ix3 K) = c • ((g2Mat g : GL Ix3 K) : Matrix Ix3 Ix3 K) := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, g2Mat_mulVec]
    exact hAg v
  rw [coe_reI, hA, ← reI_g2Mat, coe_reI]
  ext i j
  simp [Matrix.reindex_apply]

theorem le_of_permutes_G2 [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {X : Subgroup (MulAut (StdMod Ix3 K))}
    (hX1 : natImage (g2Gam K) ≤ X) (hX2 : X ≤ natNorm (g2Gam K))
    {Y B S : Subgroup (MulAut (StdMod Ix3 K))} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X)
    (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (StdMod Ix3 K))) * S = S * B) : c ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (StdMod Ix3 K)) := MulEquiv.finite_left
  have := finite_cayleyGroup (F := K)
  have hΓ := hasScalarCommutant_g2Gam (K := K)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hBN : B ≤ natNorm (g2Gam K) := hBX.trans hX2
  have hSN : S ≤ natNorm (g2Gam K) := hS.le.trans hX2
  have hperm := permute_lin_G2 hK hn hBN hSN hBodd hS.isPGroup hBS
  set ρ := g2Rho (K := K) with hρ
  have hLnX : ((natImage (g2Gam K)).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ natImage (g2Gam K)).comap ρ with hU'
  have hU'map : U'.map ρ = S ⊓ natImage (g2Gam K) :=
    Subgroup.map_comap_eq_self (by rw [range_g2Rho]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup ↥(cayleyGroup K)).map ρ = natImage (g2Gam K) := by
    rw [← MonoidHom.range_eq_map, range_g2Rho]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective g2Rho_injective, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 ↥(cayleyGroup K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  let P₀ : Sylow 2 ↥(cayleyGroup K) := isPGroup_U0.toSylow (not_two_dvd_index_U0 hK (by omega))
  have hP₀ : (P₀ : Subgroup ↥(cayleyGroup K)) = U0 K := IsPGroup.toSylow_coe _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(cayleyGroup K) P' P₀
  have hgU : U'.map (MulAut.conj g).toMonoidHom = U0 K := by
    rw [← hP₀, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := ρ g with hc₀
  have hU₁ : (S ⊓ natImage (g2Gam K)).map (MulAut.conj c₀).toMonoidHom = (U0 K).map ρ := by
    rw [← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * ρ x * c₀⁻¹ = ρ (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linSub).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linSub := g2Rho_mem_linSub g
  have hc₀N : c₀ ∈ natNorm (g2Gam K) := Subgroup.le_normalizer (g2Rho_mem_natImage g)
  have hB₁L : B₁ ≤ linSub := by
    rintro _ ⟨b, hb, rfl⟩
    exact linSub.mul_mem (linSub.mul_mem hc₀L hb.2) (linSub.inv_mem hc₀L)
  have hB₁N : B₁ ≤ natNorm (g2Gam K) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (natNorm _).mul_mem ((natNorm _).mul_mem hc₀N (hBN hb.1)) ((natNorm _).inv_mem hc₀N)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  have hB₁odd : Odd (Nat.card B₁) := by
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linSub) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    rw [h3]
    exact Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left)
  set Um := (U0 K).map (g2Mat (K := K)) with hUm
  have hU₁' : (U0 K).map ρ = Um.map matHom := by
    rw [hUm, Subgroup.map_map]
    rfl
  have hperm₁ : (B₁ : Set (MulAut (StdMod Ix3 K))) * (Um.map matHom :
      Subgroup (MulAut (StdMod Ix3 K))) =
      (Um.map matHom : Subgroup (MulAut (StdMod Ix3 K))) * B₁ := by
    rw [← hU₁', ← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  set B₂ := B₁.comap (matHom (ι := Ix3) (K := K)) with hB₂
  have hB₂map : B₂.map matHom = B₁ := Subgroup.map_comap_eq_self (fun x hx => by
    obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub (hB₁L hx)
    exact ⟨A, rfl⟩)
  have hperm₂ : (B₂ : Set (GL Ix3 K)) * (Um : Set (GL Ix3 K)) = (Um : Set (GL Ix3 K)) * B₂ := by
    have h1 := hperm₁
    rw [← hB₂map, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul] at h1
    exact Set.image_injective.mpr matHom_injective h1
  set B₃ := B₂.map (reI K) with hB₃
  have hU₃ : Um.map (reI K) = u0Six K := by
    rw [hUm, Subgroup.map_map]
    rfl
  have hB₂ab : ∀ a ∈ B₂, ∀ b ∈ B₂, a * b = b * a := fun a ha b hb => matHom_injective (by
    rw [map_mul, map_mul]
    exact hB₁ab _ ha _ hb)
  have hB₃ab : ∀ a ∈ B₃, ∀ b ∈ B₃, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hB₂ab a ha b hb]
  have hB₂card : Nat.card B₂ = Nat.card B₁ := by
    have := Subgroup.card_map_of_injective (K := B₂) (matHom_injective (ι := Ix3) (K := K))
    rw [hB₂map] at this
    exact this.symm
  have hB₃odd : Odd (Nat.card B₃) := by
    rw [hB₃, Subgroup.card_map_of_injective reI_injective, hB₂card]
    exact hB₁odd
  have hB₃U : (B₃ : Set (GL (Fin 6) K)) * (u0Six K : Set (GL (Fin 6) K)) =
      (u0Six K : Set (GL (Fin 6) K)) * B₃ := by
    rw [← hU₃, hB₃, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm₂, Set.image_mul]
  have hB₃G : ∀ b ∈ B₃, IsScalG2 b := by
    rintro _ ⟨A, hA, rfl⟩
    exact isScalG2_reI hK hn (hB₁N hA)
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    obtain ⟨A, hA, rfl⟩ : z ∈ B₂.map matHom := by rw [hB₂map]; exact hz
    have hAB : reI K A ∈ B₃ := ⟨A, hA, rfl⟩
    have h1 := pow_card_sub_one_of_g2 hK4 hB₃G hB₃ab hB₃odd hB₃U hAB
    rw [← map_pow] at h1
    have h2 : A ^ (Nat.card K - 1) = 1 := reI_injective (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (StdMod Ix3 K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (StdMod Ix3 K)) ∈ B := hYB y.2
  set σ := fieldHom hΓ (⟨y, hBN hyB⟩ : ↥(natNorm (g2Gam K))) with hσ
  set m := orderOf σ with hm
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have hmn : m ∣ n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := orderOf_pos σ
  have hym : (y : MulAut (StdMod Ix3 K)) ^ m ∈ B ⊓ linSub := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : fieldHom hΓ (⟨y, hBN hyB⟩ ^ m : ↥(natNorm (g2Gam K))) = 1 := by
      rw [map_pow, ← hσ, hm, pow_orderOf_eq_one]
    exact (fieldHom_eq_one_iff hΓ _).mp h1
  have hypow : (y : MulAut (StdMod Ix3 K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (StdMod Ix3 K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1 at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ n - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le_G2 [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (StdMod Ix3 K))} (hX1 : natImage (g2Gam K) ≤ X)
    (hX2 : X ≤ natNorm (g2Gam K)) : E3.nPrime X ≤ n := by
  have : Finite (MulAut (StdMod Ix3 K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes_G2 hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
