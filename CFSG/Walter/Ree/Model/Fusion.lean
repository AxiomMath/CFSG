module

public import CFSG.Walter.Ree.Model.JTHyp
public import CFSG.Walter.Ree.Model.FusionCheck

public noncomputable section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open scoped Pointwise

theorem pow_mul_pow_self_of_mul_self {G : Type*} [Group G] {x : G} (hx : x * x = 1) (i : ℕ) :
    x ^ i * x ^ i = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sq, hx, one_pow]

theorem mem_closure_three {G : Type*} [Group G] {x y z : G} (hxy : Commute x y)
    (hxz : Commute x z) (hyz : Commute y z) (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    {g : G} (hg : g ∈ Subgroup.closure ({x, y, z} : Set G)) :
    g = 1 ∨ g = x ∨ g = y ∨ g = z ∨ g = x * y ∨ g = x * z ∨ g = y * z ∨ g = x * y * z := by
  have key : ∃ i j k : ℕ, g = x ^ i * y ^ j * z ^ k := by
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, k, rfl⟩ := hu
      obtain ⟨i', j', k', rfl⟩ := hv
      refine ⟨i + i', j + j', k + k', ?_⟩
      have h1 : Commute (y ^ j * z ^ k) (x ^ i') :=
        ((hxy.pow_pow i' j).symm).mul_left ((hxz.pow_pow i' k).symm)
      have h2 : Commute (z ^ k) (y ^ j') := (hyz.pow_pow j' k).symm
      calc x ^ i * y ^ j * z ^ k * (x ^ i' * y ^ j' * z ^ k') =
            x ^ i * ((y ^ j * z ^ k) * x ^ i') * y ^ j' * z ^ k' := by simp only [mul_assoc]
        _ = x ^ i * (x ^ i' * (y ^ j * z ^ k)) * y ^ j' * z ^ k' := by rw [h1.eq]
        _ = x ^ i * x ^ i' * y ^ j * (z ^ k * y ^ j') * z ^ k' := by simp only [mul_assoc]
        _ = x ^ i * x ^ i' * y ^ j * (y ^ j' * z ^ k) * z ^ k' := by rw [h2.eq]
        _ = x ^ (i + i') * y ^ (j + j') * z ^ (k + k') := by
          simp only [pow_add, mul_assoc]
    | inv u _ hu =>
      obtain ⟨i, j, k, rfl⟩ := hu
      refine ⟨i, j, k, ?_⟩
      have ex := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hx i)
      have ey := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hy j)
      have ez := inv_eq_of_mul_eq_one_right (pow_mul_pow_self_of_mul_self hz k)
      rw [mul_inv_rev, mul_inv_rev, ex, ey, ez]
      calc z ^ k * (y ^ j * x ^ i) = z ^ k * (x ^ i * y ^ j) := by
            rw [(hxy.pow_pow i j).eq]
        _ = (z ^ k * x ^ i) * y ^ j := by rw [mul_assoc]
        _ = (x ^ i * z ^ k) * y ^ j := by rw [(hxz.pow_pow i k).eq]
        _ = x ^ i * (z ^ k * y ^ j) := by rw [mul_assoc]
        _ = x ^ i * y ^ j * z ^ k := by rw [← (hyz.pow_pow j k).eq, mul_assoc]
  obtain ⟨i, j, k, rfl⟩ := key
  have hpow : ∀ {w : G}, w * w = 1 → ∀ n : ℕ, w ^ n = 1 ∨ w ^ n = w := fun {w} hw n => by
    rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · left
      rw [← two_mul, pow_mul, sq, hw, one_pow]
    · right
      rw [pow_succ, pow_mul, sq, hw, one_pow, one_mul]
  rcases hpow hx i with hi | hi <;> rcases hpow hy j with hj | hj <;>
    rcases hpow hz k with hk | hk <;> rw [hi, hj, hk] <;> simp

theorem exists_conj_of_relations {G : Type*} [Group G] {Γ : Subgroup G} {t n m u c₁ c₂ : G}
    (htn : Commute t n) (htm : Commute t m) (hnm : Commute n m) (htt : t * t = 1)
    (hnn : n * n = 1) (hmm : m * m = 1) (hut : u * t * u⁻¹ = t) (hum : u * m * u⁻¹ = n)
    (hun : u⁻¹ * (n * m) * u = n) (hc₁ : c₁ * t = n * c₁) (hc₂ : c₂ * t = t * n * c₂)
    (hu : u ∈ Γ) (h₁ : c₁ ∈ Γ) (h₂ : c₂ ∈ Γ) {x : G}
    (hx : x ∈ Subgroup.closure ({t, n, m} : Set G)) (hx1 : x ≠ 1) :
    ∃ g ∈ Γ, g * x * g⁻¹ = t := by
  have hut' : u⁻¹ * t * u = t := by
    calc u⁻¹ * t * u = u⁻¹ * (u * t * u⁻¹) * u := by rw [hut]
      _ = t := by group
  have e₁ : c₁⁻¹ * n * c₁ = t := by
    calc c₁⁻¹ * n * c₁ = c₁⁻¹ * (n * c₁) := by group
      _ = t := by rw [← hc₁]; group
  have e₂ : c₂⁻¹ * (t * n) * c₂ = t := by
    calc c₂⁻¹ * (t * n) * c₂ = c₂⁻¹ * (t * n * c₂) := by group
      _ = t := by rw [← hc₂]; group
  rcases mem_closure_three htn htm hnm htt hnn hmm hx with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hx1
  · exact ⟨1, one_mem _, by group⟩
  · exact ⟨c₁⁻¹, inv_mem h₁, by rw [inv_inv]; exact e₁⟩
  · refine ⟨c₁⁻¹ * u, mul_mem (inv_mem h₁) hu, ?_⟩
    calc c₁⁻¹ * u * x * (c₁⁻¹ * u)⁻¹ = c₁⁻¹ * (u * x * u⁻¹) * c₁ := by group
      _ = t := by rw [hum, e₁]
  · exact ⟨c₂⁻¹, inv_mem h₂, by rw [inv_inv]; exact e₂⟩
  · refine ⟨c₂⁻¹ * u, mul_mem (inv_mem h₂) hu, ?_⟩
    calc c₂⁻¹ * u * (t * m) * (c₂⁻¹ * u)⁻¹ =
          c₂⁻¹ * ((u * t * u⁻¹) * (u * m * u⁻¹)) * c₂ := by group
      _ = t := by rw [hut, hum, e₂]
  · refine ⟨c₁⁻¹ * u⁻¹, mul_mem (inv_mem h₁) (inv_mem hu), ?_⟩
    calc c₁⁻¹ * u⁻¹ * (n * m) * (c₁⁻¹ * u⁻¹)⁻¹ = c₁⁻¹ * (u⁻¹ * (n * m) * u) * c₁ := by group
      _ = t := by rw [hun, e₁]
  · refine ⟨c₂⁻¹ * u⁻¹, mul_mem (inv_mem h₂) (inv_mem hu), ?_⟩
    calc c₂⁻¹ * u⁻¹ * (t * n * m) * (c₂⁻¹ * u⁻¹)⁻¹ =
          c₂⁻¹ * ((u⁻¹ * t * u) * (u⁻¹ * (n * m) * u)) * c₂ := by group
      _ = t := by rw [hut', hun, e₂]

section Identities

variable {K : Type} [Field K] [CharP K G2.prime] {a : ℕ}

omit [CharP K G2.prime] in
theorem smallReeH_neg_one_eq_constPinned :
    smallReeH a K (-1) = constPinned G2.tag K g2TWord := by
  have h : ((-1 : Kˣ) ^ 3 ^ a : Kˣ) = -1 := (three_pow_odd a).neg_one_pow
  have hd : ∀ i : Fin G2.tag.rank, torusElt G2.tag K i (-1) =
      constPinned G2.tag K (g2WeylWordInv i ++ g2WeylWordInv i) := fun i => by
    rw [constPinned_append, ← weylElt_neg_one_eq_constPinned]
    rfl
  show torusElt G2.tag K g2I0 (-1) * torusElt G2.tag K g2I1 ((-1) ^ 3 ^ a) = _
  rw [h, hd, hd, ← constPinned_append, g2TWord]
  simp only [List.append_assoc]

omit [CharP K G2.prime] in
theorem g2U₁_eq_smallReeU :
    g2U₁ K = smallReeU a K 0 1 0 := by
  have h2 : smallReeRoot 2 = g2Root11 := rfl
  have h4 : smallReeRoot 4 = g2Root13 := rfl
  have hσ0 : smallReeSigma a (0 : K) = 0 := smallReeSigma_zero
  have hσ1 : smallReeSigma a (1 : K) = 1 := one_pow _
  show _ = smallReeCoord a K 0 1 0
  rw [smallReeCoord, hσ0, hσ1]
  simp only [zero_pow (by norm_num : 3 ≠ 0), zero_mul, mul_zero, sub_zero, smallReeX_zero,
    one_mul, mul_one]
  rw [smallReeX, smallReeX, h2, h4]
  rfl

omit [CharP K G2.prime] in
theorem uSL_one_mul_WSL (h3 : (3 : K) = 0) :
    uSL (1 : K) * WSL = WSL * smallReeMSL K * uSL 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_smallReeMSL, coe_WSL, coe_uSL,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp <;> first | linear_combination | linear_combination h3 | linear_combination -h3

omit [CharP K G2.prime] in
theorem uSL_one_mul_smallReeMSL (h3 : (3 : K) = 0) :
    uSL (1 : K) * smallReeMSL K = WSL * uSL 1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_smallReeMSL, coe_WSL, coe_uSL,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp <;> first | linear_combination | linear_combination h3 | linear_combination -h3

end Identities

section Fusion

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
  (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
include hK hw₀

omit [Finite K] hK in
theorem smallReePsi_MSL :
    smallReePsi K a (smallReeMSL K) = g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ *
      g2U₁ K := by
  rw [smallReeMSL, map_mul, map_mul, map_mul, smallReePsi_uSL, smallReePsi_WSL hw₀,
    ← g2U₁_eq_smallReeU]

omit [Finite K] hK in
theorem fusion_conj_n :
    (g2U₀ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K * g2U₂ K) *
        smallReeH a K (-1) =
      canonicalRep (coxeterSystem G2.tag) K w₀ *
        (g2U₀ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K * g2U₂ K) := by
  obtain ⟨hu0, hu1, hu2⟩ := g2U_eq_constPinned K
  have h := constPinned_eq_of_constCheck g2Check_fusion_n K (g2_three_eq_zero K)
  simp only [constPinned_append] at h
  rw [smallReeH_neg_one_eq_constPinned, canonicalRep_longest hw₀, hu0, hu1, hu2]
  exact h

omit [Finite K] hK in
theorem fusion_conj_tn :
    (g2U₂ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K) * smallReeH a K (-1) =
      smallReeH a K (-1) * canonicalRep (coxeterSystem G2.tag) K w₀ *
        (g2U₂ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₀ K) := by
  obtain ⟨hu0, hu1, hu2⟩ := g2U_eq_constPinned K
  have h := constPinned_eq_of_constCheck g2Check_fusion_tn K (g2_three_eq_zero K)
  simp only [constPinned_append] at h
  rw [smallReeH_neg_one_eq_constPinned, canonicalRep_longest hw₀, hu0, hu1, hu2]
  exact h

end Fusion

@[expose] def smallReeE8
    (a : ℕ) (K : Type) [Field K] (w₀ : WeylGroup ReeTag.G2.tag) :
    Subgroup (ModGL ReeTag.G2.tag K) :=
  Subgroup.closure {smallReeH a K (-1), canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀,
    g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * g2U₁ K}

section Main

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
  (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup G2.tag}
  (hw₀ : ∀ w, (coxeterSystem G2.tag).length w ≤ (coxeterSystem G2.tag).length w₀)
include hK hw₀

theorem smallReeE8_eq_map :
    smallReeE8 a K w₀ = (Subgroup.closure ({⟨_, smallReeH_neg_one_mem_reeGamma hK⟩,
      ⟨_, smallReePsi_mem_reeGamma hK hw₀ WSL⟩,
        ⟨_, smallReePsi_mem_reeGamma hK hw₀ (smallReeMSL K)⟩} :
          Set (G2.reeGamma K a))).map (G2.reeGamma K a).subtype := by
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
  change _ = Subgroup.closure {smallReeH a K (-1), smallReePsi K a WSL,
    smallReePsi K a (smallReeMSL K)}
  rw [smallReePsi_WSL hw₀, smallReePsi_MSL hw₀]
  rfl

theorem smallReeE8_relations :
    Commute (smallReeH a K (-1)) (canonicalRep (coxeterSystem G2.tag) K w₀) ∧
    Commute (smallReeH a K (-1))
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) ∧
    Commute (canonicalRep (coxeterSystem G2.tag) K w₀)
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) ∧
    smallReeH a K (-1) * smallReeH a K (-1) = 1 ∧
    canonicalRep (coxeterSystem G2.tag) K w₀ * canonicalRep (coxeterSystem G2.tag) K w₀ = 1 ∧
    (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) *
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) = 1 := by
  have hψW : smallReePsi K a WSL = canonicalRep (coxeterSystem G2.tag) K w₀ :=
    smallReePsi_WSL hw₀
  have hψM := smallReePsi_MSL (K := K) (a := a) hw₀
  have hcent : ∀ g, smallReePsi K a g * smallReeH a K (-1) =
      smallReeH a K (-1) * smallReePsi K a g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ g)).2
  refine ⟨?_, ?_, ?_, smallReeH_neg_one_mul_self, ?_, ?_⟩
  · rw [← hψW]
    exact (hcent WSL).symm
  · rw [← hψM]
    exact (hcent _).symm
  · rw [← hψM, ← hψW]
    exact smallReePsi_WSL_commute hK hw₀
  · rw [← hψW]
    exact smallReePsi_WSL_mul_self hK hw₀
  · rw [← hψM]
    exact smallReePsi_MSL_mul_self hK hw₀

theorem exists_conj_eq_smallReeH
    {x : ModGL G2.tag K} (hx : x ∈ smallReeE8 a K w₀) (hx1 : x ≠ 1) :
    ∃ g ∈ G2.reeGamma K a, g * x * g⁻¹ = smallReeH a K (-1) := by
  have h3 := smallRee_three_eq_zero (K := K)
  have hψu : smallReePsi K a (uSL 1) = g2U₁ K := by rw [smallReePsi_uSL, g2U₁_eq_smallReeU]
  have hψW : smallReePsi K a WSL = canonicalRep (coxeterSystem G2.tag) K w₀ :=
    smallReePsi_WSL hw₀
  have hψM := smallReePsi_MSL (K := K) (a := a) hw₀
  obtain ⟨htn, htm, hnm, htt, hnn, hmm⟩ := smallReeE8_relations (a := a) hK hw₀
  have hut : g2U₁ K * smallReeH a K (-1) * (g2U₁ K)⁻¹ = smallReeH a K (-1) := by
    rw [← hψu, Subgroup.mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (smallReePsi_mem hK hw₀ (uSL 1))).2, mul_inv_cancel_right]
  have hum : g2U₁ K * (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K) *
      (g2U₁ K)⁻¹ = canonicalRep (coxeterSystem G2.tag) K w₀ := by
    have h := congrArg (smallReePsi K a) (uSL_one_mul_smallReeMSL h3)
    rw [map_mul, map_mul, hψu, hψM, hψW] at h
    rw [h, mul_inv_cancel_right]
  have hun : (g2U₁ K)⁻¹ * (canonicalRep (coxeterSystem G2.tag) K w₀ *
      (g2U₁ K * g2U₁ K * canonicalRep (coxeterSystem G2.tag) K w₀ * g2U₁ K)) * g2U₁ K =
        canonicalRep (coxeterSystem G2.tag) K w₀ := by
    have h := congrArg (smallReePsi K a) (uSL_one_mul_WSL h3)
    rw [map_mul, map_mul, map_mul, hψu, hψM, hψW] at h
    rw [mul_assoc _ _ (g2U₁ K), ← h]
    group
  have hΓu : g2U₁ K ∈ G2.reeGamma K a := g2U₁_mem_reeGamma K a
  have hΓn : canonicalRep (coxeterSystem G2.tag) K w₀ ∈ G2.reeGamma K a :=
    canonicalRep_longest_mem_reeGamma hw₀
  exact exists_conj_of_relations htn htm hnm htt hnn hmm hut hum hun
    (fusion_conj_n (K := K) (a := a) hw₀) (fusion_conj_tn (K := K) (a := a) hw₀) hΓu
    (mul_mem (mul_mem (mul_mem (mul_mem (g2U₀_mem_reeGamma K a) hΓu) hΓn) hΓu)
      (g2U₂_mem_reeGamma K a))
    (mul_mem (mul_mem (mul_mem (g2U₂_mem_reeGamma K a) hΓu) hΓn) (g2U₀_mem_reeGamma K a)) hx hx1

theorem exists_conj_eq_smallReeH_of_orderOf
    {x : ModGL G2.tag K} (hxΓ : x ∈ G2.reeGamma K a)
    (hx : orderOf x = 2) : ∃ g ∈ G2.reeGamma K a, g * x * g⁻¹ = smallReeH a K (-1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, P, hP⟩ := smallRee_E8_sylow hK hw₀
  set y : G2.reeGamma K a := ⟨x, hxΓ⟩
  have hy : orderOf y = 2 := by rw [← hx]; exact Subgroup.orderOf_mk x hxΓ
  have hpz : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P', hP'⟩ := hpz.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G2.reeGamma K a) P P'
  have hyP : y ∈ ((g • P : Sylow 2 (G2.reeGamma K a)) : Subgroup (G2.reeGamma K a)) :=
    hP' (Subgroup.mem_zpowers y)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyP
  obtain ⟨s, hs, hsy⟩ := hyP
  have hsy' : g * s * g⁻¹ = y := hsy
  have hs1 : (s : ModGL G2.tag K) ≠ 1 := by
    intro h
    have : s = 1 := Subtype.ext h
    rw [this, mul_one, mul_inv_cancel] at hsy'
    rw [← hsy', orderOf_one] at hy
    omega
  have hsS : (s : ModGL G2.tag K) ∈ smallReeE8 a K w₀ := by
    rw [smallReeE8_eq_map hK hw₀, ← hP]
    exact ⟨s, hs, rfl⟩
  obtain ⟨h, hh, hht⟩ := exists_conj_eq_smallReeH hK hw₀ hsS hs1
  refine ⟨h * (g : ModGL G2.tag K)⁻¹, mul_mem hh (inv_mem g.2), ?_⟩
  have hx' : x = (g : ModGL G2.tag K) * s * (g : ModGL G2.tag K)⁻¹ :=
    (congrArg Subtype.val hsy').symm
  rw [hx', ← hht]
  group

end Main

theorem small_Ree_prime_field_involution_fusion
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (w₀ : WeylGroup ReeTag.G2.tag)
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    smallReeE8 a K w₀ ≤ ReeTag.G2.reeGamma K a ∧
    IsElementaryAbelian 2 (smallReeE8 a K w₀) ∧
    Nat.card (smallReeE8 a K w₀) = 8 ∧
    (∃ P : Sylow 2 (ReeTag.G2.reeGamma K a),
      (P : Subgroup (ReeTag.G2.reeGamma K a)).map (ReeTag.G2.reeGamma K a).subtype =
        smallReeE8 a K w₀) ∧
    (∀ x ∈ smallReeE8 a K w₀, x ≠ 1 →
      ∃ g ∈ ReeTag.G2.reeGamma K a, g * x * g⁻¹ = smallReeH a K (-1)) ∧
    ∀ x ∈ ReeTag.G2.reeGamma K a, orderOf x = 2 →
      ∃ g ∈ ReeTag.G2.reeGamma K a, g * x * g⁻¹ = smallReeH a K (-1) := by
  obtain ⟨-, hcard, P, hP⟩ := smallRee_E8_sylow hK hw₀
  have hmap := smallReeE8_eq_map hK hw₀
  refine ⟨?_, ?_, ?_, ⟨P, by rw [hP, hmap]⟩, fun x hx hx1 => exists_conj_eq_smallReeH hK hw₀ hx hx1,
    fun x hxΓ hx => exists_conj_eq_smallReeH_of_orderOf hK hw₀ hxΓ hx⟩
  · rw [hmap]
    exact Subgroup.map_subtype_le _
  · obtain ⟨htn, htm, hnm, htt, hnn, hmm⟩ := smallReeE8_relations (a := a) hK hw₀
    exact isElementaryAbelian_closure_three htn htm hnm htt hnn hmm
  · rw [hmap, Subgroup.card_map_of_injective (ReeTag.G2.reeGamma K a).subtype_injective, hcard]

end CFSG.Walter.Ree.Model
