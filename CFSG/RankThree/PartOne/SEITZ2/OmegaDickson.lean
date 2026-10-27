module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaPlane
public import CFSG.RankThree.PartOne.SEITZ2.SL2Line

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix
open CFSG.RankThree.PartOne.CTP (u2 l2)

section Line

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_ts_apply {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (x : V) :
    eichler Q u w x = x + polar Q x u • w + polar Q x w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

omit [CharP K 2] in
theorem map_comb_eq_zero {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (p q : K) : Q (p • u + q • w) = 0 := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hu, hw, polar_smul_left_eq,
    polar_smul_right_eq, huw]
  ring

omit [CharP K 2] in
theorem polar_comb_eq_zero {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (p q r s : K) : polar Q (p • u + q • w) (r • u + s • w) = 0 := by
  have huu : polar Q u u = 0 := polar_self_eq_zero hu
  have hww : polar Q w w = 0 := polar_self_eq_zero hw
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, huu, hww,
    huw, hwu]
  ring

theorem eichler_change_basis {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (p q r s : K) :
    eichler Q (p • u + q • w) (r • u + s • w) = eichler Q u ((p * s + q * r) • w) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu' := map_comb_eq_zero hu hw huw p q
  have hw' := map_comb_eq_zero hu hw huw r s
  have huw' := polar_comb_eq_zero hu hw huw p q r s
  have hsw : Q ((p * s + q * r) • w) = 0 := by rw [map_smul_eq_sq, hw, mul_zero]
  have hsuw : polar Q u ((p * s + q * r) • w) = 0 := by
    rw [polar_smul_right_eq, huw, mul_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_ts_apply hu' hw' huw', eichler_ts_apply hu hsw hsuw]
  simp only [polar_add_right, polar_smul_right_eq]
  match_scalars
  · rfl
  · linear_combination (p * r * polar Q x u) * h2
  · linear_combination (q * s * polar Q x w) * h2

section Dual

variable {e₁ e₂ u w : V}

theorem exists_dual_pairs (he₁ : Q e₁ = 0) (he₂ : Q e₂ = 0) (he₁₂ : polar Q e₁ e₂ = 0)
    (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (hδ : polar Q e₁ u * polar Q e₂ w + polar Q e₁ w * polar Q e₂ u ≠ 0) :
    ∃ (P P' : HypPair Q) (_ : P.Orth P'), P.e = e₁ ∧ P'.e = e₂ ∧ ∀ t : K,
      eichler Q u (t • w) = eichler Q P.f
        ((t * (polar Q e₁ u * polar Q e₂ w + polar Q e₁ w * polar Q e₂ u)) • P'.f) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha⟩ : ∃ a, polar Q e₁ u = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, polar Q e₁ w = b := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, polar Q e₂ u = m := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, polar Q e₂ w = n := ⟨_, rfl⟩
  rw [ha, hb, hm, hn] at hδ ⊢
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = a * n + b * m := ⟨_, rfl⟩
  rw [← hδdef] at hδ ⊢
  have hδ' : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : V, c₁ = (δ⁻¹ * n) • u + (δ⁻¹ * m) • w := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : V, c₂ = (δ⁻¹ * b) • u + (δ⁻¹ * a) • w := ⟨_, rfl⟩
  have hQ₁ : Q c₁ = 0 := by rw [hc₁]; exact map_comb_eq_zero hu hw huw _ _
  have hQ₂ : Q c₂ = 0 := by rw [hc₂]; exact map_comb_eq_zero hu hw huw _ _
  have hc₁c₂ : polar Q c₁ c₂ = 0 := by
    rw [hc₁, hc₂]; exact polar_comb_eq_zero hu hw huw _ _ _ _
  have e₁c₁ : polar Q e₁ c₁ = 1 := by
    rw [hc₁, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb]
    linear_combination hδ' + (0 : K) * h2 - (δ⁻¹) * hδdef
  have e₂c₁ : polar Q e₂ c₁ = 0 := by
    rw [hc₁, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hm, hn]
    linear_combination (δ⁻¹ * m * n) * h2
  have e₁c₂ : polar Q e₁ c₂ = 0 := by
    rw [hc₂, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, ha, hb]
    linear_combination (δ⁻¹ * a * b) * h2
  have e₂c₂ : polar Q e₂ c₂ = 1 := by
    rw [hc₂, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hm, hn]
    linear_combination hδ' - (δ⁻¹) * hδdef
  have hu_eq : u = a • c₁ + m • c₂ := by
    rw [hc₁, hc₂]
    match_scalars
    · linear_combination (-1 : K) * hδ' + δ⁻¹ * hδdef
    · linear_combination (-(δ⁻¹ * a * m)) * h2
  have hw_eq : w = b • c₁ + n • c₂ := by
    rw [hc₁, hc₂]
    match_scalars
    · linear_combination (-1 : K) * hδ' + δ⁻¹ * hδdef
    · linear_combination (-(δ⁻¹ * b * n)) * h2
  have hOrth : (⟨e₁, c₁, he₁, hQ₁, e₁c₁⟩ : HypPair Q).Orth ⟨e₂, c₂, he₂, hQ₂, e₂c₂⟩ :=
    ⟨he₁₂, e₁c₂, by rw [polar_comm]; exact e₂c₁, hc₁c₂⟩
  refine ⟨_, _, hOrth, rfl, rfl, fun t => ?_⟩
  have hch := eichler_change_basis hQ₁ hQ₂ hc₁c₂ a m (t * b) (t * n)
  have h1 : t • w = (t * b) • c₁ + (t * n) • c₂ := by
    conv_lhs => rw [hw_eq]
    module
  have hu1 : eichler Q u (t • w) =
      eichler Q (a • c₁ + m • c₂) ((t * b) • c₁ + (t * n) • c₂) := by
    rw [← h1, ← hu_eq]
  rw [hu1, hch]
  have : a * (t * n) + m * (t * b) = t * δ := by rw [hδdef]; ring
  rw [this]

end Dual

section Dickson

variable [Finite K]

theorem fullRoot_of_pairing {k : Subfield K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = Nat.card k ^ p) (hk4 : 4 ∣ Nat.card k) {e₁ e₂ u w : V}
    (he₁ : Q e₁ = 0) (he₂ : Q e₂ = 0) (he₁₂ : polar Q e₁ e₂ = 0) (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0)
    (hδ : polar Q e₁ u * polar Q e₂ w + polar Q e₁ w * polar Q e₂ u ∉ k)
    {M : Subgroup (V ≃ₗ[K] V)} (hM₁ : ∀ c ∈ k, eichler Q e₁ (c • e₂) ∈ M)
    (hM₂ : ∀ c ∈ k, eichler Q u (c • w) ∈ M) : ∀ c : K, eichler Q e₁ (c • e₂) ∈ M := by
  have hδ0 : polar Q e₁ u * polar Q e₂ w + polar Q e₁ w * polar Q e₂ u ≠ 0 :=
    fun h0 => hδ (h0 ▸ k.zero_mem)
  obtain ⟨P, P', hOrth, hPe, hPe', hE⟩ := exists_dual_pairs he₁ he₂ he₁₂ hu hw huw hδ0
  have hM : M.comap (planeHom hOrth) = ⊤ :=
    sl2_eq_top_of_root_lines hp hp2 hK hk4 hδ
      (fun c hc => by
        rw [Subgroup.mem_comap, planeHom_u2, hPe, hPe']
        exact hM₁ c hc)
      (fun c hc => by
        rw [Subgroup.mem_comap, planeHom_l2, ← hE]
        exact hM₂ c hc)
  intro c
  have : u2 c ∈ M.comap (planeHom hOrth) := by rw [hM]; trivial
  rwa [Subgroup.mem_comap, planeHom_u2, hPe, hPe'] at this

end Dickson

end Line

end CFSG.RankThree.PartOne.SEITZ2
