module

public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.Quasithin

namespace B5

namespace P5

open Matrix CFSG.Quasithin.JonesParshall

variable {K : Type} [Field K]

theorem mul_self_eq_one_of_mulVec_eq [CharP K 2] {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    {x : Fin 2 → K} (hx : x ≠ 0) (hMx : M *ᵥ x = x) : M * M = 1 := by
  have hsing : (M - 1).det = 0 := by
    have h1 : (M - 1) *ᵥ x = 0 := by rw [sub_mulVec, hMx, one_mulVec, sub_self]
    exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, h1⟩
  rw [det_fin_two] at hdet hsing
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.sub_apply, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hsing
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * (hdet - hsing) - hdet + (M 0 0 - 1) * h2
  · linear_combination M 0 1 * (hdet - hsing) + M 0 1 * h2
  · linear_combination M 1 0 * (hdet - hsing) + M 1 0 * h2
  · linear_combination M 1 1 * (hdet - hsing) - hdet + (M 1 1 - 1) * h2

@[expose] def e₁ : Fin 2 → K := ![1, 0]

theorem eq_uMat_of_smul_e₁ {g : SL2 K} (hg : g • (e₁ : Fin 2 → K) = e₁) :
    g = uMat ((g : Matrix (Fin 2) (Fin 2) K) 0 1) := by
  have hg' : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ e₁ = e₁ := hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have := congrFun hg' 0
    rw [mulVec_two_zero] at this
    simpa [e₁] using this
  have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun hg' 1
    rw [mulVec_two_one] at this
    simpa [e₁] using this
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have := g.2
    rw [det_fin_two, h00, h10] at this
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat_coe, h00, h10, h11]

theorem card_stabilizer_e₁_le [Finite K] :
    Nat.card (MulAction.stabilizer (SL2 K) (e₁ : Fin 2 → K)) ≤ Nat.card K := by
  refine Nat.card_le_card_of_injective
    (fun g => ((g : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1) fun g h hgh => ?_
  apply Subtype.ext
  rw [eq_uMat_of_smul_e₁ g.2, eq_uMat_of_smul_e₁ h.2]
  exact congrArg uMat hgh

theorem exists_smul_e₁ {v : Fin 2 → K} (hv : v ≠ 0) : ∃ c : SL2 K, c • (e₁ : Fin 2 → K) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, h1]⟩, funext fun i => ?_⟩
    fin_cases i
    · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 0 = v 0
      rw [mulVec_two_zero]
      simp [e₁, h0]
    · change (!![0, -(v 1)⁻¹; v 1, 0] *ᵥ e₁) 1 = v 1
      rw [mulVec_two_one]
      simp [e₁]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, h0]⟩, funext fun i => ?_⟩
    fin_cases i
    · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 0 = v 0
      rw [mulVec_two_zero]
      simp [e₁]
    · change (!![v 0, 0; v 1, (v 0)⁻¹] *ᵥ e₁) 1 = v 1
      rw [mulVec_two_one]
      simp [e₁]

theorem card_stabilizer_le [Finite K] {v : Fin 2 → K} (hv : v ≠ 0) :
    Nat.card (MulAction.stabilizer (SL2 K) v) ≤ Nat.card K := by
  obtain ⟨c, rfl⟩ := exists_smul_e₁ hv
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]
  exact card_stabilizer_e₁_le

theorem orbit_eq {v : Fin 2 → K} (hv : v ≠ 0) :
    MulAction.orbit (SL2 K) v = {w | w ≠ 0} := by
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩ h0
    have : v = g⁻¹ • (g • v) := (inv_smul_smul g v).symm
    rw [h0, smul_zero] at this
    exact hv this
  · intro hw
    obtain ⟨c, hc⟩ := exists_smul_e₁ hv
    obtain ⟨d, hd⟩ := exists_smul_e₁ hw
    refine ⟨d * c⁻¹, ?_⟩
    rw [mul_smul, ← hc, inv_smul_smul, hd]

theorem odd_index_stabilizer [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) (ha : 1 ≤ a)
    {v : Fin 2 → K} (hv : v ≠ 0) : Odd (MulAction.stabilizer (SL2 K) v).index := by
  rw [MulAction.index_stabilizer, orbit_eq hv]
  have hc : ({w : Fin 2 → K | w ≠ 0} : Set (Fin 2 → K)) = {0}ᶜ := by
    ext w
    simp
  rw [hc, Set.ncard_compl, Set.ncard_singleton, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin, hK, ← pow_mul]
  obtain ⟨k, hk⟩ : ∃ k, a * 2 = k + 1 := ⟨a * 2 - 1, by omega⟩
  rw [hk, pow_succ]
  exact ⟨2 ^ k - 1, by have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega⟩

theorem card_fixed_le [Finite K] {g : SL2 K} (hg : g ≠ 1) :
    Nat.card {w : Fin 2 → K // g • w = w} ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  let W : Submodule K (Fin 2 → K) :=
    LinearMap.ker (Matrix.toLin' ((g : Matrix (Fin 2) (Fin 2) K) - 1))
  have hmem : ∀ w, w ∈ W ↔ g • w = w := fun w => by
    simp only [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, one_mulVec, sub_eq_zero]
    rfl
  have hW : W ≠ ⊤ := by
    intro htop
    apply hg
    apply Subtype.ext
    show (g : Matrix (Fin 2) (Fin 2) K) = 1
    ext i j
    have h1 : g • (Pi.single j 1 : Fin 2 → K) = Pi.single j 1 := (hmem _).1 (by rw [htop]; trivial)
    have h2 := congrFun h1 i
    change ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single j 1) i = _ at h2
    rw [mulVec_single_one] at h2
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h2
  have hrk : Module.finrank K W ≤ 1 := by
    have := Submodule.finrank_lt hW
    simp only [Module.finrank_fin_fun] at this
    omega
  calc Nat.card {w : Fin 2 → K // g • w = w} = Nat.card W :=
        Nat.card_congr (Equiv.subtypeEquivRight fun w => (hmem w).symm)
    _ = Nat.card K ^ Module.finrank K W := Module.natCard_eq_pow_finrank
    _ ≤ Nat.card K ^ 1 := Nat.pow_le_pow_right Nat.card_pos hrk
    _ = Nat.card K := pow_one _

theorem exists_fixed_ne_zero [Finite K] {a : ℕ} (hK : Nat.card K = 2 ^ a) {P : Subgroup (SL2 K)}
    (hP : IsPGroup 2 P) : ∃ e : Fin 2 → K, e ≠ 0 ∧ ∀ g ∈ P, g • e = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, this] at h1
    simp at h1
  have hdvd : 2 ∣ Nat.card (Fin 2 → K) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, hK, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  have h0 : (0 : Fin 2 → K) ∈ MulAction.fixedPoints P (Fin 2 → K) := fun g => smul_zero _
  obtain ⟨e, he, hne⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → K) hdvd h0
  exact ⟨e, Ne.symm hne, fun g hg => he ⟨g, hg⟩⟩

end P5

end B5

end CFSG.Quasithin
