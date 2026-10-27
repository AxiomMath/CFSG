module

public import CFSG.Quasithin.Background.G2A5
public import CFSG.Quasithin.Background.G2SL2

public section

namespace CFSG.Quasithin.A5Model

open CFSG.Quasithin.SL2Model
open scoped MatrixGroups LinearAlgebra.Projectivization

theorem sl2_faithful_proj (K : Type) [Field K] [CharP K 2] (g : SL(2, K))
    (h : ∀ x : ℙ K (Fin 2 → K), g • x = x) : g = 1 := by
  have h0 : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have h1 : (![0, 1] : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 1
  have h2 : (![1, 1] : Fin 2 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have e0 := h (Projectivization.mk K _ h0)
  have e1 := h (Projectivization.mk K _ h1)
  have e2 := h (Projectivization.mk K _ h2)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at e0 e1 e2
  obtain ⟨a, ha⟩ := e0
  obtain ⟨b, hb⟩ := e1
  obtain ⟨c, hc⟩ := e2
  have hg : ∀ v : Fin 2 → K, g • v = (g : Matrix (Fin 2) (Fin 2) K).mulVec v := fun v => rfl
  rw [hg] at ha hb hc
  have a00 := congrFun ha 0
  have a10 := congrFun ha 1
  have b01 := congrFun hb 0
  have b11 := congrFun hb 1
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a00 a10 b01 b11 c0 c1
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2' : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have g01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := b01.symm
  have g10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := a10.symm
  have g00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 = c := by rw [c0, g01, add_zero]
  have g11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = c := by rw [c1, g10, zero_add]
  rw [g00, g11, g01, g10] at hdet
  have hcc : (c - 1) ^ 2 = 0 := by linear_combination hdet + (1 - c) * h2'
  have hc1 : c = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hcc)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g00, g11, g01, g10, hc1]

theorem sl2_four_equiv_alt5 (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (hcard : Nat.card SL(2, K) = 60) : Nonempty (SL(2, K) ≃* alternatingGroup (Fin 5)) := by
  classical
  have hP : Nat.card (ℙ K (Fin 2 → K)) = 5 := by
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hK]
  let _ : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _
  let e : ℙ K (Fin 2 → K) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hP])
  let ψ : SL(2, K) →* Equiv.Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom SL(2, K) (ℙ K (Fin 2 → K)))
  have hinj0 : Function.Injective (MulAction.toPermHom SL(2, K) (ℙ K (Fin 2 → K))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply sl2_faithful_proj
    intro x
    have := DFunLike.congr_fun hg x
    simpa using this
  have hψ : Function.Injective ψ := e.permCongrHom.injective.comp hinj0
  have hrange_card : Nat.card ψ.range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hcard]
  have hindex : ψ.range.index = 2 := by
    have h := ψ.range.card_mul_index
    rw [hrange_card, Nat.card_perm, Nat.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have hrange : ψ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem exists_conj_eq_of_isPGroup_of_odd_index {G : Type*} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let SP : Sylow 2 G := hP.toSylow hPi
  let SQ : Sylow 2 G := hQ.toSylow hQi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SP SQ
  refine ⟨g, ?_⟩
  have h1 := congrArg (fun X : Sylow 2 G => (X : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul] at h1
  exact h1

theorem odd_index_of_card_four {X : Type*} [Group X] (H : Subgroup X) (hX : Nat.card X = 60)
    (hH : Nat.card ↥H = 4) : ¬ 2 ∣ H.index := by
  have h := H.card_mul_index
  rw [hH, hX] at h
  omega

theorem card_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem card_sl2_gf4 : Nat.card SL(2, GaloisField 2 2) = 60 := by
  rw [card_SL2, card_gf4]
  norm_num

theorem exists_mulEquiv_A5_SL2_four :
    ∃ e : A5 ≃* SL(2, GaloisField 2 2), K4.map e.toMonoidHom = Rg (GaloisField 2 2) := by
  obtain ⟨e₀⟩ := sl2_four_equiv_alt5 (GaloisField 2 2) card_gf4 card_sl2_gf4
  have hcardP : Nat.card ↥(K4.map e₀.symm.toMonoidHom) = 4 := by
    rw [Nat.card_congr (K4.equivMapOfInjective e₀.symm.toMonoidHom e₀.symm.injective).toEquiv.symm]
    exact card_K4
  have hP2 : IsPGroup 2 ↥(K4.map e₀.symm.toMonoidHom) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hcardP]
    norm_num
  have hRcard : Nat.card ↥(Rg (GaloisField 2 2)) = 4 := by
    rw [Rg_card, card_gf4]
  have hR2 : IsPGroup 2 ↥(Rg (GaloisField 2 2)) := Rg_isPGroup
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isPGroup_of_odd_index hP2
    (odd_index_of_card_four _ card_sl2_gf4 hcardP) hR2 Rg_index_odd
  refine ⟨e₀.symm.trans (MulAut.conj g), ?_⟩
  rw [Subgroup.map_map] at hg
  exact hg

theorem mem_A4s_of_normalizes_K4 :
    ∀ σ : A5, (∀ k ∈ K4, σ * k * σ⁻¹ ∈ K4) → σ ∈ A4s := by
  set_option maxRecDepth 100000 in decide

theorem mul_e12_mul_inv_of_lower_left_zero {F : Type*} [Field F] (k : SL(2, F))
    (hk : k.1 1 0 = 0) (b : F) : k * e12 b * k⁻¹ = e12 (k.1 0 0 ^ 2 * b) := by
  have hdet := k.2
  rw [Matrix.det_fin_two, hk, mul_zero, sub_zero] at hdet
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hk]
  linear_combination (-(k.1 0 0 * b)) * hdet

theorem mem_A4s_of_stab {e : A5 ≃* SL(2, GaloisField 2 2)}
    (he : K4.map e.toMonoidHom = Rg (GaloisField 2 2)) {σ : A5} (hσ : (e σ).1 1 0 = 0) :
    σ ∈ A4s := by
  apply mem_A4s_of_normalizes_K4
  intro k hk
  have hkR : e k ∈ Rg (GaloisField 2 2) := by
    rw [← he]
    exact ⟨k, hk, rfl⟩
  obtain ⟨b, hb⟩ := mem_Rg.1 hkR
  have h1 : e (σ * k * σ⁻¹) = e12 ((e σ).1 0 0 ^ 2 * b) := by
    rw [map_mul, map_mul, map_inv, ← hb]
    exact mul_e12_mul_inv_of_lower_left_zero _ hσ b
  have h2 : e (σ * k * σ⁻¹) ∈ Rg (GaloisField 2 2) := by
    rw [h1]
    exact e12_mem_Rg _
  rw [← he] at h2
  obtain ⟨y, hy, hyx⟩ := h2
  have : y = σ * k * σ⁻¹ := e.injective hyx
  rw [← this]
  exact hy

end CFSG.Quasithin.A5Model
