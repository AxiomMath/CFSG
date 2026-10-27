module

public import CFSG.LieType.BorelTits.Flag

public section

namespace CFSG.Quasithin.H13.Ch9.Sp4B

open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] noncomputable def slRep : SL(2, K) →* Module.End K (Fin 2 → K) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) K)
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, mulVecLin_one]
    rfl
  map_mul' g h := by
    rw [Matrix.SpecialLinearGroup.coe_mul, mulVecLin_mul]
    rfl

theorem slRep_apply (g : SL(2, K)) (v : Fin 2 → K) :
    slRep g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v :=
  rfl

theorem exists_sl2_mulVec_single {v : Fin 2 → K} (hv : v ≠ 0) :
    ∃ m : SL(2, K), (m : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two_of, h1]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two_of, h0]⟩, ?_⟩
    ext i
    fin_cases i <;> simp

theorem exists_sl2_mulVec_eq {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ m : SL(2, K), (m : Matrix (Fin 2) (Fin 2) K) *ᵥ u = v := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_single hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_single hv
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hb]

theorem exists_sl2_vecMul_eq {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ m : SL(2, K), u ᵥ* (m : Matrix (Fin 2) (Fin 2) K) = v := by
  obtain ⟨m, hm⟩ := exists_sl2_mulVec_eq hu hv
  refine ⟨⟨(m : Matrix (Fin 2) (Fin 2) K)ᵀ, by rw [det_transpose]; exact m.2⟩, ?_⟩
  change u ᵥ* (m : Matrix (Fin 2) (Fin 2) K)ᵀ = v
  rw [vecMul_transpose, hm]

theorem eq_bot_of_isPGroup_two [Finite K] [CharP K 2] {N : Subgroup SL(2, K)}
    (hN : IsPGroup 2 N) (hnorm : ∀ m : SL(2, K), ∀ n ∈ N, m * n * m⁻¹ ∈ N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv0, hv⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero (slRep (K := K)) 2 N hN
  have hfix : ∀ n ∈ N, ∀ u : Fin 2 → K, (n : Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    intro n hn u
    by_cases hu : u = 0
    · rw [hu, mulVec_zero]
    obtain ⟨m, hm⟩ := exists_sl2_mulVec_eq hv0 hu
    have h1 : slRep (m⁻¹ * n * m) v = v := hv _ (by simpa using hnorm m⁻¹ n hn)
    rw [slRep_apply] at h1
    calc (n : Matrix (Fin 2) (Fin 2) K) *ᵥ u
        = (n : Matrix (Fin 2) (Fin 2) K) *ᵥ ((m : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by rw [hm]
      _ = ((m * (m⁻¹ * n * m) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
          rw [show m * (m⁻¹ * n * m) = n * m by group, Matrix.SpecialLinearGroup.coe_mul,
            mulVec_mulVec]
      _ = (m : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (((m⁻¹ * n * m : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
          rw [Matrix.SpecialLinearGroup.coe_mul (A := m), mulVec_mulVec]
      _ = u := by rw [h1, hm]
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  ext i j
  have h := congrFun (hfix n hn (Pi.single j 1)) i
  simpa [mulVec_single, one_apply, Pi.single_apply] using h

theorem card_sl2_of_card_four [Fintype K] (hK : Fintype.card K = 4) :
    Nat.card SL(2, K) = 60 := by
  rw [Matrix.card_SL_field, hK]
  norm_num [Fin.prod_univ_two]

theorem charP_two_of_card_four [Fintype K] (hK : Fintype.card K = 4) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [hK]; norm_num)

theorem exists_ne_zero_ne_one_of_card_four [Fintype K] (hK : Fintype.card K = 4) :
    ∃ μ : K, μ ≠ 0 ∧ μ ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, hK] at h1
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem commutator_eq_top_of_perfect {G : Type*} [Group G] {L : Subgroup G}
    (hL : ⁅L, L⁆ = L) : commutator ↥L = ⊤ := by
  apply Subgroup.map_injective L.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    hL]

theorem eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] {L : Subgroup G}
    (hL : ⁅L, L⁆ = L) (f : ↥L →* A) (l : ↥L) : f l = 1 := by
  have h := Abelianization.commutator_subset_ker f
  rw [commutator_eq_top_of_perfect hL] at h
  exact h (Subgroup.mem_top l)

theorem surjective_of_isPGroup_ker {G H : Type*} [Group G] [Group H] [Finite H] {L : Subgroup G}
    {c : ℕ} (hL : ∀ N : Subgroup G, N ≤ L → L ≤ Subgroup.normalizer (N : Set G) →
      IsPGroup 2 N → c ≤ N.relIndex L)
    (f : ↥L →* H) (hker : IsPGroup 2 f.ker) (hH : Nat.card H ≤ c) : Function.Surjective f := by
  set N := f.ker.map L.subtype with hN
  have hNL : N ≤ L := by
    rw [hN]
    exact Subgroup.map_subtype_le _
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    have h := Subgroup.le_normalizer_map (H := f.ker) L.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hidx := hL N hNL hLN (hker.map L.subtype)
  have hrel : N.relIndex L = f.ker.index := by
    rw [Subgroup.relIndex, hN, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  rw [hrel, Subgroup.index_ker] at hidx
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  exact le_antisymm (Subgroup.card_le_card_group _) (hH.trans hidx)

end CFSG.Quasithin.H13.Ch9.Sp4B
