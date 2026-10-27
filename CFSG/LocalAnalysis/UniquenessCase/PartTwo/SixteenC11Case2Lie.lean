module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Card
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2LieA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2LieB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

theorem s16c11_modelRF3_statedSL {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 2 ≤ m) : S16C11ModelRF3 (FFModel.nat (StatedSL m K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  let e := s16c11_case2lie_slEquiv m K
  let U := LinearFlag.unitriangular m K
  let V := LinearFlag.flagStabilizer m K {i : ℕ | 2 ≤ i ∧ i ≤ m - 1}
  let T : Subgroup (StatedSL m K) := U.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K)
  let X : Subgroup (StatedSL m K) := V.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K)
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_unitriangular (K := K) (p := 2) (n := m) (by omega)
  have hU : IsPGroup 2 U := by
    rw [show U = LinearFlag.unitriangular m K from rfl]
    exact hP ▸ P.isPGroup'
  have hUidx : ¬ 2 ∣ U.index := by
    change ¬ 2 ∣ (LinearFlag.unitriangular m K).index
    exact hP ▸ P.not_dvd_index
  have hUV : U ≤ V := fun g hg =>
    LinearFlag.upperTriangular_le_flagStabilizer {i : ℕ | 2 ≤ i ∧ i ≤ m - 1}
      (LinearFlag.unitriangular_le_upperTriangular m K hg)
  have h1 : T ≤ X := (Subgroup.map_le_map_iff_of_injective e.symm.injective).mpr hUV
  have h2 : IsPGroup 2 ↥T := by
    change IsPGroup 2 ↥(U.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K))
    exact IsPGroup.map hU e.symm.toMonoidHom
  have h3 : ¬ 2 ∣ T.index := by
    change ¬ 2 ∣ (U.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K)).index
    rw [Subgroup.index_map_equiv U e.symm]
    exact hUidx
  have h4 : T.relIndex X = 3 := by
    change (U.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K)).relIndex
      (V.map (e.symm : SpecialLinearGroup (Fin m) K →* StatedSL m K)) = 3
    rw [Subgroup.relIndex_map_map_of_injective U V e.symm.injective]
    exact s16c11_case2lie_unitriangular_relIndex_flagStabilizer hm hK
  let y : (FFModel.nat (StatedSL m K)).Amb :=
    Multiplicative.ofAdd (Pi.single ⟨0, by omega⟩ 1)
  have hy : y ∈ (FFModel.nat (StatedSL m K)).sec := Subgroup.mem_top y
  have h5 : ∀ t ∈ T, (FFModel.nat (StatedSL m K)).act t y * y⁻¹ ∈
      (FFModel.nat (StatedSL m K)).ker := by
    intro t ht
    rw [show (FFModel.nat (StatedSL m K)).ker = ⊥ from rfl, Subgroup.mem_bot, mul_inv_eq_one]
    obtain ⟨u, huU, rfl⟩ := Subgroup.mem_map.mp ht
    apply Multiplicative.ofAdd.injective
    change (((e.symm u : StatedSL m K) : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
      Pi.single ⟨0, by omega⟩ 1
    rw [s16c11_case2lie_coe_slEquiv_symm]
    exact s16c11_case2lie_unitriangular_mulVec_e1 hm huU
  have h6 : ∃ g ∈ X, (FFModel.nat (StatedSL m K)).act g y * y⁻¹ ∉
      (FFModel.nat (StatedSL m K)).ker := by
    refine ⟨e.symm (LinearFlag.reflection m K 1 le_rfl (by omega)), ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
      rw [LinearFlag.mem_flagStabilizer]
      intro i hi
      have hi2 : 2 ≤ i := hi.1
      have hi1 : i ≠ 1 := by omega
      exact LinearFlag.reflection_mem_stabilizer_of_ne (i := i) (j := 1) le_rfl (by omega) hi1
    · intro hmem
      rw [show (FFModel.nat (StatedSL m K)).ker = ⊥ from rfl, Subgroup.mem_bot,
        mul_inv_eq_one] at hmem
      have h := congrArg Multiplicative.toAdd hmem
      change (((e.symm (LinearFlag.reflection m K 1 le_rfl (by omega)) : StatedSL m K) :
          GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
          (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) = Pi.single ⟨0, by omega⟩ 1 at h
      rw [s16c11_case2lie_coe_slEquiv_symm] at h
      change ((LinearFlag.reflection m K 1 le_rfl (by omega) : SpecialLinearGroup (Fin m) K) :
          Matrix (Fin m) (Fin m) K) *ᵥ (Pi.single ⟨0, by omega⟩ 1 : Fin m → K) =
          Pi.single ⟨0, by omega⟩ 1 at h
      rw [s16c11_case2lie_reflection_one_mulVec hm] at h
      have := congrFun h (⟨0, by omega⟩ : Fin m)
      simp at this
  exact ⟨T, X, h1, h2, h3, h4, y, hy, h5, h6⟩

theorem s16c11_modelRF3_statedSp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {r : ℕ}
    (hr : 2 ≤ r) : S16C11ModelRF3 (FFModel.nat (StatedSp r K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  let T := SymplecticFlag.unipotent r K
  let X := SymplecticHigher.flagStabilizer r K (Set.Icc 2 r)
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) (p := 2) (r := r)
  have hT : IsPGroup 2 T := by
    change IsPGroup 2 (SymplecticFlag.unipotent r K)
    exact hP ▸ P.isPGroup'
  have hTidx : ¬ 2 ∣ T.index := by
    change ¬ 2 ∣ (SymplecticFlag.unipotent r K).index
    exact hP ▸ P.not_dvd_index
  let y : (FFModel.nat (StatedSp r K)).Amb :=
    Multiplicative.ofAdd (Pi.single (Sum.inl ⟨0, by omega⟩) 1)
  have hy : y ∈ (FFModel.nat (StatedSp r K)).sec := Subgroup.mem_top y
  have h5 : ∀ t ∈ T, (FFModel.nat (StatedSp r K)).act t y * y⁻¹ ∈
      (FFModel.nat (StatedSp r K)).ker := by
    intro t ht
    rw [show (FFModel.nat (StatedSp r K)).ker = ⊥ from rfl, Subgroup.mem_bot, mul_inv_eq_one]
    apply Multiplicative.ofAdd.injective
    change (((t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K)
    exact s16c11_case2lie_sp_unipotent_fixes hr hK ht
  have h6 : ∃ g ∈ X, (FFModel.nat (StatedSp r K)).act g y * y⁻¹ ∉
      (FFModel.nat (StatedSp r K)).ker := by
    obtain ⟨g, hgX, hgv⟩ := s16c11_case2lie_sp_exists_moves hr hK
    refine ⟨g, hgX, ?_⟩
    intro hmem
    rw [show (FFModel.nat (StatedSp r K)).ker = ⊥ from rfl, Subgroup.mem_bot,
      mul_inv_eq_one] at hmem
    refine hgv ?_
    have h := congrArg Multiplicative.toAdd hmem
    change (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) : Fin r ⊕ Fin r → K) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : K) at h
    exact h
  exact ⟨T, X, s16c11_case2lie_sp_unipotent_le_flagStabilizer, hT, hTidx,
    s16c11_case2lie_sp_unipotent_relIndex_flagStabilizer hr hK, y, hy, h5, h6⟩

theorem s16c11_eq_of_isLn_le {W : Type} [CommGroup W] [Finite W] {L L₀ : Subgroup (MulAut W)}
    {m : ℕ} (hm : m ≠ 0) (hL₀ : IsLn ↥L₀ m 1) (hL : IsLn ↥L m 1) (hle : L ≤ L₀) : L = L₀ := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  exact Subgroup.eq_of_le_of_card_ge hle (s16e_card_eq_of_isLn hm hL₀ hL).le

theorem s16c11_eq_of_isSpn_six_le {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} (hL₀ : IsSpn ↥L₀ 6 1) (hL : IsSpn ↥L 6 1) (hle : L ≤ L₀) :
    L = L₀ := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun e : MulAut W => (e : W → W))
      (fun e₁ e₂ h => MulEquiv.ext (congrFun h))
  exact Subgroup.eq_of_le_of_card_ge hle (s16e_card_eq_of_isSpn_six hL₀ hL).le

theorem s16c11_rf3_of_binaryNaturalSL {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} {m : ℕ} (hm : 3 ≤ m) (hL₀ : IsLn ↥L₀ m 1)
    (hL : IsLn ↥L m 1) (hle : L ≤ L₀) (hJ : BinaryNaturalSL L J ⊥ m 1) :
    S16C11RF3 L₀ J := by
  obtain ⟨K, _, _, hKcard, hR⟩ := hJ
  obtain rfl : L = L₀ := s16c11_eq_of_isLn_le (by omega) hL₀ hL hle
  exact s16c11_rf3_of_modelRF3 (FFModel.nat_faithful _) hR
    (s16c11_modelRF3_statedSL (by rwa [pow_one] at hKcard) (by omega))

theorem s16c11_rf3_of_natSpn_six {W : Type} [CommGroup W] [Finite W]
    {L L₀ : Subgroup (MulAut W)} {J : Subgroup W} (hL₀ : IsSpn ↥L₀ 6 1) (hL : IsSpn ↥L 6 1)
    (hle : L ≤ L₀) (hJ : NatSpn L J ⊥ 6 1) : S16C11RF3 L₀ J := by
  obtain ⟨-, K, _, _, hKcard, hR⟩ := hJ
  obtain rfl : L = L₀ := s16c11_eq_of_isSpn_six_le hL₀ hL hle
  exact s16c11_rf3_of_modelRF3 (FFModel.nat_faithful _) hR
    (s16c11_modelRF3_statedSp (r := 6 / 2) (by rwa [pow_one] at hKcard) (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
