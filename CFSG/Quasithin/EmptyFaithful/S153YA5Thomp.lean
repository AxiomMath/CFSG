module

public import CFSG.Quasithin.EmptyFaithful.ModFA5Cfg
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Basic

public section

namespace CFSG.Quasithin.YG

open scoped Pointwise commutatorElement
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem commutator_thompsonJ_eq_single {I S K M₀ : Subgroup G} (hS : IsSylowTwoOf S I) (hK : IsShort2 K)
    (h5 : IsAltType K 5) (hSN : S ≤ Subgroup.normalizer (K : Set G)) (hI : I = S ⊔ K)
    (hM₀ : M₀ ≤ Subgroup.normalizer (S : Set G)) (hb : C5.NoCommonNormal S I M₀) :
    ⁅K, thompsonJ S⁆ = K := by
  classical
  set J := thompsonJ S with hJdef
  have hJS : J ≤ S := GammaExtra.thompsonJ_le_self S
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := hJS.trans hSN
  have hKI : K ≤ I := hI ▸ le_sup_right
  have hIK : I ≤ Subgroup.normalizer (K : Set G) := by
    rw [hI]
    exact sup_le hSN Subgroup.le_normalizer
  have hWK : ⁅K, J⁆ ≤ K := by
    refine Subgroup.commutator_le.2 fun k hk j hj => ?_
    have h1 : j * k⁻¹ * j⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hJK hj) k⁻¹).1 (K.inv_mem hk)
    have e : ⁅k, j⁆ = k * (j * k⁻¹ * j⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact K.mul_mem hk h1
  have hWn : ∀ l ∈ K, ∀ w ∈ ⁅K, J⁆, l * w * l⁻¹ ∈ ⁅K, J⁆ := by
    intro l hl w hw
    rw [Subgroup.commutator_def] at hw ⊢
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, j, hj, rfl⟩ := hx
      have e : l * ⁅k, j⁆ * l⁻¹ = ⁅l * k, j⁆ * ⁅l, j⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨l * k, K.mul_mem hl hk, j, hj, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨l, hl, j, hj, rfl⟩))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  rcases AppCS2.normal_le_or_eq_alt5 hK h5 hWK hWn with h | h
  swap
  · exact h
  exfalso
  have hQKI : blockQ K ≤ pCoreOf 2 I :=
    C1.le_pCoreOf_of_normalized ((C1.blockQ_le K).trans hKI)
      (fun g hg => C1.mem_normalizer_blockQ (hIK hg)) (C1.blockQ_isPGroup K)
  have hQS : pCoreOf 2 I ≤ S := hS.pCoreOf_le
  have hJQ : J ≤ pCoreOf 2 I := by
    intro j hj
    refine ModF.mem_pCoreOf_of_conj_mem hS.isPGroup (hS.le (hJS hj)) fun y hy => ?_
    have hy' : y ∈ ((S : Subgroup G) : Set G) * ((K : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S K hSN, ← hI]
      exact hy
    obtain ⟨s, hs, k, hk, rfl⟩ := hy'
    have hc : k * j * k⁻¹ * j⁻¹ ∈ blockQ K := h (Subgroup.commutator_mem_commutator hk hj)
    have hcS : k * j * k⁻¹ * j⁻¹ ∈ S := hQS (hQKI hc)
    have e : s * k * j * (s * k)⁻¹ = s * ((k * j * k⁻¹ * j⁻¹) * j) * s⁻¹ := by group
    rw [e]
    exact S.mul_mem (S.mul_mem hs (S.mul_mem hcS (hJS hj))) (S.inv_mem hs)
  have hJQ' : thompsonJ (pCoreOf 2 I) = J := GammaExtra.thompsonJ_eq_of_le hJQ hQS
  have hM₀J : M₀ ≤ Subgroup.normalizer (J : Set G) := hM₀.trans (GammaExtra.normalizer_le_normalizer_thompsonJ S)
  have hIJ : I ≤ Subgroup.normalizer (J : Set G) := by
    rw [← hJQ']
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I).trans
      (GammaExtra.normalizer_le_normalizer_thompsonJ _)
  have hJne : J ≠ ⊥ := by
    obtain ⟨A, hA⟩ := GammaExtra.exists_isMaxElemAbelian S
    intro hbot
    have hAbot : A = ⊥ := le_bot_iff.mp (hbot ▸ GammaExtra.le_thompsonJ hA)
    have hUS : blockU K ≤ S := ((C1.blockU_le_blockQ hK).trans hQKI).trans hQS
    have hU : Nat.card (blockU K) ≤ Nat.card A := hA.2.2 (blockU K) hUS (AppC.isElemAbelian_blockU hK)
    rw [hAbot, Subgroup.card_bot] at hU
    have : blockU K = ⊥ := Subgroup.eq_bot_of_card_eq _ (le_antisymm hU Nat.card_pos)
    exact C56.blockU_ne_bot hK this
  exact hb J hJS hJne hIJ hM₀J

end CFSG.Quasithin.YG
