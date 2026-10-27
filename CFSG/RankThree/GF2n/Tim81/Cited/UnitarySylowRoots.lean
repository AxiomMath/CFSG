module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Cited.SylowRootsModel
import CFSG.RankThree.GF2n.Tim81.Cited.SylowRootsUnique

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.LieType CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.Transvection

theorem unitarySylowRoots : UnitarySylowRoots := by
  intro K _ _ X₀ Δ f N hf hN _ hX S
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  let σ := unitaryInvolution (GaloisField 2 (2 * f)) 2 f
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have htr : ∀ a, σ a = a → ∃ c, c + σ c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hF ha
  have hN2 : 2 ≤ N := by omega
  obtain ⟨Φ', hker', hrange', hΔ', hSQ⟩ :=
    SUTrans.exists_sylowRoots_eq_map_lowRad hσ htr hN2 hker hrange hΔ S
  rw [hSQ]
  refine ⟨fun x hx y hy => SUTrans.commute_of_mem_map_lowRad hx hy,
    fun x hx => SUTrans.mul_self_eq_one_of_mem_map_lowRad hx,
    SUTrans.natCard_map_lowRad hF hf hker', ?_, ?_, ?_⟩
  · intro T _ hT
    exact SUTrans.inSubgroup_pCore_le_normalizer_map_lowRad hσ htr hN2 hker' hrange' hΔ' hT
  · intro A hA hAc
    exact SUTrans.le_map_lowRad_of_le_centralizer (X₀ := X₀) hσ hN2 hker' hΔ' hA hAc
  · intro E hE hEc hE2 hcard
    rw [← hrange'] at hE
    exact SUTrans.eq_map_lowRad_of_le_normalizer hF hf hN hker' hE hEc hE2 hcard
