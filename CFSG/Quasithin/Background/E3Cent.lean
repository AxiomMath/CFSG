module

public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Cent

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem le_centralizer_of_mem_gammaSet (hV : IsElemAbelian 2 V) {H S U A : Subgroup G}
    (hSH : S ≤ H) (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U) {i : ℕ}
    (hi : i < sParam hV - aParam (autI hU H)) (hA : A ∈ gammaSet V i S) :
    A ≤ Subgroup.centralizer (U : Set G) := by
  obtain ⟨hAS, g, hAg, hm⟩ := hA
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 A := B2F.isElemAbelian_mono hAg hVg
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAS.trans (hSH.trans hUn)
  by_contra hAc
  have hA1 : autI hU A ≠ ⊥ := fun h => hAc ((autI_eq_bot_iff hU hAN).1 h)
  have hmem : autI hU A ∈ aSet (aParam (autI hU H) + 1) (autI hU H) := by
    refine ⟨autI_mono hU (hAS.trans hSH), hA1, isElemAbelian2_autI hU hAel hAN, ?_⟩
    intro B' hB' hlt
    have hlt' : mQuot A (preI hU A hAN B') ≤ aParam (autI hU H) := by
      rw [← mQuot_autI_preI hU hAN hB']
      omega
    have hBA : preI hU A hAN B' ≤ A := preI_le hU
    have hadd := mQuot_add (V := conjSubgroup V g) hBA hAg
    have hlt2 : mQuot (conjSubgroup V g) (preI hU A hAN B') < sParam hVg := by
      rw [sParam_conj hV g hVg]
      omega
    have hCB := (e3_6 hVg hBA hAg hlt2 (B2F.isPGroup_of_isElemAbelian hU)).1
    have hpre : autI hU (preI hU A hAN B') = B' := autI_preI hU hB'
    have hBN : preI hU A hAN B' ≤ Subgroup.normalizer (U : Set G) := hBA.trans hAN
    ext v
    have e1 : v ∈ fixV B' ↔ v.val ∈ Subgroup.centralizer (preI hU A hAN B' : Set G) := by
      conv_lhs => rw [← hpre]
      exact mem_fixV_autI hU hBN v
    have e2 : v ∈ fixV (autI hU A) ↔ v.val ∈ Subgroup.centralizer (A : Set G) :=
      mem_fixV_autI hU hAN v
    rw [e1, e2]
    have hv : v.val ∈ U := v.val_mem
    constructor
    · intro hc
      have : v.val ∈ U ⊓ Subgroup.centralizer (preI hU A hAN B' : Set G) :=
        Subgroup.mem_inf.2 ⟨hv, hc⟩
      rw [← hCB] at this
      exact (Subgroup.mem_inf.1 this).2
    · intro hc
      have : v.val ∈ U ⊓ Subgroup.centralizer (A : Set G) := Subgroup.mem_inf.2 ⟨hv, hc⟩
      rw [hCB] at this
      exact (Subgroup.mem_inf.1 this).2
  have := le_aParam_of_mem_aSet (Nat.succ_pos _) hmem
  omega

theorem e3_18_comm (hV : IsElemAbelian 2 V) {H S U : Subgroup G} (hSH : S ≤ H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U) {i : ℕ}
    (hi : i < sParam hV - aParam (autI hU H)) : ⁅U, wClos V i S⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact wClos_le_of_forall fun A hA => le_centralizer_of_mem_gammaSet hV hSH hUn hU hi hA

theorem e3_18_factor (hV : IsElemAbelian 2 V) {H S U : Subgroup G} (hS : IsSylowIn 2 S H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hU : IsElemAbelian 2 U) {i : ℕ}
    (hi : i < sParam hV - aParam (autI hU H)) :
    ∀ h ∈ H, ∃ c ∈ H ⊓ Subgroup.centralizer (U : Set G),
      ∃ n ∈ H ⊓ Subgroup.normalizer (wClos V i S : Set G), h = c * n := by
  set N := H ⊓ Subgroup.centralizer (U : Set G) with hNdef
  have hNH : N ≤ H := inf_le_left
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ k ∈ H, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
      intro k hk x hx
      refine Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hk (Subgroup.mem_inf.1 hx).1) (H.inv_mem hk),
        Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      have hu' : k⁻¹ * u * k ∈ U := by
        have := (Subgroup.mem_normalizer_iff.1 (hUn (H.inv_mem hk)) u).1 hu
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 _ hu'
      calc u * (k * x * k⁻¹) = k * ((k⁻¹ * u * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * u * k)) * k⁻¹ := by rw [hc]
        _ = (k * x * k⁻¹) * u := by group
    constructor
    · exact key h hh x
    · intro hx
      have := key h⁻¹ (H.inv_mem hh) _ hx
      simpa [mul_assoc] using this
  have hSN : IsSylowIn 2 (S ⊓ N) N := B6.isSylowTwoOf_inf_normal hS hNH hHN
  have hSNe : S ⊓ N = S ⊓ Subgroup.centralizer (U : Set G) := by
    rw [hNdef, ← inf_assoc, inf_eq_left.2 (hS.le : S ≤ H)]
  have hY2 : IsPGroup 2 ↥(S ⊓ Subgroup.centralizer (U : Set G)) := hS.isPGroup.to_le inf_le_left
  have hYH : S ⊓ Subgroup.centralizer (U : Set G) ≤ H := inf_le_left.trans hS.le
  have hW : wClos V i S ≤ S ⊓ Subgroup.centralizer (U : Set G) :=
    wClos_le_of_forall fun A hA =>
      le_inf hA.1 (le_centralizer_of_mem_gammaSet hV hS.le hUn hU hi hA)
  have hfr := B6.frattini_two hNH hHN (hSNe ▸ hSN)
  have hnorm := e3_15_normalizer hS hYH hY2 hW
  intro h hh
  have hmem : h ∈ N ⊔ (H ⊓ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (U : Set G) :
      Subgroup G) : Set G)) := hfr hh
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left N
    (H ⊓ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G))
    (fun k hk => hHN hk.1)
  rw [← SetLike.mem_coe, hcoe] at hmem
  obtain ⟨c, hc, n, hn, rfl⟩ := hmem
  exact ⟨c, hc, n, Subgroup.mem_inf.2 ⟨hn.1, hnorm hn.2⟩, rfl⟩

end Cent

end E3

end CFSG.Quasithin
