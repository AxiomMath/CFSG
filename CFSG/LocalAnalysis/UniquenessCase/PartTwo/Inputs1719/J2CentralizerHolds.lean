module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2Centralizer
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtElRestJ2F
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InvolutionCentralizers
public import CFSG.GroupTheory.SylowInfNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.QuasithinUnique
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

theorem k_J2_center_five_holds :
    K_J2_center_five := by
  classical
  intro Y _ _ K hKnormal hKspor _hindex S hS
  have : K.Normal := hKnormal
  have hnorm : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.normalizer_eq_top]
  have hS2 : IsSylowTwoOf S ⊤ := ⟨hS.1, hS.2.1, hS.2.2⟩
  have hP : IsSylowTwoOf (S ⊓ K) K := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (G := Y) (S := S) (X := ⊤) (N := K)
      hS2 le_top hnorm
    simpa [inf_comm] using h
  let T : Subgroup ↥K := (S ⊓ K).subgroupOf K
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact IsPGroup.comap_subtype (K := K) hP.2.1
    · change ¬ 2 ∣ T.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      simpa [T] using hP.2.2
  let e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2 := Classical.choice hKspor
  have hcardK : Nat.card ↥K = 604800 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hcs : ∀ x y : ↥K, x ∈ T → y ∈ T →
      (∀ t ∈ T, x * t = t * x) → (∀ t ∈ T, y * t = t * y) →
        x = 1 ∨ y = 1 ∨ x = y := by
    intro x y hx hy hxc hyc
    have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
      CFSG.Quasithin.ModH.isSylowTwoOf_map_equiv e hT
    have hx' : e x ∈ T.map e.toMonoidHom := ⟨x, hx, rfl⟩
    have hy' : e y ∈ T.map e.toMonoidHom := ⟨y, hy, rfl⟩
    have hxc' : ∀ t ∈ T.map e.toMonoidHom, e x * t = t * e x := by
      rintro _ ⟨s, hs, rfl⟩
      simpa using congrArg e (hxc s hs)
    have hyc' : ∀ t ∈ T.map e.toMonoidHom, e y * t = t * e y := by
      rintro _ ⟨s, hs, rfl⟩
      simpa using congrArg e (hyc s hs)
    rcases CFSG.Quasithin.ModH.sylowFactsJ2_unfolded.1 (T.map e.toMonoidHom) hT'
        (e x) (e y) hx' hy' hxc' hyc' with h | h | h
    · left
      exact e.injective (by simpa using h)
    · right; left
      exact e.injective (by simpa using h)
    · right; right
      exact e.injective h
  have hY' : ∀ T' : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2),
      IsSylowTwoOf T' ⊤ →
        ∀ α : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J2),
          (∀ t ∈ T', α t = t) →
            ∃ z ∈ T', (∀ t ∈ T', z * t = t * z) ∧
              ∀ g, α g = z * g * z⁻¹ := by
    intro T' hT' α hα
    obtain ⟨hp, hidx⟩ := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mp hT'
    let P : Sylow 2 (CFSG.Blueprint.NativeSporadic.Carrier .J2) := hp.toSylow hidx
    have hP' : (P : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2)) = T' :=
      IsPGroup.toSylow_coe hp hidx
    have hαP : ∀ t ∈ (P : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2)),
        α t = t := by
      intro t ht
      exact hα t ht
    obtain ⟨z, hzcent, hz⟩ :=
      CFSG.Quasithin.ModH.sylowFactsJ2_unfolded.2 P α hαP
    refine ⟨(z : CFSG.Blueprint.NativeSporadic.Carrier .J2), hP' ▸ z.2, ?_, ?_⟩
    · intro t ht
      have hcomm := congrArg Subtype.val
        ((Subgroup.mem_center_iff.mp hzcent)
          (⟨t, ht⟩ : ↥(P : Subgroup _)))
      simpa using hcomm.symm
    · intro g
      exact hz g
  have hKcard : Nat.card ↥K = 2 ^ 7 * 4725 := by
    rw [hcardK]
    norm_num
  have hTcard : Nat.card T = 2 ^ 7 :=
    CFSG.Quasithin.ModH.card_eq_pow_of_isSylowTwoOf_top hT hKcard (by norm_num)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card T = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hTcard] at h1
    norm_num at h1
  obtain ⟨c₀, hc₀T, hc₀ne, hc₀sq, hc₀comm⟩ :=
    CFSG.Quasithin.ModH.exists_central_involution hT.2.1 hTne
  have hc₀ord : orderOf c₀ = 2 := by
    refine orderOf_eq_prime ?_ hc₀ne
    simpa [pow_two] using hc₀sq
  have h5C : 5 ∣ Nat.card (Subgroup.centralizer ({c₀} : Set ↥K)) := by
    rcases card_centralizer_of_involution_of_isSporadic_j2 (N := ↥K) hKspor c₀ hc₀ord
      with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxord⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({c₀} : Set ↥K)) 5 h5C
  let xK : ↥K := (x : ↥K)
  have hxKord : orderOf xK = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hxord
  have hxKcomm : c₀ * xK = xK * c₀ :=
    Subgroup.mem_centralizer_iff.mp x.2 c₀ (by simp)
  refine ⟨(xK : Y), xK.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hxKord
  · intro z hzS hzC
    let zN : Subgroup.normalizer (K : Set Y) := ⟨z, by
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top z⟩
    let α : MulAut ↥K := K.normalizerMonoidHom zN
    have hα : ∀ t ∈ T, α t = t := by
      intro t ht
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have htz : (t : Y) ∈ S := (Subgroup.mem_subgroupOf.mp ht).1
      rw [hzC (t : Y) htz]
      have hzN : (zN : Y) = z := rfl
      rw [hzN]
      group
    obtain ⟨c, hcT, hcZ, hcα⟩ :=
      CFSG.Quasithin.ModH.pointwise_of_equiv e hY' T hT α hα
    have hc_eq : c = 1 ∨ c = c₀ := by
      rcases hcs c c₀ hcT hc₀T hcZ hc₀comm with h | h | h
      · exact Or.inl h
      · exact Or.inr (False.elim (hc₀ne h))
      · exact Or.inr h
    have hαx : α xK = xK := by
      rw [hcα xK]
      rcases hc_eq with h | h
      · simp [h]
      · rw [h, hxKcomm]
        group
    have hconj : z * (xK : Y) * z⁻¹ = (xK : Y) := by
      have h1 : ((α xK : ↥K) : Y) = z * (xK : Y) * z⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe K zN xK
      rw [hαx] at h1
      exact h1.symm
    calc (xK : Y) * z = (z * (xK : Y) * z⁻¹) * z := by rw [hconj]
      _ = z * (xK : Y) := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
