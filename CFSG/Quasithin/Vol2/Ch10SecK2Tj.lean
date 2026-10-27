module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tg
public import CFSG.Quasithin.Vol2.Ch11SecAKA15

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin Ch11.SecA KGNat Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spLevi_mem_perfectCore)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom)

theorem lineTorusFacts_Sp4 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(Assembly.LowTwoRank.StatedSp 2 K) →* ↥H}
    (hR : (FFModel.nat (Assembly.LowTwoRank.StatedSp 2 K)).RealizesVia H ⊤ Z π)
    {S : Subgroup (MulAut W)} (hS : QuasithinUnique.IsSylowTwoOf S H) {U₂ : Subgroup W}
    (hU₂ : IsFlagW H S Z (2 ^ n) 2 U₂) : LineTorusFacts H S Z U₂ (2 ^ n) := by
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hR
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf hS
  rw [← hK] at hU₂
  obtain ⟨S', hS', hc, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW2 hf hg hU₂
  rw [(eq_std_of_stable_sp hS').2.1 hc]
  have hmemU : ∀ w : W, w ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup ↔
      mat 2 K g⁻¹ *ᵥ f w ∈ spPlane K := fun w => mem_gmapSp
  have hfz : ∀ w : W, mat 2 K g⁻¹ *ᵥ f w = 0 → w ∈ Z := fun w hw => by
    rw [← hf.ker, ← mat_mulVec_inv g (f w), hw, Matrix.mulVec_zero]
  refine ⟨fun w hw => ?_, fun X hZX hXU hX => ?_, ?_⟩
  ·
    change f w ∈ gmapSp g (spPlane K)
    exact gmapSp_mono g spLine_le_spPlane ((fixedW_iff_sp hf hg w).mp hw)
  ·
    by_cases h : X ≤ Z
    · exact Or.inl (le_antisymm h hZX)
    right
    obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp h
    refine le_antisymm hXU fun u hu => ?_
    have hy := (hmemU x).mp (hXU hxX)
    have hv := (hmemU u).mp hu
    obtain ⟨y, hydef⟩ : ∃ y, mat 2 K g⁻¹ *ᵥ f x = y := ⟨_, rfl⟩
    obtain ⟨v, hvdef⟩ : ∃ v, mat 2 K g⁻¹ *ᵥ f u = v := ⟨_, rfl⟩
    rw [hydef] at hy
    rw [hvdef] at hv
    obtain ⟨hy0, hy1⟩ := mem_spPlane.mp hy
    obtain ⟨hv0, hv1⟩ := mem_spPlane.mp hv
    by_cases hvz : (![v (.inl 0), v (.inl 1)] : Fin 2 → K) = 0
    · refine hZX (hfz u (hvdef.trans (vec4_eq ?_ ?_ ?_ ?_)))
      · simpa using congrFun hvz 0
      · simpa using congrFun hvz 1
      · simpa using hv0
      · simpa using hv1
    have hyz : (![y (.inl 0), y (.inl 1)] : Fin 2 → K) ≠ 0 := by
      intro h0
      refine hxZ (hfz x (hydef.trans (vec4_eq ?_ ?_ ?_ ?_)))
      · simpa using congrFun h0 0
      · simpa using congrFun h0 1
      · simpa using hy0
      · simpa using hy1
    obtain ⟨A, hA⟩ := GroupTheory.SteinbergBK.exists_sl2_mulVec_eq _ _ hyz hvz
    have hA0 := congrFun hA 0
    have hA1 := congrFun hA 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hA0 hA1
    set s := psiSp π g (spLevi 1 A) with hs
    have hsS : s ∈ perfectCore (H ⊓ stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)) := by
      rw [KA.gamma2_eq hf g]
      exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
    have hfe : f (s x) = f u := by
      have h1 := KA.act_levi1 hf g A x
      rw [hydef, KA.spLevi1_mulVec_plane A hy] at h1
      rw [← mat_mulVec_inv g (f (s x)), h1, ← mat_mulVec_inv g (f u), hvdef]
      congr 1
      refine vec4_eq ?_ ?_ ?_ ?_
      · rw [vec4_apply_inl0]; exact hA0
      · rw [vec4_apply_inl1]; exact hA1
      · rw [vec4_apply_inr0]; exact hv0.symm
      · rw [vec4_apply_inr1]; exact hv1.symm
    have hz : u * (s x)⁻¹ ∈ Z := (hf.eq_iff _ _).mp hfe.symm
    have := X.mul_mem (hZX hz) (hX s hsS x hxX)
    rwa [inv_mul_cancel_right] at this
  ·
    obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one (K := K) (by have := four_le_card hn hK; omega)
    set d : Kˣ := Units.mk0 c hc0 with hd
    set D : Assembly.LowTwoRank.StatedSp 2 K := torusHom (fun _ : Fin 2 => d) with hD
    have hDQ : D ∈ Q2 K 1 := Ch11.SecS.C11P9A.torusHom_mem_Q2 1 _
    set t := psiSp π g D with ht
    have htHU : t ∈ H ⊓ stabW (hf.pre (gmapSp g (spPlane K)).toAddSubgroup) := by
      rw [← map_stabilizer_eq hf g, ← flag_two_eq]
      exact ⟨D, hDQ, rfl⟩
    refine ⟨t, htHU, ?_, fun s hs => ?_, ?_⟩
    · classical
      have := Fintype.ofFinite K
      have hdq : d ^ (2 ^ n - 1) = 1 := by
        rw [← hK, Nat.card_eq_fintype_card, ← Fintype.card_units]
        exact pow_card_eq_one
      rw [ht, ← map_pow, hD, ← map_pow]
      have e : (fun _ : Fin 2 => d) ^ (2 ^ n - 1) = 1 := funext fun _ => by
        rw [Pi.pow_apply, hdq, Pi.one_apply]
      rw [e, map_one, map_one]
    · rw [KA.gamma2_eq hf g] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      obtain ⟨-, -, hsc⟩ := (Ch11.SecS.C11P9A.torusHom_mem_sc1_iff hK4
        (fun _ : Fin 2 => d)).mpr rfl
      have e : t * psiSp π g x * t⁻¹ * (psiSp π g x)⁻¹ = psiSp π g (D * x * D⁻¹ * x⁻¹) := by
        rw [ht]
        simp only [map_mul, map_inv]
      rw [KA.pCoreOf_gamma2_eq hf g, e]
      exact ⟨_, hsc x hx, rfl⟩
    · obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
      refine ⟨w, (hmemU w).mpr (by rw [hw, mat_inv_mulVec]; exact ⟨rfl, rfl⟩), fun h => ?_⟩
      have h1 := congrArg f h
      rw [ht, psiSp_apply, hf.act4, KA.gconj_mulVec_sp, hw, mat_inv_mulVec] at h1
      have h2 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h1
      simp only [mat_inv_mulVec] at h2
      have h3 := congrFun h2 (.inl 0)
      rw [hD] at h3
      simp [mat, coe_torusHom, Matrix.mulVec, dotProduct, vec4, Matrix.diagonal_apply, hd] at h3
      exact hc1 h3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
