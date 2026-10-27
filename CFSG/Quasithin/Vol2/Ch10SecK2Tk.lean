module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tg
public import CFSG.Quasithin.Vol2.Ch11SecAKC7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  Ch11.SecA KGNat Matrix Ch11.G2Q8

theorem lineTorusFacts_G2 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H}
    (hR : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ Z π)
    {S : Subgroup (MulAut W)} (hS : QuasithinUnique.IsSylowTwoOf S H) {U₂ : Subgroup W}
    (hU₂ : IsFlagW H S Z (2 ^ n) 2 U₂) : LineTorusFacts H S Z U₂ (2 ^ n) := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hR
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hS
  have hU := eq_U2_of_isFlagWG hW2 hf hc0 hc1 hg (by rw [hK]; exact hU₂)
  subst hU
  have hS₂ : perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup)) =
      (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g) := gammaW_two_eqG hf hc0 hc1 g
  have hfψ : ∀ γ w, g2Act g⁻¹ (f (psiG hc0 hc1 π g γ w)) = g2Act γ (g2Act g⁻¹ (f w)) :=
    fun γ w => by rw [f_psiG hf, g2Act_inv_apply]
  have hfz : ∀ w : W, g2Act g⁻¹ (f w) = 0 → w ∈ Z := fun w hw => by
    rw [← hf.ker, ← g2Act_apply_inv g (f w), hw, map_zero]
  refine ⟨fun w hw => ?_, fun X hZX hXU hX => ?_, ?_⟩
  ·
    change f w ∈ gmapG g (stdF K 2)
    rw [mem_gmapG]
    refine stdF_mono (by norm_num : 1 ≤ 2) (fixed_U0 fun u hu => ?_)
    have h1 := hw _ ((hg _).mpr ⟨u, hu, rfl⟩)
    rw [← hf.ker, hf.map_mul_inv, IsCoord.actG hf hc0 hc1, sub_eq_zero, g2Act_mul_apply,
      g2Act_mul_apply] at h1
    have h2 := congrArg (g2Act g⁻¹) h1
    rwa [g2Act_inv_apply] at h2
  ·
    by_cases h : X ≤ Z
    · exact Or.inl (le_antisymm h hZX)
    right
    obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp h
    refine le_antisymm hXU fun u hu => ?_
    have hy : g2Act g⁻¹ (f x) ∈ stdF K 2 := mem_gmapG.mp (hXU hxX)
    have hv : g2Act g⁻¹ (f u) ∈ stdF K 2 := mem_gmapG.mp hu
    by_cases hv0 : upart (g2Act g⁻¹ (f u)) = 0
    · have hu0 : upart (0 : Ix3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
      exact hZX (hfz u (KC7.eq_of_upart_eq hv (stdF K 2).zero_mem (by rw [hv0, hu0])))
    have hy0 : upart (g2Act g⁻¹ (f x)) ≠ 0 := fun h0 => by
      have hu0 : upart (0 : Ix3 → K) = 0 := funext fun i => by fin_cases i <;> rfl
      exact hxZ (hfz x (KC7.eq_of_upart_eq hy (stdF K 2).zero_mem (by rw [h0, hu0])))
    obtain ⟨A, hA⟩ := GroupTheory.SteinbergBK.exists_sl2_mulVec_eq _ _ hy0 hv0
    obtain ⟨γ, hγ⟩ := levi2_surjective h4 A
    have hγA : levi2Mat γ.1 = (A : Matrix (Fin 2) (Fin 2) K) := by
      rw [← levi2_apply, hγ]
    have hγS : (γ : ↥(cayleyGroup K)) ∈ stabQ (stdF K 2) := perfectCore_le _ γ.2
    set s := psiG hc0 hc1 π g γ with hs
    have hsS : s ∈ perfectCore (H ⊓ stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup)) := by
      rw [hS₂]
      exact ⟨γ, γ.2, rfl⟩
    have hfe : g2Act g⁻¹ (f (s x)) = g2Act g⁻¹ (f u) := by
      rw [hs, hfψ]
      refine KC7.eq_of_upart_eq ((mem_stabQ.mp hγS _).mp hy) hv ?_
      rw [upart_act _ hy, hγA, hA]
    have hfe' : f (s x) = f u := by
      rw [← g2Act_apply_inv g (f (s x)), hfe, g2Act_apply_inv]
    have hz : u * (s x)⁻¹ ∈ Z := (hf.eq_iff _ _).mp hfe'.symm
    have := X.mul_mem (hZX hz) (hX s hsS x hxX)
    rwa [inv_mul_cancel_right] at this
  ·
    set d : Kˣ := Units.mk0 c₀ hc0 with hd
    set D : ↥(cayleyGroup K) := g2T (d, 1) with hD
    have hDS : D ∈ stabQ (stdF K 2) := g2T_mem_stabQ _ 2
    set t := psiG hc0 hc1 π g D with ht
    have htHU : t ∈ H ⊓ stabW (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) := by
      rw [← map_stabQ_eq hf hc0 hc1 g]
      exact ⟨D, hDS, rfl⟩
    refine ⟨t, htHU, ?_, fun s hs => ?_, ?_⟩
    · classical
      have := Fintype.ofFinite K
      have hdq : d ^ (2 ^ n - 1) = 1 := by
        rw [← hK, Nat.card_eq_fintype_card, ← Fintype.card_units]
        exact pow_card_eq_one
      rw [ht, ← map_pow, hD, ← map_pow, Prod.pow_mk, hdq, one_pow, Prod.mk_one_one, map_one,
        map_one]
    · rw [hS₂] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      have hxS : x ∈ stabQ (stdF K 2) := perfectCore_le _ hx
      have hc : D * x * D⁻¹ * x⁻¹ ∈ pCoreOf 2 (perfectCore (stabQ (stdF K 2))) := by
        refine (mem_pCoreOf_gam2_iff h4).mpr ⟨Subgroup.mul_mem _ (g2T_conj_mem_gam2 _ hx)
          (Subgroup.inv_mem _ hx), ?_⟩
        have hinv : (d, (1 : Kˣ))⁻¹ = (d⁻¹, 1) := by rw [Prod.inv_mk, inv_one]
        rw [levi2Mat_mul ((stabQ (stdF K 2)).inv_mem hxS), hD, levi2Mat_conj_g2T _ hxS, hinv,
          levi2Mat_g2T_inl, levi2Mat_g2T_inl, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
          Matrix.mul_one, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
          ← levi2Mat_mul ((stabQ (stdF K 2)).inv_mem hxS), mul_inv_cancel, levi2Mat_one]
      have e : t * psiG hc0 hc1 π g x * t⁻¹ * (psiG hc0 hc1 π g x)⁻¹ =
          psiG hc0 hc1 π g (D * x * D⁻¹ * x⁻¹) := by
        rw [ht]
        simp only [map_mul, map_inv]
      have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
      have := finite_cayleyGroup (F := K)
      rw [hS₂, Ch11.SecS.C11P9A.pCoreOf_map_of_injective (psiG hc0 hc1 π g)
        (psiG_injective hf hc0 hc1 g) 2, e]
      exact ⟨_, hc, rfl⟩
    · obtain ⟨w, hw⟩ := hf.surj (g2Act g (eu 0 1))
      have hwU : w ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
        change f w ∈ gmapG g (stdF K 2)
        rw [mem_gmapG, hw, g2Act_inv_apply]
        exact stdF_mono (by norm_num : 1 ≤ 2) (mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)
      refine ⟨w, hwU, fun h => ?_⟩
      have h1 := congrArg f h
      rw [ht, f_psiG hf, hw, g2Act_inv_apply, hD, g2Act_g2T_eu] at h1
      have h2 := congrArg (g2Act g⁻¹) h1
      rw [g2Act_inv_apply, g2Act_inv_apply] at h2
      have h3 := congrFun h2 (.inl 0)
      simp [eu, hd] at h3
      exact hc1 h3

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
