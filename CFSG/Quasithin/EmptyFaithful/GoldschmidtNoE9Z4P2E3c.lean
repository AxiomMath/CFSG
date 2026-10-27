module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg2
public import CFSG.Quasithin.Background.GoldschmidtS146PMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.GoldS146P

section Fstar

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem exists_four_gf4 : ∃ s : Finset (GaloisField 2 2), s.card = 4 := by
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  refine ⟨Finset.univ, ?_⟩
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by omega)]
  norm_num

theorem e9_isComponent_image_sl2_four {G₁ K : Subgroup G} (hK : K ∈ cComp G₁)
    (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))) :
    CFSG.IsComponent (imageOTwoQuot G₁ K) := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple exists_four_gf4
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.symm.trans eK)
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian exists_four_gf4)).1, ?_⟩
  exact Id2519.mathlib_isSubnormal_of_open_top (subnormal_of_mem_cComp (q_image_mem_cComp hK))

theorem isPGroup_two_quotient_of_decomp {X : Type*} [Group X] {N T : Subgroup X} [N.Normal]
    (hT : IsPGroup 2 ↥T) (h : ∀ x : X, ∃ n ∈ N, ∃ t ∈ T, x = n * t) :
    IsPGroup 2 (X ⧸ N) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨n, hn, t, ht, rfl⟩ := h x
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  refine ⟨k, ?_⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hm : (QuotientGroup.mk (n * t) : X ⧸ N) = QuotientGroup.mk t := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  rw [hm, ← QuotientGroup.mk_pow, hk']
  rfl

theorem e9_fstar_of_E3 (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hC : Stage14614E9C3 T H) : oTwoUpper H ≤ oTwoFstarIn (mcOf T) := by
  classical
  obtain ⟨K₁, s, hK₁, hsT, hsN, hKz, ⟨e⟩, hG⟩ := hC
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  have hsG : s ∈ mcOf T := hTG hsT
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp hK₂
  have hN₁ := e9_isComponent_image_sl2_four hK₁ ⟨e⟩
  have hN₂ := e9_isComponent_image_sl2_four hK₂ ⟨(oTwoQuotConjEquivS s K₁).symm.trans e⟩
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := by
    rw [hKz]
    exact sup_le hK₁G hK₂G
  have hKzN : mcOf T ≤ Subgroup.normalizer
      ((conjClosure (oTwoUpper H) (mcOf T) : Subgroup G) : Set G) :=
    le_normalizer_conjClosure _ _
  have hNn : (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).Normal :=
    q_normal_image_of_normal hKzG hKzN
  have hNle : imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) ≤
      CFSG.layer (OTwoQuot (mcOf T)) := by
    rw [hKz, imageOTwoQuot_sup_S hK₁G hK₂G]
    exact sup_le (CFSG.LocalCores.component_le_layer hN₁)
      (CFSG.LocalCores.component_le_layer hN₂)
  have hpq : IsPGroup 2 (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) :=
    isPGroup_two_quotient_of_decomp (q_hatT_sylow S).2.1 (e9_hX_of_eq_sup S hG)
  have : Group.IsNilpotent (OTwoQuot (mcOf T) ⧸
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))) := hpq.isNilpotent
  have hlayer : PerfInLayer (OTwoQuot (mcOf T)) := perfInLayer_of_le_layer _ hNle
  have hperf : ⁅conjClosure (oTwoUpper H) (mcOf T), conjClosure (oTwoUpper H) (mcOf T)⁆ =
      conjClosure (oTwoUpper H) (mcOf T) := by
    rw [hKz]
    exact perfect_sup_conjSub (perfect_of_mem_cComp hK₁) s
  have hlayer' : PerfInLayer (↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T)) :=
    PerfInLayer.of_equiv (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥(mcOf T) 2))
      hlayer
  exact (le_conjClosure _ _).trans (perfect_le_oTwoFstarIn hlayer' hKzG hperf)

end Fstar

end CFSG.Quasithin
