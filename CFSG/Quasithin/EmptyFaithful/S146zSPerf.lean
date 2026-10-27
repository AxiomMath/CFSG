module

public import CFSG.Quasithin.EmptyFaithful.S146zRImg
public import CFSG.Quasithin.Background.GoldschmidtS146PGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp

public section

namespace CFSG.Quasithin.GoldS146P

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

noncomputable def oTwoQuotConjEquivS (s : G) (K : Subgroup G) :
    OTwoQuot K ≃* OTwoQuot (conjSub s K) :=
  QuotientGroup.congr _ _
    (K.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective)
    (map_pCore_mulEquiv 2 _)

omit [Finite G] in
theorem imageOTwoQuot_sup_S {G₁ K L : Subgroup G} (hK : K ≤ G₁) (hL : L ≤ G₁) :
    imageOTwoQuot G₁ (K ⊔ L) = imageOTwoQuot G₁ K ⊔ imageOTwoQuot G₁ L := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_sup hK hL, Subgroup.map_sup]

theorem isComponent_image_of_L216 {G₁ K : Subgroup G} (hK : K ∈ cComp G₁)
    (e : Nonempty (OTwoQuot K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    CFSG.IsComponent (imageOTwoQuot G₁ K) := by
  obtain ⟨e⟩ := e
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := sl2_simple
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.symm.trans eK)
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup sl2_nonabelian).1, ?_⟩
  exact Id2519.mathlib_isSubnormal_of_open_top (subnormal_of_mem_cComp (q_image_mem_cComp hK))

theorem perfInLayer_oTwoQuot_of_L216 {G₁ K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp G₁)
    (hsG : s ∈ G₁)
    (hKzN : G₁ ≤ Subgroup.normalizer ((K₁ ⊔ conjSub s K₁ : Subgroup G) : Set G))
    (hidx : (imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁)).index ∣ 32)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) :
    PerfInLayer (OTwoQuot G₁) := by
  classical
  obtain ⟨e⟩ := e
  have hK₂ : conjSub s K₁ ∈ cComp G₁ := conjSub_mem_cComp_of_mem hK₁ hsG
  have hK₁G : K₁ ≤ G₁ := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ G₁ := le_of_mem_cComp hK₂
  have hN₁ : CFSG.IsComponent (imageOTwoQuot G₁ K₁) := isComponent_image_of_L216 hK₁ ⟨e⟩
  have hN₂ : CFSG.IsComponent (imageOTwoQuot G₁ (conjSub s K₁)) :=
    isComponent_image_of_L216 hK₂ ⟨(oTwoQuotConjEquivS s K₁).symm.trans e⟩
  have hNle : imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁) ≤ CFSG.layer (OTwoQuot G₁) := by
    rw [imageOTwoQuot_sup_S hK₁G hK₂G]
    exact sup_le (CFSG.LocalCores.component_le_layer hN₁)
      (CFSG.LocalCores.component_le_layer hN₂)
  have hKzG : K₁ ⊔ conjSub s K₁ ≤ G₁ := sup_le hK₁G hK₂G
  have hNn : (imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁)).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKzG).mpr hKzN).map (qPi G₁)
      (qPi_surjective G₁)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 5)).mp
    (by simpa using hidx)
  have hpq : IsPGroup 2 (OTwoQuot G₁ ⧸ imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁)) :=
    IsPGroup.of_card (n := j) (by rw [← Subgroup.index_eq_card, hj])
  have : Finite (OTwoQuot G₁ ⧸ imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁)) :=
    Nat.finite_of_card_ne_zero (by
      rw [← Subgroup.index_eq_card, hj]
      exact pow_ne_zero _ two_ne_zero)
  have : Group.IsNilpotent (OTwoQuot G₁ ⧸ imageOTwoQuot G₁ (K₁ ⊔ conjSub s K₁)) :=
    hpq.isNilpotent
  exact perfInLayer_of_le_layer _ hNle

end CFSG.Quasithin.GoldS146P
