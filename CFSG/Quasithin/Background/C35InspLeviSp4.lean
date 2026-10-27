module

public import CFSG.Quasithin.Background.C35InspLevi
public import CFSG.Quasithin.Background.C35InspSp4A
public import CFSG.Quasithin.H13.NQCatParabolicSp4
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListTits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Levi

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix C35Pf
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

section Sp4

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_noncomm_Q2 (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2) :
    ∃ r x : ↥(perfectCore (Q2 F j)), blkN j r = 1 ∧ x * r ≠ r * x := by
  obtain ⟨s, hs⟩ := H13.NQCat.exists_unit_ne_one hK4
  rcases fin_two_cases j with rfl | rfl
  · refine ⟨⟨H13.NQCat.Sp4.xA 1, H13.NQCat.Sp4.unipotent_le_perfectCore hK4 0
      (H13.NQCat.Sp4.xA_mem 1)⟩, ⟨spLevi 0 (H13.NQCat.dg2 s), spLevi_mem_perfectCore hK4 0 _⟩,
      ?_, ?_⟩
    · apply Subtype.ext
      rw [blkN_coe]
      show blkIdx (sigma2 0) (spMat (H13.NQCat.Sp4.xA 1)) = 1
      rw [H13.NQCat.Sp4.spMat_xA]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]
    · intro h
      have h1 := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h1
      have h2 : spLevi 0 (H13.NQCat.dg2 s) * H13.NQCat.Sp4.xA 1 * (spLevi 0 (H13.NQCat.dg2 s))⁻¹ =
          H13.NQCat.Sp4.xA 1 := by
        rw [h1, mul_inv_cancel_right]
      rw [H13.NQCat.Sp4.conj_zero_xA] at h2
      have h3 := congrFun (congrFun (congrArg spMat h2) (Sum.inl 0)) (Sum.inl 1)
      rw [H13.NQCat.Sp4.spMat_xA, H13.NQCat.Sp4.spMat_xA] at h3
      have hval : ∀ t : F, ((1 + t • Matrix.single (Sum.inl 0) (Sum.inl 1) 1 -
          t • Matrix.single (Sum.inr 1) (Sum.inr 0) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F))
          (Sum.inl 0) (Sum.inl 1) = t := by
        intro t
        simp
      rw [hval, hval, mul_one] at h3
      exact H13.NQCat.units_inv_ne_one hs h3
  · refine ⟨⟨H13.NQCat.Sp4.xC 1, H13.NQCat.Sp4.unipotent_le_perfectCore hK4 1
      (H13.NQCat.Sp4.xC_mem 1)⟩, ⟨spLevi 1 (H13.NQCat.dg2 s), spLevi_mem_perfectCore hK4 1 _⟩,
      ?_, ?_⟩
    · apply Subtype.ext
      rw [blkN_coe]
      show blkIdx (sigma2 1) (spMat (H13.NQCat.Sp4.xC 1)) = 1
      rw [H13.NQCat.Sp4.spMat_xC]
      ext i k
      fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]
    · intro h
      have h1 := congrArg Subtype.val h
      simp only [Subgroup.coe_mul] at h1
      have h2 : spLevi 1 (H13.NQCat.dg2 s) * H13.NQCat.Sp4.xC 1 * (spLevi 1 (H13.NQCat.dg2 s))⁻¹ =
          H13.NQCat.Sp4.xC 1 := by
        rw [h1, mul_inv_cancel_right]
      rw [H13.NQCat.Sp4.conj_one_xC] at h2
      have h3 := congrFun (congrFun (congrArg spMat h2) (Sum.inl 0)) (Sum.inr 0)
      rw [H13.NQCat.Sp4.spMat_xC, H13.NQCat.Sp4.spMat_xC] at h3
      have hval : ∀ t : F, ((1 + t • Matrix.single (Sum.inl 0) (Sum.inr 0) 1 :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (Sum.inl 0) (Sum.inr 0) = t := by
        intro t
        simp
      rw [hval, hval, mul_one] at h3
      have h4 : ((s : F) - 1) ^ 2 = 0 := by
        linear_combination h3 + (1 - (s : F)) * (CharTwo.two_eq_zero : (2 : F) = 0)
      exact hs (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4))

end Sp4

theorem levi_sp4 {A : Type} [Group A] [Finite A] {K Y : Subgroup A}
    (hZ : IsPGroup 2 ↥(centerOf K)) {f : ℕ} (hf2 : 2 ≤ f)
    (hX : IsPSp4 2 f (↥K ⧸ Subgroup.center ↥K)) (hpar : IsParabolic2 K Y) (hne : Y ≠ K)
    (hX0 : perfectCore Y ≠ ⊥) : LeviConcl K Y := by
  classical
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hX
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let ι : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) :=
    MulEquiv.ofBijective (proj 2 F) ⟨proj_injective_charTwo, proj_surjective⟩
  let φ : ↥K →* StatedSp 2 F := (e.trans ι.symm).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := (e.trans ι.symm).surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 2
  have hU : IsSylowTwoOf (unipotent 2 F) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  obtain ⟨g, hNY, hne', hns⟩ := exists_conj_normalizer hZ hpar hne hX0 φ hφker.le hφs hU
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by rw [hθ, ker_conj_comp, hφker]
  have hYK : Y ≤ K := hpar.1
  have hB : borelSubgroup 2 F ≤ img θ Y := by
    rw [← normalizer_unipotent]
    exact hNY
  obtain ⟨j, hj⟩ := eq_Q2_of_overgroup hK hB hne' hns
  have hMj : img θ (perfectCore Y) =
      (perfectCore (Q2 F j)).map (MonoidHom.id (StatedSp 2 F)) := by
    rw [Subgroup.map_id, img_perfectCore θ hYK, hj]
  have hinj : Set.InjOn (MonoidHom.id (StatedSp 2 F))
      (perfectCore (Q2 F j) : Set (StatedSp 2 F)) := fun _ _ _ _ h => h
  have := sl2_isSimple hK4
  obtain ⟨hc, ⟨eT⟩⟩ := levi_of_model hZ hYK θ hθker.le (MonoidHom.id (StatedSp 2 F)) hinj hMj
    (sl2_nonabelian hK4) (blkN j) (blkN_surjective hK4 j) (blkN_ker_isPGroup hK j)
    (exists_noncomm_Q2 hK4 j)
  exact leviConcl_of_small hc ((smallLevi_sl2 hcard hf2).of_mulEquiv eT.symm)

end CFSG.Quasithin.C35Levi
