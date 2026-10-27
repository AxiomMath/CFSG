module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18DispRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.OddOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp4
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModSp4Outer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146ModSp4_holds : K146ModSp4 := by
  intro U _ _ hU N S n hSN hNnorm hSp hodd hn hirr hm
  classical
  have hodd' : Odd n := hodd
  obtain ⟨k, hk⟩ := hodd'
  obtain ⟨hn2, K, hfield, hfin, hchar, hKcard, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  letI := hfield
  letI := hfin
  letI := hchar
  have hKf : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hKcard]
  letI : Module (ZMod 2) (Additive U) := CFSG.Quasithin.SmithD37.zmodModule hU
  let θ : U ≃* Multiplicative (Additive U) := CFSG.Quasithin.SmithD37.theta
  let ρS : ↥S →* (Additive U ≃ₗ[ZMod 2] Additive U) :=
    (CFSG.Quasithin.SmithD37.autLin hU).toMonoidHom.comp S.subtype
  let π : ↥(CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K) →*
      (Additive U ≃ₗ[ZMod 2] Additive U) := ρS.comp e.symm.toMonoidHom
  have hπ : ∀ (g : ↥(CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K))
      (w : Additive U),
      π g w = CFSG.QuasithinUnique.Setup.Layer.binPsi θ ((e.symm g : ↥S) : MulAut U) w :=
    fun _ _ => rfl
  have hirrV : ∀ J : Subgroup U, (∀ g ∈ S, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJ => hirr.2.2.2 J hJ bot_le le_top
  have hirrW : ∀ V : Submodule (ZMod 2) (Additive U),
      (∀ g : ↥(CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K), ∀ u ∈ V,
        π g u ∈ V) → V = ⊥ ∨ V = ⊤ := by
    intro V hV
    refine CFSG.Quasithin.B42L2.irr_map θ hirrV V ?_
    rintro _ ⟨l, hl, rfl⟩ u hu
    have h := hV (e ⟨l, hl⟩) u hu
    rwa [hπ, MulEquiv.symm_apply_apply] at h
  have hntW : Nontrivial (Additive U) := by
    obtain ⟨x, -, hx1⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨Additive.ofMul x, 0, fun h => hx1 (by simpa using congrArg Additive.toMul h)⟩
  have hntπ : ∃ g, CFSG.Quasithin.B42Sp4.repOf π g ≠ 1 := by
    refine ⟨CFSG.QuasithinUnique.Setup.X7b.invX K, fun h => ?_⟩
    have h2 : ρS (e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K)) = 1 :=
      LinearEquiv.ext fun w => LinearMap.congr_fun h w
    have h3 : ((e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K) : ↥S) : MulAut U) = 1 :=
      (CFSG.Quasithin.SmithD37.autLin hU).injective h2
    have h4 : e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K) = 1 := Subtype.ext h3
    have h5 : CFSG.QuasithinUnique.Setup.X7b.invX K = 1 := by
      rw [← e.apply_symm_apply (CFSG.QuasithinUnique.Setup.X7b.invX K), h4, map_one]
    exact CFSG.QuasithinUnique.Setup.X7b.invX_ne_one (F := K) h5
  have hFact : Fact (CFSG.Quasithin.B42Sp4.repOf π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff
      (CFSG.Quasithin.B42Sp4.repOf π)).mpr ⟨hntW, hirrW⟩⟩
  letI := hFact
  have hinvS : ∃ l : ↥S, orderOf l = 2 := by
    refine ⟨e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K), ?_⟩
    have h2 : e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K) *
        e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K) = 1 := by
      rw [← map_mul, CFSG.QuasithinUnique.Setup.X7b.invX_mul_self, map_one]
    have h1 : e.symm (CFSG.QuasithinUnique.Setup.X7b.invX K) ≠ 1 := fun h =>
      CFSG.QuasithinUnique.Setup.X7b.invX_ne_one (F := K) (by
        rw [← e.apply_symm_apply (CFSG.QuasithinUnique.Setup.X7b.invX K), h, map_one])
    exact orderOf_eq_prime (by simpa [pow_two] using h2) h1
  have hEvenN : Even (Nat.card ↥N) :=
    CFSG.Quasithin.even_card_of_le_of_involution hSN hinvS
  obtain ⟨t, htN, htord, htval⟩ :=
    CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hEvenN
  have hle_t : rkIdx (fixV (Subgroup.zpowers t)) ≤ 2 * n + 2 := by
    rw [htval]; exact hm
  have hnat : NatSpn S ⊤ ⊥ 4 n := by
    by_contra hnotNat
    have hdim : Module.finrank
        (CFSG.QuasithinUnique.Setup.SL2Modules.EndRing
          (CFSG.Quasithin.B42Sp4.repOf π)) (Additive U) ≠ 4 := by
      intro h4
      apply hnotNat
      obtain ⟨i, φ', hφ'⟩ :=
        CFSG.Quasithin.B42Sp4.exists_natural_of_four hKf (by omega) π hntπ h4
      refine Thm14_5.natSpn_of_mulVec hKcard θ
        (e.trans (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorAut K ^ i)) φ' ?_
      intro l w
      have h := hφ' (e l) w
      rwa [hπ, MulEquiv.symm_apply_apply] at h
    have hdisp : 3 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
      have h4 : rkIdx (fixV (Subgroup.zpowers t)) =
          CFSG.QuasithinUnique.Setup.X7b.dispRank
            (CFSG.Quasithin.SmithD37.autLin hU t) :=
        rkIdx_fixV_zpowers_eq_dispRank hU t
      by_cases hinner : ∃ s : MulAut U, s ∈ S ∧ ∀ x ∈ S, t * x * t⁻¹ = s * x * s⁻¹
      · obtain ⟨s, hsS, hs⟩ := hinner
        have ht2 : t * t = 1 := by rw [← pow_two, ← htord]; exact pow_orderOf_eq_one t
        have htS : t ∈ S :=
          mem_of_conj_eq_conj_of_isIrrOn hU hirr
            (K148.AutAux.center_eq_bot_of_equiv_antiSp e) hsS ht2
            (fun x hx => (hs x hx).symm)
        let z : ↥(CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K) :=
          e ⟨t, htS⟩
        have hz2 : z * z = 1 := by
          rw [← map_mul]
          congr 1
          exact Subtype.ext (by simpa using ht2)
        have hz1 : z ≠ 1 := by
          intro h
          have h1 : (⟨t, htS⟩ : ↥S) = 1 := e.injective (by simpa [z] using h)
          have h2 : t = 1 := congrArg Subtype.val h1
          rw [h2, orderOf_one] at htord
          exact absurd htord (by norm_num)
        have h3 := (CFSG.Quasithin.B42Sp4.displacement_ge hKf (by omega) π hntπ hdim
          hz2 hz1).1
        have h5 : CFSG.QuasithinUnique.Setup.X7b.dispRank
            (CFSG.Quasithin.SmithD37.autLin hU t) =
            CFSG.QuasithinUnique.Setup.X7b.dispRank (π z) := by
          congr 1
          show CFSG.Quasithin.SmithD37.autLin hU t = π z
          simp [π, ρS, z]
        omega
      · rw [h4]
        exact Sp4Outer.three_mul_le_dispRank_of_not_inner hU S n hSp hodd
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mp hNnorm htN) htord hinner
    omega
  refine ⟨hnat, ?_⟩
  have hnatC : CFSG.LocalAnalysis.UniquenessCase.UC22.IsNaturalClassicalModule S n :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨hSp, hnat⟩)))
  exact Thm14_5.le_mParam_of_isNaturalClassicalModule hU hSN hNnorm hirr hnatC hEvenN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
