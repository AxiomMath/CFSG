module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Cfg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExCrit2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2FinInst
public import CFSG.Quasithin.EmptyFaithful.S146zRCaseTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Excl

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem e9_not_caseAutLn (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ cComp (mcOf T))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : Nonempty (OTwoQuot (K₁ ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) : False := by
  classical
  obtain ⟨ι⟩ := e
  have hn3 : 3 ≤ n := by omega
  have hLs : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    GoldS146P.sl_simple n hn3
  have hnc := GoldS146P.sl_nonabelian n hn3
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans hHG
  have hnorm : mcOf T ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [← hKz]
    exact le_normalizer_conjClosure _ _
  have hKTG : K₁ ⊔ T ≤ mcOf T := sup_le hK₁G hTG
  let ψ : ↥(K₁ ⊔ T) →* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(K₁ ⊔ T)))
  have hψ : Function.Surjective ψ := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = CFSG.Open.pCore 2 ↥(K₁ ⊔ T) := by
    ext x
    change ι (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hker2 : IsPGroup 2 ψ.ker := hψker ▸ CFSG.LieType.BorelTits.pCore_isPGroup 2
  let j : ↥K₁ →* ↥(K₁ ⊔ T) := Subgroup.inclusion le_sup_left
  have hj : Function.Injective j := Subgroup.inclusion_injective _
  have hjn : j.range.Normal := by
    rw [Subgroup.inclusion_range]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (hKTG.trans hnorm)
  have : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK₁)
  have : Nontrivial ↥K₁ := (Subgroup.nontrivial_iff_ne_bot _).mpr (ne_bot_of_mem_cComp hK₁)
  obtain ⟨θ, hθ, hθker⟩ := SBc15.exists_theta_sl hn ψ hψ hker2 j hj hjn
  have hkerθ : θ.ker = CFSG.Open.pCore 2 ↥K₁ :=
    q_ker_eq_pCore_of_surjective (hnc := hnc) θ hθ hθker
  let e₀ : OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hkerθ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  let e1 : ↥(imageOTwoQuot (mcOf T) K₁) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    eK.symm.trans e₀
  obtain ⟨Eh, -, hloc⟩ := e9Local_of_config h35 S hred hshape
  rw [hKz] at hloc
  rcases hn with rfl | rfl
  · exact hloc.false_of_binCrit e1 binCrit_sl4
  · exact hloc.false_of_binCrit e1 binCrit_sl5

end Excl

end CFSG.Quasithin
