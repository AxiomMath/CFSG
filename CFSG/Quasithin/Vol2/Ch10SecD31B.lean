module

public import CFSG.Quasithin.Vol2.Ch10SecDFacts31
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_sup_of_autI_le {U H K K' : Subgroup G} (hU : IsElemAbelian 2 U)
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hK : K ≤ H) (hK' : K' ≤ H)
    (hle : autI hU K ≤ autI hU K') : K ≤ K' ⊔ (H ⊓ Subgroup.centralizer (U : Set G)) := by
  intro k hk
  obtain ⟨g, hg, hge⟩ := (mem_autI hU).mp (hle (convI_mem_autI hU hk (hHU (hK hk))))
  have hc : convI hU (g⁻¹ * ⟨k, hHU (hK hk)⟩) = 1 := by
    rw [map_mul, map_inv, hge, inv_mul_cancel]
  rw [convI_eq_one_iff] at hc
  have hgk : ((g⁻¹ * ⟨k, hHU (hK hk)⟩ : Subgroup.normalizer (U : Set G)) : G) = (g : G)⁻¹ * k :=
    rfl
  have e1 : k = (g : G) * ((g : G)⁻¹ * k) := by group
  rw [e1]
  rw [hgk] at hc
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
    (Subgroup.mem_sup_right ⟨H.mul_mem (H.inv_mem (hK' hg)) (hK hk), hc⟩)

omit [Finite G] in
theorem nonempty_autI_equiv {U H : Subgroup G} (hU : IsElemAbelian 2 U)
    (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hC : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H) :
    Nonempty (↥(autI hU H) ≃* ↥H ⧸ CFSG.pCore 2 ↥H) := by
  set f := convHom hU H hHU with hf
  have hker : f.ker = CFSG.pCore 2 ↥H := by
    rw [hf, ker_convHom, hC]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  exact ⟨(MulEquiv.subgroupCongr (range_convHom hU H hHU)).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem aParam_autI_le_one (hA : FactAParamWreath) {U H T Y Z : Subgroup G}
    (hU : IsElemAbelian 2 U) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hC : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo) (hT : IsSylowTwoOf T H) (hTY : T ≤ Y)
    (hYH : Y ≤ H) (hHY : ¬ H ≤ Y ⊔ pCoreOf 2 H) (hYT : ¬ Y ≤ T ⊔ pCoreOf 2 H)
    (hZY : Y ≤ Subgroup.centralizer (Z : Set G)) (hUZ : U = conjClosure Z H) :
    E3.aParam (autI hU H) ≤ 1 := by
  obtain ⟨e₁⟩ := nonempty_autI_equiv hU hHU hC
  have hY'ne : autI hU Y ≠ autI hU H := fun heq => hHY (by
    have := le_sup_of_autI_le hU hHU le_rfl hYH heq.ge
    rwa [hC] at this)
  have hSne : autI hU T ≠ autI hU Y := fun heq => hYT (by
    have := le_sup_of_autI_le hU hHU hYH hT.1 heq.ge
    rwa [hC] at this)
  have hgen : (⨆ x ∈ autI hU H,
      (fixV (autI hU Y)).map (x : MulAut (IntMod U hU)).toMonoidHom) = ⊤ := by
    set J := ⨆ x ∈ autI hU H, (fixV (autI hU Y)).map (x : MulAut (IntMod U hU)).toMonoidHom
      with hJ
    let φ : IntMod U hU →* G :=
      { toFun := IntMod.val, map_one' := IntMod.val_one, map_mul' := IntMod.val_mul }
    have key : U ≤ J.map φ := by
      have hZU : Z ≤ U := hUZ ▸ le_conjClosure Z H
      refine hUZ.le.trans (conjClosure_le fun h hh z hz => ?_)
      let w : IntMod U hU := IntMod.mk hU ⟨z, hZU hz⟩
      have hw : w ∈ fixV (autI hU Y) := (mem_fixV_autI hU (hYH.trans hHU) w).mpr
        (Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (Subgroup.mem_centralizer_iff.mp (hZY hy) z hz).symm)
      refine ⟨convI hU ⟨h, hHU hh⟩ w, ?_, convI_apply_val hU _ _⟩
      exact (le_iSup₂ (f := fun (x : MulAut (IntMod U hU)) (_ : x ∈ autI hU H) =>
        (fixV (autI hU Y)).map (x : MulAut (IntMod U hU)).toMonoidHom)
        (convI hU ⟨h, hHU hh⟩) (convI_mem_autI hU hh (hHU hh))) ⟨w, hw, rfl⟩
    rw [eq_top_iff]
    intro w _
    obtain ⟨j, hj, hjw⟩ := key w.val_mem
    have : j = w := IntMod.val_injective hjw
    exact this ▸ hj
  exact hA (IntMod U hU) IntMod.sq_eq_one (autI hU H) (autI hU Y) (autI hU T) ⟨e₁.trans e⟩
    (autI_mono hU hYH) hY'ne (B2F.isSylowTwoOf_autI (hV := hU) hHU hT) (autI_mono hU hTY) hSne
    hgen

theorem commutator_wClos_ne_bot {V T H U M : Subgroup G} (hT : IsSylowTwoOf T H)
    (hHM : ¬ H ≤ M) (hC : H ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 H)
    (hNW : Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤ M) : ⁅U, E3.wClos V 0 T⁆ ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  have hWT : E3.wClos V 0 T ≤ T := E3.wClos_le_of_forall fun A hA => hA.1
  have hWO : E3.wClos V 0 T ≤ pCoreOf 2 H := hC ▸ le_inf (hWT.trans hT.1) hbot
  have hST : IsSylowIn 2 T T := ⟨le_rfl, hT.2.1, by rw [Subgroup.relIndex_self]; norm_num⟩
  have h1 := E3.e3_15_normalizer (V := V) hST (IsSylowTwoOf.pCoreOf_le hT)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hWO
  exact hHM ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans (h1.trans hNW))

end CFSG.Quasithin.Vol2.Ch10.SecD
