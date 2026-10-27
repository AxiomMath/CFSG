module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentySix

theorem mem_centralizer_of_bot {V : Subgroup G} {c : G}
    (hc : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G)) : c ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := hc v hv
  rw [Subgroup.mem_bot] at h1
  calc v * c = (c * v * c⁻¹ * v⁻¹)⁻¹ * (c * v) := by group
    _ = c * v := by rw [h1, inv_one, one_mul]

theorem commutator_ne_bot_of_barSub_ne_bot (D : Data G) {V L : Subgroup G}
    (hV : InCalV D.M V) (hLM : L ≤ D.M) (hVe : IsElemAbelian 2 V)
    (hH : barSub ⊥ V hVe (UC22.conjClosure D.M L) ≠ ⊥) : ⁅L, V⁆ ≠ ⊥ := by
  intro hLV
  apply hH
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hLC : L ≤ centralizer (V : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLV
  have hHC : UC22.conjClosure D.M L ≤ centralizer (V : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    rintro _ ⟨l, hl, rfl⟩
    have e : (MulAut.conj g).toMonoidHom l = g * l * g⁻¹ := by simp [MulAut.conj_apply]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (A1a.le_normalizer_centralizer hMV hg) l).1 (hLC hl)
  rw [eq_bot_iff]
  intro φ hφ
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub _ _ _ _ φ).1 hφ
  rw [Subgroup.mem_bot, actTil_eq_one_iff]
  intro v hv
  have h1 := Subgroup.mem_centralizer_iff.1 (hHC hgX) v hv
  rw [Subgroup.mem_bot]
  calc (g : G) * v * (g : G)⁻¹ * v⁻¹ = v * g * (g : G)⁻¹ * v⁻¹ := by rw [← h1]
    _ = 1 := by group

theorem centralizer_Z_le (D : Data G) {V L : Subgroup G} (hV : InCalV D.M V)
    (hLM : L ≤ D.M) (hVe : IsElemAbelian 2 V) (hU : UniqueMax D.M (L ⊔ D.T))
    (hfix : fixV (barSub ⊥ V hVe (UC22.conjClosure D.M L)) ≠ ⊥) :
    centralizer (D.Z : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hMstab : D.M ≤ stabTil ⊥ V := le_stabTil hMV (by
    rw [Subgroup.normalizer_eq_top]
    exact le_top)
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfix
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hVe w
  have hx1 : x.val ≠ 1 := by
    intro hx
    apply hw1
    apply Subtype.ext
    show mkTil ⊥ V hVe x = 1
    rw [mkTil, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_modNull, hx]
    exact Subgroup.one_mem _
  have hcx : ∀ g ∈ UC22.conjClosure D.M L, g * x.val = x.val * g := by
    intro g hg
    have hgs : g ∈ stabTil ⊥ V := hMstab (TwelveTwentyThree.conjClosure_le hLM hg)
    have h1 := (mem_fixV.1 hw) _ (actTil_mem_barSub ⊥ V hVe hg hgs)
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at h1
    calc g * x.val = g * x.val * g⁻¹ * (x.val)⁻¹ * x.val * g := by group
      _ = x.val * g := by rw [h1, one_mul]
  set H := UC22.conjClosure D.M L with hHdef
  set Y : Subgroup G := V ⊓ centralizer (H : Set G) with hYdef
  have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D hV
  have hYT : Y ≤ D.T := inf_le_left.trans hVT
  have hTY : D.T ≤ normalizer (Y : Set G) :=
    A1a.le_normalizer_inf (D.sylowM.le.trans hMV)
      (A1a.le_normalizer_centralizer
        (D.sylowM.le.trans (TwelveTwentyThree.le_normalizer_conjClosure D.M L)))
  haveI hYn : (Y.subgroupOf D.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYT).2 hTY
  have hxY : x.val ∈ Y := ⟨x.val_mem, Subgroup.mem_centralizer_iff.2 hcx⟩
  have hYne : Y.subgroupOf D.T ≠ ⊥ := by
    intro h0
    apply hx1
    have : (⟨x.val, hYT hxY⟩ : ↥D.T) ∈ Y.subgroupOf D.T := hxY
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  haveI : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
  obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hYne)
  have htY : (t : G) ∈ Y := ht.1
  have htc : ∀ k ∈ D.T, k * (t : G) = (t : G) * k := fun k hk =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 ht.2 ⟨k, hk⟩)
  have ht1' : (t : G) ≠ 1 := fun h => ht1 (Subtype.ext (Subtype.ext h))
  have htZ : (t : G) ∈ D.Z :=
    CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2
      ⟨t.2, htc, hVe.2 (t : G) htY.1⟩
  have hLc : L ≤ centralizer ((zpowers (t : G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (TwelveTwentyThree.le_conjClosure D.M L))
        htY.2))
  have hTc : D.T ≤ centralizer ((zpowers (t : G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.2 (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 htc))
  have hp : IsPGroup 2 ↥(zpowers (t : G)) :=
    (uc22p22e_isPGroup_of_elem hVe).to_le (Subgroup.zpowers_le.2 htY.1)
  have hNM : normalizer ((zpowers (t : G) : Subgroup G) : Set G) ≤ D.M :=
    uc22p22p_le_of_uniqueMax hU ⟨zpowers (t : G), Subgroup.zpowers_ne_bot.2 ht1', hp, rfl⟩
      ((sup_le hLc hTc).trans (Subgroup.centralizer_le_normalizer _))
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (Subgroup.zpowers_le.2 htZ))).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNM)

end TwelveTwentySix

theorem twelve_twentySix (D : Data G) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {L : Subgroup G}
    (hL : F12.IsComponentModO2 D.M L) (hU : UniqueMax D.M (L ⊔ D.T))
    (hH : barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥) :
    fixV (barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      (V₀ = ⊥ ∧ ClassicalEvenAltG2Der (UC22.Bar2 L) ∧
        ⁅barSub V₀ V h.isElemAbelian (F12.jOf D.T), barSub V₀ V h.isElemAbelian L⁆ ≠ ⊥) := by
  have hLM : L ≤ D.M := hL.2.1
  have hVe : IsElemAbelian 2 V := h.isElemAbelian
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    by_cases hfix : fixV (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥
    · exact Or.inl hfix
    right
    have hW : InCalW D.M D.T V := by
      rcases h.1 with h1 | ⟨h0, -, -⟩
      · exact h1.1.1
      · exact absurd rfl h0.1.1
    have hMV : D.M ≤ normalizer (V : Set G) := hW.1.1.2.2.1
    have hMstab : D.M ≤ stabTil ⊥ V := le_stabTil hMV (by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
    have hLV := TwelveTwentySix.commutator_ne_bot_of_barSub_ne_bot D hW.1.1 hLM hVe hH
    have hCle := TwelveTwentySix.centralizer_Z_le D hW.1.1 hLM hVe hU hfix
    obtain ⟨h2a, hcls⟩ := (twelve_twentyFive D h640 hFF hW hCle).2 L hL hU hLV
    refine ⟨rfl, hcls, fun hJL' => h2a ?_⟩
    have hPV := TwelveTwentyThree.pCoreOf_le_centralizer_of_twoReduced hMV hW.2.2
    have hKn : D.M ≤ normalizer ((D.M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
      A1a.le_normalizer_inf Subgroup.le_normalizer (A1a.le_normalizer_centralizer hMV)
    have hPK : pCoreOf 2 D.M ≤ D.M ⊓ centralizer (V : Set G) :=
      le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M) hPV
    have hLK : ¬ L ≤ D.M ⊓ centralizer (V : Set G) := fun hle =>
      hLV (Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans inf_le_right))
    have hJM : F12.jOf D.T ≤ D.M := (uc22p22e_jOf_le_self D.T).trans D.sylowM.le
    have hLA : ∀ x ∈ L, ∀ a ∈ F12.jOf D.T, ⁅x, a⁆ ∈ D.M ⊓ centralizer (V : Set G) := by
      intro x hx a ha
      have hxs : x ∈ stabTil ⊥ V := hMstab (hLM hx)
      have has : a ∈ stabTil ⊥ V := hMstab (hJM ha)
      have h1 : ⁅actTil ⊥ V hVe ⟨a, has⟩, actTil ⊥ V hVe ⟨x, hxs⟩⁆ ∈
          ⁅barSub ⊥ V hVe (F12.jOf D.T), barSub ⊥ V hVe L⁆ :=
        Subgroup.commutator_mem_commutator (actTil_mem_barSub ⊥ V hVe ha has)
          (actTil_mem_barSub ⊥ V hVe hx hxs)
      rw [hJL', Subgroup.mem_bot, ← map_commutatorElement, actTil_eq_one_iff] at h1
      have h2 : ⁅a, x⁆ ∈ centralizer (V : Set G) := TwelveTwentySix.mem_centralizer_of_bot h1
      refine ⟨D.M.mul_mem (D.M.mul_mem (D.M.mul_mem (hLM hx) (hJM ha)) (D.M.inv_mem (hLM hx)))
        (D.M.inv_mem (hJM ha)), ?_⟩
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ h2
    have hres := TwelveTwentyFive.commutator_mem_pCoreOf hL inf_le_left hKn hPK hLK hJM hLA
    rw [Subgroup.commutator_le]
    intro a ha x hx
    rw [TwelveTwentyFive.pCoreOf_eq hL, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (hres x hx a ha)
  · left
    have hYM : barSub V₀ V h.isElemAbelian (UC22.conjClosure D.M L) ≤
        Mbar D.M V₀ V h.isElemAbelian :=
      barSub_mono V₀ V h.isElemAbelian (TwelveTwentyThree.conjClosure_le hLM)
    refine s15_Kbar_fixV_eq_bot_of_ne_bot h hV₀ hYM ?_ hH
    rw [Subgroup.normal_subgroupOf_iff hYM]
    intro y m hy hm
    exact TwelveEighteen.conj_mem_barSub h.isElemAbelian
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L) m hm y hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
