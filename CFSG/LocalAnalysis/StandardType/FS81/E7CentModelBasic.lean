module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogL3
public import CFSG.RankThree.PartOne.S11c.EvenRootInverters
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
public import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.RankThree.Chevalley.SteinbergCFOddE6E7RootInverters
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
open CFSG.StandardType.TableBExcTwoTB
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement


theorem e7CentModelQ_holds :
    E7CentModelQ := by
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hnode : iθ .E7 = highNode .E7 := rfl
  refine ⟨?_, ?_, isTwoRadicalDecomp_highRoot (τ := .E7) (Or.inr (Or.inl rfl))
    (c := (1 : ZMod 2)) one_ne_zero⟩
  · have hθ : highRoot .E7 ∈ parabolicRadicalRoots .E7 (perpNodes .E7) :=
      (mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).2
        ⟨isRoot_highRoot _, iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
    exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hθ 1)
  · intro q₁ hq₁ q₂ hq₂
    set a : ModGL .E7 (ZMod 2) := (q₁ : ModGL .E7 (ZMod 2)) with ha_def
    set b : ModGL .E7 (ZMod 2) := (q₂ : ModGL .E7 (ZMod 2)) with hb_def
    have ha : a ∈ Qθ .E7 (ZMod 2) := HeisIrr.mem_Qθ_of_mem_highRadical hnode hq₁
    have hb : b ∈ Qθ .E7 (ZMod 2) := HeisIrr.mem_Qθ_of_mem_highRadical hnode hq₂
    have hq : ⁅q₁, q₂⁆ ∈ highRadical .E7 (ZMod 2) := by
      simpa only [commutatorElement_def] using
        mul_mem (mul_mem (mul_mem hq₁ hq₂) (inv_mem hq₁)) (inv_mem hq₂)
    have hcomm_coe : ((⁅q₁, q₂⁆ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
        ⁅a, b⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, ha_def, hb_def]
    have hc : heisCoord .E7 (ZMod 2)
        (((⁅q₁, q₂⁆ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2))) = 0 := by
      rw [hcomm_coe, commutatorElement_def]
      have hspec := heisCoord_spec .E7 (ZMod 2)
      calc heisCoord .E7 (ZMod 2) (a * b * a⁻¹ * b⁻¹)
          = heisCoord .E7 (ZMod 2) ((a * b) * (a⁻¹ * b⁻¹)) := by rw [mul_assoc, mul_assoc]
        _ = heisCoord .E7 (ZMod 2) (a * b) + heisCoord .E7 (ZMod 2) (a⁻¹ * b⁻¹) :=
              hspec.mul _ (mul_mem ha hb) _ (mul_mem (inv_mem ha) (inv_mem hb))
        _ = 0 := by
              rw [hspec.mul a ha b hb, hspec.mul a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb),
                heisCoord_inv ha, heisCoord_inv hb]
              abel
    simpa [e7HighInv] using HeisIrr.mem_zpowers_of_heisCoord_eq_zero hnode hK hq hc

@[expose] noncomputable def e7CentBstar
    (α : Fin (Tag.rank .E7) → ℤ) (hα : IsRoot .E7 α) :
    ↥(adjointGroup .E7 (ZMod 2)) :=
  ⟨rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1), by
    have hmem : rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1) ∈
        (rootSL2 .E7 (ZMod 2) α).range := ⟨uSL 1 * vSL 1, rfl⟩
    rw [range_rootSL2_of_isRoot hα] at hmem
    exact (sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)) hmem⟩

theorem e7CentBstar_coe
    {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) :
    (e7CentBstar α hα : ModGL .E7 (ZMod 2)) =
      rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1) := rfl

theorem e7CentBstar_orderOf
    {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) :
    orderOf (e7CentBstar α hα) = 3 := by
  rw [← Subgroup.orderOf_coe, e7CentBstar_coe]
  rw [orderOf_injective _ (rootSL2_injective_of_field (K := ZMod 2) α)]
  exact orderOf_eq_prime uSL_mul_vSL_pow_three uSL_mul_vSL_ne_one

private theorem e7CentBstar_conj_self
    {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) :
    pinnedX .E7 (ZMod 2) α 1 * rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1) *
        (pinnedX .E7 (ZMod 2) α 1)⁻¹ =
      (rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1))⁻¹ := by
  rw [← rootSL2_uSL_of_charTwo (K := ZMod 2) hα 1, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv]
  rw [uSL_conj_uSL_mul_vSL]

private theorem e7CentRootRankOne_classify
    {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α)
    {x : ModGL .E7 (ZMod 2)} (hx : x ∈ rootRankOneGroup .E7 (ZMod 2) α)
    (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    x = rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1) ∨
      x = (rootSL2 .E7 (ZMod 2) α (uSL 1 * vSL 1))⁻¹ := by
  simpa only [map_inv] using
    rootSL2_eq_of_order_three .E7 (ZMod 2) (Nat.card_zmod 2) hα hx h3 h1

theorem e7CentRootSL2_conj
    {a b : Fin (Tag.rank .E7) → ℤ} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) {n : ModGL .E7 (ZMod 2)} (hn : n ∈ adjointGroup .E7 (ZMod 2))
    (hmap : (rootRankOneGroup .E7 (ZMod 2) a).map (MulAut.conj n).toMonoidHom =
      rootRankOneGroup .E7 (ZMod 2) b) :
    ∃ g ∈ adjointGroup .E7 (ZMod 2),
      g * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * g⁻¹ =
        rootSL2 .E7 (ZMod 2) b (uSL 1 * vSL 1) := by
  have hmem : n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * n⁻¹ ∈
      rootRankOneGroup .E7 (ZMod 2) b := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom
      (show rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) ∈
        rootRankOneGroup .E7 (ZMod 2) a from ⟨uSL 1 * vSL 1, rfl⟩)
    rw [hmap] at h
    simpa [MulAut.conj_apply] using h
  have h3 : (n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * n⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ← map_pow, uSL_mul_vSL_pow_three, map_one, mul_one, mul_inv_cancel]
  have horder : orderOf (rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1)) = 3 := by
    rw [orderOf_injective _ (rootSL2_injective_of_field (K := ZMod 2) a)]
    exact orderOf_eq_prime uSL_mul_vSL_pow_three uSL_mul_vSL_ne_one
  have hx1 : rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    norm_num at horder
  have h1 : n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * n⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have h' := congrArg (fun y => n⁻¹ * y * n) h
    rwa [show n⁻¹ * (n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * n⁻¹) * n =
      rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) by group,
      show n⁻¹ * (1 : ModGL .E7 (ZMod 2)) * n = 1 by group] at h'
  obtain h | h := e7CentRootRankOne_classify hb hmem h3 h1
  · exact ⟨n, hn, h⟩
  · refine ⟨pinnedX .E7 (ZMod 2) b 1 * n,
      mul_mem (pinnedX_mem_adjointGroup _ _) hn, ?_⟩
    have hx := e7CentBstar_conj_self hb
    calc pinnedX .E7 (ZMod 2) b 1 * n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) *
          (pinnedX .E7 (ZMod 2) b 1 * n)⁻¹
        = pinnedX .E7 (ZMod 2) b 1 *
            (n * rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) * n⁻¹) *
            (pinnedX .E7 (ZMod 2) b 1)⁻¹ := by group
      _ = pinnedX .E7 (ZMod 2) b 1 *
            (rootSL2 .E7 (ZMod 2) b (uSL 1 * vSL 1))⁻¹ *
            (pinnedX .E7 (ZMod 2) b 1)⁻¹ := by rw [h]
      _ = rootSL2 .E7 (ZMod 2) b (uSL 1 * vSL 1) := by
            rw [show pinnedX .E7 (ZMod 2) b 1 *
              (rootSL2 .E7 (ZMod 2) b (uSL 1 * vSL 1))⁻¹ *
              (pinnedX .E7 (ZMod 2) b 1)⁻¹ =
              (pinnedX .E7 (ZMod 2) b 1 * rootSL2 .E7 (ZMod 2) b (uSL 1 * vSL 1) *
                (pinnedX .E7 (ZMod 2) b 1)⁻¹)⁻¹ by group, hx, inv_inv]

theorem e7CentB_eq_bstar
    (hα : IsRoot .E7 e7Alpha7) :
    e7CentB = e7CentBstar e7Alpha7 hα := by
  apply Subtype.ext
  change evenH .E7 (ZMod 2) e7Alpha7 =
    rootSL2 .E7 (ZMod 2) e7Alpha7 (uSL 1 * vSL 1)
  exact evenH_eq_rootSL2 (τ := .E7) (K := ZMod 2) (α := e7Alpha7) hα

private theorem e7CentRootSubgroup_le_closure  (γ : Fin (Tag.rank .E7) → ℤ) :
    (rootSubgroup .E7 (ZMod 2) γ).subgroupOf (adjointGroup .E7 (ZMod 2)) ≤
      Subgroup.closure ({⟨pinnedX .E7 (ZMod 2) γ 1, pinnedX_mem_adjointGroup γ 1⟩} :
        Set (adjointGroup .E7 (ZMod 2))) := by
  intro x hx
  have hx' : (x : ModGL .E7 (ZMod 2)) ∈ rootSubgroup .E7 (ZMod 2) γ :=
    Subgroup.mem_subgroupOf.1 hx
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hx'
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [pinnedX_zero] at hc
    have hx1 : x = 1 := Subtype.ext hc.symm
    rw [hx1]
    exact Subgroup.one_mem _
  · refine Subgroup.subset_closure ?_
    rw [Set.mem_singleton_iff]
    exact Subtype.ext hc.symm


private theorem e7CentOrderThree_conj
    {a : Fin (Tag.rank .E7) → ℤ} (ha : IsRoot .E7 a)
    {n : ModGL .E7 (ZMod 2)} (hn : n ∈ adjointGroup .E7 (ZMod 2))
    (hmap : (rootRankOneGroup .E7 (ZMod 2) a).map (MulAut.conj n).toMonoidHom =
      rootRankOneGroup .E7 (ZMod 2) (highRoot .E7))
    {r : ModGL .E7 (ZMod 2)} (hr : r ∈ rootRankOneGroup .E7 (ZMod 2) (highRoot .E7))
    (h3 : r ^ 3 = 1) (h1 : r ≠ 1) :
    ∃ g ∈ adjointGroup .E7 (ZMod 2), g * r * g⁻¹ =
      rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) := by
  obtain ⟨g₀, hg₀, hconj₀⟩ :=
    e7CentRootSL2_conj ha (isRoot_highRoot (τ := .E7)) hn hmap
  obtain h | h := e7CentRootRankOne_classify (isRoot_highRoot (τ := .E7)) hr h3 h1
  · refine ⟨g₀⁻¹, inv_mem hg₀, ?_⟩
    rw [h, ← hconj₀]
    group
  · refine ⟨(pinnedX .E7 (ZMod 2) (highRoot .E7) 1 * g₀)⁻¹,
      inv_mem (mul_mem (pinnedX_mem_adjointGroup _ _) hg₀), ?_⟩
    have hx := e7CentBstar_conj_self (isRoot_highRoot (τ := .E7))
    have hxr : (pinnedX .E7 (ZMod 2) (highRoot .E7) 1)⁻¹ * r *
        pinnedX .E7 (ZMod 2) (highRoot .E7) 1 =
        rootSL2 .E7 (ZMod 2) (highRoot .E7) (uSL 1 * vSL 1) := by
      rw [h, ← hx]
      group
    calc (pinnedX .E7 (ZMod 2) (highRoot .E7) 1 * g₀)⁻¹ * r *
          (pinnedX .E7 (ZMod 2) (highRoot .E7) 1 * g₀)
        = g₀⁻¹ * ((pinnedX .E7 (ZMod 2) (highRoot .E7) 1)⁻¹ * r *
            pinnedX .E7 (ZMod 2) (highRoot .E7) 1) * g₀ := by group
      _ = g₀⁻¹ * rootSL2 .E7 (ZMod 2) (highRoot .E7) (uSL 1 * vSL 1) * g₀ := by
            rw [hxr]
      _ = rootSL2 .E7 (ZMod 2) a (uSL 1 * vSL 1) := by rw [← hconj₀]; group

private theorem e7Cent_isRoot_alpha7 : IsRoot .E7 e7Alpha7 :=
  isRoot_single .E7 (⟨6, by decide⟩ : Fin (Tag.rank .E7))

private theorem e7CentB_mem_e7A1  :
    e7CentB ∈ e7A1 := by
  refine Subgroup.mem_subgroupOf.2 ?_
  simpa [e7CentB, pinnedElt] using
    (Subgroup.mul_mem_sup
      (mem_rootSubgroup.2 ⟨1, rfl⟩ : pinnedX .E7 (ZMod 2) e7Alpha7 1 ∈
        rootSubgroup .E7 (ZMod 2) e7Alpha7)
      (mem_rootSubgroup.2 ⟨1, rfl⟩ : pinnedX .E7 (ZMod 2) (-e7Alpha7) 1 ∈
        rootSubgroup .E7 (ZMod 2) (-e7Alpha7)))

private theorem e7CentInvol_mem_e7A1  :
    e7CentInvol ∈ e7A1 := by
  refine Subgroup.mem_subgroupOf.2 ?_
  simpa [e7CentInvol, pinnedElt] using
    (Subgroup.mem_sup_left
      (mem_rootSubgroup.2 ⟨1, rfl⟩ : pinnedX .E7 (ZMod 2) e7Alpha7 1 ∈
        rootSubgroup .E7 (ZMod 2) e7Alpha7))

private theorem e7Cent_orderOf_B  :
    orderOf e7CentB = 3 := by
  rw [e7CentB_eq_bstar e7Cent_isRoot_alpha7]
  exact e7CentBstar_orderOf e7Cent_isRoot_alpha7

private theorem e7Cent_orderOf_invol  :
    orderOf e7CentInvol = 2 := by
  rw [← Subgroup.orderOf_coe]
  simpa [e7CentInvol, pinnedElt] using
    orderOf_pinnedX_one_charTwo (K := ZMod 2) (α := e7Alpha7)

private theorem e7Cent_invol_conj_B  :
    e7CentInvol * e7CentB * e7CentInvol⁻¹ = e7CentB⁻¹ := by
  rw [e7CentB_eq_bstar e7Cent_isRoot_alpha7]
  apply Subtype.ext
  simpa [e7CentInvol, e7CentBstar, pinnedElt, Subgroup.coe_mul, Subgroup.coe_inv]
    using e7CentBstar_conj_self e7Cent_isRoot_alpha7

private theorem e7CentA1_le_closure  :
    e7A1 ≤ Subgroup.closure ({e7CentB, e7CentInvol} :
      Set ↥(adjointGroup .E7 (ZMod 2))) := by
  let C : Subgroup ↥(adjointGroup .E7 (ZMod 2)) :=
    Subgroup.closure ({e7CentB, e7CentInvol} : Set ↥(adjointGroup .E7 (ZMod 2)))
  have hk : e7CentInvol ∈ C := by
    have hm : e7CentInvol ∈ ({e7CentB, e7CentInvol} :
        Set ↥(adjointGroup .E7 (ZMod 2))) := by
      rw [Set.mem_insert_iff]; right; rfl
    exact Subgroup.subset_closure hm
  have hb : e7CentB ∈ C := by
    have hm : e7CentB ∈ ({e7CentB, e7CentInvol} :
        Set ↥(adjointGroup .E7 (ZMod 2))) := by
      rw [Set.mem_insert_iff]; left; rfl
    exact Subgroup.subset_closure hm
  have hαle : (rootSubgroup .E7 (ZMod 2) e7Alpha7).subgroupOf
      (adjointGroup .E7 (ZMod 2)) ≤ C := by
    refine (e7CentRootSubgroup_le_closure e7Alpha7).trans (Subgroup.closure_mono ?_)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [Set.mem_insert_iff]
    right
    exact Subtype.ext rfl
  have hnegle : (rootSubgroup .E7 (ZMod 2) (-e7Alpha7)).subgroupOf
      (adjointGroup .E7 (ZMod 2)) ≤ C := by
    refine (e7CentRootSubgroup_le_closure (-e7Alpha7)).trans ?_
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hkk : pinnedX .E7 (ZMod 2) e7Alpha7 1 * pinnedX .E7 (ZMod 2) e7Alpha7 1 = 1 := by
      rw [← pinnedX_add, show (1 : ZMod 2) + 1 = 0 by decide, pinnedX_zero]
    have hkb : (⟨pinnedX .E7 (ZMod 2) (-e7Alpha7) 1, pinnedX_mem_adjointGroup _ _⟩ :
        ↥(adjointGroup .E7 (ZMod 2))) = e7CentInvol * e7CentB := by
      apply Subtype.ext
      change pinnedX .E7 (ZMod 2) (-e7Alpha7) 1 =
        pinnedX .E7 (ZMod 2) e7Alpha7 1 *
          (pinnedX .E7 (ZMod 2) e7Alpha7 1 * pinnedX .E7 (ZMod 2) (-e7Alpha7) 1)
      rw [← mul_assoc, hkk, one_mul]
    rw [hkb]
    exact C.mul_mem hk hb
  rw [e7A1, Subgroup.subgroupOf_sup
    (rootSubgroup_le_adjointGroup (α := e7Alpha7))
    (rootSubgroup_le_adjointGroup (α := -e7Alpha7))]
  exact sup_le hαle hnegle

private theorem e7CentJTheta_conj  :
    ∀ r ∈ e7JTheta, orderOf r = 3 →
      ∃ g : ↥(adjointGroup .E7 (ZMod 2)), g * r * g⁻¹ = e7CentB := by
  intro r hr h3
  have hα := e7Cent_isRoot_alpha7
  have hJeq : e7JTheta =
      (rootRankOneGroup .E7 (ZMod 2) (highRoot .E7)).subgroupOf
        (adjointGroup .E7 (ZMod 2)) := by
    rw [e7JTheta, CFSG.ClassicalInvolution.ModelFacts.rootRankOneGroup_eq_sup
      (isRoot_highRoot (τ := .E7))]
    rfl
  have hmem : (r : ModGL .E7 (ZMod 2)) ∈
      rootRankOneGroup .E7 (ZMod 2) (highRoot .E7) := by
    rw [hJeq] at hr
    exact Subgroup.mem_subgroupOf.1 hr
  have h3r : r ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one r
  have hcoe3 : ((r : ModGL .E7 (ZMod 2)) ^ 3 = 1) := by
    rw [← Subgroup.coe_pow, h3r, Subgroup.coe_one]
  have h1 : (r : ModGL .E7 (ZMod 2)) ≠ 1 := by
    intro h
    have hr1 : r = 1 := Subtype.ext h
    rw [hr1, orderOf_one] at h3
    norm_num at h3
  obtain ⟨n, hn, hmap⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.E7Model.exists_conj_rankOne_to_theta
      (F := ZMod 2) (β := e7Alpha7) hα
  have htheta : CFSG.ClassicalInvolution.ModelFacts.Levi.thetaE7 = highRoot .E7 := by
    rw [CFSG.ClassicalInvolution.ModelFacts.E7Model.thetaE7_eq]
    rfl
  have hmap' : (rootRankOneGroup .E7 (ZMod 2) e7Alpha7).map
      (MulAut.conj n).toMonoidHom = rootRankOneGroup .E7 (ZMod 2) (highRoot .E7) := by
    rw [← htheta, ← hmap]
  obtain ⟨g, hg, hconj⟩ := e7CentOrderThree_conj hα hn hmap' hmem hcoe3 h1
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [e7CentB_eq_bstar hα]
  apply Subtype.ext
  simpa [e7CentBstar, Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem e7CentModelK_holds :
    E7CentModelK :=
  ⟨e7CentB_mem_e7A1, e7CentInvol_mem_e7A1, e7Cent_orderOf_B, e7Cent_orderOf_invol,
    e7Cent_invol_conj_B, e7CentA1_le_closure, e7CentJTheta_conj⟩

end CFSG.StandardType.FrameRoute.FS81
