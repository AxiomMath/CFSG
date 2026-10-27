module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteFX
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Alpha
import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c11_barSub_inf_cClos_le_centSub (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) (h169 : Concl169 D V₀ V) :
    barSub V₀ V hV (D.M ⊓ centralizer (E3.cClos V D.k D.T : Set G)) ≤
      centSub (fixV (barSub V₀ V hV D.T)) := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV _ φ).1 hφ
  obtain ⟨hgM, hgc⟩ := Subgroup.mem_inf.1 hg
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hTst : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMst
  have hVleT : V ≤ D.T := uc22p22na_le_T_of_inCalV D h.inCalV
  rw [mem_centSub]
  intro u hu
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV u
  have hcent : x.val ∈ centralizer (E3.wClos V D.k D.T : Set G) :=
    h169.1.2 x.val x.val_mem fun w hw => by
      have hwT : w ∈ D.T := E3.wClos_le D.k D.T hw
      have hwst : w ∈ stabTil V₀ V := hTst hwT
      have hfix := (mem_fixV.1 hu) (actTil V₀ V hV ⟨w, hwst⟩)
        (actTil_mem_barSub V₀ V hV hwT hwst)
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfix
      rw [commutatorElement_def]
      have h1 : x.val * w * x.val⁻¹ * w⁻¹ = (w * x.val * w⁻¹ * x.val⁻¹)⁻¹ := by group
      rw [h1]
      exact V₀.inv_mem hfix
  have hvcl : x.val ∈ E3.cClos V D.k D.T := by
    rw [E3.cClos]
    exact Subgroup.mem_inf.2 ⟨hVleT x.val_mem, hcent⟩
  have hcomm : x.val * (g : G) = (g : G) * x.val :=
    Subgroup.mem_centralizer_iff.1 hgc x.val hvcl
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  have h1 : (g : G) * x.val * (g : G)⁻¹ * x.val⁻¹ = 1 := by
    rw [← hcomm]; group
  rw [h1]
  exact V₀.one_mem

theorem s16c11_barSub_factor_of_compFactor (D : Data G) (h1610 : R16_10_2 D) (h169 : R16_9 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV)
    {X : Subgroup G} (hXM : X ≤ D.M) (hTX : D.T ≤ X) (hF : CompFactorAutInF D.k X D.T) :
    (barSub V₀ V hV X : Set (MulAut (Vtil V₀ V hV))) =
      ((barSub V₀ V hV X ⊓ centSub (fixV (barSub V₀ V hV D.T)) : Subgroup _) : Set _) *
        ((barSub V₀ V hV X ⊓ normalizer
          ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) : Subgroup _) : Set _) := by
  have h : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hP := h.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hTst : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMst
  have h169' : Concl169 D V₀ V := h169 V₀ V L hV hc
  have hCT : CFSG.QuasithinUnique.CharTwo X := s16c11_charTwo_of_sylow_le D hXM hTX
  have hS : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D hTX
  have hfac := h1610 V₀ V L hV hc X D.T hXM hCT hS hF
  have hB : E3.wClos V 0 D.T ≤ stabTil V₀ V := (E3.wClos_le 0 D.T).trans hTst
  have hnorm := close16_barSub_le_normalizer (V₀ := V₀) (V := V) (hV := hV)
    (X := X ⊓ normalizer (E3.wClos V 0 D.T : Set G)) (B := E3.wClos V 0 D.T) hB inf_le_right
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨x, hxX, rfl⟩ := (mem_barSub V₀ V hV X φ).1 hφ
    have hxX' : (x : G) ∈ (X : Set G) := hxX
    rw [hfac] at hxX'
    obtain ⟨c, hcC, n, hnN, hcn⟩ := Set.mem_mul.1 hxX'
    have hcX : c ∈ X := hcC.1
    have hccent : c ∈ centralizer (E3.cClos V D.k D.T : Set G) := hcC.2
    have hnX : n ∈ X := hnN.1
    have hnNw : n ∈ normalizer (E3.wClos V 0 D.T : Set G) := hnN.2
    have hcst : c ∈ stabTil V₀ V := hMst (hXM hcX)
    have hnst : n ∈ stabTil V₀ V := hMst (hXM hnX)
    have hxcn : (⟨c, hcst⟩ : stabTil V₀ V) * ⟨n, hnst⟩ = x := Subtype.ext hcn
    have hcM : c ∈ D.M ⊓ centralizer (E3.cClos V D.k D.T : Set G) :=
      Subgroup.mem_inf.2 ⟨hXM hcX, hccent⟩
    have hnC : n ∈ X ⊓ normalizer (E3.wClos V 0 D.T : Set G) :=
      Subgroup.mem_inf.2 ⟨hnX, hnNw⟩
    refine Set.mem_mul.2 ⟨actTil V₀ V hV ⟨c, hcst⟩,
      ⟨actTil_mem_barSub V₀ V hV hcX hcst,
        s16c11_barSub_inf_cClos_le_centSub D hV h h169'
          (actTil_mem_barSub V₀ V hV hcM hcst)⟩,
      actTil V₀ V hV ⟨n, hnst⟩,
      ⟨actTil_mem_barSub V₀ V hV hnX hnst, hnorm (actTil_mem_barSub V₀ V hV hnC hnst)⟩, ?_⟩
    rw [← map_mul, hxcn]
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hz
    exact (barSub V₀ V hV X).mul_mem ha.1 hb.1

theorem s16c11_barSub_factor_of_routeF (D : Data G) (h1610 : R16_10_2 D) (h169 : R16_9 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV)
    {Xbar : Subgroup (MulAut (Vtil V₀ V hV))} (hXM : Xbar ≤ Mbar D.M V₀ V hV)
    (hTX : barSub V₀ V hV D.T ≤ Xbar) (hsolv : Group.IsSolvable ↥Xbar) :
    (Xbar : Set (MulAut (Vtil V₀ V hV))) =
      ((Xbar ⊓ centSub (fixV (barSub V₀ V hV D.T)) : Subgroup _) : Set _) *
        ((Xbar ⊓ normalizer
          ((barSub V₀ V hV (E3.wClos V 0 D.T) : Subgroup _) : Set _) : Subgroup _) : Set _) := by
  have h : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨X, hXM', hTX', hbar, hXsolv⟩ :=
    s16c11_exists_preimage_of_solvable D hV h hXM hTX hsolv
  have hF : CompFactorAutInF D.k X D.T := s16c11_compFactorAutInF_of_isSolvable D.k hXsolv
  have hfac := s16c11_barSub_factor_of_compFactor D h1610 h169 hV hc hXM' hTX' hF
  rw [hbar] at hfac
  exact hfac

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
