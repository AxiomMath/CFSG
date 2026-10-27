module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2SpPlacementHolds
public import CFSG.LocalAnalysis.StandardType.GGQ2LinPlacementHolds
import CFSG.LocalAnalysis.StandardType.GGQ2AutomizerCover
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksMark
import CFSG.LocalAnalysis.StandardType.GGQ2LinEleH
import CFSG.LocalAnalysis.StandardType.GGQ2LinFrame
import CFSG.LocalAnalysis.StandardType.GGQ2LinFrameCard
import CFSG.LocalAnalysis.StandardType.GGQ2LinInnerDiagData
import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutAmb

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame
  CFSG.StandardType.GGQ2Frame.SpPlacement CFSG.StandardType.GGQ2Frame.SpBlocks
open CFSG.StandardType.GGQ2Frame.LinPlacement CFSG.StandardType.GGQ2Frame.LinBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem eq_zero_erase_of_occurs_span_singleton {r : ℕ} {u : PlaneRaw.V r} {i₁ : Fin r}
    (hu : ∀ i, i ≠ i₁ → u i = 0) (hu0 : u ≠ 0) {c : PlaneRaw.Code r}
    (hext : ∀ e : PlaneRaw.V r, c = .extension e → 1 < (PlaneRaw.Code.extSupport e).card)
    (hocc : PlaneRaw.occurs (Submodule.span PlaneRaw.F ({u} : Set (PlaneRaw.V r))) c) :
    c = .zero (Finset.univ.erase i₁) := by
  classical
  have hu_mem : u ∈ Submodule.span PlaneRaw.F ({u} : Set (PlaneRaw.V r)) :=
    Submodule.subset_span (Set.mem_singleton u)
  have hu_i₁ : u i₁ ≠ 0 := by
    intro h
    apply hu0
    funext i
    by_cases hi : i = i₁
    · simpa [hi] using h
    · exact hu i hi
  have hzero : ∀ i, i ≠ i₁ → ∀ w ∈ Submodule.span PlaneRaw.F ({u} : Set (PlaneRaw.V r)),
      w i = 0 := by
    intro i hi w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hu i hi]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => simp [hx]
  cases c with
  | extension e =>
      exfalso
      obtain ⟨-, χ, hχ, hev, -⟩ := hocc
      have hsub : PlaneRaw.Code.extSupport e ⊆ ({i₁} : Finset (Fin r)) := by
        intro i hi
        rw [Finset.mem_singleton]
        by_contra hne
        have h1 := hev i ((PlaneRaw.mem_extSupport e i).1 hi)
        have h2 : PlaneRaw.evalRestr
            (Submodule.span PlaneRaw.F ({u} : Set (PlaneRaw.V r))) i = 0 := by
          ext w
          exact hzero i hne (w : PlaneRaw.V r) w.2
        rw [h2] at h1
        exact (smul_ne_zero ((PlaneRaw.mem_extSupport e i).1 hi) hχ) h1.symm
      have hcard : (PlaneRaw.Code.extSupport e).card ≤ 1 := by
        calc (PlaneRaw.Code.extSupport e).card ≤ ({i₁} : Finset (Fin r)).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton i₁
      have := hext e rfl
      omega
  | zero S =>
      have hS : S = Finset.univ.erase i₁ := by
        ext i
        rw [hocc i]
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro h
          by_contra hi
          exact hu_i₁ (hi ▸ h ⟨u, hu_mem⟩)
        · intro hi w
          exact hzero i hi (w : PlaneRaw.V r) w.2
      rw [hS]

theorem exists_negEquiv_or_rotEquiv_mem_normalizerOf_symplectic {r : ℕ} (hr : 3 ≤ r)
    {u : PlaneRaw.V r} {i₁ : Fin r} (hu : ∀ i, i ≠ i₁ → u i = 0) (hu0 : u ≠ 0)
    {c : PlaneRaw.Code r} (hc : PlaneRaw.admissible .symplectic c)
    (hocc : PlaneRaw.occurs (Submodule.span PlaneRaw.F ({u} : Set (PlaneRaw.V r))) c) :
    (∃ i, PlaneRaw.negEquiv r i ∈ PlaneRaw.normalizerOf .symplectic r c) ∨
      ∃ i j, i ≠ j ∧ PlaneRaw.rotEquiv r i j ∈ PlaneRaw.normalizerOf .symplectic r c := by
  classical
  have hext : ∀ e : PlaneRaw.V r, c = .extension e → 1 < (PlaneRaw.Code.extSupport e).card := by
    intro e rfl
    have h := hc.2
    omega
  have hc0 : c = .zero (Finset.univ.erase i₁) :=
    eq_zero_erase_of_occurs_span_singleton hu hu0 hext hocc
  rw [hc0]
  set S : Finset (Fin r) := Finset.univ.erase i₁ with hS
  have hScard : S.card = r - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ, Fintype.card_fin]
  by_cases hS2 : S.card = 2
  · have h1 : 1 < S.card := by omega
    have hex : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
      exact ⟨a, b, ha, hb, hab⟩
    refine Or.inr ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.2.2, ?_⟩
    change PlaneRaw.rotEquiv r hex.choose hex.choose_spec.choose ∈
      (if S.card = 2 then
        Subgroup.zpowers (if h : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j then
          PlaneRaw.rotEquiv r h.choose h.choose_spec.choose else 1)
      else PlaneRaw.signedPermGroupOn r S)
    rw [if_pos hS2, dif_pos hex]
    exact Subgroup.mem_zpowers _
  · have hpos : 0 < S.card := by rw [hScard]; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    refine Or.inl ⟨i, ?_⟩
    change PlaneRaw.negEquiv r i ∈
      (if S.card = 2 then
        Subgroup.zpowers (if h : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j then
          PlaneRaw.rotEquiv r h.choose h.choose_spec.choose else 1)
      else PlaneRaw.signedPermGroupOn r S)
    rw [if_neg hS2]
    exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

private theorem lin_exists_exact_label {K₀ : Type} [Group K₀] {E : Subgroup K₀}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ lab.tag = .A) 3 E ⊤) :
    ∃ r : ℕ, GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 E ⊤ := by
  obtain ⟨hperf, lab, hlabΛ, hraw⟩ := hInn
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨R, _instR, I, F, _hs, _hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨⟨hnlt2, htagA⟩, _hN, _hI⟩ := hP
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := by simpa using hlabΛ.1
    have h2 : n < 2 := by simpa using hnlt2
    omega
  subst htagA
  subst hn1
  refine ⟨rank, hperf, ⟨.A, rank, 1⟩, hlabΛ, ?_⟩
  refine largeEvenRawDatum_mono (lab := ⟨.A, rank, 1⟩) ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ', ⟨-, hN', hI'⟩⟩
  exact ⟨hs, hna, θ', ⟨rfl, hN', hI'⟩⟩


theorem ggQTwoClFrameIn_of_lin {K₀ : Type} [Group K₀] [Finite K₀] {E : Subgroup K₀}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ lab.tag = .A) 3 E ⊤)
    (hEab : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set K₀), g ^ 3 = 1 → g ∈ E)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center K₀)) (hcard : 3 ^ 3 ≤ Nat.card E) :
    ∃ t, 3 ≤ t ∧ GGQTwoClFrameIn E t := by
  classical
  have hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((⊤ : Subgroup K₀) : Set K₀)) := by
    rwa [Subgroup.coe_top, Subgroup.centralizer_univ]
  obtain ⟨r, hInnA⟩ := lin_exists_exact_label hInn
  obtain ⟨t, ε, hrt⟩ := exists_planes r
  obtain ⟨K, _instK, _instFin, _instChar, ζ, hEN, ⟨ctx⟩⟩ :=
    linCtx_of_pieces linInnerDiagData_holds
      (existsLinFrame_of_cardEEq linCardEEq_holds) linEleH_holds hrt hInnA hEab hSC hC3 hcard
  have hN := linNormalizerEqs_of_pieces CoverComponents.automizerCoverEq_holds
    linAmbientTorusAut_holds linComponentTorusAut_holds linIsQuasisimpleYcode_holds ctx
  refine ⟨t, ctx.ht, ctx.fr.coord, ?_, ?_⟩
  · simpa only [PlaneRaw.ambientNormalizer] using hN.2
  · intro v i₁ hv hsupp X hX
    let w : PlaneRaw.V t := ctx.fr.coord (Additive.ofMul v)
    have hw : w ≠ 0 := by
      intro h0
      have h1 : v = 1 := by
        apply Additive.ofMul.injective
        apply ctx.fr.coord.injective
        simpa [w] using h0
      exact hv h1
    have hspan : ggLinImage (p := 3) ctx.fr.coord (Subgroup.zpowers (v : K₀)) =
        Submodule.span (ZMod 3) {w} := by
      rw [← span_singleton_eq_ggLinImage (p := 3) ctx.fr.coord (x := (v : K₀)) v.2]
    have hcz : Subgroup.centralizer ((Subgroup.zpowers (v : K₀) : Subgroup K₀) : Set K₀) =
        Subgroup.centralizer ({(v : K₀)} : Set K₀) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hX' : IsComponentOf X
        (⊤ ⊓ Subgroup.centralizer ((Subgroup.zpowers (v : K₀) : Subgroup K₀) : Set K₀)) := by
      rwa [top_inf_eq, hcz]
    obtain ⟨c, hc, hocc, hXc⟩ :=
      (linComponentOccursIff_holds ctx (Subgroup.zpowers (v : K₀))
        (Subgroup.zpowers_le.mpr v.2) X).mp hX'
    have hocc_std : PlaneRaw.occurs
        (ggLinImage (p := 3) ctx.fr.coord (Subgroup.zpowers (v : K₀))) c := hocc
    have hocc' : PlaneRaw.occurs (Submodule.span (ZMod 3) {w}) c := by
      simpa [hspan] using hocc_std
    have hc0 : c = .zero (Finset.univ.erase i₁) :=
      eq_zero_erase_of_occurs_span_singleton hsupp hw
        (fun e he => by subst he; have h := hc.2; omega) hocc'
    have hSpos : 0 < (Finset.univ.erase i₁ : Finset (Fin t)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i₁), Finset.card_univ, Fintype.card_fin]
      exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by norm_num : 1 < 3) ctx.ht)
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hSpos
    refine Or.inl ⟨i, ?_⟩
    rw [hXc, hN.1 c hc, hc0]
    exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)


theorem ggQTwoClFrameIn_of_sp {K₀ : Type} [Group K₀] [Finite K₀] {E : Subgroup K₀}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C)) 3 E ⊤)
    (hEab : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set K₀), g ^ 3 = 1 → g ∈ E)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center K₀)) (hcard : 3 ^ 3 ≤ Nat.card E) :
    ∃ t, 3 ≤ t ∧ GGQTwoClFrameIn E t := by
  classical
  obtain ⟨lab, hlab2, hhas, R, _, I, F, θ, hpred⟩ := largeEvenMarking_exists_hasLabel hInn
  obtain ⟨⟨hn2, htag⟩, -⟩ := hpred
  obtain ⟨t, r, n⟩ := lab
  have hn2' : n < 2 := hn2
  have htag' : t = .B ∨ t = .C := htag
  have hn1 : n = 1 := by
    have h1 : 1 ≤ n := hlab2.1
    omega
  obtain rfl : n = 1 := hn1
  have hlabC2 : LargeEvenInLambda2 ⟨.C, r, 1⟩ := inLambda2_C_of_BC htag' hlab2
  have hhasC : GGHasLabel ⟨.C, r, 1⟩
      (↥(⊤ : Subgroup K₀) ⧸ Subgroup.center ↥(⊤ : Subgroup K₀)) :=
    hasLabel_C_of_BC htag' hhas
  have hHmark : GGInnerDiagOn E (⊤ : Subgroup K₀) :=
    largeEvenMarking_mono (fun lab R _ I _ θ hP => ⟨hP.2.1, hP.2.2⟩) hInn
  have hInnC : GGInnerDiagOnLabel (fun _ l => l = planeAmbientLabel .symplectic r) 3 E ⊤ :=
    ggInnerDiagOn_relabel ggLabelRigidInput_holds hHmark hlabC2 hhasC
  have hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ((⊤ : Subgroup K₀) : Set K₀)) := by
    rwa [Subgroup.coe_top, Subgroup.centralizer_univ]
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ :=
    spCtx_of_pieces spInnerDiagData_holds exists_spFrame_holds spEleH_holds hInnC hEab hSC hC3
      hcard
  have hN := spNormalizerEqs_of_pieces CoverComponents.automizerCoverEq_holds
    spAmbientTorusAut_holds (spComponentTorusAut_of_parts spZeroTorusAut_holds spExtTorusAut_holds)
    spIsQuasisimpleYcode_holds ctx
  refine ⟨r, ctx.hm, ctx.fr.coord, ?_, ?_⟩
  · simpa [PlaneRaw.ambientNormalizer] using hN.2
  · intro v i₁ hv hsupp X hX
    have hcent : Subgroup.centralizer ({(v : K₀)} : Set K₀) =
        (⊤ : Subgroup K₀) ⊓ Subgroup.centralizer
          (Subgroup.zpowers (v : K₀) : Set K₀) := by
      rw [top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hX' : IsComponentOf X ((⊤ : Subgroup K₀) ⊓
        Subgroup.centralizer (Subgroup.zpowers (v : K₀) : Set K₀)) := hcent ▸ hX
    have hzle : Subgroup.zpowers (v : K₀) ≤ E := Subgroup.zpowers_le.mpr v.2
    obtain ⟨c, hc, hocc, rfl⟩ :=
      (spComponentOccursIff_holds ctx (Subgroup.zpowers (v : K₀)) hzle X).1 hX'
    rw [hN.1 c hc]
    have hU : ggLinImage (p := 3) ctx.fr.coord (Subgroup.zpowers (v : K₀)) =
        Submodule.span PlaneRaw.F
          ({ctx.fr.coord (Additive.ofMul v)} : Set (PlaneRaw.V r)) :=
      (span_singleton_eq_ggLinImage (p := 3) ctx.fr.coord v.2).symm
    have hocc' : PlaneRaw.occurs (Submodule.span PlaneRaw.F
        ({ctx.fr.coord (Additive.ofMul v)} : Set (PlaneRaw.V r))) c := by
      rw [← hU]
      exact hocc
    have hu0 : ctx.fr.coord (Additive.ofMul v) ≠ 0 := by
      intro h0
      apply hv
      have h1 : Additive.ofMul v = 0 := ctx.fr.coord.injective (by simpa using h0)
      exact Additive.ofMul.injective (by simpa using h1)
    exact exists_negEquiv_or_rotEquiv_mem_normalizerOf_symplectic ctx.hm hsupp hu0 hc hocc'

theorem ggQTwoClFrameIn_of_marking {K₀ : Type} [Group K₀] [Finite K₀] {E : Subgroup K₀}
    (hInn : GGInnerDiagOnLabel (fun _ lab => GGQTwoClLabel lab) 3 E ⊤)
    (hEab : IsElemAbelian 3 E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set K₀), g ^ 3 = 1 → g ∈ E)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center K₀)) (hcard : 3 ^ 3 ≤ Nat.card E) :
    ∃ t, 3 ≤ t ∧ GGQTwoClFrameIn E t := by
  have hInn' : GGInnerDiagOnLabel (fun _ lab => (lab.n < 2 ∧ lab.tag = .A) ∨
      (lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C))) 3 E ⊤ :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨⟨hn, ht⟩, hP⟩ =>
      ⟨ht.imp (fun h => ⟨hn, h⟩) (fun h => ⟨hn, h⟩), hP⟩) hInn
  rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => lab.n < 2 ∧ lab.tag = .A)
      (T := fun _ lab => lab.n < 2 ∧ (lab.tag = .B ∨ lab.tag = .C)) hInn' with h | h
  · exact ggQTwoClFrameIn_of_lin h hEab hSC hZ3 hcard
  · exact ggQTwoClFrameIn_of_sp h hEab hSC hZ3 hcard

end CFSG.StandardType

end
