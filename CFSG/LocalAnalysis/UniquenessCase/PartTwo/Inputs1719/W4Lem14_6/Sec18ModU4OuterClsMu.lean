module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsWedge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusOrbit
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.ElemAbelianMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.Quasithin.H
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open CFSG.SeitzReduction.F4Pilot (omIsoGroup statedOmega_le_omIsoGroup)
open scoped commutatorElement Pointwise Matrix

theorem exists_mem_nextLayer {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) {P : Subgroup W}
    (hP : ∀ a ∈ A, ∀ p ∈ P, a p ∈ P) (hPW : P ≠ ⊤) :
    ∃ w : W, w ∉ P ∧ ∀ a ∈ A, a w * w⁻¹ ∈ P := by
  have hNmap : ∀ a : A, P.map ((a : MulAut W) : W →* W) = P := by
    intro a
    refine le_antisymm ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hP (a : MulAut W) a.2 x hx
    · intro y hy
      refine ⟨((a : MulAut W)⁻¹) y, hP ((a : MulAut W)⁻¹) (A.inv_mem a.2) y hy, ?_⟩
      simp
  have hmul : ∀ a b : A,
      (QuotientGroup.congr P P ((a * b : A) : MulAut W) (hNmap (a * b)) :
          MulAut (W ⧸ P)) =
        (QuotientGroup.congr P P (a : MulAut W) (hNmap a) : MulAut (W ⧸ P)) *
          (QuotientGroup.congr P P (b : MulAut W) (hNmap b) : MulAut (W ⧸ P)) := by
    intro a b
    apply MulEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [MulAut.mul_apply, QuotientGroup.congr_mk, Subgroup.coe_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : A →* MulAut (W ⧸ P), ∀ a : A,
      φ a = QuotientGroup.congr P P (a : MulAut W) (hNmap a) :=
    ⟨MonoidHom.mk' (fun a : A => QuotientGroup.congr P P (a : MulAut W) (hNmap a)) hmul,
      fun a => rfl⟩
  have hWq : ∀ q : W ⧸ P, q ^ 2 = 1 := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW v, QuotientGroup.mk_one]
  have hA' : IsElemAbelian2 φ.range := by
    simpa [MonoidHom.range_eq_map] using
      (CFSG.ASVolI.ChH.isElemAbelian2_map_of_comm_sq φ
        (⊤ : Subgroup A)
        (fun a _ b _ => by
          apply Subtype.ext
          simpa using hA.1 (a : MulAut W) a.2 (b : MulAut W) b.2)
        (fun a _ => by
          apply Subtype.ext
          simpa [pow_two] using hA.2 (a : MulAut W) a.2))
  have hbot : (⊥ : Subgroup (W ⧸ P)) ≠ ⊤ := by
    haveI : Nontrivial (W ⧸ P) := QuotientGroup.nontrivial_iff.mpr hPW
    intro h
    have hsub : Subsingleton (W ⧸ P) := by
      refine ⟨fun x y => ?_⟩
      have hx : x = 1 := by
        have hx' : x ∈ (⊥ : Subgroup (W ⧸ P)) := by
          rw [h]
          exact Subgroup.mem_top x
        simpa using hx'
      have hy : y = 1 := by
        have hy' : y ∈ (⊥ : Subgroup (W ⧸ P)) := by
          rw [h]
          exact Subgroup.mem_top y
        simpa using hy'
      rw [hx, hy]
    obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial (W ⧸ P)).exists_pair_ne
    exact hxy (hsub.elim x y)
  obtain ⟨q, hqP, hqfix⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_mem_secondLayer hWq hA'
      (F := ⊥) bot_le hbot
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective q
  refine ⟨w, ?_, ?_⟩
  · intro hwP
    apply hqP
    rw [← hw, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hwP
  · intro a ha
    have hfix : φ ⟨a, ha⟩ ∈ φ.range := by
      rw [MonoidHom.range_eq_map]
      exact Subgroup.mem_map_of_mem φ (Subgroup.mem_top _)
    have hfix' := hqfix (φ ⟨a, ha⟩) hfix
    rw [Subgroup.mem_bot] at hfix'
    have h1 : φ ⟨a, ha⟩ q = q := (mul_inv_eq_one.mp hfix')
    rw [hφ ⟨a, ha⟩, ← hw, QuotientGroup.congr_mk] at h1
    rw [QuotientGroup.eq_iff_div_mem] at h1
    simpa [div_eq_mul_inv] using h1

private lemma aSet_five_false_of_small_displacement {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F}
    {A : Subgroup (MulAut (Multiplicative ↥(adjOmega6 F b)))}
    (hA : A ∈ E3.aSet 5 (adjAct F b c).range)
    {x : Multiplicative ↥(adjOmega6 F b)} (hx : x ∉ fixV A)
    {U₀ : Subgroup (Multiplicative ↥(adjOmega6 F b))} (hU₀ : Nat.card U₀ ≤ 16)
    (hdisp : ∀ a ∈ A, a x * x⁻¹ ∈ U₀) : False := by
  have h1 : 5 ≤ E3.mQuot A (CFSG.LocalAnalysis.UniquenessCase.PartTwo.stabAt A x) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.le_mQuot_stabAt_of_mem_aSet hA hx
  have h2 : 2 ^ E3.mQuot A (CFSG.LocalAnalysis.UniquenessCase.PartTwo.stabAt A x) ≤
      Nat.card U₀ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.two_pow_mQuot_stabAt_le hA.2.2.1 hdisp
  have h3 : 2 ^ (5 : ℕ) ≤ Nat.card U₀ :=
    le_trans (Nat.pow_le_pow_right (by norm_num) h1) h2
  omega

private noncomputable def adjWedgeHom {F : Type} [Field F] [CharP F 2] (b : F) (v : Om6Idx → F) :
    StdMod Om6Idx F →* Multiplicative ↥(adjOmega6 F b) where
  toFun w := adjWedge b v w.toAdd
  map_one' := by
    change adjWedge b v (0 : Om6Idx → F) = 1
    have h0 := adjWedge_add_right b v 0 0
    rw [add_zero] at h0
    have h2 := congrArg (fun z => (adjWedge b v 0)⁻¹ * z) h0
    simpa [mul_assoc] using h2.symm
  map_mul' w w' := by
    change adjWedge b v (w.toAdd + w'.toAdd) = adjWedge b v w.toAdd * adjWedge b v w'.toAdd
    rw [adjWedge_add_right]

private lemma adjWedge_zero {F : Type} [Field F] [CharP F 2] (b : F) (v : Om6Idx → F) :
    adjWedge b v (0 : Om6Idx → F) = (1 : Multiplicative ↥(adjOmega6 F b)) := by
  have h0 := adjWedge_add_right b v 0 0
  rw [add_zero] at h0
  have h2 := congrArg (fun z => (adjWedge b v 0)⁻¹ * z) h0
  simpa [mul_assoc] using h2.symm

private lemma toAdd_mul_inv_of_mulAut {F : Type} [Field F] [CharP F 2]
    (b : MulAut (StdMod Om6Idx F)) (w : StdMod Om6Idx F) :
    (b w * w⁻¹).toAdd = toAddMap b w.toAdd - w.toAdd := by
  rw [toAdd_mul, toAdd_inv, sub_eq_add_neg]
  rfl

private lemma adjWedge_smul_self_of_ne_zero {F : Type} [Field F] [CharP F 2] {b : F} (hb : b ≠ 0)
    {v : Om6Idx → F} (hv : v ≠ 0) (s : F) :
    adjWedge b v (s • v) = (1 : Multiplicative ↥(adjOmega6 F b)) := by
  have hzero : adjWedge b v (0 : Om6Idx → F) = 1 := by
    have h0 := adjWedge_add_right b v 0 0
    rw [add_zero] at h0
    have h2 := congrArg (fun z => (adjWedge b v 0)⁻¹ * z) h0
    simpa [mul_assoc] using h2.symm
  have h := (adjWedge_eq_iff (b := b) hb (v := v) (w := s • v) (w' := 0) hv).mpr
    ⟨s, by rw [sub_zero]⟩
  rwa [hzero] at h

private lemma adjWedge_add_left {F : Type} [Field F] [CharP F 2] (b : F) (v v' w : Om6Idx → F) :
    adjWedge b (v + v') w = adjWedge b v w * adjWedge b v' w := by
  calc adjWedge b (v + v') w = adjWedge b w (v + v') := adjWedge_comm b (v + v') w
    _ = adjWedge b w v * adjWedge b w v' := adjWedge_add_right b w v v'
    _ = adjWedge b v w * adjWedge b v' w := by rw [adjWedge_comm b w v, adjWedge_comm b w v']

private lemma adjAct_adjWedge_mul_inv {F : Type} [Field F] [CharP F 2] {b c : F} (hb : b ≠ 0)
    (g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))) (v : Om6Idx → F) (w : StdMod Om6Idx F)
    (hv : ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v = v) :
    adjAct F b c g (adjWedge b v w.toAdd) * (adjWedge b v w.toAdd)⁻¹ =
      adjWedgeHom b v (matAut (g : GL Om6Idx F) w * w⁻¹) := by
  rw [adjAct_adjWedge hb, hv, ← toAddMap_matAut]
  change adjWedgeHom b v (matAut (g : GL Om6Idx F) w) * (adjWedgeHom b v w)⁻¹ =
    adjWedgeHom b v (matAut (g : GL Om6Idx F) w * w⁻¹)
  rw [← map_inv, ← map_mul]

private lemma wedge_add_smul_pair {F : Type} [Field F] [CharP F 2] {b : F} (hb : b ≠ 0)
    {v₀ v₂ v₃ : Om6Idx → F} (hv₀ : v₀ ≠ 0) (β α : F) :
    adjWedge b (v₂ + β • v₀) (v₃ + α • v₀) =
      adjWedge b v₂ v₃ * adjWedge b v₀ (α • v₂) * adjWedge b v₀ (β • v₃) := by
  rw [adjWedge_add_left, adjWedge_add_right, adjWedge_add_right]
  rw [adjWedge_comm b v₂ (α • v₀), adjWedge_smul b α v₀ v₂]
  rw [adjWedge_smul b β v₀ v₃]
  rw [adjWedge_smul b β v₀ (α • v₀)]
  rw [show β • (α • v₀) = (β * α) • v₀ by rw [smul_smul]]
  rw [adjWedge_smul_self_of_ne_zero hb hv₀]
  simp [mul_assoc]

private lemma wedge_add_smul_pair_mul_inv {F : Type} [Field F] [CharP F 2] {b : F} (hb : b ≠ 0)
    {v₀ v₂ v₃ : Om6Idx → F} (hv₀ : v₀ ≠ 0) (β α : F) :
    adjWedge b (v₂ + β • v₀) (v₃ + α • v₀) * (adjWedge b v₂ v₃)⁻¹ =
      adjWedge b v₀ (α • v₂ + β • v₃) := by
  rw [wedge_add_smul_pair hb hv₀]
  have hcancel : ∀ a b : Multiplicative ↥(adjOmega6 F b), a * b * a⁻¹ = b := by
    intro a b
    calc a * b * a⁻¹ = b * (a * a⁻¹) := by ac_rfl
      _ = b := by rw [mul_inv_cancel, mul_one]
  calc
    adjWedge b v₂ v₃ * adjWedge b v₀ (α • v₂) * adjWedge b v₀ (β • v₃) *
        (adjWedge b v₂ v₃)⁻¹
        = adjWedge b v₂ v₃ * (adjWedge b v₀ (α • v₂) * adjWedge b v₀ (β • v₃)) *
            (adjWedge b v₂ v₃)⁻¹ := by ac_rfl
    _ = adjWedge b v₂ v₃ * adjWedge b v₀ (α • v₂ + β • v₃) *
            (adjWedge b v₂ v₃)⁻¹ := by rw [← adjWedge_add_right]
    _ = adjWedge b v₀ (α • v₂ + β • v₃) := hcancel _ _

private lemma notMem_span_of_coeff_ne_zero {F : Type} [Field F] [CharP F 2]
    {v₀ v₂ v₃ : Om6Idx → F} (hli : LinearIndependent F ![v₀, v₂, v₃]) {α β : F}
    (hβ : β ≠ 0) : α • v₂ + β • v₃ ∉ Submodule.span F {v₀} := by
  intro hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hsum : s • v₀ + α • v₂ + β • v₃ = 0 := by
    rw [hs]
    convert CharTwo.add_self_eq_zero (α • v₂ + β • v₃) using 1
    abel
  have hcoe : ![s, α, β] (2 : Fin 3) = 0 :=
    (Fintype.linearIndependent_iff.mp hli) ![s, α, β]
      (by simpa [Fin.sum_univ_three] using hsum) 2
  exact hβ (by simpa using hcoe)

private lemma card_toAddSubgroup_toSubgroup {F : Type} [Field F]
    (P : Submodule F (Om6Idx → F)) :
    Nat.card P.toAddSubgroup.toSubgroup = Nat.card P := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x =>
        ⟨x.1.toAdd, (Multiplicative.mem_toSubgroup P.toAddSubgroup x.1).mp x.2⟩
      invFun := fun x =>
        ⟨Multiplicative.ofAdd x.1,
          (Multiplicative.mem_toSubgroup P.toAddSubgroup _).mpr (by simpa using x.2)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp
  · intro x
    apply Subtype.ext
    simp

private lemma adjWedge_line_not_fixed {F : Type} [Field F] [CharP F 2] {b c : F}
    (hb : b ≠ 0) {A : Subgroup (MulAut (Multiplicative ↥(adjOmega6 F b)))}
    {A₀ : Subgroup ↥(omIsoGroup (StatedQuadMinus 3 F b c))}
    (hA₀map : A₀.map (adjAct F b c) = A)
    {v₀ v₃ : Om6Idx → F} (hv₀0 : v₀ ≠ 0)
    (hv₀fix : ∀ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v₀ = v₀)
    {g₀ : ↥(omIsoGroup (StatedQuadMinus 3 F b c))} (hg₀ : g₀ ∈ A₀)
    {u : Om6Idx → F} (hu_def : (g₀ : GL Om6Idx F) *ᵥ v₃ - v₃ = u)
    (hu : u ∉ Submodule.span F {v₀}) :
    adjWedge b v₀ v₃ ∉ fixV A := by
  intro hxfix
  have hg₀A : adjAct F b c g₀ ∈ A := by
    rw [← hA₀map]
    exact Subgroup.mem_map_of_mem _ hg₀
  have hfix := mem_fixV.mp hxfix (adjAct F b c g₀) hg₀A
  have hprod : adjAct F b c g₀ (adjWedge b v₀ v₃) * (adjWedge b v₀ v₃)⁻¹ = 1 := by
    rw [hfix, mul_inv_cancel]
  have hneg : adjWedge b v₀ (-v₃) = (adjWedge b v₀ v₃)⁻¹ := by
    have h := adjWedge_add_right b v₀ v₃ (-v₃)
    rw [add_neg_cancel, adjWedge_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hformula : adjAct F b c g₀ (adjWedge b v₀ v₃) * (adjWedge b v₀ v₃)⁻¹ =
      adjWedge b v₀ u := by
    rw [adjAct_adjWedge hb, hv₀fix g₀ hg₀, ← hu_def, sub_eq_add_neg,
      adjWedge_add_right, hneg]
  rw [hformula] at hprod
  have hne1 : adjWedge b v₀ u ≠ 1 := by
    intro hzero
    apply hu
    have h0 : adjWedge b v₀ u = adjWedge b v₀ (0 : Om6Idx → F) := by
      rw [hzero, adjWedge_zero]
    obtain ⟨s, hs⟩ := (adjWedge_eq_iff hb hv₀0 (w := u) (w' := 0)).mp h0
    rw [Submodule.mem_span_singleton]
    exact ⟨s, by simpa using hs.symm⟩
  exact hne1 hprod

private lemma adjWedge_line_displacement {F : Type} [Field F] [CharP F 2] {b c : F}
    (hb : b ≠ 0) {A : Subgroup (MulAut (Multiplicative ↥(adjOmega6 F b)))}
    {A₀ : Subgroup ↥(omIsoGroup (StatedQuadMinus 3 F b c))}
    (hA₀map : A₀.map (adjAct F b c) = A)
    {v₀ v₃ : Om6Idx → F}
    (hv₀fix : ∀ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v₀ = v₀)
    {P : Submodule F (Om6Idx → F)}
    (huP : ∀ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v₃ - v₃ ∈ P) :
    ∀ a ∈ A, a (adjWedge b v₀ v₃) * (adjWedge b v₀ v₃)⁻¹ ∈
      P.toAddSubgroup.toSubgroup.map (adjWedgeHom b v₀) := by
  intro a ha
  have ha' : a ∈ A₀.map (adjAct F b c) := by rwa [hA₀map]
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha'
  have hneg : adjWedge b v₀ (-v₃) = (adjWedge b v₀ v₃)⁻¹ := by
    have h := adjWedge_add_right b v₀ v₃ (-v₃)
    rw [add_neg_cancel, adjWedge_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hformula : adjAct F b c g (adjWedge b v₀ v₃) * (adjWedge b v₀ v₃)⁻¹ =
      adjWedge b v₀ ((g : GL Om6Idx F) *ᵥ v₃ - v₃) := by
    rw [adjAct_adjWedge hb, hv₀fix g hg, sub_eq_add_neg, adjWedge_add_right, hneg]
  rw [hformula]
  exact Subgroup.mem_map_of_mem (adjWedgeHom b v₀)
    ((Multiplicative.mem_toSubgroup P.toAddSubgroup
        (Multiplicative.ofAdd ((g : GL Om6Idx F) *ᵥ v₃ - v₃))).mpr
      (by simpa only [toAdd_ofAdd, Submodule.mem_toAddSubgroup] using huP g hg))

private lemma exists_small_displacement_of_mem_aSet {F : Type} [Field F] [Finite F]
    [CharP F 2] {b c : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {A : Subgroup (MulAut (Multiplicative ↥(adjOmega6 F b)))}
    (hA : A ∈ E3.aSet 5 (adjAct F b c).range) :
    ∃ x : Multiplicative ↥(adjOmega6 F b), x ∉ fixV A ∧
      ∃ U₀ : Subgroup (Multiplicative ↥(adjOmega6 F b)),
        Nat.card U₀ ≤ 16 ∧ ∀ a ∈ A, a x * x⁻¹ ∈ U₀ := by
  classical
  have hb : b ≠ 0 := by
    intro hb
    have hinj : Function.Injective (fun s : F => s ^ 2) := by
      intro s t hst
      change s ^ 2 = t ^ 2 at hst
      have hsq : (s + t) ^ 2 = 0 := by
        rw [add_sq, hst]
        simp [CharTwo.two_eq_zero]
        exact CharTwo.add_self_eq_zero (t ^ 2)
      have hst0 : s + t = 0 := eq_zero_of_pow_eq_zero hsq
      have hst0' : t + s = 0 := by rw [add_comm]; exact hst0
      calc s = -t := eq_neg_of_add_eq_zero_right hst0'
        _ = t := by rw [CharTwo.neg_eq]
    have hsurj : Function.Surjective (fun s : F => s ^ 2) :=
      Finite.surjective_of_injective hinj
    obtain ⟨s, hs⟩ := hsurj c
    apply hirr s
    have hsc : s ^ 2 = c := hs
    rw [hb, zero_mul, add_zero, hsc]
    exact CharTwo.add_self_eq_zero c
  let ρ : ↥(omIsoGroup (StatedQuadMinus 3 F b c)) →*
      MulAut (Multiplicative ↥(adjOmega6 F b)) := adjAct F b c
  let A₀ : Subgroup ↥(omIsoGroup (StatedQuadMinus 3 F b c)) := A.comap ρ
  let φ : ↥(omIsoGroup (StatedQuadMinus 3 F b c)) →*
      MulAut (Multiplicative (Om6Idx → F)) :=
    matHom.comp (omIsoGroup (StatedQuadMinus 3 F b c)).subtype
  let B : Subgroup (MulAut (Multiplicative (Om6Idx → F))) := A₀.map φ
  have hρinj : Function.Injective ρ := adjAct_injective hirr
  have hA₀map : A₀.map ρ = A := by
    exact Subgroup.map_comap_eq_self (f := ρ) hA.1
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    apply hA.2.1
    rw [← hA₀map, h, Subgroup.map_bot]
  have hA₀comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := by
    intro a ha b hb
    apply hρinj
    rw [map_mul, map_mul]
    apply hA.2.2.1.1
    · rw [← hA₀map]
      exact Subgroup.mem_map_of_mem ρ ha
    · rw [← hA₀map]
      exact Subgroup.mem_map_of_mem ρ hb
  have hA₀sq : ∀ a ∈ A₀, a ^ 2 = 1 := by
    intro a ha
    apply hρinj
    rw [map_pow, map_one]
    apply hA.2.2.1.2
    rw [← hA₀map]
    exact Subgroup.mem_map_of_mem ρ ha
  have hφinj : Function.Injective φ :=
    matHom_injective.comp (Subgroup.subtype_injective (omIsoGroup (StatedQuadMinus 3 F b c)))
  have hBne : B ≠ ⊥ := by
    intro h
    apply hA₀ne
    rw [Subgroup.eq_bot_iff_forall] at h ⊢
    intro g hg
    have hmem : φ g ∈ B := Subgroup.mem_map_of_mem φ hg
    have hg1 : φ g = 1 := h (φ g) hmem
    exact hφinj (by rw [hg1]; exact (map_one φ).symm)
  have hBel : IsElemAbelian2 B := by
    constructor
    · intro a ha b hb
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact hA₀comm g hg h hh
    · intro a ha
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← map_pow, ← map_one φ]
      congr 1
      exact hA₀sq g hg
  have hWst : ∀ w : Multiplicative (Om6Idx → F), w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact CharTwo.two_nsmul _
  have hlinB : ∀ a ∈ B, IsSemilinear a (RingEquiv.refl F) := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    exact isSemilinear_matAut _
  have hisoB : ∀ a ∈ B, ∀ v, StatedQuadMinus 3 F b c (toAddMap a v) =
      StatedQuadMinus 3 F b c v := by
    intro a ha v
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
    change StatedQuadMinus 3 F b c
      (toAddMap (matAut (g : GL Om6Idx F)) v) = StatedQuadMinus 3 F b c v
    rw [toAddMap_matAut]
    exact g.2 v
  let D : Submodule F (Om6Idx → F) :=
    { carrier := {v | ∀ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v = v}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw g hg
        rw [Matrix.mulVec_add, hv g hg, hw g hg]
      smul_mem' := by
        intro s v hv g hg
        rw [Matrix.mulVec_smul, hv g hg] }
  have hDmem : ∀ w : Multiplicative (Om6Idx → F),
      w.toAdd ∈ D ↔ w ∈ fixV B := by
    intro w
    constructor
    · intro hd b hb
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hb
      apply Multiplicative.toAdd.injective
      change toAddMap (matAut (g : GL Om6Idx F)) w.toAdd = w.toAdd
      rw [toAddMap_matAut]
      exact hd g hg
    · intro hfix g hg
      have hmem : φ g ∈ B := Subgroup.mem_map_of_mem φ hg
      have h := mem_fixV.mp hfix (φ g) hmem
      have h' := congrArg Multiplicative.toAdd h
      change toAddMap (matAut (g : GL Om6Idx F)) w.toAdd = w.toAdd at h'
      rw [toAddMap_matAut] at h'
      exact h'
  have hfixne : fixV B ≠ ⊥ := by
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.fixV_ne_bot hWst hBel
  have hDne : D ≠ ⊥ := by
    intro hbot
    apply hfixne
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have hmem : w.toAdd ∈ D := (hDmem w).mpr hw
    rw [hbot] at hmem
    have hzero : w.toAdd = 0 := by simpa using hmem
    exact Multiplicative.toAdd.injective (by simpa using hzero)
  have hDfix : ∀ {v : Om6Idx → F}, v ∈ D → ∀ g ∈ A₀,
      (g : GL Om6Idx F) *ᵥ v = v := fun hv => hv
  obtain ⟨w, hw, U, hUcard, hU⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.exists_small_orbit_omegaMinus
      (F := F) (b := b) (c := c) hirr (A := B) hBel hBne hlinB hisoB
  have hDpos : 0 < Module.finrank F D := by
    by_contra h
    have h0 : Module.finrank F D = 0 := by omega
    apply hDne
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : (⟨x, hx⟩ : ↥D) = 0 := (finrank_zero_iff_forall_zero.mp h0) ⟨x, hx⟩
    simpa using hx0
  by_cases hD2 : 2 ≤ Module.finrank F D
  · obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := ↥D) (n := 2) hD2
    let v₁ : Om6Idx → F := (f 0 : ↥D)
    let v₂ : Om6Idx → F := (f 1 : ↥D)
    have hv₁D : v₁ ∈ D := (f 0).2
    have hv₂D : v₂ ∈ D := (f 1).2
    have hli : LinearIndependent F ![v₁, v₂] := by
      have hmap := hf.map' (Submodule.subtype D) (Submodule.ker_subtype D)
      have hfun : (⇑D.subtype ∘ f) = ![v₁, v₂] := by
        funext i
        fin_cases i <;> rfl
      rwa [hfun] at hmap
    have hv₁0 : v₁ ≠ 0 := by simpa using hli.ne_zero 0
    have hv₂0 : v₂ ≠ 0 := by simpa using hli.ne_zero 1
    have hv₂span : v₂ ∉ Submodule.span F {v₁} := by
      intro hspan
      rw [Submodule.mem_span_singleton] at hspan
      obtain ⟨s, hs⟩ := hspan
      have hzero : s • v₁ + (1 : F) • v₂ = 0 := by
        rw [one_smul, hs]
        exact CharTwo.add_self_eq_zero v₂
      obtain ⟨-, h1⟩ := hli.eq_zero_of_pair hzero
      exact one_ne_zero h1
    rw [mem_fixV] at hw
    push Not at hw
    obtain ⟨b₀, hb₀B, hb₀w⟩ := hw
    obtain ⟨g₀, hg₀A₀, hg₀b⟩ := Subgroup.mem_map.mp hb₀B
    let u₀ : Om6Idx → F := (g₀ : GL Om6Idx F) *ᵥ w.toAdd - w.toAdd
    have hu₀ne : u₀ ≠ 0 := by
      intro h
      apply hb₀w
      have hgw : (g₀ : GL Om6Idx F) *ᵥ w.toAdd = w.toAdd := sub_eq_zero.mp h
      apply Multiplicative.toAdd.injective
      rw [← hg₀b]
      change toAddMap (matAut (g₀ : GL Om6Idx F)) w.toAdd = w.toAdd
      rw [toAddMap_matAut]
      exact hgw
    have hchoose : ∃ v : Om6Idx → F, v ∈ D ∧ v ≠ 0 ∧
        u₀ ∉ Submodule.span F {v} := by
      by_cases h1 : u₀ ∈ Submodule.span F {v₁}
      · refine ⟨v₂, hv₂D, hv₂0, ?_⟩
        intro h2
        have hdisj : Disjoint (Submodule.span F {v₁}) (Submodule.span F {v₂}) :=
          (Submodule.disjoint_span_singleton' (s := Submodule.span F {v₁}) hv₂0).mpr hv₂span
        exact hu₀ne (Submodule.disjoint_def.mp hdisj u₀ h1 h2)
      · exact ⟨v₁, hv₁D, hv₁0, h1⟩
    obtain ⟨v, hvD, hv0, hvspan⟩ := hchoose
    let U₀ : Subgroup (Multiplicative ↥(adjOmega6 F b)) := U.map (adjWedgeHom b v)
    let x : Multiplicative ↥(adjOmega6 F b) := adjWedge b v w.toAdd
    have hx : x ∉ fixV A := by
      intro hxfix
      have hg₀A : ρ g₀ ∈ A := by
        rw [← hA₀map]
        exact Subgroup.mem_map_of_mem ρ hg₀A₀
      have hfix := mem_fixV.mp hxfix (ρ g₀) hg₀A
      have hprod : ρ g₀ x * x⁻¹ = 1 := by rw [hfix, mul_inv_cancel]
      have hformula : ρ g₀ x * x⁻¹ = adjWedge b v u₀ := by
        have hvfix : ((g₀ : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v = v :=
          hDfix hvD g₀ hg₀A₀
        have harg : matAut (g₀ : GL Om6Idx F) w * w⁻¹ = Multiplicative.ofAdd u₀ := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul_inv_of_mulAut]
          rfl
        rw [adjAct_adjWedge_mul_inv hb g₀ v w hvfix, harg]
        rfl
      rw [hformula] at hprod
      apply hvspan
      have heq : adjWedge b v u₀ = adjWedge b v (0 : Om6Idx → F) := by
        rw [hprod, adjWedge_zero]
      obtain ⟨s, hs⟩ :=
        (adjWedge_eq_iff (b := b) hb (v := v) (w := u₀) (w' := 0) hv0).mp heq
      rw [Submodule.mem_span_singleton]
      exact ⟨s, by simpa using hs.symm⟩
    have hU₀card : Nat.card U₀ ≤ 16 := by
      have hle : Nat.card U₀ ≤ Nat.card U := by
        refine Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (H := U) (adjWedgeHom b v))
      calc Nat.card U₀ ≤ Nat.card U := hle
        _ ≤ Nat.card F ^ 2 := hUcard
        _ = 16 := by rw [hF]; norm_num
    have hdisp : ∀ a ∈ A, a x * x⁻¹ ∈ U₀ := by
      intro a ha
      have ha' : a ∈ A₀.map ρ := by
        rw [hA₀map]
        exact ha
      obtain ⟨g, hgA₀, rfl⟩ := Subgroup.mem_map.mp ha'
      have hvfix : ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F) *ᵥ v = v :=
        hDfix hvD g hgA₀
      have hbB : φ g ∈ B := Subgroup.mem_map_of_mem φ hgA₀
      have hUmem : matAut (g : GL Om6Idx F) w * w⁻¹ ∈ U := by
        change (φ g) w * w⁻¹ ∈ U
        exact hU (φ g) hbB
      rw [adjAct_adjWedge_mul_inv hb g v w hvfix]
      exact Subgroup.mem_map_of_mem (adjWedgeHom b v) hUmem
    refine ⟨x, hx, U₀, hU₀card, hdisp⟩
  · have hD1 : Module.finrank F D = 1 := by omega
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := ↥D) (n := 1)
      (by omega)
    let v₀ : Om6Idx → F := (f 0 : ↥D)
    have hv₀D : v₀ ∈ D := (f 0).2
    have hv₀0 : v₀ ≠ 0 := by
      have := hf.ne_zero 0
      simpa [v₀] using this
    have hDeq : D = Submodule.span F {v₀} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hD1 hv₀D hv₀0
    let Dsub : Subgroup (Multiplicative (Om6Idx → F)) := D.toAddSubgroup.toSubgroup
    have hDsub_le : Dsub ≤ fixV B := by
      intro x hx
      rw [mem_fixV]
      intro b hb
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hb
      have hxD : x.toAdd ∈ D := (Multiplicative.mem_toSubgroup D.toAddSubgroup x).mp hx
      apply Multiplicative.toAdd.injective
      change toAddMap (matAut (g : GL Om6Idx F)) x.toAdd = x.toAdd
      rw [toAddMap_matAut]
      exact hDfix hxD g hg
    have hDsub_ne_top : Dsub ≠ ⊤ := by
      intro htop
      apply CFSG.LocalAnalysis.UniquenessCase.PartTwo.fixV_ne_top hBne
      rw [← top_le_iff]
      calc (⊤ : Subgroup (StdMod Om6Idx F)) = Dsub := htop.symm
        _ ≤ fixV B := hDsub_le
    obtain ⟨w₂, hw₂Dsub, hw₂disp⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_mem_secondLayer
        hWst hBel hDsub_le hDsub_ne_top
    let v₂ : Om6Idx → F := w₂.toAdd
    have hv₂D : v₂ ∉ D := by
      intro hv
      apply hw₂Dsub
      exact (Multiplicative.mem_toSubgroup D.toAddSubgroup w₂).mpr (by simpa [v₂] using hv)
    let P : Submodule F (Om6Idx → F) := Submodule.span F {v₀, v₂}
    let Psub : Subgroup (Multiplicative (Om6Idx → F)) := P.toAddSubgroup.toSubgroup
    have hDsub_le_P : D ≤ P := by
      rw [hDeq]
      refine Submodule.span_le.mpr ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Submodule.subset_span (by simp)
    have hPinv : ∀ g ∈ A₀, ∀ p ∈ P, (g : GL Om6Idx F) *ᵥ p ∈ P := by
      intro g hg p hp
      have hgen : ∀ x ∈ ({v₀, v₂} : Set (Om6Idx → F)),
          (g : GL Om6Idx F) *ᵥ x ∈ P := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx | hx
        · rw [hx, hDfix hv₀D g hg]
          exact Submodule.subset_span (by simp)
        · rw [hx]
          have hdisp : (g : GL Om6Idx F) *ᵥ v₂ - v₂ ∈ D := by
            have h := hw₂disp (φ g) (Subgroup.mem_map_of_mem φ hg)
            rw [Multiplicative.mem_toSubgroup] at h
            rw [toAdd_mul_inv_of_mulAut (b := φ g) (w := w₂)] at h
            change toAddMap (matAut (g : GL Om6Idx F)) w₂.toAdd - w₂.toAdd ∈ D at h
            rw [toAddMap_matAut] at h
            exact h
          have hmem : (g : GL Om6Idx F) *ᵥ v₂ - v₂ ∈ P := hDsub_le_P hdisp
          have hstep : (g : GL Om6Idx F) *ᵥ v₂ = v₂ +
              ((g : GL Om6Idx F) *ᵥ v₂ - v₂) := by abel
          rw [hstep]
          exact Submodule.add_mem P (Submodule.subset_span (by simp)) hmem
      induction hp using Submodule.span_induction with
      | mem x hx => exact hgen x hx
      | zero => simp
      | add x y hx hy ihx ihy =>
          rw [Matrix.mulVec_add]
          exact Submodule.add_mem P ihx ihy
      | smul a x hx ih =>
          rw [Matrix.mulVec_smul]
          exact Submodule.smul_mem P a ih
    have hP : ∀ a ∈ B, ∀ p ∈ Psub, a p ∈ Psub := by
      intro b hb p hp
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hb
      rw [Multiplicative.mem_toSubgroup] at hp ⊢
      change (g : GL Om6Idx F) *ᵥ p.toAdd ∈ P
      exact hPinv g hg p.toAdd hp
    have hPfin : Module.finrank F P ≤ 2 := by
      have h := finrank_span_le_card (R := F) ({v₀, v₂} : Set (Om6Idx → F))
      have hcard : ({v₀, v₂} : Set (Om6Idx → F)).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact (Finset.card_insert_le _ _).trans (by simp)
      simpa [P] using h.trans hcard
    have hPne : Psub ≠ ⊤ := by
      intro htop
      have hPtop : P = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : Multiplicative.ofAdd x ∈ Psub := by
          rw [htop]
          exact Subgroup.mem_top _
        exact (Multiplicative.mem_toSubgroup P.toAddSubgroup (Multiplicative.ofAdd x)).mp hx
      have hV6 : Module.finrank F (Om6Idx → F) = 6 := by
        rw [Module.finrank_fintype_fun_eq_card]
        norm_num [Fintype.card_sum]
      have hdim : Module.finrank F P = 6 := by
        rw [hPtop, finrank_top, hV6]
      omega
    obtain ⟨w₃, hw₃P, hw₃disp⟩ := exists_mem_nextLayer hWst hBel hP hPne
    let v₃ : Om6Idx → F := w₃.toAdd
    have hv₃P : v₃ ∉ P := by
      intro hv
      apply hw₃P
      exact (Multiplicative.mem_toSubgroup P.toAddSubgroup w₃).mpr (by simpa [v₃] using hv)
    have hDline : ∀ {x : Om6Idx → F}, x ∈ D → ∃ s : F, x = s • v₀ := by
      intro x hx
      rw [hDeq] at hx
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx
      exact ⟨s, hs.symm⟩
    have hv₂not : v₂ ∉ Submodule.span F {v₀} := by
      intro hmem
      exact hv₂D (by rwa [hDeq])
    have hpair : LinearIndependent F ![v₀, v₂] := by
      rw [LinearIndependent.pair_iff' hv₀0]
      intro a ha
      exact hv₂not (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
    have hli3 : LinearIndependent F ![v₀, v₂, v₃] := by
      have hsnoc := hpair.finSnoc (x := v₃) ?_
      · simpa using hsnoc
      · intro hmem
        apply hv₃P
        have hrange : Set.range ![v₀, v₂] = ({v₀, v₂} : Set (Om6Idx → F)) := by
          ext y
          simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
        rwa [hrange] at hmem
    have hdisp₂ : ∀ g ∈ A₀, ∃ β : F,
        (g : GL Om6Idx F) *ᵥ v₂ = v₂ + β • v₀ := by
      intro g hg
      have h := hw₂disp (φ g) (Subgroup.mem_map_of_mem φ hg)
      rw [Multiplicative.mem_toSubgroup] at h
      rw [toAdd_mul_inv_of_mulAut (b := φ g) (w := w₂)] at h
      change toAddMap (matAut (g : GL Om6Idx F)) w₂.toAdd - w₂.toAdd ∈ D at h
      rw [toAddMap_matAut] at h
      obtain ⟨β, hβ⟩ := hDline h
      refine ⟨β, ?_⟩
      calc (g : GL Om6Idx F) *ᵥ v₂ = v₂ + ((g : GL Om6Idx F) *ᵥ v₂ - v₂) := by abel
        _ = v₂ + β • v₀ := by rw [hβ]
    by_cases hcase : ∀ b ∈ B, b w₃ * w₃⁻¹ ∈ Dsub
    ·
      have hdisp₃ : ∀ g ∈ A₀, ∃ α : F,
          (g : GL Om6Idx F) *ᵥ v₃ = v₃ + α • v₀ := by
        intro g hg
        have h := hcase (φ g) (Subgroup.mem_map_of_mem φ hg)
        rw [Multiplicative.mem_toSubgroup] at h
        rw [toAdd_mul_inv_of_mulAut (b := φ g) (w := w₃)] at h
        change toAddMap (matAut (g : GL Om6Idx F)) w₃.toAdd - w₃.toAdd ∈ D at h
        rw [toAddMap_matAut] at h
        obtain ⟨α, hα⟩ := hDline h
        refine ⟨α, ?_⟩
        calc (g : GL Om6Idx F) *ᵥ v₃ = v₃ + ((g : GL Om6Idx F) *ᵥ v₃ - v₃) := by abel
          _ = v₃ + α • v₀ := by rw [hα]
      let P23 : Submodule F (Om6Idx → F) := Submodule.span F {v₂, v₃}
      let P23sub : Subgroup (Multiplicative (Om6Idx → F)) := P23.toAddSubgroup.toSubgroup
      have hP23fin : Module.finrank F P23 ≤ 2 := by
        have h := finrank_span_le_card (R := F) ({v₂, v₃} : Set (Om6Idx → F))
        have hcard : ({v₂, v₃} : Set (Om6Idx → F)).toFinset.card ≤ 2 := by
          rw [Set.toFinset_insert, Set.toFinset_singleton]
          exact (Finset.card_insert_le _ _).trans (by simp)
        simpa [P23] using h.trans hcard
      have hP23card : Nat.card P23sub ≤ 16 := by
        rw [card_toAddSubgroup_toSubgroup]
        calc Nat.card P23 = Nat.card F ^ Module.finrank F P23 :=
              Module.natCard_eq_pow_finrank (K := F) (V := ↥P23)
          _ = 4 ^ Module.finrank F P23 := by rw [hF]
          _ ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hP23fin
          _ = 16 := by norm_num
      let U₀ : Subgroup (Multiplicative ↥(adjOmega6 F b)) := P23sub.map (adjWedgeHom b v₀)
      let x : Multiplicative ↥(adjOmega6 F b) := adjWedge b v₂ v₃
      have hU₀card : Nat.card U₀ ≤ 16 := by
        have hle : Nat.card U₀ ≤ Nat.card P23sub := by
          refine Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_map_dvd (H := P23sub) (adjWedgeHom b v₀))
        exact hle.trans hP23card
      have hex : ∃ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v₂ ≠ v₂ := by
        by_contra h
        apply hv₂D
        intro g hg
        by_contra hne
        exact h ⟨g, hg, hne⟩
      obtain ⟨g₀, hg₀A₀, hg₀ne⟩ := hex
      obtain ⟨β₀, hβ₀⟩ := hdisp₂ g₀ hg₀A₀
      obtain ⟨α₀, hα₀⟩ := hdisp₃ g₀ hg₀A₀
      have hβ₀ne : β₀ ≠ 0 := by
        intro hβ0
        apply hg₀ne
        rw [hβ₀, hβ0, zero_smul, add_zero]
      have hx : x ∉ fixV A := by
        intro hxfix
        have hg₀A : ρ g₀ ∈ A := by
          rw [← hA₀map]
          exact Subgroup.mem_map_of_mem ρ hg₀A₀
        have hfix := mem_fixV.mp hxfix (ρ g₀) hg₀A
        have hprod : (ρ g₀) x * x⁻¹ = 1 := by rw [hfix, mul_inv_cancel]
        have hformula : (ρ g₀) x * x⁻¹ =
            adjWedge b v₀ (α₀ • v₂ + β₀ • v₃) := by
          rw [adjAct_adjWedge hb, hβ₀, hα₀]
          exact wedge_add_smul_pair_mul_inv hb hv₀0 β₀ α₀
        rw [hformula] at hprod
        have hu : α₀ • v₂ + β₀ • v₃ ∉ Submodule.span F {v₀} :=
          notMem_span_of_coeff_ne_zero hli3 hβ₀ne
        have hne1 : adjWedge b v₀ (α₀ • v₂ + β₀ • v₃) ≠ 1 := by
          intro hzero
          apply hu
          have h0 : adjWedge b v₀ (α₀ • v₂ + β₀ • v₃) =
              adjWedge b v₀ (0 : Om6Idx → F) := by rw [hzero, adjWedge_zero]
          obtain ⟨s, hs⟩ :=
            (adjWedge_eq_iff hb hv₀0 (w := α₀ • v₂ + β₀ • v₃) (w' := 0)).mp h0
          rw [Submodule.mem_span_singleton]
          exact ⟨s, by simpa using hs.symm⟩
        exact hne1 hprod
      have hdisp : ∀ a ∈ A, a x * x⁻¹ ∈ U₀ := by
        intro a ha
        have ha' : a ∈ A₀.map ρ := by rw [hA₀map]; exact ha
        obtain ⟨g, hgA₀, rfl⟩ := Subgroup.mem_map.mp ha'
        obtain ⟨βg, hβg⟩ := hdisp₂ g hgA₀
        obtain ⟨αg, hαg⟩ := hdisp₃ g hgA₀
        have hformula : (ρ g) x * x⁻¹ =
            adjWedge b v₀ (αg • v₂ + βg • v₃) := by
          rw [adjAct_adjWedge hb, hβg, hαg]
          exact wedge_add_smul_pair_mul_inv hb hv₀0 βg αg
        rw [hformula]
        have hmem : (fun i => αg * v₂ i + βg * v₃ i) ∈ P23 := by
          have h : αg • v₂ + βg • v₃ ∈ P23 :=
            Submodule.add_mem P23
              (Submodule.smul_mem P23 αg (Submodule.subset_span (by simp)))
              (Submodule.smul_mem P23 βg (Submodule.subset_span (by simp)))
          have hfun : (fun i => αg * v₂ i + βg * v₃ i) = αg • v₂ + βg • v₃ := by
            funext i
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hfun]
          exact h
        exact Subgroup.mem_map_of_mem (adjWedgeHom b v₀)
          ((Multiplicative.mem_toSubgroup P23.toAddSubgroup
              (Multiplicative.ofAdd (fun i => αg * v₂ i + βg * v₃ i))).mpr
            (by simpa only [toAdd_ofAdd, Submodule.mem_toAddSubgroup] using hmem))
      refine ⟨x, hx, U₀, hU₀card, ?_⟩
      exact hdisp
    ·
      push Not at hcase
      obtain ⟨b₀, hb₀B, hb₀out⟩ := hcase
      obtain ⟨g₀, hg₀A₀, hg₀b⟩ := Subgroup.mem_map.mp hb₀B
      have hdisp₃P : ∀ g ∈ A₀, (g : GL Om6Idx F) *ᵥ v₃ - v₃ ∈ P := by
        intro g hg
        have h := hw₃disp (φ g) (Subgroup.mem_map_of_mem φ hg)
        rw [Multiplicative.mem_toSubgroup] at h
        rw [toAdd_mul_inv_of_mulAut (b := φ g) (w := w₃)] at h
        change toAddMap (matAut (g : GL Om6Idx F)) w₃.toAdd - w₃.toAdd ∈ P at h
        rw [toAddMap_matAut] at h
        exact h
      have hu₀D : (g₀ : GL Om6Idx F) *ᵥ v₃ - v₃ ∉ D := by
        intro h
        have hprod : (matAut (g₀ : GL Om6Idx F)) w₃ * w₃⁻¹ =
            Multiplicative.ofAdd ((g₀ : GL Om6Idx F) *ᵥ v₃ - v₃) := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul_inv_of_mulAut]
          rfl
        have hmemD : (matAut (g₀ : GL Om6Idx F)) w₃ * w₃⁻¹ ∈ Dsub := by
          rw [hprod, Multiplicative.mem_toSubgroup]
          simpa only [toAdd_ofAdd, Submodule.mem_toAddSubgroup] using h
        change (φ g₀) w₃ * w₃⁻¹ ∈ Dsub at hmemD
        rw [hg₀b] at hmemD
        exact hb₀out hmemD
      have hPcard : Nat.card Psub ≤ 16 := by
        rw [card_toAddSubgroup_toSubgroup]
        calc Nat.card P = Nat.card F ^ Module.finrank F P :=
              Module.natCard_eq_pow_finrank (K := F) (V := ↥P)
          _ = 4 ^ Module.finrank F P := by rw [hF]
          _ ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hPfin
          _ = 16 := by norm_num
      let U₀ : Subgroup (Multiplicative ↥(adjOmega6 F b)) := Psub.map (adjWedgeHom b v₀)
      let x : Multiplicative ↥(adjOmega6 F b) := adjWedge b v₀ v₃
      have hU₀card : Nat.card U₀ ≤ 16 := by
        have hle : Nat.card U₀ ≤ Nat.card Psub := by
          refine Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_map_dvd (H := Psub) (adjWedgeHom b v₀))
        exact hle.trans hPcard
      have hx : x ∉ fixV A := by
        have hu₀ : (g₀ : GL Om6Idx F) *ᵥ v₃ - v₃ ∉ Submodule.span F {v₀} := by
          rw [← hDeq]
          exact hu₀D
        exact adjWedge_line_not_fixed hb hA₀map hv₀0 (fun g hg => hv₀D g hg)
          hg₀A₀ rfl hu₀
      have hdisp : ∀ a ∈ A, a x * x⁻¹ ∈ U₀ := by
        exact adjWedge_line_displacement hb hA₀map (fun g hg => hv₀D g hg)
          (fun g hg => hdisp₃P g hg)
      refine ⟨x, hx, U₀, hU₀card, ?_⟩
      exact hdisp

theorem aSet_five_adjAct_range_eq_empty {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hF : Nat.card F = 4) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    E3.aSet 5 (adjAct F b c).range = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  obtain ⟨x, hx, U₀, hU₀, hdisp⟩ :=
    exists_small_displacement_of_mem_aSet hF hirr hA
  exact aSet_five_false_of_small_displacement hA hx hU₀ hdisp


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
