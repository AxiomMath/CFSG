module

public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetNondeg
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Roots
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux
import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.SmallF3.Omega.E7RootSet
  Certificates.OmegaSevenMax CFSG.RankThree.PartOne.KE8F TableBExcTwo TableBExcTwoTB
  TableBExcTwoFusion CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem p13e7_polarV_add_right (ψ x y : V) : polarV ψ (x + y) = polarV ψ x + polarV ψ y := by
  simp only [polarV, Pi.add_apply]
  ring

theorem p13e7_polarV_neg_right (ψ x : V) : polarV ψ (-x) = -polarV ψ x := by
  simp only [polarV, Pi.neg_apply]
  ring

theorem p13e7_polarV_zero_right (ψ : V) : polarV ψ 0 = 0 := by
  simp only [polarV, Pi.zero_apply]
  ring

@[expose] def p13e7PolarHom (ψ : V) : V →+ ZMod 3 :=
  AddMonoidHom.mk' (polarV ψ) (p13e7_polarV_add_right ψ)

@[expose] def p13e7Coord :
    (Fin 7 → ZMod 3) →+ V :=
  ExcFrameIso.frameCoordHom frameE7

@[expose] def p13e7HypVec (ψ : V) :
    AddSubgroup (Fin 7 → ZMod 3) :=
  ((p13e7PolarHom ψ).comp p13e7Coord).ker

theorem mem_p13e7HypVec {ψ : V}
    {v : Fin 7 → ZMod 3} : v ∈ p13e7HypVec ψ ↔ polarV ψ (p13e7Coord v) = 0 :=
  Iff.rfl

theorem p13e7Aux_polarV_add_left (x y z : V) : polarV (x + y) z = polarV x z + polarV y z := by
  simp only [polarV, Pi.add_apply]
  ring

theorem p13e7Aux_polarV_smul_left (c : ZMod 3) (x y : V) :
    polarV (c • x) y = c * polarV x y := by
  simp only [polarV, Pi.smul_apply, smul_eq_mul]
  ring

theorem p13e7Aux_polarV_smul_right (c : ZMod 3) (x y : V) :
    polarV x (c • y) = c * polarV x y := by
  simp only [polarV, Pi.smul_apply, smul_eq_mul]
  ring

theorem p13e7Aux_polarV_neg_left (x y : V) : polarV (-x) y = -polarV x y := by
  simp only [polarV, Pi.neg_apply]
  ring

theorem p13e7Aux_polarV_symm (x y : V) : polarV x y = polarV y x := by
  simp only [polarV]
  ring

theorem p13e7Aux_polarV_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (y : V) :
    polarV (∑ i ∈ s, f i) y = ∑ i ∈ s, polarV (f i) y := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    simp [polarV]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, p13e7Aux_polarV_add_left, ih]

theorem p13e7Aux_polarV_sum_right {ι : Type*} (s : Finset ι) (x : V) (f : ι → V) :
    polarV x (∑ i ∈ s, f i) = ∑ i ∈ s, polarV x (f i) :=
  map_sum (p13e7PolarHom x) f s

theorem p13e7_polarV_coord_coord
    (u v : Fin 7 → ZMod 3) :
    polarV (p13e7Coord u) (p13e7Coord v) = 2 * ∑ i, u i * v i := by
  have hcoord : ∀ w : Fin 7 → ZMod 3, p13e7Coord w =
      ∑ i, w i • (redV (frameE7.root i) : V) := by
    intro w
    funext k
    rfl
  rw [hcoord u, hcoord v]
  rw [p13e7Aux_polarV_sum_left]
  have hright : ∀ i : Fin 7,
      polarV (redV (frameE7.root i)) (∑ j, v j • (redV (frameE7.root j) : V)) =
        ∑ j, v j * polarV (redV (frameE7.root i)) (redV (frameE7.root j)) := by
    intro i
    rw [p13e7Aux_polarV_sum_right]
    simp [p13e7Aux_polarV_smul_right]
  simp only [p13e7Aux_polarV_smul_left, hright]
  have hxij : ∀ i j : Fin 7,
      polarV (redV (frameE7.root i)) (redV (frameE7.root j)) =
        if i = j then (2 : ZMod 3) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [← polar_qForm, e7LiftP11_polarV_redV]
      rw [TableBExcTwo.iform_self_eq_two_of_isRoot frameE7.symm_one (frameE7.isRoot i)]
      norm_num
    · rw [if_neg h, ← polar_qForm, e7LiftP11_polarV_redV, frameE7.orth i j h]
      norm_num
  calc
    ∑ i, u i * ∑ j, v j * polarV (redV (frameE7.root i)) (redV (frameE7.root j))
        = ∑ i, u i * (v i * 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · rw [hxij i i, if_pos rfl]
          · intro j _ hj
            rw [hxij i j, if_neg (Ne.symm hj)]
            simp
          · intro hi; simp at hi
    _ = 2 * ∑ i, u i * v i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

theorem p13e7Coord_injective :
    Function.Injective (p13e7Coord) := by
  intro u v h
  have hzero : p13e7Coord (u - v) = 0 := by
    rw [map_sub, h, sub_self]
  funext i
  have h2 : polarV (p13e7Coord (Pi.single i 1)) (p13e7Coord (u - v)) = 0 := by
    rw [hzero]
    simp [polarV]
  rw [p13e7_polarV_coord_coord] at h2
  rw [Finset.sum_eq_single i] at h2
  · simp only [Pi.single_eq_same, one_mul] at h2
    have h3 : (u - v) i = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (by decide)
      · exact h
    exact sub_eq_zero.mp h3
  · intro j _ hj
    simp [hj]
  · intro hi
    simp at hi

theorem p13e7Coord_surjective :
    Function.Surjective (p13e7Coord) :=
  Finite.injective_iff_surjective.mp p13e7Coord_injective

theorem p13e7Aux_frameCoord_eq
    (γ : Fin Tag.E7.rank → ℤ) (s : V) :
    ∑ j, (γ j : ZMod 3) * ExcFrames.frameCoord .E7 3 s j = polarV (redV γ) s := by
  obtain ⟨σ, rfl⟩ := redV_surj s
  rw [← polar_qForm, e7LiftP11_polarV_redV, iform]
  simp only [ExcFrames.frameCoord, redV]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem p13e7_rootChar_fam
    {L : Type} [Field L] {ζ : Lˣ} (hζ : ζ ^ 3 = 1)
    (s : V) (γ : Fin Tag.E7.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 3 s)) γ =
      CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (.ofAdd (polarV (redV γ) s)) := by
  rw [CFSG.StandardType.NoOffE8Five.rootChar_zetaVec, p13e7Aux_frameCoord_eq γ s]

theorem p13e7_rootChar_fam_eq_one
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (s : V) (γ : Fin Tag.E7.rank → ℤ) :
    rootChar (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord .E7 3 s)) γ = 1 ↔
      polarV (redV γ) s = 0 := by
  rw [p13e7_rootChar_fam hζ]
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd (polarV (redV γ) s) = (1 : Multiplicative (ZMod 3)) :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [h, map_one])
    exact Multiplicative.ofAdd.injective (by simpa using h1)
  · intro h
    rw [h]
    simp

noncomputable def p13e7Aux_polarLin (ψ : V) : V →ₗ[ZMod 3] ZMod 3 where
  toFun := polarV ψ
  map_add' := p13e7_polarV_add_right ψ
  map_smul' := fun c x => p13e7Aux_polarV_smul_right c ψ x

theorem p13e7_polarV_nondegenerate_right (a b : V)
    (h : ∀ y, polarV y a = polarV y b) : a = b := by
  have hsep : LinearMap.SeparatingRight qForm.polarBilin :=
    (QuadraticMap.nondegenerate_polar_iff.mpr e7QForm_nondegenerate).2
  have hzero : a - b = 0 := by
    refine hsep (a - b) ?_
    intro y
    rw [QuadraticMap.polarBilin_apply_apply, polar_qForm]
    rw [show polarV y (a - b) = polarV y a - polarV y b by
      rw [sub_eq_add_neg, p13e7_polarV_add_right, p13e7_polarV_neg_right]; ring]
    rw [h y, sub_self]
  exact sub_eq_zero.mp hzero

theorem p13e7_exists_smul_of_forall {ψ x : V} (_hψ : ψ ≠ 0)
    (h : ∀ s, polarV ψ s = 0 → polarV x s = 0) : ∃ c : ZMod 3, x = c • ψ := by
  have hker : LinearMap.ker (p13e7Aux_polarLin ψ) ≤ LinearMap.ker (p13e7Aux_polarLin x) := by
    intro s hs
    rw [LinearMap.mem_ker] at hs ⊢
    exact h s hs
  have hmem : p13e7Aux_polarLin x ∈ Submodule.span (ZMod 3) {p13e7Aux_polarLin ψ} := by
    have h := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => p13e7Aux_polarLin ψ)
      (K := p13e7Aux_polarLin x) (by simpa using hker)
    simpa using h
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  apply p13e7_polarV_nondegenerate_right
  intro y
  have hcy : c * polarV ψ y = polarV x y := by
    have := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f y) hc
    simpa [p13e7Aux_polarLin] using this
  rw [p13e7Aux_polarV_symm y x, ← hcy, p13e7Aux_polarV_smul_right, p13e7Aux_polarV_symm y ψ]

theorem p13e7_polarV_rhoEquiv
    (w : WeylGroup Tag.E7) (x y : V) :
    polarV (rhoEquiv w x) (rhoEquiv w y) = polarV x y := by
  rw [← polar_qForm, ← polar_qForm]
  have hmem := rhoEquiv_mem w
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hmem
  have h2 := hmem x
  have h3 := hmem y
  have h1 : qForm ((rhoEquiv w) x + (rhoEquiv w) y) = qForm (x + y) := by
    rw [← map_add]
    exact hmem (x + y)
  simp only [QuadraticMap.polar]
  rw [h1, h2, h3]

theorem p13e7Aux_zmod3_eq_one_or_two {c : ZMod 3} (hc : c ≠ 0) : c = 1 ∨ c = 2 := by
  revert c
  decide


section Hyp


@[expose] noncomputable def p13e7Hyp (K : Type) [Field K] [CharP K 2] (ψ : V) :
    Subgroup (adjointGroup .E7 K) :=
  (p13e7HypVec ψ).toSubgroup.map (tE K frameE7)

end Hyp

@[expose] noncomputable def p13e7Fam {L : Type} [Field L] (ω : Lˣ) (hω3 : ω ^ 3 = 1) (ψ : V) :
    Set (Fin Tag.E7.rank → Lˣ) :=
  {a | ∃ s : V, polarV ψ s = 0 ∧
    a = TableBExc.E6Three.zetaVec ω hω3 (ExcFrames.frameCoord .E7 3 s)}

section E7


variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem p13e7_exists_hyp {F : Subgroup (adjointGroup .E7 K)} (hF : F ≤ (tE K frameE7).range)
    (hidx : F.relIndex (tE K frameE7).range = 3) : ∃ ψ : V, ψ ≠ 0 ∧ F = p13e7Hyp K ψ := by
  classical
  have hT : Nat.card (tE K frameE7).range = 3 ^ 7 := by
    calc
      Nat.card (tE K frameE7).range = Nat.card (Multiplicative (Fin 7 → ZMod 3)) :=
        Nat.card_congr (Equiv.ofInjective (tE K frameE7) (tE_injective frameE7)).symm
      _ = Nat.card (Fin 7 → ZMod 3) := Nat.card_congr Multiplicative.toAdd
      _ = 3 ^ 7 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hFcard : Nat.card F = 3 ^ 6 := by
    have h := Subgroup.relIndex_mul_card F (tE K frameE7).range
    rw [hidx, inf_eq_left.mpr hF, hT] at h
    have h3 : (3 : ℕ) ^ 7 = 3 * 3 ^ 6 := by norm_num
    rw [h3] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  let X : AddSubgroup (Fin 7 → ZMod 3) :=
    AddSubgroup.toSubgroup.symm (F.comap (tE K frameE7))
  have hXmap : X.toSubgroup.map (tE K frameE7) = F := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_comap.mp hx
    · intro hy
      obtain ⟨v, hv⟩ := hF hy
      refine Subgroup.mem_map.mpr ⟨v, ?_, hv⟩
      rw [show X.toSubgroup = F.comap (tE K frameE7) from rfl, Subgroup.mem_comap, hv]
      exact hy
  have hXcard : Nat.card X = 3 ^ 6 := by
    have h1 : Nat.card X = Nat.card X.toSubgroup := by
      refine Nat.card_congr ?_
      exact { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
              left_inv := fun x => rfl, right_inv := fun x => rfl }
    rw [h1]
    have h2 : Nat.card X.toSubgroup = Nat.card F := by
      rw [← hXmap]
      exact (Subgroup.card_map_of_injective (tE_injective frameE7)).symm
    rw [h2]
    exact hFcard
  obtain ⟨lam, hlam, hKsub⟩ :=
    exists_functional_mem_of_card (n := 7) (by norm_num) X (by simpa using hXcard)
  let f : (Fin 7 → ZMod 3) →+ ZMod 3 :=
    AddMonoidHom.mk' (fun v => dotZ3 v lam) (by
      intro x y
      simp [dotZ3, add_mul, Finset.sum_add_distrib])
  let Kker : AddSubgroup (Fin 7 → ZMod 3) := f.ker
  have hKmem : ∀ w, w ∈ Kker ↔ dotZ3 w lam = 0 := by
    intro w
    rfl
  have hf_surj : Function.Surjective f := by
    intro c
    obtain ⟨i, hi⟩ : ∃ i, lam i ≠ 0 := by
      by_contra h
      apply hlam
      funext i
      by_contra h'
      exact h ⟨i, h'⟩
    refine ⟨Pi.single i (c / lam i), ?_⟩
    simp only [f, AddMonoidHom.mk'_apply, dotZ3, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, div_mul_cancel₀]
      exact hi
    · intro j _ hj
      simp [hj]
    · intro hi'; simp at hi'
  have hKcard : Nat.card Kker = 3 ^ 6 := by
    have h := AddSubgroup.card_ker_mul_card_range f
    have hrange : f.range = ⊤ := AddMonoidHom.range_eq_top.mpr hf_surj
    rw [hrange] at h
    have htop : Nat.card (⊤ : AddSubgroup (ZMod 3)) = 3 := by
      rw [AddSubgroup.card_top, Nat.card_zmod]
    rw [htop] at h
    have hG : Nat.card (Fin 7 → ZMod 3) = 3 ^ 7 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [hG] at h
    have h3 : (3 : ℕ) ^ 7 = 3 ^ 6 * 3 := by norm_num
    rw [h3] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hXK : X = Kker := by
    refine (AddSubgroup.eq_of_le_of_card_ge (H := Kker) (K := X) ?_ ?_).symm
    · intro w hw
      exact hKsub w ((hKmem w).mp hw)
    · rw [hXcard, hKcard]
  set ψ : V := p13e7Coord ((2 : ZMod 3) • lam) with hψdef
  have hHypVec : p13e7HypVec ψ = X := by
    ext v
    rw [mem_p13e7HypVec, hXK]
    show polarV ψ (p13e7Coord v) = 0 ↔ dotZ3 v lam = 0
    have hpolar := p13e7_polarV_coord_coord ((2 : ZMod 3) • lam) v
    rw [hψdef, hpolar]
    have hsum : 2 * ∑ i, ((2 : ZMod 3) • lam) i * v i = ∑ i, v i * lam i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring_nf
      have h4 : (4 : ZMod 3) = 1 := by decide
      rw [h4]
      ring
    rw [hsum]
    rfl
  have hHyp : p13e7Hyp K ψ = F := by
    show (p13e7HypVec ψ).toSubgroup.map (tE K frameE7) = F
    rw [hHypVec, hXmap]
  have hψ0 : ψ ≠ 0 := by
    intro h
    have h' : p13e7Coord ((2 : ZMod 3) • lam) = 0 := h
    have h2 : (2 : ZMod 3) • lam = 0 :=
      p13e7Coord_injective (by rw [map_zero]; exact h')
    have h3 : lam = 0 := by
      rcases smul_eq_zero.mp h2 with h2' | h2'
      · exact absurd h2' (by decide)
      · exact h2'
    exact hlam h3
  exact ⟨ψ, hψ0, hHyp.symm⟩

theorem p13e7_famKernel {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3) (hω3 : ω ^ 3 = 1)
    {ψ : V} (hψ : ψ ≠ 0) :
    famKernel (p13e7Fam ω hω3 ψ) = {α | IsRoot Tag.E7 α ∧ (redV α = ψ ∨ redV α = -ψ)} := by
  ext α
  simp only [famKernel, p13e7Fam, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hα, hker⟩
    have horth : ∀ s : V, polarV ψ s = 0 → polarV (redV α) s = 0 := by
      intro s hs
      have h := hker _ ⟨s, hs, rfl⟩
      rwa [p13e7_rootChar_fam_eq_one hω hω3 s α] at h
    obtain ⟨c, hc⟩ := p13e7_exists_smul_of_forall hψ horth
    have hc0 : c ≠ 0 := by
      intro hc0
      exact p13a2_E7_redV_ne_zero α hα (by rw [hc, hc0, zero_smul])
    refine ⟨hα, ?_⟩
    rcases p13e7Aux_zmod3_eq_one_or_two hc0 with h1 | h2
    · left
      rw [hc, h1, one_smul]
    · right
      rw [hc, h2, show (2 : ZMod 3) • ψ = -ψ by rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul]]
  · rintro ⟨hα, h | h⟩
    · refine ⟨hα, ?_⟩
      intro a ha
      obtain ⟨s, hs, rfl⟩ := ha
      rw [p13e7_rootChar_fam_eq_one hω hω3 s α]
      rw [h]
      exact hs
    · refine ⟨hα, ?_⟩
      intro a ha
      obtain ⟨s, hs, rfl⟩ := ha
      rw [p13e7_rootChar_fam_eq_one hω hω3 s α]
      rw [h, p13e7Aux_polarV_neg_left, hs, neg_zero]

theorem p13e7_famStabilizer {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    (hω3 : ω ^ 3 = 1) (ψ : V) :
    famStabilizer (p13e7Fam ω hω3 ψ) = {w | ∀ x : V, polarV ψ x = 0 → rhoEquiv w x = x} := by
  ext w
  simp only [famStabilizer, p13e7Fam, rootCharStabilizer, Set.mem_setOf_eq]
  constructor
  · intro h s hs
    have h1 : ∀ y : V, polarV (rhoEquiv w y) (rhoEquiv w s) = polarV (rhoEquiv w y) s := by
      intro y
      obtain ⟨v, rfl⟩ := redV_surj y
      have hmem : TableBExc.E6Three.zetaVec ω hω3 (ExcFrames.frameCoord .E7 3 s) ∈
          p13e7Fam ω hω3 ψ := ⟨s, hs, rfl⟩
      have h2 := h _ hmem v
      rw [p13e7_rootChar_fam hω3, p13e7_rootChar_fam hω3] at h2
      have h3 : polarV (rhoEquiv w (redV v)) s = polarV (redV v) s := by
        have h4 := (CFSG.RankThree.CentralCover.zmodPowHom_injective hω hω3) h2
        rw [rhoEquiv_redV]
        exact Multiplicative.ofAdd.injective h4
      rw [p13e7_polarV_rhoEquiv]
      exact h3.symm
    apply p13e7_polarV_nondegenerate_right
    intro z
    obtain ⟨y, rfl⟩ := (rhoEquiv w).surjective z
    exact h1 y
  · intro h a ha v
    obtain ⟨s, hs, rfl⟩ := ha
    rw [p13e7_rootChar_fam hω3, p13e7_rootChar_fam hω3]
    have hws : rhoEquiv w s = s := h s hs
    rw [← rhoEquiv_redV,
      show polarV (rhoEquiv w (redV v)) s =
        polarV (rhoEquiv w (redV v)) (rhoEquiv w s) by rw [hws],
      p13e7_polarV_rhoEquiv]

theorem p13e7_mem_famCentralizer {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) (hω3 : ω ^ 3 = 1) {ψ : V} {c : adjointGroup .E7 K}
    (hc : c ∈ Subgroup.centralizer (p13e7Hyp K ψ : Set (adjointGroup .E7 K))) :
    (langElt frameE7 hω)⁻¹ * adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2)) c *
        langElt frameE7 hω ∈ LayerSixE.famCentralizer (p13e7Fam ω hω3 ψ) := by
  classical
  have hfull : ∀ a : Fin Tag.E7.rank → (FiniteField.Extension K 2 2)ˣ,
      rootDiagUnit .E7 a ∈ torusGroup .E7 (FiniteField.Extension K 2 2) :=
    fun a => TableBExc.full_of_E7_E8 (Or.inl rfl) a
  rw [LayerSixE.mem_famCentralizer]
  intro a ha
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := p13e7Coord_surjective s
  have htv : tE K frameE7 (Multiplicative.ofAdd v) ∈ p13e7Hyp K ψ := by
    refine Subgroup.mem_map.mpr ⟨Multiplicative.ofAdd v, ?_, rfl⟩
    show v ∈ p13e7HypVec ψ
    rw [mem_p13e7HypVec]
    exact hs
  have hcomm : tE K frameE7 (Multiplicative.ofAdd v) * c =
      c * tE K frameE7 (Multiplicative.ofAdd v) :=
    (Subgroup.mem_centralizer_iff.1 hc) _ htv
  let Gm : ModGL .E7 (FiniteField.Extension K 2 2) := langElt frameE7 hω
  let Am : ModGL .E7 (FiniteField.Extension K 2 2) :=
    adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2))
      (tE K frameE7 (Multiplicative.ofAdd v))
  let Cm : ModGL .E7 (FiniteField.Extension K 2 2) :=
    adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2)) c
  have hAcomm : Am * Cm = Cm * Am := by
    have hιcomm : adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2))
          (tE K frameE7 (Multiplicative.ofAdd v)) *
        adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2)) c =
        adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2)) c *
        adjointMap .E7 (algebraMap K (FiniteField.Extension K 2 2))
          (tE K frameE7 (Multiplicative.ofAdd v)) := by
      rw [← map_mul, ← map_mul, hcomm]
    simpa [Am, Cm] using
      congrArg (fun x : adjointGroup .E7 (FiniteField.Extension K 2 2) =>
        (x : ModGL .E7 (FiniteField.Extension K 2 2))) hιcomm
  have hdiag : (ExcFrames.frameDiag ω hω3 (p13e7Coord v) :
      ModGL .E7 (FiniteField.Extension K 2 2)) = Gm⁻¹ * Am * Gm := by
    have h := ExcFrameIso.adjointMap_tE_eq (τ := .E7) (d := 6) frameE7.symm_one frameE7
      hω hω3 hfull v
    have h' : Am = Gm * ExcFrames.frameDiag ω hω3 (p13e7Coord v) * Gm⁻¹ := by
      have hc := congrArg (fun x : adjointGroup .E7 (FiniteField.Extension K 2 2) =>
        (x : ModGL .E7 (FiniteField.Extension K 2 2))) h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
      exact hc
    rw [h']
    group
  show (rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ω hω3
      (ExcFrames.frameCoord .E7 3 (p13e7Coord v))) :
        ModGL .E7 (FiniteField.Extension K 2 2)) * (Gm⁻¹ * Cm * Gm) *
      (rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ω hω3
        (ExcFrames.frameCoord .E7 3 (p13e7Coord v))) :
        ModGL .E7 (FiniteField.Extension K 2 2))⁻¹ = Gm⁻¹ * Cm * Gm
  rw [show (rootDiagUnit .E7 (TableBExc.E6Three.zetaVec ω hω3
        (ExcFrames.frameCoord .E7 3 (p13e7Coord v))) :
          ModGL .E7 (FiniteField.Extension K 2 2)) =
      ExcFrames.frameDiag ω hω3 (p13e7Coord v) from rfl, hdiag]
  calc
    (Gm⁻¹ * Am * Gm) * (Gm⁻¹ * Cm * Gm) * (Gm⁻¹ * Am * Gm)⁻¹
        = Gm⁻¹ * (Am * Cm * Am⁻¹) * Gm := by group
    _ = Gm⁻¹ * (Cm * Am * Am⁻¹) * Gm := by rw [hAcomm]
    _ = Gm⁻¹ * Cm * Gm := by group

end E7

end CFSG.StandardType.FrameRoute
