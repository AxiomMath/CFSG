module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Types

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

private theorem false_of_binaryNaturalSL_column {V : Type} [CommGroup V] {F : Type} [Field F]
    [Finite F] {d r : ℕ} {D X : Subgroup (MulAut V)}
    {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}
    (hM : IsMatModel D X β ρ σ) (hF2 : Nat.card F = 2) (j : Fin r)
    (hN : BinaryNaturalSL D (matColSub β j) ⊥ 2 2) : False := by
  classical
  let C : Subgroup V := matColSub β j
  obtain ⟨f, hf_mem, hf_act, hf_ne1, hf_ne_id⟩ := exists_endo_of_binaryNaturalSL hN
  have hf_memC : ∀ u : ↥C, f u ∈ C := hf_mem
  let fC : ↥C →* ↥C := f.codRestrict C hf_memC
  let e : ↥C ≃* Multiplicative (Fin d → F) := matColEquiv β j
  let φ : (Fin d → F) →+ (Fin d → F) :=
    { toFun := fun w => Multiplicative.toAdd (e (fC (e.symm (Multiplicative.ofAdd w))))
      map_zero' := by
        simp
      map_add' := by
        intro x y
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  have hφ_apply : ∀ w : Fin d → F,
      φ w = Multiplicative.toAdd (e (fC (e.symm (Multiplicative.ofAdd w)))) := fun _ => rfl
  have hφcomm : ∀ (g : ↥D) (w : Fin d → F),
      φ (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F).mulVec w) =
        (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F).mulVec (φ w)) := by
    intro g w
    let u : ↥C := e.symm (Multiplicative.ofAdd w)
    have heu : e u = Multiplicative.ofAdd w := by simp [u]
    let u' : ↥C := ⟨(g : MulAut V) (u : V),
      stableUnder_matColSub hM j g g.2 (u : V) u.2⟩
    have hu' : (u' : V) = (g : MulAut V) (u : V) := rfl
    have hgu' : e u' = Multiplicative.ofAdd
        (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F).mulVec w) := by
      apply Multiplicative.toAdd.injective
      have h2 : Multiplicative.toAdd (e u') =
          (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
            Matrix (Fin d) (Fin d) F).mulVec (Multiplicative.toAdd (e u))) :=
        matColEquiv_act hM j g u u' hu'
      rw [heu, toAdd_ofAdd] at h2
      rw [h2, toAdd_ofAdd]
    have hleft : φ (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F).mulVec w) = Multiplicative.toAdd (e (fC u')) := by
      rw [hφ_apply]
      have h1 : e.symm (Multiplicative.ofAdd
          (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
            Matrix (Fin d) (Fin d) F).mulVec w)) = u' := by
        rw [← hgu', MulEquiv.symm_apply_apply]
      rw [h1]
    have hright : Multiplicative.toAdd (e (fC u')) =
        (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
          Matrix (Fin d) (Fin d) F).mulVec (φ w)) := by
      have hfcu : fC u' = (⟨f u', hf_mem u'⟩ : ↥C) := rfl
      have hsub : (⟨f u', hf_mem u'⟩ : ↥C) =
          (⟨(g : MulAut V) (f u),
            stableUnder_matColSub hM j g g.2 (f u) (hf_mem u)⟩ : ↥C) :=
        Subtype.ext (hf_act g g.2 u u' hu')
      rw [hfcu, hsub]
      have hact2 : Multiplicative.toAdd (e (⟨(g : MulAut V) (f u),
            stableUnder_matColSub hM j g g.2 (f u) (hf_mem u)⟩ : ↥C)) =
          (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
            Matrix (Fin d) (Fin d) F).mulVec
              (Multiplicative.toAdd (e (⟨f u, hf_mem u⟩ : ↥C)))) :=
        matColEquiv_act hM j g (⟨f u, hf_mem u⟩ : ↥C)
          (⟨(g : MulAut V) (f u),
            stableUnder_matColSub hM j g g.2 (f u) (hf_mem u)⟩ : ↥C) rfl
      rw [hact2]
      have hφw : φ w = Multiplicative.toAdd (e (fC u)) := by
        rw [hφ_apply]
      have hfcu₂ : fC u = (⟨f u, hf_mem u⟩ : ↥C) := rfl
      rw [hφw, hfcu₂]
    exact hleft.trans hright
  obtain ⟨c, hc⟩ := hM.comm_F φ hφcomm
  have hc01 : c = 0 ∨ c = 1 := CFSG.Quasithin.G64.eq_zero_or_eq_one_of_card_two hF2 c
  rcases hc01 with hc0 | hc1
  · obtain ⟨u, hu⟩ := hf_ne1
    have hw : φ (Multiplicative.toAdd (e u)) = 0 := by
      rw [hc (Multiplicative.toAdd (e u)), hc0, zero_smul]
    have h2 : Multiplicative.toAdd (e (fC u)) = 0 := by
      rw [hφ_apply] at hw
      simpa using hw
    have h3 : e (fC u) = 1 := Multiplicative.toAdd.injective (by simpa using h2)
    have h4 : fC u = 1 := e.injective (by simpa using h3)
    have h5 : f u = 1 := by
      have h6 : (fC u : V) = ((1 : ↥C) : V) := congrArg (fun w : ↥C => (w : V)) h4
      simpa [fC] using h6
    exact hu h5
  · obtain ⟨u, hu⟩ := hf_ne_id
    have hw : φ (Multiplicative.toAdd (e u)) = Multiplicative.toAdd (e u) := by
      rw [hc (Multiplicative.toAdd (e u)), hc1, one_smul]
    have h2 : Multiplicative.toAdd (e (fC u)) = Multiplicative.toAdd (e u) := by
      rw [hφ_apply] at hw
      simpa using hw
    have h3 : e (fC u) = e u := Multiplicative.toAdd.injective h2
    have h4 : fC u = u := e.injective h3
    have h5 : f u = (u : V) := by
      have h6 : (fC u : V) = (u : V) := congrArg (fun w : ↥C => (w : V)) h4
      simpa [fC] using h6
    exact hu h5

theorem matModel_column_cases {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F] {d r : ℕ}
    {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F} {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F}
    (hM : IsMatModel D X β ρ σ) (hD : IsAlt ↥D 5) (j : Fin r) :
    (Nat.card F = 2 ∧ d = 4 ∧ AlternatingNatural D (matColSub β j) ⊥ 5) ∨
      (Nat.card F = 4 ∧ d = 2) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcardD : Nat.card ↥D = 60 := by
    obtain ⟨e⟩ := hD
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hDne : D ≠ ⊥ := ne_bot_of_isAlt_five hD
  have hd : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := by omega
    have hcardV : Nat.card V = 1 := by
      rw [card_eq_card_pow_of_matEquiv β, hd0']
      simp
    have hsubV : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hcardV).1
    have hDbot : D = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact MulEquiv.ext fun v => Subsingleton.elim _ _
    rw [hDbot, Subgroup.card_bot] at hcardD
    omega
  have hIrr : IsIrrOn D (matColSub β j) ⊥ := isIrrOn_matColSub hM hd j
  have hmv : ∃ g ∈ D, ∃ u ∈ matColSub β j, g u ≠ u :=
    exists_moves_matColSub hM hDne j
  obtain ⟨hcardC, hcls⟩ := a5_irr_classification hV hD hIrr hmv
  have hpoweq : Nat.card F ^ d = 16 := by
    rw [← card_matColSub β j]
    exact hcardC
  have hq2 : 2 ≤ Nat.card F := by
    have h := Finite.one_lt_card (α := F)
    omega
  have hq16 : Nat.card F ≤ 16 := by
    calc Nat.card F ≤ Nat.card F ^ d := Nat.le_self_pow (by omega : d ≠ 0) (Nat.card F)
      _ = 16 := hpoweq
  have hd4 : d ≤ 4 := by
    have h2d : 2 ^ d ≤ 16 := by
      calc 2 ^ d ≤ (Nat.card F) ^ d := Nat.pow_le_pow_left hq2 d
        _ = 16 := hpoweq
    by_contra h
    push Not at h
    have h5 : 5 ≤ d := h
    have h25 : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    norm_num at h25
    omega
  have hqd : (Nat.card F = 2 ∧ d = 4) ∨ (Nat.card F = 4 ∧ d = 2) ∨
      (Nat.card F = 16 ∧ d = 1) := by
    interval_cases hq : Nat.card F <;> interval_cases hd' : d <;>
      (norm_num at hpoweq) <;> norm_num
  rcases hqd with ⟨hF2, hdeq4⟩ | ⟨hF4, hdeq2⟩ | ⟨hF16, hdeq1⟩
  · rcases hcls with hN | hO
    · exact (false_of_binaryNaturalSL_column hM hF2 j hN).elim
    · exact Or.inl ⟨hF2, hdeq4, hO⟩
  · exact Or.inr ⟨hF4, hdeq2⟩
  · subst d
    have hperfD : Group.IsPerfect ↥D := isPerfect_of_isAlt_five hD
    have hρ1 : ρ = 1 :=
      CFSG.RankThree.SubgroupLists.perfect_hom_eq_one_of_commute hperfD ρ
        (fun a _ b _ => CFSG.RankThree.SubgroupLists.gl_fin_one_comm a b)
    have hDbot : D = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro v
      apply β.injective
      have hg1 : ρ ⟨g, hg⟩ = 1 := by rw [hρ1]; rfl
      rw [hM.hρ ⟨g, hg⟩ v, hg1]
      simp
    rw [hDbot, Subgroup.card_bot] at hcardD
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
