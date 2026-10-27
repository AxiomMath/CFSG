module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplit
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem rawDatum_elim_const' {lab : LargeEvenLabel} {Q : Prop}
    (h : LargeEvenRawDatum lab (fun _ _ _ _ => Q)) : Q := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear, LargeEvenRecipeUnitary,
    LargeEvenRecipeSymplectic, LargeEvenRecipeOmegaPlus, LargeEvenRecipeOmegaMinus,
    LargeEvenRecipeChevalley, LargeEvenRecipeTwisted, LargeEvenRecipeSuzuki,
    LargeEvenRecipeG2Derived, LargeEvenRecipeTwF4Inherited] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact hq)

theorem eq_of_ggLabelIso_of_e6Tag {labJ lab : LargeEvenLabel}
    (h : GGLabelIso labJ lab) (hP : labJ.tag = .E6 ∨ labJ.tag = .twE6) : labJ = lab := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases hP with h5 | h5 <;> rcases h1 with h6 | h6 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twA := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all
  · rcases h with ⟨-, h1⟩
    have ht : t = .A := congrArg LargeEvenLabel.tag h1
    rcases hP with h5 | h5 <;> simp_all

private theorem e6_split_concl {lab : LargeEvenLabel} (hsplit : LargeEvenSplit 3 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) (hn : lab.tag = .E6 → 2 ≤ lab.n) :
    (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨t, l, n⟩ := lab
  rcases hsplit with ⟨hunt, hdiv⟩ | ⟨hunt, -, hdiv⟩ | ⟨htag', hdiv⟩ | ⟨hn1, _⟩
  · rcases htag with rfl | rfl
    · exact Or.inl ⟨rfl, hdiv⟩
    · exact absurd hunt (by simp [LargeEvenUntwisted])
  · rcases htag with rfl | rfl
    · exact absurd trivial (by simpa [LargeEvenUntwisted] using hunt)
    · exact Or.inr ⟨rfl, hdiv⟩
  · rcases htag with rfl | rfl <;> rcases htag' with htag'' | htag'' <;>
      exact absurd htag'' (by simp)
  · rcases htag with rfl | rfl
    · exact absurd (hn rfl) (by rw [hn1]; omega)
    · exact Or.inr ⟨rfl, by rw [hn1]; norm_num⟩

section Certificates

theorem e6eps_marking_labels
    {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6 ∨ t = .twE6) X A δ J)
    (hq : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨-, lab0, hlab0, hraw0⟩ := hD.2.2.2
  have htag0 : lab0.tag = .E6 ∨ lab0.tag = .twE6 :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hraw0)
  have hHas0 : GGHasLabel lab0 (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
  obtain ⟨-, lab1, hlab1, hraw1⟩ := hq
  have hqprop1 : lab1.tag = .E6 → 2 ≤ lab1.n :=
    rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hraw1)
  have hHas1 : GGHasLabel lab1 (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw1
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  intro P hP
  obtain ⟨-, lab, hlab, hraw⟩ := hP
  have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have heq0 : lab0 = lab :=
    eq_of_ggLabelIso_of_e6Tag (hrigid lab0 lab _ hlab0 hlab hHas0 hHas) htag0
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 := heq0 ▸ htag0
  have heq1 : lab = lab1 :=
    eq_of_ggLabelIso_of_e6Tag (hrigid lab lab1 _ hlab hlab1 hHas hHas1) htag
  have hn : lab.tag = .E6 → 2 ≤ lab.n := by
    intro hE6
    have h2 := hqprop1 (by simpa [heq1] using hE6)
    simpa [heq1] using h2
  refine ⟨hX, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono (fun R _ I F hq' => ?_) hraw
  obtain ⟨θ, hPθ⟩ := hq'.2.2
  exact ⟨hq'.1, hq'.2.1, θ, hPθ, fun hsplit => e6_split_concl hsplit htag hn⟩

end Certificates

end CFSG.StandardType.TablePThreeKG

end
