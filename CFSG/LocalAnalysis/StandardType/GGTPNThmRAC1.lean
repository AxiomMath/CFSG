module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem not_ggHasLabel_a24_of_ggKacRA (hrig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore 3 A σ J) (h8 : GGTPNOnlyComp 3 σ J) (hm : GGTPNMarked 3 S A)
    {labX : LargeEvenLabel} (hΛX : LargeEvenInLambda2 labX) (hRA : GGKacRA labX 3)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ¬ GGHasLabel ⟨.A, 2, 2⟩ (↥J ⧸ Subgroup.center ↥J) := by
  intro hJ
  obtain ⟨t, r, n⟩ := labX
  have hΛ22 : LargeEvenInLambda2 ⟨.A, 2, 2⟩ := by simp [LargeEvenInLambda2]
  have hm' : GGTPNMarked 3 (fun _ lab => lab = ⟨t, r, n⟩) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  rcases split_or_fieldType_of_ggKacRA Nat.prime_three hloc h8 hRA hm' with
    ⟨a, ds, hsum, hne, hlt, hds, hcase⟩ | ⟨-, -, hcase⟩
  · rcases hcase with ⟨hΛ', hJ'⟩ | ⟨-, -, hΛ', hJ'⟩
    · have hlab : (⟨t, a - 1, n⟩ : LargeEvenLabel) = ⟨.A, 2, 2⟩ := by
        rcases ggLabelIso_typeA_cases hrig (by norm_num) hΛ' hΛ22 hJ' hJ with h | ⟨h23, -⟩
        · exact h
        · exact absurd h23 (by norm_num)
      have ht : t = .A := congrArg LargeEvenLabel.tag hlab
      have ha1 : a - 1 = 2 := congrArg LargeEvenLabel.rank hlab
      have ha : a = 3 := by omega
      have hones : ∀ x ∈ ds, x = 1 := by
        intro x hx
        rcases hds x hx with h1 | ⟨htw, -, -⟩
        · exact h1
        · exact absurd (ht.symm.trans htw) (by decide)
      have hlen : ds.sum = ds.length := by
        simpa using List.sum_eq_length_nsmul ds 1 hones
      rcases hRA with ⟨-, hdv, -⟩ | ⟨htw, -, -⟩
      · obtain ⟨k, hk⟩ := hdv
        have hpos := List.length_pos_of_ne_nil hne
        omega
      · exact absurd (ht.symm.trans htw) (by decide)
    · have hlab : (⟨.A, 1, n⟩ : LargeEvenLabel) = ⟨.A, 2, 2⟩ := by
        rcases ggLabelIso_typeA_cases hrig (by norm_num) hΛ' hΛ22 hJ' hJ with h | ⟨h23, -⟩
        · exact h
        · exact absurd h23 (by norm_num)
      have h12 : (1 : ℕ) = 2 := congrArg LargeEvenLabel.rank hlab
      omega
  · rcases hcase with ⟨-, hΛ', hJ'⟩ | ⟨-, -, hΛ', hJ'⟩
    · have hlab : (⟨.A, (r + 1) / 3 - 1, 3 * n⟩ : LargeEvenLabel) = ⟨.A, 2, 2⟩ := by
        rcases ggLabelIso_typeA_cases hrig (by norm_num) hΛ' hΛ22 hJ' hJ with h | ⟨h23, -⟩
        · exact h
        · exact absurd h23 (by norm_num)
      have hn : 3 * n = 2 := congrArg LargeEvenLabel.n hlab
      omega
    · have hlab : (⟨.twA, (r + 1) / 3 - 1, 3 * n⟩ : LargeEvenLabel) = ⟨.A, 2, 2⟩ := by
        rcases ggLabelIso_typeA_cases hrig (by norm_num) hΛ' hΛ22 hJ' hJ with h | ⟨h23, -⟩
        · exact h
        · exact absurd h23 (by norm_num)
      exact absurd (congrArg LargeEvenLabel.tag hlab) (by simp)

theorem ggTablePKnownR_a24RA (hrig : GGLabelRigidInput) : GGTablePKnownR GGRegimeA24RA := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, rfl⟩, hRA⟩ := hr
  subst hp3
  obtain ⟨⟨hloc, -, -, -, -, -, h8, hm⟩, -⟩ := hd
  exact (not_ggHasLabel_a24_of_ggKacRA hrig hloc h8 hm hΛX hRA hhX hhJ).elim

end CFSG.StandardType

end
