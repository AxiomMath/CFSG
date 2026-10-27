module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem tex_eq_of_ggLabelIso_of_exc {lab labX : LargeEvenLabel}
    (hexc : GGTPNExcTag labX.tag) (h : GGLabelIso lab labX) : lab = labX := by
  unfold GGLabelIso at h
  rcases h with heq | hBC | ⟨-, hX⟩ | ⟨-, hX⟩ | ⟨-, hX⟩ | ⟨-, hX⟩ | ⟨-, hX⟩ | ⟨hX, -⟩
  · exact heq
  · obtain ⟨-, hbc, -⟩ := hBC
    rcases hbc with hb | hc
    · rw [hb] at hexc; simp [GGTPNExcTag] at hexc
    · rw [hc] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc
  · rw [hX] at hexc; simp [GGTPNExcTag] at hexc

theorem ggTPN_excCover
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    (hm : GGTPNMarked p (fun _ _ => True) A) {labX : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 labX) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hexc : GGTPNExcTag labX.tag) :
    GGKacExcPair labX p ∨ (p = 7 ∧ labX = ⟨.E6, 0, 1⟩) := by
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  unfold GGTPNMarked at hm
  obtain ⟨lab, hΛlab, hlabHas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hm
  have hiso : GGLabelIso lab labX :=
    hrig lab labX (X ⧸ Subgroup.center X) hΛlab hΛ hlabHas hhX
  have heq : lab = labX := tex_eq_of_ggLabelIso_of_exc hexc hiso
  subst lab
  have hhalf : LargeEvenHalfSplit p labX (Subgroup.center X = ⊥) := hP.2.1
  rcases largeEvenHalfSplit_dvd hΛ hhalf with hdvd | ⟨hp7, hA8 | hE6⟩
  · left
    have hfac : (2 ^ labX.n) ^ 2 - 1 = (2 ^ labX.n - 1) * (2 ^ labX.n + 1) := by
      rw [pow_two, mul_self_tsub_one, mul_comm]
    rw [hfac] at hdvd
    refine ⟨hp, hp2, (hp.dvd_mul).mp hdvd, ?_⟩
    unfold GGTPNExcTag at hexc
    tauto
  · exfalso
    rw [hA8] at hexc
    simp [GGTPNExcTag] at hexc
  · exact Or.inr ⟨hp7, hE6⟩


end CFSG.StandardType

end
