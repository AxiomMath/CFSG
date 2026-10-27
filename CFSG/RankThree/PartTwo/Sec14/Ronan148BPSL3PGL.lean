module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Gen
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofRigid

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi Type123)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup)

section Model

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem coe_conjM'_zpow (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (n : ℤ) (m : projImage (slPi π 3 (p ^ f) K)) :
    (((Res8Hess.conjM' hπ hg ^ n) m : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk g ^ n * m * (ProjGenLinGroup.mk g ^ n)⁻¹ := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast]
    exact L3PGL.coe_conjM'_pow hπ hg k m
  · rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
    set σ := Res8Hess.conjM' hπ hg ^ k with hσ
    have h1 := L3PGL.coe_conjM'_pow hπ hg k (σ⁻¹ m)
    rw [← hσ, MulAut.apply_inv_self] at h1
    rw [inv_inv, h1]
    group

end Model

theorem gen_of_pglModel
    {X : Type} [Group X] [Finite X] {P : Subgroup (MulAut X)} (hM : PGLModel X P)
    (hperf : Group.IsPerfect X) :
    sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧ ∀ σ ∈ P, Y.map σ.toMonoidHom ≤ Y} = ⊤ := by
  obtain ⟨π, p, f, K, _, hK, hq, e, y, s, hyH, hy3, hs, hsZ, hs3, hysZ, hcorr⟩ := hM
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hsH : s ∈ glPi π 3 (p ^ f) K := Sec4.slPi_le_glPi hπ hs
  have hperfM : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hgen := ks142L3PGLGenModel_proof π p f K hπ hK hq hperfM y s hyH hsH hy3 hs hsZ hs3 hysZ
  haveI : Finite (projImage (slPi π 3 (p ^ f) K)) := Finite.of_equiv X e.toEquiv
  have hmem : ∀ Y ∈ invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH),
      Y.map e.symm.toMonoidHom ∈ {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧
        ∀ σ ∈ P, Y.map σ.toMonoidHom ≤ Y} := by
    intro Y hY
    obtain ⟨hY3, hYy, hYs⟩ := hY
    refine ⟨by rwa [Subgroup.card_map_of_injective e.symm.injective], ?_⟩
    let Stab : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))) :=
      { carrier := {τ | Y.map τ.toMonoidHom ≤ Y}
        mul_mem' := fun {a b} ha hb => by
          rintro _ ⟨v, hv, rfl⟩
          exact ha ⟨b v, hb ⟨v, hv, rfl⟩, rfl⟩
        one_mem' := by
          change Y.map (1 : MulAut _).toMonoidHom ≤ Y
          rintro _ ⟨w, hw, rfl⟩
          exact hw
        inv_mem' := fun {a} ha => by
          change Y.map a⁻¹.toMonoidHom ≤ Y
          refine L3PGL.map_le_of_map_symm_le ?_
          rw [MulAut.inv_def, MulEquiv.symm_symm]
          exact ha }
    have hsS : Res8Hess.conjM' hπ hsH ∈ Stab := hYs
    have hyS : Res8Hess.conjM' hπ hyH ∈ Stab := hYy
    intro σ hσ
    obtain ⟨i, j, hij⟩ := hcorr σ hσ
    set τ := Res8Hess.conjM' hπ hsH ^ i * Res8Hess.conjM' hπ hyH ^ j with hτ
    have hτS : τ ∈ Stab := Stab.mul_mem (Stab.zpow_mem hsS i) (Stab.zpow_mem hyS j)
    have hτe : ∀ z : X, e (σ z) = τ (e z) := by
      intro z
      apply Subtype.ext
      rw [hij z, hτ, MulAut.mul_apply, coe_conjM'_zpow, coe_conjM'_zpow]
      group
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨τ m, hτS ⟨m, hm, rfl⟩, ?_⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [hτe, MulEquiv.apply_symm_apply]
  rw [eq_top_iff]
  intro z _
  have hz : e z ∈ sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH)) :=
    hgen ▸ Subgroup.mem_top _
  have hle : (sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH))).map
      e.symm.toMonoidHom ≤ sSup {Y : Subgroup X | ¬ 3 ∣ Nat.card Y ∧
        ∀ σ ∈ P, Y.map σ.toMonoidHom ≤ Y} := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Y hY => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hmem Y hY)
  have hmem' : z ∈ (sSup (invSet142 (Res8Hess.conjM' hπ hyH) (Res8Hess.conjM' hπ hsH))).map
      e.symm.toMonoidHom := ⟨e z, hz, by simp⟩
  exact hle hmem'

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
