module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
import CFSG.RankThree.SubgroupLists2.SpectralBounds

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Open CFSG.Blueprint.Chevalley

private theorem pow_three_eq_one_of_apply_eq_smul {L V : Type*} [Field L] [AddCommGroup V]
    [Module L V] {T : Module.End L V} (hT : T ^ 3 = 1) {v : V} (hv : v ≠ 0) {c : L}
    (h : T v = c • v) : c ^ 3 = 1 := by
  have hv' : T.HasEigenvector c v :=
    Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 h, hv⟩
  have h1 := hv'.pow_apply 3
  rw [hT, Module.End.one_apply] at h1
  exact (smul_left_inj hv).1 (h1.symm.trans (one_smul L v).symm)

private theorem finite_of_commute_pow_three {L V ι : Type*} [Field L] [IsAlgClosed L]
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h3 : ((3 : ℕ) : L) ≠ 0)
    {f : ι → Module.End L V} (hf : Function.Injective f) (hcomm : ∀ i j, Commute (f i) (f j))
    (hpow : ∀ i, f i ^ 3 = 1) : Finite ι := by
  obtain ⟨b, μ, hb⟩ :=
    CFSG.RankThree.SubgroupLists.exists_basis_common_eigenvectors_of_isAlgClosed f hcomm
      fun i => CFSG.ABGLocalTools.isFinitelySemisimple_of_pow_eq_one (hpow i) h3
  have hμ (i : ι) (j : Fin (Module.finrank L V)) :
      μ i j ∈ Polynomial.nthRootsFinset 3 (1 : L) :=
    (Polynomial.mem_nthRootsFinset (by norm_num) 1).2
      (pow_three_eq_one_of_apply_eq_smul (hpow i) (b.ne_zero j) (hb i j))
  refine Finite.of_injective (β := Fin (Module.finrank L V) → Polynomial.nthRootsFinset 3 (1 : L))
    (fun i j => ⟨μ i j, hμ i j⟩) fun i k hik => hf (b.ext fun j => ?_)
  have hj : μ i j = μ k j := by simpa using congrFun hik j
  rw [hb, hb, hj]

theorem e6ModGL_finite_of_isElemAbelian_three {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {X : Subgroup (ModGL Tag.E6 L)} (hX : IsElemAbelian 3 X) :
    (X : Set (ModGL Tag.E6 L)).Finite := by
  have hc (x y : X) : Commute (x : ModGL Tag.E6 L) y :=
    congrArg Subtype.val (hX.1.is_comm.comm x y)
  have hfin : Finite X := finite_of_commute_pow_three h3
    (f := fun x : X => ((x : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)))
    (fun x y h => Subtype.ext (Units.ext h)) (fun x y => (hc x y).units_val) fun x => by
      change ((x : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) ^ 3 = 1
      rw [← Units.val_pow_eq_pow_val, hX.2 _ x.2, Units.val_one]
  exact Set.finite_coe_iff.mp hfin

end CFSG.StandardType.SCFourCover

end
