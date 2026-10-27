module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.KnownMultDihedral
public import CFSG.Quasithin.Background.KnownMultOdd
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem isPGroup_two_ker_psl_two_odd {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h9 : p ^ f ≠ 9) {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (φ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center X) : IsPGroup 2 φ.ker := by
  refine isPGroup_two_of_forall_odd_sylow_eq_bot fun r hr hr2 _ C => ?_
  by_cases hrp : r = p
  · subst hrp
    exact CFSG.SectionRank.OddCover.psl_two_sylow_kernel_eq_bot hp2 hK h9 φ hφ hZ C
  · have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Finite.of_surjective φ hφ
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))
    exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot φ hφ hZ C Q
      (CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic hp.out hp2 hK hr2 hrp Q)

theorem card_ker_le_two_psl_two_odd {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (h9 : p ^ f ≠ 9) {X : Type*} [Group X]
    [Finite X] [Group.IsPerfect X] (φ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center X) : Nat.card φ.ker ≤ 2 :=
  card_ker_le_two_of_dihedral_sylow φ hφ hZ (isPGroup_two_ker_psl_two_odd hp2 hK h9 φ hφ hZ)
    (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K
      ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hf, hK⟩)

theorem exists_surjective_ker_eq_of_mulEquiv_stated_psl {X : Type*} [Group X] (Z : Subgroup X)
    [Z.Normal] (K : Type) [Field K] (e : X ⧸ Z ≃* StatedProj (StatedSL 2 K)) :
    ∃ φ : X →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K,
      Function.Surjective φ ∧ φ.ker = Z := by
  let e2 : X ⧸ Z ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact ⟨e2.toMonoidHom.comp (QuotientGroup.mk' Z),
    e2.surjective.comp (QuotientGroup.mk'_surjective Z), ker_mk_comp_mulEquiv Z e2⟩

theorem isPGroup_two_of_mulEquiv_stated_psl_two_odd {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X) {K : Type}
    [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h9 : p ^ f ≠ 9) (e : X ⧸ Z ≃* StatedProj (StatedSL 2 K)) : IsPGroup 2 Z := by
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_ker_eq_of_mulEquiv_stated_psl Z K e
  have h := isPGroup_two_ker_psl_two_odd hp2 hK h9 φ hφ (hker.le.trans hZ)
  rwa [hker] at h

theorem l2MultiplierFact : L2MultiplierFact := by
  intro r hr h5 X _ _ hperf Z _ hZ hPSL
  have : Fact r.Prime := ⟨hr⟩
  have : Group.IsPerfect X := hperf
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hPSL
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_ker_eq_of_mulEquiv_stated_psl Z K e
  have hr2 : r ≠ 2 := by omega
  have h9 : r ^ 1 ≠ 9 := by
    rw [pow_one]
    rintro rfl
    norm_num at hr
  have := card_ker_le_two_psl_two_odd (p := r) (f := 1) hr2 le_rfl hK h9 φ hφ (hker.le.trans hZ)
  rwa [hker] at this

end CFSG.Quasithin
