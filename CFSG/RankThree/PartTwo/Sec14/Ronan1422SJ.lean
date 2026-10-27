module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartTwo.Sec14.Ronan1422SK
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem aschbacherSolvableCore_eq_ker {X : Type*} [Group X] [Finite X]
    (f : X →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hsol : Group.IsSolvable f.ker) (h3 : ¬ 3 ∣ Nat.card f.ker) :
    aschbacherSolvableCore 3 X = f.ker := by
  obtain ⟨hθsol, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := X) Nat.prime_three
  refine le_antisymm ?_ (hmax _ inferInstance hsol h3)
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnormal : ((aschbacherSolvableCore 3 X).map f).Normal := by
    haveI : (aschbacherSolvableCore 3 X).Characteristic :=
      (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.1
    exact (inferInstance : (aschbacherSolvableCore 3 X).Normal).map f hf
  rcases hnormal.eq_bot_or_eq_top with h0 | htop
  · intro x hx
    rw [MonoidHom.mem_ker]
    have := Subgroup.mem_map_of_mem f hx
    rwa [h0, Subgroup.mem_bot] at this
  · exfalso
    have hsol' : Group.IsSolvable ((aschbacherSolvableCore 3 X).map f) :=
      Group.isSolvable_of_surjective (f := (f.subgroupMap _)) (f.subgroupMap_surjective _)
    rw [htop] at hsol'
    have hsolA : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := (⊤ : Subgroup (alternatingGroup (Fin 6))).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    have : Nontrivial (alternatingGroup (Fin 6)) := hsimple.toNontrivial
    haveI := isPerfect_alternatingGroup_six
    exact Group.IsPerfect.not_isSolvable _ hsolA

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_quot_of {X : Type*} [Group X] [Finite X]
    (f : X →* alternatingGroup (Fin 6)) (hf : Function.Surjective f) (h2 : IsPGroup 2 f.ker) :
    IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsol : Group.IsSolvable f.ker := by
    haveI := h2.isNilpotent
    infer_instance
  have h3 : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hθ := aschbacherSolvableCore_eq_ker f hf hsol h3
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnc : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hperf := isPerfect_alternatingGroup_six
    have : Nontrivial (alternatingGroup (Fin 6)) := hsimple.toNontrivial
    have hsol' : Group.IsSolvable (alternatingGroup (Fin 6)) := by
      let _ : CommGroup (alternatingGroup (Fin 6)) := { (inferInstance : Group _) with
        mul_comm := hc }
      infer_instance
    exact Group.IsPerfect.not_isSolvable _ hsol'
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).symm hq

theorem mem_thetaComponentsAt_of_quot {M K R : Subgroup G} {c : G} (hKM : K ≤ M) (hcM : c ∈ M)
    (hKc : K ≤ Subgroup.centralizer ({c} : Set G))
    (hKN : M ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hKp : Group.IsPerfect ↥K) (f : ↥K →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hker : f.ker = R.subgroupOf K) (hR2 : IsPGroup 2 R)
    (hRK : R ≤ K) :
    K.subgroupOf M ∈ thetaComponentsAt 3 (⟨c, hcM⟩ : ↥M) := by
  set c' : ↥M := ⟨c, hcM⟩ with hc'
  set C' : Subgroup ↥M := Subgroup.centralizer ({c'} : Set ↥M) with hC'
  set K' : Subgroup ↥M := K.subgroupOf M with hK'
  have hK'C : K' ≤ C' := by
    intro x hx
    rw [hC', Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKc (Subgroup.mem_subgroupOf.mp hx))
    exact this
  set Y : Subgroup ↥C' := K'.subgroupOf C' with hY
  let e : ↥Y ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hK'C).trans (Subgroup.subgroupOfEquivOfLe hKM)
  refine ⟨Y, ⟨?_, ?_, ?_⟩, Subgroup.map_subgroupOf_eq_of_le hK'C⟩
  · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · refine Subgroup.Normal.isSubnormal ⟨fun y hy g => ?_⟩
    rw [hY, Subgroup.mem_subgroupOf, hK', Subgroup.mem_subgroupOf] at hy ⊢
    have hgM : ((g : ↥M) : G) ∈ M ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨(g : ↥M).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp g.2
      exact congrArg Subtype.val this
    have := (Subgroup.mem_normalizer_iff.mp (hKN hgM) _).mp hy
    simpa using this
  · have h2 : IsPGroup 2 (f.comp e.toMonoidHom).ker := by
      have hiso : (f.comp e.toMonoidHom).ker = f.ker.comap e.toMonoidHom := rfl
      rw [hiso, hker]
      have hR2' : IsPGroup 2 (R.subgroupOf K) := hR2.comap_subtype
      exact hR2'.comap_of_injective _ e.injective
    exact isQuasisimple_quot_of _ (hf.comp e.surjective) h2

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {A M : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian p A) :
    CFSG.Assembly.IsElemAbelian p (A.subgroupOf M) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
  · have := hA.1.is_comm.comm ⟨((x : ↥M) : G), x.2⟩ ⟨((y : ↥M) : G), y.2⟩
    simpa using congrArg Subtype.val this
  · simpa using hA.2 _ hx

theorem exists_thetaComponent_of_quot (h48 : Sec4.Item4_8) (h45 : Sec4.Item4_5)
    {M A K : Subgroup G} {c : G} (hM4 : SectionFourHyp ↥M)
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hAM : A ≤ M)
    (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hK : K.subgroupOf M ∈ thetaComponentsAt 3 (⟨c, hAM hcA⟩ : ↥M)) :
    ∃ J ∈ thetaComponents 3 ↥M, K.subgroupOf M ≤ J ∧
      A.subgroupOf M ≤ Subgroup.normalizer (J : Set ↥M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA'el : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf M) := isElemAbelian_subgroupOf hAel
  have hA'27 : Nat.card (A.subgroupOf M) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hA27]
    norm_num
  have hc'A : (⟨c, hAM hcA⟩ : ↥M) ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.mpr hcA
  have hc'1 : (⟨c, hAM hcA⟩ : ↥M) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  obtain ⟨J, hJ, hKJ⟩ := h48 ↥M hM4 (A.subgroupOf M) hA'el ⟨3, le_rfl, hA'27⟩ _ hc'A hc'1 _ hK
  have hA'3 : IsPGroup 3 (A.subgroupOf M) := IsPGroup.of_card hA'27
  exact ⟨J, hJ, hKJ, h45 ↥M hM4 (A.subgroupOf M) hA'3 (Or.inr ⟨hA'el, 3, le_rfl, hA'27⟩) J hJ⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
