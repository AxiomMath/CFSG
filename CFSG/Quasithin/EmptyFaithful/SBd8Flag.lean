module

public import CFSG.Quasithin.EmptyFaithful.SBd8Map
public import CFSG.Quasithin.EmptyFaithful.SBd8NS
import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

namespace Flag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L


section Lattice

variable {F : Type} [Field F] {n : ℕ}

@[expose] def IsCuts (n : ℕ) (J : Set ℕ) : Prop := ∀ i ∈ J, 1 ≤ i ∧ i < n

theorem isCuts_empty : IsCuts n ∅ := fun i hi => by simp at hi

theorem eq_flagStabilizer_borelOvergroupCuts {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hH : upperTriangular n F ≤ H) :
    H = flagStabilizer n F (borelOvergroupCuts H) ∧ IsCuts n (borelOvergroupCuts H) :=
  ⟨(borel_overgroups H hH).1, fun _ hi => ⟨hi.1, hi.2.1⟩⟩

theorem borelOvergroupCuts_flagStabilizer {J : Set ℕ} (hJ : IsCuts n J) :
    borelOvergroupCuts (flagStabilizer n F J) = J :=
  ((borel_overgroups (flagStabilizer n F J) (upperTriangular_le_flagStabilizer J)).2 J hJ rfl).symm

theorem borelOvergroupCuts_anti {H H' : Subgroup (SpecialLinearGroup (Fin n) F)} (h : H ≤ H') :
    borelOvergroupCuts H' ⊆ borelOvergroupCuts H :=
  fun _ ⟨hi, hin, hr⟩ => ⟨hi, hin, fun hr' => hr (h hr')⟩

theorem flagStabilizer_le_iff {I J : Set ℕ} (hI : IsCuts n I) (hJ : IsCuts n J) :
    flagStabilizer n F I ≤ flagStabilizer n F J ↔ J ⊆ I := by
  constructor
  · intro h
    have := borelOvergroupCuts_anti h
    rwa [borelOvergroupCuts_flagStabilizer hJ, borelOvergroupCuts_flagStabilizer hI] at this
  · intro h g hg
    exact mem_flagStabilizer.2 fun i hi => mem_flagStabilizer.1 hg i (h hi)

theorem flagStabilizer_injOn {I J : Set ℕ} (hI : IsCuts n I) (hJ : IsCuts n J)
    (h : flagStabilizer n F I = flagStabilizer n F J) : I = J :=
  Set.Subset.antisymm ((flagStabilizer_le_iff hJ hI).1 h.ge) ((flagStabilizer_le_iff hI hJ).1 h.le)

theorem flagStabilizer_ne_top {J : Set ℕ} (hJ : IsCuts n J) (hne : J.Nonempty) :
    flagStabilizer n F J ≠ ⊤ := by
  intro h
  rw [← flagStabilizer_empty n F] at h
  obtain ⟨i, hi⟩ := hne
  have := flagStabilizer_injOn hJ isCuts_empty h
  rw [this] at hi
  exact hi

theorem flagStabilizer_union (I J : Set ℕ) :
    flagStabilizer n F (I ∪ J) = flagStabilizer n F I ⊓ flagStabilizer n F J := by
  ext g
  simp only [mem_flagStabilizer, Subgroup.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi)
    exacts [h1 i hi, h2 i hi]

theorem isCuts_singleton {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) : IsCuts n {j} := fun i hi => by
  rw [Set.mem_singleton_iff.1 hi]
  exact ⟨hj, hjn⟩

theorem isCoatom_flagStabilizer_singleton {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    IsCoatom (flagStabilizer n F {j}) := by
  have hJ : IsCuts n {j} := isCuts_singleton hj hjn
  refine ⟨flagStabilizer_ne_top hJ ⟨j, rfl⟩, fun H hlt => ?_⟩
  have hH : upperTriangular n F ≤ H := (upperTriangular_le_flagStabilizer _).trans hlt.le
  obtain ⟨hHeq, hHc⟩ := eq_flagStabilizer_borelOvergroupCuts hH
  have hsub : borelOvergroupCuts H ⊆ {j} :=
    (flagStabilizer_le_iff hJ hHc).1 (hlt.le.trans_eq hHeq)
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · rw [hHeq, h, flagStabilizer_empty]
  · exact absurd (hHeq.trans (by rw [h])) hlt.ne'

theorem exists_singleton_of_isCoatom {H : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hH : upperTriangular n F ≤ H) (hc : IsCoatom H) :
    ∃ j, 1 ≤ j ∧ j < n ∧ H = flagStabilizer n F {j} := by
  obtain ⟨hHeq, hHc⟩ := eq_flagStabilizer_borelOvergroupCuts hH
  have hne : (borelOvergroupCuts H).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact hc.1 (by rw [hHeq, hne, flagStabilizer_empty])
  obtain ⟨j, hj⟩ := hne
  obtain ⟨hj1, hjn⟩ := hHc j hj
  have hJ : IsCuts n {j} := isCuts_singleton hj1 hjn
  have hle : H ≤ flagStabilizer n F {j} := by
    have := (flagStabilizer_le_iff (F := F) hHc hJ).2 (Set.singleton_subset_iff.2 hj)
    rwa [← hHeq] at this
  refine ⟨j, hj1, hjn, ?_⟩
  rcases hc.le_iff.1 hle with h | h
  · exact absurd h (flagStabilizer_ne_top hJ ⟨j, rfl⟩)
  · exact h.symm

end Lattice


section Action

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem upperTriangular_eq_unitriangular (hF : Nat.card F = 2) :
    upperTriangular n F = unitriangular n F :=
  le_antisymm (upperTriangular_le_unitriangular hF) (unitriangular_le_upperTriangular n F)

theorem map_flagStabilizer_singleton (hF : Nat.card F = 2)
    {α : MulAut (SpecialLinearGroup (Fin n) F)}
    (hα : (unitriangular n F).map α.toMonoidHom = unitriangular n F) {j : ℕ} (hj : 1 ≤ j)
    (hjn : j < n) :
    ∃ j', 1 ≤ j' ∧ j' < n ∧
      (flagStabilizer n F {j}).map α.toMonoidHom = flagStabilizer n F {j'} := by
  have hcoat : IsCoatom (α.mapSubgroup (flagStabilizer n F {j})) :=
    (OrderIso.isCoatom_iff α.mapSubgroup _).2 (isCoatom_flagStabilizer_singleton hj hjn)
  have hU : upperTriangular n F ≤ α.mapSubgroup (flagStabilizer n F {j}) := by
    calc upperTriangular n F = unitriangular n F := upperTriangular_eq_unitriangular hF
      _ = (unitriangular n F).map α.toMonoidHom := hα.symm
      _ ≤ (flagStabilizer n F {j}).map α.toMonoidHom := Subgroup.map_mono (by
          rw [← upperTriangular_eq_unitriangular hF]
          exact upperTriangular_le_flagStabilizer _)
  exact exists_singleton_of_isCoatom hU hcoat

theorem exists_sigma (hF : Nat.card F = 2) {α : MulAut (SpecialLinearGroup (Fin n) F)}
    (hα : (unitriangular n F).map α.toMonoidHom = unitriangular n F) :
    ∃ σ : ℕ → ℕ, ∀ j, 1 ≤ j → j < n →
      1 ≤ σ j ∧ σ j < n ∧
        (flagStabilizer n F {j}).map α.toMonoidHom = flagStabilizer n F {σ j} := by
  have h : ∀ j, ∃ j', 1 ≤ j → j < n →
      (1 ≤ j' ∧ j' < n ∧ (flagStabilizer n F {j}).map α.toMonoidHom = flagStabilizer n F {j'}) := by
    intro j
    by_cases hj : 1 ≤ j ∧ j < n
    · obtain ⟨j', h1, h2, h3⟩ := map_flagStabilizer_singleton hF hα hj.1 hj.2
      exact ⟨j', fun _ _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose σ hσ using h
  exact ⟨σ, hσ⟩

omit [Finite F] in
theorem sigma_injOn {α : MulAut (SpecialLinearGroup (Fin n) F)} {σ : ℕ → ℕ}
    (hσ : ∀ j, 1 ≤ j → j < n →
      1 ≤ σ j ∧ σ j < n ∧
        (flagStabilizer n F {j}).map α.toMonoidHom = flagStabilizer n F {σ j})
    {j k : ℕ} (hj : 1 ≤ j) (hjn : j < n) (hk : 1 ≤ k) (hkn : k < n) (h : σ j = σ k) : j = k := by
  have h1 := (hσ j hj hjn).2.2
  have h2 := (hσ k hk hkn).2.2
  rw [h] at h1
  have h3 : flagStabilizer n F {j} = flagStabilizer n F {k} :=
    Subgroup.map_injective α.injective (h1.trans h2.symm)
  exact Set.singleton_eq_singleton_iff.1
    (flagStabilizer_injOn (isCuts_singleton hj hjn) (isCuts_singleton hk hkn) h3)

omit [Finite F] in
theorem map_flagStabilizer_pair {α : MulAut (SpecialLinearGroup (Fin n) F)} {σ : ℕ → ℕ}
    (hσ : ∀ j, 1 ≤ j → j < n →
      1 ≤ σ j ∧ σ j < n ∧
        (flagStabilizer n F {j}).map α.toMonoidHom = flagStabilizer n F {σ j})
    {j k : ℕ} (hj : 1 ≤ j) (hjn : j < n) (hk : 1 ≤ k) (hkn : k < n) :
    (flagStabilizer n F {j, k}).map α.toMonoidHom = flagStabilizer n F {σ j, σ k} := by
  rw [Set.insert_eq, Set.insert_eq (σ j), flagStabilizer_union, flagStabilizer_union,
    Subgroup.map_inf _ _ α.toMonoidHom α.injective, (hσ j hj hjn).2.2, (hσ k hk hkn).2.2]

end Action

theorem isSolvable_map_iff {M : Type*} [Group M] (H : Subgroup M) (α : MulAut M) :
    Group.IsSolvable ↥(H.map α.toMonoidHom) ↔ Group.IsSolvable ↥H := by
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (H.equivMapOfInjective α.toMonoidHom α.injective).toMonoidHom) (MulEquiv.injective _)
  · intro h
    exact Group.isSolvable_of_isSolvable_injective
      (f := (H.equivMapOfInjective α.toMonoidHom α.injective).symm.toMonoidHom)
      (MulEquiv.injective _)


section Blocks

theorem isSolvable_flagStabilizer_of_small {n : ℕ} (hn : 1 ≤ n) {I : Set ℕ}
    (hsmall : ∀ a m : ℕ, a + m ≤ n → (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) :
    Group.IsSolvable ↥(flagStabilizer n (ZMod 2) I) := by
  rw [isSolvable_iff_perfectCore_eq_bot]
  exact perfectCore_eq_bot_of_small (Nat.card_zmod 2) hn hsmall

theorem three_dvd_card_specialLinearGroup {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  rw [card_SL_eq (by omega), Nat.card_zmod]
  refine Dvd.dvd.mul_left ?_ _
  have : (2 ^ 2 - 1 : ℕ) ∣ ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) :=
    Finset.dvd_prod_of_mem (fun j => 2 ^ j - 1) (Finset.mem_Icc.2 ⟨le_rfl, hm⟩)
  simpa using this

theorem not_isSolvable_specialLinearGroup {m : ℕ} (hm3 : 3 ≤ m) :
    ¬ Group.IsSolvable (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  intro hsolv
  have := sl_isSimple_of_card_two (K := ZMod 2) (Nat.card_zmod 2) hm3
  obtain ⟨a, b, hab⟩ := sl_nonabelian_of_card_two (K := ZMod 2) (Nat.card_zmod 2) hm3
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)

theorem not_isSolvable_flagStabilizer_of_big {n : ℕ} {I : Set ℕ} {a m : ℕ} (h : a + m ≤ n)
    (hm3 : 3 ≤ m) (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I)
    (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    ¬ Group.IsSolvable ↥(flagStabilizer n (ZMod 2) I) := by
  intro hsolv
  have hsurj := bigBlockHom_surjective (K := ZMod 2) (Nat.card_zmod 2) h hm3 ha hb hno
  have h1 : Group.IsSolvable ↥(perfectCore (flagStabilizer n (ZMod 2) I)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (perfectCore_le (flagStabilizer n (ZMod 2) I)))
      (Subgroup.inclusion_injective _)
  exact not_isSolvable_specialLinearGroup hm3 (Group.isSolvable_of_surjective hsurj)

theorem false_of_bigBlock {n : ℕ} {K : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hY : Group.IsSolvable ↥(oPrimeResidualOf 3 K)) {I : Set ℕ}
    (hK : K = flagStabilizer n (ZMod 2) I) {a m : ℕ} (h : a + m ≤ n) (hm3 : 3 ≤ m)
    (ha : a = 0 ∨ a ∈ I) (hb : a + m = n ∨ a + m ∈ I) (hno : ∀ c ∈ I, ¬ (a < c ∧ c < a + m)) :
    False := by
  subst hK
  have hs := sl_isSimple_of_card_two (K := ZMod 2) (Nat.card_zmod 2) hm3
  exact false_of_surjective_of_solvable_oPrime (perfectCore_le _) hY (bigBlockHom I a m h ha hb)
    (bigBlockHom_surjective (K := ZMod 2) (Nat.card_zmod 2) h hm3 ha hb hno)
    (normal_solvable_eq_bot_of_simple hs (not_isSolvable_specialLinearGroup hm3))
    (three_dvd_card_specialLinearGroup (by omega))

end Blocks


section Std

variable {n : ℕ} {A : Subgroup (MulAut (SpecialLinearGroup (Fin n) (ZMod 2)))}
  {K : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}

theorem exists_cuts
    (d : OvgData (SpecialLinearGroup (Fin n) (ZMod 2)) A (unitriangular n (ZMod 2)) K) :
    ∃ I, IsCuts n I ∧ K = flagStabilizer n (ZMod 2) I := by
  have hUK : upperTriangular n (ZMod 2) ≤ K := by
    rw [upperTriangular_eq_unitriangular (Nat.card_zmod 2)]
    exact d.U_le
  obtain ⟨h1, h2⟩ := eq_flagStabilizer_borelOvergroupCuts hUK
  exact ⟨_, h2, h1⟩

theorem eq_of_stable
    (d : OvgData (SpecialLinearGroup (Fin n) (ZMod 2)) A (unitriangular n (ZMod 2)) K)
    {I J : Set ℕ} (hI : IsCuts n I) (hJ : IsCuts n J) (hK : K = flagStabilizer n (ZMod 2) I)
    (hJne : J.Nonempty) (hJI : J ⊆ I)
    (hst : ∀ α ∈ A, (flagStabilizer n (ZMod 2) J).map α.toMonoidHom =
      flagStabilizer n (ZMod 2) J) : I = J := by
  have hKJ : K ≤ flagStabilizer n (ZMod 2) J := by
    rw [hK]
    exact (flagStabilizer_le_iff hI hJ).2 hJI
  have h1 := d.K_max _ hKJ (flagStabilizer_ne_top hJ hJne) hst
  rw [hK] at h1
  exact Set.Subset.antisymm ((flagStabilizer_le_iff hJ hI).1 h1) hJI

end Std

section Reduction

variable {X : Type} [Group X] [Finite X]

theorem exists_stdData {n : ℕ} (hn : 1 ≤ n) {A : Subgroup (MulAut X)} {U K : Subgroup X}
    (d : OvgData X A U K) (φ : X ≃* SpecialLinearGroup (Fin n) (ZMod 2)) :
    ∃ ψ : X ≃* SpecialLinearGroup (Fin n) (ZMod 2),
      OvgData (SpecialLinearGroup (Fin n) (ZMod 2)) (A.map (MulAut.congr ψ).toMonoidHom)
        (unitriangular n (ZMod 2)) (K.map ψ.toMonoidHom) := by
  have hU₀ : IsSylowTwoOf (unitriangular n (ZMod 2)) ⊤ :=
    CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular hn
  have hU₁ : IsSylowTwoOf (U.map φ.toMonoidHom) ⊤ := by
    have := isSylowTwoOf_map' d.U_syl φ.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ φ.surjective] at this
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj hU₀ hU₁
  refine ⟨φ.trans (MulAut.conj g⁻¹), ?_⟩
  have hU : U.map (φ.trans (MulAut.conj g⁻¹)).toMonoidHom = unitriangular n (ZMod 2) := by
    have h1 : U.map (φ.trans (MulAut.conj g⁻¹)).toMonoidHom =
        (U.map φ.toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hg]
    have h2 := B6.conjSub_mul g⁻¹ g (unitriangular n (ZMod 2))
    rw [inv_mul_cancel, B6.conjSub_one] at h2
    exact h2.symm
  have := d.map (φ.trans (MulAut.conj g⁻¹))
  rwa [hU] at this

end Reduction

end Flag

end SBd8

end CFSG.Quasithin
