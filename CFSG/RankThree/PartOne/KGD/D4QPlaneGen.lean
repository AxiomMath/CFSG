module

public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open scoped Pointwise

theorem d4Q_exists_ne_one_ker_of_card_sq {A : Type*} [Group A] [Finite A] {L : Type*} [Field L]
    {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ 2) (χ : A →* Lˣ) (hχ : ∀ a, χ a ^ p = 1) :
    ∃ a : A, a ≠ 1 ∧ χ a = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective χ := (injective_iff_map_eq_one χ).2 fun a ha => by
    by_contra hne
    exact hcon a hne ha
  have hle : Nat.card A ≤ Nat.card (rootsOfUnity p L) :=
    Nat.card_le_card_of_injective (fun a => (⟨χ a, (mem_rootsOfUnity p (χ a)).2 (hχ a)⟩ :
      rootsOfUnity p L)) fun a b hab => hinj (congrArg Subtype.val hab)
  have h2 := card_rootsOfUnity L p
  have hp2 := hp.two_le
  rw [hA] at hle
  nlinarith

theorem mem_centralizer_of_mem_autCore {M : Type*} [Group M] {p : ℕ} {B : Subgroup M} {a s : M}
    (hs : s ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M))) :
    s * a = a * s := by
  obtain ⟨s', -, rfl⟩ := Subgroup.mem_map.1 hs
  have h := (Subgroup.mem_inf.1 s'.2).2
  rw [Subgroup.mem_centralizer_iff] at h
  exact (h a rfl).symm

theorem apply_eq_of_comm_conj {C : Type*} [Group C]
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (η : MulAut C) (x : C)
    (h : η * (MulAut.conj x : MulAut C) = (MulAut.conj x : MulAut C) * η) : η x = x := by
  apply hinj
  refine MulEquiv.ext fun y => ?_
  have h1 := congrArg (fun φ : MulAut C => φ (η.symm y)) h
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply] at h1
  simpa [MulAut.conj_apply] using h1

theorem innerCorePreimage {C : Type*} [Group C] [Finite C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) (x : C) :
    ∃ V : Subgroup (Subgroup.centralizer ({x} : Set C)), V.Normal ∧ Group.IsSolvable V ∧
      ∀ q ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ⊓
        (MulAut.conj : C →* MulAut C).range,
      ∃ v ∈ V, MulAut.conj (v : C) = q := by
  classical
  set Int : C →* MulAut C := MulAut.conj with hInt
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup C, D = Subgroup.centralizer ({x} : Set C) := ⟨_, rfl⟩
  have hSM : S ≤ M := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hSnorm : ∀ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
    rw [hS] at hs ⊢
    obtain ⟨s', hs', rfl⟩ := hs
    refine ⟨⟨m, hm⟩ * s' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (aschbacherSolvableCore_normal p M).conj_mem s' hs' ⟨m, hm⟩
  have hSsol : Group.IsSolvable S := by
    have h := (solvable_prime_complement_core_characterization (H := M) hp).1
    rw [hS, inSubgroup]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective (aschbacherSolvableCore p M) M.subtype
        M.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)
  have hIntD : ∀ d ∈ D, Int d ∈ M := by
    intro d hd
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    rw [hD] at hd
    exact congrArg Int (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
  have hYSD : S.comap Int ≤ D := by
    intro y hy
    have hyM : Int y ∈ M := hSM hy
    rw [hM] at hyM
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hyM).2 (Int x) rfl
    rw [hD]
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hinj (by rw [map_mul, map_mul]; exact h1.symm))
  have hVnormal : ((S.comap Int).subgroupOf D).Normal := ⟨fun v hv d => by
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    change Int ((d : C) * (v : C) * (d : C)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnorm _ (hIntD d d.2) _ hv⟩
  have hVsol : Group.IsSolvable ((S.comap Int).subgroupOf D) := by
    let f : ((S.comap Int).subgroupOf D) →* S :=
      ((Int.comp D.subtype).comp ((S.comap Int).subgroupOf D).subtype).codRestrict S
        fun v => Subgroup.mem_subgroupOf.1 v.2
    exact Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab =>
      Subtype.ext (Subtype.ext (hinj (congrArg Subtype.val hab)))
  subst hD
  refine ⟨(S.comap Int).subgroupOf (Subgroup.centralizer ({x} : Set C)), hVnormal, hVsol, ?_⟩
  intro q hq
  obtain ⟨hqS, y, hy⟩ := Subgroup.mem_inf.1 hq
  have hyS : y ∈ S.comap Int := by
    rw [Subgroup.mem_comap, hy]
    exact hqS
  exact ⟨⟨y, hYSD hyS⟩, Subgroup.mem_subgroupOf.2 hyS, hy⟩

end CFSG.RankThree.PartOne.KGD
