module

public import CFSG.RankThree.PartOne.KE.A1Quasi
public import CFSG.RankThree.PartOne.KE.NativeCyclicAbstract

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

theorem aut_mul_conj_mul_inv {C : Type*} [Group C] (η : MulAut C) (g : C) :
    η * MulAut.conj g * η⁻¹ = MulAut.conj (η g) := by
  ext h
  simp [MulAut.conj_apply]

theorem fixes_of_commute_conj {C : Type*} [Group C] (hC : Subgroup.center C = ⊥) (m : MulAut C)
    (x : C) (hm : m * MulAut.conj x = MulAut.conj x * m) : m x = x := by
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  apply hinj
  rw [← aut_mul_conj_mul_inv, hm, mul_assoc, mul_inv_cancel, mul_one]

theorem core_le_range_conj_of_quasisimple {C : Type*} [Group C] [Finite C] {p : ℕ}
    (hp : p.Prime) (hC : Subgroup.center C = ⊥) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B) {x : C}
    (hq : CFSG.IsQuasisimple (⁅Subgroup.centralizer ({x} : Set C),
      Subgroup.centralizer ({x} : Set C)⁆ : Subgroup C))
    (hrigid : ∀ η : MulAut C,
      (∀ d ∈ (⁅Subgroup.centralizer ({x} : Set C), Subgroup.centralizer ({x} : Set C)⁆ :
        Subgroup C), η d = d) → η ∈ (MulAut.conj : C →* MulAut C).range) :
    inSubgroup (aschbacherSolvableCore p)
      (B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C))) ≤
        (MulAut.conj : C →* MulAut C).range := by
  classical
  have hinj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    conj_injective_of_center_eq_bot hC
  set D : Subgroup C := Subgroup.centralizer ({x} : Set C) with hD
  set D₀ : Subgroup C := ⁅D, D⁆ with hD₀
  obtain ⟨M, hM⟩ : ∃ M : Subgroup (MulAut C), M =
      B ⊓ Subgroup.centralizer ({(MulAut.conj x : MulAut C)} : Set (MulAut C)) := ⟨_, rfl⟩
  rw [← hM]
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (MulAut C), S = inSubgroup (aschbacherSolvableCore p) M :=
    ⟨_, rfl⟩
  rw [← hS]
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
  have hmx : ∀ m ∈ M, m x = x := by
    intro m hm
    rw [hM] at hm
    refine fixes_of_commute_conj hC m x ?_
    have h := Subgroup.mem_centralizer_iff.1 hm.2 (MulAut.conj x) rfl
    exact h.symm
  have hmD : ∀ m ∈ M, ∀ d ∈ D, m d ∈ D := by
    intro m hm d hd
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h := Subgroup.mem_centralizer_singleton_iff.1 hd
    calc m d * x = m d * m x := by rw [hmx m hm]
      _ = m (d * x) := (map_mul m d x).symm
      _ = m (x * d) := by rw [h]
      _ = m x * m d := map_mul m x d
      _ = x * m d := by rw [hmx m hm]
  have hD₀D : D₀ ≤ D := Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hmD₀ : ∀ m ∈ M, ∀ d ∈ D₀, m d ∈ D₀ := by
    intro m hm d hd
    have hmap : D.map (m : C →* C) ≤ D := by
      rintro _ ⟨e, he, rfl⟩
      exact hmD m hm e he
    have h1 : D₀.map (m : C →* C) ≤ D₀ := by
      rw [hD₀, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨d, hd, rfl⟩
  set P : Subgroup (MulAut C) := D₀.map (MulAut.conj : C →* MulAut C) with hP
  have hPq : CFSG.IsQuasisimple P :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective D₀ (MulAut.conj : C →* MulAut C) hinj) hq
  have hPM : P ≤ M := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hM]
    refine Subgroup.mem_inf.2 ⟨hB ⟨d, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [← map_mul, ← map_mul]
    exact congrArg MulAut.conj (Subgroup.mem_centralizer_singleton_iff.1 (hD₀D hd)).symm
  set ψ : M →* MulAut C := M.subtype with hψ
  have hψinj : Function.Injective ψ := M.subtype_injective
  have hPψ : P ≤ ψ.range := by
    intro u hu
    exact ⟨⟨u, hPM hu⟩, rfl⟩
  have hnorm : ∀ m : M, ∀ u ∈ P, ψ m * u * (ψ m)⁻¹ ∈ P := by
    rintro ⟨m, hm⟩ _ ⟨d, hd, rfl⟩
    refine ⟨m d, hmD₀ m hm d hd, ?_⟩
    change MulAut.conj (m d) = m * MulAut.conj d * m⁻¹
    rw [aut_mul_conj_mul_inv]
  have hVn : (S.subgroupOf M).Normal := ⟨fun s hs m => by
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hSnorm m m.2 s hs⟩
  have hVs : Group.IsSolvable (S.subgroupOf M) := by
    have e : S.subgroupOf M ≃* S := Subgroup.subgroupOfEquivOfLe hSM
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hcomm := commutes_of_quasisimple_embedding ψ hψinj P hPψ hPq hnorm (S.subgroupOf M)
  intro s hs
  refine hrigid s fun d hd => ?_
  have h1 : ψ ⟨s, hSM hs⟩ * MulAut.conj d = MulAut.conj d * ψ ⟨s, hSM hs⟩ :=
    hcomm ⟨s, hSM hs⟩ (Subgroup.mem_subgroupOf.2 hs) _ ⟨d, hd, rfl⟩
  apply hinj
  rw [← aut_mul_conj_mul_inv]
  have h2 : s * MulAut.conj d = MulAut.conj d * s := h1
  rw [h2, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.RankThree.PartOne.KE
