module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigPairIndep
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Module

theorem ggQ2s08_big_W_equiv {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hMW : GGQ2LabelWeyl lab M.coxeter)
    (htag : lab.tag = .twA) (h4 : 4 ≤ lab.rank) :
    Nonempty (↥(ggAutomizer L Bs) ≃* Equiv.Perm (Fin (lab.rank + 1))) := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
    simpa [GGQ2LabelWeyl, htag] using hMW
  let s : Fin lab.rank → MulAut ↥Bs := fun k => M.simple (e k)
  have hα : ∀ i, M.root i (M.coroot i) = (2 : ZMod 3) := by
    intro i
    rw [M.pairing i i, M.isCartan.1 i]
    norm_num
  have hlin : ∀ i, ggLin (p := 3) M.model (M.simple i) = reflection (hα i) := fun i =>
    ggLin_eq_reflection M.model (hα i) (M.simple_apply i)
  have hφL : M.coxeter.IsLiftable M.simple := by
    intro i j
    apply ggLin_injective (p := 3) M.model
    rw [map_pow, map_mul, hlin i, hlin j, map_one]
    exact isLiftable_reflection_of_intCartan M.isCartan M.coroot M.root hα M.pairing i j
  have hsLiftable : (CoxeterMatrix.A lab.rank).IsLiftable s := by
    intro k l
    have h := hφL (e k) (e l)
    have hkl : M.coxeter (e k) (e l) = (CoxeterMatrix.A lab.rank) k l := by
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rwa [hkl] at h
  set Φ : (CoxeterMatrix.A lab.rank).Group →* MulAut ↥Bs :=
    (CoxeterMatrix.A lab.rank).toCoxeterSystem.lift ⟨s, hsLiftable⟩ with hΦ
  have hsimple : ∀ k : Fin lab.rank,
      Φ ((CoxeterMatrix.A lab.rank).toCoxeterSystem.simple k) = s k := fun k => by
    rw [hΦ, CoxeterSystem.lift_apply_simple]
  have hs_range : Set.range s = Set.range M.simple := by
    ext φ
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨e.symm i, ?_⟩
      change M.simple (e (e.symm i)) = M.simple i
      rw [Equiv.apply_symm_apply]
  have hrangeΦ : Φ.range = ggAutomizer L Bs := by
    have hcomp : (⇑Φ) ∘ (CoxeterMatrix.A lab.rank).toCoxeterSystem.simple = s :=
      funext hsimple
    rw [M.automizer_L, MonoidHom.range_eq_map,
      ← (CoxeterMatrix.A lab.rank).toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp, hcomp, hs_range]
  obtain ⟨ε, hε⟩ := ggCoxeterA_mulEquivPerm lab.rank
  let ψ : Equiv.Perm (Fin (lab.rank + 1)) →* MulAut ↥Bs := Φ.comp ε.symm.toMonoidHom
  have hψ_simple : ∀ k : Fin lab.rank,
      ψ (Equiv.swap k.castSucc k.succ) = s k := by
    intro k
    have h1 : ε.symm (Equiv.swap k.castSucc k.succ) =
        (CoxeterMatrix.A lab.rank).toCoxeterSystem.simple k := by
      rw [← hε k, MulEquiv.symm_apply_apply, CoxeterMatrix.toCoxeterSystem_simple]
    change Φ (ε.symm (Equiv.swap k.castSucc k.succ)) = s k
    rw [h1]
    exact hsimple k
  let k0 : Fin lab.rank := ⟨0, by omega⟩
  let k1 : Fin lab.rank := ⟨1, by omega⟩
  have hk01 : k0 ≠ k1 := by
    intro h
    have h0 : (k0 : ℕ) = 0 := rfl
    have h1 : (k1 : ℕ) = 1 := rfl
    have hv : (k0 : ℕ) = (k1 : ℕ) := congrArg Fin.val h
    omega
  have hle3A : ∀ i j : Fin lab.rank, i ≠ j → (CoxeterMatrix.A lab.rank).M i j ≤ 3 := by
    intro i j hij
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  have hle3 : ∀ i j : M.Λ, i ≠ j → M.coxeter i j ≤ 3 := by
    intro i j hij
    rw [he, CoxeterMatrix.reindex_apply]
    exact hle3A (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h))
  have h6 : ∀ i j : M.Λ, i ≠ j → M.coxeter i j ≠ 6 := by
    intro i j hij h
    have := hle3 i j hij
    omega
  have hpair : LinearIndependent (ZMod 3) ![M.coroot (e k0), M.coroot (e k1)] :=
    ggQ2s08_big_pairIndep M hMW htag h4 (e k0) (e k1) (e.injective.ne hk01)
  have hfacts :=
    ggQ2s08d_coxeter_facts_of_pair M h6 (e k0) (e k1) (e.injective.ne hk01) hpair
  have hne01 : s k0 ≠ s k1 := fun h =>
    hfacts.2.1 (congrArg (ggLin (p := 3) M.model) h)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    by_contra hne
    haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
    have hnt : Nontrivial ψ.ker := (Subgroup.nontrivial_iff_ne_bot ψ.ker).mpr hne
    have hcard : 5 ≤ Nat.card (Fin (lab.rank + 1)) := by
      simp only [Nat.card_fin]
      omega
    have halt : alternatingGroup (Fin (lab.rank + 1)) ≤ ψ.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal (N := ψ.ker) hcard hnt
    let A : Fin (lab.rank + 1) := k0.castSucc
    let B : Fin (lab.rank + 1) := k0.succ
    let C : Fin (lab.rank + 1) := k1.succ
    have hAB : A ≠ B := by
      intro h
      have hA : (A : ℕ) = 0 := rfl
      have hB : (B : ℕ) = 1 := rfl
      have hv : (A : ℕ) = (B : ℕ) := congrArg Fin.val h
      omega
    have hAC : A ≠ C := by
      intro h
      have hA : (A : ℕ) = 0 := rfl
      have hC : (C : ℕ) = 2 := rfl
      have hv : (A : ℕ) = (C : ℕ) := congrArg Fin.val h
      omega
    have hBC : B ≠ C := by
      intro h
      have hB : (B : ℕ) = 1 := rfl
      have hC : (C : ℕ) = 2 := rfl
      have hv : (B : ℕ) = (C : ℕ) := congrArg Fin.val h
      omega
    have hcyc : (Equiv.swap A B * Equiv.swap B C).IsThreeCycle := by
      have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := B) (b := A) (c := C)
        hAB.symm hBC hAC
      rwa [Equiv.swap_comm B A] at h
    have h3 : Equiv.swap A B * Equiv.swap B C ∈ alternatingGroup (Fin (lab.rank + 1)) :=
      hcyc.mem_alternatingGroup
    have hker : ψ (Equiv.swap A B * Equiv.swap B C) = 1 :=
      MonoidHom.mem_ker.mp (halt h3)
    have hAB' : ψ (Equiv.swap A B) = s k0 := hψ_simple k0
    have hBC' : ψ (Equiv.swap B C) = s k1 := hψ_simple k1
    rw [map_mul, hAB', hBC'] at hker
    have hsq : s k1 * s k1 = 1 := by
      have h := hsLiftable k1 k1
      rw [(CoxeterMatrix.A lab.rank).diagonal k1, pow_one] at h
      exact h
    have heq : s k0 = s k1 := by
      calc s k0 = s k0 * 1 := (mul_one _).symm
        _ = s k0 * (s k1 * s k1) := by rw [hsq]
        _ = (s k0 * s k1) * s k1 := by rw [mul_assoc]
        _ = 1 * s k1 := by rw [hker]
        _ = s k1 := one_mul _
    exact hne01 heq
  have hrangeψ : ψ.range = ggAutomizer L Bs := by
    rw [← hrangeΦ]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨ε.symm σ, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ε g, by change Φ (ε.symm (ε g)) = Φ g; rw [MulEquiv.symm_apply_apply]⟩
  exact ⟨((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrangeψ)).symm⟩

theorem ggQ2s08_big_W_card {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hMW : GGQ2LabelWeyl lab M.coxeter)
    (htag : lab.tag = .twA) (h4 : 4 ≤ lab.rank) :
    Nat.card ↥(ggAutomizer L Bs) = (lab.rank + 1).factorial := by
  obtain ⟨e⟩ := ggQ2s08_big_W_equiv M hMW htag h4
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]

end CFSG.StandardType

end
