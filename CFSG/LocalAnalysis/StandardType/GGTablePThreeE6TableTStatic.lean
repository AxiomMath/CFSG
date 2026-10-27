module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRoots
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTClasses
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTRank

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Certificates.Data.E6TableT

section Static

private def chiVal (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) : ZMod 3 :=
  ∑ k, ((x k : ℤ) : ZMod 3) * v k

private lemma e6Chi_apply (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6Chi v (Multiplicative.ofAdd x) = Multiplicative.ofAdd (chiVal v x) := rfl

private lemma e6Chi_apply_eq_one_iff (v : Fin Tag.E6.rank → ZMod 3) (x : Fin Tag.E6.rank → ℤ) :
    e6Chi v (Multiplicative.ofAdd x) = 1 ↔ chiVal v x = 0 := by
  rw [e6Chi_apply, ofAdd_eq_one]

private lemma chiVal_add (v : Fin Tag.E6.rank → ZMod 3) (x y : Fin Tag.E6.rank → ℤ) :
    chiVal v (x + y) = chiVal v x + chiVal v y := by
  simp only [chiVal, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private def chiHom (v : Fin Tag.E6.rank → ZMod 3) : (Fin Tag.E6.rank → ℤ) →+ ZMod 3 :=
  { toFun := chiVal v, map_zero' := by simp [chiVal], map_add' := chiVal_add v }

private lemma smul_single_one (x : Fin Tag.E6.rank → ℤ) (i : Fin Tag.E6.rank) :
    x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single i (x i) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single, h]

private lemma rho_eq_sum (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y) (x : Fin Tag.E6.rank → ℤ) :
    ρ x = ∑ i, x i • ρ (Pi.single i 1) := by
  have hzero : ρ 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    exact (add_left_cancel (show ρ 0 + 0 = ρ 0 + ρ 0 by rw [add_zero]; exact h)).symm
  let f : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := ρ, map_zero' := hzero, map_add' := hadd }
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    exact Finset.sum_congr rfl fun i _ => (smul_single_one x i).symm
  have hfx : f x = ∑ i, x i • f (Pi.single i 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul]
  exact hfx

private lemma chiVal_rho (v : Fin Tag.E6.rank → ZMod 3) (r : ZMod 3)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) v r) (x : Fin Tag.E6.rank → ℤ) :
    chiVal v (ρ x) = r * chiVal v x := by
  rw [rho_eq_sum ρ hadd x]
  have hb : ∀ i, chiVal v (ρ (Pi.single i 1)) = r * v i := fun i => hadm.2.2 i
  have hsum : chiVal v (∑ i, x i • ρ (Pi.single i 1)) =
      ∑ i, (x i : ZMod 3) * (r * v i) := by
    change chiHom v (∑ i, x i • ρ (Pi.single i 1)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rw [show chiHom v (ρ (Pi.single i 1)) = r * v i from hb i]
    ring
  rw [hsum, chiVal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma classSet_finite (l : List Vec) : (classSet l).Finite := by
  have h : classSet l = List.ofFn ⁻¹' ({x : Vec | x ∈ l} : Set Vec) := rfl
  rw [h]
  exact Set.Finite.preimage (List.ofFn_injective.injOn)
    (by simpa only [List.mem_toFinset] using Set.finite_mem_finset l.toFinset)

private lemma componentOrbitLength_eq_one_of_mapsTo
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hfin : Ψ.Finite) (hρ : ∀ γ ∈ Ψ, ρ γ ∈ Ψ) :
    componentOrbitLength ρ Ψ = 1 := by
  have hsub : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' Ψ ⊆ Ψ := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hρ γ hγ
  have himg : (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) '' Ψ = Ψ :=
    Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_image_of_injective Ψ ρ.injective]) hfin
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧
      (ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[s] '' Ψ = Ψ} := by
    refine ⟨Nat.one_pos, ?_⟩
    rw [Function.iterate_one]
    exact himg
  have hle : componentOrbitLength ρ Ψ ≤ 1 := by
    unfold componentOrbitLength
    exact Nat.sInf_le h1
  have hpos : 0 < componentOrbitLength ρ Ψ := by
    unfold componentOrbitLength
    exact (Nat.sInf_mem ⟨1, h1⟩).1
  omega

private lemma static_component
    (v : Fin Tag.E6.rank → ZMod 3)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) (r : ZMod 3)
    (hadd : ∀ x y, ρ (x + y) = ρ x + ρ y)
    (hroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ))
    (hadm : E6Admissible (fun i => ρ (Pi.single i 1)) v r)
    (Ψ : Set (Fin Tag.E6.rank → ℤ)) (hΨ : E6KerComponent v Ψ)
    (huniq : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ), E6KerComponent v Ψ' → Ψ' = Ψ)
    (hfin : Ψ.Finite)
    (c m : ℕ) (hcomp : compRank Ψ = c) (hcard : Ψ.ncard = m) :
    compRank Ψ = c ∧ Ψ.ncard = m ∧ componentOrbitLength ρ Ψ = 1 := by
  refine ⟨hcomp, hcard, ?_⟩
  obtain ⟨i, rfl⟩ := hΨ
  have hstable : ∀ γ ∈ componentRoots (e6Chi v) i, ρ γ ∈ componentRoots (e6Chi v) i := by
    intro γ hγ
    have hkerγ : γ ∈ kernelRoots (e6Chi v) := hγ.1
    have hchiγ : chiVal v γ = 0 := (e6Chi_apply_eq_one_iff v γ).mp hkerγ.2
    have hchiρ : chiVal v (ρ γ) = 0 := by
      rw [chiVal_rho v r ρ hadd hadm γ, hchiγ, mul_zero]
    have hkerργ : ρ γ ∈ kernelRoots (e6Chi v) :=
      ⟨hroot γ hkerγ.1, (e6Chi_apply_eq_one_iff v (ρ γ)).mpr hchiρ⟩
    have hmem : ρ γ ∈ componentRoots (e6Chi v)
        (⟦⟨ρ γ, hkerργ⟩⟧ : KernelComponent (e6Chi v)) := ⟨hkerργ, rfl⟩
    have hcomp' : componentRoots (e6Chi v) (⟦⟨ρ γ, hkerργ⟩⟧ : KernelComponent (e6Chi v)) =
        componentRoots (e6Chi v) i := huniq _ ⟨_, rfl⟩
    rwa [hcomp'] at hmem
  exact componentOrbitLength_eq_one_of_mapsTo hfin hstable

private lemma e6KerComponent_unique_of_classes_singleton
    (k : Fin 5) (l : List Vec) (hclasses : classes (reps.getD k []) = [l]) :
    ∀ Ψ Ψ' : Set (Fin Tag.E6.rank → ℤ),
      E6KerComponent (repZ k) Ψ → E6KerComponent (repZ k) Ψ' → Ψ = Ψ' := by
  intro Ψ Ψ' hΨ hΨ'
  obtain ⟨l₁, hl₁, rfl⟩ := (e6KerComponent_iff_classes k Ψ).mp hΨ
  obtain ⟨l₂, hl₂, rfl⟩ := (e6KerComponent_iff_classes k Ψ').mp hΨ'
  have h1 : l₁ = l := List.mem_singleton.mp (hclasses ▸ hl₁)
  have h2 : l₂ = l := List.mem_singleton.mp (hclasses ▸ hl₂)
  rw [h1, h2]

private lemma exists_singleton_class_of_map (k : Fin 5) (n : ℕ)
    (h : (classes (reps.getD k [])).map List.length = [n]) :
    ∃ l : List Vec, classes (reps.getD k []) = [l] ∧ l.length = n := by
  have hlen : (classes (reps.getD k [])).length = 1 := by
    have := congrArg List.length h
    simpa using this
  obtain ⟨l, hl⟩ := List.length_eq_one_iff.mp hlen
  rw [hl] at h
  simp only [List.map_cons, List.map_nil] at h
  refine ⟨l, hl, ?_⟩
  have := congrArg (fun L : List ℕ => L.getD 0 0) h
  simpa using this

private lemma getD_map_range (f : ℕ → List ℕ) (n i : ℕ) (d : List ℕ) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

private lemma classes_lengths_getD_two :
    (classes (reps.getD (2 : Fin 5) [])).map List.length = [24] := by
  have h := congrArg (fun L : List (List ℕ) => L.getD 2 []) classes_lengths
  rw [getD_map_range (fun k => (classes (reps.getD k [])).map List.length) 5 2 [] (by decide)] at h
  have hr : ([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List ℕ)).getD 2 [] = [24] := by decide
  rw [hr] at h
  simpa using h

private lemma classes_lengths_getD_three :
    (classes (reps.getD (3 : Fin 5) [])).map List.length = [30] := by
  have h := congrArg (fun L : List (List ℕ) => L.getD 3 []) classes_lengths
  rw [getD_map_range (fun k => (classes (reps.getD k [])).map List.length) 5 3 [] (by decide)] at h
  have hr : ([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List ℕ)).getD 3 [] = [30] := by decide
  rw [hr] at h
  simpa using h

private lemma classes_lengths_getD_four :
    (classes (reps.getD (4 : Fin 5) [])).map List.length = [40] := by
  have h := congrArg (fun L : List (List ℕ) => L.getD 4 []) classes_lengths
  rw [getD_map_range (fun k => (classes (reps.getD k [])).map List.length) 5 4 [] (by decide)] at h
  have hr : ([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List ℕ)).getD 4 [] = [40] := by decide
  rw [hr] at h
  simpa using h

private lemma classes_getD_one :
    ∃ l₁ l₂ : List Vec,
      classes (reps.getD (1 : Fin 5) []) = [l₁, l₂] ∧ l₁.length = 20 ∧ l₂.length = 2 := by
  have h : (classes (reps.getD (1 : Fin 5) [])).map List.length = [20, 2] := by
    have h := congrArg (fun L : List (List ℕ) => L.getD 1 []) classes_lengths
    rw [getD_map_range (fun k => (classes (reps.getD k [])).map List.length) 5 1 [] (by decide)] at h
    have hr : ([[6, 6, 6], [20, 2], [24], [30], [40]] : List (List ℕ)).getD 1 [] = [20, 2] := by decide
    rw [hr] at h
    simpa using h
  have hlen : (classes (reps.getD (1 : Fin 5) [])).length = 2 := by
    have := congrArg List.length h
    simpa using this
  obtain ⟨l₁, l₂, hl⟩ := List.length_eq_two.mp hlen
  rw [hl] at h
  simp only [List.map_cons, List.map_nil] at h
  have h1 : l₁.length = 20 := by
    have := congrArg (fun L : List ℕ => L.getD 0 0) h
    simpa using this
  have h2 : l₂.length = 2 := by
    have := congrArg (fun L : List ℕ => L.getD 1 0) h
    simpa using this
  exact ⟨l₁, l₂, hl, h1, h2⟩

end Static

theorem e6TableTAt_repD5 : E6TableTAt (repZ 4) := by
  intro ρ r hadd hroot hadm hv0 Ψ hΨ hsingle
  obtain ⟨l, hclasses, hlen⟩ :=
    exists_singleton_class_of_map 4 40 classes_lengths_getD_four
  have hl : l ∈ classes (reps.getD (4 : Fin 5) []) := by
    rw [hclasses]; exact List.mem_singleton.mpr rfl
  have hΨl : E6KerComponent (repZ 4) (classSet l) :=
    (e6KerComponent_iff_classes 4 (classSet l)).mpr ⟨l, hl, rfl⟩
  have huniq := e6KerComponent_unique_of_classes_singleton 4 l hclasses
  have hEq : Ψ = classSet l := huniq Ψ (classSet l) hΨ hΨl
  have huniqΨ : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ),
      E6KerComponent (repZ 4) Ψ' → Ψ' = Ψ := by
    intro Ψ' hΨ'
    exact (huniq Ψ' (classSet l) hΨ' hΨl).trans hEq.symm
  have hfin : Ψ.Finite := by rw [hEq]; exact classSet_finite l
  have hcard : Ψ.ncard = 40 := by
    rw [hEq, classSet_ncard 4 l hl, hlen]
  have hcomp : compRank Ψ = 5 := by
    rw [hEq]
    exact (classes_compRank 4 l hl).2.2.2 rfl
  exact Or.inl (static_component (repZ 4) ρ r hadd hroot hadm Ψ hΨ huniqΨ hfin 5 40 hcomp hcard)

theorem e6TableTAt_repA5 : E6TableTAt (repZ 3) := by
  intro ρ r hadd hroot hadm hv0 Ψ hΨ hsingle
  obtain ⟨l, hclasses, hlen⟩ :=
    exists_singleton_class_of_map 3 30 classes_lengths_getD_three
  have hl : l ∈ classes (reps.getD (3 : Fin 5) []) := by
    rw [hclasses]; exact List.mem_singleton.mpr rfl
  have hΨl : E6KerComponent (repZ 3) (classSet l) :=
    (e6KerComponent_iff_classes 3 (classSet l)).mpr ⟨l, hl, rfl⟩
  have huniq := e6KerComponent_unique_of_classes_singleton 3 l hclasses
  have hEq : Ψ = classSet l := huniq Ψ (classSet l) hΨ hΨl
  have huniqΨ : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ),
      E6KerComponent (repZ 3) Ψ' → Ψ' = Ψ := by
    intro Ψ' hΨ'
    exact (huniq Ψ' (classSet l) hΨ' hΨl).trans hEq.symm
  have hfin : Ψ.Finite := by rw [hEq]; exact classSet_finite l
  have hcard : Ψ.ncard = 30 := by
    rw [hEq, classSet_ncard 3 l hl, hlen]
  have hcomp : compRank Ψ = 5 := by
    rw [hEq]
    exact (classes_compRank 3 l hl).2.2.1 rfl
  exact Or.inr (Or.inl
    (static_component (repZ 3) ρ r hadd hroot hadm Ψ hΨ huniqΨ hfin 5 30 hcomp hcard))

theorem e6TableTAt_repD4 : E6TableTAt (repZ 2) := by
  intro ρ r hadd hroot hadm hv0 Ψ hΨ hsingle
  obtain ⟨l, hclasses, hlen⟩ :=
    exists_singleton_class_of_map 2 24 classes_lengths_getD_two
  have hl : l ∈ classes (reps.getD (2 : Fin 5) []) := by
    rw [hclasses]; exact List.mem_singleton.mpr rfl
  have hΨl : E6KerComponent (repZ 2) (classSet l) :=
    (e6KerComponent_iff_classes 2 (classSet l)).mpr ⟨l, hl, rfl⟩
  have huniq := e6KerComponent_unique_of_classes_singleton 2 l hclasses
  have hEq : Ψ = classSet l := huniq Ψ (classSet l) hΨ hΨl
  have huniqΨ : ∀ Ψ' : Set (Fin Tag.E6.rank → ℤ),
      E6KerComponent (repZ 2) Ψ' → Ψ' = Ψ := by
    intro Ψ' hΨ'
    exact (huniq Ψ' (classSet l) hΨ' hΨl).trans hEq.symm
  have hfin : Ψ.Finite := by rw [hEq]; exact classSet_finite l
  have hcard : Ψ.ncard = 24 := by
    rw [hEq, classSet_ncard 2 l hl, hlen]
  have hcomp : compRank Ψ = 4 := by
    rw [hEq]
    exact (classes_compRank 2 l hl).2.1 rfl
  exact Or.inr (Or.inr (Or.inl
    (static_component (repZ 2) ρ r hadd hroot hadm Ψ hΨ huniqΨ hfin 4 24 hcomp hcard)))

theorem e6TableTAt_repA4A1 : E6TableTAt (repZ 1) := by
  intro ρ r hadd hroot hadm hv0 Ψ hΨ hsingle
  obtain ⟨l₁, l₂, hclasses, hlen₁, hlen₂⟩ := classes_getD_one
  have hm₁ : l₁ ∈ classes (reps.getD (1 : Fin 5) []) := by
    rw [hclasses]; exact List.mem_cons_self ..
  have hm₂ : l₂ ∈ classes (reps.getD (1 : Fin 5) []) := by
    rw [hclasses]; exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  have hcomp : ∀ l' ∈ classes (reps.getD (1 : Fin 5) []),
      E6KerComponent (repZ 1) (classSet l') := by
    intro l' hl'
    exact (e6KerComponent_iff_classes 1 (classSet l')).mpr ⟨l', hl', rfl⟩
  obtain ⟨l, hl, hΨl⟩ := (e6KerComponent_iff_classes 1 Ψ).mp hΨ
  have hl' : l = l₁ ∨ l = l₂ := by
    have : l ∈ [l₁, l₂] := hclasses ▸ hl
    simpa [List.mem_cons, List.mem_singleton] using this
  rcases hl' with hll₁ | hll₂
  · rw [hll₁] at hΨl
    obtain ⟨n, hn⟩ := hsingle (classSet l₂) (hcomp l₂ hm₂)
    have hcardEq : Ψ.ncard = (classSet l₂).ncard := by
      have h := congrArg Set.ncard hn
      rwa [Set.ncard_image_of_injective Ψ (ρ.injective.iterate n)] at h
    have hbad : (20 : ℕ) = 2 := by
      calc (20 : ℕ) = l₁.length := hlen₁.symm
        _ = (classSet l₁).ncard := (classSet_ncard 1 l₁ hm₁).symm
        _ = Ψ.ncard := by rw [hΨl]
        _ = (classSet l₂).ncard := hcardEq
        _ = l₂.length := classSet_ncard 1 l₂ hm₂
        _ = 2 := hlen₂
    exact absurd hbad (by decide)
  · rw [hll₂] at hΨl
    obtain ⟨n, hn⟩ := hsingle (classSet l₁) (hcomp l₁ hm₁)
    have hcardEq : Ψ.ncard = (classSet l₁).ncard := by
      have h := congrArg Set.ncard hn
      rwa [Set.ncard_image_of_injective Ψ (ρ.injective.iterate n)] at h
    have hbad : (2 : ℕ) = 20 := by
      calc (2 : ℕ) = l₂.length := hlen₂.symm
        _ = (classSet l₂).ncard := (classSet_ncard 1 l₂ hm₂).symm
        _ = Ψ.ncard := by rw [hΨl]
        _ = (classSet l₁).ncard := hcardEq
        _ = l₁.length := classSet_ncard 1 l₁ hm₁
        _ = 20 := hlen₁
    exact absurd hbad (by decide)

end CFSG.StandardType.TablePThreeKG

end
