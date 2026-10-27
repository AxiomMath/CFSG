module

public import CFSG.LieType.Steinberg.Bruhat
public import TauCeti.GroupTheory.Coxeter.Parabolic

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

@[expose] def cellUnion (S : Set (coxeterMatrix D.isFiniteType).Group) : Set K :=
  ⋃ w ∈ S, bruhatCell hct w

theorem mem_cellUnion {S : Set (coxeterMatrix D.isFiniteType).Group} {g : K} :
    g ∈ cellUnion hct S ↔ ∃ w ∈ S, g ∈ bruhatCell hct w := by
  simp [cellUnion]

theorem cellUnion_mono {S S' : Set (coxeterMatrix D.isFiniteType).Group} (h : S ⊆ S') :
    cellUnion hct S ⊆ cellUnion hct S' := fun g hg => by
  obtain ⟨w, hw, hg⟩ := (mem_cellUnion hct).1 hg
  exact (mem_cellUnion hct).2 ⟨w, h hw, hg⟩

theorem mul_mem_cellUnion {S : Set (coxeterMatrix D.isFiniteType).Group} {b g : K}
    (hb : b ∈ borel D H) (hg : g ∈ cellUnion hct S) : b * g ∈ cellUnion hct S := by
  obtain ⟨w, hw, hg⟩ := (mem_cellUnion hct).1 hg
  exact (mem_cellUnion hct).2 ⟨w, hw, mul_mem_bruhatCell hct hb hg⟩

theorem n_mul_mem_cellUnion (hext : SteinbergExtras D n H)
    {S : Set (coxeterMatrix D.isFiniteType).Group} (i : Fin D.rank) {g : K}
    (hg : g ∈ cellUnion hct S) :
    n i * g ∈ cellUnion hct
      (S ∪ (fun w => (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w) '' S) := by
  obtain ⟨w, hw, hg⟩ := (mem_cellUnion hct).1 hg
  rcases n_mul_mem_bruhatCell hct hext hg i with h | h
  · exact (mem_cellUnion hct).2 ⟨w, Or.inl hw, h⟩
  · exact (mem_cellUnion hct).2 ⟨_, Or.inr ⟨w, hw, rfl⟩, h⟩

theorem n_mul_mem_cellUnion_of_stable (hext : SteinbergExtras D n H)
    {S : Set (coxeterMatrix D.isFiniteType).Group} {J : Set (Fin D.rank)}
    (hS : ∀ k ∈ J, ∀ w ∈ S, (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k * w ∈ S)
    {i : Fin D.rank} (hi : i ∈ J) {g : K} (hg : g ∈ cellUnion hct S) :
    n i * g ∈ cellUnion hct S := by
  refine cellUnion_mono hct (fun w hw => ?_) (n_mul_mem_cellUnion hct hext i hg)
  rcases hw with hw | ⟨w', hw', rfl⟩
  · exact hw
  · exact hS i hi w' hw'

theorem nrep_mul_mem_cellUnion (hext : SteinbergExtras D n H)
    {S : Set (coxeterMatrix D.isFiniteType).Group} {J : Set (Fin D.rank)}
    (hS : ∀ k ∈ J, ∀ w ∈ S, (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k * w ∈ S)
    {u : (coxeterMatrix D.isFiniteType).Group}
    (hu : u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J) {g : K}
    (hg : g ∈ cellUnion hct S) : nrep hct u * g ∈ cellUnion hct S := by
  obtain ⟨ω, hred, hωJ, rfl⟩ :=
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic hu
  rw [nrep_wordProd hct hred]
  clear hred hu
  induction ω with
  | nil => simpa using hg
  | cons k ω ih =>
    rw [List.map_cons, List.prod_cons, mul_assoc]
    exact n_mul_mem_cellUnion_of_stable hct hext hS (hωJ k List.mem_cons_self)
      (ih fun i hi => hωJ i (List.mem_cons_of_mem k hi))

theorem mul_mem_cellUnion_of_mem (hext : SteinbergExtras D n H)
    {S : Set (coxeterMatrix D.isFiniteType).Group} {J : Set (Fin D.rank)}
    (hS : ∀ k ∈ J, ∀ w ∈ S, (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k * w ∈ S)
    {a g : K}
    (ha : a ∈ cellUnion hct
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J : Set _))
    (hg : g ∈ cellUnion hct S) : a * g ∈ cellUnion hct S := by
  obtain ⟨u, hu, b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_cellUnion hct).1 ha
  rw [show b₁ * nrep hct u * b₂ * g = b₁ * (nrep hct u * (b₂ * g)) by group]
  exact mul_mem_cellUnion hct hb₁
    (nrep_mul_mem_cellUnion hct hext hS hu (mul_mem_cellUnion hct hb₂ hg))

end CFSG.Timmesfeld.ARS
