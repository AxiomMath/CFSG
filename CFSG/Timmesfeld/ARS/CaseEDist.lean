module

public import CFSG.Timmesfeld.ARS.CaseECells
public import CFSG.Timmesfeld.ARS.CaseELevel
public import CFSG.Timmesfeld.ARS.CaseESpecial

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Stab

variable {G : Type*} [Group G] {K : Type*} [Group K]

@[expose] def stabOf (Ψ : K →* G) (C : Subgroup G) : Subgroup K :=
  (Subgroup.normalizer (C : Set G)).comap Ψ

theorem mem_stabOf {Ψ : K →* G} {C : Subgroup G} {g : K} :
    g ∈ stabOf Ψ C ↔ conjSub C (Ψ g) = C := by
  rw [stabOf, Subgroup.mem_comap]
  exact conjSub_eq_self_iff.symm

theorem conjSub_commutator (X Y : Subgroup G) (g : G) :
    conjSub ⁅X, Y⁆ g = ⁅conjSub X g, conjSub Y g⁆ :=
  Subgroup.map_commutator _ _ _

theorem commuting_conjSub_iff' {X Y : Subgroup G} (g : G) :
    Commuting (conjSub X g) (conjSub Y g) ↔ Commuting X Y := by
  refine ⟨fun h => ?_, fun h => h.conjSub g⟩
  have h1 := h.conjSub g⁻¹
  rwa [← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one, conjSub_one] at h1

end Stab

section Parabolic

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {K : Type*} [Group K] {A A₀ : Subgroup G}
  {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Ψ : K →* G}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)

theorem borel_le_stabOf {C : Subgroup G}
    (hCT : (⨆ i, H i).map Ψ ≤ Subgroup.normalizer (C : Set G))
    (hCU : Commuting C ((posUnipotent D).map Ψ)) : borel D H ≤ stabOf Ψ C := by
  refine sup_le ?_ ?_
  · exact Subgroup.map_le_iff_le_comap.1 hCT
  · exact Subgroup.map_le_iff_le_comap.1 (le_normalizer_of_commuting hCU)

theorem n_mem_stabOf (hF : CompFrame R A A₀ D n H Ψ) {C : Subgroup G} (k : Fin D.rank)
    (hP : Commuting C ((D.rootGroup (Pi.single k 1)).map Ψ))
    (hQ : Commuting C ((D.rootGroup (-Pi.single k 1)).map Ψ)) : n k ∈ stabOf Ψ C :=
  mem_stabOf.2 (conjSub_n_eq_of_commuting hF k hP hQ)

theorem nrep_mem_stabOf {C : Subgroup G} {J : Set (Fin D.rank)}
    (hn : ∀ k ∈ J, n k ∈ stabOf Ψ C) {u : (coxeterMatrix D.isFiniteType).Group}
    (hu : u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic J) :
    nrep hct u ∈ stabOf Ψ C := by
  obtain ⟨ω, hred, hωJ, rfl⟩ :=
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic hu
  rw [nrep_wordProd hct hred]
  clear hred hu
  induction ω with
  | nil => exact one_mem _
  | cons k ω ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (hn k (hωJ k List.mem_cons_self))
      (ih fun i hi => hωJ i (List.mem_cons_of_mem k hi))

include hct in
theorem mem_parabolic_of_nrep_mem_stabOf {C : Subgroup G}
    (hCU : Commuting C ((posUnipotent D).map Ψ)) {j : Fin D.rank}
    (hQj : ¬ Commuting C ((D.rootGroup (-Pi.single j 1)).map Ψ))
    (hn : ∀ k, k ≠ j → n k ∈ stabOf Ψ C) (w : (coxeterMatrix D.isFiniteType).Group)
    (hw : nrep hct w ∈ stabOf Ψ C) :
    w ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j} := by
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem with hcs
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  induction hl : cs.length w using Nat.strong_induction_on generalizing w with
  | _ N ih =>
    by_cases hw1 : w = 1
    · rw [hw1]
      exact one_mem _
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw1
    have hneg : weylAction D.isFiniteType w (Pi.single i 1) ≤ 0 :=
      (isRightDescent_iff D.isFiniteType w i).1 hi
    by_cases hij : i = j
    · exfalso
      subst hij
      have hroot : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ (Φ.single_mem i)
      have hγ : weylAction D.isFiniteType w (-Pi.single i 1) ∈ D.roots :=
        weylAction_mem_roots _ _ hroot
      have hpos : 0 < ht (weylAction D.isFiniteType w (-Pi.single i 1)) := by
        refine ht_pos_of_nonneg hγ fun k => ?_
        rw [map_neg, Pi.neg_apply, Pi.zero_apply, neg_nonneg]
        exact hneg k
      have hc : Commuting C ((D.rootGroup (weylAction D.isFiniteType w
          (-Pi.single i 1))).map Ψ) :=
        hCU.mono le_rfl (Subgroup.map_mono (rootGroup_le_posUnipotent hγ hpos))
      rw [← actsAs_nrep hct w _ hroot, ← map_conjSub_eq, ← mem_stabOf.1 hw,
        commuting_conjSub_iff'] at hc
      exact hQj hc
    · have hlen : cs.length (w * cs.simple i) + 1 = cs.length w := cs.isRightDescent_iff.1 hi
      have hlen' : (coxeterMatrix D.isFiniteType).toCoxeterSystem.length (w * cs.simple i) + 1 =
          (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w := hlen
      have hmul : nrep hct w = nrep hct (w * cs.simple i) * n i := by
        have h1 := nrep_mul hct (w := w * cs.simple i) (w' := cs.simple i) (by
          rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one,
            CoxeterSystem.length_simple]
          omega)
        rwa [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one, nrep_simple] at h1
      have hw' : nrep hct (w * cs.simple i) ∈ stabOf Ψ C := by
        have e : nrep hct (w * cs.simple i) = nrep hct w * (n i)⁻¹ := by
          rw [hmul, mul_inv_cancel_right]
        rw [e]
        exact mul_mem hw (inv_mem (hn i hij))
      have h1 := ih (cs.length (w * cs.simple i)) (by omega) _ hw' rfl
      have e : w = w * cs.simple i * cs.simple i := by
        rw [mul_assoc, CoxeterSystem.simple_mul_simple_self, mul_one]
      rw [e]
      exact mul_mem h1 (cs.simple_mem_parabolic hij)

include hct in
theorem stabOf_subset_cellUnion (hext : SteinbergExtras D n H) {C : Subgroup G}
    (hB : borel D H ≤ stabOf Ψ C) {j : Fin D.rank}
    (hpar : ∀ w, nrep hct w ∈ stabOf Ψ C →
      w ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j})
    {g : K} (hg : g ∈ stabOf Ψ C) :
    g ∈ cellUnion hct
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j} : Set _) := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext g
  refine (mem_cellUnion hct).2 ⟨w, hpar w ?_, b₁, hb₁, b₂, hb₂, rfl⟩
  have e : nrep hct w = b₁⁻¹ * (b₁ * nrep hct w * b₂) * b₂⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem (hB hb₁)) hg) (inv_mem (hB hb₂))

@[expose] def oneStep (j : Fin D.rank) (w : (coxeterMatrix D.isFiniteType).Group) : Prop :=
  ∃ u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j},
    ∃ v ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j},
      w = u * v ∨ w = u * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j * v

@[expose] def twoStep (j : Fin D.rank) (w : (coxeterMatrix D.isFiniteType).Group) : Prop :=
  ∃ u ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j},
    ∃ v ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j},
      ∃ y, (y = 1 ∨ y = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j ∨
        ∃ z ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j},
          y = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j * z *
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j) ∧ w = u * y * v

include hct in
theorem mem_cellUnion_twoStep (hext : SteinbergExtras D n H) {P : Subgroup K} {j : Fin D.rank}
    (hP : ∀ g ∈ P, g ∈ cellUnion hct
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic {k | k ≠ j} : Set _))
    {a b c : K} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) :
    a * n j * b * n j * c ∈ cellUnion hct {w | twoStep j w} := by
  set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
  set WJ := cs.parabolic {k | k ≠ j}
  have hs1 : ∀ k ∈ ({k | k ≠ j} : Set (Fin D.rank)), ∀ w ∈ {w | oneStep j w},
      cs.simple k * w ∈ {w | oneStep j w} := by
    rintro k hk w ⟨u, hu, v, hv, h | h⟩ <;>
      refine ⟨cs.simple k * u, mul_mem (cs.simple_mem_parabolic hk) hu, v, hv, ?_⟩
    · exact Or.inl (by rw [h, mul_assoc])
    · exact Or.inr (by rw [h, mul_assoc, mul_assoc, mul_assoc])
  have hs2 : ∀ k ∈ ({k | k ≠ j} : Set (Fin D.rank)), ∀ w ∈ {w | twoStep j w},
      cs.simple k * w ∈ {w | twoStep j w} := by
    rintro k hk w ⟨u, hu, v, hv, y, hy, rfl⟩
    exact ⟨cs.simple k * u, mul_mem (cs.simple_mem_parabolic hk) hu, v, hv, y, hy, by group⟩
  have h1 : n j * c ∈ cellUnion hct {w | oneStep j w} := by
    refine cellUnion_mono hct (fun w hw => ?_) (n_mul_mem_cellUnion hct hext j (hP c hc))
    rcases hw with hw | ⟨w', hw', rfl⟩
    · exact ⟨w, hw, 1, one_mem _, Or.inl (mul_one w).symm⟩
    · exact ⟨1, one_mem _, w', hw', Or.inr (by rw [one_mul])⟩
  have h2 : b * (n j * c) ∈ cellUnion hct {w | oneStep j w} :=
    mul_mem_cellUnion_of_mem hct hext hs1 (hP b hb) h1
  have h3 : n j * (b * (n j * c)) ∈ cellUnion hct {w | twoStep j w} := by
    refine cellUnion_mono hct (fun w hw => ?_) (n_mul_mem_cellUnion hct hext j h2)
    rcases hw with ⟨u, hu, v, hv, h | h⟩ | ⟨w', ⟨u, hu, v, hv, h | h⟩, rfl⟩
    · exact ⟨u, hu, v, hv, 1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨u, hu, v, hv, cs.simple j, Or.inr (Or.inl rfl), h⟩
    · refine ⟨1, one_mem _, u * v, mul_mem hu hv, cs.simple j, Or.inr (Or.inl rfl), ?_⟩
      simp only [h, one_mul]
      rfl
    · refine ⟨1, one_mem _, v, hv, cs.simple j * u * cs.simple j,
        Or.inr (Or.inr ⟨u, hu, rfl⟩), ?_⟩
      simp only [h, one_mul, mul_assoc]
      rfl
  have h4 := mul_mem_cellUnion_of_mem hct hext hs2 (hP a ha) h3
  rwa [show a * n j * b * n j * c = a * (n j * (b * (n j * c))) by group]

end Parabolic

end CFSG.Timmesfeld.ARS
