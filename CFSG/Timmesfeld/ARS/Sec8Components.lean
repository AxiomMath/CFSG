module

public import CFSG.Timmesfeld.ARS.Sec8Restrict
public import CFSG.Timmesfeld.ARS.Sec8Levi

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem commuting_gen_gen {S T : Set (Subgroup G)} (h : ∀ X ∈ S, ∀ Y ∈ T, Commuting X Y) :
    Commuting (gen S) (gen T) :=
  commuting_iff_le_centralizer.2 (gen_le fun Y hY => commuting_iff_le_centralizer.1
    (commuting_iff_le_centralizer.2 (gen_le fun X hX => commuting_iff_le_centralizer.1
      (h X hX Y hY).symm)).symm)

theorem conjSub_le_sup_of_le_normalizer {K M' : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (M' : Set G)) {m : G} (hm : m ∈ M') :
    conjSub K m ≤ M' ⊔ K := by
  rintro _ ⟨k, hk, rfl⟩
  change m * k * m⁻¹ ∈ M' ⊔ K
  have h1 : k * m⁻¹ * k⁻¹ ∈ M' := (Subgroup.mem_normalizer_iff.1 (hK hk) m⁻¹).1 (M'.inv_mem hm)
  rw [show m * k * m⁻¹ = m * (k * m⁻¹ * k⁻¹) * k by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (M'.mul_mem hm h1)) (Subgroup.mem_sup_right hk)

namespace Levi

theorem conjSub_mem_leviSet (hR : IsRootClass R) {A A₀ B : Subgroup G}
    (hB : B ∈ leviSet R A A₀) {g : G} (hgA : conjSub A g = A) (hgA₀ : conjSub A₀ g = A₀) :
    conjSub B g ∈ leviSet R A A₀ :=
  ⟨hgA ▸ conjSub_mem_sigmaSet hR hB.1 g, hgA₀ ▸ conjSub_mem_sigmaSet hR hB.2 g⟩

theorem conjSub_mem_leviSet_of_mem_levi (hR : IsRootClass R) {A A₀ B : Subgroup G}
    (hB : B ∈ leviSet R A A₀) {g : G} (hg : g ∈ levi R A A₀) :
    conjSub B g ∈ leviSet R A A₀ :=
  conjSub_mem_leviSet hR hB
    (conjSub_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hg) a ha).symm)
    (conjSub_of_forall_commute fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hg) a ha).symm)

theorem mem_leviSet_of_le_levi (hR : IsRootClass R) {A A₀ B : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hB : B ∈ R) (hBV : B ≤ levi R A A₀) : B ∈ leviSet R A A₀ := by
  have hAB : Commuting A B :=
    commuting_iff_le_centralizer.2 (hBV.trans (levi_le_centralizer_left A A₀))
  have hA₀B : Commuting A₀ B :=
    commuting_iff_le_centralizer.2 (hBV.trans (levi_le_centralizer_right A A₀))
  refine ⟨⟨hB, fun e => ?_, hAB⟩, ⟨hB, fun e => ?_, hA₀B⟩⟩
  · exact hA₀.2.not_commuting (hR.ne_bot A hA) (e ▸ hA₀B).symm
  · exact hA₀.2.not_commuting (hR.ne_bot A hA) (e ▸ hAB)

theorem commutator_mem_leviSet (hR : IsRootClass R) {A A₀ B C : Subgroup G} (hA : A ∈ R)
    (hA₀ : A₀ ∈ omegaSet R A) (hB : B ∈ leviSet R A A₀) (hC : C ∈ leviSet R A A₀)
    (h : Special R B C) : ⁅B, C⁆ ∈ leviSet R A A₀ :=
  mem_leviSet_of_le_levi hR hA hA₀ h.1 (QD.commutator_le_of_le (le_gen hB) (le_gen hC))

theorem exists_opposite_mem_leviSet (h : Hyp G R) {A A₀ E : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) : ∃ F ∈ leviSet R A A₀, Opposite E F := by
  have := h.finite
  have hR := h.root
  have hER : E ∈ R := hE.1.1
  obtain ⟨hQM, hset, -, -, hMP⟩ := Q_eq_M h hA
  have hEl : E ∉ lambdaSet R A := fun hEl =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hEl hE.2.2.2
  have hEI : E ∉ isolatedSet R A := by
    intro hI
    have hmem : E ∈ {X | X ∈ R ∧ X ≤ M R A} := ⟨hER, hQM ▸ QD.le_Q hI⟩
    rw [hset] at hmem
    rcases hmem with h1 | h1
    · exact hE.1.2.1 h1
    · exact hEl h1
  obtain ⟨C, hCc, hEC⟩ := QD.exists_opposite_of_notMem_isolatedSet ⟨hER, hE.1.2.2⟩ hEI
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCc.1
  have hcA : conjSub A c = A := conjSub_of_forall_commute fun a ha => (hCc.2 a ha c hc).symm
  have hA₀c : conjSub A₀ c ∈ omegaSet R A :=
    ⟨hR.conjSub_mem hA₀.1 c, hcA ▸ Opposite.conj hA₀.2 c⟩
  obtain ⟨m, hm, hmA₀⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hA hAne hA₀c hA₀
  have hmA : conjSub A m = A :=
    conjSub_of_forall_commute fun a ha => (QD.commuting_M hR hA a ha m hm).symm
  set F := conjSub E (m * c) with hF
  have hFl : F ∈ leviSet R A A₀ := conjSub_mem_leviSet hR hE
    (by rw [conjSub_mul, hcA, hmA]) (by rw [conjSub_mul]; exact hmA₀)
  have hFR : F ∈ R := hFl.1.1
  have hEN := QD.le_normalizer_M hR hA ⟨hER, hE.1.2.2⟩
  have hFN := QD.le_normalizer_M hR hA ⟨hFR, hFl.1.2.2⟩
  have hEc : conjSub E c ≤ M R A ⊔ F := by
    have : conjSub E c = conjSub F m⁻¹ := by rw [hF, ← conjSub_mul, inv_mul_cancel_left]
    rw [this]
    exact conjSub_le_sup_of_le_normalizer hFN (Subgroup.inv_mem _ hm)
  have hop : Opposite E (conjSub E c) := opposite_conjSub_of_opposite hR hCc.1 hER hEC.symm hc hc1
  have hno2 : ∀ P : Subgroup G, IsPGroup 2 P → E ≤ P → conjSub E c ≤ P → False := fun P hP h1 h2 =>
    Sec3.not_opposite_of_isPGroup_sup hR hER (hR.conjSub_mem hER c) (hP.to_le (sup_le h1 h2)) hop
  have hFE : E ≠ F := by
    intro e
    rw [← e] at hEc
    exact hno2 _ (IsPGroup.to_sup_of_normal_right' (hR.isPGroup hER) hMP hEN) le_sup_left
      (hEc.trans (sup_comm _ _).le)
  refine ⟨F, hFl, ?_⟩
  have hfin : IsPGroup 2 ↥(E ⊔ F) → False := fun hP =>
    hno2 _ (IsPGroup.to_sup_of_normal_right' hP hMP (sup_le hEN hFN))
      (le_sup_left.trans le_sup_left)
      (hEc.trans (sup_le le_sup_right (le_sup_right.trans le_sup_left)))
  rcases hR.rel E hER F hFR hFE with hcm | ho | hs
  · exact absurd (isPGroup_sup_of_commuting (hR.isPGroup hER) (hR.isPGroup hFR) hcm) hfin
  · exact ho
  · exact absurd (hs.isPGroup_sup hR hER hFR) hfin

abbrev comp (R : Set (Subgroup G)) (A A₀ E : Subgroup G) : Set (Subgroup G) :=
  {X | Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E X}

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

theorem comp_subset {E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    comp R A A₀ E ⊆ leviSet R A A₀ := fun _ hX =>
  (Sec3.mem_and_exists_opposite_of_reflTransGen hE (exists_opposite_mem_leviSet h hA hAne hA₀ hE)
    hX).1

omit h hA hAne hA₀ in
theorem comp_eq_of_mem {E X : Subgroup G} (hX : X ∈ comp R A A₀ E) :
    comp R A A₀ X = comp R A A₀ E := by
  ext Y
  exact ⟨fun hY => hX.trans hY, fun hY => (Sec3.reflTransGen_oppGraph_symm hX).trans hY⟩

theorem commuting_of_notMem_comp {E F : Subgroup G} (hE : E ∈ leviSet R A A₀)
    (hF : F ∈ leviSet R A A₀) (hEF : F ∉ comp R A A₀ E) : Commuting E F := by
  have := h.finite
  have hR := h.root
  obtain ⟨-, -, -, h4⟩ := component_decomposition hR h.noIsolated (leviSet R A A₀)
    (fun _ hX => hX.1.1) (fun g hg _ hB => conjSub_mem_leviSet_of_mem_levi hR hB hg)
    (fun _ hB _ hC hs => commutator_mem_leviSet hR hA hA₀ hB hC hs)
  rcases h4 E hE F hF (exists_opposite_mem_leviSet h hA hAne hA₀ hE)
    (exists_opposite_mem_leviSet h hA hAne hA₀ hF) hEF with h1 | h1
  · exact h1
  · obtain ⟨D, hD, hop⟩ := exists_opposite_mem_leviSet h hA hAne hA₀ h1.1
    exact absurd hop (h1.2 D hD)

theorem mem_comp_of_le {E B : Subgroup G} (hE : E ∈ leviSet R A A₀) (hB : B ∈ R)
    (hBle : B ≤ gen (comp R A A₀ E)) : B ∈ comp R A A₀ E := by
  have hR := h.root
  have hBl : B ∈ leviSet R A A₀ :=
    mem_leviSet_of_le_levi hR hA hA₀ hB (hBle.trans (gen_mono (comp_subset h hA hAne hA₀ hE)))
  by_contra hBE
  obtain ⟨D, hD, hBD⟩ := exists_opposite_mem_leviSet h hA hAne hA₀ hBl
  have hDE : D ∉ comp R A A₀ E := fun hDE =>
    hBE (comp_eq_of_mem hDE ▸ Relation.ReflTransGen.single ⟨hD, hBl, hBD.symm⟩)
  have hcomm : Commuting (gen (comp R A A₀ E)) (gen {D}) := by
    refine commuting_gen_gen fun X hX Y hY => ?_
    rw [Set.mem_singleton_iff] at hY
    subst hY
    exact commuting_of_notMem_comp h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE hX) hD
      (comp_eq_of_mem hX ▸ hDE)
  exact hBD.not_commuting (hR.ne_bot B hB) (hcomm.mono hBle (le_gen (Set.mem_singleton D)))

end Levi

open Levi

theorem exists_levi_components (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    ∃ (r : ℕ) (Δ : Fin r → Set (Subgroup G)),
      leviSet R A A₀ = ⋃ i, Δ i ∧ (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
      (∀ i j, i ≠ j → Commuting (gen (Δ i)) (gen (Δ j))) ∧
      ∀ i, (Δ i).Nontrivial ∧ {B | B ∈ R ∧ B ≤ gen (Δ i)} = Δ i ∧
        IsRootClass (restrict R (gen (Δ i))) ∧ NoIsolated (restrict R (gen (Δ i))) := by
  have := h.finite
  have hR := h.root
  set cs : Set (Set (Subgroup G)) := {S | ∃ E ∈ leviSet R A A₀, S = comp R A A₀ E} with hcs
  have : Finite cs := Set.toFinite cs |>.to_subtype
  set e := Finite.equivFin cs
  have hΔ : ∀ i, ∃ E ∈ leviSet R A A₀, (e.symm i : Set (Subgroup G)) = comp R A A₀ E :=
    fun i => (e.symm i).2
  have hmemi : ∀ {E}, (hE : E ∈ leviSet R A A₀) →
      (e.symm (e ⟨comp R A A₀ E, E, hE, rfl⟩) : Set (Subgroup G)) = comp R A A₀ E := fun _ => by
    rw [Equiv.symm_apply_apply]
  have hdisj : ∀ i j, i ≠ j → Disjoint (e.symm i : Set (Subgroup G)) (e.symm j) := by
    intro i j hij
    refine Set.disjoint_left.2 fun X hXi hXj => hij ?_
    obtain ⟨E, -, hEi⟩ := hΔ i
    obtain ⟨F, -, hFj⟩ := hΔ j
    rw [hEi] at hXi
    rw [hFj] at hXj
    apply e.symm.injective
    apply Subtype.ext
    rw [hEi, hFj, ← comp_eq_of_mem hXi, comp_eq_of_mem hXj]
  refine ⟨Nat.card cs, fun i => e.symm i, ?_, hdisj, fun i j hij => ?_, fun i => ?_⟩
  · ext X
    refine ⟨fun hX => Set.mem_iUnion.2 ⟨e ⟨comp R A A₀ X, X, hX, rfl⟩, ?_⟩, fun hX => ?_⟩
    · rw [hmemi hX]
      exact Relation.ReflTransGen.refl
    · obtain ⟨i, hXi⟩ := Set.mem_iUnion.1 hX
      obtain ⟨E, hE, hEi⟩ := hΔ i
      exact comp_subset h hA hAne hA₀ hE (hEi ▸ hXi)
  · refine commuting_gen_gen fun X hXi Y hYj => ?_
    obtain ⟨E, hE, hEi⟩ := hΔ i
    have hX : X ∈ comp R A A₀ E := by rw [← hEi]; exact hXi
    have hXl := comp_subset h hA hAne hA₀ hE hX
    obtain ⟨F, hF, hFj⟩ := hΔ j
    have hYl := comp_subset h hA hAne hA₀ hF (by rw [← hFj]; exact hYj)
    refine commuting_of_notMem_comp h hA hAne hA₀ hXl hYl fun hY => ?_
    exact Set.disjoint_left.1 (hdisj i j hij)
      (show Y ∈ (e.symm i : Set (Subgroup G)) by rw [hEi, ← comp_eq_of_mem hX]; exact hY) hYj
  · obtain ⟨E, hE, hEi⟩ := hΔ i
    change (e.symm i : Set (Subgroup G)).Nontrivial ∧
      {B | B ∈ R ∧ B ≤ gen (e.symm i : Set (Subgroup G))} = (e.symm i : Set (Subgroup G)) ∧
      IsRootClass (restrict R (gen (e.symm i : Set (Subgroup G)))) ∧
      NoIsolated (restrict R (gen (e.symm i : Set (Subgroup G))))
    rw [hEi]
    have hcR : ∀ X ∈ comp R A A₀ E, X ∈ R := fun X hX => (comp_subset h hA hAne hA₀ hE hX).1.1
    have hset : {B | B ∈ R ∧ B ≤ gen (comp R A A₀ E)} = comp R A A₀ E := Set.Subset.antisymm
      (fun B hB => mem_comp_of_le h hA hAne hA₀ hE hB.1 hB.2) fun B hB => ⟨hcR B hB, le_gen hB⟩
    have hopp : ∀ B ∈ comp R A A₀ E, ∃ C ∈ comp R A A₀ E, Opposite B C := by
      intro B hB
      obtain ⟨C, hC, hBC⟩ :=
        exists_opposite_mem_leviSet h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE hB)
      exact ⟨C, hB.tail ⟨comp_subset h hA hAne hA₀ hE hB, hC, hBC⟩, hBC⟩
    obtain ⟨-, h2, -, -⟩ := component_decomposition hR h.noIsolated (leviSet R A A₀)
      (fun _ hX => hX.1.1) (fun g hg _ hB => conjSub_mem_leviSet_of_mem_levi hR hB hg)
      (fun _ hB _ hC hs => commutator_mem_leviSet hR hA hA₀ hB hC hs)
    refine ⟨?_, hset, ?_, ?_⟩
    · obtain ⟨C, hC, hEC⟩ := hopp E Relation.ReflTransGen.refl
      exact ⟨E, Relation.ReflTransGen.refl, C, hC, hEC.ne⟩
    · refine isRootClass_restrict hR (hcR E Relation.ReflTransGen.refl)
        (le_gen Relation.ReflTransGen.refl) (fun B hB hBle => ?_) ?_
      · obtain ⟨g, hg, hgB⟩ := (h2 E hE (exists_opposite_mem_leviSet h hA hAne hA₀ hE) B
          (mem_comp_of_le h hA hAne hA₀ hE hB hBle)).1
        exact ⟨g, hg, hgB⟩
      · rw [hset]
        exact le_rfl
    · refine noIsolated_restrict fun B hB hBle => ?_
      obtain ⟨C, hC, hBC⟩ := hopp B (mem_comp_of_le h hA hAne hA₀ hE hB hBle)
      exact ⟨C, hcR C hC, le_gen hC, hBC⟩

theorem levi_components_of_sec8 (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (h8 : Sec8 R A) (hA₀ : A₀ ∈ omegaSet R A) :
    ∃ (r : ℕ) (Δ : Fin r → Set (Subgroup G)),
      leviSet R A A₀ = ⋃ i, Δ i ∧ (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
      (∀ i j, i ≠ j → Commuting (gen (Δ i)) (gen (Δ j))) ∧
      ∀ i, (Δ i).Nontrivial ∧ {B | B ∈ R ∧ B ≤ gen (Δ i)} = Δ i ∧
        IsRootClass (restrict R (gen (Δ i))) ∧ NoIsolated (restrict R (gen (Δ i))) :=
  exists_levi_components h hA h8.2 hA₀

end CFSG.Timmesfeld.ARS
