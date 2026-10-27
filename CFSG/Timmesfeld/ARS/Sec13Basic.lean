module

public import CFSG.Timmesfeld.ARS.Sec8LeviAction
public import CFSG.Timmesfeld.ARS.CaseD4Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def deltaSet (R : Set (Subgroup G)) (A A₀ B : Subgroup G) : Set (Subgroup G) :=
  leviSet R A A₀ ∩ lambdaSet R B

structure Sec13 (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Prop where
  hyp : Hyp G R
  mem : A ∈ R
  sec8 : Sec8 R A
  max : IsSigmaMaximal R (centralGroup R A)
  opp : A₀ ∈ omegaSet R A
  conn : ∀ E ∈ leviSet R A A₀, ∀ F ∈ leviSet R A A₀,
    Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E F
  nondeg : ∃ E ∈ leviSet R A A₀, ∃ F ∈ leviSet R A A₀, Special R E F

theorem leviSet_conjSub (hR : IsRootClass R) (A A₀ : Subgroup G) (g : G) :
    leviSet R (conjSub A g) (conjSub A₀ g) = conjSet (leviSet R A A₀) g := by
  ext X
  rw [mem_conjSet]
  constructor
  · intro hX
    have h1 := conjSub_mem_sigmaSet hR hX.1 g⁻¹
    have h2 := conjSub_mem_sigmaSet hR hX.2 g⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h1 h2
    exact ⟨h1, h2⟩
  · intro hX
    have h1 := conjSub_mem_sigmaSet hR hX.1 g
    have h2 := conjSub_mem_sigmaSet hR hX.2 g
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1 h2
    exact ⟨h1, h2⟩

theorem reflTransGen_oppGraph_conjSet {Δ : Set (Subgroup G)} {E F : Subgroup G} (g : G)
    (h : Relation.ReflTransGen (oppGraph Δ) E F) :
    Relation.ReflTransGen (oppGraph (conjSet Δ g)) (conjSub E g) (conjSub F g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hXY ih =>
    exact ih.tail ⟨conjSub_mem_conjSet hXY.1 g, conjSub_mem_conjSet hXY.2.1 g,
      Opposite.conj hXY.2.2 g⟩

theorem Sec13.of_mem_omegaSet {A A₀ : Subgroup G} (hS : Sec13 R A A₀) {B D : Subgroup G}
    (hB : B ∈ R) (hD : D ∈ omegaSet R B) : Sec13 R B D := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hS.mem hB
  have hA₀g : conjSub A₀ g ∈ omegaSet R B :=
    ⟨hR.conjSub_mem hS.opp.1 g, hg ▸ Opposite.conj hS.opp.2 g⟩
  have h8B : Sec8 R B := Sec8.of_mem hR hS.mem hB hS.sec8
  obtain ⟨m, hm, hmD⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet hS.hyp hB h8B.2 hA₀g hD
  have hmB : conjSub B m = B := conjSub_eq_self_iff.2 ((isPGroup_M hR hB).2.1 hm)
  have hlevi : leviSet R B D = conjSet (leviSet R A A₀) (m * g) := by
    rw [← leviSet_conjSub hR, conjSub_mul, conjSub_mul, hg, hmB, hmD]
  refine ⟨hS.hyp, hB, h8B, isSigmaMaximal_centralGroup_of_mem hR hS.mem hB hS.max, hD, ?_, ?_⟩
  · rw [hlevi]
    rintro _ ⟨E, hE, rfl⟩ _ ⟨F, hF, rfl⟩
    exact reflTransGen_oppGraph_conjSet _ (hS.conn E hE F hF)
  · obtain ⟨E, hE, F, hF, hEF⟩ := hS.nondeg
    rw [hlevi]
    exact ⟨_, conjSub_mem_conjSet hE _, _, conjSub_mem_conjSet hF _,
      Sec3.special_conjSub hR hEF _⟩

theorem conjSet_deltaSet (hR : IsRootClass R) {A A₀ B : Subgroup G} {v : G}
    (hv : v ∈ levi R A A₀) : conjSet (deltaSet R A A₀ B) v = deltaSet R A A₀ (conjSub B v) := by
  ext X
  rw [mem_conjSet]
  have hv' : v⁻¹ ∈ levi R A A₀ := Subgroup.inv_mem _ hv
  constructor
  · rintro ⟨hX1, hX2⟩
    have h1 := Levi.conjSub_mem_leviSet_of_mem_levi hR hX1 hv
    have h2 := conjSub_mem_lambdaSet hR hX2 v
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨hX1, hX2⟩
    have h2 := conjSub_mem_lambdaSet hR hX2 v⁻¹
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one] at h2
    exact ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR hX1 hv', h2⟩

theorem mem_lambdaSet_of_le_M_of_hyp (h : Hyp G R) {X C : Subgroup G} (hX : X ∈ R)
    (hC : C ∈ R) (hle : C ≤ M R X) (hne : C ≠ X) : C ∈ lambdaSet R X := by
  have hmem : C ∈ {B | B ∈ R ∧ B ≤ M R X} := ⟨hC, hle⟩
  rw [(Q_eq_M h hX).2.1] at hmem
  exact hmem.resolve_left hne

section Basic

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hA₀

theorem commuting_of_mem_deltaSet {B E F : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hE : E ∈ deltaSet R A A₀ B) (hF : F ∈ deltaSet R A A₀ B) : Commuting E F := by
  have hBR : B ∈ R := hB.1.1.1
  rw [commuting_iff_commutator_eq_bot, eq_bot_iff, ← M_inf_levi_eq_bot h hA hA₀]
  refine le_inf ?_ (QD.commutator_le_of_le (le_gen hE.1) (le_gen hF.1))
  calc ⁅E, F⁆ ≤ ⁅M R B, M R B⁆ := Subgroup.commutator_mono (QD.le_M hE.2) (QD.le_M hF.2)
    _ = B := (Q_eq_M h hBR).2.2.1
    _ ≤ M R A := QD.le_M hB.1

theorem commuting_gen_deltaSet {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    Commuting (gen (deltaSet R A A₀ B)) (gen (deltaSet R A A₀ B)) :=
  commuting_gen_of_pairwise fun _ hE _ hF => commuting_of_mem_deltaSet h hA hA₀ hB hE hF

omit hA₀ in
theorem special_of_not_commuting_of_mem_leviSet {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hBX : ¬ Commuting B X) : Special R B X := by
  have := h.finite
  have hR := h.root
  have hne : B ≠ X := fun e => hBX (e ▸ hR.commuting_self hB.1.1.1)
  rcases hR.rel _ hB.1.1.1 _ hX.1.1 hne with hc | ho | hs
  · exact absurd hc hBX
  · exact absurd ho.symm (CaseD4.not_opposite_of_mem_leviSet hR hA hB hX)
  · exact hs

omit hA₀ in
theorem special_of_commutator_mem_of_mem_leviSet {B X : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ leviSet R A A₀) (hBX : ⁅B, X⁆ ∈ R) :
    Special R B X :=
  special_of_not_commuting_of_mem_leviSet h hA hB hX fun hc =>
    h.root.ne_bot _ hBX (commuting_iff_commutator_eq_bot.1 hc)

omit hA₀ in
theorem not_opposite_of_mem_lambdaSet {B C : Subgroup G} (hB : B ∈ lambdaSet R A)
    (hC : C ∈ lambdaSet R A) : ¬ Opposite B C := by
  have := h.finite
  have hR := h.root
  have hP : IsPGroup 2 ↥(B ⊔ C) :=
    (isPGroup_M hR hA).1.to_le (sup_le (QD.le_M hB) (QD.le_M hC))
  exact Sec3.not_opposite_of_isPGroup_sup hR hB.1.1 hC.1.1 hP

omit hA₀ in
theorem commuting_or_commutator_eq_of_mem_lambdaSet {B C : Subgroup G}
    (hB : B ∈ lambdaSet R A) (hC : C ∈ lambdaSet R A) (hBC : B ≠ C) :
    Commuting B C ∨ (Special R B C ∧ ⁅B, C⁆ = A) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  rcases hR.rel _ hB.1.1 _ hC.1.1 hBC with hc | ho | hs
  · exact Or.inl hc
  · exact absurd ho (not_opposite_of_mem_lambdaSet h hA hB hC)
  · refine Or.inr ⟨hs, ?_⟩
    have hle : ⁅B, C⁆ ≤ A := by
      rw [← (Q_eq_M h hA).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hB) (QD.le_M hC)
    exact QD.eq_of_le_of_mem hR hiso hs.1 hA hle

end Basic

section Levi

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hA₀

theorem deltaSet_nonempty {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    (deltaSet R A A₀ B).Nonempty := by
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_not_commuting h hA hAne hA₀ hB
  have hs := special_of_not_commuting_of_mem_leviSet h hA hB hX hBX
  obtain ⟨-, D, hD, -, hBD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX hB hs
  exact ⟨D, hD, mem_lambdaSet_comm hD.1.1 hBD⟩

theorem exists_mem_leviSet_special {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    ∃ X ∈ leviSet R A A₀, Special R B X := by
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_not_commuting h hA hAne hA₀ hB
  exact ⟨X, hX, special_of_not_commuting_of_mem_leviSet h hA hB hX hBX⟩

theorem commutator_mem_lambdaStar {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hs : Special R B X) :
    ⁅B, X⁆ ∈ lambdaStar R A A₀ ∧ ⁅B, X⁆ ∈ lambdaSet R B ∧ ⁅B, X⁆ ∈ lambdaSet R X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨h1, -⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX hB hs
  obtain ⟨hB', hX'⟩ := mem_lambdaSet_commutator hR hiso hB.1.1.1 hX.1.1 hs
  exact ⟨h1 _ hs.1 le_sup_right, mem_lambdaSet_comm hs.1 hB', mem_lambdaSet_comm hs.1 hX'⟩

end Levi

theorem Sec13.exists_mem_levi_conjSet_deltaSet_eq {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
    {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) :
    ∃ v ∈ levi R A A₀, conjSet (deltaSet R A A₀ B) v = deltaSet R A A₀ C := by
  obtain ⟨v, hv, hBv⟩ :=
    exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hS.mem hS.sec8.2 hS.max hS.opp hB hC
  exact ⟨v, hv, by rw [conjSet_deltaSet hS.hyp.root hv, hBv]⟩

end CFSG.Timmesfeld.ARS
