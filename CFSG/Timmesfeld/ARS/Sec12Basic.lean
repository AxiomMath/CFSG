module

public import CFSG.Timmesfeld.ARS.InductionMax
public import CFSG.Timmesfeld.ARS.Sec13Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def LeviConnected (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Prop :=
  ∀ E ∈ leviSet R A A₀, ∀ F ∈ leviSet R A A₀, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E F

structure Sec12 (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Prop where
  hyp : Hyp G R
  mem : A ∈ R
  sec8 : Sec8 R A
  max : IsSigmaMaximal R (centralGroup R A)
  opp : A₀ ∈ omegaSet R A
  deg : ∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y

theorem Sec12.of_caseM (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R)
    (hcoat : IsCoatom (Subgroup.normalizer (A : Set G))) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) {A₀ : Subgroup G} (hA₀ : A₀ ∈ omegaSet R A)
    (hdeg : ∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y) : Sec12 R A A₀ where
  hyp := h
  mem := hA
  sec8 := ⟨hcoat, hAne⟩
  max := hmax
  opp := hA₀
  deg := hdeg

theorem leviConnected_of_card_eq_one (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (h1 : Nat.card (leviComps R A A₀) = 1) : LeviConnected R A A₀ := by
  intro E hE F hF
  have hF' : F ∈ Levi.comp R A A₀ E := by
    rw [comp_eq_leviSet_of_card_eq_one h hA hAne hA₀ h1 hE]
    exact hF
  exact hF'

theorem Sec12.of_mem_omegaSet {A A₀ : Subgroup G} (hS : Sec12 R A A₀) {B D : Subgroup G}
    (hB : B ∈ R) (hD : D ∈ omegaSet R B) : Sec12 R B D := by
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
  refine ⟨hS.hyp, hB, h8B, isSigmaMaximal_centralGroup_of_mem hR hS.mem hB hS.max, hD, ?_⟩
  rw [hlevi]
  rintro _ ⟨E, hE, rfl⟩ _ ⟨F, hF, rfl⟩ hEF
  have := Sec3.special_conjSub hR hEF (m * g)⁻¹
  rw [Plane.conjSub_conjSub_inv, Plane.conjSub_conjSub_inv] at this
  exact hS.deg E hE F hF this

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem comp_eq (hconn : LeviConnected R A A₀) {E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    Levi.comp R A A₀ E = leviSet R A A₀ :=
  Set.Subset.antisymm (Levi.comp_subset hS.hyp hS.mem hS.sec8.2 hS.opp hE)
    fun F hF => hconn E hE F hF

theorem ne_of_mem_lambdaStar_of_mem_leviSet {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) : B ≠ X := by
  rintro rfl
  exact hS.hyp.root.ne_bot _ hB.2.2.1 (commuting_iff_commutator_eq_bot.1 hX.2.2.2)

theorem mem_lambdaSet_of_commuting {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hBX : Commuting B X) : B ∈ lambdaSet R X := by
  have hsub := Levi.comp_subset hS.hyp hS.mem hS.sec8.2 hS.opp hX
  have hdeg : ∀ Y ∈ Levi.comp R A A₀ X, ∀ Z ∈ Levi.comp R A A₀ X, ¬ Special R Y Z :=
    fun Y hY Z hZ => hS.deg Y (hsub hY) Z (hsub hZ)
  have key := sigmaSet_inter_lambdaStar_eq_of_isSigmaMaximal hS.hyp hS.mem hS.sec8.2 hS.max
    hS.opp hX hdeg (Sec9.self_mem_comp A A₀ X)
  have hmem : B ∈ sigmaSet R X ∩ lambdaStar R A A₀ :=
    ⟨⟨hB.1.1.1, hS.ne_of_mem_lambdaStar_of_mem_leviSet hB hX, hBX.symm⟩, hB⟩
  rw [key] at hmem
  exact hmem.1

theorem mem_deltaSet_of_commuting {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hBX : Commuting B X) : X ∈ deltaSet R A A₀ B :=
  ⟨hX, mem_lambdaSet_comm hX.1.1 (hS.mem_lambdaSet_of_commuting hB hX hBX)⟩

theorem mem_deltaSet_or_special {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) : X ∈ deltaSet R A A₀ B ∨ Special R B X := by
  by_cases hc : Commuting B X
  · exact Or.inl (hS.mem_deltaSet_of_commuting hB hX hc)
  · exact Or.inr (special_of_not_commuting_of_mem_leviSet hS.hyp hS.mem hB hX hc)

theorem commuting_of_mem_deltaSet' {B X Y : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ deltaSet R A A₀ B) (hY : Y ∈ deltaSet R A A₀ B) : Commuting X Y :=
  commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB hX hY

theorem deltaSet_inter_eq_empty_of_special {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hBC : Special R B C) :
    deltaSet R A A₀ B ∩ deltaSet R A A₀ C = ∅ := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  refine Set.eq_empty_iff_forall_notMem.2 fun X ⟨hXB, hXC⟩ => ?_
  have hXR : X ∈ R := hXB.1.1.1
  have hne : B ≠ C := by
    rintro rfl
    exact hR.ne_bot _ hBC.1 (commuting_iff_commutator_eq_bot.1 (hR.commuting_self hB.1.1.1))
  have hBCA : ⁅B, C⁆ = A := by
    rcases commuting_or_commutator_eq_of_mem_lambdaSet hS.hyp hS.mem hB.1 hC.1 hne with hc | hs
    · exact absurd (commuting_iff_commutator_eq_bot.1 hc) (hR.ne_bot _ hBC.1)
    · exact hs.2
  have hle : A ≤ X := by
    rw [← hBCA, ← (Q_eq_M hS.hyp hXR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hB.1.1.1 hXB.2))
      (QD.le_M (mem_lambdaSet_comm hC.1.1.1 hXC.2))
  exact hXB.1.1.2.1 (QD.eq_of_le_of_mem hR hiso hS.mem hXR hle).symm

theorem not_commuting_and_commuting {B X Y : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hY : Y ∈ leviSet R A A₀) (hXY : Opposite X Y)
    (hBX : Commuting B X) (hBY : Commuting B Y) : False :=
  hXY.not_commuting (hS.hyp.root.ne_bot X hX.1.1) (hS.commuting_of_mem_deltaSet' hB
    (hS.mem_deltaSet_of_commuting hB hX hBX) (hS.mem_deltaSet_of_commuting hB hY hBY))

theorem commuting_iff_mem_deltaSet_commutator {B D X : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hD : D ∈ leviSet R A A₀) (hBD : Special R B D)
    (hX : X ∈ deltaSet R A A₀ B) : Commuting X D ↔ X ∈ deltaSet R A A₀ ⁅B, D⁆ := by
  have := hS.hyp.finite
  obtain ⟨hC, -, hCD⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hB hD hBD
  constructor
  · intro hXD
    have hXC : Commuting ⁅B, D⁆ X :=
      commuting_commutator_of_commuting hX.2.1.2.2 hXD.symm
    exact hS.mem_deltaSet_of_commuting hC hX.1 hXC
  · intro hXC
    exact hS.commuting_of_mem_deltaSet' hC hXC ⟨hD, mem_lambdaSet_comm hD.1.1 hCD⟩

theorem ncard_deltaSet_eq {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) :
    (deltaSet R A A₀ B).ncard = (deltaSet R A A₀ C).ncard := by
  obtain ⟨v, hv, hBv⟩ :=
    exists_mem_levi_conjSub_eq_of_isSigmaMaximal hS.hyp hS.mem hS.sec8.2 hS.max hS.opp hB hC
  rw [← hBv, ← conjSet_deltaSet hS.hyp.root hv, conjSet]
  refine (Set.ncard_image_of_injective _ fun X Y hXY => ?_).symm
  have := congrArg (fun Z : Subgroup G => conjSub Z v⁻¹) hXY
  simpa only [Plane.conjSub_conjSub_inv] using this

theorem mem_deltaSet_of_forall_commuting {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hXB : ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) :
    X ∈ deltaSet R A A₀ B := by
  have := hS.hyp.finite
  rcases hS.mem_deltaSet_or_special hB hX with hX' | hs
  · exact hX'
  exfalso
  obtain ⟨hC, -, hCX⟩ := commutator_mem_lambdaStar hS.hyp hS.mem hS.sec8.2 hS.opp hB hX hs
  have hsub : deltaSet R A A₀ B ⊆ deltaSet R A A₀ ⁅B, X⁆ := fun Y hY =>
    (hS.commuting_iff_mem_deltaSet_commutator hB hX hs hY).1 (hXB Y hY).symm
  have hXC : X ∈ deltaSet R A A₀ ⁅B, X⁆ := ⟨hX, mem_lambdaSet_comm hX.1.1 hCX⟩
  have hXnB : X ∉ deltaSet R A A₀ B := fun hX' =>
    hS.hyp.root.ne_bot _ hs.1 (commuting_iff_commutator_eq_bot.1 hX'.2.1.2.2)
  have hlt : deltaSet R A A₀ B ⊂ deltaSet R A A₀ ⁅B, X⁆ :=
    Set.ssubset_iff_subset_ne.2 ⟨hsub, fun e => hXnB (e ▸ hXC)⟩
  have := Set.ncard_lt_ncard hlt (Set.toFinite _)
  rw [hS.ncard_deltaSet_eq hB hC] at this
  exact lt_irrefl _ this

end Sec12

end CFSG.Timmesfeld.ARS
