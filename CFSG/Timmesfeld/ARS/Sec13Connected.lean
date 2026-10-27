module

public import CFSG.Timmesfeld.ARS.Sec13Centralizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def LeviClosed (R : Set (Subgroup G)) (A A₀ : Subgroup G) : Prop :=
  ∀ E ∈ leviSet R A A₀, ∀ E' ∈ leviSet R A A₀,
    (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E'

theorem Sec13.exists_conjSub_eq {A A₀ : Subgroup G} (hS : Sec13 R A A₀) {B D : Subgroup G}
    (hB : B ∈ R) (hD : D ∈ omegaSet R B) : ∃ g : G, conjSub A g = B ∧ conjSub A₀ g = D := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hS.mem hB
  have hA₀g : conjSub A₀ g ∈ omegaSet R B :=
    ⟨hR.conjSub_mem hS.opp.1 g, hg ▸ Opposite.conj hS.opp.2 g⟩
  obtain ⟨m, hm, hmD⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet hS.hyp hB
    (Sec8.of_mem hR hS.mem hB hS.sec8).2 hA₀g hD
  have hmB : conjSub B m = B := conjSub_eq_self_iff.2 ((isPGroup_M hR hB).2.1 hm)
  exact ⟨m * g, by rw [conjSub_mul, hg, hmB], by rw [conjSub_mul, hmD]⟩

theorem LeviClosed.of_mem_omegaSet {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
    (hcl : LeviClosed R A A₀) {B D : Subgroup G} (hB : B ∈ R) (hD : D ∈ omegaSet R B) :
    LeviClosed R B D := by
  have hR := hS.hyp.root
  obtain ⟨g, rfl, rfl⟩ := hS.exists_conjSub_eq hB hD
  rw [LeviClosed, leviSet_conjSub hR]
  rintro _ ⟨E, hE, rfl⟩ _ ⟨E', hE', rfl⟩ hEE'
  congr 1
  refine hcl E hE E' hE' fun X hX => ?_
  have := hEE' _ (conjSub_mem_conjSet hX g)
  constructor
  · intro h
    have h1 := (this.1 (h.conjSub g)).conjSub g⁻¹
    rwa [Plane.conjSub_conjSub_inv, Plane.conjSub_conjSub_inv] at h1
  · intro h
    have h1 := (this.2 (h.conjSub g)).conjSub g⁻¹
    rwa [Plane.conjSub_conjSub_inv, Plane.conjSub_conjSub_inv] at h1

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀) (hcl : LeviClosed R A A₀)
include hS

theorem commuting_commutator_of_mem_deltaSet {B D F Y : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ leviSet R A A₀) (hDB : Commuting D B) (hF : F ∈ deltaSet R A A₀ B)
    (hY : Y ∈ deltaSet R A A₀ B) : Commuting ⁅D, F⁆ Y := by
  have hR := hS.hyp.root
  have habel := commuting_gen_deltaSet hS.hyp hS.mem hS.opp hB
  refine commuting_iff_commutator_eq_bot.2 (Subgroup.commutator_commutator_eq_bot_of_rotate
    ?_ ?_)
  · rw [commuting_iff_commutator_eq_bot.1 (commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB hF
      hY), Subgroup.commutator_bot_left]
  ·
    have hYD : ⁅Y, D⁆ ≤ gen (deltaSet R A A₀ B) := by
      rw [Subgroup.commutator_le]
      intro y hy d hd
      have hYd : conjSub Y d ∈ deltaSet R A A₀ B := by
        have := conjSet_deltaSet_eq_of_commuting hR hD hDB hd
        rw [← this]
        exact conjSub_mem_conjSet hY d
      rw [commutatorElement_def]
      have h1 : d * y⁻¹ * d⁻¹ ∈ conjSub Y d := conj_mem_conjSub d (Y.inv_mem hy)
      rw [show y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) by group]
      exact Subgroup.mul_mem _ (le_gen hY hy) (le_gen hYd h1)
    exact commuting_iff_commutator_eq_bot.1 (habel.mono hYD (le_gen hF))

include hcl in
theorem exists_mem_deltaSet_of_notMem_lambdaSet {B E F : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hE : E ∈ deltaSet R A A₀ B) (hF : F ∈ deltaSet R A A₀ B)
    (hEF : E ≠ F) (hFE : F ∉ lambdaSet R E) :
    ∃ D ∈ deltaSet R A A₀ B, D ∈ lambdaSet R E ∧ D ∈ lambdaSet R F := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hcEF := commuting_of_mem_deltaSet hS.hyp hS.mem hS.opp hB hF hE
  obtain ⟨D', ⟨hD', hD'E⟩, hFD'⟩ :=
    hS.exists_mem_inter_lambdaSet_not_commuting hcl hE.1 hF.1 hEF.symm hcEF
  have hD'B := commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hS.mem hS.opp hB hE hD' hD'E
  have hs : Special R D' F := by
    have hne : D' ≠ F := fun e => hFD' (by rw [e]; exact hR.commuting_self hFR)
    rcases hR.rel _ hD'.1.1 _ hFR hne with hc | ho | hs
    · exact absurd hc.symm hFD'
    · exact absurd hcEF (not_commuting_of_opposite_of_mem_lambdaSet hR hFR ho.symm
        (mem_lambdaSet_comm hER hD'E))
    · exact hs
  set D := ⁅D', F⁆ with hDdef
  have hDR : D ∈ R := hs.1
  have hDΔ : D ∈ leviSet R A A₀ := Levi.commutator_mem_leviSet hR hS.mem hS.opp hD' hF.1 hs
  obtain ⟨hD'D, hFD⟩ := mem_lambdaSet_commutator hR hiso hD'.1.1 hFR hs
  have hDE : D ≠ E := fun e => hFE (by rw [← e]; exact hFD)
  have hDEl : D ∈ lambdaSet R E := mem_lambdaSet_of_le_M_of_hyp hS.hyp hER hDR
    (commutator_le_of_le_normalizer (QD.le_M hD'E)
      (QD.le_normalizer_M hR hER ⟨hFR, hcEF.symm⟩)) hDE
  have hDB : D ∈ deltaSet R A A₀ B := by
    rw [← hS.setOf_forall_commuting_eq hB]
    exact ⟨hDΔ, fun Y hY => hS.commuting_commutator_of_mem_deltaSet hB hD' hD'B hF hY⟩
  exact ⟨D, hDB, hDEl, mem_lambdaSet_comm hDR hFD⟩

abbrev centGen (R : Set (Subgroup G)) (A A₀ B : Subgroup G) : Subgroup G :=
  gen {X | X ∈ leviSet R A A₀ ∧ Commuting X B}

omit hS in
theorem centGen_le_levi (B : Subgroup G) : centGen R A A₀ B ≤ levi R A A₀ :=
  gen_mono fun _ hX => hX.1

theorem exists_mem_centGen_conjSub_eq_of_mem_lambdaSet {B E F : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hE : E ∈ deltaSet R A A₀ B) (hF : F ∈ deltaSet R A A₀ B)
    (hEF : F ∈ lambdaSet R E) : ∃ g ∈ centGen R A A₀ B, conjSub E g = F := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hER : E ∈ R := hE.1.1.1
  have hFR : F ∈ R := hF.1.1.1
  have hFE : E ∈ lambdaSet R F := mem_lambdaSet_comm hER hEF
  obtain ⟨P, hPR, hPle, hPE, hPF⟩ := exists_mem_le_sup_ne_ne hR hiso hER hEF E F
  obtain ⟨U, ⟨hU, hUE⟩, u, hu, hFu⟩ := hS.exists_mem_inter_lambdaSet_conjSub_eq hE.1 hF.1 hEF
    hFR le_sup_right hEF.1.2.1 hPR hPle hPE
  obtain ⟨U', ⟨hU', hU'F⟩, u', hu', hEu'⟩ := hS.exists_mem_inter_lambdaSet_conjSub_eq hF.1 hE.1
    hFE hER le_sup_right hFE.1.2.1 hPR (sup_comm E F ▸ hPle) hPF
  have hUB := commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hS.mem hS.opp hB hE hU hUE
  have hU'B := commuting_of_mem_deltaSet_of_mem_lambdaSet hS.hyp hS.mem hS.opp hB hF hU' hU'F
  have hUc : U ∈ {X | X ∈ leviSet R A A₀ ∧ Commuting X B} := ⟨hU, hUB⟩
  have hU'c : U' ∈ {X | X ∈ leviSet R A A₀ ∧ Commuting X B} := ⟨hU', hU'B⟩
  refine ⟨u⁻¹ * u', Subgroup.mul_mem _ (Subgroup.inv_mem _ (le_gen hUc hu)) (le_gen hU'c hu'),
    ?_⟩
  rw [conjSub_mul, hEu', ← hFu, Plane.conjSub_conjSub_inv]

include hcl in
theorem exists_mem_gen_conjSub_eq {B E F : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hE : E ∈ deltaSet R A A₀ B) (hF : F ∈ deltaSet R A A₀ B) :
    ∃ g ∈ centGen R A A₀ B, conjSub E g = F := by
  by_cases hEF : E = F
  · exact ⟨1, one_mem _, by rw [conjSub_one, hEF]⟩
  by_cases hFE : F ∈ lambdaSet R E
  · exact hS.exists_mem_centGen_conjSub_eq_of_mem_lambdaSet hB hE hF hFE
  obtain ⟨D, hD, hDE, hDF⟩ := hS.exists_mem_deltaSet_of_notMem_lambdaSet hcl hB hE hF hEF hFE
  obtain ⟨g, hg, hgD⟩ := hS.exists_mem_centGen_conjSub_eq_of_mem_lambdaSet hB hE hD hDE
  obtain ⟨g', hg', hg'F⟩ := hS.exists_mem_centGen_conjSub_eq_of_mem_lambdaSet hB hD hF
    (mem_lambdaSet_comm hF.1.1.1 hDF)
  exact ⟨g' * g, Subgroup.mul_mem _ hg' hg, by rw [conjSub_mul, hgD, hg'F]⟩

include hcl in
theorem reflTransGen_deltaSet {B E F : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hE : E ∈ deltaSet R A A₀ B) (hF : F ∈ deltaSet R A A₀ B) :
    Relation.ReflTransGen (fun X Y => X ∈ deltaSet R A A₀ B ∧ Y ∈ deltaSet R A A₀ B ∧
      Y ∈ lambdaSet R X) E F := by
  by_cases hEF : E = F
  · exact hEF ▸ Relation.ReflTransGen.refl
  by_cases hFE : F ∈ lambdaSet R E
  · exact Relation.ReflTransGen.single ⟨hE, hF, hFE⟩
  obtain ⟨D, hD, hDE, hDF⟩ := hS.exists_mem_deltaSet_of_notMem_lambdaSet hcl hB hE hF hEF hFE
  exact (Relation.ReflTransGen.single ⟨hE, hD, hDE⟩).tail
    ⟨hD, hF, mem_lambdaSet_comm hF.1.1.1 hDF⟩

end Sec13

end CFSG.Timmesfeld.ARS
