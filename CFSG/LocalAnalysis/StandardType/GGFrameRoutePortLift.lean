module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open
open scoped commutatorElement

private lemma mem_center_of_map_mem_center {J Q : Type*} [Group J] [Group Q]
    (φ : J →* Q) (hperf : commutator J = ⊤) (hker : φ.ker ≤ Subgroup.center J)
    {e : J} (he : φ e ∈ Subgroup.center Q) : e ∈ Subgroup.center J := by
  have : Group.IsPerfect J := Group.isPerfect_def.mpr hperf
  have hcent : e ∈ Subgroup.centralizer (⊤ : Set J) := by
    refine CFSG.mem_centralizer_of_commutator_mem_center (J := ⊤) inferInstance (r := e) ?_ ?_
    · exact Subgroup.mem_normalizer_iff.mpr fun _ => by simp
    · intro j _
      have hkerj : e * j * e⁻¹ * j⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        change φ ⁅e, j⁆ = 1
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
        exact (Subgroup.mem_center_iff.mp he (φ j)).symm
      have hcenterj : e * j * e⁻¹ * j⁻¹ ∈ Subgroup.center J := hker hkerj
      refine ⟨⟨e * j * e⁻¹ * j⁻¹, Subgroup.mem_top _⟩, ?_, rfl⟩
      exact Subgroup.mem_center_iff.mpr fun y =>
        Subtype.ext (Subgroup.mem_center_iff.mp hcenterj y.1)
  simpa [Subgroup.centralizer_univ] using hcent

private lemma isElemAbelian_map {J Q : Type*} [Group J] [Group Q] (φ : J →* Q)
    {E : Subgroup J} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map φ) := by
  refine ⟨?_, ?_⟩
  · have : IsMulCommutative E := hE.1
    exact Subgroup.map_isMulCommutative (H := E) φ
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 e he, map_one]

private lemma isElemAbelian_map_card_center_inf {J K : Type*} [Group J] [Group K]
    (φ : J →* K) (hperf : commutator J = ⊤) (hker : φ.ker ≤ Subgroup.center J)
    {r : ℕ} {E : Subgroup J} (hEab : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ r)
    (hEdisj : E ⊓ Subgroup.center J = ⊥) (hdisj : E ⊓ φ.ker = ⊥) :
    IsElemAbelian 3 (E.map φ) ∧ Nat.card (E.map φ) = 3 ^ r ∧
      E.map φ ⊓ Subgroup.center K = ⊥ := by
  have hinjOn : Set.InjOn φ (E : Set J) := by
    intro x hxE y hyE hxy
    have hmem : x * y⁻¹ ∈ E ⊓ φ.ker := by
      refine ⟨E.mul_mem hxE (E.inv_mem hyE), ?_⟩
      change φ (x * y⁻¹) = 1
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hdisj] at hmem
    have h1 : x * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc x = x * y⁻¹ * y := by group
      _ = y := by rw [h1, one_mul]
  have hcard : Nat.card (E.map φ) = Nat.card E := by
    change Nat.card (φ '' (E : Set J)) = Nat.card (E : Set J)
    exact Nat.card_image_of_injOn hinjOn
  refine ⟨isElemAbelian_map φ hEab, by rw [hcard, hEcard], ?_⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx.1
  have heZ : e ∈ Subgroup.center J := mem_center_of_map_mem_center φ hperf hker hx.2
  have hmem : e ∈ E ⊓ Subgroup.center J := ⟨he, heZ⟩
  rw [hEdisj] at hmem
  have he1 : e = 1 := Subgroup.mem_bot.mp hmem
  simp [he1]

theorem F08b_transfer {J Q : Type} [Group J] [Group Q] (φ : J →* Q) (hperf : commutator J = ⊤)
    (hker : φ.ker ≤ Subgroup.center J) (Kb : Subgroup Q) (hK : φ.range ≤ Kb) {r : ℕ}
    (hw : Rank3Witness J r) : Rank3Witness ↥Kb r := by
  obtain ⟨E, t, hEab, hEcard, hEdisj, hpow, htcent, hEcent⟩ := hw
  let φ' : J →* ↥Kb := φ.codRestrict Kb fun x => hK (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hker' : φ'.ker = φ.ker := MonoidHom.ker_codRestrict φ Kb _
  have hker_le : φ'.ker ≤ Subgroup.center J := hker' ▸ hker
  have hdisj : E ⊓ φ'.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : x ∈ Subgroup.center J := hker_le hx.2
    have hmem : x ∈ E ⊓ Subgroup.center J := ⟨hx.1, hxZ⟩
    rwa [hEdisj] at hmem
  obtain ⟨hE'ab, hE'card, hE'disj⟩ :=
    isElemAbelian_map_card_center_inf φ' hperf hker_le hEab hEcard hEdisj hdisj
  refine ⟨E.map φ', φ' t, hE'ab, hE'card, hE'disj, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hpow
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · intro ht'
    exact htcent (mem_center_of_map_mem_center φ' hperf hker_le ht')
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : e * t = t * e := by
      have h := hEcent he
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    rw [← map_mul, ← map_mul, hcomm]

end CFSG.StandardType.FrameRoute
