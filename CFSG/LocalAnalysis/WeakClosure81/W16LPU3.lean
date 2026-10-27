module

public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Cover
public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3StdQ
public import CFSG.LocalAnalysis.WeakClosure81.W16LPU3Swap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open CFSG.Open

section Certified


theorem w16l_cover_ker_le_center {Q : Type} [Group Q] {n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData 2 n F) (π : ↥(unitarySU 2 n F 3) →* Q)
    (ε : (Q ⧸ Subgroup.center Q) ≃* unitaryPSU h 3)
    (hε : ∀ g, ε (QuotientGroup.mk (π g)) = unitaryProj h 3 g) :
    π.ker ≤ Subgroup.center ↥(unitarySU 2 n F 3) := by
  intro g hg
  have h1 : unitaryProj h 3 g = 1 := by
    rw [← hε, MonoidHom.mem_ker.mp hg, QuotientGroup.mk_one, map_one]
  have h2 : g ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj]
    exact h1
  exact unitaryScalars_le_center h 3 h2

theorem w16l_perfect_of_standard {Q : Type} [Group Q] {L X L₀ : Subgroup Q} (k₁ : Q)
    (hL : CFSG.Quasithin.conjSubgroup L k₁ = L₀)
    (hXC : X ≤ Subgroup.centralizer (L : Set Q)) (hnc : ¬ X ≤ Subgroup.center Q)
    (H : ∀ X' : Subgroup Q, X' ≤ Subgroup.centralizer (L₀ : Set Q) → ¬ X' ≤ Subgroup.center Q →
      ∃ x ∈ X', ∃ k : Q, k⁻¹ * x * k ∈ L₀ ⊔ X' ∧ k⁻¹ * x * k ∉ X') :
    ∃ k : Q, ∃ x ∈ X, k⁻¹ * x * k ∈ L ⊔ X ∧ k⁻¹ * x * k ∉ X := by
  have hX'C : CFSG.Quasithin.conjSubgroup X k₁ ≤
      Subgroup.centralizer (L₀ : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hyX : k₁ * y * k₁⁻¹ ∈ X := (CFSG.Quasithin.mem_conjSubgroup_iff).1 hy
    have hzC : z ∈ CFSG.Quasithin.conjSubgroup L k₁ := by rwa [hL]
    have hzL : k₁ * z * k₁⁻¹ ∈ L := (CFSG.Quasithin.mem_conjSubgroup_iff).1 hzC
    have hcomm := (Subgroup.mem_centralizer_iff).1 (hXC hyX) (k₁ * z * k₁⁻¹) hzL
    calc z * y = k₁⁻¹ * ((k₁ * z * k₁⁻¹) * (k₁ * y * k₁⁻¹)) * k₁ := by group
      _ = k₁⁻¹ * ((k₁ * y * k₁⁻¹) * (k₁ * z * k₁⁻¹)) * k₁ := by rw [hcomm]
      _ = y * z := by group
  have hX'nc : ¬ CFSG.Quasithin.conjSubgroup X k₁ ≤ Subgroup.center Q := by
    intro hle
    apply hnc
    intro a ha
    have hy : k₁⁻¹ * a * k₁ ∈ CFSG.Quasithin.conjSubgroup X k₁ := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      have hka : k₁ * (k₁⁻¹ * a * k₁) * k₁⁻¹ = a := by group
      rwa [hka]
    have hc : k₁⁻¹ * a * k₁ ∈ Subgroup.center Q := hle hy
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro b
    have hcb := hc (k₁⁻¹ * b * k₁)
    calc b * a = k₁ * ((k₁⁻¹ * b * k₁) * (k₁⁻¹ * a * k₁)) * k₁⁻¹ := by group
      _ = k₁ * ((k₁⁻¹ * a * k₁) * (k₁⁻¹ * b * k₁)) * k₁⁻¹ := by rw [hcb]
      _ = a * b := by group
  obtain ⟨x', hx', k', h1, h2⟩ :=
    H (CFSG.Quasithin.conjSubgroup X k₁) hX'C hX'nc
  have hsup : CFSG.Quasithin.conjSubgroup (L ⊔ X) k₁ =
      CFSG.Quasithin.conjSubgroup L k₁ ⊔ CFSG.Quasithin.conjSubgroup X k₁ :=
    Subgroup.map_sup L X (MulAut.conj k₁⁻¹).toMonoidHom
  have h1' : k'⁻¹ * x' * k' ∈ CFSG.Quasithin.conjSubgroup (L ⊔ X) k₁ := by
    rw [hsup, hL]
    exact h1
  have hconj : (k₁ * k' * k₁⁻¹)⁻¹ * (k₁ * x' * k₁⁻¹) * (k₁ * k' * k₁⁻¹) =
      k₁ * (k'⁻¹ * x' * k') * k₁⁻¹ := by group
  refine ⟨k₁ * k' * k₁⁻¹, k₁ * x' * k₁⁻¹, ?_, ?_, ?_⟩
  · exact (CFSG.Quasithin.mem_conjSubgroup_iff).1 hx'
  · rw [hconj]
    exact (CFSG.Quasithin.mem_conjSubgroup_iff).1 h1'
  · rw [hconj]
    intro hh
    exact h2 ((CFSG.Quasithin.mem_conjSubgroup_iff).2 hh)

theorem perfectPSUThreeFact_holds : PerfectPSUThreeFact := by
  intro Q _ _ n hperf hQ R hR hRc g hg X _ hXC hnc
  have hn : 2 ≤ n := two_le_of_isPSUGp hQ
  have hX := w16l_isU3Shape_of_perfect hperf hQ
  obtain ⟨F, _, hF, π, ε, hπ, hε⟩ := w16l_exists_cover_unitarySU hperf hQ
  obtain ⟨k₁, hk₁⟩ := w16l_exists_conj_eq_map_Sig01_Q hX hF π ε hπ hε hR hRc hg
  have hker := w16l_cover_ker_le_center hF π ε hε
  obtain ⟨k, x, hx, h1, h2⟩ := w16l_perfect_of_standard k₁ hk₁ hXC hnc
    fun X' hX' hnc' => w16l_swap_of_centralizes_Sig01 hF hn π hπ hker hX' hnc'
  exact ⟨k, x, hx, h1, h2⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
