module

public import CFSG.Quasithin.EmptyFaithful.ModBA6Perfect

public section

namespace CFSG.Quasithin.ModC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isMulCommutative_blockU {K : Subgroup G} (hshort : IsShort2 K) :
    IsMulCommutative ↥(blockU K) := by
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hUQ' : blockU K ≤ blockQ K := hUQ.trans inf_le_left
  have hcomm' : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hUQ ha).2) b (hUQ' hb)).symm
  exact ⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩

theorem exists_core_equiv_six {K : Subgroup G} (hshort : IsShort2 K) (hA : IsAlt 6 (OTwoQuot K))
    (hW : Nat.card ↥(blockU K) = 2 ^ 5) :
    ∃ Φ : ↥(blockU K) ≃* ↥(coreMod 6), ∀ g : MulAut ↥(blockU K), g ∈ autOn K (blockU K) ↔
      ∃ σ ∈ alternatingGroup (Fin 6), ∀ w, Φ (g w) = coreAct 6 σ (Φ w) := by
  have := isMulCommutative_blockU hshort
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hx).2) q hq).symm
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  have hcomm : ⁅blockU K, K⁆ = blockU K := C1.commutator_blockU hshort
  have hne : ¬ K ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro h
    have hbot : ⁅blockU K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [hcomm] at hbot
    rw [hbot] at hW
    simp at hW
  obtain ⟨e⟩ := hA
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := H13.nonempty_autOn_mulEquiv_of_simple hKW hO2 hne
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)
  have hc' := H13.commV_autOn_eq_top hKW hcomm
  have hsq' : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  exact ModA6.exists_core_equiv hsq' (by rw [hW]; norm_num) (autOn K (blockU K)) ⟨eA⟩ hc'

theorem exists_core_equiv_seven {K : Subgroup G} (hshort : IsShort2 K) (hA : IsAlt 7 (OTwoQuot K))
    (hW : Nat.card ↥(blockU K) = 2 ^ 6) :
    ∃ Φ : ↥(blockU K) ≃* ↥(coreMod 7), ∀ g : MulAut ↥(blockU K), g ∈ autOn K (blockU K) ↔
      ∃ σ ∈ alternatingGroup (Fin 7), ∀ w, Φ (g w) = coreAct 7 σ (Φ w) := by
  have := isMulCommutative_blockU hshort
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hx).2) q hq).symm
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  have hcomm : ⁅blockU K, K⁆ = blockU K := C1.commutator_blockU hshort
  have hne : ¬ K ≤ Subgroup.centralizer (blockU K : Set G) := by
    intro h
    have hbot : ⁅blockU K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [hcomm] at hbot
    rw [hbot] at hW
    simp at hW
  obtain ⟨e⟩ := hA
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := H13.nonempty_autOn_mulEquiv_of_simple hKW hO2 hne
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e)
  have hc' := H13.commV_autOn_eq_top hKW hcomm
  have hsq' : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥(blockU K) :=
    (autOn K (blockU K)).subtype.comp eA.symm.toMonoidHom
  have hρ : ρ.range = autOn K (blockU K) := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact (eA.symm σ).2
    · intro ha
      exact ⟨eA ⟨a, ha⟩, by simp [ρ]⟩
  obtain ⟨Φ, hΦ⟩ := ModB.a7PerfectSixCore_of_noPerfectSixA6 ModB.noPerfectSixA6_holds ↥(blockU K) hsq'
    (by rw [hW]) ρ (by rw [hρ]; exact hc')
  refine ⟨Φ, fun g => ⟨fun hg => ?_, fun ⟨σ, hσ, h⟩ => ?_⟩⟩
  · refine ⟨((eA ⟨g, hg⟩ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)), (eA ⟨g, hg⟩).2, fun w => ?_⟩
    have hρg : ρ (eA ⟨g, hg⟩) = g := by simp [ρ]
    have := hΦ (eA ⟨g, hg⟩) w
    rwa [hρg] at this
  · have hg : g = ρ ⟨σ, hσ⟩ := by
      refine MulEquiv.ext fun w => ?_
      apply Φ.injective
      rw [h w, hΦ ⟨σ, hσ⟩ w]
    rw [hg, ← hρ]
    exact ⟨⟨σ, hσ⟩, rfl⟩

end CFSG.Quasithin.ModC
