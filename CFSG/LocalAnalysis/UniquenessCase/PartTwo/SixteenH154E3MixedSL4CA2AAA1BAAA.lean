module

public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem s16h_sl4_mem_sup_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, x, hx, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, H.mul_mem ha₁ ha₂, b₁ * b₂, K.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * ((a₂ * b₁) * b₂) := by group
      _ = a₁ * ((b₁ * a₂) * b₂) := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, ?_⟩
    rw [hcomm a ha b hb, mul_inv_rev]

theorem s16h_sl4_alt_inf_eq_bot {W : Type} [CommGroup W]
    {L L' : Subgroup (MulAut W)} (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (e : ↥L ≃* alternatingGroup (Fin 5)) : L ⊓ L' = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxe : e x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx z]
    rw [alternatingGroup.center_eq_bot (by norm_num)] at hxe
    exact Subgroup.mem_bot.mpr
      (e.injective ((Subgroup.mem_bot.mp hxe).trans (map_one e).symm))
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2 x hx.2)
  rw [hZ] at hxZ
  exact Subgroup.mem_bot.mpr (Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxZ))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
