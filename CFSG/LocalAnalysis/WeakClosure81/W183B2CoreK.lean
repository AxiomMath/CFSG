module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKB
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt IsSp4)

theorem w183b2_core_k_of_abs {G : Type} [Group G] [Finite G] {Q : Type} [AddCommGroup Q]
    [Module (AlgebraicClosure (ZMod 2)) Q] [FiniteDimensional (AlgebraicClosure (ZMod 2)) Q]
    {ρ : Representation (AlgebraicClosure (ZMod 2)) G Q} {A₁ A₂ Δ : Subgroup G}
    (h : CoreSetting ρ A₁ A₂ Δ) (hAbs : AbsIrrOverF4 ↥A₁) :
    Nat.card ↥Δ ≤ 4 := by
  by_cases hA : ∃ U : Submodule (AlgebraicClosure (ZMod 2)) Q,
      w183b2SimpleSub ρ (A₁ ⊔ A₂) U ∧ ∀ d ∈ Δ, U.map (ρ d) = U
  · obtain ⟨U, hU, hΔ⟩ := hA
    have hinv : ∀ g : G, ∀ u ∈ U, ρ g u ∈ U := by
      let St : Subgroup G :=
        { carrier := {g | ∀ u ∈ U, ρ g u ∈ U ∧ ρ g⁻¹ u ∈ U}
          mul_mem' := fun {g g'} hg hg' u hu => by
            refine ⟨?_, ?_⟩
            · rw [map_mul, Module.End.mul_apply]
              exact (hg _ ((hg' u hu).1)).1
            · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
              exact (hg' _ ((hg u hu).2)).2
          one_mem' := fun u hu => by simpa using hu
          inv_mem' := fun {g} hg u hu => by simpa using (hg u hu).symm }
      have hN : A₁ ⊔ A₂ ≤ St := fun n hn u hu =>
        ⟨hU.2.1 n hn u hu, hU.2.1 n⁻¹ ((A₁ ⊔ A₂).inv_mem hn) u hu⟩
      have hD : Δ ≤ St := fun d hd u hu => by
        refine ⟨?_, ?_⟩
        · rw [← hΔ d hd]
          exact Submodule.mem_map_of_mem hu
        · rw [← hΔ d⁻¹ (Δ.inv_mem hd)]
          exact Submodule.mem_map_of_mem hu
      have htop : St = ⊤ := by
        rw [eq_top_iff, ← h.gen]
        exact sup_le hN hD
      intro g u hu
      have hg : g ∈ St := by rw [htop]; exact Subgroup.mem_top g
      exact (hg u hu).1
    have hUtop : U = ⊤ := by
      rcases ((ComponentInitial.PairedTensorOrbits.isIrreducible_iff ρ).1 h.irr).2 U hinv with
        h0 | h1
      · exact absurd h0 hU.1
      · exact h1
    refine w183b2_core_k_caseA_of_abs h hAbs (fun V hV => ?_)
    rcases hU.2.2 V hV (by rw [hUtop]; exact le_top) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (h1.trans hUtop)
  · refine le_trans (w183b2_core_k_caseB h (fun U hU => ?_)) (by norm_num)
    by_contra hcon
    refine hA ⟨U, hU, fun d hd => ?_⟩
    by_contra hne
    exact hcon ⟨d, hd, hne⟩

end CFSG.LocalAnalysis.WeakClosure81

end
