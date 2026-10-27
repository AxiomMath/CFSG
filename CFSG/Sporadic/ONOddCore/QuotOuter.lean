module

public import CFSG.Sporadic.ONOddCore.QuotTauIso
public import CFSG.Sporadic.ONOddCore.QuotSigma

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_record
    {d f g : ℕ} (hd : d < 3) (hf : f < 2) (hg : g < 2) :
    ∃ k < 12, (recK k).diag = d ∧ (recK k).field = f ∧ (recK k).graph = g := by
  refine ⟨4 * d + 2 * f + g, by omega, ?_⟩
  have h := recK_triple (k := 4 * d + 2 * f + g) (by omega)
  interval_cases d <;> interval_cases f <;> interval_cases g <;> simpa [tripleList] using h

theorem r3e_on_twelve_quotient_outer_representatives :
    Nat.card RM = 40320 ∧ ⁅RM, RM⁆ = onX ∧
      RM ⊓ Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) = ⊥ ∧
      Function.Injective iotaR ∧ Function.Injective resX ∧
      (∀ {d d' f f' g g' : ℕ}, d < 3 → d' < 3 → f < 2 → f' < 2 → g < 2 → g' < 2 →
        (sigmaX d f g : Outer onX) = (sigmaX d' f' g' : Outer onX) → d = d' ∧ f = f' ∧ g = g') ∧
      (∀ α : MulAut onX, ∃ d < 3, ∃ f < 2, ∃ g < 2,
        (α : Outer onX) = (sigmaX d f g : Outer onX)) ∧
      (∀ d f g : ℕ, d < 3 → f < 2 → g < 2 → ∀ r : RM,
        sigmaX d f g * iotaR r * (sigmaX d f g)⁻¹ ∈ iotaR.range) ∧
      (∀ j < 2, qGenPerm j = onu * permOfArr 120 Data.M120Chain.generators[j]! * onu⁻¹) ∧
      qGroup = RM ∧
      ∀ k < 12,
        (∀ j (hj : j < 2), ((tauAut k ⟨qGenPerm j, qGenPerm_mem_RM hj⟩ : RM) :
          Equiv.Perm (Fin 120)) = qImgPerm (recK k) j) ∧
        (∀ x : RM, ((tauAut k x : RM) : Equiv.Perm (Fin 120)) = quotFun (recK k) (toQ x)) ∧
        (∀ x : onX, ((tauAut k ⟨x, onX_le_RM x.2⟩ : RM) : Equiv.Perm (Fin 120)) =
          ((sigmaX (recK k).diag (recK k).field (recK k).graph x : onX) :
            Equiv.Perm (Fin 120))) ∧
        ∀ r : RM, iotaR (tauAut k r) = sigmaX (recK k).diag (recK k).field (recK k).graph *
          iotaR r * (sigmaX (recK k).diag (recK k).field (recK k).graph)⁻¹ := by
  refine ⟨card_RM, commutator_RM, RM_inf_centralizer, iotaR_injective, resX_injective,
    fun hd hd' hf hf' hg hg' h => sigmaX_outer_injective hd hd' hf hf' hg hg' h,
    fun α => ?_, fun d f g hd hf hg r => ?_, fun j hj => qGenPerm_eq hj, qGroup_eq_RM,
    fun k hk => ⟨fun j hj => tauAut_gen hk hj, tauAut_eq_quotFun hk, tauAut_X hk,
      iotaR_tauAut hk⟩⟩
  · obtain ⟨d, hd, f, hf, g, hg, x, rfl⟩ := exists_sigma α
    refine ⟨d, hd, f, hf, g, hg, ?_⟩
    have h1 : ((MulAut.conj x : MulAut onX) : Outer onX) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (MonoidHom.mem_range.2 ⟨x, rfl⟩)
    rw [QuotientGroup.mk_mul, h1, one_mul]
  · obtain ⟨k, hk, rfl, rfl, rfl⟩ := exists_record hd hf hg
    exact ⟨tauAut k r, iotaR_tauAut hk r⟩

end CFSG.Sporadic.ONOddCore
