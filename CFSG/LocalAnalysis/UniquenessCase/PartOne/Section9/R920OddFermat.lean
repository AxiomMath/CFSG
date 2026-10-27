module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GH74.GLS.LU.Local.FiveSL2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFrob
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddRed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups

theorem eq_zero_of_fixed_of_ne_one {V : Type*} {F : Type} [Field F] [Fintype F] {p : ℕ}
    [Fact p.Prime] [AddCommGroup V] [Module (ZMod p) V] (σ : Representation (ZMod p) SL(2, F) V)
    (hF : ringChar F ≠ 2) (hp : p ≠ 2) (hneg : ∀ v, σ (-1) v = -v)
    (hfpf : ∀ g : SL(2, F), (orderOf g).Prime → orderOf g ≠ 2 → ∀ v, σ g v = v → v = 0)
    {g : SL(2, F)} (hg : g ≠ 1) (v : V) (hv : σ g v = v) : v = 0 := by
  classical
  obtain ⟨ℓ, hℓ, hℓg⟩ := Nat.exists_prime_and_dvd (fun h => hg (orderOf_eq_one_iff.mp h))
  have key : ∀ h : SL(2, F), orderOf h = ℓ → σ h v = v → v = 0 := by
    intro h ho hhv
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hsq := pow_orderOf_eq_one h
      rw [ho] at hsq
      rcases (CFSG.LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hF h).mp hsq with rfl | rfl
      · rw [orderOf_one] at ho
        omega
      · rw [hneg] at hhv
        have h2 : (2 : ZMod p) ≠ 0 := by
          intro h0
          have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
          rw [ZMod.natCast_eq_zero_iff] at h0'
          exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h0')
        have hvv : (2 : ZMod p) • v = 0 := by
          rw [two_smul]
          calc v + v = -v + v := by rw [hhv]
            _ = 0 := neg_add_cancel v
        exact (smul_eq_zero.mp hvv).resolve_left h2
    · exact hfpf h (by rw [ho]; exact hℓ) (by rw [ho]; exact hℓ2) v hhv
  refine key _ (orderOf_pow_orderOf_div (orderOf_pos g).ne' hℓg) ?_
  rw [map_pow, Module.End.pow_apply]
  exact Function.iterate_fixed hv _

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem I9_le_M (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hZ : UCK.ZassenhausPerfect) :
    F09.I9 H ≤ D.M := by
  classical
  rcases em (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ q - 1) with hr | -
  · exact S.I9_le_M_of_odd_dvd hN hyp hr hK461 hK462 hSch
  by_contra hIM
  obtain ⟨p, hp, F, hF, hFt, V, hV, hVm, hVf, σ, hcard, hp2, -, hσ, hneg, hfpf⟩ :=
    S.exists_sl2_rep_of_not_le hN hyp hK461 hK462 hSch hIM
  have hq := S.gt
  have hqF : (Fintype.card F).Prime := by rw [hcard]; exact S.prime
  haveI : Fact (Fintype.card F).Prime := ⟨hqF⟩
  haveI : CharP F (Fintype.card F) := charP_of_card_eq_prime rfl
  have hcast : ∀ n : ℕ, 0 < n → n ≤ 5 → (n : F) ≠ 0 := fun n hn h5 h =>
    absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff F _ n).mp h)) (by omega)
  have h2 : (2 : F) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by norm_num)
  have h4 : (2 : F) ^ 2 ≠ 1 := fun h => hcast 3 (by norm_num) (by norm_num) (by
    push_cast
    linear_combination h)
  have hchar : ringChar F ≠ 2 := by
    rw [ringChar.eq F (Fintype.card F)]
    omega
  haveI : Nontrivial SL(2, F) := nontrivial_of_ne _ _ (CFSG.PSL2Table.neg_one_ne_one_SL h2)
  obtain ⟨e⟩ := hZ p SL(2, F) (Matrix.SL2.commutator_eq_top h2 h4) V σ hσ
    (fun g hg v hv => eq_zero_of_fixed_of_ne_one σ hchar hp2 hneg hfpf hg v hv)
    Finite.one_lt_card.ne'
  have h120 : Fintype.card F ∣ Nat.factorial 5 := by
    rw [← CFSG.PSL2Table.card_unipSL, show Nat.factorial 5 = 120 by rfl,
      ← CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm]
    exact Subgroup.card_subgroup_dvd_card _
  have h5 := (Nat.Prime.dvd_factorial hqF).mp h120
  omega

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
