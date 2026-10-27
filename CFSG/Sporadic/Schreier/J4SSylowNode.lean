
module

public import CFSG.Sporadic.Schreier.J4SSylowNodeBase

public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ

theorem sylow_five_generated
    (S : Sylow 2 J) :
    (∃ s : Finset J, s.card ≤ 5 ∧ Subgroup.closure (s : Set J) = S) ∧
      ∃ d ≤ 5, Nat.card ((S : Subgroup J) ⧸ frattini (S : Subgroup J)) = 2 ^ d ∧
        Nonempty (Additive ((S : Subgroup J) ⧸ frattini (S : Subgroup J)) ≃+ (Fin d → ZMod 2)) := by
  classical
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S0Sylow S
  have hS : (S : Subgroup J) = S0.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, S0Sylow_coe]
    rfl
  let t : Fin 5 → J := fun i => g * gens5 i * g⁻¹
  have ht : (S : Subgroup J) = Subgroup.closure (Set.range t) := by
    rw [hS, S0_eq_closure_gens5, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  refine ⟨⟨Finset.univ.image t, ?_, ?_⟩, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ht]
  · have hP : IsPGroup 2 (S : Subgroup J) := S.isPGroup'
    obtain ⟨-, hcomm, hpow, -, d, hd, he⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
    let _ : CommGroup ((S : Subgroup J) ⧸ frattini (S : Subgroup J)) :=
      IsMulCommutative.instCommGroup
    have htS : ∀ i, t i ∈ (S : Subgroup J) := fun i => ht ▸ Subgroup.subset_closure ⟨i, rfl⟩
    let w : Fin 5 → (S : Subgroup J) ⧸ frattini (S : Subgroup J) := fun i =>
      QuotientGroup.mk' _ ⟨t i, htS i⟩
    have h1 : Subgroup.closure (Set.range fun i => (⟨t i, htS i⟩ : (S : Subgroup J))) = ⊤ := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (S : Subgroup J))
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        ← Set.range_comp]
      exact ht.symm
    have hgen : Subgroup.closure (Set.range w) = ⊤ := by
      have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (frattini (S : Subgroup J)))) h1
      rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), ← Set.range_comp] at h2
      exact h2
    have hcard := card_le_of_closure_two w (fun i => hpow _) hgen
    refine ⟨d, ?_, hd, he⟩
    rw [hd] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

theorem R3E_J4_five_generator_Sylow_two_subgroup :
    U ≤ K ∧ Nat.card U = 1024 ∧
      Subgroup.closure {m | ∃ g ∈ U, m = g * vS * g⁻¹} = N ∧
      N ≤ S0 ∧ U ≤ S0 ∧ (N.subgroupOf S0).Normal ∧ N ⊓ U = ⊥ ∧ N ⊔ U = S0 ∧
      Nat.card S0 = 2 ^ 21 ∧ (∃ P : Sylow 2 J, (P : Subgroup J) = S0) ∧
      ∀ S : Sylow 2 J, (∃ s : Finset J, s.card ≤ 5 ∧ Subgroup.closure (s : Set J) = S) ∧
        ∃ d ≤ 5, Nat.card ((S : Subgroup J) ⧸ frattini (S : Subgroup J)) = 2 ^ d ∧
          Nonempty (Additive ((S : Subgroup J) ⧸ frattini (S : Subgroup J)) ≃+ (Fin d → ZMod 2)) :=
  ⟨U_le_K, card_U, conjGen_eq_N, N_le_S0, U_le_S0, N_normal_in_S0, N_inf_U, N_sup_U, card_S0,
    ⟨S0Sylow, S0Sylow_coe⟩, sylow_five_generated⟩

end CFSG.Sporadic.J4Schreier
