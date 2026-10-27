module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs
public import CFSG.Quasithin.Background.PSL2TwoNilpotent
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem outTwoNilpotent_of_twoNilpotent_outer {S : Type} [Group S]
    (h : TwoNilpotent (Outer S)) :
    ∃ N : Subgroup (MulAut S), N.Normal ∧ innAut S ≤ N ∧ Odd ((innAut S).relIndex N) ∧
      ∀ α : MulAut S, ∃ k : ℕ, α ^ (2 ^ k) ∈ N := by
  obtain ⟨M, hM, hodd, h2⟩ := h
  set π : MulAut S →* Outer S := QuotientGroup.mk' (inner S) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hle : innAut S ≤ M.comap π := fun x hx => by
    have hx' : x ∈ inner S := hx
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx'
    change π x ∈ M
    rw [h1]
    exact M.one_mem
  refine ⟨M.comap π, hM.comap π, hle, ?_, fun α => ?_⟩
  · let ψ : ↥(M.comap π) →* ↥M :=
      (π.comp (M.comap π).subtype).codRestrict M fun x => x.2
    have hψs : Function.Surjective ψ := fun m => by
      obtain ⟨a, ha⟩ := hπs m
      exact ⟨⟨a, by change π a ∈ M; rw [ha]; exact m.2⟩, Subtype.ext ha⟩
    have hker : ψ.ker = (innAut S).subgroupOf (M.comap π) := by
      ext x
      simp [ψ, Subgroup.mem_subgroupOf, hπ, QuotientGroup.eq_one_iff]
      rfl
    have hrel : (innAut S).relIndex (M.comap π) = Nat.card M := by
      show ((innAut S).subgroupOf (M.comap π)).index = Nat.card M
      rw [Subgroup.index_eq_card, ← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv
    rw [hrel]
    exact hodd
  · obtain ⟨k, hk⟩ := h2 (π α)
    exact ⟨k, by simpa only [Subgroup.mem_comap, map_pow] using hk⟩

theorem twoNilpotent_of_comm {A : Type*} [Group A] [Finite A] (h : ∀ a b : A, a * b = b * a) :
    TwoNilpotent A :=
  TwoNilpotent.of_normal_comm ⊤ (fun a _ b _ => h a b) fun a => ⟨0, by simp⟩

theorem twoNilpotent_of_isCyclic {A : Type*} [Group A] [Finite A] [IsCyclic A] :
    TwoNilpotent A :=
  twoNilpotent_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b

theorem twoNilpotent_of_isPGroup_two {A : Type*} [Group A] (h : IsPGroup 2 A) : TwoNilpotent A :=
  ⟨⊥, inferInstance, by rw [Subgroup.card_bot]; exact odd_one, fun a => by
    obtain ⟨k, hk⟩ := h a
    exact ⟨k, by rw [hk]; exact Subgroup.one_mem _⟩⟩

theorem twoNilpotent_of_odd {A : Type*} [Group A] (h : Odd (Nat.card A)) : TwoNilpotent A :=
  ⟨⊤, inferInstance, by rwa [Subgroup.card_top], fun a => ⟨0, by simp⟩⟩

theorem isPerfect_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Group.IsPerfect S := by
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (((commutator_eq_bot_iff S).mp h).is_comm.comm a b)
  · exact h

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

noncomputable def centerQuotientEquiv {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : S ⧸ Subgroup.center S ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnab)).trans
    QuotientGroup.quotientBot

end CFSG.Quasithin.H13.OutTwoNilp
