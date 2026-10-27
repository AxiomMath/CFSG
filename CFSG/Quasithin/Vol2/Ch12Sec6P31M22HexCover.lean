module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.P31Sec.M22Hex

theorem allNS_of_surjective_of_comm_ker {S Q Q' : Type} [Group S] [Group Q] [Group Q']
    (f : Q →* Q') (hf : Function.Surjective f)
    (hker : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a) (h : AllNS S Q') : AllNS S Q := by
  haveI : Group.IsSolvable ↥f.ker :=
    isSolvable_of_comm fun a b => Subtype.ext (hker a a.2 b b.2)
  exact AllNS.of_split f.ker AllNS.of_solvable
    (AllNS.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm h)

theorem allNS_alt6_of_surjective_of_comm_ker {Q : Type} [Group Q]
    (f : Q →* ↥(alternatingGroup (Fin 6))) (hf : Function.Surjective f)
    (hker : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a) :
    AllNS ↥(alternatingGroup (Fin 6)) Q :=
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  allNS_of_surjective_of_comm_ker f hf hker (AllNS.of_simple this (MulEquiv.refl _))

theorem cover_hexad {G M : Type} [Group G] [Group M] (π : G →* M) (hπ : Function.Surjective π)
    (hKc : ∀ z ∈ π.ker, ∀ g : G, g * z = z * g)
    (hKchar : ∀ α : G ≃* G, π.ker.map α.toMonoidHom = π.ker)
    (S : Subgroup G) (B : Subgroup M) (hSB : S.map π ≤ B)
    (huniq : ∀ Q : Subgroup M, S.map π ≤ Q → Q.index = B.index → Q = B)
    (hself : ∀ x ∈ Subgroup.normalizer (B : Set M), x ∈ B)
    (f : ↥B →* ↥(alternatingGroup (Fin 6))) (hf : Function.Surjective f)
    (hker : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a) :
    ∃ B' : Subgroup G, S ≤ B' ∧ AllNS ↥(alternatingGroup (Fin 6)) ↥B' ∧
      (∃ φ : ↥B' →* ↥(alternatingGroup (Fin 6)), Function.Surjective φ) ∧
      (∀ x ∈ Subgroup.normalizer (B' : Set G), x ∈ B') ∧
      (∀ α : G ≃* G, (∀ x : G, x ∈ S ↔ α x ∈ S) → ∀ x : G, x ∈ B' ↔ α x ∈ B') := by
  have hSB' : S ≤ B.comap π := fun s hs => Subgroup.mem_comap.2 (hSB ⟨s, hs, rfl⟩)
  let ρ : ↥(B.comap π) →* ↥B := π.subgroupComap B
  have hρ : Function.Surjective ρ := π.subgroupComap_surjective B hπ
  have hρker : ∀ a ∈ ρ.ker, ∀ b ∈ ρ.ker, a * b = b * a := by
    intro a ha b _
    have ha1 : π (a : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
    exact Subtype.ext (hKc _ (MonoidHom.mem_ker.2 ha1) (b : G)).symm
  have key : ∀ α : G ≃* G, (∀ x : G, x ∈ S ↔ α x ∈ S) →
      ∀ x : G, x ∈ B.comap π → α x ∈ B.comap π := by
    intro α hα x hx
    set B'' : Subgroup G := (B.comap π).map α.toMonoidHom with hB''
    have hK : π.ker ≤ B'' := by
      rw [← hKchar α]
      refine Subgroup.map_mono fun z hz => ?_
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hz]
      exact B.one_mem
    have hSB'' : S.map π ≤ B''.map π := by
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s, ?_, rfl⟩
      have hs' : α.symm s ∈ S := (hα _).2 (by simpa using hs)
      exact ⟨α.symm s, hSB' hs', by simp⟩
    have hidx : (B''.map π).index = B.index := by
      rw [Subgroup.index_map_eq B'' hπ hK]
      exact (Subgroup.index_map_equiv (B.comap π) α).trans
        (Subgroup.index_comap_of_surjective B hπ)
    have heq : B''.map π = B := huniq _ hSB'' hidx
    have hmem : α x ∈ B'' := ⟨x, hx, rfl⟩
    show π (α x) ∈ B
    rw [← heq]
    exact Subgroup.mem_map_of_mem π hmem
  refine ⟨B.comap π, hSB', ?_, ⟨f.comp ρ, hf.comp hρ⟩, ?_, ?_⟩
  · exact allNS_of_surjective_of_comm_ker ρ hρ hρker
      (allNS_alt6_of_surjective_of_comm_ker f hf hker)
  · intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx
    have hπx : π x ∈ Subgroup.normalizer (B : Set M) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      obtain ⟨z, rfl⟩ := hπ y
      have h2 : z ∈ B.comap π ↔ x * z * x⁻¹ ∈ B.comap π := hx z
      have e : π x * π z * (π x)⁻¹ = π (x * z * x⁻¹) := by simp
      rw [e]
      exact h2
    exact hself _ hπx
  · intro α hα x
    refine ⟨key α hα x, fun hx => ?_⟩
    have hα' : ∀ y : G, y ∈ S ↔ α.symm y ∈ S := fun y => by
      have := hα (α.symm y)
      rwa [MulEquiv.apply_symm_apply, Iff.comm] at this
    simpa using key α.symm hα' (α x) hx

end CFSG.Quasithin.H13.P31Sec.M22Hex
