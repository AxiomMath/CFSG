module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

@[expose] def HasOffender {G : Type*} [Group G] (J K : Subgroup G) : Prop :=
  ∃ g ∈ J, ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf g = r ∧ r ∣ Nat.card K ∧
    ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 J

theorem HasOffender.map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {J K : Subgroup G} (h : HasOffender J K) :
    HasOffender (J.map e.toMonoidHom) (K.map e.toMonoidHom) := by
  obtain ⟨g, hg, r, hr, h5, ho, hd, hc⟩ := h
  refine ⟨e g, Subgroup.mem_map_of_mem _ hg, r, hr, h5, ?_, ?_, ?_⟩
  · rw [← ho]
    exact orderOf_injective e.toMonoidHom e.injective g
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rintro _ ⟨k, hk, rfl⟩
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact ⟨g * k * g⁻¹ * k⁻¹, hc k hk, by simp⟩

theorem HasOffender.of_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {J K : Subgroup G} (h : HasOffender (J.map e.toMonoidHom) (K.map e.toMonoidHom)) :
    HasOffender J K := by
  have h' := h.map_mulEquiv e.symm
  have hmap : ∀ L : Subgroup G,
      (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := fun L => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id L
    ext x
    simp
  rwa [hmap, hmap] at h'

theorem isParabolicTwo_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {J : Subgroup G} (h : IsParabolicTwo ⊤ J) : IsParabolicTwo ⊤ (J.map e.toMonoidHom) := by
  obtain ⟨-, T, ⟨-, hTp, hTi⟩, hN⟩ := h
  refine ⟨le_top, T.map e.toMonoidHom, ⟨le_top, hTp.map _, ?_⟩, ?_⟩
  · have h1 : ((T.map e.toMonoidHom).subgroupOf ⊤).index = (T.map e.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have h2 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right _
    have h3 : (T.map e.toMonoidHom).index = T.index := Subgroup.index_map_equiv T e
    rw [h1, h3]
    rwa [h2] at hTi
  · intro x hx
    have hx' := (Subgroup.mem_inf.mp hx).2
    rw [← Subgroup.map_equiv_normalizer_eq] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hN ⟨Subgroup.mem_top _, hy⟩, rfl⟩

theorem eq_bot_of_perfect_of_le_solvable {X : Type*} [Group X] {J K : Subgroup X}
    [Group.IsSolvable J] (hKJ : K ≤ J) (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  by_contra hne
  have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hKJ)
  have hperf : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact (IsSolvable.commutator_lt_top_of_nontrivial (G := K)).ne
    (Group.isPerfect_def.mp hperf)

@[expose] noncomputable def sylowOfTopTwo {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : Sylow 2 X :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hT.2.1.toSylow (by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h)

theorem coe_sylowOfTopTwo {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : ((sylowOfTopTwo hT : Sylow 2 X) : Subgroup X) = T := rfl

@[expose] def DicksonSL2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = 2 ^ f → Odd f →
    ∀ H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), ⁅H, H⁆ = H → H ≠ ⊥ →
      ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card H ∧ r ∣ Nat.card K - 1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
