module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Vol2.Ch4Sec4Inputs

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

variable {H : Type} [Group H]

theorem ncard_conjSubgroupsBy_eq_index (X K : Subgroup H) :
    (conjSubgroupsBy X K).ncard = ((Subgroup.normalizer (K : Set H)).subgroupOf X).index := by
  let φ : ↥X →* MulAut H := MulAut.conj.comp X.subtype
  let _ : MulAction ↥X (Subgroup H) := MulAction.compHom (Subgroup H) φ
  have hsmul : ∀ (h : ↥X) (Y : Subgroup H), h • Y = Y.map (MulAut.conj (h : H)).toMonoidHom :=
    fun h Y => rfl
  have hstab : MulAction.stabilizer ↥X K = (Subgroup.normalizer (K : Set H)).subgroupOf X := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have horb : MulAction.orbit ↥X K = conjSubgroupsBy X K := by
    ext Y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h K⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, hsmul ⟨t, ht⟩ K⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

theorem commutator_le_of_index_le_two {X N : Subgroup H} (h : (N.subgroupOf X).index ≤ 2)
    (h0 : (N.subgroupOf X).index ≠ 0) : ⁅X, X⁆ ≤ N := by
  rcases (by omega : (N.subgroupOf X).index = 1 ∨ (N.subgroupOf X).index = 2) with h1 | h2
  · have htop := Subgroup.index_eq_one.mp h1
    have hXN : X ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : ↥X) ∈ N.subgroupOf X := htop ▸ Subgroup.mem_top _
      exact this
    exact (Subgroup.commutator_le_self X).trans hXN
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have key : ∀ a b : ↥X, a * b ∈ N.subgroupOf X ↔ (a ∈ N.subgroupOf X ↔ b ∈ N.subgroupOf X) :=
      fun a b => Subgroup.mul_mem_iff_of_index_two h2
    have hinv : ∀ a : ↥X, a⁻¹ ∈ N.subgroupOf X ↔ a ∈ N.subgroupOf X := fun a => inv_mem_iff
    have hc : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥X)⁻¹ * (⟨y, hy⟩ : ↥X)⁻¹ ∈
        N.subgroupOf X := by
      rw [key, key, key, hinv, hinv]
      tauto
    have e : ⁅x, y⁆ = (((⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥X)⁻¹ * (⟨y, hy⟩ : ↥X)⁻¹ : ↥X) :
        H) := by
      rw [commutatorElement_def]
      rfl
    rw [e]
    exact hc

variable [Finite H]

theorem commutator_le_normalizer {K : Subgroup H} (h2 : (conjSubgroups K).ncard ≤ 2)
    (X : Subgroup H) : ⁅X, X⁆ ≤ Subgroup.normalizer (K : Set H) := by
  have hsub : conjSubgroupsBy X K ⊆ conjSubgroups K := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hle : (conjSubgroupsBy X K).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h2
  rw [ncard_conjSubgroupsBy_eq_index] at hle
  exact commutator_le_of_index_le_two hle (Subgroup.index_ne_zero_of_finite)

theorem le_normalizer_of_perfect {K X : Subgroup H} (h2 : (conjSubgroups K).ncard ≤ 2)
    (hX : ⁅X, X⁆ = X) : X ≤ Subgroup.normalizer (K : Set H) :=
  hX ▸ commutator_le_normalizer h2 X

theorem le_normalizer_of_commutator_eq {K X V : Subgroup H} (h2 : (conjSubgroups K).ncard ≤ 2)
    (hV : V = ⁅V, X⁆) :
    V ≤ Subgroup.normalizer (K : Set H) := by
  have h1 : ⁅V, X⁆ ≤ ⁅V ⊔ X, V ⊔ X⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
  rw [hV]
  exact h1.trans (commutator_le_normalizer h2 _)

omit [Finite H] in
theorem ncard_conjSubgroups_of_normal {K : Subgroup H} (hK : K.Normal) :
    (conjSubgroups K).ncard ≤ 2 := by
  have h : conjSubgroups K = {K} := by
    ext K'
    constructor
    · rintro ⟨h, rfl⟩
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hK]; trivial)).trans rfl
    · intro hK'
      rw [Set.mem_singleton_iff.mp hK']
      exact ⟨1, by rw [map_one]; exact (Subgroup.map_id K).symm⟩
  rw [h, Set.ncard_singleton]
  omega

end CFSG.Quasithin.H13.Ch4.E443
