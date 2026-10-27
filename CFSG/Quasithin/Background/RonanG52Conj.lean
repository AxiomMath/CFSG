module

public import CFSG.Quasithin.H13.A6G5

public section

namespace CFSG.Quasithin.RonanG52

open Equiv CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

namespace Aux

local instance decMemG5G1 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Perm.sign σ = 1 ∧ ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

local instance decMemCA6 (σ : Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1))

local instance decMemT0 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1 ⊓ cA6) :=
  (inferInstance : Decidable (σ ∈ g5G1 ∧ σ ∈ cA6))

theorem natCard_eq_filter (K : Subgroup (Perm (Fin 6))) [DecidablePred (· ∈ K)] :
    Nat.card K = ((Finset.univ : Finset (Perm (Fin 6))).filter (· ∈ K)).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_g5G1 : Nat.card g5G1 = 24 := by
  rw [natCard_eq_filter]
  decide +kernel

theorem card_T0 : Nat.card ↥(g5G1 ⊓ cA6) = 8 := by
  rw [natCard_eq_filter]
  decide +kernel

theorem g5G1_ne_cA6 : g5G1 ≠ cA6 := by
  intro h
  have h1 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∈ g5G1 := by decide +kernel
  have h2 : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∉ cA6 := by decide +kernel
  rw [h] at h1
  exact h2 h1

theorem g5G1_le : g5G1 ≤ alternatingGroup (Fin 6) :=
  fun σ hσ => Equiv.Perm.mem_alternatingGroup.mpr hσ.1

theorem cA6_le : cA6 ≤ alternatingGroup (Fin 6) :=
  fun σ hσ => Equiv.Perm.mem_alternatingGroup.mpr hσ.2

theorem T0_le : g5G1 ⊓ cA6 ≤ alternatingGroup (Fin 6) :=
  inf_le_of_left_le g5G1_le

theorem mul_index_eq_360 {K : Subgroup (Perm (Fin 6))} (hK : K ≤ alternatingGroup (Fin 6))
    {n : ℕ} (h : Nat.card K = n) :
    n * (K.subgroupOf (alternatingGroup (Fin 6))).index = 360 := by
  have e : Nat.card (K.subgroupOf (alternatingGroup (Fin 6))) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have h1 := Subgroup.card_mul_index (K.subgroupOf (alternatingGroup (Fin 6)))
  rw [e, h, card_alt6] at h1
  exact h1

theorem relIndex_eq_fifteen {K : Subgroup (Perm (Fin 6))} (hK : K ≤ alternatingGroup (Fin 6))
    (h : Nat.card K = 24) : K.relIndex (alternatingGroup (Fin 6)) = 15 := by
  have h1 := mul_index_eq_360 hK h
  unfold Subgroup.relIndex
  omega

abbrev conjSub (c : Perm (Fin 6)) (K : Subgroup (Perm (Fin 6))) : Subgroup (Perm (Fin 6)) :=
  K.map (MulAut.conj c⁻¹).toMonoidHom

theorem conj_inj (c : Perm (Fin 6)) : Function.Injective (MulAut.conj c⁻¹).toMonoidHom :=
  fun _ _ h => (MulAut.conj c⁻¹).injective h

theorem mem_conjSub {c x : Perm (Fin 6)} {K : Subgroup (Perm (Fin 6))} :
    x ∈ conjSub c K ↔ c * x * c⁻¹ ∈ K := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h
    have e : c * (MulAut.conj c⁻¹).toMonoidHom y * c⁻¹ = y := by
      show c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y
      group
    rw [e]
    exact hy
  · intro h
    refine Subgroup.mem_map.mpr ⟨c * x * c⁻¹, h, ?_⟩
    show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
    group

theorem card_conjSub (c : Perm (Fin 6)) (K : Subgroup (Perm (Fin 6))) :
    Nat.card (conjSub c K) = Nat.card K :=
  Subgroup.card_map_of_injective (conj_inj c)

theorem conjSub_le {c : Perm (Fin 6)} (hc : c ∈ alternatingGroup (Fin 6))
    {K : Subgroup (Perm (Fin 6))} (hK : K ≤ alternatingGroup (Fin 6)) :
    conjSub c K ≤ alternatingGroup (Fin 6) := by
  intro x hx
  have h := Equiv.Perm.mem_alternatingGroup.mp (hK (mem_conjSub.mp hx))
  have hc' := Equiv.Perm.mem_alternatingGroup.mp hc
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [map_mul, map_inv, hc', one_mul, inv_one, mul_one] at h
  exact h

theorem conjSub_injective {c : Perm (Fin 6)} {K K' : Subgroup (Perm (Fin 6))}
    (h : conjSub c K = conjSub c K') : K = K' :=
  Subgroup.map_injective (conj_inj c) h

theorem isPGroup_subgroupOf {T : Subgroup (Perm (Fin 6))}
    (hT : IsSylowTwoOf T (alternatingGroup (Fin 6))) :
    IsPGroup 2 (T.subgroupOf (alternatingGroup (Fin 6))) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT.2.1
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT.1).toEquiv]
  exact hn

theorem exists_conj_of_isSylowTwoOf {T S : Subgroup (Perm (Fin 6))}
    (hT : IsSylowTwoOf T (alternatingGroup (Fin 6)))
    (hS : IsSylowTwoOf S (alternatingGroup (Fin 6))) :
    ∃ c : Perm (Fin 6), c ∈ alternatingGroup (Fin 6) ∧ ∀ t ∈ T, c * t * c⁻¹ ∈ S := by
  let P : Sylow 2 (alternatingGroup (Fin 6)) :=
    (isPGroup_subgroupOf hT).toSylow hT.2.2
  let Q : Sylow 2 (alternatingGroup (Fin 6)) :=
    (isPGroup_subgroupOf hS).toSylow hS.2.2
  haveI : Finite (Sylow 2 (alternatingGroup (Fin 6))) := Sylow.finite_of_finiteIndex P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(alternatingGroup (Fin 6))) P Q
  refine ⟨(g : Perm (Fin 6)), g.2, fun t ht => ?_⟩
  have htA : t ∈ alternatingGroup (Fin 6) := hT.1 ht
  have hxP : (⟨t, htA⟩ : alternatingGroup (Fin 6)) ∈
      (P : Subgroup (alternatingGroup (Fin 6))) :=
    Subgroup.mem_subgroupOf.mpr ht
  have h1 : MulAut.conj g ⟨t, htA⟩ ∈
      ((g • P : Sylow 2 (alternatingGroup (Fin 6))) : Subgroup (alternatingGroup (Fin 6))) :=
    Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hxP
  rw [hg] at h1
  have h2 : MulAut.conj g ⟨t, htA⟩ ∈ S.subgroupOf (alternatingGroup (Fin 6)) := h1
  have h3 : ((MulAut.conj g ⟨t, htA⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ S :=
    Subgroup.mem_subgroupOf.mp h2
  have e : ((MulAut.conj g ⟨t, htA⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      (g : Perm (Fin 6)) * t * (g : Perm (Fin 6))⁻¹ := by
    simp [MulAut.conj_apply]
  rw [e] at h3
  exact h3

theorem isSylowTwoOf_T0 : IsSylowTwoOf (g5G1 ⊓ cA6) (alternatingGroup (Fin 6)) := by
  unfold IsSylowTwoOf
  have h := mul_index_eq_360 T0_le card_T0
  refine ⟨T0_le, IsPGroup.iff_card.mpr ⟨3, ?_⟩, ?_⟩
  · rw [card_T0]
    norm_num
  · omega

end Aux

theorem exists_conj_g5G1_cA6_iff {T G₁ G₂ : Subgroup (Perm (Fin 6))}
    (hsyl : IsSylowTwoOf T (alternatingGroup (Fin 6)))
    (index₁ : G₁.relIndex (alternatingGroup (Fin 6)) = 15)
    (index₂ : G₂.relIndex (alternatingGroup (Fin 6)) = 15)
    (only : ∀ H : Subgroup (Perm (Fin 6)), H ≤ alternatingGroup (Fin 6) → T ≤ H →
      H.relIndex (alternatingGroup (Fin 6)) = 15 → H = G₁ ∨ H = G₂) :
    ∃ c : Perm (Fin 6), c ∈ alternatingGroup (Fin 6) ∧
      ((∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ cA6) ∨
        (∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ cA6)) := by
  obtain ⟨c, hcA, hc⟩ := Aux.exists_conj_of_isSylowTwoOf hsyl Aux.isSylowTwoOf_T0
  have hT₁ : T ≤ Aux.conjSub c g5G1 :=
    fun t ht => Aux.mem_conjSub.mpr (Subgroup.mem_inf.mp (hc t ht)).1
  have hT₂ : T ≤ Aux.conjSub c cA6 :=
    fun t ht => Aux.mem_conjSub.mpr (Subgroup.mem_inf.mp (hc t ht)).2
  have hA₁ : Aux.conjSub c g5G1 ≤ alternatingGroup (Fin 6) :=
    Aux.conjSub_le hcA Aux.g5G1_le
  have hA₂ : Aux.conjSub c cA6 ≤ alternatingGroup (Fin 6) :=
    Aux.conjSub_le hcA Aux.cA6_le
  have hi₁ : (Aux.conjSub c g5G1).relIndex (alternatingGroup (Fin 6)) = 15 :=
    Aux.relIndex_eq_fifteen hA₁ (by rw [Aux.card_conjSub, Aux.card_g5G1])
  have hi₂ : (Aux.conjSub c cA6).relIndex (alternatingGroup (Fin 6)) = 15 :=
    Aux.relIndex_eq_fifteen hA₂ (by rw [Aux.card_conjSub, card_cA6])
  have o₁ := only _ hA₁ hT₁ hi₁
  have o₂ := only _ hA₂ hT₂ hi₂
  have hne : Aux.conjSub c g5G1 ≠ Aux.conjSub c cA6 :=
    fun h => Aux.g5G1_ne_cA6 (Aux.conjSub_injective h)
  refine ⟨c, hcA, ?_⟩
  rcases o₁ with h₁ | h₁ <;> rcases o₂ with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne
  · exact Or.inl ⟨fun g => by rw [← h₁]; exact Aux.mem_conjSub,
      fun g => by rw [← h₂]; exact Aux.mem_conjSub⟩
  · exact Or.inr ⟨fun g => by rw [← h₁]; exact Aux.mem_conjSub,
      fun g => by rw [← h₂]; exact Aux.mem_conjSub⟩
  · exact absurd (h₁.trans h₂.symm) hne

theorem exists_conj_g5G1_cA6 {T G₁ G₂ : Subgroup (Perm (Fin 6))}
    (hsyl : IsSylowTwoOf T (alternatingGroup (Fin 6)))
    (le₁ : G₁ ≤ alternatingGroup (Fin 6)) (le₂ : G₂ ≤ alternatingGroup (Fin 6))
    (T_le₁ : T ≤ G₁) (T_le₂ : T ≤ G₂)
    (index₁ : G₁.relIndex (alternatingGroup (Fin 6)) = 15)
    (index₂ : G₂.relIndex (alternatingGroup (Fin 6)) = 15) (ne : G₁ ≠ G₂)
    (only : ∀ H : Subgroup (Perm (Fin 6)), H ≤ alternatingGroup (Fin 6) → T ≤ H →
      H.relIndex (alternatingGroup (Fin 6)) = 15 → H = G₁ ∨ H = G₂) :
    ∃ c : Perm (Fin 6), c ∈ alternatingGroup (Fin 6) ∧
      ((∀ g ∈ g5G1, c⁻¹ * g * c ∈ G₁) ∧ (∀ g ∈ cA6, c⁻¹ * g * c ∈ G₂) ∨
        (∀ g ∈ g5G1, c⁻¹ * g * c ∈ G₂) ∧ (∀ g ∈ cA6, c⁻¹ * g * c ∈ G₁)) := by
  obtain ⟨c, hcA, hc⟩ := exists_conj_g5G1_cA6_iff hsyl index₁ index₂ only
  have key : ∀ (G : Subgroup (Perm (Fin 6))) (X : Subgroup (Perm (Fin 6))),
      (∀ g, g ∈ G ↔ c * g * c⁻¹ ∈ X) → ∀ g ∈ X, c⁻¹ * g * c ∈ G := fun G X h g hg =>
    (h _).mpr (by rw [show c * (c⁻¹ * g * c) * c⁻¹ = g by group]; exact hg)
  refine ⟨c, hcA, ?_⟩
  rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl ⟨key _ _ h₁, key _ _ h₂⟩
  · exact Or.inr ⟨key _ _ h₁, key _ _ h₂⟩

end CFSG.Quasithin.RonanG52
