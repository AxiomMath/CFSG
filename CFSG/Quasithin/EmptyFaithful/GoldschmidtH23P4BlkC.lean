module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Data.Nat.Squarefree

public section

namespace CFSG.Quasithin.H23P4

private theorem squarefree_fifteen : Squarefree (15 : ℕ) := by decide +kernel

theorem perfect_action_trivial {Γ V : Type*} [Group Γ] [Finite Γ] [MulAction Γ V] [Finite V]
    (o : V) (hcard : Nat.card V = 16) (ho : ∀ γ : Γ, γ • o = o) (hperf : commutator Γ = ⊤)
    (hdich : ∀ γ : Γ, (∀ v : V, γ • v = v) ∨ ∀ v : V, γ • v = v → v = o) :
    ∀ (γ : Γ) (v : V), γ • v = v := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  have : Fintype V := Fintype.ofFinite V
  let T : Subgroup Γ := (MulAction.toPermHom Γ V).ker
  have hT : ∀ γ, γ ∈ T ↔ ∀ v : V, γ • v = v := by
    intro γ
    simp only [T, MonoidHom.mem_ker, Equiv.ext_iff, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  have hfix : ∀ γ : Γ, Nat.card (MulAction.fixedBy V γ) = 1 + if γ ∈ T then 15 else 0 := by
    intro γ
    by_cases hγ : γ ∈ T
    · have h1 : MulAction.fixedBy V γ = Set.univ :=
        Set.eq_univ_of_forall fun v => (hT γ).1 hγ v
      simp only [hγ, ↓reduceIte]
      rw [h1, Nat.card_congr (Equiv.Set.univ V), hcard]
    · have h1 : MulAction.fixedBy V γ = {o} := by
        ext v
        rw [MulAction.mem_fixedBy, Set.mem_singleton_iff]
        refine ⟨fun hv => ?_, fun hv => hv ▸ ho γ⟩
        rcases hdich γ with h | h
        · exact absurd ((hT γ).2 h) hγ
        · exact h v hv
      simp only [hγ, ↓reduceIte]
      rw [h1]
      simp
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group Γ V
  have hsum : ∑ g : Γ, Fintype.card (MulAction.fixedBy V g) =
      Fintype.card Γ + 15 * Nat.card T := by
    have h1 : ∀ g : Γ, Fintype.card (MulAction.fixedBy V g) = 1 + if g ∈ T then 15 else 0 :=
      fun g => by rw [← hfix g, Nat.card_eq_fintype_card]
    simp only [h1]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card (α := T),
      Fintype.card_subtype, mul_comm]
  have hΓ : Nat.card T * T.index = Fintype.card Γ := by
    rw [Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hn : T.index ∣ 15 := by
    have h0 := hB
    rw [hsum, ← hΓ] at h0
    have h1 : Nat.card T * (T.index + 15) =
        Nat.card T * (Fintype.card (Quotient (MulAction.orbitRel Γ V)) * T.index) := by
      linarith [h0]
    have h2 := Nat.eq_of_mul_eq_mul_left hTpos h1
    exact (Nat.dvd_add_right (dvd_refl _)).1
      ⟨Fintype.card (Quotient (MulAction.orbitRel Γ V)), by rw [h2]; ring⟩
  have hsq : Squarefree (Nat.card (Γ ⧸ T)) :=
    Squarefree.squarefree_of_dvd hn squarefree_fifteen
  have : IsZGroup (Γ ⧸ T) := IsZGroup.of_squarefree hsq
  have : Group.IsPerfect Γ := Group.isPerfect_def.mpr hperf
  have hsub : Subsingleton (Γ ⧸ T) := by
    by_contra hns
    have : Nontrivial (Γ ⧸ T) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (Γ ⧸ T) inferInstance
  have hTtop : T = ⊤ := by
    rw [← Subgroup.index_eq_one]
    exact Nat.card_of_subsingleton (1 : Γ ⧸ T)
  intro γ v
  exact (hT γ).1 (hTtop ▸ Subgroup.mem_top γ) v

end CFSG.Quasithin.H23P4
