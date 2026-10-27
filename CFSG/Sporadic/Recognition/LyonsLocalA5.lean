module

public import CFSG.Sporadic.Recognition.LyonsAS4Cover
public import CFSG.Sporadic.Recognition.LyonsAS4Perm

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def pts5 : Fin 5 ≃ {x : Fin 11 // 6 ≤ x.val} where
  toFun i := ⟨⟨i.val + 6, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 6, by have := x.1.2; omega⟩
  left_inv i := by ext; simp
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have := x.2
    simp only
    omega

@[expose] def ι5 : Perm (Fin 5) →* Perm (Fin 11) := Equiv.Perm.extendDomainHom pts5

theorem ι5_injective : Function.Injective ι5 := Equiv.Perm.extendDomainHom_injective pts5

theorem sign_ι5 (σ : Perm (Fin 5)) : sign (ι5 σ) = sign σ := by
  change sign (σ.extendDomain pts5) = sign σ
  exact sign_extendDomain σ pts5

theorem ι5_apply_of_lt (σ : Perm (Fin 5)) {x : Fin 11} (hx : x.val < 6) : ι5 σ x = x := by
  change (σ.extendDomain pts5) x = x
  apply Equiv.Perm.extendDomain_apply_not_subtype
  simp only [not_le]
  exact hx

@[expose] def A5p : Subgroup (Perm (Fin 11)) := (alternatingGroup (Fin 5)).map ι5

theorem card_A5p : Nat.card ↥A5p = 60 := by
  rw [A5p, Subgroup.card_map_of_injective ι5_injective, nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem A5p_even {σ : Perm (Fin 11)} (h : σ ∈ A5p) : sign σ = 1 := by
  obtain ⟨τ, hτ, rfl⟩ := h
  rw [sign_ι5]
  exact (mem_alternatingGroup).1 hτ

theorem A5p_fix {σ : Perm (Fin 11)} (h : σ ∈ A5p) {x : Fin 11} (hx : x.val < 6) : σ x = x := by
  obtain ⟨τ, -, rfl⟩ := h
  exact ι5_apply_of_lt τ hx

theorem A5p_comm_x1p {σ : Perm (Fin 11)} (h : σ ∈ A5p) : σ * x1p = x1p * σ := by
  have hd : Disjoint σ x1p := by
    intro x
    by_cases hx : x.val < 6
    · left; exact A5p_fix h hx
    · right
      apply x1p_apply_of_ne <;> (intro hh; apply hx; rw [hh]; decide)
  exact hd.commute

theorem A5p_comm_x2p {σ : Perm (Fin 11)} (h : σ ∈ A5p) : σ * x2p = x2p * σ := by
  have hd : Disjoint σ x2p := by
    intro x
    by_cases hx : x.val < 6
    · left; exact A5p_fix h hx
    · right
      revert x
      decide
  exact hd.commute

noncomputable def A5pEquiv : alternatingGroup (Fin 5) ≃* ↥A5p :=
  (alternatingGroup (Fin 5)).equivMapOfInjective ι5 ι5_injective

instance : IsSimpleGroup ↥A5p := A5pEquiv.symm.isSimpleGroup

theorem A5p_eq_bot_of_odd {J : Subgroup (Perm (Fin 11))} (hJ : J ≤ A5p)
    (hn : ∀ g ∈ A5p, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hodd : Odd (Nat.card ↥J)) : J = ⊥ := by
  have hnorm : (J.subgroupOf A5p).Normal := by
    refine ⟨fun j hj g => ?_⟩
    rw [mem_subgroupOf] at hj ⊢
    simpa using hn g.1 g.2 j hj
  have := hnorm
  rcases (inferInstance : IsSimpleGroup ↥A5p).eq_bot_or_eq_top_of_normal
    (J.subgroupOf A5p) with h | h
  · rw [eq_bot_iff]
    intro j hj
    have : (⟨j, hJ hj⟩ : ↥A5p) ∈ J.subgroupOf A5p := hj
    rw [h, Subgroup.mem_bot] at this
    have := congrArg Subtype.val this
    exact Subgroup.mem_bot.2 this
  · exfalso
    have hJA : J = A5p := by
      apply le_antisymm hJ
      intro a ha
      have : (⟨a, ha⟩ : ↥A5p) ∈ J.subgroupOf A5p := by rw [h]; exact mem_top _
      exact this
    rw [hJA, card_A5p] at hodd
    exact absurd hodd (by decide)

namespace IsCover11

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

@[expose] def A5sub (ρ : E →* Perm (Fin 11)) : Subgroup E := A5p.comap ρ

theorem mem_A5sub {e : E} : e ∈ A5sub ρ ↔ ρ e ∈ A5p := Iff.rfl

theorem card_A5sub (h : IsCover11 ρ z) : Nat.card ↥(A5sub ρ) = 120 := by
  rw [A5sub, h.card_comap (fun σ hσ => (mem_alternatingGroup).2 (A5p_even hσ)), card_A5p]

theorem eq_bot_of_odd_normal (h : IsCover11 ρ z) {J : Subgroup E} (hJ : J ≤ A5sub ρ)
    (hn : ∀ g ∈ A5sub ρ, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hodd : Odd (Nat.card ↥J)) : J = ⊥ := by
  have hJρ : J.map ρ ≤ A5p := by
    rintro _ ⟨j, hj, rfl⟩
    exact hJ hj
  have hn' : ∀ σ ∈ A5p, ∀ τ ∈ J.map ρ, σ * τ * σ⁻¹ ∈ J.map ρ := by
    rintro σ hσ _ ⟨j, hj, rfl⟩
    obtain ⟨g, hg⟩ := h.exists_lift (A5p_even hσ)
    have hgA : g ∈ A5sub ρ := by rw [mem_A5sub, hg]; exact hσ
    refine ⟨g * j * g⁻¹, hn g hgA j hj, ?_⟩
    rw [map_mul, map_mul, map_inv, hg]
  have hoddρ : Odd (Nat.card ↥(J.map ρ)) :=
    Odd.of_dvd_nat hodd (Subgroup.card_map_dvd J ρ)
  have hbot := A5p_eq_bot_of_odd hJρ hn' hoddρ
  rw [eq_bot_iff]
  intro j hj
  have hρj : ρ j = 1 := by
    have : ρ j ∈ J.map ρ := ⟨j, hj, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rcases h.mem_ker_iff.1 hρj with h1 | h1
  · exact Subgroup.mem_bot.2 h1
  · exfalso
    rw [h1] at hj
    have h2 : orderOf (⟨z, hj⟩ : ↥J) ∣ Nat.card ↥J := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, h.orderOf_z] at h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end IsCover11

end CFSG.Sporadic.Recognition.LyonsSims
