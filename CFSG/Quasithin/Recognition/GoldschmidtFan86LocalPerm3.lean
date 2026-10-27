module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem localHom_surjective_of_valence_three {v : V} (hv : Fan86.valence Γ v = 3) :
    Function.Surjective (F.localHom v) := by
  classical
  have hp := F.valence_isPrime v
  have := F.finite_neighborSet v
  have := Fintype.ofFinite (Γ.neighborSet v)
  have hcard : Fintype.card (Γ.neighborSet v) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hv
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence v
  have hσ := F.orderOf_localHom hx hxo
  let σ : Perm (Γ.neighborSet v) := F.localHom v ⟨x, hx⟩
  let Q : Subgroup (Perm (Γ.neighborSet v)) := (F.localHom v).range
  have hσQ : σ ∈ Q := ⟨_, rfl⟩
  have h3 : 3 ∣ Nat.card Q := by
    have := orderOf_dvd_natCard (⟨σ, hσQ⟩ : Q)
    rwa [Subgroup.orderOf_mk, hσ, hv] at this
  have h6 : Nat.card Q ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card Q
    rwa [Nat.card_eq_fintype_card (α := Perm (Γ.neighborSet v)), Fintype.card_perm, hcard] at this
  have hne : Nat.card Q ≠ 3 := by
    intro h
    have hle : Subgroup.zpowers σ ≤ Q := Subgroup.zpowers_le.2 hσQ
    have hz : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hσ, hv]
    have heq : Subgroup.zpowers σ = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hz, h])
    obtain ⟨a, ha⟩ := F.exists_adj v
    obtain ⟨g, hg, hga, c, hc, hgc⟩ := F.frobenius_nonreg v a ha
    let τ : Perm (Γ.neighborSet v) := F.localHom v ⟨g, hg⟩
    have hτQ : τ ∈ Subgroup.zpowers σ := heq ▸ (⟨_, rfl⟩ : τ ∈ Q)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hτQ
    have hcomm : Commute τ σ := by
      rw [← hk]
      exact (Commute.refl σ).zpow_left k
    have hτa : τ ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext hga
    have hτ1 : τ = 1 := by
      ext b
      obtain ⟨i, hi⟩ := FrobPrime.exists_pow_apply_eq hp rfl hσ ⟨a, ha⟩ b
      have h2 := congrArg (fun f : Perm (Γ.neighborSet v) => f ⟨a, ha⟩) (hcomm.pow_right i).eq
      simp only [Perm.mul_apply, hτa] at h2
      rw [hi] at h2
      exact congrArg Subtype.val h2
    apply hgc
    have := congrArg (fun f : Perm (Γ.neighborSet v) => ((f ⟨c, hc⟩ : Γ.neighborSet v) : V)) hτ1
    exact this
  have h6' : Nat.card Q = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) h6
    generalize Nat.card Q = m at h3 h6 hne hle ⊢
    interval_cases m <;> simp_all
  have htop : Q = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [h6', Nat.card_eq_fintype_card (α := Perm (Γ.neighborSet v)), Fintype.card_perm, hcard]
    rfl
  exact MonoidHom.range_eq_top.1 htop

theorem exists_perm3 {v : V} (hv : Fan86.valence Γ v = 3) :
    ∃ φ : ↥(MulAction.stabilizer G v) →* Perm (Fin 3), Function.Surjective φ ∧
      ∀ g : ↥(MulAction.stabilizer G v), φ g = 1 ↔ (g : G) ∈ nbrStab Γ G v := by
  classical
  have := F.finite_neighborSet v
  have := Fintype.ofFinite (Γ.neighborSet v)
  have hcard : Fintype.card (Γ.neighborSet v) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hv
  let e : Γ.neighborSet v ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  refine ⟨e.permCongrHom.toMonoidHom.comp (F.localHom v),
    e.permCongrHom.surjective.comp (F.localHom_surjective_of_valence_three hv), fun g => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  exact MonoidHom.mem_ker.symm.trans (F.mem_ker_localHom v g)

end FanTree

end CFSG.Quasithin.Fan86
