module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.SBd19F

open scoped IsMulCommutative

theorem sylow_inf_center_eq_bot {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {p : ℕ}
    [Fact p.Prime] (P : Sylow p L) [IsMulCommutative (P : Subgroup L)] :
    (P : Subgroup L) ⊓ Subgroup.center L = ⊥ := by
  classical
  let τ : L →* (P : Subgroup L) := MonoidHom.transfer (MonoidHom.id (P : Subgroup L))
  have hτ : ∀ g : L, τ g = 1 := by
    intro g
    have hg : g ∈ commutator L := Group.IsPerfect.mem_commutator
    exact MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker τ hg)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzP, hzZ⟩ := Subgroup.mem_inf.mp hz
  have key : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup L) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := fun k g₀ _ => by
    have := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hzZ k) g₀
    rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup L)) z key
  have hz1 : z ^ (P : Subgroup L).index = 1 := by
    have h2 : (⟨z ^ (P : Subgroup L).index, _⟩ : (P : Subgroup L)) = 1 :=
      h1.symm.trans (hτ z)
    exact congrArg Subtype.val h2
  have hord : orderOf z ∣ (P : Subgroup L).index := orderOf_dvd_of_pow_eq_one hz1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨z, hzP⟩
  have hk' : orderOf z = p ^ k := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  have hk0 : k = 0 := by
    by_contra hne
    exact P.not_dvd_index ((dvd_pow_self p hne).trans (hk' ▸ hord))
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
  rw [hk']
  exact Subgroup.one_mem _

theorem exists_noncyclic_sylow_quotient {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    {p : ℕ} [Fact p.Prime] {E : Subgroup L} (hEexp : ∀ x ∈ E, x ^ p = 1)
    (hE : Nat.card E = p ^ 2) :
    ∃ Q : Sylow p (L ⧸ Subgroup.center L), ¬ IsCyclic (Q : Subgroup (L ⧸ Subgroup.center L)) := by
  classical
  by_contra hcon
  push Not at hcon
  have hEp : IsPGroup p E := fun x => by
    refine ⟨1, ?_⟩
    simpa using Subtype.ext (hEexp x x.2)
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  let π : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map π).exists_le_sylow
  have hQc : IsCyclic (Q : Subgroup (L ⧸ Subgroup.center L)) := hcon Q
  have hrcyc : IsCyclic ((P : Subgroup L).map π) := by
    have : IsCyclic (((P : Subgroup L).map π).subgroupOf (Q : Subgroup (L ⧸ Subgroup.center L))) :=
      inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQ).surjective
  let f : (P : Subgroup L) →* (P : Subgroup L).map π := π.subgroupMap (P : Subgroup L)
  have hker : f.ker ≤ Subgroup.center (P : Subgroup L) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : (x : L) ∈ Subgroup.center L := by
      have : π x = 1 := by
        have := MonoidHom.mem_ker.mp hx
        exact congrArg Subtype.val this
      exact (QuotientGroup.eq_one_iff _).mp this
    exact Subtype.ext (Subgroup.mem_center_iff.mp h1 y)
  have : IsMulCommutative (P : Subgroup L) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hker
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : (x : L) ∈ Subgroup.center L := by
      have : π x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp this
    have := sylow_inf_center_eq_bot P
    have hx1 : (x : L) ∈ (P : Subgroup L) ⊓ Subgroup.center L := ⟨x.2, hxZ⟩
    rw [this, Subgroup.mem_bot] at hx1
    exact Subgroup.mem_bot.mpr (Subtype.ext hx1)
  have hPcyc : IsCyclic (P : Subgroup L) :=
    have := hrcyc
    isCyclic_of_injective f hinj
  have hEcyc : IsCyclic E := by
    have : IsCyclic (E.subgroupOf (P : Subgroup L)) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEP).surjective
  obtain ⟨g, hg⟩ := hEcyc.exists_ofOrder_eq_natCard
  have h1 : g ^ p = 1 := Subtype.ext (hEexp g g.2)
  have h2 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one h1
  rw [hg, hE] at h2
  have hp := (Fact.out : p.Prime)
  have := Nat.le_of_dvd hp.pos h2
  nlinarith [hp.two_le]

end CFSG.Quasithin.SBd19F
