module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.Quasithin

theorem isPGroup_two_of_forall_odd_sylow_eq_bot {K : Type*} [Group K] [Finite K]
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (C : Sylow r K), (C : Subgroup K) = ⊥) :
    IsPGroup 2 K := by
  rw [IsPGroup.iff_card]
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card K → d = 2 := by
    intro d hd hdvd
    by_contra hd2
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨C⟩ := (inferInstance : Nonempty (Sylow d K))
    exact Sylow.ne_bot_of_dvd_card C hdvd (h d hd hd2 C)
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime⟩

theorem isPGroup_two_ker_of_cyclic_odd_sylow {X G : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] [Group G] (φ : X →* G) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center X)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r G),
      IsCyclic (Q : Subgroup G)) : IsPGroup 2 φ.ker := by
  have : Finite G := Finite.of_surjective φ hφ
  refine isPGroup_two_of_forall_odd_sylow_eq_bot fun r hr hr2 _ C => ?_
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r G))
  exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot φ hφ hZ C Q
    (hcyc r hr hr2 Q)

theorem ker_mk_comp_mulEquiv {X J : Type*} [Group X] [Group J] (Z : Subgroup X) [Z.Normal]
    (e : X ⧸ Z ≃* J) : (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isPGroup_two_of_mulEquiv_cyclic_odd_sylow {X J : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] [Group J] (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X)
    (e : X ⧸ Z ≃* J)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r J),
      IsCyclic (Q : Subgroup J)) : IsPGroup 2 Z := by
  have hker := ker_mk_comp_mulEquiv Z e
  have h := isPGroup_two_ker_of_cyclic_odd_sylow (e.toMonoidHom.comp (QuotientGroup.mk' Z))
    (e.surjective.comp (QuotientGroup.mk'_surjective Z)) (hker.le.trans hZ) hcyc
  rwa [hker] at h

end CFSG.Quasithin
