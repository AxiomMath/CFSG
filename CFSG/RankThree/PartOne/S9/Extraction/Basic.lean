module

public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG

variable {H : Type*} [Group H]

theorem le_normalizer_inf {A K₁ K₂ : Subgroup H} (h₁ : A ≤ normalizer (K₁ : Set H))
    (h₂ : A ≤ normalizer (K₂ : Set H)) :
    A ≤ normalizer ((K₁ ⊓ K₂ : Subgroup H) : Set H) := by
  rw [le_normalizer_iff] at h₁ h₂ ⊢
  intro a ha k hk
  exact ⟨h₁ a ha k hk.1, h₂ a ha k hk.2⟩

theorem le_normalizer_sup {A K₁ K₂ : Subgroup H} (h₁ : A ≤ normalizer (K₁ : Set H))
    (h₂ : A ≤ normalizer (K₂ : Set H)) :
    A ≤ normalizer ((K₁ ⊔ K₂ : Subgroup H) : Set H) := by
  intro a ha
  have e₁ := mem_normalizer_iff_map_conj_eq.mp (h₁ ha)
  have e₂ := mem_normalizer_iff_map_conj_eq.mp (h₂ ha)
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]

theorem exists_minimal_commGen [Finite H] (A J W : Subgroup H)
    (hAW : A ≤ normalizer (W : Set H)) (hW : ⁅W, A⁆ = W) (hWJ : ¬ W ≤ J) :
    ∃ R : Subgroup H, R ≤ W ∧ A ≤ normalizer (R : Set H) ∧ ⁅R, A⁆ = R ∧ ¬ R ≤ J ∧
      ∀ U : Subgroup H, U < R → A ≤ normalizer (U : Set H) → ⁅U, A⁆ = U → U ≤ J := by
  classical
  let S : Set (Subgroup H) :=
    {Y | Y ≤ W ∧ A ≤ normalizer (Y : Set H) ∧ ⁅Y, A⁆ = Y ∧ ¬ Y ≤ J}
  obtain ⟨R, hRS, hRmin⟩ := (wellFounded_lt (α := Subgroup H)).has_min S ⟨W, le_rfl, hAW, hW, hWJ⟩
  refine ⟨R, hRS.1, hRS.2.1, hRS.2.2.1, hRS.2.2.2, fun U hUR hAU hUc => ?_⟩
  by_contra hUJ
  exact hRmin U ⟨hUR.le.trans hRS.1, hAU, hUc, hUJ⟩ hUR

theorem map_pCore_subtype_le {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (r : ℕ) :
    (pCore r N).map N.subtype ≤ pCore r G := by
  have hn : ((pCore r N).map N.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  exact le_sSup ⟨hn, (pCore_isPGroup).map N.subtype⟩

theorem inSubgroup_pCore_eq_inf {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (r : ℕ) :
    inSubgroup (pCore r) N = N ⊓ pCore r G := by
  refine le_antisymm (le_inf (map_subtype_le _) (map_pCore_subtype_le N r)) ?_
  set K : Subgroup G := N ⊓ pCore r G with hK
  have hKn : K.Normal := inferInstance
  have hKp : IsPGroup r K := pCore_isPGroup.to_le inf_le_right
  have hKN : K ≤ N := inf_le_left
  have hsubn : (K.subgroupOf N).Normal := hKn.subgroupOf N
  have hsubp : IsPGroup r (K.subgroupOf N) := hKp.of_equiv (subgroupOfEquivOfLe hKN).symm
  have hle : K.subgroupOf N ≤ pCore r N := le_sSup ⟨hsubn, hsubp⟩
  calc K = (K.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hKN).symm
    _ ≤ (pCore r N).map N.subtype := map_mono hle

theorem eq_of_isSylowOf_of_isPGroup [Finite H] {p : ℕ} (hp : p.Prime) {T S M : Subgroup H}
    (hT : IsSylowOf p T S) (hTM : T ≤ M) (hMS : M ≤ S) (hM : IsPGroup p M) : M = T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hidx⟩ := hT
  have hdvd : T.relIndex M ∣ T.relIndex S := by
    rw [← relIndex_mul_relIndex T M S hTM hMS]
    exact dvd_mul_right _ _
  have hcard : T.relIndex M * Nat.card (T ⊓ M : Subgroup H) = Nat.card M :=
    relIndex_mul_card T M
  rw [inf_eq_left.mpr hTM] at hcard
  obtain ⟨m, hm⟩ := hM.exists_card_eq
  have hdm : T.relIndex M ∣ p ^ m := by
    rw [← hm, ← hcard]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdm
  have hj0 : j = 0 := by
    by_contra hne
    apply hidx
    rw [hj] at hdvd
    exact (dvd_pow_self p hne).trans hdvd
  rw [hj0, pow_zero] at hj
  exact le_antisymm (relIndex_eq_one.mp hj) hTM

theorem card_comap_mk' (J : Subgroup H) [J.Normal] (O : Subgroup (H ⧸ J)) :
    Nat.card (O.comap (QuotientGroup.mk' J)) = Nat.card J * Nat.card O := by
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hJF : J ≤ O.comap π := fun x hx => by
    have h1 : (x : H ⧸ J) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    show (x : H ⧸ J) ∈ O
    rw [h1]
    exact one_mem _
  have h := card_ker_mul_card_range (π.comp (O.comap π).subtype)
  have hker : (π.comp (O.comap π).subtype).ker = J.subgroupOf (O.comap π) := by
    ext x
    simp [hπ, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hrange : (π.comp (O.comap π).subtype).range = O := by
    rw [MonoidHom.range_comp, range_subtype, map_comap_eq_self_of_surjective hπs]
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe hJF).toEquiv] at h
  exact h.symm

theorem pCore_two_quotient_eq_bot [Finite H] : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
  set J := pCore 2 H with hJ
  set O := pCore 2 (H ⧸ J) with hO
  set π := QuotientGroup.mk' J with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective J
  have hK : IsPGroup 2 (O.comap π) := by
    obtain ⟨a, ha⟩ := (pCore_isPGroup : IsPGroup 2 J).exists_card_eq
    obtain ⟨c, hc⟩ := (pCore_isPGroup : IsPGroup 2 O).exists_card_eq
    exact IsPGroup.of_card (n := a + c) (by rw [card_comap_mk', ha, hc, pow_add])
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKJ : O.comap π ≤ J := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ J.map π := map_mono hKJ
    _ = ⊥ := QuotientGroup.map_mk'_self J

end CFSG.RankThree.PartOne.Extract
