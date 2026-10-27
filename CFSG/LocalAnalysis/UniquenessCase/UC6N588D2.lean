module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.N588

open Subgroup
open scoped commutatorElement
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)

theorem commutator_eq_top_of_simple {Q : Type*} [Group Q] (hS : IsSimpleGroup Q)
    (hnc : ¬ ∀ a b : Q, a * b = b * a) : commutator Q = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    apply hnc
    intro a b
    have : ⁅a, b⁆ ∈ commutator Q := by
      rw [commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  · exact h

theorem not_isSolvable_of_simple {Q : Type*} [Group Q] (hS : IsSimpleGroup Q)
    (hnc : ¬ ∀ a b : Q, a * b = b * a) : ¬ Group.IsSolvable Q := by
  intro hsol
  haveI := hS.toNontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne
    (commutator_eq_top_of_simple hS hnc)

variable {X : Type} [Group X] [Finite X]

theorem sup_eq_top_of_map_eq_top {P K : Subgroup X} [P.Normal]
    (h : K.map (QuotientGroup.mk' P) = ⊤) : K ⊔ P = ⊤ := by
  have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' P) K
  rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
  exact h1.symm

theorem le_of_map_eq_bot {P K : Subgroup X} [P.Normal]
    (h : K.map (QuotientGroup.mk' P) = ⊥) : K ≤ P := by
  intro x hx
  have : QuotientGroup.mk' P x ∈ K.map (QuotientGroup.mk' P) := mem_map_of_mem _ hx
  rw [h, mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 this

theorem le_of_normal_of_isSolvable {P : Subgroup X} [P.Normal] (hS : IsSimpleGroup (X ⧸ P))
    (hnc : ¬ ∀ a b : X ⧸ P, a * b = b * a) {N : Subgroup X} (hN : N.Normal)
    (hNs : Group.IsSolvable N) : N ≤ P := by
  haveI : (N.map (QuotientGroup.mk' P)).Normal := hN.map _ (QuotientGroup.mk'_surjective P)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' P)) with h | h
  · exact le_of_map_eq_bot h
  · exfalso
    apply not_isSolvable_of_simple hS hnc
    have hsurj : Function.Surjective ((QuotientGroup.mk' P).comp N.subtype) := by
      intro q
      have hq : q ∈ N.map (QuotientGroup.mk' P) := h ▸ mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj

theorem card_quot_dvd_of_sup_eq_top {N K : Subgroup X} [N.Normal] (h : N ⊔ K = ⊤) :
    Nat.card (X ⧸ N) ∣ Nat.card K := by
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp K.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ N ⊔ K := h ▸ mem_top x
    obtain ⟨n, hn, k, hk, rfl⟩ := mem_sup_of_normal_left.mp hx
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [MonoidHom.comp_apply, coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, ← mul_assoc]
    exact Normal.conj_mem' inferInstance n hn k
  exact Subgroup.card_dvd_of_surjective hsurj

theorem eq_top_of_coprime_quot {r : ℕ}
    (hgen : ∀ T : Subgroup X, (∀ ℓ : X, (∃ a : ℕ, orderOf ℓ = r ^ a) → ℓ ∈ T) → T = ⊤)
    {N : Subgroup X} [N.Normal] (hN : Nat.Coprime r (Nat.card (X ⧸ N))) : N = ⊤ := by
  apply hgen
  rintro ℓ ⟨a, ha⟩
  rw [← QuotientGroup.eq_one_iff]
  have h1 : orderOf (ℓ : X ⧸ N) ∣ r ^ a := by
    have := orderOf_map_dvd (QuotientGroup.mk' N) ℓ
    rw [ha] at this
    exact this
  have h2 : orderOf (ℓ : X ⧸ N) ∣ Nat.card (X ⧸ N) := orderOf_dvd_natCard _
  have h3 : Nat.Coprime (r ^ a) (Nat.card (X ⧸ N)) := Nat.Coprime.pow_left a hN
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)

theorem isSolvable_fittingSubgroupOf_top :
    Group.IsSolvable (CFSG.fittingSubgroupOf (⊤ : Subgroup X)) := by
  haveI : Group.IsSolvable (CFSG.fittingSubgroup ↥(⊤ : Subgroup X)) := inferInstance
  exact Group.isSolvable_of_surjective
    (f := ((CFSG.fittingSubgroup ↥(⊤ : Subgroup X)).equivMapOfInjective _
      (⊤ : Subgroup X).subtype_injective).toMonoidHom) (MulEquiv.surjective _)

theorem isSubnormal_of_isComponentOf_top {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    K.IsSubnormal := by
  have h := hK.2.1.map (f := (⊤ : Subgroup X).subtype) fun x => ⟨⟨x, mem_top x⟩, rfl⟩
  rwa [subgroupOf_map_subtype, inf_top_eq] at h

theorem quasisimple_or_centralizer_le {r : ℕ} {P : Subgroup X} [P.Normal]
    (hPs : Group.IsSolvable P) (hPr : Nat.Coprime r (Nat.card P)) (hS : IsSimpleGroup (X ⧸ P))
    (hnc : ¬ ∀ a b : X ⧸ P, a * b = b * a)
    (hgen : ∀ T : Subgroup X, (∀ ℓ : X, (∃ a : ℕ, orderOf ℓ = r ^ a) → ℓ ∈ T) → T = ⊤) :
    CFSG.solvableRadical X = P ∧ commutator X = ⊤ ∧
      (CFSG.Open.IsQuasisimple X ∨ centralizer (P : Set X) ≤ P) := by
  have hrad : CFSG.solvableRadical X = P :=
    le_antisymm (sSup_le fun N hN => le_of_normal_of_isSolvable hS hnc hN.1 hN.2)
      (le_sSup ⟨inferInstance, hPs⟩)
  have hperf : commutator X = ⊤ := by
    have hmap : (commutator X).map (QuotientGroup.mk' P) = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective P), ← commutator_def]
      exact commutator_eq_top_of_simple hS hnc
    exact eq_top_of_coprime_quot hgen (Nat.Coprime.coprime_dvd_right
      (card_quot_dvd_of_sup_eq_top (sup_eq_top_of_map_eq_top hmap)) hPr)
  refine ⟨hrad, hperf, ?_⟩
  by_cases hq : CFSG.Open.IsQuasisimple X
  · exact Or.inl hq
  right
  have hcomp : ∀ K : Subgroup X, IsComponentOf K ⊤ → False := by
    intro K hK
    obtain ⟨hKnt, hKperf, hKs⟩ := hK.2.2
    have hKP : ⁅K, P⁆ = ⊥ := CFSG.Walter.isComponentOf_commutator_eq_bot_of_isSolvable hK hPs
      le_top (le_top.trans (normalizer_eq_top (H := P)).ge)
    have hKsn := (isSubnormal_of_isComponentOf_top hK).map (QuotientGroup.mk'_surjective P)
    rcases hKsn.eq_bot_or_top_of_isSimpleGroup hS with h | h
    · have hKK : ⁅K, K⁆ = ⊥ :=
        eq_bot_iff.2 ((commutator_mono le_rfl (le_of_map_eq_bot h)).trans hKP.le)
      rw [commutator_self_eq_of_perfect hKperf] at hKK
      subst hKK
      obtain ⟨a, b, hab⟩ := hKnt.exists_pair_ne
      exact hab (Subsingleton.elim a b)
    · have hsup : K ⊔ P = ⊤ := sup_eq_top_of_map_eq_top h
      haveI hKn : K.Normal := ⟨fun n hn g => by
        have hg : g ∈ K ⊔ P := hsup ▸ mem_top g
        obtain ⟨k, hk, p, hp, rfl⟩ := mem_sup_of_normal_right.mp hg
        have hc : ⁅n, p⁆ = 1 := by
          have := commutator_mem_commutator hn hp
          rwa [hKP, mem_bot] at this
        rw [commutatorElement_eq_one_iff_mul_comm] at hc
        have hpn : p * n * p⁻¹ = n := by rw [← hc, mul_inv_cancel_right]
        rw [show k * p * n * (k * p)⁻¹ = k * (p * n * p⁻¹) * k⁻¹ by group, hpn]
        exact K.mul_mem (K.mul_mem hk hn) (K.inv_mem hk)⟩
      have hKtop : K = ⊤ := eq_top_of_coprime_quot hgen (Nat.Coprime.coprime_dvd_right
        (card_quot_dvd_of_sup_eq_top (sup_comm K P ▸ hsup)) hPr)
      apply hq
      let e : ↥K ≃* X := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
      exact ⟨hperf, (MulEquiv.isSimpleGroup_congr
        (QuotientGroup.congr (center ↥K) (center X) e (Subgroup.map_center_eq e))).mp hKs⟩
  have hE : componentLayerOf (⊤ : Subgroup X) = ⊥ :=
    sSup_eq_bot.2 fun K hK => (hcomp K hK).elim
  have hF : generalizedFittingSubgroupOf (⊤ : Subgroup X) ≤ P := by
    rw [generalizedFittingSubgroupOf, hE, sup_bot_eq]
    exact le_of_normal_of_isSolvable hS hnc (CFSG.fittingSubgroupOf_normal ⊤ inferInstance)
      isSolvable_fittingSubgroupOf_top
  exact (centralizer_le hF).trans
    (CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le.trans hF)

end CFSG.LocalAnalysis.UniquenessCase.UC6.N588
