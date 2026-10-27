module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCConjugate

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.GorensteinLyons (mem_conjugate_iff_conj_mem mem_normalizer_iff_conjugate_eq)

variable {X : Type*} [Group X]

theorem normalClosure_le_iSup_conjugate {Q P : Subgroup X} [Q.Normal] (hQP : Q ⊔ P = ⊤) :
    normalClosure (P : Set X) ≤ ⨆ q ∈ Q, CFSG.conjugate P q := by
  rw [normalClosure, closure_le]
  intro x hx
  obtain ⟨p, hp, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  have hc : c⁻¹ ∈ (↑(P ⊔ Q) : Set X) := by
    rw [sup_comm, hQP]
    exact mem_top _
  rw [mul_normal P Q] at hc
  obtain ⟨p', hp', q', hq', hpq⟩ := hc
  have hpq : p' * q' = c⁻¹ := hpq
  refine (le_iSup₂ (f := fun q (_ : q ∈ Q) => CFSG.conjugate P q) q' hq') ?_
  rw [mem_conjugate_iff_conj_mem]
  have hc' : c = q'⁻¹ * p'⁻¹ := by rw [← mul_inv_rev, hpq, inv_inv]
  rw [hc', show q' * (q'⁻¹ * p'⁻¹ * p * (q'⁻¹ * p'⁻¹)⁻¹) * q'⁻¹ = p'⁻¹ * p * p' by group]
  exact mul_mem (mul_mem (inv_mem hp') hp) hp'

theorem residual_coprime_complement_normal_generation {r : ℕ} (hr : r.Prime) [Finite X]
    {Q P : Subgroup X} [Q.Normal] (hQ : IsPGroup r Q) (hP : Nat.Coprime (Nat.card P) r)
    (hQP : Q ⊔ P = ⊤) (hres : ∀ (N : Subgroup X) [N.Normal], IsPGroup r (X ⧸ N) → N = ⊤) :
    (⨆ q ∈ Q, CFSG.conjugate P q) = ⊤ ∧ ⁅Q, P⁆ = Q ∧
    ∀ (B : Type*) [Group B] [Finite B] (ι : X →* B) [ι.range.Normal], Function.Injective ι →
      IsPGroup r (B ⧸ ι.range) →
      ι.range = closure {b : B | Nat.Coprime (orderOf b) r} ∧ ι.range.Characteristic := by
  have : Fact r.Prime := ⟨hr⟩
  have hN : normalClosure (P : Set X) = ⊤ := by
    apply hres
    refine hQ.of_surjective ((QuotientGroup.mk' (normalClosure (P : Set X))).comp Q.subtype) ?_
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have htop : Q ⊔ normalClosure (P : Set X) = ⊤ := by
      rw [← top_le_iff, ← hQP]
      exact sup_le_sup_left le_normalClosure Q
    have hx : x ∈ (↑(Q ⊔ normalClosure (P : Set X)) : Set X) := by
      rw [htop]
      exact mem_top x
    rw [mul_normal] at hx
    obtain ⟨q, hq, n, hn, rfl⟩ := hx
    refine ⟨⟨q, hq⟩, ?_⟩
    show ((q : X) : X ⧸ normalClosure (P : Set X)) = ((q * n : X) : X ⧸ normalClosure (P : Set X))
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hM : (⨆ q ∈ Q, CFSG.conjugate P q) = ⊤ := by
    rw [← top_le_iff, ← hN]
    exact normalClosure_le_iSup_conjugate hQP
  refine ⟨hM, ?_, ?_⟩
  ·
    have hPN : P ≤ normalizer ((⁅Q, P⁆ : Subgroup X) : Set X) := by
      intro p hp
      have hQn : CFSG.conjugate Q p = Q := mem_normalizer_iff_conjugate_eq.mp (by
        rw [normalizer_eq_top]
        exact mem_top p)
      have hPn : CFSG.conjugate P p = P := mem_normalizer_iff_conjugate_eq.mp (le_normalizer hp)
      rw [mem_normalizer_iff_conjugate_eq]
      unfold CFSG.conjugate at hQn hPn ⊢
      rw [map_commutator, hQn, hPn]
    have hconj : ∀ q ∈ Q, CFSG.conjugate P q ≤ P ⊔ ⁅Q, P⁆ := by
      intro q hq y hy
      rw [mem_conjugate_iff_conj_mem] at hy
      have e : y = (q * y * q⁻¹) * ⁅(q * y * q⁻¹)⁻¹, q⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      rw [e]
      refine mul_mem_sup hy ?_
      rw [commutator_comm]
      exact commutator_mem_commutator (inv_mem hy) (inv_mem hq)
    have htop : P ⊔ ⁅Q, P⁆ = ⊤ := by
      rw [← top_le_iff, ← hM]
      exact iSup₂_le hconj
    have hbot : Q ⊓ P = ⊥ := by
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      exact disjoint_iff.mp
        (disjoint_of_coprime_natCard (hk ▸ Nat.Coprime.pow_left k (Nat.Coprime.symm hP)))
    refine le_antisymm (commutator_le_left Q P) fun q hq => ?_
    have hq' : q ∈ (↑(P ⊔ ⁅Q, P⁆) : Set X) := by
      rw [htop]
      exact mem_top q
    rw [coe_mul_of_left_le_normalizer_right P _ hPN] at hq'
    obtain ⟨p, hp, d, hd, hpd⟩ := hq'
    have hpd : p * d = q := hpd
    have hpQ : p ∈ Q := by
      rw [show p = q * d⁻¹ by rw [← hpd]; group]
      exact mul_mem hq (inv_mem (commutator_le_left Q P hd))
    have hp1 : p = 1 := mem_bot.mp (hbot ▸ mem_inf.mpr ⟨hpQ, hp⟩)
    rw [← hpd, hp1, one_mul]
    exact hd
  · intro B _ _ ι _ hι hBX
    obtain ⟨Y, hY⟩ : ∃ Y : Subgroup B, closure {b : B | Nat.Coprime (orderOf b) r} = Y :=
      ⟨_, rfl⟩
    rw [hY]
    have hYchar : Y.Characteristic := by
      refine characteristic_iff_map_le.mpr fun φ => ?_
      rw [← hY, MonoidHom.map_closure]
      apply closure_mono
      rintro _ ⟨b, hb, rfl⟩
      show Nat.Coprime (orderOf (φ b)) r
      rw [MulEquiv.orderOf_eq]
      exact hb
    have hYX : Y ≤ ι.range := by
      rw [← hY, closure_le]
      intro b hb
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hBX) (b : B ⧸ ι.range)
      have hdvd : orderOf (b : B ⧸ ι.range) ∣ orderOf b :=
        orderOf_map_dvd (QuotientGroup.mk' ι.range) b
      rw [hk] at hdvd
      have hk0 : k = 0 := by
        by_contra hk0
        exact hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hb)
          ((dvd_pow_self r hk0).trans hdvd))
      rw [hk0, pow_zero, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at hk
      exact hk
    have hXY : ι.range ≤ Y := by
      have hYn : (Y.comap ι).Normal := Subgroup.Normal.comap inferInstance ι
      have hPY : P ≤ Y.comap ι := by
        intro p hp
        rw [mem_comap, ← hY]
        apply subset_closure
        show Nat.Coprime (orderOf (ι p)) r
        rw [orderOf_injective ι hι p]
        exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard P hp) hP
      have hle : (⨆ q ∈ Q, CFSG.conjugate P q) ≤ Y.comap ι := by
        refine iSup₂_le fun q _ y hy => ?_
        rw [mem_conjugate_iff_conj_mem] at hy
        have h := hYn.conj_mem _ (hPY hy) q⁻¹
        rwa [show q⁻¹ * (q * y * q⁻¹) * q⁻¹⁻¹ = y by group] at h
      rw [hM, top_le_iff] at hle
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ Y.comap ι := hle ▸ mem_top x
      exact hx
    have heq : ι.range = Y := le_antisymm hXY hYX
    exact ⟨heq, heq ▸ hYchar⟩

end CFSG.Quasithin.SteinbergCC
