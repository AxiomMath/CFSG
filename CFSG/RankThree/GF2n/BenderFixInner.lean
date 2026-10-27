module

public import CFSG.RankThree.GF2n.DihedralAut
public import CFSG.RankThree.GF2n.BenderStrongWC
public import CFSG.GH74.Uniqueness.Bender.SuzukiAut

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.GH74.Uniqueness.Bender DihedralGroup

variable {K : Type} [Group K] [Finite K]

theorem exists_conj_of_fix_linear {n : ℕ} (h : BenderType K n 1 1) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) (σ : MulAut K) (hfix : ∀ t ∈ T, σ t = t) :
    ∃ t ∈ T, ∀ k, σ k = t * k * t⁻¹ := by
  obtain ⟨Q, hQ⟩ := eq_rootCenter_of_strongWC h hT hT1
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  have hQZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
      (by rw [hc.card_eq, hc.card_center, pow_one])
  obtain ⟨r, hr, hσr⟩ := h.lemma_3_6_a Q σ (fun x hx => hfix x (by rw [hQ, hQZ]; exact hx))
  exact ⟨r, by rw [hQ]; exact hr, hσr⟩

theorem exists_conj_of_fix_suzuki {n e : ℕ} (h : BenderType K n 2 e) {T : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) (σ : MulAut K) (hσ2 : ∀ k, σ (σ k) = k)
    (hfix : ∀ t ∈ T, σ t = t) : ∃ t ∈ T, ∀ k, σ k = t * k * t⁻¹ := by
  obtain ⟨Q, hQ⟩ := eq_rootCenter_of_strongWC h hT hT1
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  have hfixZ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z := fun z hz =>
    hfix z (by rw [hQ]; exact hz)
  obtain ⟨s, hs, hσs⟩ := h.centralizingInner_suzuki Q σ
    (h.mem_of_centralizes_rootCenter Q σ hfixZ) hfixZ
  have hss : s * s = 1 := by
    have hcen : s * s ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 := hσ2 k
      rw [hσs, MulAut.conj_apply, MulAut.conj_apply] at h1
      calc k * (s * s) = (s * (s * k * s⁻¹) * s⁻¹) * (s * s) := by rw [h1]
        _ = s * s * k := by group
    rw [h.center_eq_bot, Subgroup.mem_bot] at hcen
    exact hcen
  refine ⟨s, ?_, fun k => by rw [hσs, MulAut.conj_apply]⟩
  rw [hQ]
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  · exact hc.center_of_involution s (le_borel _ hs) (orderOf_eq_prime (by rw [sq]; exact hss) hs1)

theorem exists_sr_of_orderOf_eq_two {m : ℕ} (hm : Odd m) {d : DihedralGroup m}
    (hd : orderOf d = 2) : ∃ k : ZMod m, d = sr k := by
  rcases d with i | i
  · exfalso
    have h1 : (r i) ^ m = 1 := by rw [r_pow, ZMod.natCast_self, mul_zero, r_zero]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hd] at h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  · exact ⟨i, rfl⟩

theorem exists_reflection_of_dihedral {m : ℕ} (hm : Odd m) (e : K ≃* DihedralGroup m)
    {T : Subgroup K} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ∃ t₀ ∈ T, t₀ * t₀ = 1 ∧ (∀ t ∈ T, t = 1 ∨ t = t₀) ∧ ∃ k : ZMod m, e t₀ = sr k := by
  have h2 := card_eq_two_of_dihedral hm e hT hT1
  obtain ⟨⟨t₀, ht₀⟩, ht₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀1' (Subtype.ext h)
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥T)).mp h2
  have huniq : ∀ t ∈ T, t = 1 ∨ t = t₀ := by
    intro t ht
    by_cases ht1 : t = 1
    · exact Or.inl ht1
    · right
      have e1 := hy ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
      have e2 := hy ⟨t₀, ht₀⟩ ht₀1'
      exact congrArg Subtype.val (e1.trans e2.symm)
  have hord : orderOf t₀ = 2 := by
    have hdvd : orderOf t₀ ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard T ht₀
      rwa [h2] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht₀1
    · exact h
  refine ⟨t₀, ht₀, ?_, huniq, ?_⟩
  · rw [← sq, ← hord]
    exact pow_orderOf_eq_one t₀
  · exact exists_sr_of_orderOf_eq_two hm (by rw [MulEquiv.orderOf_eq]; exact hord)

theorem exists_conj_of_fix_dihedral {m : ℕ} (hm : Odd m) (e : K ≃* DihedralGroup m)
    {T T' : Subgroup K} (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hT' : IsPGroup 2 T')
    (hT'1 : T' ≠ ⊥) (σ : MulAut K) (hσ2 : ∀ k, σ (σ k) = k) (hfix : ∀ t ∈ T, σ t = t)
    (hgen : T' ⊔ T'.map σ.toMonoidHom = ⊤) : ∃ t ∈ T, ∀ k, σ k = t * k * t⁻¹ := by
  obtain ⟨t₀, ht₀, ht₀2, -, k₀, hk₀⟩ := exists_reflection_of_dihedral hm e hT hT1
  obtain ⟨t₁, ht₁, -, hT'u, j₀, hj₀⟩ := exists_reflection_of_dihedral hm e hT' hT'1
  set σ' : MulAut (DihedralGroup m) := (e.symm.trans σ).trans e with hσ'
  have hσ'a : ∀ d, σ' d = e (σ (e.symm d)) := fun d => rfl
  have hσ'2 : ∀ d, σ' (σ' d) = d := fun d => by
    rw [hσ'a, hσ'a, MulEquiv.symm_apply_apply, hσ2, MulEquiv.apply_symm_apply]
  have hfix' : σ' (sr k₀) = sr k₀ := by
    rw [hσ'a, ← hk₀, MulEquiv.symm_apply_apply, hfix t₀ ht₀]
  have hgen' : ∀ d : DihedralGroup m,
      d ∈ Subgroup.closure ({sr j₀, σ' (sr j₀)} : Set (DihedralGroup m)) := by
    have hle : T' ⊔ T'.map σ.toMonoidHom ≤
        (Subgroup.closure ({sr j₀, σ' (sr j₀)} : Set (DihedralGroup m))).comap
          e.toMonoidHom := by
      refine sup_le (fun t ht => ?_) ?_
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
        rcases hT'u t ht with h | h
        · rw [h, map_one]
          exact Subgroup.one_mem _
        · rw [h, hj₀]
          exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rintro _ ⟨t, ht, rfl⟩
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom]
        rcases hT'u t ht with h | h
        · rw [h, map_one, map_one]
          exact Subgroup.one_mem _
        · rw [h, show e (σ t₁) = σ' (sr j₀) by rw [hσ'a, ← hj₀, MulEquiv.symm_apply_apply]]
          exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    intro d
    have := hle (show e.symm d ∈ T' ⊔ T'.map σ.toMonoidHom by rw [hgen]; trivial)
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at this
  have hconj := dihedral_eq_conj hm σ' hσ'2 hfix' hgen'
  refine ⟨t₀, ht₀, fun k => ?_⟩
  have h1 := hconj (e k)
  rw [hσ'a, MulEquiv.symm_apply_apply, ← hk₀, ← map_mul, ← map_mul] at h1
  rw [e.injective h1, inv_eq_of_mul_eq_one_right ht₀2]

end CFSG.RankThree.GF2n
