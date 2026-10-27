module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenBasis
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenLevi

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

include h in
theorem exists_isPGroup_le_centralizer_even (hn : 3 ≤ n) (s : unitarySU 2 f K (2 * n))
    (hss : s * s = 1) :
    ∃ R : Subgroup (unitarySU 2 f K (2 * n)), IsPGroup 2 R ∧ R ≤ centralizer {s} ∧
      2 ^ (f * (n ^ 2 + 2)) ≤ Nat.card R := by
  have : CharP K 2 := h.charP
  set S := ((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) with hS
  set W : Submodule K (Fin (2 * n) → K) := LinearMap.range (S.mulVecLin - LinearMap.id) with hW
  have hmemW : ∀ v, S *ᵥ v - v ∈ W := fun v => ⟨v, rfl⟩
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, stdHermForm h (2 * n) x y = 0 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact stdHermForm_sub_sub_eq_zero_of_mul_self h hss a b
  obtain ⟨hk, w, hw, hWw⟩ := exists_wittBasis_eq_aSpan h (r := n) (ε := 0) zero_le_one
    (by ring) W hWiso
  rcases Nat.lt_or_ge (Module.finrank K W) n with hlt | hge
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨w', hw', hle⟩ := exists_rebase h (by rw [Module.finrank_fin_fun]; ring) hw
    have hWM : W ≤ aSpanTop K ⇑w' := hWw.le.trans ((aSpan_mono _ (by omega)).trans hle)
    refine ⟨pairRadical 2 f (aSpanTop K ⇑w') (aSpanTop K ⇑w' ⊔ zSpan K ⇑w'),
      isPGroup_pairRadical 2 f _ _, fun g hg => ?_, ?_⟩
    · refine mem_centralizer_of_mem_pairRadical (fun x => hWM (hmemW x)) (fun x hx => ?_) hg
      exact mulVec_eq_self_of_forall_stdHermForm_eq_zero h hss fun u =>
        form_eq_zero_of_mem_aSpanTop h hw' (hWM (hmemW u)) hx
    · refine le_trans (Nat.pow_le_pow_right two_pos ?_) (card_pairRadical_ge h w' hw')
      exact Nat.mul_le_mul_left _ (by nlinarith)
  · have hkn : Module.finrank K W = n := le_antisymm hk hge
    rw [hkn, aSpan_self_eq] at hWw
    obtain ⟨v, hv, hs1, hs2⟩ := exists_adapted_wittBasis h s hss hw hWw
    exact exists_isPGroup_le_centralizer_of_adapted h hv hn hs1 hs2

theorem le_factorization_card_centralizer_of_isPGroup {N e : ℕ} (hN : 1 ≤ N)
    (hR : ∀ s : unitarySU 2 f K N, s * s = 1 → ∃ R : Subgroup (unitarySU 2 f K N),
      IsPGroup 2 R ∧ R ≤ centralizer {s} ∧ 2 ^ e ≤ Nat.card R)
    (y : unitaryPSU h N) (hy : orderOf y = 2) :
    e ≤ (Nat.card (centralizer ({y} : Set (unitaryPSU h N)))).factorization 2 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hss, rfl⟩ := exists_mk_eq_mul_self_eq_one h hN y (by
    have := pow_orderOf_eq_one y
    rwa [hy] at this)
  obtain ⟨R, hR2, hRC, hRcard⟩ := hR s hss
  set π : unitarySU 2 f K N →* unitaryPSU h N := QuotientGroup.mk' (unitaryScalars h N) with hπ
  have hodd := odd_card_unitaryScalars h hN
  have hinj : Function.Injective (π.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgZ : (g : unitarySU 2 f K N) ∈ unitaryScalars h N := (QuotientGroup.eq_one_iff _).mp hg
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) g
    have hdvd : orderOf g ∣ Nat.card (unitaryScalars h N) := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hgZ]
      exact orderOf_dvd_natCard _
    rcases k with _ | k
    · rwa [pow_zero, orderOf_eq_one_iff] at hk
    · rw [hk] at hdvd
      have h1 := Nat.odd_iff.mp hodd
      have h2 := Nat.mod_eq_zero_of_dvd (dvd_trans (dvd_pow_self 2 k.succ_ne_zero) hdvd)
      omega
  set Q := (π.comp R.subtype).range with hQ
  have hQ2 : IsPGroup 2 Q := hR2.of_surjective _ (π.comp R.subtype).rangeRestrict_surjective
  have hQC : Q ≤ centralizer ({(QuotientGroup.mk s : unitaryPSU h N)} :
      Set (unitaryPSU h N)) := by
    rintro _ ⟨g, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp (hRC g.2)
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hπ,
      QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  have hQcard : 2 ^ e ≤ Nat.card Q := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hRcard
  obtain ⟨a, ha⟩ := hQ2.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card (centralizer ({(QuotientGroup.mk s : unitaryPSU h N)} :
      Set (unitaryPSU h N))) := ha ▸ Subgroup.card_dvd_of_le hQC
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  rw [ha] at hQcard
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hQcard
  omega

theorem le_factorization_card_centralizer_even (hn : 3 ≤ n) (y : unitaryPSU h (2 * n))
    (hy : orderOf y = 2) :
    f * (n ^ 2 + 2) ≤
      (Nat.card (centralizer ({y} : Set (unitaryPSU h (2 * n))))).factorization 2 :=
  le_factorization_card_centralizer_of_isPGroup h (by omega)
    (fun s hss => exists_isPGroup_le_centralizer_even h hn s hss) y hy

end CFSG.SeitzReduction.UnitaryPilot
