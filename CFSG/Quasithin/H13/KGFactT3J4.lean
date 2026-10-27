module

public import CFSG.Quasithin.H13.KGFactT3J4Core
public import CFSG.Quasithin.H13.NQCatT3J4
public import CFSG.Quasithin.H13.NQCatT3Perm
public import CFSG.Sporadic.Schreier.J4SThree

public section

namespace CFSG.Quasithin.H13.KGT3J4

open CFSG.Sporadic.J4 CFSG.Quasithin.J4Loc CFSG.Blueprint
open CFSG.Quasithin.H13.NQCat.T513 CFSG.Quasithin.H13.NQCat.T3
open CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Sporadic.J4Schreier CFSG.LocalAnalysis.ComponentInitial in
theorem not_three_dvd_card_outer_J :
    ¬ 3 ∣ Nat.card (Outer J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCp : ¬ 3 ∣ Nat.card (pointwiseFixingAut H) := by
    intro h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group.2
    rw [hk] at h
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  exact not_dvd_card_outer_of_sylow_bound (by norm_num : 3 ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2

theorem oddInner_J :
    ∀ α : MulAut J, Odd (orderOf α) → ∃ g : J, α = MulAut.conj g := by
  intro α hα
  have hF := j4Facts
  have : Finite (MulAut J) := Finite.of_injective _ DFunLike.coe_injective
  set a : Outer J := QuotientGroup.mk α with ha
  have h1 : orderOf a ∣ orderOf α := orderOf_map_dvd (QuotientGroup.mk' (inner J)) α
  have h2 : orderOf a ∣ Nat.card (Outer J) := orderOf_dvd_natCard a
  have hodd : Odd (orderOf a) := Odd.of_dvd_nat hα h1
  have h3 : orderOf a = 1 := by
    by_contra hne
    have hp : (orderOf a).minFac.Prime := Nat.minFac_prime hne
    have hpd : (orderOf a).minFac ∣ Nat.card (Outer J) := (Nat.minFac_dvd _).trans h2
    have hpa : (orderOf a).minFac ∣ orderOf a := Nat.minFac_dvd _
    have hp2 : (orderOf a).minFac ≠ 2 := by
      intro h
      rw [h] at hpa
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpa)
    have hp3 : (orderOf a).minFac ≠ 3 := by
      intro h
      rw [h] at hpd
      exact not_three_dvd_card_outer_J hpd
    have hp5 : 5 ≤ (orderOf a).minFac := by
      have := hp.two_le
      by_contra hlt
      interval_cases h : (orderOf a).minFac
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    exact CFSG.Sporadic.J4Schreier.not_dvd_card_outer_J hp hp5 hpd
  rw [orderOf_eq_one_iff, ha, QuotientGroup.eq_one_iff] at h3
  obtain ⟨g, hg⟩ := h3
  exact ⟨g, hg.symm⟩

theorem center_J_eq_bot : Subgroup.center J = ⊥ := by
  have hF := j4Facts
  have : IsSimpleGroup J := isSimpleGroup_J hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := J) 2
      (by rw [card_J hF]; norm_num)
    have hN : (Subgroup.zpowers x).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hc : g ∈ Subgroup.center J := h ▸ Subgroup.mem_top g
      rw [Subgroup.mem_center_iff] at hc
      rw [← hc n, mul_inv_cancel_right]
      exact hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
    · rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hx
      norm_num at hx
    · have h2 := congrArg (fun K : Subgroup J => Nat.card K) h1
      simp only [Nat.card_zpowers, hx, Subgroup.card_top, card_J hF] at h2
      norm_num at h2

theorem le_normalizer_of_transport {Γ P : Type} [Group Γ] [Group P] (ψ : P ≃* Γ)
    {P₀ : Subgroup Γ} {T R E : Subgroup P} (hT : T.map ψ.toMonoidHom = P₀)
    (hcore : ∀ R' E' : Subgroup Γ, ⁅R', R'⁆ = R' → Nat.card R' = Nat.card R →
      P₀ ≤ Subgroup.normalizer (R' : Set Γ) → IsPGroup 3 ↥E' → Nat.card E' = Nat.card E →
      Nat.card ↥(E' ⊔ P₀) = Nat.card ↥(E ⊔ T) → ∀ b' ∈ R', b' ∈ E' → orderOf b' = 3 →
      E' ≤ Subgroup.normalizer (R' : Set Γ))
    (hRp : ⁅R, R⁆ = R) (hTR : T ≤ Subgroup.normalizer (R : Set P)) (hE3 : IsPGroup 3 ↥E)
    {b : P} (hbR : b ∈ R) (hbE : b ∈ E) (hb3 : orderOf b = 3) :
    E ≤ Subgroup.normalizer (R : Set P) := by
  have h := hcore (R.map ψ.toMonoidHom) (E.map ψ.toMonoidHom)
    (by rw [← Subgroup.map_commutator, hRp])
    (Subgroup.card_map_of_injective ψ.injective)
    (by rw [← hT, ← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hTR)
    (hE3.map _)
    (Subgroup.card_map_of_injective ψ.injective)
    (by rw [← hT, ← Subgroup.map_sup, Subgroup.card_map_of_injective ψ.injective])
    (ψ b) ⟨b, hbR, rfl⟩ ⟨b, hbE, rfl⟩ (by rw [MulEquiv.orderOf_eq]; exact hb3)
  rw [← Subgroup.map_equiv_normalizer_eq] at h
  exact (Subgroup.map_le_map_iff_of_injective ψ.injective).mp h

theorem normalizer_of_model {Γ : Type} [Group Γ] [Finite Γ] {P₀ : Subgroup Γ}
    (hP0 : CFSG.QuasithinUnique.IsSylowTwoOf P₀ ⊤) (hP0c : Nat.card P₀ = 2 ^ 21)
    (hcenΓ : Subgroup.center Γ = ⊥)
    (hinnΓ : ∀ α : MulAut Γ, Odd (orderOf α) → ∃ g : Γ, α = MulAut.conj g)
    (hcoreΓ : ∀ R' E' : Subgroup Γ, ⁅R', R'⁆ = R' → ∀ a : ℕ, Nat.card R' = 2 ^ a * 15 →
      P₀ ≤ Subgroup.normalizer (R' : Set Γ) → IsPGroup 3 ↥E' → 9 ≤ Nat.card E' →
      Nat.card ↥(E' ⊔ P₀) = Nat.card E' * 2 ^ 21 → ∀ b' ∈ R', b' ∈ E' → orderOf b' = 3 →
      E' ≤ Subgroup.normalizer (R' : Set Γ))
    {A : Type} [Group A] [Finite A] {Q R S B D : Subgroup A} (h : Star513 Q R S B D)
    (eQ : ↥Q ≃* Γ) (hD3 : ∀ d ∈ D, ∃ k : ℕ, d ^ (3 ^ k) ∈ Subgroup.centralizer (Q : Set A)) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  by_contra hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Subgroup.center ↥Q = ⊥ := by
    have h1 := (Subgroup.map_center_eq (G := ↥Q) (H := Γ) eQ).trans hcenΓ
    exact (Subgroup.map_eq_bot_iff_of_injective _ eQ.injective).mp h1
  let ψQ : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : Finite (↥Q ⧸ Subgroup.center ↥Q) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcen : Subgroup.center (↥Q ⧸ Subgroup.center ↥Q) = ⊥ := by
    have h1 := (Subgroup.map_center_eq (G := ↥Q ⧸ Subgroup.center ↥Q) (H := ↥Q) ψQ).trans hZ
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψQ.injective).mp h1
  have hinn : ∀ α : MulAut (↥Q ⧸ Subgroup.center ↥Q), Odd (orderOf α) →
      ∃ x, α = MulAut.conj x :=
    oddInner_of_mulEquiv (ψQ.trans eQ) hinnΓ
  let e : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥Q ⧸ Subgroup.center ↥Q := MulEquiv.refl _
  obtain ⟨b, hb, hb3⟩ := exists_b_three e h
  obtain ⟨hE3, hE9⟩ := exists_three_group e hcen hinn h hD3 hnot hb hb3
  have hcard := card_sup_three e hcen hinn h hD3 hb hb3
  have hbQ : b ∈ Q := h.R_le (h.hall_B.1 hb).1
  set E := iPart Q e D ⊔ Subgroup.zpowers (toP Q e ⟨b, hbQ⟩) with hEdef
  set T := pImg Q e (S ⊓ Q) with hTdef
  set Rb := pImg Q e R with hRbdef
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  have hTs : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ :=
    CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨hT2, hTi⟩
  obtain ⟨ψ, hψ⟩ := sylow_transport hP0 (ψQ.trans eQ) hTs
  have hTc : Nat.card T = 2 ^ 21 := by
    rw [← hP0c, ← hψ, Subgroup.card_map_of_injective ψ.injective]
  have hinj : Function.Injective (toP Q e) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_toP, hZ]
  have hRQp : ⁅R.subgroupOf Q, R.subgroupOf Q⁆ = R.subgroupOf Q := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.R_le, h.R_perfect]
  have hRp : ⁅Rb, Rb⁆ = Rb := by
    rw [hRbdef, pImg, ← Subgroup.map_commutator, hRQp]
  obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (G := ↥R) (p := 2)).exists_card_eq
  obtain ⟨eL⟩ := exists_l24_of_lieModel h.R_type
  have hR60 : Nat.card R = 2 ^ (c + 2) * 15 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥R)
    have h2 : Nat.card (CFSG.Quasithin.ModO2 R) = 60 := CFSG.Walter.JT.card_of_psl24 eL
    rw [show Nat.card (↥R ⧸ CFSG.pCore 2 ↥R) = 60 from h2, hc] at h1
    rw [h1, pow_add]
    ring
  have hRbc : Nat.card Rb = 2 ^ (c + 2) * 15 := by
    rw [hRbdef, pImg, Subgroup.card_map_of_injective hinj, ← hR60]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R_le).toEquiv
  have hTR : T ≤ Subgroup.normalizer (Rb : Set (↥Q ⧸ Subgroup.center ↥Q)) := by
    intro t ht
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨s, hsQ, hs, rfl⟩ := (mem_pImg Q e).1 ht
    obtain ⟨r, hrQ, hr, rfl⟩ := (mem_pImg Q e).1 hy
    have hsr : s * r * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (h.S_le_R hs.1) r).mp hr
    have e1 : toP Q e ⟨s, hsQ⟩ * toP Q e ⟨r, hrQ⟩ * (toP Q e ⟨s, hsQ⟩)⁻¹ =
        toP Q e ⟨s * r * s⁻¹, h.R_le hsr⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact toP_mem_pImg Q e _ hsr
  have hEN : E ≤ Subgroup.normalizer (Rb : Set (↥Q ⧸ Subgroup.center ↥Q)) := by
    refine le_normalizer_of_transport ψ hψ ?_ hRp hTR hE3
      (toP_mem_pImg Q e hbQ (h.hall_B.1 hb).1)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hb3
    intro R' E' hR'p hR'c hPR' hE'3 hE'c hE'P b' hb'R hb'E hb'3
    refine hcoreΓ R' E' hR'p (c + 2) (hR'c.trans hRbc) hPR' hE'3 (hE'c ▸ hE9) ?_ b' hb'R hb'E
      hb'3
    rw [hE'P, hcard, hTc, hE'c]
  exact hnot (le_normalizer_of_iPart e hinn h (le_sup_left.trans hEN))

theorem factType513ThreeJ4_holds [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    FactType513ThreeJ4 := by
  intro A _ _ Q R S B D h hQ hD3
  have hF := j4Facts
  obtain ⟨e₀⟩ := hQ
  obtain ⟨eJ⟩ : Nonempty (↥Q ≃* J) := ⟨e₀.trans (seedEquiv hF.mat)⟩
  exact normalizer_of_model isSylowTwoOf_P0 (CFSG.Sporadic.J4.QT.card_P0 hF.mat hF)
    center_J_eq_bot oddInner_J
    (fun R' E' hR'p _ hR'c hPR' hE'3 hE'9 hE'P b' hb'R hb'E hb'3 =>
      core hR'p hR'c hPR' hE'3 hE'9 hE'P hb'R hb'E hb'3) h eJ hD3

end CFSG.Quasithin.H13.KGT3J4
