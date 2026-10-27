module

public import CFSG.RankThree.PartOne.S11c.Sec66K1Plane
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.S11c.Sec66Degen
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114SuzukiZero

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem sz_coset_data {T : Type} [Group T] {a : ℕ} {K : Type}
    [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : T ≃* suzukiGroup a K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut T}
    (hord : orderOf α = p) (hαinn : α ∉ innerAut T) :
    ∃ (b : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (β ψ : MulAut (suzukiGroup a K)),
      (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
      ψ * MulAut.congr e α * ψ⁻¹ = β ∧ Nonempty (↥(fixSub β) ≃* suzukiGroup b k) := by
  have hα' : MulAut.congr e α ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  obtain ⟨σ, h, b, k, _, _, -, hbp, hkcard, hconj, ⟨eq⟩⟩ :=
    KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e α)
      ((orderOf_congr e α).trans hord) hα'
  exact ⟨b, k, inferInstance, inferInstance, szFieldAut a K σ, MulAut.conj h, hbp, hkcard, hconj,
    ⟨eq⟩⟩

theorem sz_card_fixSub_twenty {T : Type} [Group T] {a : ℕ}
    {K : Type} [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : T ≃* suzukiGroup a K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpa : p = 2 * a + 1)
    {α : MulAut T} (hord : orderOf α = p) (hαinn : α ∉ innerAut T) :
    Nat.card (fixSub α) = 20 := by
  obtain ⟨b, k, _, _, β, ψ, hbp, hkcard, hψ, ⟨efix⟩⟩ := sz_coset_data ha hK e hp hp2 hord hαinn
  have hb0 : b = 0 := by
    have h1 : (2 * b + 1) * p = 1 * p := by rw [hbp, one_mul, hpa]
    have h2 := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk : Nat.card k = 2 ^ (2 * 0 + 1) := hkcard
  have h1 : Nat.card (fixSub α) = Nat.card (fixSub β) :=
    card_fixSub_eq_of_conj e α β ψ (by rw [hψ])
  rw [h1, Nat.card_congr efix.toEquiv,
    Nat.card_congr (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
      (a := 0) (K := k) hk).toEquiv]
  exact CFSG.BenderSuzuki.lemma114_suzukiZero_card

theorem sec66T_K2_Sz : Sec66T_K2 .twistedB2 := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨-, -, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := lieModel_twistedB2_iff.mp hM
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  obtain ⟨-, -, -, -, hcyc, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  let π : MulAut T →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (suzukiGroup a K) :=
    (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K))).comp
      (MulAut.congr e).toMonoidHom
  refine no_plane_of_cyclic_quotient hp π ?_ E hE hcard hEinn
  intro x hx _
  have hxi : MulAut.congr e x ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    (QuotientGroup.eq_one_iff _).mp hx
  exact (mem_innerAut_congr e x).mp hxi

theorem sec66T_K1_Sz : Sec66T_K1 .twistedB2 := by
  intro T _ _ p hp hp5 hmodel _ α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  obtain ⟨hn0, -, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := lieModel_twistedB2_iff.mp hM
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have hp2 : p ≠ 2 := by omega
  subst hn0
  have hfinG : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  obtain ⟨b, k, _, _, β, ψ, hbp, hkcard, hψ, ⟨efix⟩⟩ := sz_coset_data ha hK e hp hp2 hord hαinn
  by_cases hb : 1 ≤ b
  ·
    obtain ⟨-, hnt, hsimple⟩ := suzuki_simple hb hkcard
    have hnab : ∃ x y : suzukiGroup b k, x * y ≠ y * x :=
      exists_noncomm_of_perfect (suzuki_perfect hb hkcard).1
    have hX : LieModel (suzukiGroup b k) .twistedB2 0 2 (2 * b + 1) :=
      lieModel_twistedB2_iff.mpr ⟨rfl, rfl, b, hb, k, inferInstance, inferInstance, rfl, hkcard,
        ⟨MulEquiv.refl _⟩⟩
    have hfix := lieModel_fixRes_of_simple hnab efix hX
    have hff' : f = p * (2 * b + 1) := by rw [mul_comm, hbp, hfa]
    exact fieldAutT_of_conj_fix e hM hff' (by omega) α β ψ hψ hfix
  ·
    exfalso
    have : Fact p.Prime := ⟨hp⟩
    have hb0 : b = 0 := by omega
    subst hb0
    have hpa : p = 2 * a + 1 := by simpa using hbp
    have hcard20 := sz_card_fixSub_twenty ha hK e hp hp2 hpa hord hαinn
    have hqfix : q ∈ fixSub α := hαq
    have hordq : orderOf q = p := orderOf_eq_prime hqp hq1
    have hdvd : p ∣ 20 := by
      have h1 := orderOf_dvd_natCard (⟨q, hqfix⟩ : fixSub α)
      rw [Subgroup.orderOf_mk, hordq, hcard20] at h1
      exact h1
    have hp5eq : p = 5 := by
      have h20 : p ∣ 2 ^ 2 * 5 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).mp h20 with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h
    have hcenter : Subgroup.center T = ⊥ :=
      center_eq_bot_of_mulEquiv e (KE.suzuki_center_eq_bot ha hK)
    obtain ⟨R, β₁, hRne, hR2, h5, -, -, -, hβ1, hβp, hβfix, hcases⟩ :=
      exists_fixed_line_of_K1 hcenter hp hp5 hord hαinn hq1 hqp hαq hU2 hαU hqU hmv
    have h16 : 16 ≤ Nat.card R := h5 hp5eq
    rcases hcases with ⟨b', hb', hb'ord⟩ | ⟨hβinn, hβord⟩
    ·
      have hRC : R.map e.toMonoidHom ≤
          Subgroup.centralizer ({e b'} : Set (suzukiGroup a K)) := by
        rintro _ ⟨r, hr, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : β₁ r = r := hβfix r hr
        rw [← hb', MulAut.conj_apply] at h1
        have h2 : b' * r = r * b' := by
          calc b' * r = (b' * r * b'⁻¹) * b' := by group
            _ = r * b' := by rw [h1]
        show e r * e b' = e b' * e r
        rw [← map_mul, ← map_mul, h2]
      have hb'1 : b' ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hb'ord
        exact hp.one_lt.ne hb'ord
      have hx1 : e b' ≠ 1 := fun h => hb'1 (e.injective (by rw [h, map_one]))
      have hxodd : Odd (orderOf (e b')) := by
        rw [show orderOf (e b') = orderOf b' from orderOf_injective e.toMonoidHom e.injective b',
          hb'ord, hp5eq]
        decide
      have hodd :=
        ((CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2
          (e b') hx1 hxodd).1
      have hbot := eq_bot_of_isPGroup_two_of_odd (hR2.map e.toMonoidHom) hRC hodd
      apply hRne
      have hc : Nat.card (R.map e.toMonoidHom) = Nat.card R :=
        Subgroup.card_map_of_injective e.injective
      rw [hbot, Subgroup.card_bot] at hc
      exact Subgroup.eq_bot_of_card_eq R hc.symm
    ·
      have hcard20' := sz_card_fixSub_twenty ha hK e hp hp2 hpa hβord hβinn
      have hle : R ≤ fixSub β₁ := fun r hr => hβfix r hr
      exact false_of_two_group_in_card_twenty hR2 hle hcard20' h16

end CFSG.RankThree.PartOne.Sec66T
