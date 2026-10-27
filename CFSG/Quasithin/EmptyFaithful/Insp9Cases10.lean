module

public import CFSG.Quasithin.EmptyFaithful.Insp9Cases9
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace Insp9

section PSigma

open CFSG.GorensteinWalter

theorem exists_normal_psl_of_psigma {D : Type} [Group D] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ 2) (e : D ≃* ↥(F6.PSigmaL2 K)) :
    ∃ Kq : Subgroup D, Kq.Normal ∧ CFSG.IsQuasisimple ↥Kq ∧ Kq.index ∣ 2 ∧
      Nat.card ↥(Subgroup.center ↥Kq) = 1 ∧ 2 * Nat.card ↥Kq = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by
  have hp2 : p ≠ 2 := by omega
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  have h9 : 9 ≤ p ^ 2 := by nlinarith
  have h3 : 3 < Nat.card K := by rw [hK]; omega
  have hPn : (pGammaL2PSLRange K).Normal := pGammaL2PSLRange_normal K hodd h3
  have hPA : pGammaL2PSLRange K ≤ F6.PSigmaL2 K := le_sup_left
  set A := F6.PSigmaL2 K with hA
  set Q : Subgroup ↥A := (pGammaL2PSLRange K).subgroupOf A with hQ
  have hQn : Q.Normal := inferInstance
  let eQ : ↥Q ≃* PSL2 K :=
    (Subgroup.subgroupOfEquivOfLe hPA).trans (pGammaL2PSLRangeEquiv K).symm
  have hsimpleP : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; omega)
  have hsimpleQ : IsSimpleGroup ↥Q := eQ.isSimpleGroup
  have hcardQ : 2 * Nat.card ↥Q = p ^ 2 * ((p ^ 2) ^ 2 - 1) := by
    rw [Nat.card_congr eQ.toEquiv, psl2_card_formula K hodd, hK]
    have hmod : (p ^ 2) ^ 2 % 2 = 1 := by
      rw [← pow_mul, Nat.pow_mod, hpo]
    have h2 : 2 ∣ (p ^ 2) ^ 2 - 1 := by omega
    exact Nat.mul_div_cancel' (Dvd.dvd.mul_left h2 _)
  have hnc : ∃ a b : ↥Q, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥Q := ⟨⟨fun a b => hcomm a b⟩⟩
    have hq : (Nat.card ↥Q).Prime := IsSimpleGroup.prime_card
    have hcop : Nat.Coprime (p ^ 2) 2 :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (by omega))))
    have hdvd : p ^ 2 ∣ Nat.card ↥Q :=
      hcop.dvd_of_dvd_mul_left ⟨(p ^ 2) ^ 2 - 1, hcardQ⟩
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · omega
    · rw [← h1] at hcardQ
      have h4 : (p ^ 2) * 2 = (p ^ 2) * ((p ^ 2) ^ 2 - 1) := by rw [mul_comm]; exact hcardQ
      have h5 := Nat.eq_of_mul_eq_mul_left (by omega) h4
      have : 9 * 9 ≤ (p ^ 2) ^ 2 := by nlinarith
      omega
  have hqQ : CFSG.IsQuasisimple ↥Q := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hZQ : Subgroup.center ↥Q = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc
  have hidxQ : Q.index ∣ 2 := by
    let ψ := pGammaL2FieldProjection K A
    have hL : pGammaL2LinearKernel K A ≤ Q := by
      intro x hx
      have hx' : ψ x = 1 := (mem_pGammaL2LinearKernel_iff K A x).mp hx
      have hxA : (x : PGammaL2 K) ∈ pGammaL2PSLRange K ⊔
          (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range := x.2
      obtain ⟨a, ha, r, hr, har⟩ := Subgroup.mem_sup_of_normal_left.mp hxA
      obtain ⟨σ, rfl⟩ := hr
      obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K a).mp ha
      have hσ : σ = 1 := by
        have h1 : ψ x = σ := by
          show SemidirectProduct.rightHom (x : PGammaL2 K) = σ
          rw [← har]
          simp
        rw [← h1]; exact hx'
      show (x : PGammaL2 K) ∈ pGammaL2PSLRange K
      rw [← har, hσ, map_one, mul_one]
      exact ha
    have h1 : Q.index ∣ (pGammaL2LinearKernel K A).index := Subgroup.index_dvd_of_le hL
    rw [pGammaL2LinearKernel_index_eq_card_range] at h1
    have h2 : Nat.card ↥ψ.range ∣ Nat.card (RingAut K) := Subgroup.card_subgroup_dvd_card _
    rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1] at h2
    exact h1.trans h2
  let eKQ : ↥(Q.map e.symm.toMonoidHom) ≃* ↥Q :=
    (Subgroup.equivMapOfInjective Q e.symm.toMonoidHom e.symm.injective).symm
  have hnc' : ∃ a b : ↥(Q.map e.symm.toMonoidHom), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eKQ.symm a, eKQ.symm b, fun h => hab (eKQ.symm.injective (by
      rw [map_mul, map_mul]; exact h))⟩
  have hsimple' : IsSimpleGroup ↥(Q.map e.symm.toMonoidHom) := eKQ.isSimpleGroup
  refine ⟨Q.map e.symm.toMonoidHom, Subgroup.Normal.map hQn _ e.symm.surjective,
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc').1, ?_, ?_, ?_⟩
  · rw [Subgroup.index_map_of_bijective e.symm.bijective]
    exact hidxQ
  · rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnc', Subgroup.card_bot]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcardQ

end PSigma

section Arith

theorem no_odd_sq_dvd {q n : ℕ} (hq : q % 2 = 1) (hq5 : 5 ≤ q)
    (hn : n = 12096 ∨ n ∈ omegaQL ∨ n ∈ flOrders ∨ n = 360 ∨ n = 168) : ¬ q ^ 2 ∣ n := by
  intro hd
  have hb : ∀ m ∈ omegaQL, 0 < m ∧ m ≤ 2097024 := by unfold omegaQL; decide +kernel
  have hb' : ∀ m ∈ flOrders, 0 < m ∧ m ≤ 2097024 := by unfold flOrders; decide +kernel
  have hn0 : 0 < n ∧ n ≤ 2097024 := by
    rcases hn with rfl | hm | hm | rfl | rfl
    · norm_num
    · exact hb n hm
    · exact hb' n hm
    · norm_num
    · norm_num
  have hq1500 : q < 1500 := by
    by_contra hcon
    have h1 : q ^ 2 ≤ n := Nat.le_of_dvd hn0.1 hd
    have h2 : 1500 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have d1 : ∀ q ∈ Finset.range 1500, q % 2 = 1 → 5 ≤ q → ¬ q ^ 2 ∣ 12096 := by decide +kernel
  have d2 : ∀ q ∈ Finset.range 1500, q % 2 = 1 → 5 ≤ q → ∀ m ∈ omegaQL, ¬ q ^ 2 ∣ m := by
    unfold omegaQL; decide +kernel
  have d3 : ∀ q ∈ Finset.range 1500, q % 2 = 1 → 5 ≤ q → ∀ m ∈ flOrders, ¬ q ^ 2 ∣ m := by
    unfold flOrders; decide +kernel
  have d4 : ∀ q ∈ Finset.range 1500, q % 2 = 1 → 5 ≤ q → ¬ q ^ 2 ∣ 360 := by decide +kernel
  have d5 : ∀ q ∈ Finset.range 1500, q % 2 = 1 → 5 ≤ q → ¬ q ^ 2 ∣ 168 := by decide +kernel
  have hqr := Finset.mem_range.mpr hq1500
  rcases hn with rfl | hm | hm | rfl | rfl
  · exact d1 q hqr hq hq5 hd
  · exact d2 q hqr hq hq5 n hm hd
  · exact d3 q hqr hq hq5 n hm hd
  · exact d4 q hqr hq hq5 hd
  · exact d5 q hqr hq hq5 hd

end Arith

section Case9

variable {D : Type} [Group D] [Finite D] {D₁ D₂ J N : Subgroup D}

theorem case9_psigma (h : Data D₁ D₂ J N) (hs : B56Setting D N) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ 2)
    (e : D ≃* ↥(F6.PSigmaL2 K)) (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 4) : InspGoal D N := by
  obtain ⟨Kq, hKn, hKq, hidx, hZ, hcard⟩ := exists_normal_psl_of_psigma hp (by omega) K hK e
  rcases h.le_or_card_dvd_six hKq hidx (by rw [hZ]; exact one_dvd _) with hKN | hsmall
  · exfalso
    have hpo : p % 2 = 1 := by
      have := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
      exact this
    have h5 : ¬ 2 ^ 5 ∣ Nat.card D := h.not_two_pow_dvd hT (m := 5) (by norm_num)
    have h5N : ¬ 2 ^ 5 ∣ Nat.card ↥N := fun hd =>
      h5 (hd.trans (Subgroup.card_subgroup_dvd_card N))
    have h8N : ¬ 2 ^ 8 ∣ Nat.card ↥N := fun hd =>
      h5N ((Nat.pow_dvd_pow 2 (by norm_num : 5 ≤ 8)).trans hd)
    have hKn' : ∀ x ∈ N, ∀ k ∈ Kq, x * k * x⁻¹ ∈ Kq := fun x _ k hk => hKn.conj_mem k hk x
    have hcop : Nat.Coprime (p ^ 2) 2 :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (by omega))))
    have hp2K : p ^ 2 ∣ Nat.card ↥Kq := hcop.dvd_of_dvd_mul_left ⟨(p ^ 2) ^ 2 - 1, hcard⟩
    have h8K : 8 ∣ Nat.card ↥Kq := by
      obtain ⟨k, hk⟩ : ∃ k, p ^ 2 = 8 * k + 1 := by
        have : p ^ 2 % 8 = 1 := by
          have h2 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
          rcases h2 with h2 | h2 | h2 | h2 <;> simp [Nat.pow_mod, h2]
        exact ⟨p ^ 2 / 8, by omega⟩
      have hsq : (8 * k + 1) ^ 2 - 1 = 16 * (4 * k ^ 2 + k) := by
        have : (8 * k + 1) ^ 2 = 16 * (4 * k ^ 2 + k) + 1 := by ring
        omega
      rw [hk, hsq] at hcard
      exact ⟨(8 * k + 1) * (4 * k ^ 2 + k), by nlinarith⟩
    rcases hs.normal_quasisimple_cases hKN hKn' hKq h8N with hd | hm | ⟨c, hc, hdc⟩ | hd | hd |
        ⟨c, hdc, hcN⟩
    · exact no_odd_sq_dvd hpo hp5 (Or.inl rfl) (hp2K.trans hd)
    · exact no_odd_sq_dvd hpo hp5 (Or.inr (Or.inl (by
        have := hm; exact this))) (hp2K.trans (dvd_refl _))
    · exact no_odd_sq_dvd hpo hp5 (Or.inr (Or.inr (Or.inl hc))) (hp2K.trans hdc)
    · exact no_odd_sq_dvd hpo hp5 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (hp2K.trans hd)
    · exact no_odd_sq_dvd hpo hp5 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (hp2K.trans hd)
    · have h1 : 8 ∣ c := h8K.trans hdc
      have h2 : 168 * 8 ∣ 168 * c := Nat.mul_dvd_mul_left 168 h1
      exact h5N ((show 2 ^ 5 ∣ 168 * 8 by norm_num).trans (h2.trans hcN))
  · left
    exact hs.s3_of_small (card_small_of_dvd_six hsmall).1 (card_small_of_dvd_six hsmall).2

theorem inspCase9 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseNineCat H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseNineCat H₁ H₂ →
      InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨hD, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ 4 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      simp
    rcases hD with he | hH | ⟨p, hp, hmod, hL2⟩
    · obtain ⟨e⟩ := he
      exact case9_s7 h hs e
    · exact case9_hat7 h hs hH hT
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL2
      exact case9_psigma h hs hp (by omega) K hK e hT
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Case9

end Insp9

end CFSG.Quasithin
