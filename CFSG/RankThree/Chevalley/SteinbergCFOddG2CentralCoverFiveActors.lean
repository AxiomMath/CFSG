module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFOddCommutingSL2
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2OddField
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2Defining
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (localRank)

theorem mem_range_conj_of_congr {T H : Type*} [Group T] [Group H] (e : T ≃* H) (β : MulAut T)
    (h : MulAut.congr e β ∈ (MulAut.conj : H →* MulAut H).range) :
    β ∈ (MulAut.conj : T →* MulAut T).range := by
  obtain ⟨c, hc⟩ := h
  refine ⟨e.symm c, MulEquiv.ext fun t => ?_⟩
  have h1 := congrArg (fun γ : MulAut H => γ (e t)) hc
  change c * e t * c⁻¹ = e (β (e.symm (e t))) at h1
  rw [MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply, ← e.symm_apply_apply (β t), ← h1]
  simp

theorem odd_G2_actual_central_cover_rank_three_five_actors_inner {X T : Type} [Group X]
    [Finite X] [Group T] (Y : Subgroup X) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (η : Y →* T)
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center Y) (hX : localRank p X ≤ 3)
    (hmod : ChevalleyExceptionalModel T .G2 p f) :
    (3 < p → f = 1) ∧ (p = 3 → f ≤ 2) ∧
      ∀ β : MulAut T, orderOf β = 5 → β ∈ (MulAut.conj : T →* MulAut T).range := by
  classical
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  set e' : T ≃* adjointGroup .G2 K := e.trans (adjointQuotientEquiv .G2 K) with he'
  have hbound : 3 < p ^ f → p ^ f ≠ 9 → f ≤ 1 := fun h3 h9 => by
    obtain ⟨ι₁, ι₂, h₁, h₂, hcomm⟩ := G2_two_commuting_faithful_SL2 K hK2
    have hker' : (e'.toMonoidHom.comp η).ker ≤ Subgroup.center Y := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      simpa using hy
    obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
      CFSG.RankThree.CentralCover.commuting_SL2_odd_field_actual_central_cover_local_rank Y hp hp2
        hf (by norm_num : 1 ≤ 2) (by rw [← Nat.card_eq_fintype_card]; exact hK) h3 h9
        (e'.toMonoidHom.comp η) (e'.surjective.comp hη) hker' ![ι₁, ι₂]
        (fun i => by fin_cases i <;> assumption) (fun i j hij A B => by
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · exact hcomm A B
          · exact (hcomm B A).symm
          · exact absurd rfl hij)
    omega
  have hp3 : 3 < p → f = 1 := fun hp3 => by
    have h := CFSG.RankThree.CentralCover.three_lt_pow_and_ne_nine hp hp3 hf
    have := hbound h.1 h.2
    omega
  have hp3' : p = 3 → f ≤ 2 := by
    rintro rfl
    by_contra hf3
    have h27 : 27 ≤ 3 ^ f := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := hbound (by omega) (by omega)
    omega
  refine ⟨hp3, hp3', fun β hβ => mem_range_conj_of_congr e' β ?_⟩
  have hβ' : orderOf (MulAut.congr e' β) = 5 := by
    rw [MulEquiv.orderOf_eq, hβ]
  rcases lt_or_eq_of_le (show 3 ≤ p from by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hp.two_le
      obtain ⟨k, hk⟩ := h
      omega) with hlt | heq
  ·
    have hf1 := hp3 hlt
    obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2
        (Or.inr ⟨rfl, by omega⟩)
    rw [← hΘker, MonoidHom.mem_ker]
    exact ringEquiv_eq_one_of_card_eq_prime hp (by rw [hK, hf1, pow_one]) _
  ·
    subst heq
    have hf2 := hp3' rfl
    have : CharP K ReeTag.G2.prime := ‹CharP K 3›
    obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
    have : NeZero (2 * f) := ⟨by omega⟩
    have hinner : ∀ γ : MulAut (adjointGroup ReeTag.G2.tag K), orderOf γ = 5 →
        γ ∈ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
          MulAut (adjointGroup ReeTag.G2.tag K)).range := by
      intro γ hγ
      rw [← hΘker, MonoidHom.mem_ker]
      have h1 : orderOf (Θ γ) ∣ 5 := by
        rw [← hγ]
        exact orderOf_map_dvd _ _
      have h2 : orderOf (Θ γ) ∣ 2 * f := by
        have := orderOf_dvd_natCard (Θ γ)
        rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
      have h3 : orderOf (Θ γ) = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h1 with h | h
        · exact h
        · rw [h] at h2
          have := Nat.le_of_dvd (by omega) h2
          omega
      exact orderOf_eq_one_iff.1 h3
    exact hinner _ hβ'

end CFSG.RankThree.Chevalley
