module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldCentralizer

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.PresentationLocal
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem card_sympFour : Nat.card sympFour = 720 := by
  rw [Nat.card_congr (Equiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩),
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem card_spFixedGroup_of_card_two {p : ℕ} (hp : Odd p) {σ : K ≃+* K} (hσp : σ ^ p = 1)
    (hk2 : Nat.card (descentField σ) = 2) :
    Nat.card ↥(spFixedGroup (fieldAut 2 K σ)) = 720 := by
  have : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  rw [spFixedGroup_fieldAut_eq_range hp hσp, ← range_subfieldInj (r := 2) σ]
  rw [← Nat.card_congr (MonoidHom.ofInjective (subfieldInj_injective (r := 2) σ)).toEquiv,
    Nat.card_congr (statedProjEquivSympFour hk2).toEquiv, card_sympFour]

theorem exceptional_fixedGroup_prime_order {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hk2 : Nat.card (descentField σ) = 2) {x : StatedProj (StatedSp 2 K)}
    (hx : x ∈ spFixedGroup (fieldAut 2 K σ)) (hxp : orderOf x = p) :
    ℓ = 2 ∧ f = p ∧ p = 5 ∧ ℓ ^ f = 32 := by
  obtain ⟨hpf, hcardk⟩ := card_descentField hℓ hf hK hσ
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hcard := card_spFixedGroup_of_card_two hodd hσp hk2
  have hdvd : p ∣ 720 := by
    have := Subgroup.orderOf_dvd_natCard (spFixedGroup (fieldAut 2 K σ)) hx
    rwa [hxp, hcard] at this
  have hp5 : p = 5 := by
    have h720 : p ∣ 2 ^ 4 * 3 ^ 2 * 5 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h720 with h | h
    · exfalso
      rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
  have hpow : ℓ ^ (f / p) = 2 := by rw [← hcardk, hk2]
  have hfp : 1 ≤ f / p := by
    by_contra h0
    have : f / p = 0 := Nat.lt_one_iff.mp (not_le.mp h0)
    rw [this, pow_zero] at hpow
    omega
  have hℓ2 : ℓ = 2 := by
    have h1 : ℓ ∣ 2 := by
      rw [← hpow]
      exact dvd_pow_self ℓ (Nat.pos_iff_ne_zero.mp hfp)
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1
  have hfd : f / p = 1 := by
    rw [hℓ2] at hpow
    exact Nat.pow_right_injective (le_refl 2) (by simpa using hpow)
  have hfpeq : f = p := by
    have := Nat.mul_div_cancel' hpf
    rw [hfd, mul_one] at this
    exact this.symm
  refine ⟨hℓ2, hfpeq, hp5, ?_⟩
  rw [hℓ2, hfpeq, hp5]
  norm_num

end Fixed

section Plane

variable {K : Type} [Field K] [Finite K]

theorem noninner_plane_exceptional {ℓ f r p : ℕ} (O : SpOuter ℓ f r K) (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (hr : 2 ≤ r) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hcyc : IsCyclic (K ≃+* K)) {A : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    [IsElementaryAbelian p A] (hAcard : Nat.card A = p ^ 2)
    (hAH : ¬ A ≤ inner (StatedProj (StatedSp r K))) :
    r = 2 → ℓ = 2 → f = p → p = 5 ∧ ℓ ^ f = 32 := by
  intro hr2 hℓ2 hfp
  subst hr2
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hcap := card_inf_inner_eq_prime O hr hp hp2 hcyc hAcard hAH
  obtain ⟨a₀, ha₀A, ha₀H⟩ := IsConcreteLE.not_le_iff_exists.mp hAH
  obtain ⟨hpf, σ, hσ, h, -, hah⟩ := noninner_element_data O hp hp2 ha₀A ha₀H
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ inner (StatedProj (StatedSp 2 K))))
    p (by rw [hcap])
  set x : MulAut (StatedProj (StatedSp 2 K)) := (g : MulAut (StatedProj (StatedSp 2 K))) with hx
  have hxA : x ∈ A := g.2.1
  have hxH : x ∈ inner (StatedProj (StatedSp 2 K)) := g.2.2
  have hxp : orderOf x = p := by rw [hx, Subgroup.orderOf_coe, hg]
  have hcomm : a₀ * x = x * a₀ :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨a₀, ha₀A⟩ ⟨x, hxA⟩)
  have hq4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hfp' : p ≤ f := Nat.le_of_dvd (by omega) hpf
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
      _ ≤ ℓ ^ p := Nat.pow_le_pow_left hℓ.two_le p
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hfp'
  have hinj := KCSymplectic.conj_injective_statedProj_statedSp (r := 2) (K := K) hr hq4
  set y : MulAut (StatedProj (StatedSp 2 K)) := h⁻¹ * x * h with hy
  have hyH : y ∈ inner (StatedProj (StatedSp 2 K)) := by
    have := (inner_normal (StatedProj (StatedSp 2 K))).conj_mem x hxH h⁻¹
    rwa [inv_inv] at this
  have hyf : y * fieldAut 2 K σ = fieldAut 2 K σ * y := by
    have h1 : fieldAut 2 K σ = h⁻¹ * a₀ * h := by rw [hah]; group
    rw [hy, h1]
    calc h⁻¹ * x * h * (h⁻¹ * a₀ * h) = h⁻¹ * (x * a₀) * h := by group
      _ = h⁻¹ * (a₀ * x) * h := by rw [hcomm]
      _ = h⁻¹ * a₀ * h * (h⁻¹ * x * h) := by group
  obtain ⟨z, hz⟩ := hyH
  have hzf : fieldAut 2 K σ z = z := by
    refine (conj_mem_centralizer_iff hinj (fieldAut 2 K σ) z).mp ?_
    rw [Subgroup.mem_centralizer_singleton_iff, hz]
    exact hyf
  have hzp : orderOf z = p := by
    have h1 : orderOf (MulAut.conj z : MulAut (StatedProj (StatedSp 2 K))) = orderOf z :=
      orderOf_injective _ hinj z
    have h2 : orderOf y = orderOf x := by
      have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹ : MulAut (MulAut (StatedProj (StatedSp 2 K)))) x
      rw [hy]
      simpa [MulAut.conj_apply] using this
    rw [← h1, hz, h2, hxp]
  have hk2 : Nat.card (descentField σ) = 2 := by
    obtain ⟨-, hcard⟩ := card_descentField hℓ hf hK hσ
    rw [hcard, hℓ2, hfp, Nat.div_self hp.pos, pow_one]
  obtain ⟨-, -, hp5, hq⟩ := exceptional_fixedGroup_prime_order hℓ hf hK hp hp3 hσ hk2
    (x := z) hzf hzp
  exact ⟨hp5, hq⟩

end Plane

end CFSG.RankThree.PartOne.KCSpComm
