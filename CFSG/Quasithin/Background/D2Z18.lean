module

public import CFSG.Quasithin.Background.D2Z17

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section Concl

variable {X : Subgroup (MulAut V)} {r : ℚ}

theorem acts_trivially_of_coprime (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} (hrk : rk W = 2)
    {y : MulAut V} (hy : y ∈ stabSub W) (hcop : Nat.Coprime (orderOf y) 6) :
    ∀ w ∈ W, y w = w := by
  have hVW : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have h6 := card_mulAut_of_rk_two (V := ↥W) hVW hrk
  set φ := resHom W ⟨y, hy⟩ with hφ
  have h1 : orderOf φ ∣ orderOf y := by
    have := orderOf_map_dvd (resHom W) (⟨y, hy⟩ : stabSub W)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf φ ∣ 6 := by
    have := orderOf_dvd_natCard φ
    rwa [h6] at this
  have h3 : orderOf φ ∣ Nat.gcd (orderOf y) 6 := Nat.dvd_gcd h1 h2
  rw [hcop, Nat.dvd_one] at h3
  have hφ1 : φ = 1 := orderOf_eq_one_iff.mp h3
  intro w hw
  have := congrArg (fun ψ : MulAut ↥W => ((ψ ⟨w, hw⟩ : ↥W) : V)) hφ1
  exact this

theorem coprime_six_of_prime_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℕ) :
    Nat.Coprime (p ^ a) 6 := by
  refine Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_)
  have := Nat.le_of_dvd (by norm_num) hd
  interval_cases p
  · omega
  · exact absurd hp (by norm_num)

theorem pCoreOf_eq_bot_of_five_le (hV : ∀ v : V, v ^ 2 = 1) {s : ℕ}
    {Pi : Fin s → Subgroup (MulAut V)} (d : PDecomp X Pi) (hW : fixV (pCoreOf 3 X) = ⊥)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) : pCoreOf p X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [eq_bot_iff]
  intro y hy
  have hyX : y ∈ X := pCoreOf_le p X hy
  have hcomm : ∀ z ∈ pCoreOf 3 X, y * z = z * y := by
    intro z hz
    have hzX : z ∈ X := pCoreOf_le 3 X hz
    have hc1 : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf p X := by
      have h1 : z * y⁻¹ * z⁻¹ ∈ pCoreOf p X :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p X hzX) y⁻¹).mp
          ((pCoreOf p X).inv_mem hy)
      have := (pCoreOf p X).mul_mem hy h1
      simpa [mul_assoc] using this
    have hc2 : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 3 X := by
      have h1 : y * z * y⁻¹ ∈ pCoreOf 3 X :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hyX) z).mp hz
      exact (pCoreOf 3 X).mul_mem h1 ((pCoreOf 3 X).inv_mem hz)
    have hbot : pCoreOf p X ⊓ pCoreOf 3 X = ⊥ :=
      isPGroup_bot_of_two_primes (p := p) (q := 3) (by omega)
        ((pCoreOf_isPGroup p X).to_le inf_le_left) ((pCoreOf_isPGroup 3 X).to_le inf_le_right)
    have hc : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf p X ⊓ pCoreOf 3 X := ⟨hc1, hc2⟩
    rw [hbot] at hc
    have h1 : y * z * y⁻¹ * z⁻¹ = 1 := Subgroup.mem_bot.mp hc
    have h2 : y * z * y⁻¹ = z := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hstab : ∀ i, y ∈ stabSub (commV (Pi i)) := by
    intro i
    refine mem_stabSub_commV (fun q hq => ?_) (fun q hq => ?_)
    · have hqP : q ∈ pCoreOf 3 X := d.le_P i hq
      rw [hcomm q hqP, mul_inv_cancel_right]; exact hq
    · have hqP : q ∈ pCoreOf 3 X := d.le_P i hq
      have : y⁻¹ * q * y = q := by
        calc y⁻¹ * q * y = y⁻¹ * (q * y) := by group
          _ = y⁻¹ * (y * q) := by rw [← hcomm q hqP]
          _ = q := by group
      rw [this]; exact hq
  obtain ⟨a, ha⟩ := exists_orderOf_eq_pow (pCoreOf_isPGroup p X) hy
  have hcop : Nat.Coprime (orderOf y) 6 := by
    rw [ha]; exact coprime_six_of_prime_ge_five (Fact.out) hp5 a
  have htriv : ∀ i, ∀ w ∈ commV (Pi i), y w = w := fun i =>
    acts_trivially_of_coprime hV (d.rk_eq i) (hstab i) hcop
  have htop := iSup_commV_eq_top hV d hW
  have : fixV (Subgroup.zpowers y) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le fun i w hw => mem_fixV_zpowers_iff.mpr (htriv i w hw)
  exact Subgroup.mem_bot.mpr (eq_one_of_fixV_eq_top this)

theorem rk_eq_two_mul (hV : ∀ v : V, v ^ 2 = 1) {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)}
    (d : PDecomp X Pi) (hW : fixV (pCoreOf 3 X) = ⊥) : rk V = 2 * s := by
  have htop := iSup_commV_eq_top hV d hW
  have h1 := rk_iSup_biSup_eq_sum (fun i => commV (Pi i)) d.vindep Finset.univ
  have e : (⨆ i ∈ (Finset.univ : Finset (Fin s)), commV (Pi i)) = ⨆ i, commV (Pi i) :=
    le_antisymm (iSup₂_le fun i _ => le_iSup (fun i => commV (Pi i)) i)
      (iSup_le fun i => le_iSup₂_of_le i (Finset.mem_univ i) le_rfl)
  rw [e, htop, rk_top] at h1
  simp only [d.rk_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  omega

theorem fittingOf_eq_pCoreOf_three (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r) {s : ℕ}
    {Pi : Fin s → Subgroup (MulAut V)} (d : PDecomp X Pi) (hW : fixV (pCoreOf 3 X) = ⊥) :
    fittingOf X = pCoreOf 3 X := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply le_antisymm
  · have hR : fittingRes23 X = ⊥ := by
      refine eq_bot_iff.mpr (iSup_le fun p => iSup_le fun hp => iSup_le fun hp2 =>
        iSup_le fun hp3 => ?_)
      have : Fact p.Prime := ⟨hp⟩
      have hp5 : 5 ≤ p := by
        by_contra hlt
        push Not at hlt
        have h2le := hp.two_le
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by norm_num)
      exact (pCoreOf_eq_bot_of_five_le hV d hW hp5).le
    calc fittingOf X ≤ oddFitting X := fittingOf_le_oddFitting h.o2
      _ ≤ pCoreOf 3 X ⊔ fittingRes23 X := oddFitting_le_sup X
      _ = pCoreOf 3 X := by rw [hR, sup_bot_eq]
  · exact le_fittingOf_of_normal (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X) fun x hx g hg =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hx) g).mp hg

theorem D2_22_syl2 (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) {s : ℕ} {Pi : Fin s → Subgroup (MulAut V)}
    (d : PDecomp X Pi) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X)
    (hXeq : X = pCoreOf 3 X ⊔ A) : QhatStar X = sylow2Of X := by
  have hcardX : Nat.card X = 3 ^ s * 4 := by
    have := card_sup_pCoreOf hV hA (hall A hA) d
    rwa [← hXeq] at this
  refine qhatStar_eq_sylow2Of (QhatStar_nonempty h.qhat h.le_two) fun B hB => ?_
  obtain ⟨r', -, -, ⟨⟨hB2, -⟩, -⟩, -⟩ := QhatStar_spec hB
  refine mem_sylow2Of_of_card (QhatStar_le hB) hB2.isElemAbelian2.isPGroup (m := 3 ^ s)
    ((show Odd 3 from ⟨1, rfl⟩).pow) ?_
  rw [hcardX, (hall B hB).card_A hV, mul_comm]

theorem D2_22_six (hV : ∀ v : V, v ^ 2 = 1) (h : D217Hyp X r)
    (hall : ∀ B ∈ QhatStar X, D214Hyp X B r) {Pi : Fin 3 → Subgroup (MulAut V)}
    (d : PDecomp X Pi) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X)
    (hXeq : X = pCoreOf 3 X ⊔ A) (hr : r = 3 / 2) (hW : fixV (pCoreOf 3 X) = ⊥) :
    IsElemAbelian 3 (fittingOf X) ∧ Nat.card (fittingOf X) = 27 ∧
      (∃ E : Subgroup (MulAut V), E ≤ X ∧ IsElemAbelian2 E ∧ Nat.card E = 4 ∧
        X = fittingOf X ⊔ E) ∧ rk V = 6 ∧ r = 3 / 2 := by
  have hF := fittingOf_eq_pCoreOf_three hV h d hW
  have hcomm := hcomm_of_hall hV h hall
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  obtain ⟨a, b, k⟩ := (hall A hA).exists_klein hV
  refine ⟨?_, ?_, ⟨A, QhatStar_le hA, hA2.isElemAbelian2, (hall A hA).card_A hV, ?_⟩, ?_, hr⟩
  · rw [hF]
    exact ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩,
      pCoreOf_pow_three hV (hall A hA)⟩
  · rw [hF, d.card_P]; norm_num
  · rw [hF]; exact hXeq
  · rw [rk_eq_two_mul hV d hW]

omit [Finite V] in
theorem D2_22_five_iso {Pi : Fin 2 → Subgroup (MulAut V)} {A : Subgroup (MulAut V)}
    (hc : Case7i X A Pi) (hXeq : X = pCoreOf 3 X ⊔ A) :
    Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3) := by
  obtain ⟨-, L₁, L₂, hcomm, hinf, hsup, ⟨e₁⟩, ⟨e₂⟩, -⟩ := hc
  obtain ⟨e⟩ := sup_mulEquiv_prod hcomm hinf
  have hX : X = L₁ ⊔ L₂ := by rw [hsup]; exact hXeq
  exact ⟨(MulEquiv.subgroupCongr hX).trans (e.trans (MulEquiv.prodCongr e₁ e₂))⟩

end Concl

end CFSG.Quasithin
