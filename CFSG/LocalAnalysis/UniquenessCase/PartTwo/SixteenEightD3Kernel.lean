module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Supp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
  {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}

private lemma s16e_d3_ker_le_stabSub (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) :
    s16e_d3_ker A Δ ≤ stabSub (Δ i) :=
  fun _ hg => Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hg).2 i

theorem s16e_d3_card_autSub_ker_dvd (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) :
    Nat.card (autSub (s16e_d3_ker A Δ) (Δ i)) ∣ 21 := by
  have hk : s16e_d3_ker A Δ ≤ stabSub (Δ i) := s16e_d3_ker_le_stabSub h i
  have hL : L ≤ stabSub (Δ i) := (s16e_d3_le_ker h).trans hk
  have hNL : ∀ n ∈ s16e_d3_ker A Δ, L.map (MulAut.conj n).toMonoidHom = L :=
    fun n hn => h.normal n (Subgroup.mem_inf.mp hn).1
  exact s16e_d3_card_autSub_dvd (Y := Δ i) h.sq_eq_one (s16e_d3_card_block h i) hk hL hNL
    (s16e_d3_card_autSub h i)

theorem s16e_d3_card_ker_dvd (h : s16e_d3_Ctx A L r Δ σ) :
    Nat.card ↥(s16e_d3_ker A Δ) ∣ 21 ^ (r + 1) := by
  classical
  let B := s16e_d3_ker A Δ
  have hk : ∀ i : Fin (r + 1), B ≤ stabSub (Δ i) := fun i => s16e_d3_ker_le_stabSub h i
  let φ : ∀ i : Fin (r + 1), ↥B →* ↥(autSub B (Δ i)) := fun i =>
    ((resHom (Δ i)).comp (Subgroup.inclusion (hk i))).codRestrict (autSub B (Δ i))
      (fun g => mem_autSub.mpr ⟨⟨(g : MulAut W), hk i g.2⟩, g.2, rfl⟩)
  let Φ : ↥B →* (∀ i : Fin (r + 1), ↥(autSub B (Δ i))) := MonoidHom.pi φ
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine s16e_d3_eq_one_of_forall_fixes h.cfg fun i x hx => ?_
    have h1 : φ i g = 1 := by
      have h := congrFun hg i
      rw [MonoidHom.pi_apply] at h
      simpa using h
    have h2 : (φ i g : MulAut ↥(Δ i)) = 1 := by
      rw [h1]; rfl
    have h3 := congrArg (fun (ψ : MulAut ↥(Δ i)) => ((ψ ⟨x, hx⟩ : ↥(Δ i)) : W)) h2
    simp only [MulAut.one_apply] at h3
    change ((resHom (Δ i) (Subgroup.inclusion (hk i) g) ⟨x, hx⟩ : ↥(Δ i)) : W) = x at h3
    rw [resHom_apply] at h3
    simpa using h3
  have hdiv : Nat.card ↥B ∣ Nat.card (∀ i : Fin (r + 1), ↥(autSub B (Δ i))) :=
    Subgroup.card_dvd_of_injective Φ hΦ
  rw [Nat.card_pi] at hdiv
  refine hdiv.trans ?_
  have hprod : (∏ i : Fin (r + 1), Nat.card ↥(autSub B (Δ i))) ∣ 21 ^ (r + 1) := by
    have h := Finset.prod_dvd_prod_of_dvd (s := Finset.univ)
      (fun i : Fin (r + 1) => Nat.card ↥(autSub B (Δ i))) (fun _ : Fin (r + 1) => 21)
      (fun i _ => s16e_d3_card_autSub_ker_dvd h i)
    simpa using h
  exact hprod

theorem s16e_d3_not_three_dvd_card_inf_centSub (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) :
    ¬ 3 ∣ Nat.card ↥(s16e_d3_ker A Δ ⊓ centSub (Δ i)) := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(s16e_d3_ker A Δ ⊓ centSub (Δ i))) 3 h3
  have hx3 : (x : MulAut W) ^ 3 = 1 := by
    have h1 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg (fun y : ↥(s16e_d3_ker A Δ ⊓ centSub (Δ i)) => (y : MulAut W)) h1
  have hxB : (x : MulAut W) ∈ s16e_d3_ker A Δ := (Subgroup.mem_inf.mp x.2).1
  have hxc : ∀ y ∈ Δ i, (x : MulAut W) y = y :=
    mem_centSub.mp (Subgroup.mem_inf.mp x.2).2
  have hx1 : (x : MulAut W) = 1 := s16e_d3_eq_one_of_pow_three h hxB hx3 i hxc
  have hxone : x = 1 := Subtype.ext (by simpa using hx1)
  rw [hxone, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem s16e_d3_not_nine_dvd_card_ker (h : s16e_d3_Ctx A L r Δ σ) :
    ¬ 9 ∣ Nat.card ↥(s16e_d3_ker A Δ) := by
  intro h9
  let B := s16e_d3_ker A Δ
  have hk : B ≤ stabSub (Δ 0) := s16e_d3_ker_le_stabSub h 0
  have hcard : Nat.card (autSub B (Δ 0)) * Nat.card ↥(B ⊓ centSub (Δ 0)) = Nat.card ↥B :=
    card_autSub_mul (A := B) (U := Δ 0) hk
  have hc3 : ¬ 3 ∣ Nat.card ↥(B ⊓ centSub (Δ 0)) := by
    simpa [B] using s16e_d3_not_three_dvd_card_inf_centSub h 0
  have hcop : Nat.Coprime 9 (Nat.card ↥(B ⊓ centSub (Δ 0))) := by
    have hc : Nat.Coprime 3 (Nat.card ↥(B ⊓ centSub (Δ 0))) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hc3
    have h := (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 3
      (Nat.card ↥(B ⊓ centSub (Δ 0)))).2 hc
    simpa using h
  have hdvd : 9 ∣ Nat.card (autSub B (Δ 0)) * Nat.card ↥(B ⊓ centSub (Δ 0)) := by
    rw [hcard]; exact h9
  have h9a : 9 ∣ Nat.card (autSub B (Δ 0)) := hcop.dvd_mul_right.1 hdvd
  exact absurd (h9a.trans (by simpa [B] using s16e_d3_card_autSub_ker_dvd h 0))
    (by norm_num)

theorem s16e_d3_dvd_seven_pow_mul_three {n m : ℕ} (h21 : n ∣ 21 ^ m) (h9 : ¬ 9 ∣ n) :
    n ∣ 7 ^ m * 3 := by
  have h21eq : (21 : ℕ) ^ m = 3 ^ m * 7 ^ m := by
    rw [← mul_pow]; norm_num
  rw [h21eq] at h21
  obtain ⟨d1, d2, hd1, hd2, hd12⟩ := Nat.dvd_mul.mp h21
  obtain ⟨a, _ha, hda⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd1
  have ha1 : a ≤ 1 := by
    by_contra hle
    have ha2 : 2 ≤ a := by omega
    have h9d1 : 9 ∣ d1 := by
      rw [hda, show (9 : ℕ) = 3 ^ 2 from by norm_num]
      exact pow_dvd_pow 3 ha2
    exact h9 (by rw [← hd12]; exact dvd_mul_of_dvd_left h9d1 d2)
  have hd1_3 : d1 ∣ 3 := by
    rw [hda]
    interval_cases a <;> norm_num
  rw [← hd12]
  calc d1 * d2 ∣ 3 * 7 ^ m := mul_dvd_mul hd1_3 hd2
    _ = 7 ^ m * 3 := Nat.mul_comm _ _

theorem s16e_d3_card_ker_dvd_seven_pow_mul_three (h : s16e_d3_Ctx A L r Δ σ) :
    Nat.card ↥(s16e_d3_ker A Δ) ∣ 7 ^ (r + 1) * 3 :=
  s16e_d3_dvd_seven_pow_mul_three (s16e_d3_card_ker_dvd h) (s16e_d3_not_nine_dvd_card_ker h)

theorem s16e_d3_card_dvd_seven_pow_mul_three_mul_factorial (h : s16e_d3_Ctx A L r Δ σ) :
    Nat.card ↥A ∣ 7 ^ (r + 1) * 3 * Nat.factorial (r + 1) := by
  rw [s16e_d3_card_eq_mul_factorial h.cfg]
  exact mul_dvd_mul_right (s16e_d3_card_ker_dvd_seven_pow_mul_three h) _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
