module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBeta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_central_conj_eq_self {p : ℕ} {t : MulAut W} {P : Subgroup (MulAut W)}
    (h : InvCfg131 p t P)
    (hα : ¬ ∃ z ∈ P, orderOf z = p ∧ (∀ y ∈ P, y * z = z * y) ∧ t * z * t⁻¹ = z⁻¹)
    {z : MulAut W} (hzP : z ∈ P) (hzc : ∀ y ∈ P, y * z = z * y) :
    t * z * t⁻¹ = z := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rw [h.ht, pow_two] at h2
    exact h2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htzc : ∀ y ∈ P, y * (t * z * t⁻¹) = (t * z * t⁻¹) * y := by
    intro y hy
    have hmem : t⁻¹ * y * t ∈ P := by
      rw [htinv]
      simpa [htinv] using h.hn y hy
    have h1 : y * (t * z * t⁻¹) = t * ((t⁻¹ * y * t) * z) * t⁻¹ := by group
    have h2 : t * ((t⁻¹ * y * t) * z) * t⁻¹ = t * (z * (t⁻¹ * y * t)) * t⁻¹ := by
      rw [hzc (t⁻¹ * y * t) hmem]
    have h3 : t * (z * (t⁻¹ * y * t)) * t⁻¹ = (t * z * t⁻¹) * y := by group
    exact h1.trans (h2.trans h3)
  set c : MulAut W := z⁻¹ * (t * z * t⁻¹) with hcdef
  have hcP : c ∈ P := P.mul_mem (P.inv_mem hzP) (h.hn z hzP)
  have hcc : ∀ y ∈ P, y * c = c * y := by
    intro y hy
    have hzy : Commute y z := (commute_iff_eq y z).mpr (hzc y hy)
    have hz1 : y * z⁻¹ = z⁻¹ * y := hzy.inv_right.eq
    have hz2 : y * (t * z * t⁻¹) = (t * z * t⁻¹) * y := htzc y hy
    calc y * c = (y * z⁻¹) * (t * z * t⁻¹) := by rw [hcdef]; group
      _ = (z⁻¹ * y) * (t * z * t⁻¹) := by rw [hz1]
      _ = z⁻¹ * (y * (t * z * t⁻¹)) := by group
      _ = z⁻¹ * ((t * z * t⁻¹) * y) := by rw [hz2]
      _ = (z⁻¹ * (t * z * t⁻¹)) * y := by group
      _ = c * y := by rw [hcdef]
  have hcinv : t * c * t⁻¹ = c⁻¹ := by
    have h2 : t * (t * z * t⁻¹) * t⁻¹ = z := by
      have h2' : t * (t * z * t) * t = z := by
        calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
          _ = z := by rw [htt]; simp
      simpa [htinv] using h2'
    rw [hcdef]
    calc t * (z⁻¹ * (t * z * t⁻¹)) * t⁻¹
        = (t * z * t⁻¹)⁻¹ * (t * (t * z * t⁻¹) * t⁻¹) := by group
      _ = (t * z * t⁻¹)⁻¹ * z := by rw [h2]
      _ = (z⁻¹ * (t * z * t⁻¹))⁻¹ := by group
  by_contra hne
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hne
    calc t * z * t⁻¹ = z * (z⁻¹ * (t * z * t⁻¹)) := by group
      _ = z * 1 := by rw [← hcdef, hc1]
      _ = z := by simp
  obtain ⟨k, hk⟩ := h.hP.exists_orderOf_eq_pow (⟨c, hcP⟩ : ↥P)
  have hcord : orderOf c = p ^ k := by
    rw [← Subgroup.orderOf_mk c hcP]
    exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcord
    exact hc1 (orderOf_eq_one_iff.mp hcord)
  have hdvd : p ∣ orderOf c := by
    rw [hcord]
    exact dvd_pow_self p hk0
  let c' : MulAut W := c ^ (orderOf c / p)
  have hc'ord : orderOf c' = p := by
    dsimp only [c']
    exact orderOf_pow_orderOf_div (by rw [hcord]; exact pow_ne_zero k h.hp.ne_zero) hdvd
  have hc'P : c' ∈ P := P.pow_mem hcP _
  have hc'c : ∀ y ∈ P, y * c' = c' * y := by
    intro y hy
    have hcomm : Commute y c := (commute_iff_eq y c).mpr (hcc y hy)
    exact (hcomm.pow_right _).eq
  have hc'inv : t * c' * t⁻¹ = c'⁻¹ := by
    dsimp only [c']
    exact w16g_conj_pow_inv hcinv _
  exact hα ⟨c', hc'P, hc'ord, hc'c, hc'inv⟩

private theorem w16g_exists_central_prime_order {p : ℕ} {t : MulAut W}
    {P : Subgroup (MulAut W)} (h : InvCfg131 p t P)
    (hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) :
    ∃ z₀ : MulAut W, z₀ ∈ P ∧ orderOf z₀ = p ∧
      (∀ y ∈ P, y * z₀ = z₀ * y) ∧ t * z₀ * t⁻¹ = z₀ := by
  haveI : Fact p.Prime := ⟨h.hp⟩
  haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr h.hne
  have hcenter : Nontrivial (Subgroup.center ↥P) := IsPGroup.center_nontrivial h.hP
  obtain ⟨g, hg, hg1⟩ :=
    (Subgroup.nontrivial_iff_exists_ne_one (H := Subgroup.center ↥P)).mp hcenter
  have hgdvd : p ∣ orderOf g := h.hP.dvd_orderOf hg1
  have hgdvd' : p ∣ orderOf (g : MulAut W) := by
    rw [Subgroup.orderOf_coe g]
    exact hgdvd
  refine ⟨(g : MulAut W) ^ (orderOf (g : MulAut W) / p), P.pow_mem g.2 _, ?_, ?_, ?_⟩
  · exact orderOf_pow_orderOf_div (orderOf_pos (g : MulAut W)).ne' hgdvd'
  · intro y hy
    have hgc : y * (g : MulAut W) = (g : MulAut W) * y :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hg ⟨y, hy⟩)
    have hcomm : Commute y (g : MulAut W) := (commute_iff_eq y _).mpr hgc
    exact (hcomm.pow_right _).eq
  · have hgc : ∀ y ∈ P, y * (g : MulAut W) = (g : MulAut W) * y :=
      fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.mp hg ⟨y, hy⟩)
    have hgt : t * (g : MulAut W) * t⁻¹ = (g : MulAut W) := hcen _ g.2 hgc
    have hconj : MulAut.conj t (g : MulAut W) = (g : MulAut W) := by
      rw [MulAut.conj_apply, hgt]
    calc t * (g : MulAut W) ^ (orderOf (g : MulAut W) / p) * t⁻¹
        = MulAut.conj t ((g : MulAut W) ^ (orderOf (g : MulAut W) / p)) :=
          (MulAut.conj_apply t _).symm
      _ = (MulAut.conj t (g : MulAut W)) ^ (orderOf (g : MulAut W) / p) :=
          map_pow (MulAut.conj t) _ _
      _ = (g : MulAut W) ^ (orderOf (g : MulAut W) / p) := by rw [hconj]

theorem card_eq_prime_step {p : ℕ} {t : MulAut W} {P : Subgroup (MulAut W)} (h : InvCfg131 p t P)
    (ih : ∀ (W' : Type) [CommGroup W'] [Finite W'] (t' : MulAut W')
      (P' : Subgroup (MulAut W')), Nat.card W' < Nat.card W → InvCfg131 p t' P' →
        Nat.card P' = p) : Nat.card P = p := by
  classical
  by_cases hα : ∃ z ∈ P, orderOf z = p ∧ (∀ y ∈ P, y * z = z * y) ∧ t * z * t⁻¹ = z⁻¹
  · obtain ⟨z, hzP, hz, hzc, hzi⟩ := hα
    exact card_eq_prime_of_central_inverted h hzP hz hzc hzi
  · have hcen : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z :=
      fun z hzP hzc => w16g_central_conj_eq_self h hα hzP hzc
    obtain ⟨z₀, hz₀P, hz₀ord, hz₀c, hz₀t⟩ := w16g_exists_central_prime_order h hcen
    set Z₀ : Subgroup (MulAut W) := Subgroup.zpowers z₀ with hZ₀def
    have hZ₀P : Z₀ ≤ P := by
      rw [hZ₀def]
      exact Subgroup.zpowers_le.mpr hz₀P
    have hZ₀c : ∀ z ∈ Z₀, ∀ y ∈ P, y * z = z * y := by
      intro z hz y hy
      rw [hZ₀def] at hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcomm : Commute y z₀ := (commute_iff_eq y z₀).mpr (hz₀c y hy)
      exact (hcomm.zpow_right k).eq
    have hZ₀ : IsElemAbelianOfRank p 1 ↥Z₀ := by
      rw [hZ₀def]
      exact w16g_isElemAbelianOfRank_one_of_card h.hp (by rw [Nat.card_zpowers, hz₀ord])
    have hZ₀t : ∀ z ∈ Z₀, t * z * t⁻¹ = z := by
      intro z hz
      rw [hZ₀def] at hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hconj : MulAut.conj t z₀ = z₀ := by rw [MulAut.conj_apply, hz₀t]
      calc t * z₀ ^ k * t⁻¹ = MulAut.conj t (z₀ ^ k) := (MulAut.conj_apply t _).symm
        _ = (MulAut.conj t z₀) ^ k := map_zpow (MulAut.conj t) _ _
        _ = z₀ ^ k := by rw [hconj]
    by_cases hβ : ∃ Z : Subgroup (MulAut W), Z ≤ P ∧ (∀ z ∈ Z, ∀ y ∈ P, y * z = z * y) ∧
        IsElemAbelianOfRank p 1 ↥Z ∧ commSub (commSub ⊤ Z) (Subgroup.zpowers t) = ⊥
    · obtain ⟨Z, hZP, hZc, hZ, h0⟩ := hβ
      exact card_eq_prime_of_central_comm_eq_bot h ih hZP hZc hZ
        (fun z hz => hcen z (hZP hz) (hZc z hz)) h0
    · have hS : commSub (commSub ⊤ Z₀) (Subgroup.zpowers t) ≠ ⊥ := by
        intro hbot
        exact hβ ⟨Z₀, hZ₀P, hZ₀c, hZ₀, hbot⟩
      have hp7 : p = 7 := eq_seven_of_central_comm_ne_bot h hZ₀P hZ₀c hZ₀ hZ₀t hS
      rw [hp7] at h
      exfalso
      have hnab : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        have hcent : P ≤ Subgroup.centralizer (Subgroup.zpowers t) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
          have htx : t * x * t⁻¹ = x := hcen x hx (fun y hy => (hcon x hx y hy).symm)
          have hcomm : Commute t x := by
            rw [commute_iff_eq]
            calc t * x = t * x * t⁻¹ * t := by group
              _ = x * t := by rw [htx]
          rw [← hk]
          exact (hcomm.zpow_left k).eq
        have hbot : ⁅P, Subgroup.zpowers t⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
        rw [h.hc] at hbot
        exact h.hne hbot
      exact false_of_nonabelian_seven h hnab hcen

theorem card_eq_prime_aux (p : ℕ) (n : ℕ) :
    ∀ (W : Type) [CommGroup W] [Finite W] (t : MulAut W) (P : Subgroup (MulAut W)),
      Nat.card W ≤ n → InvCfg131 p t P → Nat.card P = p := by
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro W _ _ t P hn h
    exact card_eq_prime_step h
      (fun W' _ _ t' P' hlt h' => ihn (Nat.card W') (lt_of_lt_of_le hlt hn) W' t' P' le_rfl h')

theorem card_eq_prime_of_comm_eq_self (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {p : ℕ}
    (hp : p.Prime) {P : Subgroup (MulAut W)} (hP : IsPGroup p ↥P) (hne : P ≠ ⊥)
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P)
    (hgood : 3 < p ∨ InducesTransvection t ⊤) : Nat.card P = p :=
  card_eq_prime_aux p (Nat.card W) W t P le_rfl ⟨hW, ht, hrk, hp, hP, hne, hn, hc, hgood⟩

theorem w4Lem13_1_holds : W4Lem13_1 := by
  intro W _ _ hW t ht hrk p P hp hP hne hn hc
  exact ⟨le_seven_of_comm_eq_self hW ht hrk hp hP hne hn hc,
    fun hgood => card_eq_prime_of_comm_eq_self hW ht hrk hp hP hne hn hc hgood⟩

end CFSG.LocalAnalysis.WeakClosure81
