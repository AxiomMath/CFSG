module

public import CFSG.Quasithin.EmptyFaithful.T1521SU3Zc

public section

namespace CFSG.Quasithin.U31521

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Goldschmidt
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open CFSG.ProperTwoGeneratedCore.RootCenter CFSG.ComponentClassification.AschbacherToolkit

variable {X : Type} [Group X]

theorem conj_mem_sup_aux {H K : Subgroup X} {g : X} (hH : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hK : ∀ k ∈ K, g * k * g⁻¹ ∈ K) {x : X} (hx : x ∈ H ⊔ K) : g * x * g⁻¹ ∈ H ⊔ K := by
  have h1 : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    exact hH h hh
  have h2 : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact hK k hk
  have h3 := sup_le_sup h1 h2
  rw [← Subgroup.map_sup] at h3
  exact h3 ⟨x, hx, rfl⟩

section CentralizerOne

variable [Finite X]

theorem centralizer_eq_one_of_not_centralizes {T : Sylow 2 X} {D : Subgroup X}
    (hD : G3a.BorelSetup T D)
    (hcase : (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 2 ∧
        Nat.card D = Nat.card (sylowCenter (T : Subgroup X)) - 1) ∨
      (Nat.card (T : Subgroup X) = Nat.card (sylowCenter (T : Subgroup X)) ^ 3 ∧
        Nat.card D = (Nat.card (sylowCenter (T : Subgroup X)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (sylowCenter (T : Subgroup X)) + 1)))
    {w : X} (hw : w ∈ D) {z₀ : X} (hz₀ : z₀ ∈ sylowCenter (T : Subgroup X))
    (hnc : w * z₀ ≠ z₀ * w) : ∀ c ∈ (T : Subgroup X), w * c = c * w → c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := sylowCenter (T : Subgroup X) with hZ
  set C : Subgroup X := (T : Subgroup X) ⊓ Subgroup.centralizer ({w} : Set X) with hC
  have hCmem : ∀ c, c ∈ C ↔ c ∈ (T : Subgroup X) ∧ w * c = c * w := by
    intro c
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
  have hCZ : ∀ u ∈ Z, u ∈ C → u = 1 := by
    intro u huZ huC
    by_contra hu1
    have hcen := hD.mem_centralizer_center hw huZ hu1 ((hCmem u).1 huC).2
    exact hnc (Subgroup.mem_centralizer_iff.mp hcen z₀ hz₀).symm
  have hZle : Z ≤ (T : Subgroup X) := sylowCenter_le _
  have hCle : C ≤ (T : Subgroup X) := inf_le_left
  have hYle : C ⊔ Z ≤ (T : Subgroup X) := sup_le hCle hZle
  have hDY : D ≤ Subgroup.normalizer ((C ⊔ Z : Subgroup X) : Set X) := by
    intro δ hδ
    apply A4.mem_normalizer_of_conj_mem
    intro x hx
    refine conj_mem_sup_aux (fun c hc => ?_) (fun z hz => hD.conj_mem_center hδ hz) hx
    obtain ⟨hcT, hcw⟩ := (hCmem c).1 hc
    refine (hCmem _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hD.le hδ) c).mp hcT, ?_⟩
    have hcomm : Commute w δ := hD.comm hw hδ
    have hcomm' : w * δ⁻¹ = δ⁻¹ * w := hcomm.inv_right.eq
    calc w * (δ * c * δ⁻¹) = (w * δ) * c * δ⁻¹ := by group
      _ = δ * (w * c) * δ⁻¹ := by rw [hcomm.eq]; group
      _ = δ * (c * w) * δ⁻¹ := by rw [hcw]
      _ = δ * c * (w * δ⁻¹) := by group
      _ = δ * c * (δ⁻¹ * w) := by rw [hcomm']
      _ = (δ * c * δ⁻¹) * w := by group
  have hCbot : ∀ c ∈ C, c = 1 := by
    rcases hD.eq_or_eq_of_invariant hcase le_sup_right hYle hDY with hY | hY
    · intro c hc
      have hCZ' : C ≤ Z := le_sup_left.trans hY.le
      exact hCZ c (hCZ' hc) hc
    · by_contra hcon
      push Not at hcon
      obtain ⟨c₁, hc₁, hc₁1⟩ := hcon
      have hCp : IsPGroup 2 C := T.isPGroup'.to_le hCle
      have : Nontrivial ↥C := ⟨⟨⟨c₁, hc₁⟩, 1, fun h => hc₁1 (congrArg Subtype.val h)⟩⟩
      have hnt := hCp.center_nontrivial
      obtain ⟨z', hz'⟩ := exists_ne (1 : ↥(Subgroup.center ↥C))
      have hz'C : ((z' : ↥C) : X) ∈ C := (z' : ↥C).2
      have hzcomm : ∀ y ∈ C, ((z' : ↥C) : X) * y = y * ((z' : ↥C) : X) := fun y hy => by
        have := Subgroup.mem_center_iff.mp z'.2 ⟨y, hy⟩
        exact (congrArg Subtype.val this).symm
      have hle : C ⊔ Z ≤ Subgroup.centralizer ({((z' : ↥C) : X)} : Set X) := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hzcomm y hy).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact ((mem_sylowCenter.mp hy).2 _ (hCle hz'C)).symm
      have hzZ : ((z' : ↥C) : X) ∈ Z := by
        refine mem_sylowCenter.mpr ⟨hCle hz'C, fun t ht => ?_⟩
        have ht' : t ∈ C ⊔ Z := by
          rw [hY]
          exact ht
        exact Subgroup.mem_centralizer_singleton_iff.mp (hle ht')
      have h1 := hCZ _ hzZ hz'C
      exact hz' (Subtype.ext (Subtype.ext h1))
  intro c hc hwc
  exact hCbot c ((hCmem c).2 ⟨hc, hwc⟩)

end CentralizerOne

structure GoodElt (R : Subgroup X) (β : MulAut X) (r w : X) : Prop where
  r_mem : r ∈ R
  w_norm : w ∈ Subgroup.normalizer (R : Set X)
  w_odd : Odd (orderOf w)
  fix : ((MulAut.conj r)⁻¹ * β) w = w
  centr : ∀ c ∈ R, w * c = c * w → c = 1
  surj : ∀ c ∈ R, ∃ s ∈ R, s⁻¹ * w * s * w⁻¹ = c

section Good

variable [Finite X]

theorem exists_goodElt {n : ℕ} (hn : 2 ≤ n) (hX : IsPSU 3 2 n X)
    (R : Sylow 2 X) {β : MulAut X} (hβ : β ∈ autStab (R : Subgroup X)) (hβ2 : β ^ 2 = 1) :
    ∃ r w : X, GoodElt (R : Subgroup X) β r w := by
  obtain ⟨e⟩ := nonempty_equiv_psu3_of_isPSU hn hX
  obtain ⟨D, hD⟩ := G3a.exists_borelSetup (bender_of_isPSU hn hX) R
  obtain ⟨hZc, hTc, hDc⟩ := hD.orders_psu3 hn e
  have hcase : (Nat.card (R : Subgroup X) = Nat.card (sylowCenter (R : Subgroup X)) ^ 2 ∧
        Nat.card D = Nat.card (sylowCenter (R : Subgroup X)) - 1) ∨
      (Nat.card (R : Subgroup X) = Nat.card (sylowCenter (R : Subgroup X)) ^ 3 ∧
        Nat.card D = (Nat.card (sylowCenter (R : Subgroup X)) ^ 2 - 1) /
          Nat.gcd 3 (Nat.card (sylowCenter (R : Subgroup X)) + 1)) := by
    right
    rw [hZc, hTc, hDc]
    exact ⟨rfl, rfl⟩
  obtain ⟨T', hT'ne, hDT'⟩ := hD.exists_fixed
  have hDeq := hD.normalizer_inf_eq hT'ne hDT'
  have hβS : β • R = R := Bender.Omega.smul_eq_of_mapsTo (fun s hs => (mem_autStab.mp hβ s).2 hs)
  obtain ⟨r, hr, hrT'⟩ := Bender.Omega.exists_conj_adjust hD.se hD.card hT'ne β hβS
  set β' : MulAut X := (MulAut.conj r)⁻¹ * β with hβ'
  have hβ'R : β' • R = R := by
    rw [hβ', mul_smul, hβS, inv_smul_eq_iff, Bender.Omega.conj_smul_self hr]
  have hβ'stab : β' ∈ autStab (R : Subgroup X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (conj_mem_autStab hr)) hβ
  have hβ'D : ∀ d ∈ D, β' d ∈ D := by
    intro d hd
    rw [← hDeq] at hd ⊢
    have h1 := Bender.Omega.mem_normalizer_smul (α := β') hd.1
    have h2 := Bender.Omega.mem_normalizer_smul (α := β') hd.2
    rw [hβ'R] at h1
    rw [hrT'] at h2
    exact ⟨h1, h2⟩
  have hβ'2 : β' ^ 2 = 1 := by
    set y : X := (β r * r)⁻¹ with hy
    have hc : β * MulAut.conj r * β⁻¹ = MulAut.conj (β r) := mul_conj_mul_inv β r
    have hc' : β * (MulAut.conj r)⁻¹ * β⁻¹ = (MulAut.conj (β r))⁻¹ := by
      rw [← hc]
      group
    have hb2 : β * β = 1 := by rw [← pow_two]; exact hβ2
    have h1 : β' ^ 2 = MulAut.conj y := by
      calc β' ^ 2 = (MulAut.conj r)⁻¹ * (β * (MulAut.conj r)⁻¹ * β⁻¹) * (β * β) := by
            rw [hβ', pow_two]
            group
        _ = (MulAut.conj r)⁻¹ * (MulAut.conj (β r))⁻¹ := by rw [hc', hb2, mul_one]
        _ = MulAut.conj y := by
            rw [hy, map_inv, map_mul, mul_inv_rev]
    have hyR : y ∈ (R : Subgroup X) :=
      (R : Subgroup X).inv_mem ((R : Subgroup X).mul_mem ((mem_autStab.mp hβ r).2 hr) hr)
    have hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
      intro d hd
      have := hβ'D _ (hβ'D d hd)
      rw [← MulAut.mul_apply, ← pow_two, h1, MulAut.conj_apply] at this
      exact this
    have hyc : ∀ d ∈ D, d * y = y * d := by
      intro d hd
      have h2 : y * d * y⁻¹ * d⁻¹ ∈ D := D.mul_mem (hyD d hd) (D.inv_mem hd)
      have h3 : y * (d * y⁻¹ * d⁻¹) ∈ (R : Subgroup X) :=
        (R : Subgroup X).mul_mem hyR ((Subgroup.mem_normalizer_iff.mp (hD.le hd) y⁻¹).mp
          ((R : Subgroup X).inv_mem hyR))
      have h4 : y * d * y⁻¹ * d⁻¹ = y * (d * y⁻¹ * d⁻¹) := by group
      have h5 : y * d * y⁻¹ * d⁻¹ ∈ (R : Subgroup X) ⊓ D := ⟨h4 ▸ h3, h2⟩
      rw [hD.inf, Subgroup.mem_bot] at h5
      have : y * d = d * y := by
        have h6 : y * d * y⁻¹ = d := by
          calc y * d * y⁻¹ = (y * d * y⁻¹ * d⁻¹) * d := by group
            _ = d := by rw [h5, one_mul]
        calc y * d = (y * d * y⁻¹) * y := by group
          _ = d * y := by rw [h6]
      exact this.symm
    have hy1 : y = 1 := hD.eq_one_of_commute hyR hyc
    rw [h1, hy1, map_one]
  have hβ'Z : ∀ u ∈ sylowCenter (R : Subgroup X), β' u = u := fun u hu =>
    centralizes_center_of_sq_eq_one hn hX R hβ'stab hβ'2 (mem_sylowCenter.mp hu).1
      (fun y hy => ((mem_sylowCenter.mp hu).2 y hy).symm)
  obtain ⟨z₀, hz₀, hz₀1, -⟩ := hD.exists_ne 1
  obtain ⟨w₁, hw₁, hw₁1, hw₁z⟩ := hD.exists_ne z₀
  obtain ⟨x, hxD, hxz⟩ := hD.trans hz₀ hw₁ hz₀1 hw₁1
  have hxnc : x * z₀ ≠ z₀ * x := by
    intro h
    apply hw₁z
    rw [← hxz]
    calc x⁻¹ * z₀ * x = x⁻¹ * (z₀ * x) := by group
      _ = x⁻¹ * (x * z₀) := by rw [h]
      _ = z₀ := by group
  have hxodd : Odd (orderOf x) := by
    exact hD.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hxD)
  set w : X := x * β' x with hw
  have hwD : w ∈ D := D.mul_mem hxD (hβ'D x hxD)
  have hwfix : β' w = w := by
    rw [hw, map_mul, show β' (β' x) = x from by
      rw [← MulAut.mul_apply, ← pow_two, hβ'2, MulAut.one_apply]]
    exact (hD.comm (hβ'D x hxD) hxD)
  have hwnc : w * z₀ ≠ z₀ * w := by
    intro hwz
    have h1 : (β' x) * z₀ * (β' x)⁻¹ = x * z₀ * x⁻¹ := by
      have hxz' : x * z₀ * x⁻¹ ∈ sylowCenter (R : Subgroup X) := hD.conj_mem_center hxD hz₀
      have := hβ'Z _ hxz'
      rw [map_mul, map_mul, hβ'Z z₀ hz₀, map_inv] at this
      exact this
    have h3 : w * z₀ * w⁻¹ = (x * x) * z₀ * (x * x)⁻¹ := by
      calc w * z₀ * w⁻¹ = x * ((β' x) * z₀ * (β' x)⁻¹) * x⁻¹ := by rw [hw]; group
        _ = x * (x * z₀ * x⁻¹) * x⁻¹ := by rw [h1]
        _ = (x * x) * z₀ * (x * x)⁻¹ := by group
    have h4 : w * z₀ * w⁻¹ = z₀ := by rw [hwz]; group
    rw [h3] at h4
    have hcomm : Commute (x * x) z₀ := by
      have : (x * x) * z₀ = z₀ * (x * x) := by
        calc (x * x) * z₀ = ((x * x) * z₀ * (x * x)⁻¹) * (x * x) := by group
          _ = z₀ * (x * x) := by rw [h4]
      exact this
    obtain ⟨k, hk⟩ := hxodd
    have hxpow : x = (x * x) ^ (k + 1) := by
      have h5 : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
      have h6 : x ^ (2 * (k + 1)) = x := by
        have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
        rw [this, pow_succ, h5, one_mul]
      rw [← sq, ← pow_mul]
      exact h6.symm
    apply hxnc
    have : Commute x z₀ := by
      rw [hxpow]
      exact hcomm.pow_left (k + 1)
    exact this
  have hwcentr := centralizer_eq_one_of_not_centralizes hD hcase hwD hz₀ hwnc
  have hwodd : Odd (orderOf w) :=
    hD.odd.of_dvd_nat (Subgroup.orderOf_dvd_natCard D hwD)
  exact ⟨r, w, ⟨hr, hD.le hwD, hwodd, hwfix, hwcentr, fun c hc =>
    G3a.BorelSetup.exists_eq_commutator (T := R) (hD.le hwD) hwcentr hc⟩⟩

end Good

end CFSG.Quasithin.U31521
