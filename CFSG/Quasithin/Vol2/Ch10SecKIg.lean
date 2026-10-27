module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B4L3Inv
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10KH

open CFSG.Open CFSG.Quasithin

section Sections

variable {V : Type} [CommGroup V] {Y : Type} [Group Y]

theorem mul_self_mem_centSec (hV : ∀ v : V, v ^ 2 = 1) {W J U : Subgroup V} {n : MulAut V}
    (h1 : n ∈ centSec W J) (h2 : n ∈ centSec J U) : n * n ∈ centSec W U := by
  refine ⟨(stabSub W).mul_mem h1.1 h1.1, fun w hw => ?_⟩
  set j := n w * w⁻¹ with hj
  have hjU : n j * j⁻¹ ∈ U := h2.2 j (h1.2 w hw)
  have hnw : n w = j * w := by rw [hj, inv_mul_cancel_right]
  have hjj : j⁻¹ = j := by
    have := hV j
    rw [pow_two] at this
    exact inv_eq_of_mul_eq_one_right this
  have he : (n * n) w * w⁻¹ = n j * j⁻¹ := by
    rw [MulAut.mul_apply, hnw, map_mul, hnw, mul_assoc, mul_inv_cancel_right, hjj]
  rw [he]
  exact hjU

theorem comap_centSec_normal (ρ : Y →* MulAut V) {W U : Subgroup V} (hW : ρ.range ≤ stabSub W)
    (hU : ρ.range ≤ stabSub U) : ((centSec W U).comap ρ).Normal := by
  refine ⟨fun k hk y => ?_⟩
  show ρ (y * k * y⁻¹) ∈ centSec W U
  rw [map_mul, map_mul, map_inv]
  exact conj_mem_centSec (hW ⟨y, rfl⟩) (hU ⟨y, rfl⟩) hk

omit [CommGroup V] in
theorem le_stabSub_of_invariant [CommGroup V] {X : Subgroup (MulAut V)} {J : Subgroup V}
    (hJ : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J) : X ≤ stabSub J := by
  intro x hx u
  refine ⟨fun h => ?_, hJ x hx u⟩
  have := hJ x⁻¹ (X.inv_mem hx) _ h
  simpa using this

theorem eq_one_of_mem_centSec_top_bot {g : MulAut V} (hg : g ∈ centSec ⊤ ⊥) : g = 1 := by
  refine MulEquiv.ext fun w => ?_
  have := Subgroup.mem_bot.1 (hg.2 w trivial)
  exact mul_inv_eq_one.1 this

variable [Finite V]

theorem exists_irr_section (hV : ∀ v : V, v ^ 2 = 1) (ρ : Y →* MulAut V) (N : Subgroup Y)
    (hQ : ∀ K : Subgroup Y, K.Normal → (∀ n ∈ N, n * n ∈ K) → N ≤ K) (hN : ¬ N ≤ ρ.ker) :
    ∃ W U : Subgroup V, U < W ∧ ρ.range ≤ stabSub W ∧ ρ.range ≤ stabSub U ∧
      (∀ J : Subgroup V, (∀ x ∈ ρ.range, ∀ w ∈ J, x w ∈ J) → U ≤ J → J ≤ W →
        J = U ∨ J = W) ∧ ¬ N ≤ (centSec W U).comap ρ := by
  have key : ∀ k : ℕ, ∀ W U : Subgroup V, Nat.card W - Nat.card U ≤ k → U ≤ W →
      ρ.range ≤ stabSub W → ρ.range ≤ stabSub U → ¬ N ≤ (centSec W U).comap ρ →
      ∃ W U : Subgroup V, U < W ∧ ρ.range ≤ stabSub W ∧ ρ.range ≤ stabSub U ∧
        (∀ J : Subgroup V, (∀ x ∈ ρ.range, ∀ w ∈ J, x w ∈ J) → U ≤ J → J ≤ W →
          J = U ∨ J = W) ∧ ¬ N ≤ (centSec W U).comap ρ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro W U hk hUW hW hU hNWU
      have hne : U ≠ W := by
        rintro rfl
        exact hNWU fun n _ =>
          ⟨hU ⟨n, rfl⟩, fun w hw => U.mul_mem ((hU ⟨n, rfl⟩ w).2 hw) (U.inv_mem hw)⟩
      by_cases hirr : ∀ J : Subgroup V, (∀ x ∈ ρ.range, ∀ w ∈ J, x w ∈ J) → U ≤ J → J ≤ W →
          J = U ∨ J = W
      · exact ⟨W, U, lt_of_le_of_ne hUW hne, hW, hU, hirr, hNWU⟩
      · push Not at hirr
        obtain ⟨J, hJ, hUJ, hJW, hJU, hJW'⟩ := hirr
        have hJs : ρ.range ≤ stabSub J := le_stabSub_of_invariant hJ
        have hcU : Nat.card U < Nat.card J :=
          Subgroup.card_lt_of_lt (lt_of_le_of_ne hUJ (Ne.symm hJU))
        have hcW : Nat.card J < Nat.card W := Subgroup.card_lt_of_lt (lt_of_le_of_ne hJW hJW')
        by_cases h1 : N ≤ (centSec W J).comap ρ
        · by_cases h2 : N ≤ (centSec J U).comap ρ
          · refine absurd (hQ _ (comap_centSec_normal ρ hW hU) fun n hn => ?_) hNWU
            show ρ (n * n) ∈ centSec W U
            rw [map_mul]
            exact mul_self_mem_centSec hV (h1 hn) (h2 hn)
          · exact ih (Nat.card J - Nat.card U) (by omega) J U le_rfl hUJ hJs hU h2
        · exact ih (Nat.card W - Nat.card J) (by omega) W J le_rfl hJW hW hJs h1
  refine key _ ⊤ ⊥ le_rfl bot_le (fun x _ u => ⟨fun _ => trivial, fun _ => trivial⟩)
    (fun x _ u => ?_) fun hle => hN fun n hn => ?_
  · simp only [Subgroup.mem_bot]
    exact map_eq_one_iff x x.injective
  · exact MonoidHom.mem_ker.2 (eq_one_of_mem_centSec_top_bot (hle hn))

end Sections

theorem eq_bot_or_eq_of_le_three {Y : Type} [Group Y] [Finite Y] {Z K : Subgroup Y}
    (hZ : Nat.card Z = 3) (hKZ : K ≤ Z) : K = ⊥ ∨ K = Z := by
  have hd : Nat.card K ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hKZ
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · exact Or.inl (Subgroup.eq_bot_of_card_eq K h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hKZ (by rw [h3, hZ]))

theorem eq_mul_self_mul_of_three {Y : Type} [Group Y] {Z : Subgroup Y} (hZ : Nat.card Z = 3)
    {n : Y} (hn : n ∈ Z) : n = n * n * (n * n) := by
  have h := pow_card_eq_one' (G := ↥Z) (x := ⟨n, hn⟩)
  rw [hZ] at h
  have h3 : n ^ 3 = 1 := by simpa using congrArg Subtype.val h
  calc n = n ^ 3 * n := by rw [h3, one_mul]
    _ = n * n * (n * n) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem mul_comm_of_mul_self {Y : Type} [Group Y] (hsq : ∀ y : Y, y * y = 1) (a c : Y) :
    a * c = c * a := by
  have hinv : ∀ y : Y, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (hsq y)
  calc a * c = (a * c)⁻¹ := (hinv _).symm
    _ = c⁻¹ * a⁻¹ := mul_inv_rev a c
    _ = c * a := by rw [hinv, hinv]

section Induced

variable {V : Type} [CommGroup V] [Finite V] {Y : Type} [Group Y] {ρ : Y →* MulAut V}
  {W U : Subgroup V}

theorem quasithinGenFitting_eq_self {Ω : Type*} [Group Ω] {X : Subgroup Ω}
    (hq : CFSG.IsQuasisimple ↥X) : quasithinGenFitting X = X :=
  le_antisymm (quasithinGenFitting_le X)
    (le_sup_of_le_right (le_sSup ⟨le_rfl, IsSubnormal.refl X, B1Red.isQuasisimple_to_open hq⟩))

omit [Finite V] in
theorem sec_sq (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) : ∀ v : Sec W U, v ^ 2 = 1 := by
  intro v
  induction v using QuotientGroup.induction_on with
  | H w =>
    rw [← QuotientGroup.mk_pow, show w ^ 2 = 1 from Subtype.ext (by simpa using hV w),
      QuotientGroup.mk_one]

theorem b4Hyp_autSec (hUW : U < W) (hXW : ρ.range ≤ stabSub W) (hXU : ρ.range ≤ stabSub U)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ ρ.range, ∀ w ∈ J, x w ∈ J) → U ≤ J → J ≤ W →
      J = U ∨ J = W)
    (hfaith : ρ.range ⊓ centSec W U = ⊥) (hS : SQTKGroup ↥ρ.range)
    (hq : CFSG.IsQuasisimple ↥ρ.range) :
    B4Hyp (autSec ρ.range W U) (autSec ρ.range W U) :=
  ⟨B5.sqtk_autSec hXW hXU hfaith hS,
    (B5.genFitting_autSec le_rfl hXW hXU hfaith (quasithinGenFitting_eq_self hq)).symm,
    B5.isQuasisimple_autSec hXW hXU hfaith hq, B5.isIrrSec_autSec hUW hirr hXW hXU⟩

omit [Finite V] in
theorem commV_secHom_le {X : Subgroup (MulAut V)} (hXW : X ≤ stabSub W) (hXU : X ≤ stabSub U)
    (g : ↥X) :
    commV (Subgroup.zpowers (B5.secHom X hXW hXU g)) ≤
      ((commV (Subgroup.zpowers (g : MulAut V))).subgroupOf W).map
        (QuotientGroup.mk' (U.subgroupOf W)) := by
  rw [G6.commV_le_iff]
  intro x hx v
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← map_zpow, B5.secHom_mk]
  have hmem : ((g ^ k : ↥X) : MulAut V) ∈ Subgroup.zpowers (g : MulAut V) := by
    rw [Subgroup.coe_zpow]
    exact zpow_mem (Subgroup.mem_zpowers _) k
  refine ⟨⟨((g ^ k : ↥X) : MulAut V) (w : V), (hXW (g ^ k).2 w).2 w.2⟩ * w⁻¹, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 (G6.mem_commV_of_mem hmem (w : V))

theorem qhatOf_autSec_le (hV : ∀ v : V, v ^ 2 = 1) (hXW : ρ.range ≤ stabSub W)
    (hXU : ρ.range ≤ stabSub U) (hfaith : ρ.range ⊓ centSec W U = ⊥) {b : Y} (hb2 : b ^ 2 = 1)
    (hb1 : ρ b ≠ 1) (hc : Nat.card ↥(commV (Subgroup.zpowers (ρ b))) ≤ 4) :
    qhatOf (autSec ρ.range W U) ≤ ((2 : ℚ) : WithTop ℚ) := by
  set X := ρ.range with hXdef
  set g : ↥X := ⟨ρ b, b, rfl⟩ with hg
  set σ := B5.secHom X hXW hXU g with hσ
  have hσG : σ ∈ autSec X W U := by
    rw [← B5.range_secHom X hXW hXU]
    exact ⟨g, rfl⟩
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσ, ← map_pow]
    have : g ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; simp [g, ← map_pow, hb2])
    rw [this, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hk : g ∈ (B5.secHom X hXW hXU).ker := h
    rw [B5.ker_secHom_eq_bot X hXW hXU hfaith, Subgroup.mem_bot] at hk
    exact hb1 (congrArg Subtype.val hk)
  have hV' := sec_sq hV W U
  set A := Subgroup.zpowers σ with hA
  have hcardA : Nat.card ↥A = 2 := by
    rw [hA, Nat.card_zpowers]
    exact orderOf_eq_prime hσ2 hσ1
  have hA2 : IsA2 (autSec X W U) A := by
    refine ⟨(Subgroup.zpowers_le).2 hσG, Subgroup.zpowers_ne_bot.2 hσ1, ?_, fun a ha => ?_⟩
    · intro a ha c hc'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact zpow_mul_comm σ i j
    · have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
      rw [hcardA] at h
      simpa using congrArg Subtype.val h
  have hquad : commSeries A 3 = ⊥ :=
    commSeries_eq_bot_of_le (k := 2) (by norm_num)
      ((isQuadratic_iff_commSeries_two A).1 (isQuadratic_zpowers hV' hσ2))
  have hcomm : Nat.card ↥(commV A) ≤ 4 := by
    set C := (commV (Subgroup.zpowers (ρ b))).subgroupOf W with hC
    have h1 := commV_secHom_le hXW hXU g
    calc Nat.card ↥(commV A) ≤ Nat.card ↥(C.map (QuotientGroup.mk' (U.subgroupOf W))) :=
          Subgroup.card_le_of_le h1
      _ ≤ Nat.card ↥C := Nat.card_le_card_of_surjective _
          ((QuotientGroup.mk' (U.subgroupOf W)).subgroupMap_surjective C)
      _ ≤ Nat.card ↥(commV (Subgroup.zpowers (ρ b))) :=
          Nat.card_le_card_of_injective (fun x => (⟨x.1.1, x.2⟩ : ↥(commV _))) fun x y hxy => by
            have h := congrArg Subtype.val hxy
            exact Subtype.ext (Subtype.ext h)
      _ ≤ 4 := hc
  have hr : rAV A ≤ 2 := by
    rw [rAV_le_two_iff hV' hA2, hcardA, ← card_commV_mul_card_fixV hV' σ]
    calc Nat.card ↥(commV A) * Nat.card ↥(fixV A) ≤ 4 * Nat.card ↥(fixV A) :=
          Nat.mul_le_mul_right _ hcomm
      _ = 2 ^ 2 * Nat.card ↥(fixV A) := by norm_num
  show kq (autSec X W U) 3 ≤ ((2 : ℚ) : WithTop ℚ)
  exact kq_le_iff.2 ⟨A, hA2, hquad, hr⟩

end Induced

end CFSG.Quasithin.Vol2.Ch10.SecF.C10KH
