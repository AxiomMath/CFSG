module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.ActionTI
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.InvSets
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

section
variable {Y Γ : Type*} [Group Y] [Finite Y] [Group Γ]

structure LiftData (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (P : Subgroup Y)
    (θ : Y → Γ) (Lift : Γ → Y → Prop) : Prop where
  hom : ∀ x ∈ P, ∀ y ∈ P, θ (x * y) = θ x * θ y
  faithful : ∀ x ∈ P, (∀ a : A, θ x • a = a) → x = 1
  conj : ∀ w e, Lift w e → ∀ p ∈ P, w * θ p * w⁻¹ = θ (e * p * e⁻¹)
  move : ∀ w e, Lift w e → ∀ p ∈ P, Lift (θ p * w * (θ p)⁻¹) (p * e * p⁻¹)
  ti : ∀ w e w' e', Lift w e → Lift w' e' → e ≠ e' → TIPair (A := A) w w'

variable {A : Type*} [AddCommGroup A] [DistribMulAction Γ A] {P : Subgroup Y} {θ : Y → Γ}
  {Lift : Γ → Y → Prop}

namespace LiftData

theorem map_one (hL : LiftData A P θ Lift) : θ 1 = 1 := by
  have h := hL.hom 1 P.one_mem 1 P.one_mem
  rw [one_mul] at h
  calc θ 1 = (θ 1)⁻¹ * (θ 1 * θ 1) := by group
    _ = 1 := by rw [← h, inv_mul_cancel]

theorem map_inv (hL : LiftData A P θ Lift) {x : Y} (hx : x ∈ P) : θ x⁻¹ = (θ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hL.hom _ (P.inv_mem hx) _ hx, inv_mul_cancel, hL.map_one]

theorem map_pow (hL : LiftData A P θ Lift) {x : Y} (hx : x ∈ P) (n : ℕ) : θ (x ^ n) = θ x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, hL.map_one]
  | succ n ih => rw [pow_succ, hL.hom _ (P.pow_mem hx n) _ hx, ih, pow_succ]

theorem odd_orderOf (hL : LiftData A P θ Lift) (hPodd : Odd (Nat.card P)) {x : Y} (hx : x ∈ P) :
    Odd (orderOf (θ x)) := by
  have h1 : θ x ^ orderOf x = 1 := by rw [← hL.map_pow hx, pow_orderOf_eq_one, hL.map_one]
  exact Odd.of_dvd_nat (Odd.of_dvd_nat hPodd (Subgroup.orderOf_dvd_natCard P hx))
    (orderOf_dvd_of_pow_eq_one h1)

theorem map_comm (hL : LiftData A P θ Lift) {x y : Y} (hx : x ∈ P) (hy : y ∈ P) :
    θ (x * y * x⁻¹ * y⁻¹) = θ x * θ y * (θ x)⁻¹ * (θ y)⁻¹ := by
  rw [hL.hom _ (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) _ (P.inv_mem hy),
    hL.hom _ (P.mul_mem hx hy) _ (P.inv_mem hx), hL.hom _ hx _ hy, hL.map_inv hx, hL.map_inv hy]

theorem commute_of_commute (hL : LiftData A P θ Lift) {x y : Y} (hx : x ∈ P) (hy : y ∈ P)
    (h : x * y = y * x) : θ x * θ y = θ y * θ x := by
  rw [← hL.hom _ hx _ hy, h, hL.hom _ hy _ hx]

theorem inv_of_mem (hL : LiftData A P θ Lift) {e : Fin 3 → Y} {w : Γ} {i : Fin 3}
    (hw : Lift w (e i)) {x : Y} (hx : x ∈ InvSet P e i) : w * θ x * w⁻¹ = (θ x)⁻¹ := by
  rw [hL.conj _ _ hw x hx.1, hx.2.1, hL.map_inv hx.1]

theorem comm_of_mem (hL : LiftData A P θ Lift) {e : Fin 3 → Y} {w : Γ} {i j : Fin 3}
    (hij : i ≠ j) (hw : Lift w (e j)) {x : Y} (hx : x ∈ InvSet P e i) : w * θ x = θ x * w := by
  have h := hL.conj _ _ hw x hx.1
  rw [conj_eq_of_comm (hx.2.2 j (Ne.symm hij))] at h
  calc w * θ x = w * θ x * w⁻¹ * w := by group
    _ = θ x * w := by rw [h]

theorem fix_sq (hL : LiftData A P θ Lift) (hPodd : Odd (Nat.card P)) {e : Fin 3 → Y}
    (he : ∀ i, e i * e i = 1) (hec : ∀ i j, e i * e j = e j * e i)
    (hen : ∀ i j, i ≠ j → e i ≠ e j) {w : Fin 3 → Γ} (hw : ∀ i, Lift (w i) (e i))
    (hwc : ∀ i j, w i * w j = w j * w i) {i j : Fin 3} (hij : i ≠ j) {x : Y}
    (hx : x ∈ InvSet P e i) (a : A) : θ x • (w j • a - a) = w j • a - a := by
  have hxP := hx.1
  have hne : x⁻¹ * e i * x⁻¹⁻¹ ≠ e j := by
    intro h
    have hei : (e i)⁻¹ = e i := inv_eq_of_mul_eq_one_right (he i)
    have hprod : e i * e j = x * x := by
      rw [← h, show e i * (x⁻¹ * e i * x⁻¹⁻¹) = (e i * x⁻¹ * (e i)⁻¹) * x by rw [hei]; group,
        show e i * x⁻¹ * (e i)⁻¹ = (e i * x * (e i)⁻¹)⁻¹ by group, hx.2.1, inv_inv]
    have hsq : (e i * e j) * (e i * e j) = 1 := by
      rw [show e i * e j * (e i * e j) = e i * (e j * e i) * e j by group, ← hec i j,
        show e i * (e i * e j) * e j = (e i * e i) * (e j * e j) by group, he i, he j, one_mul]
    have h1 := eq_one_of_sq_of_odd hPodd (by rw [hprod]; exact P.mul_mem hxP hxP) hsq
    exact hen i j hij (by rw [← mul_right_cancel_iff (a := e j), he j, h1])
  have hTI2 : TIPair (A := A) ((θ x)⁻¹ * w i * θ x) (w j) := by
    have hlift := hL.move _ _ (hw i) x⁻¹ (P.inv_mem hxP)
    rw [hL.map_inv hxP, inv_inv] at hlift
    exact hL.ti _ _ _ _ hlift (hw j) hne
  exact fix_of_square (hL.inv_of_mem (hw i) hx) (hwc i j) (hL.comm_of_mem hij (hw j) hx)
    (hL.odd_orderOf hPodd hxP) (hL.ti _ _ _ _ (hw i) (hw j) (hen i j hij)) hTI2 a

theorem fix_fact (hL : LiftData A P θ Lift) (h2 : ∀ a : A, a + a = 0)
    (hPodd : Odd (Nat.card P)) {e : Fin 3 → Y}
    (he : ∀ i, e i * e i = 1) (hec : ∀ i j, e i * e j = e j * e i)
    (hen : ∀ i j, i ≠ j → e i ≠ e j) {w : Fin 3 → Γ} (hw : ∀ i, Lift (w i) (e i))
    (hwc : ∀ i j, w i * w j = w j * w i) {i j : Fin 3} (hij : i ≠ j) {x y : Y}
    (hx : x ∈ InvSet P e i) (hy : y ∈ InvSet P e j) (hxy : x * y = y * x) (a : A) :
    θ y • (θ x • a - a) = θ x • a - a :=
  fix_of_factA h2 (hL.comm_of_mem hij (hw j) hx).symm (hL.commute_of_commute hx.1 hy.1 hxy)
    (hL.inv_of_mem (hw j) hy) (hL.odd_orderOf hPodd hx.1) (hL.odd_orderOf hPodd hy.1)
    (hL.fix_sq hPodd he hec hen hw hwc hij hx) a

theorem comm_of_invSet (hL : LiftData A P θ Lift) (h2 : ∀ a : A, a + a = 0) [hPn : P.Normal]
    {Z₀ : Subgroup Y} (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀) (hPodd : Odd (Nat.card P))
    {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdn : ∀ i j, i ≠ j → d i ≠ d j) {t : Y} (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    {w : Fin 3 → Γ} (hw : ∀ i, Lift (w i) (d i)) (hwc : ∀ i j, w i * w j = w j * w i)
    (i : Fin 3) : ∀ x ∈ InvSet P d i, ∀ y ∈ InvSet P d i, x * y = y * x := by
  intro x hx y hy
  have hji : i + 1 ≠ i := fin3_add1_ne i
  have hx' := conj_mem_invSet_succ ht hx
  have hy' := conj_mem_invSet_succ ht hy
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hζZ : ζ ∈ Z₀ := by rw [hζ]; exact hP' x hx.1 y hy.1
  have hζP : ζ ∈ P := hZP hζZ
  have hζc := mem_center_iff.mp (hZc hζZ)
  have hζ' : (t * x * t⁻¹) * (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ = ζ := by
    rw [show (t * x * t⁻¹) * (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ =
      t * (x * y * x⁻¹ * y⁻¹) * t⁻¹ by group, ← hζ, hζc t]
    group
  have hθζ : θ (t * x * t⁻¹) * θ (t * y * t⁻¹) * (θ (t * x * t⁻¹))⁻¹ * (θ (t * y * t⁻¹))⁻¹ =
      θ ζ := by rw [← hL.map_comm hx'.1 hy'.1, hζ']
  have hζw : θ ζ * w i = w i * θ ζ := by
    have h := hL.conj _ _ (hw i) ζ hζP
    rw [conj_eq_of_comm (hζc (d i))] at h
    calc θ ζ * w i = w i * θ ζ * (w i)⁻¹ * w i := by rw [h]
      _ = w i * θ ζ := by group
  have hfx := hL.fix_sq hPodd hd hdc hdn hw hwc hji hx'
  have hfy := hL.fix_sq hPodd hd hdc hdn hw hwc hji hy'
  have hw' : ∀ a : A, w i • (θ ζ • a - a) = θ ζ • a - a := by
    intro a
    have := fix_comm_of_fix (by rw [hθζ]; exact hζw) hfx hfy a
    rwa [hθζ] at this
  have hc : θ x * θ y * (θ x)⁻¹ * (θ y)⁻¹ = θ ζ := by rw [hζ, hL.map_comm hx.1 hy.1]
  have hcomm : ∀ u ∈ P, θ ζ * θ u = θ u * θ ζ := fun u hu =>
    hL.commute_of_commute hζP hu (hζc u).symm
  have htriv : ∀ a : A, θ ζ • a = a := by
    intro a
    have := comm_acts_trivially h2 (by rw [hc]; exact hcomm x hx.1)
      (by rw [hc]; exact hcomm y hy.1) (hL.inv_of_mem (hw i) hx) (hL.inv_of_mem (hw i) hy)
      (hL.odd_orderOf hPodd hx.1) (hL.odd_orderOf hPodd hy.1)
      (by rw [hc]; exact hL.odd_orderOf hPodd hζP) (by rw [hc]; exact hw') a
    rwa [hc] at this
  have hζ1 : ζ = 1 := hL.faithful ζ hζP htriv
  calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = y * x := by rw [← hζ, hζ1, one_mul]

@[expose] def kerSub (hL : LiftData A P θ Lift) (hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (c : Y)
    (U : AddSubgroup A) : Subgroup Y where
  carrier := {x | x ∈ P ∧ c * x * c⁻¹ = x⁻¹ ∧ ∀ u ∈ U, θ x • u = u}
  one_mem' := ⟨P.one_mem, by group, fun u _ => by rw [hL.map_one, one_smul]⟩
  mul_mem' := by
    rintro x y ⟨hxP, hxc, hxU⟩ ⟨hyP, hyc, hyU⟩
    refine ⟨P.mul_mem hxP hyP, ?_, fun u hu => ?_⟩
    · rw [show c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) by group, hxc, hyc,
        ← mul_inv_rev, hab y hyP x hxP]
    · rw [hL.hom _ hxP _ hyP, mul_smul, hyU u hu, hxU u hu]
  inv_mem' := by
    rintro x ⟨hxP, hxc, hxU⟩
    refine ⟨P.inv_mem hxP, ?_, fun u hu => ?_⟩
    · rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ by group, hxc]
    · rw [hL.map_inv hxP, inv_smul_eq_iff, hxU u hu]

theorem false_of_frame [Finite A] (hL : LiftData A P θ Lift) (h2 : ∀ a : A, a + a = 0)
    [hPn : P.Normal] {Z₀ R : Subgroup Y} [hZn : Z₀.Normal] [hRn : R.Normal]
    (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀) (hPodd : Odd (Nat.card P))
    {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1) (hdc : ∀ i j, d i * d j = d j * d i)
    (hdn : ∀ i j, i ≠ j → d i ≠ d j) {t : Y} (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀)
    (hRS : ∀ r ∈ R, ∀ x ∈ P, (d 0 * r * (d 0)⁻¹ * r⁻¹) * x * (d 0 * r * (d 0)⁻¹ * r⁻¹)⁻¹ *
      x⁻¹ ∈ Z₀)
    (hYR : ∀ y : Y, ∃ r ∈ R, ∃ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 ∧ y = r * g)
    (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    (hmax : ∀ N : Subgroup Y, N.Normal → Z₀ ≤ N → N ≤ P → N = Z₀ ∨ N = P)
    (hnt : ∀ i, ∃ a ∈ InvSet P d i, a ≠ 1)
    (hframe : ∀ g : Y, g * (d 0 * d 1 * d 2) * g⁻¹ = d 0 * d 1 * d 2 →
      ∃ w : Fin 3 → Γ, (∀ i, Lift (w i) (g * d i * g⁻¹)) ∧ ∀ i j, w i * w j = w j * w i) :
    False := by
  classical
  set c := d 0 * d 1 * d 2 with hcdef
  obtain ⟨w, hw, hwc⟩ := hframe 1 (by group)
  simp only [one_mul, inv_one, mul_one] at hw
  have hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x :=
    abelian_of_invSet_comm hZc hZP hP' hPodd hd hdc hc hLA
      (fun i => hL.comm_of_invSet h2 hZc hZP hP' hPodd hd hdc hdn ht hw hwc i)
  have hcz : ∀ x ∈ Z₀, c * x * c⁻¹ = x⁻¹ → x = 1 := by
    intro x hx hcx
    have hxc : c * x * c⁻¹ = x := by rw [mem_center_iff.mp (hZc hx) c]; group
    exact eq_one_of_sq_of_odd hPodd (hZP hx) (by
      calc x * x = x * (c * x * c⁻¹)⁻¹ := by rw [hcx, inv_inv]
        _ = 1 := by rw [hxc, mul_inv_cancel])
  have hC : ∀ c₀ ∈ P, c * c₀ * c⁻¹ = c₀⁻¹ → ∀ a : A, θ c₀ • a = a := by
    intro c₀ hc₀P hc₀
    by_contra hne
    push_neg at hne
    obtain ⟨a₀, ha₀⟩ := hne
    let f : A →+ A :=
      { toFun := fun a => θ c₀ • a - a
        map_zero' := by rw [smul_zero, sub_zero]
        map_add' := fun a b => by rw [smul_add]; abel }
    have hf : ∀ a, f a = θ c₀ • a - a := fun a => rfl
    set Qs : Set Γ := θ '' (P : Set Y) with hQs
    have hQc : ∀ p ∈ Qs, ∀ q ∈ Qs, p * q = q * p := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hL.commute_of_commute hx hy (hab x hx y hy)
    have hc₀Q : θ c₀ ∈ Qs := ⟨c₀, hc₀P, rfl⟩
    have hBinv : ∀ q ∈ Qs, ∀ u ∈ f.range, q • u ∈ f.range := by
      rintro q hq _ ⟨a, rfl⟩
      refine ⟨q • a, ?_⟩
      rw [hf, hf, smul_sub, smul_smul, smul_smul, hQc q hq _ hc₀Q]
    let S : Set (AddSubgroup A) := {U | U ≠ ⊥ ∧ U ≤ f.range ∧ ∀ q ∈ Qs, ∀ u ∈ U, q • u ∈ U}
    have hBS : f.range ∈ S := by
      refine ⟨fun hbot => ?_, le_rfl, hBinv⟩
      have hmem : f a₀ ∈ f.range := ⟨a₀, rfl⟩
      rw [hbot, AddSubgroup.mem_bot, hf, sub_eq_zero] at hmem
      exact ha₀ hmem
    obtain ⟨U, ⟨hU0, hUB, hUinv⟩, hmin⟩ :=
      WellFounded.has_min (InvImage.wf (fun U : AddSubgroup A => Nat.card U) wellFounded_lt) S
        ⟨_, hBS⟩
    have hUmin : ∀ U' : AddSubgroup A, U' ≤ U → (∀ q ∈ Qs, ∀ u ∈ U', q • u ∈ U') →
        U' = ⊥ ∨ U' = U := by
      intro U' hU'U hU'inv
      by_cases h : U' = ⊥
      · exact Or.inl h
      · right
        have := hmin U' ⟨h, hU'U.trans hUB, hU'inv⟩
        exact AddSubgroup.eq_of_le_of_card_ge hU'U (not_lt.mp this)
    set L := kerSub hL hab c U with hLdef
    have hfr : ∀ g : Y, g * c * g⁻¹ = c → ∀ i j, i ≠ j →
        InvSet P (fun l => g * d l * g⁻¹) i ⊆ L ∨ InvSet P (fun l => g * d l * g⁻¹) j ⊆ L := by
      intro g hg i j hij
      obtain ⟨w', hw', hw'c⟩ := hframe g hg
      set e : Fin 3 → Y := fun l => g * d l * g⁻¹ with he
      have hed : ∀ i, e i * e i = 1 := fun i => by
        show g * d i * g⁻¹ * (g * d i * g⁻¹) = 1
        rw [show g * d i * g⁻¹ * (g * d i * g⁻¹) = g * (d i * d i) * g⁻¹ by group, hd i]; group
      have hedc : ∀ i j, e i * e j = e j * e i := fun i j => by
        show g * d i * g⁻¹ * (g * d j * g⁻¹) = g * d j * g⁻¹ * (g * d i * g⁻¹)
        rw [show g * d i * g⁻¹ * (g * d j * g⁻¹) = g * (d i * d j) * g⁻¹ by group, hdc i j]
        group
      have hedn : ∀ i j, i ≠ j → e i ≠ e j := fun i j hij h => hdn i j hij (by
        have h' : g * d i * g⁻¹ = g * d j * g⁻¹ := h
        simpa using h')
      have hce : e 0 * e 1 * e 2 = c := by
        show g * d 0 * g⁻¹ * (g * d 1 * g⁻¹) * (g * d 2 * g⁻¹) = c
        rw [← hg, hcdef]; group
      have hmemL : ∀ k, (∀ x ∈ θ '' InvSet P e k, ∀ u ∈ U, x • u = u) →
          InvSet P e k ⊆ L := by
        intro k h x hx
        refine ⟨hx.1, ?_, fun u hu => h _ ⟨x, hx, rfl⟩ u hu⟩
        rw [← hce]; exact c_inv_of_mem_invSet hx
      rcases fix_or_fix_of_minimal (Q := Qs) hQc hUinv hUmin
          (C₁ := θ '' InvSet P e i) (C₂ := θ '' InvSet P e j)
          (Set.image_mono fun x hx => hx.1)
          (by
            rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a
            exact hL.fix_fact h2 hPodd hed hedc hedn hw' hw'c hij hx hy
              (hab x hx.1 y hy.1) a) with h | h
      · exact Or.inl (hmemL i h)
      · exact Or.inr (hmemL j h)
    rcases le_or_sup_eq_of_frames hZc hZP hP' hPodd hd hdc hc hLA hRS hYR hgen hmax L
        (fun x hx => hx.1) hfr with h | h
    · have h1e : (fun l => (1 : Y) * d l * 1⁻¹) = d := by funext l; group
      have h01 := hfr 1 (by group) 0 1 (by decide)
      rw [h1e] at h01
      have hk : ∃ k, InvSet P d k ⊆ L := by
        rcases h01 with h0 | h0
        · exact ⟨0, h0⟩
        · exact ⟨1, h0⟩
      obtain ⟨k, hk⟩ := hk
      obtain ⟨a, ha, ha1⟩ := hnt k
      exact ha1 (hcz a (h (hk ha)) (hk ha).2.1)
    · obtain ⟨l, hl, hz⟩ := h c₀ hc₀P
      have hzc : c * (c₀⁻¹ * l) * c⁻¹ = (c₀⁻¹ * l)⁻¹ := by
        rw [show c * (c₀⁻¹ * l) * c⁻¹ = (c * c₀ * c⁻¹)⁻¹ * (c * l * c⁻¹) by group, hc₀, hl.2.1,
          inv_inv, mul_inv_rev, inv_inv]
        exact hab c₀ hc₀P _ (P.inv_mem hl.1)
      have hl' : l = c₀ := by
        have := hcz _ hz hzc
        calc l = c₀ * (c₀⁻¹ * l) := by group
          _ = c₀ := by rw [this, mul_one]
      obtain ⟨⟨u, hu⟩, hu0'⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hU0
      have hu0 : u ≠ 0 := fun h => hu0' (Subtype.ext h)
      obtain ⟨a, ha⟩ := hUB hu
      have hfix : θ c₀ • (θ c₀ • a - a) = θ c₀ • a - a := by
        rw [← hf, ha]
        have := hl.2.2 u hu
        rwa [hl'] at this
      apply hu0
      rw [← ha, hf]
      exact eq_zero_of_fix h2 (hL.odd_orderOf hPodd hc₀P) hfix
  obtain ⟨a, ha, ha1⟩ := hnt 0
  exact ha1 (hL.faithful a ha.1 (hC a ha.1 (c_inv_of_mem_invSet ha)))

end LiftData

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
