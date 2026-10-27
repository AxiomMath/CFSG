module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofCommon

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

theorem F3_aux : ∀ t : F3, t + t * (-1) = 0 := by decide

section DL

variable {G : Type} [Group G]

@[expose] noncomputable def dl (d z : G) : F3 :=
  @dite _ (∃ k : ℤ, d ^ k = z) (Classical.propDecidable _)
    (fun h => ((Classical.choose h : ℤ) : F3)) (fun _ => 0)

theorem dl_zpow {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (k : ℤ) : dl d (d ^ k) = (k : F3) := by
  have hh : ∃ k' : ℤ, d ^ k' = d ^ k := ⟨k, rfl⟩
  unfold dl
  rw [@dif_pos _ (Classical.propDecidable _) hh]
  have hspec := Classical.choose_spec hh
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have h1 := zpow_eq_zpow_iff_modEq.mp hspec
  rw [hord] at h1
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mpr (by simpa using h1)

theorem dl_mul {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {z₁ z₂ : G}
    (h₁ : z₁ ∈ Subgroup.zpowers d) (h₂ : z₂ ∈ Subgroup.zpowers d) :
    dl d (z₁ * z₂) = dl d z₁ + dl d z₂ := by
  obtain ⟨k₁, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₁
  obtain ⟨k₂, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₂
  rw [← _root_.zpow_add, dl_zpow hd3 hd1, dl_zpow hd3 hd1, dl_zpow hd3 hd1]
  push_cast
  rfl

theorem dl_one {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : dl d 1 = 0 := by
  have := dl_zpow hd3 hd1 0
  simpa using this

theorem dl_inv {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {z : G} (hz : z ∈ Subgroup.zpowers d) :
    dl d z⁻¹ = - dl d z := by
  have h := dl_mul hd3 hd1 hz (Subgroup.inv_mem _ hz)
  rw [mul_inv_cancel, dl_one hd3 hd1] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem dl_eq_zero_iff {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {z : G}
    (hz : z ∈ Subgroup.zpowers d) : dl d z = 0 ↔ z = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [dl_zpow hd3 hd1]
  constructor
  · intro h
    have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have : (3 : ℤ) ∣ k := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp h
      simpa using this
    obtain ⟨m, rfl⟩ := this
    rw [_root_.zpow_mul]
    simp [hd3]
  · intro h
    have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    have : (orderOf d : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [hord] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mpr (by simpa using this)

theorem dl_zpow_val {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {z : G}
    (hz : z ∈ Subgroup.zpowers d) : d ^ (dl d z).val = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [dl_zpow hd3 hd1]
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hord]
  have : ((((k : F3).val : ℕ) : ℤ) : F3) = (k : F3) := by simp
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ 3).mp this
  simpa using h2

end DL

section Pairing

variable {G : Type} [Group G]

@[expose] def cm (x y : G) : G := y⁻¹ * (x * y * x⁻¹)

@[expose] noncomputable def om (d x y : G) : F3 := dl d (cm x y)

structure CommData (Q : Subgroup G) (d : G) : Prop where
  hd3 : d ^ 3 = 1
  hd1 : d ≠ 1
  hdQ : d ∈ Q
  hzc : ∀ z ∈ Subgroup.zpowers d, ∀ q ∈ Q, q * z = z * q
  hcm : ∀ y ∈ Q, ∀ q ∈ Q, cm q y ∈ Subgroup.zpowers d

namespace CommData

variable {Q : Subgroup G} {d : G} (h : CommData Q d)

include h

theorem zpowers_le : Subgroup.zpowers d ≤ Q := Subgroup.zpowers_le.mpr h.hdQ

theorem cm_mul_left {x x' y : G} (hx : x ∈ Q) (hx' : x' ∈ Q) (hy : y ∈ Q) :
    cm (x * x') y = cm x y * cm x' y := by
  have hc := h.hcm y hy x hx
  have hc' := h.hcm y hy x' hx'
  have e1 : x * y * x⁻¹ = y * cm x y := by unfold cm; group
  have e2 : x' * y * x'⁻¹ = y * cm x' y := by unfold cm; group
  have e3 : x * cm x' y * x⁻¹ = cm x' y := by
    rw [h.hzc _ hc' x hx]; group
  calc cm (x * x') y = y⁻¹ * (x * (x' * y * x'⁻¹) * x⁻¹) := by unfold cm; group
    _ = y⁻¹ * (x * (y * cm x' y) * x⁻¹) := by rw [e2]
    _ = y⁻¹ * ((x * y * x⁻¹) * (x * cm x' y * x⁻¹)) := by group
    _ = y⁻¹ * ((y * cm x y) * cm x' y) := by rw [e1, e3]
    _ = cm x y * cm x' y := by group

theorem cm_mul_right {x y y' : G} (hx : x ∈ Q) (hy : y ∈ Q) (hy' : y' ∈ Q) :
    cm x (y * y') = cm x y * cm x y' := by
  have hc := h.hcm y hy x hx
  have hc' := h.hcm y' hy' x hx
  have e1 : x * y * x⁻¹ = y * cm x y := by unfold cm; group
  have e2 : x * y' * x⁻¹ = y' * cm x y' := by unfold cm; group
  have e3 : y'⁻¹ * cm x y * y' = cm x y := by
    have := h.hzc _ hc y' hy'
    calc y'⁻¹ * cm x y * y' = y'⁻¹ * (cm x y * y') := by group
      _ = y'⁻¹ * (y' * cm x y) := by rw [this]
      _ = cm x y := by group
  calc cm x (y * y') = y'⁻¹ * y⁻¹ * ((x * y * x⁻¹) * (x * y' * x⁻¹)) := by unfold cm; group
    _ = y'⁻¹ * y⁻¹ * ((y * cm x y) * (y' * cm x y')) := by rw [e1, e2]
    _ = (y'⁻¹ * cm x y * y') * cm x y' := by group
    _ = cm x y * cm x y' := by rw [e3]

theorem cm_self (x : G) : cm x x = 1 := by unfold cm; group

theorem cm_one_left (y : G) : cm 1 y = 1 := by unfold cm; group

theorem cm_d_right {x : G} (hx : x ∈ Q) : cm x d = 1 := by
  have := h.hzc d (Subgroup.mem_zpowers d) x hx
  unfold cm
  calc d⁻¹ * (x * d * x⁻¹) = d⁻¹ * (d * x * x⁻¹) := by rw [this]
    _ = 1 := by group

theorem cm_d_left {y : G} (hy : y ∈ Q) : cm d y = 1 := by
  have := h.hzc d (Subgroup.mem_zpowers d) y hy
  unfold cm
  calc y⁻¹ * (d * y * d⁻¹) = y⁻¹ * (y * d * d⁻¹) := by rw [← this]
    _ = 1 := by group

theorem cm_z_left {x z y : G} (hx : x ∈ Q) (hz : z ∈ Subgroup.zpowers d) (hy : y ∈ Q) :
    cm (x * z) y = cm x y := by
  have hzQ : z ∈ Q := h.zpowers_le hz
  have h1 : cm z y = 1 := by
    have := h.hzc z hz y hy
    unfold cm
    calc y⁻¹ * (z * y * z⁻¹) = y⁻¹ * (y * z * z⁻¹) := by rw [← this]
      _ = 1 := by group
  rw [h.cm_mul_left hx hzQ hy, h1, mul_one]

theorem cm_z_right {x y z : G} (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Subgroup.zpowers d) :
    cm x (y * z) = cm x y := by
  have hzQ : z ∈ Q := h.zpowers_le hz
  have h1 : cm x z = 1 := by
    have := h.hzc z hz x hx
    unfold cm
    calc z⁻¹ * (x * z * x⁻¹) = z⁻¹ * (z * x * x⁻¹) := by rw [this]
      _ = 1 := by group
  rw [h.cm_mul_right hx hy hzQ, h1, mul_one]

theorem cm_inv {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : cm y x = (cm x y)⁻¹ := by
  have hc := h.hcm y hy x hx
  have hu := h.hcm x hx y hy
  have hxy : x * y * x⁻¹ * y⁻¹ = cm x y := by
    have := h.hzc _ hc y hy
    unfold cm at this ⊢
    calc x * y * x⁻¹ * y⁻¹ = y * (y⁻¹ * (x * y * x⁻¹)) * y⁻¹ := by group
      _ = y⁻¹ * (x * y * x⁻¹) := by rw [this]; group
  have hyx : y * x * y⁻¹ * x⁻¹ = cm y x := by
    have := h.hzc _ hu x hx
    unfold cm at this ⊢
    calc y * x * y⁻¹ * x⁻¹ = x * (x⁻¹ * (y * x * y⁻¹)) * x⁻¹ := by group
      _ = x⁻¹ * (y * x * y⁻¹) := by rw [this]; group
  rw [← hyx, ← hxy]
  group

theorem om_add_left {x x' y : G} (hx : x ∈ Q) (hx' : x' ∈ Q) (hy : y ∈ Q) :
    om d (x * x') y = om d x y + om d x' y := by
  unfold om
  rw [h.cm_mul_left hx hx' hy]
  exact dl_mul h.hd3 h.hd1 (h.hcm y hy x hx) (h.hcm y hy x' hx')

theorem om_add_right {x y y' : G} (hx : x ∈ Q) (hy : y ∈ Q) (hy' : y' ∈ Q) :
    om d x (y * y') = om d x y + om d x y' := by
  unfold om
  rw [h.cm_mul_right hx hy hy']
  exact dl_mul h.hd3 h.hd1 (h.hcm y hy x hx) (h.hcm y' hy' x hx)

theorem om_self (x : G) : om d x x = 0 := by
  unfold om; rw [h.cm_self]; exact dl_one h.hd3 h.hd1

theorem om_one_left (y : G) : om d 1 y = 0 := by
  unfold om; rw [h.cm_one_left]; exact dl_one h.hd3 h.hd1

theorem om_neg {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : om d y x = - om d x y := by
  unfold om
  rw [h.cm_inv hx hy]
  exact dl_inv h.hd3 h.hd1 (h.hcm y hy x hx)

theorem om_d_right {x : G} (hx : x ∈ Q) : om d x d = 0 := by
  unfold om; rw [h.cm_d_right hx]; exact dl_one h.hd3 h.hd1

theorem om_d_left {y : G} (hy : y ∈ Q) : om d d y = 0 := by
  unfold om; rw [h.cm_d_left hy]; exact dl_one h.hd3 h.hd1

theorem om_z_left {x z y : G} (hx : x ∈ Q) (hz : z ∈ Subgroup.zpowers d) (hy : y ∈ Q) :
    om d (x * z) y = om d x y := by
  unfold om; rw [h.cm_z_left hx hz hy]

theorem om_z_right {x y z : G} (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Subgroup.zpowers d) :
    om d x (y * z) = om d x y := by
  unfold om; rw [h.cm_z_right hx hy hz]

theorem om_one_right {x : G} (hx : x ∈ Q) : om d x 1 = 0 := by
  have := h.om_add_right hx Q.one_mem Q.one_mem
  rw [mul_one] at this
  exact add_eq_left.mp this.symm

theorem om_pow_right {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) (n : ℕ) :
    om d x (y ^ n) = (n : F3) * om d x y := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact h.om_one_right hx
  | succ n ih =>
    rw [pow_succ, h.om_add_right hx (Q.pow_mem hy n) hy, ih]
    push_cast
    ring

omit h in
theorem cm_conj (g x y : G) : cm (g * x * g⁻¹) (g * y * g⁻¹) = g * cm x y * g⁻¹ := by
  unfold cm; group

theorem om_conj {g : G} {m : ℤ} (hg : g * d * g⁻¹ = d ^ m) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    om d (g * x * g⁻¹) (g * y * g⁻¹) = (m : F3) * om d x y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.hcm y hy x hx)
  unfold om
  rw [cm_conj, ← hk, ← conj_zpow, hg, ← _root_.zpow_mul, dl_zpow h.hd3 h.hd1,
    dl_zpow h.hd3 h.hd1]
  push_cast
  rfl

theorem comm_of_om_zero {a x : G} (ha : a ∈ Q) (hx : x ∈ Q) (h0 : om d a x = 0) :
    a * x = x * a := by
  have h1 : cm a x = 1 := (dl_eq_zero_iff h.hd3 h.hd1 (h.hcm x hx a ha)).mp h0
  unfold cm at h1
  calc a * x = x * (x⁻¹ * (a * x * a⁻¹)) * a := by group
    _ = x * a := by rw [h1]; group

theorem om_zero_of_comm {a x : G} (hc : a * x = x * a) : om d a x = 0 := by
  unfold om cm
  have : x⁻¹ * (a * x * a⁻¹) = 1 := by rw [hc]; group
  rw [this]
  exact dl_one h.hd3 h.hd1

end CommData

end Pairing

section Basis

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

structure QData (A Q : Subgroup G) (d a₀ a₁ : G) : Prop where
  hAe : IsElemAbelian 3 A
  hA27 : Nat.card A = 27
  hdA : d ∈ A
  hd1 : d ≠ 1
  hQX : IsExtra2127 Q
  hQS : IsSylowOf 3 Q (Subgroup.normalizer (A : Set G))
  hAQ : A ≤ Q
  hQC : Q ⊓ Subgroup.centralizer (A : Set G) = A
  hdc : ∀ q ∈ Q, q * d * q⁻¹ = d
  ha₀ : a₀ ∈ A
  ha₁ : a₁ ∈ A
  ha₀d : a₀ ∉ Subgroup.zpowers d
  ha₁d : a₁ ∉ Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d

namespace QData

variable {A Q : Subgroup G} {d a₀ a₁ : G} (h : QData A Q d a₀ a₁)

include h

theorem hd3 : d ^ 3 = 1 := h.hAe.2 d h.hdA

theorem hdQ : d ∈ Q := h.hAQ h.hdA

theorem hQ243 : Nat.card Q = 243 := by
  obtain ⟨-, h35, -⟩ := h.hQX
  rw [h35]; norm_num

theorem hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (h.hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem comm : CommData Q d where
  hd3 := h.hd3
  hd1 := h.hd1
  hdQ := h.hdQ
  hzc := by
    intro z hz q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hqd : Commute q d := by
      show q * d = d * q
      calc q * d = q * d * q⁻¹ * q := by group
        _ = d * q := by rw [h.hdc q hq]
    exact (hqd.zpow_right k).eq
  hcm := Item2119End2Proof.comm_mem_zpowers h.hQX.1 h.hdQ h.hd1 h.hd3 h.hdc

theorem hA_eq : Subgroup.zpowers a₀ ⊔ Subgroup.zpowers d ⊔ Subgroup.zpowers a₁ = A :=
  Item2119End8Proof.sup_zpowers_eq h.hAe.2 h.hA27 h.hdA h.hd1 h.ha₀ h.ha₁ h.ha₀d h.ha₁d

theorem exists_f :
    ∃ f₀ ∈ Q, ∃ f₁ ∈ Q, om d a₀ f₀ = 1 ∧ om d a₁ f₀ = 0 ∧ om d a₀ f₁ = 0 ∧ om d a₁ f₁ = 1 ∧
      om d f₀ f₁ = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC := h.comm
  have ha₀Q : a₀ ∈ Q := h.hAQ h.ha₀
  have ha₁Q : a₁ ∈ Q := h.hAQ h.ha₁
  let Λ : Q →* Multiplicative (Fin 2 → F3) :=
    { toFun := fun x => Multiplicative.ofAdd ![om d a₀ x, om d a₁ x]
      map_one' := by
        have e0 := hC.om_one_right ha₀Q
        have e1 := hC.om_one_right ha₁Q
        show Multiplicative.ofAdd ![om d a₀ ((1 : Q) : G), om d a₁ ((1 : Q) : G)] = 1
        rw [Subgroup.coe_one, e0, e1]
        ext i; fin_cases i <;> rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd ![om d a₀ ((x * y : Q) : G), om d a₁ ((x * y : Q) : G)] =
          Multiplicative.ofAdd ![om d a₀ x, om d a₁ x] *
            Multiplicative.ofAdd ![om d a₀ y, om d a₁ y]
        rw [Subgroup.coe_mul, hC.om_add_right ha₀Q x.2 y.2, hC.om_add_right ha₁Q x.2 y.2]
        ext i; fin_cases i <;> rfl }
  have hΛ : ∀ x : Q, Λ x = Multiplicative.ofAdd ![om d a₀ x, om d a₁ x] := fun x => rfl
  have hker : Λ.ker = A.subgroupOf Q := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΛ]
    constructor
    · intro hx
      have hx' : (![om d a₀ x, om d a₁ x] : Fin 2 → F3) = 0 := ofAdd_eq_one.mp hx
      have e0 : om d a₀ x = 0 := by simpa using congrFun hx' 0
      have e1 : om d a₁ x = 0 := by simpa using congrFun hx' 1
      have hxQ : (x : G) ∈ Q := x.2
      have hle : A ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
        rw [← h.hA_eq]
        refine sup_le (sup_le ?_ ?_) ?_
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hC.comm_of_om_zero ha₀Q hxQ e0)
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (hC.hzc d (Subgroup.mem_zpowers d) x hxQ).symm
        · rw [Subgroup.zpowers_le]
          exact Subgroup.mem_centralizer_singleton_iff.mpr (hC.comm_of_om_zero ha₁Q hxQ e1)
      have hxC : (x : G) ∈ Subgroup.centralizer (A : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
      rw [← h.hQC]
      exact ⟨hxQ, hxC⟩
    · intro hx
      have e0 : om d a₀ x = 0 := hC.om_zero_of_comm (h.hAc _ h.ha₀ _ hx)
      have e1 : om d a₁ x = 0 := hC.om_zero_of_comm (h.hAc _ h.ha₁ _ hx)
      rw [e0, e1]
      exact (ofAdd_eq_one).mpr (by ext i; fin_cases i <;> rfl)
  have hkerCard : Nat.card Λ.ker = 27 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hAQ).toEquiv, h.hA27]
  have hprod := Subgroup.card_ker_mul_card_range Λ
  rw [hkerCard] at hprod
  have hQ243 := h.hQ243
  have hrange9 : Nat.card Λ.range = 9 := by
    have : Nat.card Q = 243 := hQ243
    omega
  have hMcard : Nat.card (Multiplicative (Fin 2 → F3)) = 9 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hrange : Λ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange9, hMcard])
  have hsurj : ∀ y, ∃ x : Q, Λ x = y := fun y => by
    have : y ∈ Λ.range := by rw [hrange]; exact Subgroup.mem_top y
    exact this
  obtain ⟨x₀, hx₀⟩ := hsurj (Multiplicative.ofAdd ![1, 0])
  obtain ⟨x₁, hx₁⟩ := hsurj (Multiplicative.ofAdd ![0, 1])
  rw [hΛ] at hx₀ hx₁
  have hx₀' := Multiplicative.ofAdd.injective hx₀
  have hx₁' := Multiplicative.ofAdd.injective hx₁
  have o00 : om d a₀ x₀ = 1 := by simpa using congrFun hx₀' 0
  have o10 : om d a₁ x₀ = 0 := by simpa using congrFun hx₀' 1
  have o01 : om d a₀ x₁ = 0 := by simpa using congrFun hx₁' 0
  have o11 : om d a₁ x₁ = 1 := by simpa using congrFun hx₁' 1
  set c := (om d x₀ x₁).val with hc
  have hc' : (c : F3) = om d x₀ x₁ := ZMod.natCast_zmod_val _
  have hpowQ : a₀ ^ c ∈ Q := Q.pow_mem ha₀Q c
  have hA₀₀ : om d a₀ a₀ = 0 := hC.om_self a₀
  have hA₁₀ : om d a₁ a₀ = 0 := hC.om_zero_of_comm (h.hAc _ h.ha₁ _ h.ha₀)
  refine ⟨x₀, x₀.2, x₁ * a₀ ^ c, Q.mul_mem x₁.2 hpowQ, o00, o10, ?_, ?_, ?_⟩
  · rw [hC.om_add_right ha₀Q x₁.2 hpowQ, hC.om_pow_right ha₀Q ha₀Q, o01, hA₀₀]; ring
  · rw [hC.om_add_right ha₁Q x₁.2 hpowQ, hC.om_pow_right ha₁Q ha₀Q, o11, hA₁₀]; ring
  · rw [hC.om_add_right x₀.2 x₁.2 hpowQ, hC.om_pow_right x₀.2 ha₀Q, hC.om_neg ha₀Q x₀.2, o00, hc']
    exact F3_aux _

end QData

structure SympBasis (A Q : Subgroup G) (d a₀ a₁ f₀ f₁ : G) : Prop extends QData A Q d a₀ a₁ where
  hf₀ : f₀ ∈ Q
  hf₁ : f₁ ∈ Q
  o00 : om d a₀ f₀ = 1
  o10 : om d a₁ f₀ = 0
  o01 : om d a₀ f₁ = 0
  o11 : om d a₁ f₁ = 1
  off : om d f₀ f₁ = 0

@[expose] noncomputable def Phi (d a₀ a₁ f₀ f₁ x : G) : V4 :=
  ![om d x f₀, om d x f₁, om d a₀ x, om d a₁ x]

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem hC : CommData Q d := h.toQData.comm

theorem ha₀Q : a₀ ∈ Q := h.hAQ h.ha₀
theorem ha₁Q : a₁ ∈ Q := h.hAQ h.ha₁

theorem Phi_mul {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    Phi d a₀ a₁ f₀ f₁ (x * y) = Phi d a₀ a₁ f₀ f₁ x + Phi d a₀ a₁ f₀ f₁ y := by
  have hC := h.hC
  ext i
  fin_cases i <;> simp [Phi, hC.om_add_left hx hy h.hf₀, hC.om_add_left hx hy h.hf₁,
    hC.om_add_right h.ha₀Q hx hy, hC.om_add_right h.ha₁Q hx hy]

theorem Phi_one : Phi d a₀ a₁ f₀ f₁ 1 = 0 := by
  have hC := h.hC
  ext i
  fin_cases i <;> simp [Phi, hC.om_one_left, hC.om_one_right h.ha₀Q, hC.om_one_right h.ha₁Q]

theorem Phi_inv {x : G} (hx : x ∈ Q) :
    Phi d a₀ a₁ f₀ f₁ x⁻¹ = - Phi d a₀ a₁ f₀ f₁ x := by
  have h1 := h.Phi_mul (Q.inv_mem hx) hx
  rw [inv_mul_cancel, h.Phi_one] at h1
  exact eq_neg_of_add_eq_zero_left h1.symm

theorem om_z_zero_left {z y : G} (hz : z ∈ Subgroup.zpowers d) (hy : y ∈ Q) : om d z y = 0 := by
  have hC := h.hC
  have := hC.om_z_left (x := 1) Q.one_mem hz hy
  rwa [one_mul, hC.om_one_left] at this

theorem om_z_zero_right {x z : G} (hx : x ∈ Q) (hz : z ∈ Subgroup.zpowers d) : om d x z = 0 := by
  have hC := h.hC
  have := hC.om_z_right (y := 1) hx Q.one_mem hz
  rwa [one_mul, hC.om_one_right hx] at this

theorem Phi_z0 {z : G} (hz : z ∈ Subgroup.zpowers d) : Phi d a₀ a₁ f₀ f₁ z = 0 := by
  ext i
  fin_cases i <;> simp [Phi, h.om_z_zero_left hz h.hf₀, h.om_z_zero_left hz h.hf₁,
    h.om_z_zero_right h.ha₀Q hz, h.om_z_zero_right h.ha₁Q hz]

theorem Phi_z {x z : G} (hx : x ∈ Q) (hz : z ∈ Subgroup.zpowers d) :
    Phi d a₀ a₁ f₀ f₁ (x * z) = Phi d a₀ a₁ f₀ f₁ x := by
  rw [h.Phi_mul hx (h.hC.zpowers_le hz), h.Phi_z0 hz, add_zero]

theorem Phi_a₀ : Phi d a₀ a₁ f₀ f₁ a₀ = ![1, 0, 0, 0] := by
  have hC := h.hC
  have e : om d a₁ a₀ = 0 := hC.om_zero_of_comm (h.hAc _ h.ha₁ _ h.ha₀)
  ext i
  fin_cases i <;> simp [Phi, h.o00, h.o01, hC.om_self, e]

theorem Phi_a₁ : Phi d a₀ a₁ f₀ f₁ a₁ = ![0, 1, 0, 0] := by
  have hC := h.hC
  have e : om d a₀ a₁ = 0 := hC.om_zero_of_comm (h.hAc _ h.ha₀ _ h.ha₁)
  ext i
  fin_cases i <;> simp [Phi, h.o10, h.o11, hC.om_self, e]

theorem Phi_f₀ : Phi d a₀ a₁ f₀ f₁ f₀ = ![0, 0, 1, 0] := by
  have hC := h.hC
  ext i
  fin_cases i <;> simp [Phi, h.o00, h.o10, h.off, hC.om_self]

theorem Phi_f₁ : Phi d a₀ a₁ f₀ f₁ f₁ = ![0, 0, 0, 1] := by
  have hC := h.hC
  have e : om d f₁ f₀ = 0 := by rw [hC.om_neg h.hf₀ h.hf₁, h.off]; exact neg_zero
  ext i
  fin_cases i <;> simp [Phi, h.o01, h.o11, hC.om_self, e]

theorem Phi_pow {x : G} (hx : x ∈ Q) (n : ℕ) :
    Phi d a₀ a₁ f₀ f₁ (x ^ n) = n • Phi d a₀ a₁ f₀ f₁ x := by
  induction n with
  | zero => simp [h.Phi_one]
  | succ n ih => rw [pow_succ, h.Phi_mul (Q.pow_mem hx n) hx, ih, succ_nsmul]

@[expose] def rep (d a₀ a₁ f₀ f₁ : G) (n : V4) : G :=
  a₀ ^ (n 0).val * a₁ ^ (n 1).val * f₀ ^ (n 2).val * f₁ ^ (n 3).val

theorem rep_mem (n : V4) : rep d a₀ a₁ f₀ f₁ n ∈ Q :=
  Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.pow_mem h.ha₀Q _) (Q.pow_mem h.ha₁Q _))
    (Q.pow_mem h.hf₀ _)) (Q.pow_mem h.hf₁ _)

theorem Phi_rep (n : V4) : Phi d a₀ a₁ f₀ f₁ (rep d a₀ a₁ f₀ f₁ n) = n := by
  unfold rep
  rw [h.Phi_mul (Q.mul_mem (Q.mul_mem (Q.pow_mem h.ha₀Q _) (Q.pow_mem h.ha₁Q _))
      (Q.pow_mem h.hf₀ _)) (Q.pow_mem h.hf₁ _),
    h.Phi_mul (Q.mul_mem (Q.pow_mem h.ha₀Q _) (Q.pow_mem h.ha₁Q _)) (Q.pow_mem h.hf₀ _),
    h.Phi_mul (Q.pow_mem h.ha₀Q _) (Q.pow_mem h.ha₁Q _),
    h.Phi_pow h.ha₀Q, h.Phi_pow h.ha₁Q, h.Phi_pow h.hf₀, h.Phi_pow h.hf₁, h.Phi_a₀, h.Phi_a₁,
    h.Phi_f₀, h.Phi_f₁]
  ext i
  fin_cases i <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem Phi_ker {x : G} (hx : x ∈ Q) (h0 : Phi d a₀ a₁ f₀ f₁ x = 0) :
    x ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Φ : Q →* Multiplicative V4 :=
    { toFun := fun y => Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ y)
      map_one' := by
        show Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ ((1 : Q) : G)) = 1
        rw [Subgroup.coe_one, h.Phi_one]; rfl
      map_mul' := by
        intro y z
        show Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ ((y * z : Q) : G)) =
          Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ y) * Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ z)
        rw [Subgroup.coe_mul, h.Phi_mul y.2 z.2]; rfl }
  have hΦ : ∀ y : Q, Φ y = Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ y) := fun y => rfl
  have hrange : Φ.range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    exact ⟨⟨_, h.rep_mem (Multiplicative.toAdd v)⟩, by rw [hΦ]; simp [h.Phi_rep]⟩
  have hcard81 : Nat.card (Multiplicative V4) = 81 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hprod := Subgroup.card_ker_mul_card_range Φ
  rw [hrange, Subgroup.card_top, hcard81, h.hQ243] at hprod
  have hker3 : Nat.card Φ.ker = 3 := by omega
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.hd3 h.hd1]
  have hZ : (Subgroup.zpowers d).subgroupOf Q ≤ Φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, hΦ]
    have hz' : (z : G) ∈ Subgroup.zpowers d := hz
    rw [h.Phi_z0 hz']; rfl
  have hZ3 : Nat.card ((Subgroup.zpowers d).subgroupOf Q) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hC.zpowers_le).toEquiv, hd3]
  have heq : (Subgroup.zpowers d).subgroupOf Q = Φ.ker :=
    Subgroup.eq_of_le_of_card_ge hZ (by rw [hker3, hZ3])
  have hmem : (⟨x, hx⟩ : Q) ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, hΦ]
    show Multiplicative.ofAdd (Phi d a₀ a₁ f₀ f₁ x) = 1
    rw [h0]; rfl
  rw [← heq] at hmem
  exact hmem

theorem Phi_eq {x y : G} (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : Phi d a₀ a₁ f₀ f₁ x = Phi d a₀ a₁ f₀ f₁ y) : x⁻¹ * y ∈ Subgroup.zpowers d := by
  apply h.Phi_ker (Q.mul_mem (Q.inv_mem hx) hy)
  rw [h.Phi_mul (Q.inv_mem hx) hy, h.Phi_inv hx, hxy]
  exact neg_add_cancel _

theorem closure_eq : Subgroup.closure ({a₀, a₁, f₀, f₁, d} : Set G) = Q := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h.ha₀Q
    · exact h.ha₁Q
    · exact h.hf₀
    · exact h.hf₁
    · exact h.hdQ
  · intro x hx
    have hr := h.rep_mem (Phi d a₀ a₁ f₀ f₁ x)
    have hz := h.Phi_eq hr hx (h.Phi_rep _)
    have hcl : rep d a₀ a₁ f₀ f₁ (Phi d a₀ a₁ f₀ f₁ x) ∈
        Subgroup.closure ({a₀, a₁, f₀, f₁, d} : Set G) := by
      unfold rep
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_ <;>
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
    have hzcl : (rep d a₀ a₁ f₀ f₁ (Phi d a₀ a₁ f₀ f₁ x))⁻¹ * x ∈
        Subgroup.closure ({a₀, a₁, f₀, f₁, d} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hz
    have := Subgroup.mul_mem _ hcl hzcl
    simpa using this

theorem ext_add {V : Type*} [AddCommGroup V] (u v : G → V)
    (hu : ∀ x ∈ Q, ∀ y ∈ Q, u (x * y) = u x + u y)
    (hv : ∀ x ∈ Q, ∀ y ∈ Q, v (x * y) = v x + v y)
    (h₁ : u a₀ = v a₀) (h₂ : u a₁ = v a₁) (h₃ : u f₀ = v f₀) (h₄ : u f₁ = v f₁)
    (h₅ : u d = v d) : ∀ x ∈ Q, u x = v x := by
  have hu1 : u 1 = 0 := by
    have := hu 1 Q.one_mem 1 Q.one_mem
    rw [mul_one] at this
    exact add_eq_left.mp this.symm
  have hv1 : v 1 = 0 := by
    have := hv 1 Q.one_mem 1 Q.one_mem
    rw [mul_one] at this
    exact add_eq_left.mp this.symm
  intro x hx
  rw [← h.closure_eq] at hx
  refine Subgroup.closure_induction (p := fun x _ => u x = v x) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [hu1, hv1]
  · intro x y hx hy ihx ihy
    rw [h.closure_eq] at hx hy
    rw [hu x hx y hy, hv x hx y hy, ihx, ihy]
  · intro x hx ihx
    rw [h.closure_eq] at hx
    have e1 := hu x⁻¹ (Q.inv_mem hx) x hx
    have e2 := hv x⁻¹ (Q.inv_mem hx) x hx
    rw [inv_mul_cancel, hu1] at e1
    rw [inv_mul_cancel, hv1] at e2
    have i1 : u x⁻¹ = - u x := eq_neg_of_add_eq_zero_left e1.symm
    have i2 : v x⁻¹ = - v x := eq_neg_of_add_eq_zero_left e2.symm
    rw [i1, i2, ihx]

end SympBasis

theorem omega4_add_left (u u' w : V4) : omega4 (u + u') w = omega4 u w + omega4 u' w := by
  simp [omega4]; ring

theorem omega4_zero_left (w : V4) : omega4 0 w = 0 := by simp [omega4]

theorem omega4_e0 : ∀ y : V4, omega4 ![1, 0, 0, 0] y = y 2 := by decide +kernel
theorem omega4_e1 : ∀ y : V4, omega4 ![0, 1, 0, 0] y = y 3 := by decide +kernel
theorem omega4_e2 : ∀ y : V4, omega4 ![0, 0, 1, 0] y = - y 0 := by decide +kernel
theorem omega4_e3 : ∀ y : V4, omega4 ![0, 0, 0, 1] y = - y 1 := by decide +kernel

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem omega4_Phi {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    omega4 (Phi d a₀ a₁ f₀ f₁ x) (Phi d a₀ a₁ f₀ f₁ y) = om d x y := by
  have hC := h.hC
  refine h.ext_add (fun x => omega4 (Phi d a₀ a₁ f₀ f₁ x) (Phi d a₀ a₁ f₀ f₁ y))
    (fun x => om d x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx
  · intro x hx x' hx'
    show omega4 (Phi d a₀ a₁ f₀ f₁ (x * x')) _ = omega4 (Phi d a₀ a₁ f₀ f₁ x) _ +
      omega4 (Phi d a₀ a₁ f₀ f₁ x') _
    rw [h.Phi_mul hx hx', omega4_add_left]
  · intro x hx x' hx'
    exact hC.om_add_left hx hx' hy
  · show omega4 (Phi d a₀ a₁ f₀ f₁ a₀) _ = om d a₀ y
    rw [h.Phi_a₀, omega4_e0]; rfl
  · show omega4 (Phi d a₀ a₁ f₀ f₁ a₁) _ = om d a₁ y
    rw [h.Phi_a₁, omega4_e1]; rfl
  · show omega4 (Phi d a₀ a₁ f₀ f₁ f₀) _ = om d f₀ y
    rw [h.Phi_f₀, omega4_e2]
    show - om d y f₀ = om d f₀ y
    rw [hC.om_neg h.hf₀ hy]; exact neg_neg _
  · show omega4 (Phi d a₀ a₁ f₀ f₁ f₁) _ = om d f₁ y
    rw [h.Phi_f₁, omega4_e3]
    show - om d y f₁ = om d f₁ y
    rw [hC.om_neg h.hf₁ hy]; exact neg_neg _
  · show omega4 (Phi d a₀ a₁ f₀ f₁ d) _ = om d d y
    rw [h.Phi_z0 (Subgroup.mem_zpowers d), omega4_zero_left, hC.om_d_left hy]

end SympBasis

@[expose] noncomputable def Mg (d a₀ a₁ f₀ f₁ g : G) : M4 :=
  Matrix.of fun i j => Phi d a₀ a₁ f₀ f₁ (g * ![a₀, a₁, f₀, f₁] j * g⁻¹) i

namespace SympBasis

variable {A Q : Subgroup G} {d a₀ a₁ f₀ f₁ : G} (h : SympBasis A Q d a₀ a₁ f₀ f₁)

include h

theorem conj_mem {g x : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Q) :
    g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem Mg_apply {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d) {x : G} (hx : x ∈ Q) :
    Phi d a₀ a₁ f₀ f₁ (g * x * g⁻¹) = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ x) := by
  refine h.ext_add (fun x => Phi d a₀ a₁ f₀ f₁ (g * x * g⁻¹))
    (fun x => (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx
  · intro x hx y hy
    show Phi d a₀ a₁ f₀ f₁ (g * (x * y) * g⁻¹) = _ + _
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this, h.Phi_mul (h.conj_mem hg hx) (h.conj_mem hg hy)]
  · intro x hx y hy
    show (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ (x * y)) = _ + _
    rw [h.Phi_mul hx hy, Matrix.mulVec_add]
  · show _ = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ a₀)
    rw [h.Phi_a₀]
    ext i
    simp [Mg, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · show _ = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ a₁)
    rw [h.Phi_a₁]
    ext i
    simp [Mg, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · show _ = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ f₀)
    rw [h.Phi_f₀]
    ext i
    simp [Mg, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · show _ = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ f₁)
    rw [h.Phi_f₁]
    ext i
    simp [Mg, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · show Phi d a₀ a₁ f₀ f₁ (g * d * g⁻¹) = (Mg d a₀ a₁ f₀ f₁ g).mulVec (Phi d a₀ a₁ f₀ f₁ d)
    rw [h.Phi_z0 hgd, h.Phi_z0 (Subgroup.mem_zpowers d), Matrix.mulVec_zero]

theorem Mg_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hgd : g * d * g⁻¹ ∈ Subgroup.zpowers d) (hg' : g' ∈ Subgroup.normalizer (Q : Set G)) :
    Mg d a₀ a₁ f₀ f₁ (g * g') = Mg d a₀ a₁ f₀ f₁ g * Mg d a₀ a₁ f₀ f₁ g' := by
  ext i j
  have hb : ∀ j : Fin 4, ![a₀, a₁, f₀, f₁] j ∈ Q := by
    intro j; fin_cases j
    · exact h.ha₀Q
    · exact h.ha₁Q
    · exact h.hf₀
    · exact h.hf₁
  have h1 := h.Mg_apply hg hgd (h.conj_mem hg' (hb j))
  have e : g * (g' * ![a₀, a₁, f₀, f₁] j * g'⁻¹) * g⁻¹ =
      g * g' * ![a₀, a₁, f₀, f₁] j * (g * g')⁻¹ := by group
  rw [e] at h1
  have := congrFun h1 i
  simp only [Mg, Matrix.of_apply]
  rw [this, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, Mg]

theorem Mg_one : Mg d a₀ a₁ f₀ f₁ 1 = 1 := by
  ext i j
  fin_cases j
  · have := congrFun h.Phi_a₀ i
    simp [Mg, this, Matrix.one_apply]
    fin_cases i <;> simp
  · have := congrFun h.Phi_a₁ i
    simp [Mg, this, Matrix.one_apply]
    fin_cases i <;> simp
  · have := congrFun h.Phi_f₀ i
    simp [Mg, this, Matrix.one_apply]
    fin_cases i <;> simp
  · have := congrFun h.Phi_f₁ i
    simp [Mg, this, Matrix.one_apply]
    fin_cases i <;> simp

theorem basis_mem (j : Fin 4) : ![a₀, a₁, f₀, f₁] j ∈ Q := by
  fin_cases j
  · exact h.ha₀Q
  · exact h.ha₁Q
  · exact h.hf₀
  · exact h.hf₁

theorem Mg_Q {q : G} (hq : q ∈ Q) : Mg d a₀ a₁ f₀ f₁ q = 1 := by
  have hC := h.hC
  have hqN : q ∈ Subgroup.normalizer (Q : Set G) := (Subgroup.mem_normalizer_iff).mpr
    fun x => ⟨fun hx => Q.mul_mem (Q.mul_mem hq hx) (Q.inv_mem hq), fun hx => by
      have := Q.mul_mem (Q.mul_mem (Q.inv_mem hq) hx) hq
      simpa [mul_assoc] using this⟩
  ext i j
  have hb := h.basis_mem j
  have e : q * ![a₀, a₁, f₀, f₁] j * q⁻¹ =
      ![a₀, a₁, f₀, f₁] j * cm q (![a₀, a₁, f₀, f₁] j) := by
    unfold cm; group
  have hz := hC.hcm _ hb q hq
  have h1 : Phi d a₀ a₁ f₀ f₁ (q * ![a₀, a₁, f₀, f₁] j * q⁻¹) =
      Phi d a₀ a₁ f₀ f₁ (![a₀, a₁, f₀, f₁] j) := by
    rw [e]; exact h.Phi_z hb hz
  have h2 : (1 : M4) i j = Phi d a₀ a₁ f₀ f₁ (![a₀, a₁, f₀, f₁] j) i := by
    have := congrFun (congrFun h.Mg_one i) j
    simp only [Mg, Matrix.of_apply, one_mul, inv_one, mul_one] at this
    exact this.symm
  rw [h2]
  simp only [Mg, Matrix.of_apply]
  rw [h1]

theorem Mg_omega {g : G} {m : ℤ} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hgd : g * d * g⁻¹ = d ^ m) (u v : V4) :
    omega4 ((Mg d a₀ a₁ f₀ f₁ g).mulVec u) ((Mg d a₀ a₁ f₀ f₁ g).mulVec v) =
      (m : F3) * omega4 u v := by
  have hC := h.hC
  have hgz : g * d * g⁻¹ ∈ Subgroup.zpowers d := by
    rw [hgd]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) m
  have hu := h.Phi_rep u
  have hv := h.Phi_rep v
  rw [← hu, ← hv, ← h.Mg_apply hg hgz (h.rep_mem u), ← h.Mg_apply hg hgz (h.rep_mem v),
    h.omega4_Phi (h.conj_mem hg (h.rep_mem u)) (h.conj_mem hg (h.rep_mem v)),
    hC.om_conj hgd (h.rep_mem u) (h.rep_mem v), h.omega4_Phi (h.rep_mem u) (h.rep_mem v)]

theorem Mg_symp {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hgd : g * d * g⁻¹ = d)
    (u v : V4) :
    omega4 ((Mg d a₀ a₁ f₀ f₁ g).mulVec u) ((Mg d a₀ a₁ f₀ f₁ g).mulVec v) = omega4 u v := by
  have := h.Mg_omega (m := 1) hg (by rw [hgd, zpow_one]) u v
  rw [this]; simp

theorem Mg_mult {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) (hgd : g * d * g⁻¹ = d⁻¹)
    (u v : V4) :
    omega4 ((Mg d a₀ a₁ f₀ f₁ g).mulVec u) ((Mg d a₀ a₁ f₀ f₁ g).mulVec v) = - omega4 u v := by
  have := h.Mg_omega (m := -1) hg (by rw [hgd, zpow_neg_one]) u v
  rw [this]; push_cast; exact neg_one_mul _

end SympBasis

end Basis

theorem exists_sylowOf_ge {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Y : Subgroup G} (hP : IsPGroup p P) (hPY : P ≤ Y) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S Y ∧ P ≤ S := by
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP.comap_subtype
  refine ⟨(S : Subgroup Y).map Y.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPY hx⟩, hS hx, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
