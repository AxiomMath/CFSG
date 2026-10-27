module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreGrp
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBraid

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {Q : Type*} [Group Q] [Finite Q]

@[expose] def deltaSet (Ob : Subgroup Q) (vb : Q) : Set Q := {a | ∃ x ∈ Ob, a = x * vb * x⁻¹}

structure SevenEightFrame (Lb Ob : Subgroup Q) (Db : Set Q) (vb : Q) : Prop where
  le : Ob ≤ Lb
  le_normalizer : Lb ≤ Subgroup.normalizer (Ob : Set Q)
  mul_self : ∀ d ∈ Db, d * d = 1
  closure_eq : Subgroup.closure Db = Lb
  mem : vb ∈ Db
  comm : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a * a' = a' * a
  four_le : 4 ≤ (deltaSet Ob vb).ncard
  dichotomy : ∀ d ∈ Db, (∀ a ∈ deltaSet Ob vb, d * a = a * d) ∨
    (∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1)
  exists_pow_three : ∃ d ∈ Db, ∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1

private theorem seven_eight_core_q_braid {a d : Q} (ha : a * a = 1) (hd : d * d = 1)
    (h3 : (a * d) ^ 3 = 1) : a * d * a = d * a * d := by
  have hcube : a * d * a * d * a * d = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using h3
  have key : (a * d * a * d * a * d) * (d * a * d) = a * d * a := by
    have e1 : (a * d * a * d * a * d) * (d * a * d) = a * d * a * d * a * (d * d) * a * d := by
      group
    have e2 : a * d * a * d * a * a * d = a * d * a * d * (a * a) * d := by group
    have e3 : a * d * a * d * d = a * d * a * (d * d) := by group
    rw [e1, hd, mul_one, e2, ha, mul_one, e3, hd, mul_one]
  calc a * d * a = (a * d * a * d * a * d) * (d * a * d) := key.symm
    _ = 1 * (d * a * d) := by rw [hcube]
    _ = d * a * d := one_mul _

private theorem seven_eight_core_q_mem_Lb_of_mem_Db {Lb Ob : Subgroup Q} {Db : Set Q}
    {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) {d : Q} (hd : d ∈ Db) : d ∈ Lb := by
  rw [← hF.closure_eq]
  exact Subgroup.subset_closure hd

private theorem seven_eight_core_q_vb_mem_Lb {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) : vb ∈ Lb :=
  seven_eight_core_q_mem_Lb_of_mem_Db hF hF.mem

private theorem seven_eight_core_q_vb_mem_delta {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) : vb ∈ deltaSet Ob vb :=
  ⟨1, Ob.one_mem, by rw [one_mul, inv_one, mul_one]⟩

private theorem seven_eight_core_q_vb_mul_self {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) : vb * vb = 1 :=
  hF.mul_self vb hF.mem

private theorem seven_eight_core_q_vb_inv {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) : vb⁻¹ = vb :=
  inv_eq_of_mul_eq_one_right (seven_eight_core_q_vb_mul_self hF)

private theorem seven_eight_core_q_map_conj_eq_self {Xb : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (Xb : Set Q)) :
    Xb.map (MulAut.conj g).toMonoidHom = Xb := by
  have h := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hg
  simpa [MulEquiv.coe_toMonoidHom] using h

private theorem seven_eight_core_q_commutator_conj {Xb : Subgroup Q} {a g : Q}
    (hg : g ∈ Subgroup.normalizer (Xb : Set Q)) :
    ⁅Xb, Subgroup.zpowers (g * a * g⁻¹)⁆ =
      (⁅Xb, Subgroup.zpowers a⁆).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
    seven_eight_core_q_map_conj_eq_self hg]
  show ⁅Xb, Subgroup.zpowers (g * a * g⁻¹)⁆ =
    ⁅Xb, Subgroup.zpowers (MulAut.conj g a)⁆
  rw [MulAut.conj_apply]

private theorem seven_eight_core_q_odd_card {Xb : Subgroup Q} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hXp : IsPGroup p Xb) : Odd (Nat.card Xb) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem seven_eight_core_q_eq_one_of_sq_eq_one {Xb : Subgroup Q} (hodd : Odd (Nat.card Xb))
    {x : Q} (hx : x ∈ Xb) (hx2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h2 : orderOf x ∣ Nat.card Xb := Subgroup.orderOf_dvd_natCard Xb hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)

private theorem seven_eight_core_q_commutator_self_le (Xb : Subgroup Q) : ⁅Xb, Xb⁆ ≤ Xb := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  rw [commutatorElement_def]
  exact Xb.mul_mem (Xb.mul_mem (Xb.mul_mem hg1 hg2) (Xb.inv_mem hg1)) (Xb.inv_mem hg2)

private theorem seven_eight_core_q_commutator_le_of_mem_normalizer {Xb : Subgroup Q} {a : Q}
    (haX : a ∈ Subgroup.normalizer (Xb : Set Q)) : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb := by
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg2
  have hnorm : a ^ n ∈ Subgroup.normalizer (Xb : Set Q) :=
    (Subgroup.normalizer (Xb : Set Q)).zpow_mem haX n
  have hconj : a ^ n * g1⁻¹ * (a ^ n)⁻¹ ∈ Xb :=
    (Subgroup.mem_normalizer_iff.mp hnorm g1⁻¹).mp (Xb.inv_mem hg1)
  have hc : ⁅g1, a ^ n⁆ = g1 * (a ^ n * g1⁻¹ * (a ^ n)⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hc]
  exact Xb.mul_mem hg1 hconj

private theorem seven_eight_core_q_mem_normalizer_of_mem_deltaSet {Lb Ob : Subgroup Q}
    {Db : Set Q} {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) {Xb : Subgroup Q}
    (hX : IsMinCommInvariant Lb Xb vb) {a : Q} (ha : a ∈ deltaSet Ob vb) :
    a ∈ Subgroup.normalizer (Xb : Set Q) := by
  obtain ⟨x, hx, rfl⟩ := ha
  have hxL : x ∈ Lb := hF.le hx
  have hvL : vb ∈ Lb := seven_eight_core_q_vb_mem_Lb hF
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hX.normalizes hxL) (hX.normalizes hvL))
    (Subgroup.inv_mem _ (hX.normalizes hxL))

private theorem seven_eight_core_q_conj_mem_commutator {Xb : Subgroup Q} {a a' g : Q}
    (hg : g ∈ Subgroup.normalizer (Xb : Set Q)) (hga : g * a * g⁻¹ = a') {m : Q}
    (hm : m ∈ ⁅Xb, Subgroup.zpowers a⁆) :
    g * m * g⁻¹ ∈ ⁅Xb, Subgroup.zpowers a'⁆ := by
  have h := seven_eight_core_q_commutator_conj (Xb := Xb) (a := a) (g := g) hg
  rw [hga] at h
  rw [h]
  simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hm

private theorem seven_eight_core_q_mem_normalizer_commutator_of_commute {Xb : Subgroup Q}
    {a g : Q} (hg : g ∈ Subgroup.normalizer (Xb : Set Q)) (hcomm : g * a = a * g) :
    g ∈ Subgroup.normalizer (⁅Xb, Subgroup.zpowers a⁆ : Subgroup Q) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hga : g * a * g⁻¹ = a := by rw [hcomm]; group
  have h := seven_eight_core_q_commutator_conj (Xb := Xb) (a := a) (g := g) hg
  rw [hga] at h
  simpa [MulEquiv.coe_toMonoidHom] using h.symm

private theorem seven_eight_core_q_map_commute {M : Subgroup Q} {f : Q →* Q}
    (hab : ∀ m ∈ M, ∀ m' ∈ M, m * m' = m' * m) :
    ∀ m ∈ M.map f, ∀ m' ∈ M.map f, m * m' = m' * m := by
  rintro m ⟨m₀, hm₀, rfl⟩ m' ⟨m'₀, hm'₀, rfl⟩
  rw [← map_mul, ← map_mul, hab m₀ hm₀ m'₀ hm'₀]

theorem SevenEightFrame.mul_self_and_mem_of_mem_deltaSet {Lb Ob : Subgroup Q} {Db : Set Q}
    {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) {a : Q} (ha : a ∈ deltaSet Ob vb) :
    a * a = 1 ∧ a ∈ Lb := by
  obtain ⟨x, hx, rfl⟩ := ha
  have hxL : x ∈ Lb := hF.le hx
  have hvL : vb ∈ Lb := seven_eight_core_q_vb_mem_Lb hF
  have hv2 : vb * vb = 1 := seven_eight_core_q_vb_mul_self hF
  constructor
  · calc (x * vb * x⁻¹) * (x * vb * x⁻¹) = x * (vb * vb) * x⁻¹ := by group
      _ = 1 := by rw [hv2]; group
  · exact Lb.mul_mem (Lb.mul_mem hxL hvL) (Lb.inv_mem hxL)

theorem SevenEightFrame.mul_mem_of_mem_deltaSet {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) {a a' : Q} (ha : a ∈ deltaSet Ob vb)
    (ha' : a' ∈ deltaSet Ob vb) : a * a' ∈ Ob := by
  obtain ⟨x, hx, rfl⟩ := ha
  obtain ⟨x', hx', rfl⟩ := ha'
  have hvL : vb ∈ Lb := seven_eight_core_q_vb_mem_Lb hF
  have hv2 : vb * vb = 1 := seven_eight_core_q_vb_mul_self hF
  have hvinv : vb⁻¹ = vb := seven_eight_core_q_vb_inv hF
  have hbn : vb ∈ Subgroup.normalizer (Ob : Set Q) := hF.le_normalizer hvL
  have ho1 : vb * x⁻¹ * vb⁻¹ ∈ Ob :=
    (Subgroup.mem_normalizer_iff.mp hbn x⁻¹).mp (Ob.inv_mem hx)
  have ho2 : x' * (vb * x'⁻¹ * vb⁻¹) ∈ Ob :=
    Ob.mul_mem hx' ((Subgroup.mem_normalizer_iff.mp hbn x'⁻¹).mp (Ob.inv_mem hx'))
  have ho3 : vb * (x' * (vb * x'⁻¹ * vb⁻¹)) * vb⁻¹ ∈ Ob :=
    (Subgroup.mem_normalizer_iff.mp hbn _).mp ho2
  have hprod : x * (vb * x⁻¹ * vb⁻¹) * (vb * (x' * (vb * x'⁻¹ * vb⁻¹)) * vb⁻¹) ∈ Ob :=
    Ob.mul_mem (Ob.mul_mem hx ho1) ho3
  have key : (x * vb * x⁻¹) * (x' * vb * x'⁻¹) =
      x * (vb * x⁻¹ * vb⁻¹) * (vb * (x' * (vb * x'⁻¹ * vb⁻¹)) * vb⁻¹) := by
    rw [hvinv]
    have e1 : x * (vb * x⁻¹ * vb) * (vb * (x' * (vb * x'⁻¹ * vb)) * vb) =
        x * vb * x⁻¹ * (vb * vb) * x' * vb * x'⁻¹ * (vb * vb) := by group
    rw [e1, hv2]
    group
  rw [key]
  exact hprod

theorem SevenEightFrame.exists_conj_eq_of_pow_three {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) {d : Q} (hd : d ∈ Db)
    (h3 : ∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1) : ∃ y ∈ Lb, d = y * vb * y⁻¹ := by
  have hvL : vb ∈ Lb := seven_eight_core_q_vb_mem_Lb hF
  have hdL : d ∈ Lb := seven_eight_core_q_mem_Lb_of_mem_Db hF hd
  have hv2 : vb * vb = 1 := seven_eight_core_q_vb_mul_self hF
  have hd2 : d * d = 1 := hF.mul_self d hd
  have hbraid : vb * d * vb = d * vb * d :=
    seven_eight_core_q_braid hv2 hd2 (h3 vb (seven_eight_core_q_vb_mem_delta hF))
  have hvdinv : (vb * d)⁻¹ = d * vb := by
    rw [mul_inv_rev, seven_eight_core_q_vb_inv hF, inv_eq_of_mul_eq_one_right hd2]
  refine ⟨vb * d, Lb.mul_mem hvL hdL, ?_⟩
  have hfinal : (vb * d) * vb * (d * vb) = d := by
    calc (vb * d) * vb * (d * vb) = vb * (d * vb * d) * vb := by group
      _ = vb * (vb * d * vb) * vb := by rw [← hbraid]
      _ = (vb * vb) * d * (vb * vb) := by group
      _ = d := by rw [hv2, one_mul, mul_one]
  calc d = (vb * d) * vb * (d * vb) := hfinal.symm
    _ = (vb * d) * vb * (vb * d)⁻¹ := by rw [hvdinv]

theorem SevenEightFrame.ncard_conj_le {Lb Ob : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) {d : Q} (hd : d ∈ Db)
    (h3 : ∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1) :
    {e : Q | ∃ o ∈ Ob, e = o * d * o⁻¹}.ncard ≤ (deltaSet Ob vb).ncard := by
  obtain ⟨y, hyL, hd_eq⟩ := hF.exists_conj_eq_of_pow_three hd h3
  have hyn : y ∈ Subgroup.normalizer (Ob : Set Q) := hF.le_normalizer hyL
  have hyinvn : y⁻¹ ∈ Subgroup.normalizer (Ob : Set Q) :=
    (Subgroup.normalizer (Ob : Set Q)).inv_mem hyn
  have hS_eq : {e : Q | ∃ o ∈ Ob, e = o * d * o⁻¹} =
      (fun a => y * a * y⁻¹) '' (deltaSet Ob vb) := by
    ext e
    constructor
    · rintro ⟨o, ho, rfl⟩
      have ho' : y⁻¹ * o * y ∈ Ob := by
        simpa using (Subgroup.mem_normalizer_iff.mp hyinvn o).mp ho
      refine ⟨(y⁻¹ * o * y) * vb * (y⁻¹ * o * y)⁻¹, ⟨_, ho', rfl⟩, ?_⟩
      rw [hd_eq]
      group
    · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyn x).mp hx, ?_⟩
      rw [hd_eq]
      group
  have hinj : Function.Injective (fun a => y * a * y⁻¹) := by
    intro a b hab
    have h1 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
    have h2 : y⁻¹ * (y * b * y⁻¹) * y = b := by group
    have hab' : y * a * y⁻¹ = y * b * y⁻¹ := hab
    calc a = y⁻¹ * (y * a * y⁻¹) * y := h1.symm
      _ = y⁻¹ * (y * b * y⁻¹) * y := by rw [hab']
      _ = b := h2
  rw [hS_eq, Set.ncard_image_of_injective _ hinj]

theorem SevenEightFrame.commute_of_mem_commutator_zpowers {Lb Ob Xb : Subgroup Q} {Db : Set Q}
    {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) (hX : IsMinCommInvariant Lb Xb vb) {p : ℕ}
    (hp : p.Prime) (hXp : IsPGroup p Xb)
    (hinf : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥)
    {a : Q} (ha : a ∈ deltaSet Ob vb) :
    ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a⁆, m * m' = m' * m := by
  intro m hm m' hm'
  have hfoura : 1 < (deltaSet Ob vb).ncard := lt_of_lt_of_le (by norm_num) hF.four_le
  obtain ⟨a', ha', hne'⟩ := Set.exists_ne_of_one_lt_ncard (s := deltaSet Ob vb) hfoura a
  have hne : a ≠ a' := hne'.symm
  have ha2 : a * a = 1 := (hF.mul_self_and_mem_of_mem_deltaSet ha).1
  have ha'2 : a' * a' = 1 := (hF.mul_self_and_mem_of_mem_deltaSet ha').1
  obtain ⟨d₀, hd₀D, hd₀⟩ := hF.exists_pow_three
  have hd₀L : d₀ ∈ Lb := seven_eight_core_q_mem_Lb_of_mem_Db hF hd₀D
  have hd₀2 : d₀ * d₀ = 1 := hF.mul_self d₀ hd₀D
  have hbraid₀ : a * d₀ * a = d₀ * a * d₀ := seven_eight_core_q_braid ha2 hd₀2 (hd₀ a ha)
  have hbraid' : a' * d₀ * a' = d₀ * a' * d₀ := seven_eight_core_q_braid ha'2 hd₀2 (hd₀ a' ha')
  set z : Q := d₀ * a' * a * d₀ with hzdef
  have hzL : z ∈ Lb :=
    Lb.mul_mem (Lb.mul_mem (Lb.mul_mem hd₀L (hF.mul_self_and_mem_of_mem_deltaSet ha').2)
      (hF.mul_self_and_mem_of_mem_deltaSet ha).2) hd₀L
  have hzinv : z⁻¹ = d₀ * a * a' * d₀ := by
    rw [hzdef]
    have e : (d₀ * a' * a * d₀)⁻¹ = d₀⁻¹ * a⁻¹ * a'⁻¹ * d₀⁻¹ := by group
    rw [e, inv_eq_of_mul_eq_one_right hd₀2, inv_eq_of_mul_eq_one_right ha2,
      inv_eq_of_mul_eq_one_right ha'2]
  have hza : z * a * z⁻¹ = a' := by
    rw [hzdef, hzinv]
    have s1 : d₀ * a' * a * d₀ * a * (d₀ * a * a' * d₀)
        = d₀ * a' * (a * d₀ * a) * d₀ * a * a' * d₀ := by group
    rw [s1, hbraid₀]
    have t2 : d₀ * a' * (d₀ * a * d₀) * d₀ * a * a' * d₀
        = d₀ * a' * d₀ * a * (d₀ * d₀) * a * a' * d₀ := by group
    rw [t2, hd₀2, mul_one]
    have s2 : d₀ * a' * d₀ * a * a * a' * d₀ = d₀ * a' * d₀ * (a * a) * a' * d₀ := by
      group
    rw [s2, ha2, mul_one]
    have s3 : d₀ * a' * d₀ * a' * d₀ = d₀ * (a' * d₀ * a') * d₀ := by group
    rw [s3, hbraid']
    have s4 : d₀ * (d₀ * a' * d₀) * d₀ = (d₀ * d₀) * a' * (d₀ * d₀) := by group
    rw [s4, hd₀2, one_mul, mul_one]
  have hzn : z ∈ Subgroup.normalizer (Xb : Set Q) := hX.normalizes hzL
  have haXn : a ∈ Subgroup.normalizer (Xb : Set Q) :=
    seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX ha
  have hMAX : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb :=
    seven_eight_core_q_commutator_le_of_mem_normalizer haXn
  have hzcent : z ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
    have hd₀c : d₀ ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
      obtain ⟨y, hyL, rfl⟩ := hF.exists_conj_eq_of_pow_three hd₀D hd₀
      exact hX.conj_mem_centralizer_commutator hp hXp hyL
    have hac : a ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
      obtain ⟨x, hx, rfl⟩ := ha
      exact hX.conj_mem_centralizer_commutator hp hXp (hF.le hx)
    have ha'c : a' ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
      obtain ⟨x, hx, rfl⟩ := ha'
      exact hX.conj_mem_centralizer_commutator hp hXp (hF.le hx)
    have h1 : d₀ * a' ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) :=
      Subgroup.mul_mem _ hd₀c ha'c
    have h2 : d₀ * a' * a ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) :=
      Subgroup.mul_mem _ h1 hac
    exact Subgroup.mul_mem _ h2 hd₀c
  have hcM : ⁅m, m'⁆ ∈ ⁅Xb, Subgroup.zpowers a⁆ := by
    rw [commutatorElement_def]
    exact (⁅Xb, Subgroup.zpowers a⁆).mul_mem
      ((⁅Xb, Subgroup.zpowers a⁆).mul_mem
        ((⁅Xb, Subgroup.zpowers a⁆).mul_mem hm hm')
        ((⁅Xb, Subgroup.zpowers a⁆).inv_mem hm))
      ((⁅Xb, Subgroup.zpowers a⁆).inv_mem hm')
  have hcX : ⁅m, m'⁆ ∈ (⁅Xb, Xb⁆ : Subgroup Q) :=
    Subgroup.commutator_mem_commutator (hMAX hm) (hMAX hm')
  have hzc : z * ⁅m, m'⁆ * z⁻¹ = ⁅m, m'⁆ := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzcent) ⁅m, m'⁆ hcX
    rw [← hcomm]; group
  have hmem1 : z * m * z⁻¹ ∈ ⁅Xb, Subgroup.zpowers a'⁆ :=
    seven_eight_core_q_conj_mem_commutator hzn hza hm
  have hmem2 : z * m' * z⁻¹ ∈ ⁅Xb, Subgroup.zpowers a'⁆ :=
    seven_eight_core_q_conj_mem_commutator hzn hza hm'
  have hcM' : z * ⁅m, m'⁆ * z⁻¹ ∈ ⁅Xb, Subgroup.zpowers a'⁆ := by
    have hid : z * ⁅m, m'⁆ * z⁻¹ = ⁅z * m * z⁻¹, z * m' * z⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [hid]
    exact (⁅Xb, Subgroup.zpowers a'⁆).mul_mem
      ((⁅Xb, Subgroup.zpowers a'⁆).mul_mem
        ((⁅Xb, Subgroup.zpowers a'⁆).mul_mem hmem1 hmem2)
        ((⁅Xb, Subgroup.zpowers a'⁆).inv_mem hmem1))
      ((⁅Xb, Subgroup.zpowers a'⁆).inv_mem hmem2)
  have hbot : ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥ := hinf a ha a' ha' hne
  have hc_bot : ⁅m, m'⁆ ∈ (⊥ : Subgroup Q) := by
    have hmem : ⁅m, m'⁆ ∈ ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ := by
      refine ⟨hcM, ?_⟩
      rwa [← hzc]
    rwa [hbot] at hmem
  rw [Subgroup.mem_bot] at hc_bot
  exact commutatorElement_eq_one_iff_mul_comm.mp hc_bot

theorem SevenEightFrame.commute_of_mem_commutator_zpowers_of_ne {Lb Ob Xb : Subgroup Q}
    {Db : Set Q} {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) (hX : IsMinCommInvariant Lb Xb vb)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p Xb)
    (hcl : ∀ x ∈ Xb, ∀ y ∈ Xb, ∀ z ∈ Xb, ⁅⁅x, y⁆, z⁆ = 1)
    (hcent : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a')
    (hinf : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥)
    {a a' : Q} (ha : a ∈ deltaSet Ob vb) (ha' : a' ∈ deltaSet Ob vb) (hne : a ≠ a') :
    ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a'⁆, m * m' = m' * m := by
  intro m hm m' hm'
  have ha2 : a * a = 1 := (hF.mul_self_and_mem_of_mem_deltaSet ha).1
  have haXn : a ∈ Subgroup.normalizer (Xb : Set Q) :=
    seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX ha
  have ha'Xn : a' ∈ Subgroup.normalizer (Xb : Set Q) :=
    seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX ha'
  have hMAX : ⁅Xb, Subgroup.zpowers a⁆ ≤ Xb :=
    seven_eight_core_q_commutator_le_of_mem_normalizer haXn
  have hMA'X : ⁅Xb, Subgroup.zpowers a'⁆ ≤ Xb :=
    seven_eight_core_q_commutator_le_of_mem_normalizer ha'Xn
  have hcX : ⁅m, m'⁆ ∈ ⁅Xb, Xb⁆ :=
    Subgroup.commutator_mem_commutator (hMAX hm) (hMA'X hm')
  have hcXb : ⁅m, m'⁆ ∈ Xb := seven_eight_core_q_commutator_self_le Xb hcX
  have hacent : a ∈ Subgroup.centralizer ((⁅Xb, Xb⁆ : Subgroup Q) : Set Q) := by
    obtain ⟨x, hx, rfl⟩ := ha
    exact hX.conj_mem_centralizer_commutator hp hXp (hF.le hx)
  have hac : ⁅m, m'⁆ * a = a * ⁅m, m'⁆ :=
    Subgroup.mem_centralizer_iff.mp hacent ⁅m, m'⁆ hcX
  have hinv_m : a * m * a⁻¹ = m⁻¹ :=
    conj_eq_inv_of_mem_commutator_zpowers ha2
      (hF.commute_of_mem_commutator_zpowers hX hp hXp hinf ha) m hm
  have hfix' : a * m' * a⁻¹ = m' := by
    have h := hcent a' ha' a ha hne.symm m' hm'
    rw [h]; group
  have hc_eq : ⁅m, m'⁆ = ⁅m⁻¹, m'⁆ := by
    calc ⁅m, m'⁆ = a * ⁅m, m'⁆ * a⁻¹ := by rw [← hac]; group
      _ = ⁅a * m * a⁻¹, a * m' * a⁻¹⁆ := by rw [commutatorElement_def]; group
      _ = ⁅m⁻¹, m'⁆ := by rw [hinv_m, hfix']
  have hcm : ⁅m, m'⁆ * m = m * ⁅m, m'⁆ :=
    commutatorElement_eq_one_iff_mul_comm.mp (hcl m (hMAX hm) m' (hMA'X hm') m (hMAX hm))
  have hcinv_m : ⁅m, m'⁆⁻¹ * m = m * ⁅m, m'⁆⁻¹ := by
    calc ⁅m, m'⁆⁻¹ * m = ⁅m, m'⁆⁻¹ * m * ⁅m, m'⁆ * ⁅m, m'⁆⁻¹ := by group
      _ = ⁅m, m'⁆⁻¹ * (m * ⁅m, m'⁆) * ⁅m, m'⁆⁻¹ := by group
      _ = ⁅m, m'⁆⁻¹ * (⁅m, m'⁆ * m) * ⁅m, m'⁆⁻¹ := by rw [← hcm]
      _ = m * ⁅m, m'⁆⁻¹ := by group
  have hid : ⁅m⁻¹, m'⁆ = m⁻¹ * ⁅m, m'⁆⁻¹ * m := by
    rw [commutatorElement_def]; group
  have hc_eq_inv : ⁅m, m'⁆ = ⁅m, m'⁆⁻¹ := by
    calc ⁅m, m'⁆ = ⁅m⁻¹, m'⁆ := hc_eq
      _ = m⁻¹ * ⁅m, m'⁆⁻¹ * m := hid
      _ = ⁅m, m'⁆⁻¹ := by
        rw [show m⁻¹ * ⁅m, m'⁆⁻¹ * m = m⁻¹ * (⁅m, m'⁆⁻¹ * m) by group, hcinv_m]
        group
  have hodd : Odd (Nat.card Xb) := seven_eight_core_q_odd_card hp hp2 hXp
  have hc2 : ⁅m, m'⁆ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [hc_eq_inv]
    exact inv_mul_cancel _
  have hc1 : ⁅m, m'⁆ = 1 := seven_eight_core_q_eq_one_of_sq_eq_one hodd hcXb hc2
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

theorem SevenEightFrame.commutator_zpowers_le_iSup {Lb Ob Xb : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) (hX : IsMinCommInvariant Lb Xb vb) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p Xb)
    (hcent : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a')
    (hinf : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥)
    {d : Q} (hd : d ∈ Db) (h3 : ∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1) :
    ⁅Xb, Subgroup.zpowers d⁆ ≤ ⨆ a : ↥(deltaSet Ob vb), ⁅Xb, Subgroup.zpowers (a : Q)⁆ := by
  have hodd : Odd (Nat.card Xb) := seven_eight_core_q_odd_card hp hp2 hXp
  have hvbΔ : vb ∈ deltaSet Ob vb := seven_eight_core_q_vb_mem_delta hF
  have hι : 4 ≤ Nat.card ↥(deltaSet Ob vb) := by
    rw [Nat.card_coe_set_eq]
    exact hF.four_le
  have hcommι : ∀ i j : ↥(deltaSet Ob vb), (i : Q) * (j : Q) = (j : Q) * (i : Q) :=
    fun i j => hF.comm (i : Q) i.2 (j : Q) j.2
  have hS : {e : Q | ∃ o ∈ Ob, e = o * d * o⁻¹}.ncard ≤ Nat.card ↥(deltaSet Ob vb) := by
    rw [Nat.card_coe_set_eq]
    exact hF.ncard_conj_le hd h3
  have hmem : ∀ i j : ↥(deltaSet Ob vb), i ≠ j →
      ((i : Q) * (j : Q))⁻¹ * d * ((i : Q) * (j : Q)) ∈
        {e : Q | ∃ o ∈ Ob, e = o * d * o⁻¹} := by
    intro i j _
    have ho : (i : Q) * (j : Q) ∈ Ob := hF.mul_mem_of_mem_deltaSet i.2 j.2
    exact ⟨((i : Q) * (j : Q))⁻¹, Ob.inv_mem ho, by simp⟩
  obtain ⟨i, f, hf, hfb⟩ := exists_mul_commute_of_ncard_le hι
    (fun x : ↥(deltaSet Ob vb) => (x : Q)) hcommι d hS hmem
  have hbab : ∀ m ∈ ⁅Xb, Subgroup.zpowers d⁆,
      ∀ m' ∈ ⁅Xb, Subgroup.zpowers d⁆, m * m' = m' * m := by
    obtain ⟨y, hyL, rfl⟩ := hF.exists_conj_eq_of_pow_three hd h3
    have hMeq := seven_eight_core_q_commutator_conj (Xb := Xb) (a := vb) (g := y)
      (hX.normalizes hyL)
    rw [hMeq]
    exact seven_eight_core_q_map_commute
      (hF.commute_of_mem_commutator_zpowers hX hp hXp hinf hvbΔ)
  exact commutator_zpowers_le_iSup_of_pow_three hodd
    (fun x : ↥(deltaSet Ob vb) => (x : Q))
    (fun i => (hF.mul_self_and_mem_of_mem_deltaSet i.2).1) hcommι
    (fun i => seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX i.2)
    (fun i j hij => hcent (j : Q) j.2 (i : Q) i.2 (fun h => hij (Subtype.ext h.symm)))
    (fun i => hF.commute_of_mem_commutator_zpowers hX hp hXp hinf i.2)
    (hF.mul_self d hd) (hX.normalizes (seven_eight_core_q_mem_Lb_of_mem_Db hF hd))
    hbab (h3 (i : Q) i.2) hf hfb

theorem SevenEightFrame.isMulCommutative_and_iSup_eq {Lb Ob Xb : Subgroup Q} {Db : Set Q}
    {vb : Q} (hF : SevenEightFrame Lb Ob Db vb) (hX : IsMinCommInvariant Lb Xb vb) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hXp : IsPGroup p Xb)
    (hcl : ∀ x ∈ Xb, ∀ y ∈ Xb, ∀ z ∈ Xb, ⁅⁅x, y⁆, z⁆ = 1)
    (hcent : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a')
    (hinf : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥) :
    (∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x) ∧
      (⨆ a : ↥(deltaSet Ob vb), ⁅Xb, Subgroup.zpowers (a : Q)⁆) = Xb := by
  have hodd : Odd (Nat.card Xb) := seven_eight_core_q_odd_card hp hp2 hXp
  have hvbΔ : vb ∈ deltaSet Ob vb := seven_eight_core_q_vb_mem_delta hF
  set U : Subgroup Q := ⨆ a : ↥(deltaSet Ob vb), ⁅Xb, Subgroup.zpowers (a : Q)⁆ with hU
  have hnormMa : ∀ a : ↥(deltaSet Ob vb),
      (a : Q) ∈ Subgroup.normalizer (Xb : Set Q) :=
    fun a => seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX a.2
  have hMaX : ∀ a : ↥(deltaSet Ob vb), ⁅Xb, Subgroup.zpowers (a : Q)⁆ ≤ Xb :=
    fun a => seven_eight_core_q_commutator_le_of_mem_normalizer (hnormMa a)
  have hUX : U ≤ Xb := by
    rw [hU]
    exact iSup_le hMaX
  have hDnorm : ∀ d ∈ Db, d ∈ Subgroup.normalizer (U : Set Q) := by
    intro d hd
    rcases hF.dichotomy d hd with hcom | hbraid
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [hU, Subgroup.map_iSup]
      refine iSup_congr fun a => ?_
      have h := seven_eight_core_q_mem_normalizer_commutator_of_commute
        (hX.normalizes (seven_eight_core_q_mem_Lb_of_mem_Db hF hd)) (hcom (a : Q) a.2)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
      simpa [MulEquiv.coe_toMonoidHom] using h
    · have hDU : ⁅Xb, Subgroup.zpowers d⁆ ≤ U := by
        rw [hU]
        exact hF.commutator_zpowers_le_iSup hX hp hp2 hXp hcent hinf hd hbraid
      have hfwd : ∀ v ∈ U, d * v * d⁻¹ ∈ U := by
        intro v hv
        have hvX : v ∈ Xb := hUX hv
        have hcomm : ⁅v, d⁆ ∈ ⁅Xb, Subgroup.zpowers d⁆ :=
          Subgroup.commutator_mem_commutator hvX (Subgroup.mem_zpowers d)
        have hmem : ⁅v, d⁆ ∈ U := hDU hcomm
        have hdU : ⁅d, v⁆ ∈ U := by
          rw [← commutatorElement_inv]
          exact U.inv_mem hmem
        have hdecomp : d * v * d⁻¹ = ⁅d, v⁆ * v := by
          rw [commutatorElement_def]; group
        rw [hdecomp]
        exact U.mul_mem hdU hv
      have hdinv : d⁻¹ * d⁻¹ = 1 := by
        rw [inv_eq_of_mul_eq_one_right (hF.mul_self d hd), hF.mul_self d hd]
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        exact hfwd u hu
      · intro hu
        have h1 := hfwd (d * u * d⁻¹) hu
        have heq : d * (d * u * d⁻¹) * d⁻¹ = u := by
          calc d * (d * u * d⁻¹) * d⁻¹ = (d * d) * u * (d⁻¹ * d⁻¹) := by group
            _ = u := by rw [hF.mul_self d hd, hdinv, one_mul, mul_one]
        rwa [heq] at h1
  have hLnorm : Lb ≤ Subgroup.normalizer (U : Set Q) := by
    rw [← hF.closure_eq]
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem x hx => exact hDnorm x hx
    | one => exact (Subgroup.normalizer (U : Set Q)).one_mem
    | mul x y hx hy ihx ihy => exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => exact Subgroup.inv_mem _ ih
  have hUeq : U = Xb := by
    by_contra hne
    have hlt : U < Xb := lt_of_le_of_ne hUX hne
    have hmin : ⁅U, Subgroup.zpowers vb⁆ = ⊥ := hX.minimal U hlt hLnorm
    have hMle : ⁅Xb, Subgroup.zpowers vb⁆ ≤ U := by
      rw [hU]
      exact le_iSup (fun a : ↥(deltaSet Ob vb) => ⁅Xb, Subgroup.zpowers (a : Q)⁆)
        ⟨vb, hvbΔ⟩
    have hcentU : U ≤ Subgroup.centralizer (Subgroup.zpowers vb : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmin
    have hMbot : ⁅Xb, Subgroup.zpowers vb⁆ = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have hmU : m ∈ U := hMle hm
      have hcomm : vb * m = m * vb :=
        (Subgroup.mem_centralizer_iff.mp (hcentU hmU)) vb (Subgroup.mem_zpowers vb)
      have hinv : vb * m * vb⁻¹ = m⁻¹ :=
        conj_eq_inv_of_mem_commutator_zpowers (seven_eight_core_q_vb_mul_self hF)
          (hF.commute_of_mem_commutator_zpowers hX hp hXp hinf hvbΔ) m hm
      have hminv : m⁻¹ = m := by rw [← hinv, hcomm]; group
      have hsq : m ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hminv]
        exact inv_mul_cancel m
      have hm1 : m = 1 := seven_eight_core_q_eq_one_of_sq_eq_one hodd (hUX hmU) hsq
      rwa [Subgroup.mem_bot]
    exact hX.ne_bot hMbot
  have habel : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx
    refine Subgroup.iSup_induction
      (C := fun z => ∀ y ∈ U, z * y = y * z)
      (fun a : ↥(deltaSet Ob vb) => ⁅Xb, Subgroup.zpowers (a : Q)⁆) hx ?_ ?_ ?_
    · intro a xa hxa y hy
      refine Subgroup.iSup_induction
        (C := fun z => xa * z = z * xa)
        (fun b : ↥(deltaSet Ob vb) => ⁅Xb, Subgroup.zpowers (b : Q)⁆) hy ?_ ?_ ?_
      · intro b yb hyb
        by_cases hab : a = b
        · subst hab
          exact hF.commute_of_mem_commutator_zpowers hX hp hXp hinf a.2 xa hxa yb hyb
        · exact hF.commute_of_mem_commutator_zpowers_of_ne hX hp hp2 hXp hcl hcent hinf
            a.2 b.2 (fun h => hab (Subtype.ext h)) xa hxa yb hyb
      · rw [mul_one, one_mul]
      · intro y1 y2 h1 h2
        calc xa * (y1 * y2) = (xa * y1) * y2 := (mul_assoc _ _ _).symm
          _ = (y1 * xa) * y2 := by rw [h1]
          _ = y1 * (xa * y2) := mul_assoc _ _ _
          _ = y1 * (y2 * xa) := by rw [h2]
          _ = (y1 * y2) * xa := (mul_assoc _ _ _).symm
    · intro y hy
      rw [one_mul, mul_one]
    · intro x1 x2 h1 h2
      intro y hy
      calc (x1 * x2) * y = x1 * (x2 * y) := mul_assoc _ _ _
        _ = x1 * (y * x2) := by rw [h2 y hy]
        _ = (x1 * y) * x2 := (mul_assoc _ _ _).symm
        _ = (y * x1) * x2 := by rw [h1 y hy]
        _ = y * (x1 * x2) := mul_assoc _ _ _
  refine ⟨?_, hUeq⟩
  intro x hx y hy
  rw [← hUeq] at hx hy
  exact habel x hx y hy

theorem SevenEightFrame.false_of_map_conj_eq {Lb Ob Xb : Subgroup Q} {Db : Set Q} {vb : Q}
    (hF : SevenEightFrame Lb Ob Db vb) (hX : IsMinCommInvariant Lb Xb vb)
    (hodd : Odd (Nat.card Xb)) (hXab : ∀ x ∈ Xb, ∀ y ∈ Xb, x * y = y * x)
    (hcent : ∀ a ∈ deltaSet Ob vb, ∀ a' ∈ deltaSet Ob vb, a ≠ a' →
      ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a')
    {d : Q} (hd : d * d = 1) (h3 : ∀ a ∈ deltaSet Ob vb, (a * d) ^ 3 = 1)
    {k l : ↥(deltaSet Ob vb)}
    (hmap : (⨆ j : ↥(deltaSet Ob vb), ⨆ (_ : j ≠ k), ⁅Xb, Subgroup.zpowers (j : Q)⁆).map
        (MulAut.conj d).toMonoidHom =
      ⨆ j : ↥(deltaSet Ob vb), ⨆ (_ : j ≠ l), ⁅Xb, Subgroup.zpowers (j : Q)⁆) : False := by
  have h2 : ({k, l} : Set ↥(deltaSet Ob vb)).ncard ≤ 2 := by
    have h := Set.ncard_insert_le k ({l} : Set ↥(deltaSet Ob vb))
    rw [Set.ncard_singleton] at h
    simpa using h
  have hlt : ({k, l} : Set ↥(deltaSet Ob vb)).ncard <
      (Set.univ : Set ↥(deltaSet Ob vb)).ncard := by
    rw [Set.ncard_univ]
    have h4 : 2 < Nat.card ↥(deltaSet Ob vb) := by
      rw [Nat.card_coe_set_eq]
      exact lt_of_lt_of_le (by norm_num) hF.four_le
    exact lt_of_le_of_lt h2 h4
  obtain ⟨j, -, hjnot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hjk : j ≠ k := by
    intro h
    exact hjnot (by simp [h])
  have hjl : j ≠ l := by
    intro h
    exact hjnot (by simp [h])
  apply _root_.CFSG.LocalAnalysis.WeakClosure81.false_of_map_conj_eq (Xb := Xb)
    (ι := ↥(deltaSet Ob vb)) (b := d) (k := k) (l := l) (j := j) hodd
    (fun x : ↥(deltaSet Ob vb) => (x : Q))
    (fun i => (hF.mul_self_and_mem_of_mem_deltaSet i.2).1)
    (fun i => seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX i.2)
    (fun i j hij => hcent (j : Q) j.2 (i : Q) i.2 (fun h => hij (Subtype.ext h.symm)))
    (fun i m hm m' hm' =>
      hXab m (seven_eight_core_q_commutator_le_of_mem_normalizer
        (seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX i.2) hm)
      m' (seven_eight_core_q_commutator_le_of_mem_normalizer
        (seven_eight_core_q_mem_normalizer_of_mem_deltaSet hF hX i.2) hm'))
    hd (fun i => h3 (i : Q) i.2) hmap hjk hjl ?_
  obtain ⟨x, hx, hxeq⟩ := j.2
  have h := hX.commutator_conj_ne_bot (l := x) (hF.le hx)
  rw [← hxeq] at h
  exact h


end CFSG.LocalAnalysis.WeakClosure81
