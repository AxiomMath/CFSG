module

public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {D : Set G}

theorem exists_zpow_conj_eq {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hodd : Odd (orderOf (x * y))) (i : ℤ) :
    ∃ j : ℤ, (x * y) ^ j * x * ((x * y) ^ j)⁻¹ = (x * y) ^ i * x := by
  obtain ⟨k, hk⟩ := hodd
  have hpow : (x * y) ^ ((2 * k + 1 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hk, pow_orderOf_eq_one]
  refine ⟨i * (k + 1), ?_⟩
  have hc := mul_zpow_mul_eq_zpow_neg_mul hx hy (-(i * (k + 1)))
  rw [neg_neg] at hc
  have e : i * (k + 1) + i * (k + 1) = ((2 * k + 1 : ℕ) : ℤ) * i + i := by push_cast; ring
  calc (x * y) ^ (i * (k + 1)) * x * ((x * y) ^ (i * (k + 1)))⁻¹
      = (x * y) ^ (i * (k + 1)) * (x * (x * y) ^ (-(i * (k + 1)))) := by
        rw [zpow_neg]; group
    _ = (x * y) ^ (i * (k + 1)) * ((x * y) ^ (i * (k + 1)) * x) := by rw [hc]
    _ = (x * y) ^ (((2 * k + 1 : ℕ) : ℤ) * i + i) * x := by
        rw [← mul_assoc, ← zpow_add, e]
    _ = (x * y) ^ i * x := by rw [zpow_add, zpow_mul, hpow, one_zpow, one_mul]

theorem odd_orderOf_zpow {x : G} (hodd : Odd (orderOf x)) (i : ℤ) : Odd (orderOf (x ^ i)) := by
  refine Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one ?_)
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
    one_zpow]

theorem conj_zpow_eq_inv {t x : G} (h : t * x * t⁻¹ = x⁻¹) (i : ℤ) :
    t * x ^ i * t⁻¹ = (x ^ i)⁻¹ := by
  rw [← conj_zpow, h, inv_zpow]

theorem eq_one_of_mul_self_of_odd {x : G} (h2 : x * x = 1) (hodd : Odd (orderOf x)) : x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h2])
  have h1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem conj_mem_sup {P Q : Subgroup G} {g : G} (hP : ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hQ : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {m : G} (hm : m ∈ P ⊔ Q) : g * m * g⁻¹ ∈ P ⊔ Q := by
  have hle : P ⊔ Q ≤ (P ⊔ Q).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun p hp => Subgroup.mem_sup_left (hP p hp))
      (fun q hq => Subgroup.mem_sup_right (hQ q hq))
  exact hle hm

theorem commute_of_mem_commutator_zpowers (hD : IsOddTransp D) (hN : IsNormalSet D)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) {t : G} (ht : t ∈ D) (htQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    {y : G} (hy : y ∈ ⁅Q, Subgroup.zpowers t⁆) : Commute t y := by
  have hle : ⁅Q, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer {t} := by
    rw [Subgroup.commutator_le]
    intro q hq s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases (mem_zpowers_of_mul_self (hD.mul_self_eq_one ht)).mp hs with rfl | rfl
    · simp
    ·
      have hqt : q * s * q⁻¹ ∈ D := hN q s ht
      have hmem : s⁻¹ * (q * s * q⁻¹) ∈ Q := by
        have := Q.mul_mem (htQ q hq) (Q.inv_mem hq)
        rw [hD.inv_eq ht]
        simpa [mul_assoc, hD.inv_eq ht] using this
      have hc := commute_of_inv_mul_mem_two hD hQ ht hqt hmem
      rw [commutatorElement_def]
      have h2 : Commute s (q * s * q⁻¹ * s⁻¹) := hc.mul_right (Commute.refl s).inv_right
      exact h2.eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem pow_mul_eq_mul_pow_mul {Q₀ Q : Subgroup G} {h w : G} (hQ₀Q : Q₀ ≤ Q) (hwQ : w ∈ Q)
    (hQcomm : ∀ p ∈ Q, ∀ q ∈ Q, Commute p q) (hcomm : ∀ q ∈ Q, ⁅q, h⁻¹⁆ ∈ Q₀) (n : ℕ) :
    ∃ y ∈ Q₀, (h * w) ^ n = h ^ n * (w ^ n * y) := by
  induction n with
  | zero => exact ⟨1, Q₀.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyn⟩ := ih
    have huQ : w ^ n * y ∈ Q := Q.mul_mem (Q.pow_mem hwQ n) (hQ₀Q hy)
    have hy' : ⁅(w ^ n * y)⁻¹, h⁻¹⁆ ∈ Q₀ := hcomm _ (Q.inv_mem huQ)
    refine ⟨y * ⁅(w ^ n * y)⁻¹, h⁻¹⁆, Q₀.mul_mem hy hy', ?_⟩
    have hcw : Commute w (y * ⁅(w ^ n * y)⁻¹, h⁻¹⁆) :=
      hQcomm w hwQ _ (Q.mul_mem (hQ₀Q hy) (hQ₀Q hy'))
    have e1 : h⁻¹ * (w ^ n * y) * h = w ^ n * y * ⁅(w ^ n * y)⁻¹, h⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    calc (h * w) ^ (n + 1) = h ^ n * (w ^ n * y) * (h * w) := by rw [pow_succ, hyn]
      _ = h ^ (n + 1) * (h⁻¹ * (w ^ n * y) * h) * w := by rw [pow_succ]; group
      _ = h ^ (n + 1) * (w ^ n * (y * ⁅(w ^ n * y)⁻¹, h⁻¹⁆ * w)) := by
        rw [e1]
        simp only [mul_assoc]
      _ = h ^ (n + 1) * (w ^ (n + 1) * (y * ⁅(w ^ n * y)⁻¹, h⁻¹⁆)) := by
        rw [← hcw.eq, pow_succ w n, mul_assoc (w ^ n) w]

section SecondKind

variable [Finite G] (hD : IsOddTransp D) (hN : IsNormalSet D) {a b c : G}
  (htri : IsTriangle D a b c) (h4 : orderOf (a * c * b) = 4)
  (hno : ∀ x ∈ D, x ∈ Subgroup.closure {a, b} → IsTriangle D a x c → ¬ IsThirdKind a x c)
include hD hN htri h4 hno

theorem commute_conj_of_secondKind {g : G} (hg : g ∈ Subgroup.closure {a, b}) :
    Commute (a * c) (g * (a * c) * g⁻¹) := by
  have htri0 := htri
  obtain ⟨ha, hc, hb, hac, hcomm, hab, hcb⟩ := htri
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hc
  have hw2 : a * c * (a * c) = 1 := IsTriangle.uv_mul_self hD htri0
  have hoddab : Odd (orderOf (a * b)) := hD.odd_of_not_commute ha hb hab
  have haw : a * (a * c) * a⁻¹ = a * c := by
    rw [hD.inv_eq ha, ← mul_assoc, ha2, one_mul, hcomm.eq]
  have hwD : a * c ∉ D := by
    intro hw
    rcases hD.2 _ hw _ hb with h | h <;> rw [h4] at h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by norm_num)
    · exact absurd h (by decide)
  have hreflD : ∀ i : ℤ, (a * b) ^ i * a ∈ D := by
    intro i
    obtain ⟨j, hj⟩ := exists_zpow_conj_eq ha2 hb2 hoddab i
    rw [← hj]
    exact hN _ _ ha
  have hreflX : ∀ i : ℤ, (a * b) ^ i * a ∈ Subgroup.closure ({a, b} : Set G) := fun i =>
    Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure
      (by simp)) (Subgroup.subset_closure (by simp))) i) (Subgroup.subset_closure (by simp))
  have hrefl : ∀ i : ℤ, (a * b) ^ i * a ≠ a →
      Commute (a * c) ((a * b) ^ i * a * (a * c) * ((a * b) ^ i * a)⁻¹) := by
    intro i hra
    set r := (a * b) ^ i * a with hr
    have hrD : r ∈ D := hreflD i
    set s := a * r with hs
    have hs_eq : s = (a * b) ^ (-i) := by
      rw [hs, hr, ← mul_assoc, mul_zpow_mul_eq_zpow_neg_mul ha2 hb2, mul_assoc, ha2, mul_one]
    have hsodd : Odd (orderOf s) := hs_eq ▸ odd_orderOf_zpow hoddab (-i)
    have hs1 : s ≠ 1 := by
      intro h1
      apply hra
      rw [hs] at h1
      rw [← hD.eq_of_mul_eq_one ha h1]
    have har : ¬ Commute a r := by
      intro hc'
      apply hs1
      refine eq_one_of_mul_self_of_odd ?_ hsodd
      have := (commute_iff_mul_sq_eq_one ha2 (hD.mul_self_eq_one hrD)).mp hc'
      rwa [pow_two] at this
    have hcr : ¬ Commute c r := by
      intro hcr'
      set N := Subgroup.zpowers s with hNdef
      have hab' : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
        rw [hD.inv_eq ha, mul_inv_rev, hD.inv_eq ha, hD.inv_eq hb, ← mul_assoc, ha2, one_mul]
      have hbb' : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
        rw [hD.inv_eq hb, mul_inv_rev, hD.inv_eq ha, hD.inv_eq hb]
        calc b * (a * b) * b = b * a * (b * b) := by group
          _ = b * a := by rw [hb2, mul_one]
      have hsa : a * s * a⁻¹ = s⁻¹ := by rw [hs_eq]; exact conj_zpow_eq_inv hab' _
      have hsb : b * s * b⁻¹ = s⁻¹ := by rw [hs_eq]; exact conj_zpow_eq_inv hbb' _
      have hcs : Commute c s := (hcomm.symm.mul_right hcr')
      have hgenN : ∀ t ∈ ({a, b, c} : Set G), ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
        rintro t (rfl | rfl | rfl) n hn <;> obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        · rw [← conj_zpow, hsa]; exact Subgroup.zpow_mem _ (Subgroup.inv_mem _
            (Subgroup.mem_zpowers _)) _
        · rw [← conj_zpow, hsb]; exact Subgroup.zpow_mem _ (Subgroup.inv_mem _
            (Subgroup.mem_zpowers _)) _
        · rw [(hcs.zpow_right k).eq, mul_inv_cancel_right]; exact Subgroup.zpow_mem _
            (Subgroup.mem_zpowers _) _
      have hT2 : ∀ t ∈ ({a, b, c} : Set G), t * t = 1 := by
        rintro t (rfl | rfl | rfl) <;> assumption
      have hKN : ∀ g ∈ Subgroup.closure ({a, b, c} : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
        fun g hg => conj_mem_of_mem_closure hT2 hgenN hg
      obtain ⟨g₂, hg₂, hg₂e⟩ := hD.exists_conj ha hb hab
      obtain ⟨g₁, hg₁, hg₁e⟩ := hD.exists_conj hb hc (fun h => hcb h.symm)
      have hg₂K : g₂ ∈ Subgroup.closure ({a, b, c} : Set G) :=
        Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp) hg₂
      have hg₁K : g₁ ∈ Subgroup.closure ({a, b, c} : Set G) :=
        Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp) hg₁
      set g := g₁ * g₂ with hgdef
      have hgK : g ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.mul_mem _ hg₁K hg₂K
      have hga : g * a * g⁻¹ = c := by
        rw [hgdef, mul_inv_rev]
        calc g₁ * g₂ * a * (g₂⁻¹ * g₁⁻¹) = g₁ * (g₂ * a * g₂⁻¹) * g₁⁻¹ := by group
          _ = c := by rw [hg₂e, hg₁e]
      have hts : g⁻¹ * s * g ∈ N := by
        have := hKN g⁻¹ (Subgroup.inv_mem _ hgK) s (Subgroup.mem_zpowers s)
        simpa using this
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hts
      have hcomm_ct : Commute c (g⁻¹ * s * g) := hk ▸ hcs.zpow_right k
      have hasa : a * s * a⁻¹ = s := by
        have hac' : a = g⁻¹ * c * g := by rw [← hga]; group
        rw [hac']
        calc g⁻¹ * c * g * s * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * (g * s * g⁻¹) * c⁻¹) * g := by group
          _ = s := by
            have h1 : g * s * g⁻¹ = (g * s * g⁻¹) := rfl
            have hcg : Commute c (g * s * g⁻¹) := by
              have := hKN g hgK s (Subgroup.mem_zpowers s)
              obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp this
              exact hk' ▸ hcs.zpow_right k'
            rw [hcg.eq, mul_inv_cancel_right]
            group
      apply hs1
      refine eq_one_of_mul_self_of_odd ?_ hsodd
      have : s = s⁻¹ := hasa.symm.trans hsa
      calc s * s = s * s⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel s
    have htri' : IsTriangle D a r c := ⟨ha, hc, hrD, hac, hcomm, har, hcr⟩
    have hr4 : orderOf (a * c * r) = 4 := by
      rcases htri'.orderOf_cases hD hN with ⟨hodd, -⟩ | h4' | h3
      · exact absurd (htri'.mul_mem_of_odd hD hN hodd) hwD
      · exact h4'
      · exact absurd h3 (hno r hrD (hreflX i) htri')
    have hr2 := hD.mul_self_eq_one hrD
    have hconj2 : r * (a * c) * r⁻¹ * (r * (a * c) * r⁻¹) = 1 := by
      calc r * (a * c) * r⁻¹ * (r * (a * c) * r⁻¹) = r * (a * c * (a * c)) * r⁻¹ := by group
        _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
    rw [commute_iff_mul_sq_eq_one hw2 hconj2]
    have hsq : ((a * c) * (r * (a * c) * r⁻¹)) ^ 2 = (a * c * r) ^ 4 := by
      rw [hD.inv_eq hrD]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [hsq, ← hr4, pow_orderOf_eq_one]
  obtain ⟨i, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair ha2 hb2 hg
  ·
    have e : (a * b) ^ i * (a * c) * ((a * b) ^ i)⁻¹ =
        (a * b) ^ i * a * (a * c) * ((a * b) ^ i * a)⁻¹ := by
      rw [mul_inv_rev, show (a * b) ^ i * a * (a * c) * (a⁻¹ * ((a * b) ^ i)⁻¹) =
        (a * b) ^ i * (a * (a * c) * a⁻¹) * ((a * b) ^ i)⁻¹ by group, haw]
    rw [e]
    by_cases hra : (a * b) ^ i * a = a
    · rw [hra, haw]
    · exact hrefl i hra
  · by_cases hra : (a * b) ^ i * a = a
    · rw [hra, haw]
    · exact hrefl i hra

theorem secondKind_structure : SecondKindStructure a b c := by
  have htri0 := htri
  obtain ⟨ha, hc, hb, hac, hcomm, hab, hcb⟩ := htri
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  have hc2 := hD.mul_self_eq_one hc
  have hw2 : a * c * (a * c) = 1 := IsTriangle.uv_mul_self hD htri0
  have hoddab : Odd (orderOf (a * b)) := hD.odd_of_not_commute ha hb hab
  set X := Subgroup.closure ({a, b} : Set G) with hXdef
  set K := Subgroup.closure ({a, b, c} : Set G) with hKdef
  set w := a * c with hwdef
  set Q := conjClosure X w with hQdef
  have hXK : X ≤ K := Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp)
  have haX : a ∈ X := Subgroup.subset_closure (by simp)
  have hbX : b ∈ X := Subgroup.subset_closure (by simp)
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hcK : c ∈ K := Subgroup.subset_closure (by simp)
  have hwK : w ∈ K := K.mul_mem haK hcK
  have hP1 : ∀ g ∈ X, Commute w (g * w * g⁻¹) := fun g hg =>
    commute_conj_of_secondKind hD hN htri0 h4 hno hg
  have hgenQ : ∀ g ∈ X, g * w * g⁻¹ ∈ Q := fun g hg => Subgroup.subset_closure ⟨g, hg, rfl⟩
  have hwQ : w ∈ Q := by simpa using hgenQ 1 X.one_mem
  have hQcomm : ∀ p ∈ Q, ∀ q ∈ Q, Commute p q := by
    intro p hp q hq
    refine Asc72.commute_of_mem_closure ?_ hp hq
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    have h1 := (hP1 (h⁻¹ * g) (X.mul_mem (X.inv_mem hh) hg)).symm.map (MulAut.conj h).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    convert h1 using 1
    group
  have hQsq : ∀ q ∈ Q, q * q = 1 := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, -, rfl⟩ := hx
      calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
        _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      rw [show x * y * (x * y) = x * x * (y * y) by
        rw [mul_assoc x y, ← mul_assoc y x, ← (hQcomm x hx y hy).eq]; group, ihx, ihy, mul_one]
    | inv x _ ih => rw [← mul_inv_rev, ih, inv_one]
  have hQ2 : IsPGroup 2 Q := fun q => ⟨1, Subtype.ext (by simpa [pow_two] using hQsq q q.2)⟩
  have hQK : Q ≤ K := (Subgroup.closure_le _).mpr (by
    rintro _ ⟨g, hg, rfl⟩
    exact K.mul_mem (K.mul_mem (hXK hg) hwK) (K.inv_mem (hXK hg)))
  have hXconj : ∀ t ∈ X, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq =>
    Asc72.conj_mem_closure (by rintro _ ⟨g, hg, rfl⟩; exact ⟨t * g, X.mul_mem ht hg, by group⟩) hq
  have hKQ : ∀ g ∈ K, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hg
    refine conj_mem_of_mem_closure (T := {a, b, c}) ?_ ?_ hg
    · rintro t (rfl | rfl | rfl) <;> assumption
    · rintro t ht q hq
      rcases ht with rfl | rfl | rfl
      · exact hXconj _ haX q hq
      · exact hXconj _ hbX q hq
      · have hcw : t = a * w := by rw [hwdef, ← mul_assoc, ha2, one_mul]
        have hwq : w * q * w⁻¹ = q := by rw [(hQcomm w hwQ q hq).eq, mul_inv_cancel_right]
        rw [hcw, show a * w * q * (a * w)⁻¹ = a * (w * q * w⁻¹) * a⁻¹ by group, hwq]
        exact hXconj _ haX q hq
  have hnorm : ∀ g ∈ K, g ∈ Subgroup.normalizer (Q : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun h =>
      ⟨fun hh => hKQ g hg h hh, fun hh => by
        have := hKQ g⁻¹ (K.inv_mem hg) _ hh
        simpa [mul_assoc] using this⟩
  have hKXQ : K ≤ X ⊔ Q := (Subgroup.closure_le _).mpr (by
    rintro t (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left haX
    · exact Subgroup.mem_sup_left hbX
    · have hcw : t = a * w := by rw [hwdef, ← mul_assoc, ha2, one_mul]
      rw [hcw]
      exact (X ⊔ Q).mul_mem (Subgroup.mem_sup_left haX) (Subgroup.mem_sup_right hwQ))
  have hXQ : (↑(X ⊔ Q) : Set G) = (X : Set G) * (Q : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X Q (fun g hg => hnorm g (hXK hg))
  have hmax : ∀ P : Subgroup G, P ≤ K → (∀ g ∈ K, ∀ p ∈ P, g * p * g⁻¹ ∈ P) → IsPGroup 2 P →
      P ≤ Q := by
    intro P hPK hPn hP2 p hp
    have hpXQ : p ∈ (↑(X ⊔ Q) : Set G) := hKXQ (hPK hp)
    rw [hXQ] at hpXQ
    obtain ⟨x, hx, q, hq, hxq⟩ := Set.mem_mul.mp hpXQ
    subst hxq
    have hPQ2 : IsPGroup 2 (P ⊔ Q : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hP2 hQ2 (fun g hg => hnorm g (hPK hg))
    have hxPQ : x ∈ P ⊔ Q := by
      have := (P ⊔ Q).mul_mem (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right (Q.inv_mem hq))
      simpa using this
    have hPQK : ∀ g ∈ K, ∀ m ∈ P ⊔ Q, g * m * g⁻¹ ∈ P ⊔ Q := fun g hg m hm =>
      conj_mem_sup (hPn g hg) (hKQ g hg) hm
    obtain ⟨i, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair ha2 hb2 hx
    · have h1 : (a * b) ^ i = 1 :=
        eq_one_of_isPGroup_of_odd hPQ2 hxPQ (odd_orderOf_zpow hoddab i)
      rw [h1, one_mul]
      exact hq
    · exfalso
      obtain ⟨j, hj⟩ := exists_zpow_conj_eq ha2 hb2 hoddab i
      have hjK : ((a * b) ^ j)⁻¹ ∈ K := K.inv_mem (hXK (X.zpow_mem (X.mul_mem haX hbX) j))
      have haPQ : a ∈ P ⊔ Q := by
        have := hPQK _ hjK _ hxPQ
        rw [← hj] at this
        simpa [mul_assoc] using this
      obtain ⟨g₂, hg₂, hg₂e⟩ := hD.exists_conj ha hb hab
      have hbPQ : b ∈ P ⊔ Q := hg₂e ▸ hPQK g₂ (hXK hg₂) a haPQ
      have h1 := eq_one_of_isPGroup_of_odd hPQ2 ((P ⊔ Q).mul_mem haPQ hbPQ) hoddab
      exact hab (hD.eq_of_mul_eq_one ha h1 ▸ Commute.refl a)
  set Qa := ⁅Q, Subgroup.zpowers a⁆ with hQadef
  set Qb := ⁅Q, Subgroup.zpowers b⁆ with hQbdef
  have hcommQ : ∀ {t : G}, t ∈ K → ⁅Q, Subgroup.zpowers t⁆ ≤ Q := by
    intro t ht
    rw [Subgroup.commutator_le]
    intro q hq s hs
    have hsK : s ∈ K := (Subgroup.zpowers_le.mpr ht) hs
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    have := hKQ s hsK _ (Q.inv_mem hq)
    exact Q.mul_mem hq (by simpa [mul_assoc] using this)
  have hQaQ : Qa ≤ Q := hcommQ haK
  have hQbQ : Qb ≤ Q := hcommQ hbK
  have hQ0Q : Qa ⊔ Qb ≤ Q := sup_le hQaQ hQbQ
  have hcommX : ∀ g ∈ X, ∀ q ∈ Q, ⁅q, g⁆ ∈ Qa ⊔ Qb := by
    intro g hg
    refine commutatorElement_mem_of_mem_closure hQ0Q (T := {a, b}) ?_ ?_ hg
    · rintro t (rfl | rfl) <;> assumption
    · rintro t (rfl | rfl) q hq
      · exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq
          (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq
          (Subgroup.mem_zpowers _))
  have hw0 : w ∈ Qa ⊔ Qb := by
    have hbaX : b * a ∈ X := X.mul_mem hbX haX
    have hhw : b * a * w = b * c := by rw [hwdef, mul_assoc, ← mul_assoc a a c, ha2, one_mul]
    obtain ⟨y, hy, hyk⟩ := pow_mul_eq_mul_pow_mul hQ0Q hwQ hQcomm
      (fun q hq => hcommX _ (X.inv_mem hbaX) q hq) (orderOf (b * c))
    rw [hhw, pow_orderOf_eq_one] at hyk
    have hbcodd : Odd (orderOf (b * c)) := hD.odd_of_not_commute hb hc (fun h => hcb h.symm)
    have hbaodd : Odd (orderOf (b * a)) := hD.odd_of_not_commute hb ha (fun h => hab h.symm)
    have hpowQ : (b * a) ^ orderOf (b * c) ∈ Q := by
      have e : (b * a) ^ orderOf (b * c) = (w ^ orderOf (b * c) * y)⁻¹ :=
        eq_inv_of_mul_eq_one_left hyk.symm
      rw [e]
      exact Q.inv_mem (Q.mul_mem (Q.pow_mem hwQ _) (hQ0Q hy))
    have h1 : (b * a) ^ orderOf (b * c) = 1 := by
      refine eq_one_of_isPGroup_of_odd hQ2 hpowQ ?_
      have := odd_orderOf_zpow hbaodd (orderOf (b * c))
      simpa using this
    rw [h1, one_mul] at hyk
    obtain ⟨m, hm⟩ := hbcodd
    have hwk : w ^ orderOf (b * c) = w := by
      rw [hm, pow_succ, pow_mul, pow_two, hw2, one_pow, one_mul]
    rw [hwk] at hyk
    have : w = y⁻¹ := eq_inv_of_mul_eq_one_left hyk.symm
    rw [this]
    exact (Qa ⊔ Qb).inv_mem hy
  have hQ0 : Q ≤ Qa ⊔ Qb := by
    rw [hQdef, conjClosure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    have e : g * w * g⁻¹ = w * ⁅w⁻¹, g⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact (Qa ⊔ Qb).mul_mem hw0 (hcommX g hg _ (Q.inv_mem hwQ))
  have hQa_cent : ∀ y ∈ Qa, Commute a y := fun y hy =>
    commute_of_mem_commutator_zpowers hD hN hQ2 ha (hKQ a haK) hy
  have hQb_cent : ∀ y ∈ Qb, Commute b y := fun y hy =>
    commute_of_mem_commutator_zpowers hD hN hQ2 hb (hKQ b hbK) hy
  have hcomm_a : ∀ x ∈ Q, ⁅x, a⁆ ∈ Q := fun x hx =>
    hQaQ (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers a))
  have hmul_a : ∀ x₁ ∈ Q, ∀ x₂ ∈ Q, ⁅x₁ * x₂, a⁆ = ⁅x₁, a⁆ * ⁅x₂, a⁆ := by
    intro x₁ hx₁ x₂ hx₂
    rw [commutatorElement_mul_left_eq_conj_mul, (hQcomm x₁ hx₁ _ (hcomm_a x₂ hx₂)).eq,
      mul_inv_cancel_right, (hQcomm _ (hcomm_a x₂ hx₂) _ (hcomm_a x₁ hx₁)).eq]
  have hprod : (↑(Qa ⊔ Qb) : Set G) = (Qa : Set G) * (Qb : Set G) := by
    refine Subgroup.coe_mul_of_left_le_normalizer_right Qa Qb fun g hg =>
      Subgroup.mem_normalizer_iff.mpr fun h => ?_
    constructor
    · intro hh
      rw [(hQcomm g (hQaQ hg) h (hQbQ hh)).eq, mul_inv_cancel_right]
      exact hh
    · intro hh
      have hhQ : g * h * g⁻¹ ∈ Q := hQbQ hh
      have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [e, (hQcomm _ (Q.inv_mem (hQaQ hg)) _ hhQ).eq, inv_mul_cancel_right]
      exact hh
  have hQa_img : ∀ y ∈ Qa, ∃ x ∈ Qb, y = ⁅x, a⁆ := by
    intro y hy
    rw [hQadef, Subgroup.commutator_def] at hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨q, hq, t, ht, rfl⟩ := hz
      rcases (mem_zpowers_of_mul_self ha2).mp ht with rfl | rfl
      · exact ⟨1, Qb.one_mem, by simp⟩
      · have hq0 : q ∈ (↑(Qa ⊔ Qb) : Set G) := hQ0 hq
        rw [hprod] at hq0
        obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := Set.mem_mul.mp hq0
        subst hy
        refine ⟨y₂, hy₂, ?_⟩
        rw [hmul_a y₁ (hQaQ hy₁) y₂ (hQbQ hy₂)]
        have h1 : ⁅y₁, t⁆ = 1 := (commutatorElement_eq_one_iff_commute).mpr (hQa_cent y₁ hy₁).symm
        rw [h1, one_mul]
    | one => exact ⟨1, Qb.one_mem, by simp⟩
    | mul y₁ y₂ _ _ ih₁ ih₂ =>
      obtain ⟨x₁, hx₁, rfl⟩ := ih₁
      obtain ⟨x₂, hx₂, rfl⟩ := ih₂
      exact ⟨x₁ * x₂, Qb.mul_mem hx₁ hx₂, (hmul_a x₁ (hQbQ hx₁) x₂ (hQbQ hx₂)).symm⟩
    | inv y _ ih =>
      obtain ⟨x, hx, rfl⟩ := ih
      refine ⟨x⁻¹, Qb.inv_mem hx, ?_⟩
      have h := hmul_a x⁻¹ (Q.inv_mem (hQbQ hx)) x (hQbQ hx)
      rw [inv_mul_cancel, commutatorElement_one_left] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
  have hconj : ∃ x ∈ Qb, x * a * x⁻¹ = c := by
    have hw' : w ∈ (↑(Qa ⊔ Qb) : Set G) := hw0
    rw [hprod] at hw'
    obtain ⟨y₁, hy₁, y₂, hy₂, hwy⟩ := Set.mem_mul.mp hw'
    obtain ⟨x₀, hx₀, rfl⟩ := hQa_img y₁ hy₁
    refine ⟨x₀, hx₀, ?_⟩
    have hdD : x₀ * a * x₀⁻¹ ∈ D := hN x₀ a ha
    have hcd : c = x₀ * a * x₀⁻¹ * y₂ := by
      have hc' : c = a * w := by rw [hwdef, ← mul_assoc, ha2, one_mul]
      rw [hc', ← hwy, ← mul_assoc, (hQa_cent _ hy₁).eq, commutatorElement_def]
      group
    by_contra hne
    have hy₂c : Commute y₂ c := by
      have hy₂a : Commute y₂ a := by
        have e : y₂ = ⁅x₀, a⁆⁻¹ * w := by rw [← hwy]; group
        rw [e]
        exact (hQa_cent _ hy₁).symm.inv_left.mul_left ((Commute.refl a).mul_left hcomm.symm)
      have hy₂w : Commute y₂ w := hQcomm y₂ (hQbQ hy₂) w hwQ
      have hc' : c = a * w := by rw [hwdef, ← mul_assoc, ha2, one_mul]
      rw [hc']
      exact hy₂a.mul_right hy₂w
    have hdc : Commute (x₀ * a * x₀⁻¹) c := by
      have e : x₀ * a * x₀⁻¹ = c * y₂⁻¹ := by rw [hcd]; group
      rw [e]
      exact (Commute.refl c).mul_left hy₂c.inv_left
    have hprodD : x₀ * a * x₀⁻¹ * c = y₂ := by
      rw [hcd, ← mul_assoc, hD.mul_self_eq_one hdD, one_mul]
    have hbprod : Commute b (x₀ * a * x₀⁻¹ * c) := hprodD ▸ hQb_cent y₂ hy₂
    have := ((hD.commute_mul_iff hdD hc hb hne hdc).mp hbprod).2
    exact hcb this.symm
  exact ⟨hQK, hKQ, hQcomm, hQsq, hmax, le_antisymm hQ0 hQ0Q,
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hQb_cent y hy).eq.symm, hconj⟩

end SecondKind

theorem oddTranspSecondKind : OddTranspSecondKind :=
  fun _ _ _ _ hD hN _ _ _ htri h4 hno => secondKind_structure hD hN htri h4 hno

end CFSG.Timmesfeld.Bridge.OddTransp
