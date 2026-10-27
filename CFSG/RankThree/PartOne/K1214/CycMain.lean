module

public import CFSG.RankThree.PartOne.K1214.OmegaAlg
public import CFSG.RankThree.PartOne.K1214.CycAlg
public import CFSG.RankThree.PartOne.K1214.CycPi
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG

variable {G : Type*} [Group G]

structure CycBase (p : ℕ) (c b : G) (E P Q R Z : Subgroup G) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  P_p : IsPGroup p ↥P
  Q_le : Q ≤ P
  Q_norm : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q
  P_gen : ∃ f ∈ P, P = Q ⊔ Subgroup.zpowers f
  Q_eq : Q = Z ⊔ R
  Z_le : Z ≤ P
  R_le : R ≤ P
  ZR : ∀ z ∈ Z, ∀ r ∈ R, z * r = r * z
  ZR_bot : R ⊓ Z = ⊥
  Z_norm : ∀ x ∈ P, ∀ z ∈ Z, x * z * x⁻¹ ∈ Z
  R_norm : ∀ x ∈ P, ∀ r ∈ R, x * r * x⁻¹ ∈ R
  c_P : c ∈ P
  c_E : c ∈ E
  c_Q : c ∉ Q
  c_p : c ^ p = 1
  b_E : b ∈ E
  b_Z : b ∈ Z
  b_ne : b ≠ 1
  b_cent : ∀ x ∈ P, x * b = b * x
  E_le : E ≤ P
  E_elem : IsElementaryAbelian p ↥E
  E_max : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → E ≤ F → F = E
  shape : ∃ r e : ℕ, (r = 1 ∨ r = 2) ∧ 2 ≤ e ∧
    Nonempty (↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) ∧ Nat.card E = p ^ (r + 2)

structure CycData (p : ℕ) (c b : G) (E P Q R Z : Subgroup G) : Prop extends
    CycBase p c b E P Q R Z where
  Z_ab : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z

namespace CycBase

variable {p : ℕ} {c b : G} {E P Q R Z : Subgroup G} (h : CycBase p c b E P Q R Z)

include h

theorem fact_prime : Fact p.Prime := ⟨h.prime⟩

theorem b_p : b ^ p = 1 := by
  have := h.fact_prime
  have hE := h.E_elem
  exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b h.b_E

theorem orderOf_b : orderOf b = p := by
  have := h.fact_prime
  exact orderOf_eq_prime h.b_p h.b_ne

theorem orderOf_c : orderOf c = p := by
  have := h.fact_prime
  refine orderOf_eq_prime h.c_p fun h1 => h.c_Q ?_
  rw [h1]
  exact Q.one_mem

theorem R_ab : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := by
  obtain ⟨r, e, -, -, ⟨φ⟩, -⟩ := h.shape
  intro x hx y hy
  have h1 : φ (⟨x, hx⟩ * ⟨y, hy⟩) = φ (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val (φ.injective h1)

@[expose] def Rp : Subgroup G := torsionSub R h.R_ab p

theorem Rp_le_R : h.Rp ≤ R := fun _ hx => hx.1

theorem Rp_le_Q : h.Rp ≤ Q := by
  intro x hx
  rw [h.Q_eq]
  exact Subgroup.mem_sup_right hx.1

theorem Rp_elem : IsElementaryAbelian p ↥h.Rp := by
  have : IsMulCommutative ↥h.Rp :=
    ⟨⟨fun a b => Subtype.ext (h.R_ab a a.2.1 b b.2.1)⟩⟩
  refine { toIsMulCommutative := this, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
  exact Subtype.ext x.2.2

theorem card_Rp {r e : ℕ} (he : 1 ≤ e) (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e)))) :
    Nat.card h.Rp = p ^ r := by
  have := h.fact_prime
  rw [← card_torsion_pi (p := p) (e := e) (r := r) he]
  refine Nat.card_congr
    { toFun := fun y => ⟨φ ⟨y.1, y.2.1⟩, by
        rw [← map_pow]
        have : (⟨y.1, y.2.1⟩ : ↥R) ^ p = 1 := Subtype.ext y.2.2
        rw [this, map_one]⟩
      invFun := fun v => ⟨((φ.symm v.1 : ↥R) : G), (φ.symm v.1).2, by
        have h1 : (φ.symm v.1) ^ p = 1 := by
          rw [← map_pow]
          have : v.1 ^ p = 1 := v.2
          rw [this, map_one]
        exact congrArg Subtype.val h1⟩
      left_inv := fun y => by
        apply Subtype.ext
        simp
      right_inv := fun v => by
        apply Subtype.ext
        simp }

theorem Q_normal' : (Q.subgroupOf P).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := h.Q_norm g g.2 n hn
  simpa using this

theorem zpowers_c_inf_Q [Finite G] : Subgroup.zpowers c ⊓ Q = ⊥ := by
  have := h.fact_prime
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rw [Subgroup.mem_bot]
  by_contra hx
  have hx' : Subgroup.zpowers x = Subgroup.zpowers c :=
    Torsion37.zpowers_eq_of_mem_of_ne_one h.prime h.orderOf_c hx1 hx
  have hcx : c ∈ Subgroup.zpowers x := by
    rw [hx']
    exact Subgroup.mem_zpowers c
  exact h.c_Q (Subgroup.zpowers_le.2 hx2 hcx)

theorem c_normalizer_R : c ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h.R_norm c h.c_P x hx
  · intro hx
    have h1 := h.R_norm c⁻¹ (P.inv_mem h.c_P) _ hx
    have h2 : c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x := by group
    rwa [h2] at h1

theorem actR : (∀ x ∈ R, (c * x * c⁻¹ * x⁻¹) ^ p = 1) ∧
    (∀ x ∈ R, x ^ p = 1 → c * x * c⁻¹ = x) := by
  obtain ⟨r, e, hr, he2, ⟨φ⟩, -⟩ := h.shape
  have := h.fact_prime
  exact act_subgroup h.p5 hr (by omega) (Or.inr he2) φ h.c_normalizer_R h.c_p

section Fin

variable [Finite G]

theorem E_sub : ∀ e ∈ E, ∃ j : ℕ, ∃ q ∈ Q, e = c ^ j * q := by
  intro e he
  obtain ⟨f, hfP, hPf⟩ := h.P_gen
  have := h.fact_prime
  have hE := h.E_elem
  exact exists_c_pow_mul h.prime h.Q_le h.Q_normal' hfP hPf h.c_P h.c_Q h.c_p (h.E_le he)
    (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he)

theorem Rp_comm_E : ∀ y ∈ h.Rp, ∀ e ∈ E, y * e = e * y := by
  intro y hy e he
  obtain ⟨j, q, hq, rfl⟩ := h.E_sub e he
  have hcy : Commute c y := by
    have := h.actR.2 y hy.1 hy.2
    show c * y = y * c
    calc c * y = (c * y * c⁻¹) * c := by group
      _ = y * c := by rw [this]
  have hyq : Commute y q := by
    rw [h.Q_eq] at hq
    obtain ⟨z, hz, r, hr, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute h.ZR hq
    exact Commute.mul_right (h.ZR z hz y hy.1).symm (h.R_ab y hy.1 r hr)
  exact (Commute.mul_right (hcy.pow_left j).symm hyq).eq

theorem Rp_le_E : h.Rp ≤ E := by
  have hE := h.E_elem
  have hRp := h.Rp_elem
  have hcent : h.Rp ≤ Subgroup.centralizer (E : Set G) := fun y hy e he =>
    (h.Rp_comm_E y hy e he).symm
  have hF : IsElementaryAbelian p ↥(E ⊔ h.Rp) := IsElementaryAbelian.sup_of_le_centralizer hcent
  have := h.E_max _ hF le_sup_left
  have h1 : h.Rp ≤ E ⊔ h.Rp := le_sup_right
  rwa [this] at h1

theorem E_eq {r e : ℕ} (he : 1 ≤ e) (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e))))
    (hEcard : Nat.card E = p ^ (r + 2)) :
    E = Subgroup.zpowers c ⊔ h.Rp ⊔ Subgroup.zpowers b := by
  have := h.fact_prime
  have hcRp : ∀ k ∈ Subgroup.zpowers c, ∀ y ∈ h.Rp, k * y = y * k := by
    intro k hk y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hcy : Commute c y := by
      have := h.actR.2 y hy.1 hy.2
      show c * y = y * c
      calc c * y = (c * y * c⁻¹) * c := by group
        _ = y * c := by rw [this]
    exact (hcy.zpow_left j).eq
  have hdisj1 : Disjoint (Subgroup.zpowers c) h.Rp := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have : x ∈ Subgroup.zpowers c ⊓ Q := ⟨hx.1, h.Rp_le_Q hx.2⟩
    rw [h.zpowers_c_inf_Q] at this
    exact this
  have hbcomm : ∀ k ∈ Subgroup.zpowers c ⊔ h.Rp, ∀ l ∈ Subgroup.zpowers b, k * l = l * k := by
    intro k hk l hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    have hkb : Commute k b := by
      have : Subgroup.zpowers c ⊔ h.Rp ≤ Subgroup.centralizer ({b} : Set G) := by
        refine sup_le ?_ ?_
        · intro x hx
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcb : Commute c b := h.b_cent c h.c_P
          exact (hcb.zpow_left j).eq
        · intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (h.ZR b h.b_Z x hx.1).symm
      have := Subgroup.mem_centralizer_singleton_iff.1 (this hk)
      exact this
    exact (hkb.zpow_right j).eq
  have hdisj2 : Disjoint (Subgroup.zpowers c ⊔ h.Rp) (Subgroup.zpowers b) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk, y, hy, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcRp hx1
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hx2
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hbZ : b ^ j ∈ Z := Subgroup.zpow_mem _ h.b_Z j
    have hcQ : c ^ i ∈ Q := by
      have h1 : c ^ i = b ^ j * y⁻¹ := by rw [hj]; group
      rw [h1]
      exact Q.mul_mem (by rw [h.Q_eq]; exact Subgroup.mem_sup_left hbZ)
        (Q.inv_mem (h.Rp_le_Q hy))
    have hc1 : c ^ i = 1 := by
      have : c ^ i ∈ Subgroup.zpowers c ⊓ Q := ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i, hcQ⟩
      rw [h.zpowers_c_inf_Q, Subgroup.mem_bot] at this
      exact this
    rw [hc1, one_mul] at hj ⊢
    have hyZ : y ∈ R ⊓ Z := ⟨hy.1, by rw [← hj]; exact hbZ⟩
    rw [h.ZR_bot, Subgroup.mem_bot] at hyZ
    exact hyZ
  have hcard1 : Nat.card ↥(Subgroup.zpowers c ⊔ h.Rp) = p * p ^ r := by
    rw [Torsion37.card_sup_of_commute_disjoint hcRp hdisj1, Nat.card_zpowers, h.orderOf_c,
      h.card_Rp he φ]
  have hcard2 : Nat.card ↥(Subgroup.zpowers c ⊔ h.Rp ⊔ Subgroup.zpowers b) = p ^ (r + 2) := by
    rw [Torsion37.card_sup_of_commute_disjoint hbcomm hdisj2, hcard1, Nat.card_zpowers,
      h.orderOf_b]
    ring
  have hle : Subgroup.zpowers c ⊔ h.Rp ⊔ Subgroup.zpowers b ≤ E :=
    sup_le (sup_le (Subgroup.zpowers_le.2 h.c_E) h.Rp_le_E) (Subgroup.zpowers_le.2 h.b_E)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hEcard, hcard2])).symm

theorem E_inf_Z {r e : ℕ} (he : 1 ≤ e) (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e))))
    (hEcard : Nat.card E = p ^ (r + 2)) {y : G} (hyE : y ∈ E) (hyZ : y ∈ Z) :
    y ∈ Subgroup.zpowers b := by
  rw [h.E_eq he φ hEcard] at hyE
  have hcRp : ∀ k ∈ Subgroup.zpowers c, ∀ y ∈ h.Rp, k * y = y * k := by
    intro k hk y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hcy : Commute c y := by
      have := h.actR.2 y hy.1 hy.2
      show c * y = y * c
      calc c * y = (c * y * c⁻¹) * c := by group
        _ = y * c := by rw [this]
    exact (hcy.zpow_left j).eq
  have hbcomm : ∀ k ∈ Subgroup.zpowers c ⊔ h.Rp, ∀ l ∈ Subgroup.zpowers b, k * l = l * k := by
    intro k hk l hl
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    have hkb : Commute k b := by
      have : Subgroup.zpowers c ⊔ h.Rp ≤ Subgroup.centralizer ({b} : Set G) := by
        refine sup_le ?_ ?_
        · intro x hx
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hcb : Commute c b := h.b_cent c h.c_P
          exact (hcb.zpow_left j).eq
        · intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (h.ZR b h.b_Z x hx.1).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (this hk)
    exact (hkb.zpow_right j).eq
  obtain ⟨w, hw, bk, hbk, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hbcomm hyE
  obtain ⟨k, hk, y', hy', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcRp hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hbk
  have hbZ : b ^ j ∈ Z := Subgroup.zpow_mem _ h.b_Z j
  have hcQ : c ^ i ∈ Q := by
    have h1 : c ^ i = (c ^ i * y' * b ^ j) * (b ^ j)⁻¹ * y'⁻¹ := by group
    rw [h1]
    refine Q.mul_mem (Q.mul_mem ?_ ?_) (Q.inv_mem (h.Rp_le_Q hy'))
    · rw [h.Q_eq]
      exact Subgroup.mem_sup_left hyZ
    · rw [h.Q_eq]
      exact Subgroup.mem_sup_left (Z.inv_mem hbZ)
  have hc1 : c ^ i = 1 := by
    have : c ^ i ∈ Subgroup.zpowers c ⊓ Q := ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i, hcQ⟩
    rw [h.zpowers_c_inf_Q, Subgroup.mem_bot] at this
    exact this
  rw [hc1, one_mul] at hyZ ⊢
  have hy'Z : y' ∈ Z := by
    have := Z.mul_mem hyZ (Z.inv_mem hbZ)
    simpa using this
  have : y' ∈ R ⊓ Z := ⟨hy'.1, hy'Z⟩
  rw [h.ZR_bot, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) j

theorem Y_torsion {r e : ℕ} (he : 1 ≤ e) (φ : ↥R ≃* (Fin r → Multiplicative (ZMod (p ^ e))))
    (hEcard : Nat.card E = p ^ (r + 2)) {y : G} (hyZ : y ∈ Z) (hyc : c * y * c⁻¹ = y)
    (hyp : y ^ p = 1) : y ∈ Subgroup.zpowers b := by
  have hE := h.E_elem
  have hy_E : y ∈ E := by
    have hEle : E ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [h.E_eq he φ hEcard]
      refine sup_le (sup_le ?_ ?_) ?_
      · refine Subgroup.zpowers_le.2 ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc c * y = (c * y * c⁻¹) * c := by group
          _ = y * c := by rw [hyc]
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (h.ZR y hyZ x hx.1).symm
      · refine Subgroup.zpowers_le.2 ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (h.b_cent y (h.Z_le hyZ)).symm
    have hyF : IsElementaryAbelian p ↥(Subgroup.zpowers y) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one hyp
    have hcent : Subgroup.zpowers y ≤ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.zpowers_le]
      intro e he'
      exact Subgroup.mem_centralizer_singleton_iff.1 (hEle he')
    have hF : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers y) :=
      IsElementaryAbelian.sup_of_le_centralizer hcent
    have := h.E_max _ hF le_sup_left
    have h1 : Subgroup.zpowers y ≤ E ⊔ Subgroup.zpowers y := le_sup_right
    rw [this] at h1
    exact h1 (Subgroup.mem_zpowers y)
  exact h.E_inf_Z he φ hEcard hy_E hyZ

end Fin

end CycBase

end CFSG.RankThree.PartOne.K1214
