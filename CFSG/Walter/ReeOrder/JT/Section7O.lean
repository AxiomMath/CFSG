module

public import CFSG.Walter.Transitivity.Family
public import CFSG.Walter.ReeOrder.JT.Section7L

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups commutatorElement
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem card_eq_of_isCyclic_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {H : Subgroup X}
    (hH : IsCyclic H) (hH1 : H ≠ ⊥) (hpow : ∀ x ∈ H, x ^ p = 1) : Nat.card H = p := by
  have hexp : Monoid.exponent H ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hpow x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  rcases (Nat.dvd_prime hp.out).mp hexp with h1 | h1
  · exact absurd (Subgroup.card_eq_one.mp h1) hH1
  · exact h1

omit [Finite X] in
theorem map_omegaZ {Y : Type*} [Group Y] (e : X ≃* Y) (H : Subgroup X) (p : ℕ) :
    (omegaZ H p).map e.toMonoidHom = omegaZ (H.map e.toMonoidHom) p := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxH, hxc, hxp⟩, rfl⟩
    refine ⟨⟨x, hxH, rfl⟩, ?_, by simp [← map_pow, hxp]⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hxc z hz]
  · rintro ⟨⟨x, hxH, rfl⟩, hxc, hxp⟩
    refine ⟨x, ⟨hxH, fun z hz => ?_, ?_⟩, rfl⟩
    · apply e.injective
      simpa using hxc _ ⟨z, hz, rfl⟩
    · apply e.injective
      simpa using hxp

theorem exists_ne_one_fixed {A : Type*} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hA : IsPGroup p A) (hA1 : 1 < Nat.card A) {Y : Subgroup (MulAut A)} (hY : IsPGroup p Y) :
    ∃ a : A, a ≠ 1 ∧ ∀ y ∈ Y, (y : MulAut A) a = a := by
  classical
  have hmod := hY.card_modEq_card_fixedPoints A
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpA : Nat.card A ≡ 0 [MOD p] := by
    rw [hn, Nat.modEq_zero_iff_dvd]
    exact dvd_pow_self p hn0
  have hfix : Nat.card (MulAction.fixedPoints Y A) ≡ 0 [MOD p] := hmod.symm.trans hpA
  have h1 : (1 : A) ∈ MulAction.fixedPoints Y A := fun y => map_one (y : MulAut A)
  have hcard : 1 < Nat.card (MulAction.fixedPoints Y A) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints Y A) := Nat.card_pos_iff.mpr
      ⟨⟨⟨1, h1⟩⟩, inferInstance⟩
    have := Nat.modEq_zero_iff_dvd.mp hfix
    have := Nat.le_of_dvd hpos this
    have := hp.out.two_le
    omega
  have := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (⟨1, h1⟩ : MulAction.fixedPoints Y A)
  refine ⟨a, fun h0 => ha1 (Subtype.ext h0), fun y hy => ha ⟨y, hy⟩⟩

theorem le_normalizer_of_card_eq_mul {p : ℕ} [hp : Fact p.Prime] {H K : Subgroup X}
    (hHK : H ≤ K) (hK : IsPGroup p K) (hcard : Nat.card K = p * Nat.card H) :
    K ≤ Subgroup.normalizer (H : Set X) := by
  have hidx : (H.subgroupOf K).index = p := by
    have h1 := (H.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hcard, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hmin : (Nat.card K).minFac = p := by
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      rw [hn] at hcard
      have := hp.out.two_le
      have : 1 ≤ Nat.card H := Nat.card_pos
      nlinarith
    rw [hn, Nat.Prime.pow_minFac hp.out hn0]
  have hnorm : (H.subgroupOf K).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  intro k hk
  exact mem_normalizer_of_conj_mem fun x hx => hnorm.conj_mem ⟨x, hHK hx⟩ hx ⟨k, hk⟩

end General

section CentralPart

variable {X : Type*} [Group X] {p : ℕ} [hp : Fact p.Prime]

@[expose] def centralPart (hp2 : p ≠ 2) (P W : Subgroup X)
    (hW : ∀ w ∈ W, ∀ y ∈ P, w * y = y * w) : Subgroup X where
  carrier := {x | x ∈ P ∧ x ^ p = 1 ∧ ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ W}
  one_mem' := ⟨P.one_mem, one_pow p, fun y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haP, hap, hac⟩ ⟨hbP, hbp, hbc⟩
    refine ⟨P.mul_mem haP hbP, ?_, fun y hy => ?_⟩
    ·
      have hcent : ⁅(⟨b, hbP⟩ : P), (⟨a, haP⟩ : P)⁆ ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro z
        apply Subtype.ext
        have hw := hbc a haP
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        exact (hW _ hw _ z.2).symm
      have := pth_mul_eq_one_of_class2 (p := p) hp2 (⟨a, haP⟩ : P) (⟨b, hbP⟩ : P) hcent
        (Subtype.ext hap) (Subtype.ext hbp)
      simpa using congrArg Subtype.val this
    · have h1 := hbc y hy
      have h2 := hac y hy
      have : a * b * y * (a * b)⁻¹ * y⁻¹ =
          (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by
        have hc : a * (b * y * b⁻¹ * y⁻¹) = (b * y * b⁻¹ * y⁻¹) * a := (hW _ h1 a haP).symm
        calc a * b * y * (a * b)⁻¹ * y⁻¹
            = a * (b * y * b⁻¹ * y⁻¹) * y * a⁻¹ * y⁻¹ := by group
          _ = (b * y * b⁻¹ * y⁻¹) * a * y * a⁻¹ * y⁻¹ := by rw [hc]
          _ = (b * y * b⁻¹ * y⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
      rw [this]
      exact W.mul_mem h1 h2
  inv_mem' := by
    rintro a ⟨haP, hap, hac⟩
    refine ⟨P.inv_mem haP, by rw [inv_pow, hap, inv_one], fun y hy => ?_⟩
    have h1 := hac y hy
    have hc : (a * y * a⁻¹ * y⁻¹)⁻¹ * a = a * (a * y * a⁻¹ * y⁻¹)⁻¹ :=
      hW _ (W.inv_mem h1) _ haP
    have : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = (a * y * a⁻¹ * y⁻¹)⁻¹ := by
      have e : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * ((a * y * a⁻¹ * y⁻¹)⁻¹ * a) := by group
      rw [e, hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact W.inv_mem h1

variable (hp2 : p ≠ 2) {P W : Subgroup X} (hW : ∀ w ∈ W, ∀ y ∈ P, w * y = y * w)

theorem mem_centralPart_iff {x : X} : x ∈ centralPart hp2 P W hW ↔
    x ∈ P ∧ x ^ p = 1 ∧ ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ W := Iff.rfl

theorem centralPart_le : centralPart hp2 P W hW ≤ P := fun _ hx => hx.1

theorem le_centralPart (hWP : W ≤ P) (hWp : ∀ w ∈ W, w ^ p = 1) : W ≤ centralPart hp2 P W hW :=
  fun w hw => ⟨hWP hw, hWp w hw, fun y hy => by
    rw [hW w hw y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact W.one_mem⟩

theorem le_normalizer_centralPart [Finite X] {g : X} (hgP : g ∈ Subgroup.normalizer (P : Set X))
    (hgW : g ∈ Subgroup.normalizer (W : Set X)) :
    g ∈ Subgroup.normalizer ((centralPart hp2 P W hW : Subgroup X) : Set X) := by
  refine mem_normalizer_of_conj_mem fun x hx => ⟨?_, ?_, fun y hy => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgP x).mp hx.1
  · rw [← MulAut.conj_apply, ← map_pow, hx.2.1, map_one]
  · have hy' : g⁻¹ * y * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgP) y).mp hy
      simpa using this
    have h1 := hx.2.2 _ hy'
    have h2 := (Subgroup.mem_normalizer_iff.mp hgW _).mp h1
    have : g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ := by group
    rw [← this]
    exact h2

end CentralPart

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_E₀
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    (P : Sylow p G) (hT₀P : c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hPc : ¬ IsCyclic (P : Subgroup G)) (hW : IsCyclic (omegaZ (P : Subgroup G) p)) :
    ∃ e₀ : G, e₀ ∈ (P : Subgroup G) ∧ orderOf e₀ = p ∧
      (∀ y ∈ (P : Subgroup G), e₀ * y * e₀⁻¹ * y⁻¹ ∈ omegaZ (P : Subgroup G) p) ∧
      e₀ ∉ omegaZ (P : Subgroup G) p ∧
      c.T₀ ≤ Subgroup.normalizer (Subgroup.zpowers e₀ : Set G) ∧
      ∃ u ∈ c.T₀, u ≠ 1 ∧ e₀ * u = u * e₀ := by
  classical
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hp2 : p ≠ 2 := by omega
  set W := omegaZ (P : Subgroup G) p with hWdef
  have hWc : ∀ w ∈ W, ∀ y ∈ (P : Subgroup G), w * y = y * w := fun w hw y hy => hw.2.1 y hy
  have hWP : W ≤ P := omegaZ_le
  have hWp : ∀ w ∈ W, w ^ p = 1 := fun w hw => pow_eq_one_of_mem_omegaZ hw
  have hP1 : (P : Subgroup G) ≠ ⊥ := fun h0 => hPc (by rw [h0]; infer_instance)
  have hW1 : W ≠ ⊥ := omegaZ_ne_bot P.isPGroup' hP1
  have hWcard : Nat.card W = p := card_eq_of_isCyclic_of_pow_eq_one hW hW1 hWp
  have hTW : c.T₀ ≤ Subgroup.normalizer (W : Set G) :=
    hT₀P.trans normalizer_le_normalizer_omegaZ
  set U := centralPart hp2 (P : Subgroup G) W hWc with hUdef
  have hUP : U ≤ P := centralPart_le hp2 hWc
  have hUp : IsPGroup p U := P.isPGroup'.to_le hUP
  have hTU : c.T₀ ≤ Subgroup.normalizer (U : Set G) := fun τ hτ =>
    le_normalizer_centralPart hp2 hWc (hT₀P hτ) (hTW hτ)
  have hWU : W ≤ U := le_centralPart hp2 hWc hWP hWp
  have hUW : ∃ x ∈ U, x ∉ W := by
    have : Fact (IsPGroup p (P : Subgroup G)) := ⟨P.isPGroup'⟩
    obtain ⟨E, hEn, hEc, hEe⟩ := lemma_4_5_a (R := (P : Subgroup G)) hp2 hPc
    have hEW : ¬ E ≤ W.subgroupOf P := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [hEc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, hWcard] at this
      have := hp.out.two_le
      nlinarith
    obtain ⟨x, hxE, hxW⟩ := Set.not_subset.mp hEW
    have hEpow : ∀ y ∈ E, y ^ p = 1 := fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy
    have hxp : x ^ p = 1 := hEpow x hxE
    have hWE : W.subgroupOf P ≤ E := by
      have hnil : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
      have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := (P : Subgroup G))
        (H := E) (by
          intro h0
          rw [h0, Subgroup.card_bot] at hEc
          have := hp.out.two_le
          nlinarith)
      obtain ⟨⟨z, hzE, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
      have hzp : z ^ p = 1 := hEpow z hzE
      have hz1' : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext (Subtype.ext h0))
      have hzW : (z : G) ∈ W := by
        refine ⟨z.2, fun y hy => ?_, by simpa using congrArg Subtype.val hzp⟩
        have := Subgroup.mem_center_iff.mp hzZ ⟨y, hy⟩
        exact (congrArg Subtype.val this).symm
      have hzpG : (z : G) ^ p = 1 := by simpa using congrArg Subtype.val hzp
      have hzW' : Subgroup.zpowers (z : G) = W := by
        refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzW) ?_
        rw [hWcard, Nat.card_zpowers, orderOf_eq_prime hzpG hz1']
      intro w hw
      have hw' : (w : G) ∈ Subgroup.zpowers (z : G) := hzW' ▸ hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have : w = z ^ k := Subtype.ext (by simpa using hk.symm)
      rw [this]
      exact E.zpow_mem hzE k
    set WP := W.subgroupOf (P : Subgroup G)
    have hWPc : ∀ w ∈ WP, ∀ g : (P : Subgroup G), g * w * g⁻¹ = w := by
      intro w hw g
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := hWc (w : G) hw (g : G) g.2
      rw [← this, mul_inv_cancel_right]
    have hWPc' : ∀ w ∈ WP, ∀ g : (P : Subgroup G), w * g * w⁻¹ = g := by
      intro w hw g
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := hWc (w : G) hw (g : G) g.2
      rw [this, mul_inv_cancel_right]
    have hWPn : WP.Normal := ⟨fun w hw g => by rw [hWPc w hw g]; exact hw⟩
    set π := QuotientGroup.mk' WP
    have hπx1 : π x ≠ 1 := by
      intro h0
      exact hxW ((QuotientGroup.eq_one_iff x).mp h0)
    have hπxp : (π x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
    have hEmap : E.map π = Subgroup.zpowers (π x) := by
      have hEeq : E = WP ⊔ Subgroup.zpowers x := by
        have hle : WP ⊔ Subgroup.zpowers x ≤ E := sup_le hWE ((Subgroup.zpowers_le).mpr hxE)
        refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
        have hdisj : Disjoint WP (Subgroup.zpowers x) := by
          rw [Subgroup.disjoint_def]
          intro a haW hax
          by_contra ha1
          have hxa : Subgroup.zpowers x ≤ WP := by
            have hx1 : x ≠ 1 := fun h0 => hxW (by rw [h0]; exact WP.one_mem)
            have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
            have hza : Subgroup.zpowers a = Subgroup.zpowers x := by
              refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hax) ?_
              rw [Nat.card_zpowers, Nat.card_zpowers, hxo]
              have hao : orderOf a ∣ p :=
                (orderOf_dvd_of_mem_zpowers hax).trans (dvd_of_eq hxo)
              rcases (Nat.dvd_prime hp.out).mp hao with h1 | h1
              · exact absurd (orderOf_eq_one_iff.mp h1) ha1
              · exact h1.ge
            rw [← hza, Subgroup.zpowers_le]
            exact haW
          exact hxW (hxa (Subgroup.mem_zpowers x))
        have hx1 : x ≠ 1 := fun h0 => hxW (by rw [h0]; exact WP.one_mem)
        rw [card_sup_eq_mul_of_disjoint (fun w hw => mem_normalizer_of_conj_mem fun y _ => by
          rwa [hWPc' w hw y]) hdisj, hEc, Nat.card_zpowers,
          orderOf_eq_prime hxp hx1,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWP).toEquiv, hWcard, pow_two]
      rw [hEeq, Subgroup.map_sup, MonoidHom.map_zpowers]
      have : WP.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [this, bot_sup_eq]
    have hnorm : (Subgroup.zpowers (π x)).Normal :=
      hEmap ▸ hEn.map π (QuotientGroup.mk'_surjective WP)
    have : Fact (IsPGroup p ((P : Subgroup G) ⧸ WP)) := ⟨P.isPGroup'.to_quotient WP⟩
    have hcen := normal_subgroup_card_eq_prime_le_center (G := (P : Subgroup G) ⧸ WP)
      (p := p) (Subgroup.zpowers (π x)) (by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime hπxp hπx1)
    have hxc := Subgroup.mem_center_iff.mp (hcen (Subgroup.mem_zpowers (π x)))
    refine ⟨x, ⟨x.2, by simpa using congrArg Subtype.val hxp, fun y hy => ?_⟩, hxW⟩
    have h1 := hxc (π ⟨y, hy⟩)
    have h2 : π (⟨y, hy⟩ * x * (⟨y, hy⟩ * x)⁻¹) = π (x * ⟨y, hy⟩ * (⟨y, hy⟩ * x)⁻¹) := by
      simp only [map_mul, map_inv, h1]
    rw [mul_inv_cancel, map_one] at h2
    have h3 : x * ⟨y, hy⟩ * (⟨y, hy⟩ * x)⁻¹ ∈ WP := (QuotientGroup.eq_one_iff _).mp h2.symm
    have h4 : (x : G) * y * (x : G)⁻¹ * y⁻¹ = ((x * ⟨y, hy⟩ * (⟨y, hy⟩ * x)⁻¹ : P) : G) := by
      simp [mul_assoc]
    rw [h4]
    exact h3
  obtain ⟨x₀, hx₀U, hx₀W⟩ := hUW
  have hrel := h.relIndex_eq_mul hp3 c hpq hUp hWU hTU hTW
  have hne1 : W.relIndex U ≠ 1 := fun h1 => hx₀W ((Subgroup.relIndex_eq_one.mp h1) hx₀U)
  have key : ∀ u ∈ c.T₀, u ≠ 1 → (W ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
      (U ⊓ Subgroup.centralizer ({u} : Set G)) ≠ 1 →
      ∃ e₀ : G, e₀ ∈ (P : Subgroup G) ∧ orderOf e₀ = p ∧
        (∀ y ∈ (P : Subgroup G), e₀ * y * e₀⁻¹ * y⁻¹ ∈ W) ∧ e₀ ∉ W ∧
        c.T₀ ≤ Subgroup.normalizer (Subgroup.zpowers e₀ : Set G) ∧
        ∃ u ∈ c.T₀, u ≠ 1 ∧ e₀ * u = u * e₀ := by
    intro u hu hu1 hne
    have hnle : ¬ U ⊓ Subgroup.centralizer ({u} : Set G) ≤
        W ⊓ Subgroup.centralizer ({u} : Set G) := fun hle => hne (Subgroup.relIndex_eq_one.mpr hle)
    obtain ⟨e₀, ⟨he₀U, he₀u⟩, he₀W⟩ := Set.not_subset.mp hnle
    have he₀W' : e₀ ∉ W := fun h0 => he₀W ⟨h0, he₀u⟩
    have he₀1 : e₀ ≠ 1 := fun h0 => he₀W' (h0 ▸ W.one_mem)
    have he₀o : orderOf e₀ = p := orderOf_eq_prime he₀U.2.1 he₀1
    have huo := c.orderOf_of_mem hu hu1
    set E₀ := U ⊓ Subgroup.centralizer ({u} : Set G)
    have hE₀card : Nat.card E₀ ≤ p := h.card_le_of_le_centralizer hp3 hpq (hUp.to_le inf_le_left)
      (fun z hz => hz.1.2.1) huo inf_le_right
    have hzE₀ : Subgroup.zpowers e₀ = E₀ := Subgroup.eq_of_le_of_card_ge
      ((Subgroup.zpowers_le).mpr ⟨he₀U, he₀u⟩) (by rw [Nat.card_zpowers, he₀o]; exact hE₀card)
    have hTE₀ : c.T₀ ≤ Subgroup.normalizer (E₀ : Set G) := by
      refine Walter.Transitivity.le_normalizer_inf hTU
        (fun τ hτ => mem_normalizer_of_conj_mem fun z hz => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      have hτu : τ * u = u * τ := c.comm_of_mem hτ hu
      have hτu' : τ⁻¹ * u = u * τ⁻¹ := by
        calc τ⁻¹ * u = τ⁻¹ * (u * τ) * τ⁻¹ := by group
          _ = τ⁻¹ * (τ * u) * τ⁻¹ := by rw [hτu]
          _ = u * τ⁻¹ := by group
      calc τ * z * τ⁻¹ * u = τ * z * (τ⁻¹ * u) := by group
        _ = τ * (z * u) * τ⁻¹ := by rw [hτu']; group
        _ = τ * (u * z) * τ⁻¹ := by rw [hz]
        _ = (τ * u) * z * τ⁻¹ := by group
        _ = u * (τ * z * τ⁻¹) := by rw [hτu]; group
    refine ⟨e₀, hUP he₀U, he₀o, he₀U.2.2, he₀W', hzE₀ ▸ hTE₀, u, hu, hu1,
      Subgroup.mem_centralizer_singleton_iff.mp he₀u⟩
  by_cases ht : (W ⊓ Subgroup.centralizer ({h.t} : Set G)).relIndex
      (U ⊓ Subgroup.centralizer ({h.t} : Set G)) = 1
  · by_cases hw : (W ⊓ Subgroup.centralizer ({c.w} : Set G)).relIndex
        (U ⊓ Subgroup.centralizer ({c.w} : Set G)) = 1
    · refine key _ c.tw_mem_T₀ c.tw_ne_one fun htw => hne1 ?_
      rw [hrel, ht, hw, htw]
    · exact key _ c.w_mem_T₀ c.w_ne_one hw
  · exact key _ c.t_mem_T₀ h.t_ne_one ht

end JTHyp

end CFSG.Walter.JT
