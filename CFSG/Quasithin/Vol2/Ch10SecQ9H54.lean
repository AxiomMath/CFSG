module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H53
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

open CFSG.Quasithin
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem map_normal {O : Subgroup Y} [O.Normal] {P : Subgroup ↥O} [hP : P.Characteristic] :
    (P.map O.subtype).Normal := by
  constructor
  rintro _ ⟨x, hx, rfl⟩ y
  have h := (Subgroup.characteristic_iff_map_eq.mp hP) (MulAut.conjNormal y)
  have hx' : MulAut.conjNormal y x ∈ P := by
    rw [← h]
    exact ⟨x, hx, rfl⟩
  exact ⟨_, hx', by simp [MulAut.conjNormal_apply]⟩

omit [Group Y] in
theorem map_frattini_mulEquiv {R : Type*} [Group R] (e : R ≃* R) :
    (frattini R).map (e : R →* R) = frattini R := by
  rw [← MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance e

noncomputable def frattiniConj (V : Subgroup Y) [V.Normal] : Y →* MulAut (↥V ⧸ frattini ↥V) where
  toFun g := QuotientGroup.congr (frattini ↥V) (frattini ↥V) (MulAut.conjNormal g)
    (map_frattini_mulEquiv _)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_one]
    rfl
  map_mul' g h := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, map_mul]
    rfl

theorem frattiniConj_mk (V : Subgroup Y) [V.Normal] (g : Y) (x : ↥V) :
    frattiniConj V g (x : ↥V ⧸ frattini ↥V) =
      ((MulAut.conjNormal g x : ↥V) : ↥V ⧸ frattini ↥V) :=
  QuotientGroup.congr_mk _ _ _ (map_frattini_mulEquiv _) x

theorem actsTrivially_of_frattiniConj_eq_one {V : Subgroup Y} [V.Normal] {y : Y}
    (hy : frattiniConj V y = 1) : ActsTriviallyOnFrattiniQuotient V y := by
  intro d hd
  have h := congrArg (fun φ : MulAut (↥V ⧸ frattini ↥V) => φ (⟨d, hd⟩ : ↥V)) hy
  simp only [frattiniConj_mk, MulAut.one_apply] at h
  have h' := (QuotientGroup.eq (s := frattini ↥V)).mp h.symm
  refine ⟨_, h', ?_⟩
  simp [MulAut.conjNormal_apply]

variable [Finite Y] {q : ℕ} [hq : Fact q.Prime]

omit [Finite Y] hq in
theorem isPGroup_map (P : Subgroup ↥(CFSG.pCore q Y)) :
    IsPGroup q ↥(P.map (CFSG.pCore q Y).subtype) :=
  CFSG.pCore_isPGroup.to_le (Subgroup.map_subtype_le P)

omit [Finite Y] hq in
theorem exists_ne_of_isExtraspecial {R : Type*} [Group R] (hex : CFSG.IsExtraspecial q R) :
    ∃ x y : R, x * y ≠ y * x := by
  by_contra h
  push Not at h
  obtain ⟨a, b, hab⟩ := (CFSG.IsExtraspecial.quotient_nontrivial q R).exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [QuotientGroup.eq]
  exact Subgroup.mem_center_iff.mpr fun g => h g _

omit [Finite Y] hq in
theorem le_card_frattini {R : Type*} [Group R] [Finite R] [Fact q.Prime] (h : IsPGroup q R)
    {x : R} (hx : x ∈ frattini R) (hx1 : x ≠ 1) : q ≤ Nat.card (frattini R) := by
  have hp : IsPGroup q (frattini R) := h.to_subgroup _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have hb := Subgroup.eq_bot_of_card_eq _ hk
    rw [hb] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  rw [hk]
  exact Nat.le_self_pow hk0 q

theorem card_quotient_frattini_le (P : Subgroup ↥(CFSG.pCore q Y))
    (hPt : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P) :
    Nat.card (↥(P.map (CFSG.pCore q Y).subtype) ⧸
      frattini ↥(P.map (CFSG.pCore q Y).subtype)) ≤ q ^ 2 := by
  set V := P.map (CFSG.pCore q Y).subtype with hV
  have : Fact (IsPGroup q ↥V) := ⟨isPGroup_map P⟩
  let e : ↥P ≃* ↥V :=
    P.equivMapOfInjective (CFSG.pCore q Y).subtype (CFSG.pCore q Y).subtype_injective
  have hcV : Nat.card ↥V = Nat.card ↥P := (Nat.card_congr e.toEquiv).symm
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥V)
  have hpos : 0 < Nat.card (frattini ↥V) := Nat.card_pos
  rcases hPt with hPe | ⟨hex, h3, -⟩
  · obtain ⟨f⟩ : Nonempty (↥P ≃* Multiplicative (Fin 2 → ZMod q)) := hPe
    have hc : Nat.card ↥P = q ^ 2 := by
      rw [Nat.card_congr f.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    calc Nat.card (↥V ⧸ frattini ↥V)
        ≤ Nat.card (↥V ⧸ frattini ↥V) * Nat.card (frattini ↥V) := Nat.le_mul_of_pos_right _ hpos
      _ = q ^ 2 := by rw [← hmul, hcV, hc]
  · obtain ⟨x, y, hxy⟩ := exists_ne_of_isExtraspecial hex
    have hmem : ⁅e x, e y⁆ ∈ frattini ↥V := by
      refine CFSG.commutator_le_frattini_of_isPGroup (R := ↥V) (p := q) ?_
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hne : ⁅e x, e y⁆ ≠ 1 := by
      rw [← map_commutatorElement, Ne, MulEquiv.map_eq_one_iff,
        commutatorElement_eq_one_iff_mul_comm]
      exact hxy
    have hΦ := le_card_frattini (isPGroup_map P) hmem hne
    have h1 : Nat.card (↥V ⧸ frattini ↥V) * q ≤ q ^ 2 * q := by
      calc Nat.card (↥V ⧸ frattini ↥V) * q
          ≤ Nat.card (↥V ⧸ frattini ↥V) * Nat.card (frattini ↥V) := Nat.mul_le_mul_left _ hΦ
        _ = q ^ 2 * q := by rw [← hmul, hcV, h3, pow_succ]
    exact Nat.le_of_mul_le_mul_right h1 hq.out.pos

theorem mul_conj_mem_frattiniIn (hq2 : q ≠ 2) {P : Subgroup ↥(CFSG.pCore q Y)}
    (hsc : IsSupercritical q P) (hPt : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P)
    {F : Subgroup Y}
    (hker : ∀ x : Y, ActsTriviallyOnFrattiniQuotient (P.map (CFSG.pCore q Y).subtype) x ↔ x ∈ F)
    {K : Subgroup Y} (hKF : K ⊓ F = ⊥) {k₁ k₂ : Y} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hk : k₁ * k₂ ≠ k₂ * k₁) {w : Y} (hw2 : w * w = 1) (hwF : w ∉ F)
    (hw₁ : k₁ * w = w * k₁) (hw₂ : k₂ * w = w * k₂) :
    ∀ d ∈ P.map (CFSG.pCore q Y).subtype,
      d * (w * d * w⁻¹) ∈ frattiniIn (P.map (CFSG.pCore q Y).subtype) := by
  set V := P.map (CFSG.pCore q Y).subtype with hV
  have : P.Characteristic := hsc.characteristic
  have : V.Normal := map_normal
  have : Fact (IsPGroup q ↥V) := ⟨isPGroup_map P⟩
  have hel : IsElementaryAbelian q (↥V ⧸ frattini ↥V) := CFSG.isElementaryAbelian_quotient_frattini
  set ρ := frattiniConj V with hρ
  have hρF : ∀ y, ρ y = 1 → y ∈ F := fun y hy =>
    (hker y).mp (actsTrivially_of_frattiniConj_eq_one hy)
  have hcomm : ∀ a b : ↥V ⧸ frattini ↥V, a * b = b * a :=
    isMulCommutative_iff.mp hel.toIsMulCommutative
  have hexp : ∀ a : ↥V ⧸ frattini ↥V, a ^ q = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (@IsElementaryAbelian.exponent_dvd_p q _ _ hel)
  have hσ2 : ρ w * ρ w = 1 := by rw [← map_mul, hw2, map_one]
  have hσ1 : ρ w ≠ 1 := fun h => hwF (hρF w h)
  have hασ : ρ k₁ * ρ w = ρ w * ρ k₁ := by rw [← map_mul, ← map_mul, hw₁]
  have hβσ : ρ k₂ * ρ w = ρ w * ρ k₂ := by rw [← map_mul, ← map_mul, hw₂]
  have hαβ : ρ k₁ * ρ k₂ ≠ ρ k₂ * ρ k₁ := by
    intro h
    have h1 : ρ (k₁ * k₂ * (k₂ * k₁)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, h, mul_inv_cancel]
    have h2 : k₁ * k₂ * (k₂ * k₁)⁻¹ ∈ K ⊓ F :=
      ⟨K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem (K.mul_mem hk₂ hk₁)), hρF _ h1⟩
    rw [hKF, Subgroup.mem_bot, mul_inv_eq_one] at h2
    exact hk h2
  have key := apply_eq_inv_of_comm hq2 hcomm hexp (card_quotient_frattini_le P hPt) hσ2 hσ1 hασ
    hβσ hαβ
  intro d hd
  have h := key ((⟨d, hd⟩ : ↥V) : ↥V ⧸ frattini ↥V)
  rw [frattiniConj_mk, ← QuotientGroup.mk_inv] at h
  have h' := (frattini ↥V).inv_mem ((QuotientGroup.eq (s := frattini ↥V)).mp h)
  refine ⟨_, h', ?_⟩
  simp [MulAut.conjNormal_apply, mul_assoc]

end CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv
