module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2

open CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl ShapeModel

def modelActFun (h : ShapeH) (m : ShapeN 2) : ShapeN 2 :=
  if h.1 = Multiplicative.ofAdd 1 then
    (if h.2 = Multiplicative.ofAdd 1 then m⁻¹ else m).swap
  else if h.2 = Multiplicative.ofAdd 1 then m⁻¹ else m

theorem modelActFun_mul (h : ShapeH) (m m' : ShapeN 2) :
    modelActFun h (m * m') = modelActFun h m * modelActFun h m' := by
  revert h m m'
  decide

theorem modelActFun_modelActFun (h h' : ShapeH) (m : ShapeN 2) :
    modelActFun h (modelActFun h' m) = modelActFun (h * h') m := by
  revert h h' m
  decide

theorem modelActFun_one (m : ShapeN 2) : modelActFun 1 m = m := by
  revert m
  decide

theorem modelActFun_involutive (h : ShapeH) (m : ShapeN 2) :
    modelActFun h (modelActFun h m) = m := by
  revert h m
  decide

def modelActAut (h : ShapeH) : MulAut (ShapeN 2) where
  toFun := modelActFun h
  invFun := modelActFun h
  left_inv := modelActFun_involutive h
  right_inv := modelActFun_involutive h
  map_mul' := modelActFun_mul h

def modelAct : ShapeH →* MulAut (ShapeN 2) where
  toFun := modelActAut
  map_one' := MulEquiv.ext modelActFun_one
  map_mul' h h' := MulEquiv.ext fun m => (modelActFun_modelActFun h h' m).symm

abbrev ModelGrp := ShapeN 2 ⋊[modelAct] ShapeH

instance : Fintype ModelGrp := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

def modelA : ModelGrp := ⟨(Multiplicative.ofAdd 1, 1), 1⟩

def modelB : ModelGrp := ⟨(1, Multiplicative.ofAdd 1), 1⟩

def modelT : ModelGrp := ⟨1, (Multiplicative.ofAdd 1, 1)⟩

def modelY : ModelGrp := ⟨1, (1, Multiplicative.ofAdd 1)⟩

theorem shapeData_model : ShapeData 2 modelA modelB modelT modelY where
  a_pow := by decide
  b_pow := by decide
  ab := by
    unfold Commute SemiconjBy
    decide
  t_sq := by decide
  y_sq := by decide
  ty := by
    unfold Commute SemiconjBy
    decide
  tab := by decide
  tba := by decide
  ya := by decide
  yb := by decide

theorem model_eq_word : ∀ x : ModelGrp,
    x = modelA ^ (Multiplicative.toAdd x.left.1).val *
      modelB ^ (Multiplicative.toAdd x.left.2).val * modelT ^ (Multiplicative.toAdd x.right.1).val *
      modelY ^ (Multiplicative.toAdd x.right.2).val := by
  decide

theorem card_modelGrp : Nat.card ModelGrp = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem lift_model_surjective : Function.Surjective shapeData_model.lift := by
  rw [← MonoidHom.range_eq_top, shapeData_model.lift_range, shapeData_model.fN_range,
    shapeData_model.fH_range, eq_top_iff]
  intro x _
  rw [model_eq_word x]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))

noncomputable def shapeEquivModel : ShapeGrp 2 ≃* ModelGrp :=
  haveI : Finite (ShapeGrp 2) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  MulEquiv.ofBijective shapeData_model.lift
    (lift_model_surjective.bijective_of_nat_card_le
      (by rw [card_shapeGrp, card_modelGrp]; norm_num))

def coordD (x : ModelGrp) : ZMod 2 :=
  (((Multiplicative.toAdd x.left.1).val + (Multiplicative.toAdd x.left.2).val : ℕ) : ZMod 2)

def coordE (x : ModelGrp) : ZMod 2 := Multiplicative.toAdd x.right.1

def coordF (x : ModelGrp) : ZMod 2 := Multiplicative.toAdd x.right.2

theorem exists_eq_word_mul_sq : ∀ x : ModelGrp, ∃ y : ModelGrp,
    x = modelA ^ (coordD x).val * modelT ^ (coordE x + coordF x).val *
      (modelT * modelY) ^ (coordF x).val * (y * y) := by
  decide

theorem card_pow_four_ne_one : (Finset.univ.filter fun x : ModelGrp => x ^ 4 ≠ 1).card = 16 := by
  decide

theorem card_order_four_ker_mod_five : ∀ n : ZMod 2 × ZMod 2 × ZMod 2, n ≠ 0 →
    (Finset.univ.filter fun x : ModelGrp => x ^ 2 ≠ 1 ∧ x ^ 4 = 1 ∧
      n.1 * coordD x + n.2.1 * (coordE x + coordF x) + n.2.2 * coordF x = 0).card % 5 ≠ 0 := by
  decide

theorem card_sq_eq_one_commute_le_of_swap : ∀ g : ModelGrp, g.right.1 = Multiplicative.ofAdd 1 →
    (Finset.univ.filter fun x : ModelGrp => x * x = 1 ∧ x * g = g * x).card ≤ 12 := by
  decide

theorem card_sq_eq_one_commute_le_of_inv : ∀ g : ModelGrp, g.right.1 = 1 →
    g.right.2 = Multiplicative.ofAdd 1 →
    (Finset.univ.filter fun x : ModelGrp =>
      x * x = 1 ∧ x * g = g * x ∧ x.right.1 = 1).card ≤ 8 := by
  decide

theorem card_sq_eq_one_of_right_eq_one :
    (Finset.univ.filter fun x : ModelGrp => x * x = 1 ∧ x.right = 1).card = 4 := by
  decide

section Orbit

variable {E : Type*} [Group E] [Finite E]

theorem natCard_modEq_natCard_fixed (θ : MulAut E) (hθ : θ ^ 5 = 1) (q : E → Prop)
    (hq : ∀ x, q (θ x) ↔ q x) :
    Nat.card {x // q x} ≡ Nat.card {x // q x ∧ θ x = x} [MOD 5] := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let σ : Equiv.Perm {x // q x} :=
    Equiv.Perm.subtypePerm (θ.toEquiv : Equiv.Perm E) fun x => hq x
  have hpow : ∀ (k : ℕ) (x : {x // q x}), ((σ ^ k) x : E) = (θ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσ : σ ^ 5 ^ 1 = 1 := by
    ext x
    rw [pow_one, hpow, hθ]
    rfl
  have key := Equiv.Perm.card_compl_support_modEq hσ
  have h2 : Nat.card {x // q x ∧ θ x = x} = ((Equiv.Perm.support σ)ᶜ).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
        invFun := fun y => ⟨y.1.1, y.1.2, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact Subtype.ext x.2.2
    · have hy := y.2
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hy
      exact congrArg Subtype.val hy
  rw [h2, Nat.card_eq_fintype_card]
  exact key.symm

end Orbit

section Fixed

variable {E : Type*} [Group E]

def fixedSubgroupOf (θ : MulAut E) : Subgroup E where
  carrier := {x | θ x = x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := map_one θ
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

end Fixed

section Main

open Finset

theorem natCard_subtype_eq_card_filter (E : Subgroup ModelGrp) (P : ModelGrp → Prop)
    [DecidablePred P] [DecidablePred (· ∈ E)] :
    Nat.card {x : E // P x} = (univ.filter fun y : ModelGrp => y ∈ E ∧ P y).card := by
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ E) P), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem coe_pow_map_eq_one_iff {E : Subgroup ModelGrp} (θ : MulAut E) (x : E) (k : ℕ) :
    ((θ x : E) : ModelGrp) ^ k = 1 ↔ (x : ModelGrp) ^ k = 1 := by
  rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, OneMemClass.coe_eq_one, OneMemClass.coe_eq_one,
    ← map_pow, map_eq_one_iff _ θ.injective]

theorem model_mulAut_five_free (E : Subgroup ModelGrp) : ¬ 5 ∣ Nat.card (MulAut E) := by
  classical
  intro h5
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨θ, hθ⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hθ5 : θ ^ 5 = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hθ1 : θ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hθ
    exact absurd hθ (by norm_num)
  set C := fixedSubgroupOf θ with hC
  have hcount := natCard_modEq_natCard_fixed θ hθ5
  have hEC : Nat.card E % 5 = Nat.card C % 5 := by
    have h := hcount (fun _ => True) (fun _ => Iff.rfl)
    have h1 : Nat.card {x : E // True} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    have h2 : Nat.card {x : E // True ∧ θ x = x} = Nat.card C :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1, x.2.2⟩
          invFun := fun x => ⟨x.1, trivial, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, h2] at h
    exact h
  have hCE : Nat.card C < Nat.card E := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group C) fun h => hθ1 ?_
    have htop := (Subgroup.card_eq_iff_eq_top C).1 h
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ C := htop ▸ Subgroup.mem_top x
    exact hx
  have hE64 : Nat.card E ∣ 64 := card_modelGrp ▸ Subgroup.card_subgroup_dvd_card E
  have hCdvd : Nat.card C ∣ Nat.card E := Subgroup.card_subgroup_dvd_card C
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have key : ∀ a ∈ Nat.divisors 64, ∀ c ∈ Nat.divisors a, a % 5 = c % 5 → c < a →
      (a = 16 ∧ c = 1) ∨ (a = 32 ∧ c = 2) ∨ (a = 64 ∧ c = 4) := by
    decide
  have hfixpow : ∀ x : E, θ x = x → x ^ Nat.card C = 1 := fun x hx =>
    congrArg Subtype.val (pow_card_eq_one' (G := C) (x := ⟨x, hx⟩))
  rcases key _ (Nat.mem_divisors.2 ⟨hE64, by norm_num⟩) _
      (Nat.mem_divisors.2 ⟨hCdvd, hEpos.ne'⟩) hEC hCE with
    ⟨hE, hC1⟩ | ⟨hE, hC2⟩ | ⟨hE, hC4⟩
  ·
    have hfix1 : ∀ x : E, θ x = x → x = 1 := by
      intro x hx
      have h := hfixpow x hx
      rwa [hC1, pow_one] at h
    have hcount1 : ∀ (q : E → Prop) (hq : ∀ x, q (θ x) ↔ q x), q 1 →
        Nat.card {x // q x} % 5 = 1 := by
      intro q hq h1
      have h := hcount q hq
      have hu : Nat.card {x // q x ∧ θ x = x} = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨1, h1, map_one θ⟩, fun y => Subtype.ext (hfix1 y.1 y.2.2)⟩
      rw [hu] at h
      exact h
    have hZ : Nat.card (Subgroup.center E) % 5 = 1 := by
      refine hcount1 (· ∈ Subgroup.center E) (fun x => ?_) (Subgroup.one_mem _)
      simp only [Subgroup.mem_center_iff]
      constructor
      · intro h g
        apply θ.injective
        rw [map_mul, map_mul]
        exact h (θ g)
      · intro h g
        rw [← θ.apply_symm_apply g, ← map_mul, ← map_mul, h]
    have hp2 : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hE]; norm_num)
    have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE]; norm_num)
    have hZnt : Nontrivial (Subgroup.center E) := hp2.center_nontrivial
    have hZ1 : 1 < Nat.card (Subgroup.center E) := Finite.one_lt_card_iff_nontrivial.2 hZnt
    have hZdvd : Nat.card (Subgroup.center E) ∣ 16 := hE ▸ Subgroup.card_subgroup_dvd_card _
    have hZ16 : Nat.card (Subgroup.center E) = 16 := by
      have key16 : ∀ c ∈ Nat.divisors 16, c % 5 = 1 → 1 < c → c = 16 := by decide
      exact key16 _ (Nat.mem_divisors.2 ⟨hZdvd, by norm_num⟩) hZ hZ1
    have hZtop : Subgroup.center E = ⊤ :=
      (Subgroup.card_eq_iff_eq_top _).1 (by rw [hZ16, hE])
    have hcomm : ∀ a b : E, a * b = b * a := by
      intro a b
      have hb : b ∈ Subgroup.center E := hZtop ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.1 hb a)
    let Ω : Subgroup E :=
      { carrier := {x | x * x = 1}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [mul_assoc, ← mul_assoc b a b, hcomm b a, mul_assoc a b b, ← mul_assoc, ha, hb,
            one_mul]
        one_mem' := mul_one 1
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [← mul_inv_rev, ha, inv_one] }
    have hΩ : Nat.card Ω % 5 = 1 := by
      refine hcount1 (fun x => x * x = 1) (fun x => ?_) (mul_one 1)
      rw [← map_mul, map_eq_one_iff _ θ.injective]
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [hE]; norm_num)
    have hgΩ : g ∈ Ω := by
      show g * g = 1
      have h := pow_orderOf_eq_one g
      rw [hg, pow_two g] at h
      exact h
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg
      exact absurd hg (by norm_num)
    have hΩ1 : 1 < Nat.card Ω := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      exact hg1 ((Subgroup.mem_bot).1 (hbot ▸ hgΩ))
    have hΩdvd : Nat.card Ω ∣ 16 := hE ▸ Subgroup.card_subgroup_dvd_card _
    have hΩ16 : Nat.card Ω = 16 := by
      have key16 : ∀ c ∈ Nat.divisors 16, c % 5 = 1 → 1 < c → c = 16 := by decide
      exact key16 _ (Nat.mem_divisors.2 ⟨hΩdvd, by norm_num⟩) hΩ hΩ1
    have hΩtop : Ω = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 (by rw [hΩ16, hE])
    have hsq : ∀ x ∈ E, x * x = 1 := by
      intro x hx
      have h : (⟨x, hx⟩ : E) ∈ Ω := hΩtop ▸ Subgroup.mem_top _
      exact congrArg Subtype.val h
    have hcommQ : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩)
    have hcardE : (univ.filter fun y : ModelGrp => y ∈ E).card = 16 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hE
    have hright : ∀ u : Multiplicative (ZMod 2), u ≠ Multiplicative.ofAdd 1 → u = 1 := by
      decide
    by_cases h1 : ∃ g ∈ E, g.right.1 = Multiplicative.ofAdd 1
    · obtain ⟨g, hgE, hg1⟩ := h1
      have hsub : (univ.filter fun y : ModelGrp => y ∈ E) ⊆
          univ.filter fun x : ModelGrp => x * x = 1 ∧ x * g = g * x := by
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx ⊢
        exact ⟨hsq x hx, hcommQ x hx g hgE⟩
      have := card_le_card hsub
      have := card_sq_eq_one_commute_le_of_swap g hg1
      omega
    · push Not at h1
      have hr1 : ∀ x ∈ E, x.right.1 = 1 := fun x hx => hright _ (h1 x hx)
      by_cases h2 : ∃ g ∈ E, g.right.2 = Multiplicative.ofAdd 1
      · obtain ⟨g, hgE, hg2⟩ := h2
        have hsub : (univ.filter fun y : ModelGrp => y ∈ E) ⊆
            univ.filter fun x : ModelGrp => x * x = 1 ∧ x * g = g * x ∧ x.right.1 = 1 := by
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact ⟨hsq x hx, hcommQ x hx g hgE, hr1 x hx⟩
        have := card_le_card hsub
        have := card_sq_eq_one_commute_le_of_inv g (hr1 g hgE) hg2
        omega
      · push Not at h2
        have hsub : (univ.filter fun y : ModelGrp => y ∈ E) ⊆
            univ.filter fun x : ModelGrp => x * x = 1 ∧ x.right = 1 := by
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact ⟨hsq x hx, Prod.ext (hr1 x hx) (hright _ (h2 x hx))⟩
        have := card_le_card hsub
        have := card_sq_eq_one_of_right_eq_one
        omega
  ·
    have hord4 : Nat.card {x : E // (x : ModelGrp) ^ 2 ≠ 1 ∧ (x : ModelGrp) ^ 4 = 1} % 5 = 0 := by
      have h := hcount (fun x => (x : ModelGrp) ^ 2 ≠ 1 ∧ (x : ModelGrp) ^ 4 = 1) (fun x => by
        simp only [ne_eq, coe_pow_map_eq_one_iff])
      have h0 : Nat.card {x : E // ((x : ModelGrp) ^ 2 ≠ 1 ∧ (x : ModelGrp) ^ 4 = 1) ∧
          θ x = x} = 0 := by
        rw [Nat.card_eq_zero]
        left
        refine ⟨fun y => y.2.1.1 ?_⟩
        have := hfixpow y.1 y.2.2
        rw [hC2] at this
        rw [← Subgroup.coe_pow, this, OneMemClass.coe_one]
      rw [h0] at h
      exact h
    have hidx : E.index = 2 := by
      have h := Subgroup.card_mul_index E
      rw [hE, card_modelGrp] at h
      omega
    let ψ : ModelGrp → ZMod 2 := fun x => if x ∈ E then 0 else 1
    have hψE : ∀ x, x ∈ E ↔ ψ x = 0 := by
      intro x
      by_cases hx : x ∈ E <;> simp [ψ, hx]
    have hψmul : ∀ x y, ψ (x * y) = ψ x + ψ y := by
      intro x y
      have h := Subgroup.mul_mem_iff_of_index_two hidx (a := x) (b := y)
      by_cases hx : x ∈ E <;> by_cases hy : y ∈ E
      · simp [ψ, hx, hy, h.2 (iff_of_true hx hy)]
      · simp [ψ, hx, hy, mt h.1 (by tauto)]
      · simp [ψ, hx, hy, mt h.1 (by tauto)]
      · simp only [ψ, hx, hy, h.2 (iff_of_false hx hy), if_true, if_false]
        decide
    have hψpow : ∀ (r : ModelGrp) (u : ZMod 2), ψ (r ^ u.val) = u * ψ r := by
      intro r u
      have h01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
      rcases h01 u with rfl | rfl
      · simp [ψ]
      · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one, one_mul]
    have hψsq : ∀ y, ψ (y * y) = 0 := fun y => (hψE _).1 (Subgroup.mul_self_mem_of_index_two hidx y)
    set n : ZMod 2 × ZMod 2 × ZMod 2 := (ψ modelA, ψ modelT, ψ (modelT * modelY)) with hn
    have hψ : ∀ x, ψ x = n.1 * coordD x + n.2.1 * (coordE x + coordF x) + n.2.2 * coordF x := by
      intro x
      obtain ⟨y, hy⟩ := exists_eq_word_mul_sq x
      conv_lhs => rw [hy]
      rw [hψmul, hψmul, hψmul, hψpow, hψpow, hψpow, hψsq]
      simp only [hn]
      ring
    by_cases hn0 : n = 0
    · have htop : E = ⊤ := by
        refine eq_top_iff.2 fun x _ => (hψE x).2 ?_
        rw [hψ, hn0]
        simp
      have h := Subgroup.card_top (G := ModelGrp)
      rw [← htop, hE, card_modelGrp] at h
      exact absurd h (by norm_num)
    · have h := card_order_four_ker_mod_five n hn0
      rw [natCard_subtype_eq_card_filter E (fun y => y ^ 2 ≠ 1 ∧ y ^ 4 = 1)] at hord4
      have hfilt : (univ.filter fun y : ModelGrp => y ∈ E ∧ (y ^ 2 ≠ 1 ∧ y ^ 4 = 1)) =
          univ.filter fun x : ModelGrp => x ^ 2 ≠ 1 ∧ x ^ 4 = 1 ∧
            n.1 * coordD x + n.2.1 * (coordE x + coordF x) + n.2.2 * coordF x = 0 := by
        ext x
        simp only [mem_filter, mem_univ, true_and, hψE, hψ]
        tauto
      rw [hfilt] at hord4
      exact h hord4
  ·
    have htop : E = ⊤ := (Subgroup.card_eq_iff_eq_top E).1 (by rw [hE, card_modelGrp])
    have h := hcount (fun x => (x : ModelGrp) ^ 4 ≠ 1) (fun x => by
      simp only [ne_eq, coe_pow_map_eq_one_iff])
    have h0 : Nat.card {x : E // (x : ModelGrp) ^ 4 ≠ 1 ∧ θ x = x} = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun y => y.2.1 ?_⟩
      have := hfixpow y.1 y.2.2
      rw [hC4] at this
      rw [← Subgroup.coe_pow, this, OneMemClass.coe_one]
    rw [h0, natCard_subtype_eq_card_filter E (fun y => y ^ 4 ≠ 1)] at h
    have hfilt : (univ.filter fun y : ModelGrp => y ∈ E ∧ y ^ 4 ≠ 1) =
        univ.filter fun x : ModelGrp => x ^ 4 ≠ 1 := by
      ext x
      simp [htop]
    rw [hfilt, card_pow_four_ne_one] at h
    exact absurd h (by decide)

end Main

theorem mulAut_five_free_shape (E : Subgroup (ShapeGrp 2)) : ¬ 5 ∣ Nat.card (MulAut E) := by
  have e : E ≃* E.map shapeEquivModel.toMonoidHom :=
    E.equivMapOfInjective shapeEquivModel.toMonoidHom shapeEquivModel.injective
  rw [Nat.card_congr (MulAut.congr e).toEquiv]
  exact model_mulAut_five_free _

theorem normal_mulAut_five_free_shape
    (E : Subgroup (CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.ShapeModel.ShapeGrp 2))
    (_hE : E.Normal) : ¬ 5 ∣ Nat.card (MulAut E) :=
  mulAut_five_free_shape E

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35G2
