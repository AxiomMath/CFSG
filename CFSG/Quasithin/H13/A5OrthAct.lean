module

public import CFSG.Quasithin.H13.A5Orth
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13.A5.Orth

open CFSG.Open CFSG.Quasithin

@[expose] def pi8 : QuaternionGroup 2 → Fin 2 → ZMod 2
  | QuaternionGroup.a i => ![(i.val : ZMod 2), 0]
  | QuaternionGroup.xa i => ![(i.val : ZMod 2), 1]

@[expose] def q8 (v : Fin 2 → ZMod 2) : ZMod 2 := v 0 + v 1 + v 0 * v 1

theorem pi8_mul : ∀ x y : QuaternionGroup 2, pi8 (x * y) = pi8 x + pi8 y := by decide

theorem pi8_surj : ∀ v : Fin 2 → ZMod 2, ∃ x : QuaternionGroup 2, pi8 x = v := by decide

theorem pi8_eq_zero : ∀ x : QuaternionGroup 2,
    pi8 x = 0 ↔ (x = 1 ∨ x = QuaternionGroup.a 2) := by decide

theorem pi8_central : ∀ x : QuaternionGroup 2, (∀ y : QuaternionGroup 2, x * y = y * x) →
    pi8 x = 0 := by decide

theorem sq_q8 : ∀ x : QuaternionGroup 2,
    (q8 (pi8 x) = 0 ∧ x * x = 1) ∨ (q8 (pi8 x) = 1 ∧ x * x = QuaternionGroup.a 2) := by decide

theorem a2_central : (∀ y : QuaternionGroup 2, QuaternionGroup.a 2 * y = y * QuaternionGroup.a 2) ∧
    QuaternionGroup.a (2 : ZMod (2 * 2)) ≠ 1 := by decide

theorem a2_mul_a2 : QuaternionGroup.a (2 : ZMod (2 * 2)) * QuaternionGroup.a 2 = 1 := by decide

@[expose] def pairVec (v w : Fin 2 → ZMod 2) : V4 := ![v 0, v 1, w 0, w 1]

theorem pairVec_add (v w v' w' : Fin 2 → ZMod 2) :
    pairVec (v + v') (w + w') = pairVec v w + pairVec v' w' := by
  funext i
  fin_cases i <;> rfl

theorem pairVec_zero : pairVec 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem pairVec_eq_zero : ∀ v w : Fin 2 → ZMod 2, pairVec v w = 0 ↔ v = 0 ∧ w = 0 := by
  decide

theorem pairVec_surj : ∀ u : V4, ∃ v w : Fin 2 → ZMod 2, pairVec v w = u := by decide

theorem q_pairVec : ∀ v w : Fin 2 → ZMod 2, q (pairVec v w) = q8 v + q8 w := by decide

variable {G : Type} [Group G]

structure Q8Coords (P : Subgroup G) where
  θ : ↥P →* Multiplicative V4
  z : G
  θ_surj : Function.Surjective θ
  z_mem : z ∈ P
  z_ne : z ≠ 1
  z_sq : z ^ 2 = 1
  ker_iff : ∀ u : ↥P, θ u = 1 ↔ ((u : G) = 1 ∨ (u : G) = z)
  sq : ∀ u : ↥P, (q (Multiplicative.toAdd (θ u)) = 0 ∧ (u : G) ^ 2 = 1) ∨
    (q (Multiplicative.toAdd (θ u)) = 1 ∧ (u : G) ^ 2 = z)
  center : ∀ u : ↥P, (∀ v : ↥P, u * v = v * u) → ((u : G) = 1 ∨ (u : G) = z)

@[expose] noncomputable def coordPair {P : Subgroup G} {A B : Subgroup ↥P}
    (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* QuaternionGroup 2) :
    ↥A × ↥B →* Multiplicative V4 where
  toFun ab := Multiplicative.ofAdd (pairVec (pi8 (eA ab.1)) (pi8 (eB ab.2)))
  map_one' := by
    show Multiplicative.ofAdd (pairVec (pi8 (eA 1)) (pi8 (eB 1))) = 1
    rw [map_one, map_one, show pi8 1 = 0 from (pi8_eq_zero 1).2 (Or.inl rfl), pairVec_zero]
    rfl
  map_mul' ab cd := by
    show Multiplicative.ofAdd (pairVec (pi8 (eA (ab.1 * cd.1))) (pi8 (eB (ab.2 * cd.2)))) = _
    rw [map_mul, map_mul, pi8_mul, pi8_mul, pairVec_add]
    rfl

@[expose] def mulPair {P : Type*} [Group P] {A B : Subgroup P}
    (h : A ≤ Subgroup.centralizer (B : Set P)) : ↥A × ↥B →* P where
  toFun ab := (ab.1 : P) * ab.2
  map_one' := by
    show ((1 : ↥A) : P) * ((1 : ↥B) : P) = 1
    rw [OneMemClass.coe_one, OneMemClass.coe_one, mul_one]
  map_mul' ab cd := by
    have hc : (ab.2 : P) * cd.1 = cd.1 * ab.2 :=
      (Subgroup.mem_centralizer_iff.mp (h cd.1.2) ab.2 ab.2.2)
    show (ab.1 * cd.1 : P) * (ab.2 * cd.2) = (ab.1 * ab.2) * (cd.1 * cd.2)
    calc (ab.1 : P) * cd.1 * (ab.2 * cd.2) = ab.1 * (cd.1 * ab.2) * cd.2 := by group
      _ = ab.1 * (ab.2 * cd.1) * cd.2 := by rw [hc]
      _ = ab.1 * ab.2 * (cd.1 * cd.2) := by group

theorem mulPair_surjective {P : Type*} [Group P] {A B : Subgroup P}
    (h : A ≤ Subgroup.centralizer (B : Set P)) (hAB : A ⊔ B = ⊤) :
    Function.Surjective (mulPair h) := by
  intro x
  have hN : A ≤ Subgroup.normalizer (B : Set P) := h.trans (Subgroup.centralizer_le_normalizer _)
  have hx : x ∈ ((A ⊔ B : Subgroup P) : Set P) := by rw [hAB]; trivial
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hN] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem nonempty_q8Coords {P : Subgroup G} (hP : IsQ8Sq ↥P) : Nonempty (Q8Coords P) := by
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, ⟨eA⟩, ⟨eB⟩⟩ := hP
  have hμ : Function.Surjective (mulPair hAB) := mulPair_surjective hAB hsup
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hAB ha) b hb).symm
  have hcentA : ∀ a : ↥A, (∀ a' : ↥A, a * a' = a' * a) →
      eA a = 1 ∨ eA a = QuaternionGroup.a 2 := by
    intro a ha
    refine (pi8_eq_zero _).1 (pi8_central _ fun y => ?_)
    obtain ⟨a', rfl⟩ := eA.surjective y
    rw [← map_mul, ← map_mul, ha]
  have hcentB : ∀ b : ↥B, (∀ b' : ↥B, b * b' = b' * b) →
      eB b = 1 ∨ eB b = QuaternionGroup.a 2 := by
    intro b hb
    refine (pi8_eq_zero _).1 (pi8_central _ fun y => ?_)
    obtain ⟨b', rfl⟩ := eB.surjective y
    rw [← map_mul, ← map_mul, hb]
  have h8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardAB : Nat.card ↥(A ⊓ B) = 2 := by
    have h := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hsup, Subgroup.card_top, hcard, Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv,
      h8] at h
    omega
  obtain ⟨x, hx1⟩ : ∃ x : ↥(A ⊓ B), x ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card ↥(A ⊓ B) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by
      rw [h a, h b]⟩, ⟨1⟩⟩
    omega
  set zA : ↥P := (eA.symm (QuaternionGroup.a 2) : ↥P) with hzA
  set zB : ↥P := (eB.symm (QuaternionGroup.a 2) : ↥P) with hzB
  have hx1' : (x : ↥P) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxA : (x : ↥P) = zA := by
    rcases hcentA ⟨x, x.2.1⟩ fun a' => Subtype.ext (hcomm a' a'.2 x x.2.2).symm with h | h
    · exfalso
      apply hx1'
      have : (⟨x, x.2.1⟩ : ↥A) = 1 := eA.injective (by rw [h, map_one])
      exact congrArg (fun y : ↥A => (y : ↥P)) this
    · rw [hzA, ← h, MulEquiv.symm_apply_apply]
  have hxB : (x : ↥P) = zB := by
    rcases hcentB ⟨x, x.2.2⟩ fun b' => Subtype.ext (hcomm x x.2.1 b' b'.2) with h | h
    · exfalso
      apply hx1'
      have : (⟨x, x.2.2⟩ : ↥B) = 1 := eB.injective (by rw [h, map_one])
      exact congrArg (fun y : ↥B => (y : ↥P)) this
    · rw [hzB, ← h, MulEquiv.symm_apply_apply]
  have hzAB : zA = zB := hxA.symm.trans hxB
  have hsqA : ∀ a : ↥A, (q8 (pi8 (eA a)) = 0 ∧ (a : ↥P) * a = 1) ∨
      (q8 (pi8 (eA a)) = 1 ∧ (a : ↥P) * a = zA) := by
    intro a
    rcases sq_q8 (eA a) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, ?_⟩
      have : a * a = 1 := eA.injective (by rw [map_mul, h2, map_one])
      exact congrArg (fun y : ↥A => (y : ↥P)) this
    · refine Or.inr ⟨h1, ?_⟩
      have : a * a = eA.symm (QuaternionGroup.a 2) := eA.injective (by
        rw [map_mul, h2, MulEquiv.apply_symm_apply])
      exact congrArg (fun y : ↥A => (y : ↥P)) this
  have hsqB : ∀ b : ↥B, (q8 (pi8 (eB b)) = 0 ∧ (b : ↥P) * b = 1) ∨
      (q8 (pi8 (eB b)) = 1 ∧ (b : ↥P) * b = zA) := by
    intro b
    rcases sq_q8 (eB b) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, ?_⟩
      have : b * b = 1 := eB.injective (by rw [map_mul, h2, map_one])
      exact congrArg (fun y : ↥B => (y : ↥P)) this
    · refine Or.inr ⟨h1, ?_⟩
      have : b * b = eB.symm (QuaternionGroup.a 2) := eB.injective (by
        rw [map_mul, h2, MulEquiv.apply_symm_apply])
      rw [hzAB]
      exact congrArg (fun y : ↥B => (y : ↥P)) this
  have hzA2 : zA * zA = 1 := by
    have : (eA.symm (QuaternionGroup.a 2) : ↥A) * eA.symm (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, a2_mul_a2, map_one]
    exact congrArg (fun y : ↥A => (y : ↥P)) this
  have hzA1 : zA ≠ 1 := by
    intro h
    have h2 : (eA.symm (QuaternionGroup.a 2) : ↥A) = 1 := Subtype.ext h
    have := congrArg eA h2
    rw [MulEquiv.apply_symm_apply, map_one] at this
    exact a2_central.2 this
  have hkerμ : ∀ ab : ↥A × ↥B, mulPair hAB ab = 1 →
      pi8 (eA ab.1) = 0 ∧ pi8 (eB ab.2) = 0 := by
    rintro ⟨a, b⟩ hab
    have hab' : (a : ↥P) * b = 1 := hab
    have hba : (a : ↥P) = (b : ↥P)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have haB : (a : ↥P) ∈ B := hba ▸ B.inv_mem b.2
    have hbA : (b : ↥P) ∈ A := by
      have : (b : ↥P) = (a : ↥P)⁻¹ := by rw [hba, inv_inv]
      exact this ▸ A.inv_mem a.2
    refine ⟨(pi8_eq_zero _).2 (hcentA a fun a' => Subtype.ext ?_),
      (pi8_eq_zero _).2 (hcentB b fun b' => Subtype.ext ?_)⟩
    · exact (hcomm a' a'.2 a haB).symm
    · exact hcomm b hbA b' b'.2
  have hker : (mulPair hAB).ker ≤ (coordPair eA eB).ker := by
    intro ab hab
    obtain ⟨h1, h2⟩ := hkerμ ab hab
    show Multiplicative.ofAdd (pairVec (pi8 (eA ab.1)) (pi8 (eB ab.2))) = 1
    rw [h1, h2, pairVec_zero]
    rfl
  let θ : ↥P →* Multiplicative V4 :=
    (mulPair hAB).liftOfRightInverse (Function.surjInv hμ) (Function.rightInverse_surjInv hμ)
      ⟨coordPair eA eB, hker⟩
  have hθμ : ∀ ab, θ (mulPair hAB ab) =
      Multiplicative.ofAdd (pairVec (pi8 (eA ab.1)) (pi8 (eB ab.2))) := fun ab =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ ab
  refine ⟨⟨θ, (zA : G), ?_, zA.2, ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro u
    obtain ⟨v, w, rfl⟩ := pairVec_surj (Multiplicative.toAdd u)
    obtain ⟨y, hy⟩ := pi8_surj v
    obtain ⟨y', hy'⟩ := pi8_surj w
    refine ⟨mulPair hAB (eA.symm y, eB.symm y'), ?_⟩
    rw [hθμ]
    simp only [MulEquiv.apply_symm_apply, hy, hy']
    rfl
  ·
    intro h
    exact hzA1 (Subtype.ext h)
  ·
    rw [pow_two]
    exact congrArg Subtype.val hzA2
  ·
    intro u
    obtain ⟨⟨a, b⟩, rfl⟩ := hμ u
    rw [hθμ]
    have hiff : Multiplicative.ofAdd (pairVec (pi8 (eA a)) (pi8 (eB b))) = 1 ↔
        pi8 (eA a) = 0 ∧ pi8 (eB b) = 0 := by
      rw [← pairVec_eq_zero]
      exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => by rw [h]; rfl⟩
    rw [hiff, pi8_eq_zero, pi8_eq_zero]
    have hA1 : eA a = 1 ↔ (a : ↥P) = 1 := by
      rw [← map_one eA, eA.injective.eq_iff]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    have hA2 : eA a = QuaternionGroup.a 2 ↔ (a : ↥P) = zA := by
      rw [← eA.apply_symm_apply (QuaternionGroup.a 2), eA.injective.eq_iff]
      exact ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
    have hB1 : eB b = 1 ↔ (b : ↥P) = 1 := by
      rw [← map_one eB, eB.injective.eq_iff]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    have hB2 : eB b = QuaternionGroup.a 2 ↔ (b : ↥P) = zA := by
      rw [← eB.apply_symm_apply (QuaternionGroup.a 2), eB.injective.eq_iff, hzAB]
      exact ⟨fun h => by rw [h], fun h => Subtype.ext h⟩
    rw [hA1, hA2, hB1, hB2]
    show _ ↔ ((a : ↥P) * b : G) = 1 ∨ ((a : ↥P) * b : G) = (zA : G)
    constructor
    · rintro ⟨ha | ha, hb | hb⟩ <;> rw [ha, hb]
      · left; simp
      · right; simp
      · right; simp
      · left; exact congrArg Subtype.val hzA2
    · intro h
      have hzc : ∀ y : ↥P, y ∈ B → zA * y = y * zA := fun y hy =>
        hcomm zA (eA.symm (QuaternionGroup.a 2)).2 y hy
      rcases h with h | h
      · obtain ⟨h1, h2⟩ := hkerμ (a, b) (Subtype.ext h)
        rw [pi8_eq_zero, hA1, hA2] at h1
        rw [pi8_eq_zero, hB1, hB2] at h2
        exact ⟨h1, h2⟩
      ·
        have hcz : Commute (((eA.symm (QuaternionGroup.a 2) : ↥A) : ↥P) : G) ((b : ↥P) : G) :=
          congrArg Subtype.val (hzc b b.2)
        have hab : mulPair hAB (a * (eA.symm (QuaternionGroup.a 2))⁻¹, b) = 1 := by
          apply Subtype.ext
          show (((a * (eA.symm (QuaternionGroup.a 2))⁻¹ : ↥A) : ↥P) : G) * ((b : ↥P) : G) = 1
          have h' : ((a : ↥P) : G) * ((b : ↥P) : G) =
              (((eA.symm (QuaternionGroup.a 2) : ↥A) : ↥P) : G) := h
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          calc ((a : ↥P) : G) * ((((eA.symm (QuaternionGroup.a 2) : ↥A) : ↥P) : G))⁻¹ *
                ((b : ↥P) : G) =
              ((a : ↥P) : G) * ((b : ↥P) : G) *
                ((((eA.symm (QuaternionGroup.a 2) : ↥A) : ↥P) : G))⁻¹ := by
                rw [mul_assoc, hcz.inv_left.eq, ← mul_assoc]
            _ = 1 := by rw [h', mul_inv_cancel]
        obtain ⟨h1, h2⟩ := hkerμ _ hab
        have h1' : pi8 (eA a) = 0 := by
          have := h1
          simp only at this
          rw [map_mul, pi8_mul, map_inv, MulEquiv.apply_symm_apply] at this
          have hz0 : pi8 (QuaternionGroup.a 2)⁻¹ = 0 := by decide
          rwa [hz0, add_zero] at this
        rw [pi8_eq_zero, hA1, hA2] at h1'
        rw [pi8_eq_zero, hB1, hB2] at h2
        exact ⟨h1', h2⟩
  ·
    intro u
    obtain ⟨⟨a, b⟩, rfl⟩ := hμ u
    rw [hθμ, toAdd_ofAdd, q_pairVec]
    have hsq : (((mulPair hAB (a, b) : ↥P) : G)) ^ 2 =
        (((a : ↥P) * a * ((b : ↥P) * b) : ↥P) : G) := by
      have hc : (b : ↥P) * a = a * b := (hcomm a a.2 b b.2).symm
      show ((a : ↥P) * b : G) ^ 2 = _
      rw [pow_two]
      have hc' : ((b : ↥P) : G) * ((a : ↥P) : G) = ((a : ↥P) : G) * ((b : ↥P) : G) :=
        congrArg Subtype.val hc
      simp only [Subgroup.coe_mul]
      calc ((a : ↥P) : G) * ((b : ↥P) : G) * (((a : ↥P) : G) * ((b : ↥P) : G)) =
          ((a : ↥P) : G) * (((b : ↥P) : G) * ((a : ↥P) : G)) * ((b : ↥P) : G) := by group
        _ = ((a : ↥P) : G) * (((a : ↥P) : G) * ((b : ↥P) : G)) * ((b : ↥P) : G) := by rw [hc']
        _ = _ := by group
    rw [hsq]
    rcases hsqA a with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> rcases hsqB b with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
      rw [ha1, hb1, ha2, hb2]
    · left; simp
    · right; simp
    · right; simp
    · left
      refine ⟨by decide, ?_⟩
      exact congrArg Subtype.val hzA2
  ·
    intro u hu
    obtain ⟨⟨a, b⟩, rfl⟩ := hμ u
    have ha : ∀ a' : ↥A, a * a' = a' * a := by
      intro a'
      apply Subtype.ext
      have h1 := hu a'
      have hb : (b : ↥P) * a' = a' * b := (hcomm a' a'.2 b b.2).symm
      show (a : ↥P) * a' = a' * a
      have h1' : (a : ↥P) * b * a' = a' * (a * b) := h1
      calc (a : ↥P) * a' = (a : ↥P) * ((a' : ↥P) * b) * (b : ↥P)⁻¹ := by group
        _ = (a : ↥P) * ((b : ↥P) * a') * (b : ↥P)⁻¹ := by rw [hb]
        _ = (a : ↥P) * b * a' * (b : ↥P)⁻¹ := by group
        _ = (a' : ↥P) * ((a : ↥P) * b) * (b : ↥P)⁻¹ := by rw [h1']
        _ = (a' : ↥P) * a := by group
    have hb : ∀ b' : ↥B, b * b' = b' * b := by
      intro b'
      apply Subtype.ext
      have h1 := hu b'
      have ha' : (a : ↥P) * b' = b' * a := hcomm a a.2 b' b'.2
      show (b : ↥P) * b' = b' * b
      have h1' : (a : ↥P) * b * b' = b' * (a * b) := h1
      calc (b : ↥P) * b' = (a : ↥P)⁻¹ * (a * b * b') := by group
        _ = (a : ↥P)⁻¹ * (b' * (a * b)) := by rw [h1']
        _ = (a : ↥P)⁻¹ * ((b' * a) * b) := by group
        _ = (a : ↥P)⁻¹ * ((a * b') * b) := by rw [ha']
        _ = (b' : ↥P) * b := by group
    have hA1 : eA a = 1 → (a : ↥P) = 1 := fun h => by
      have : a = 1 := eA.injective (by rw [h, map_one])
      rw [this]; rfl
    have hA2 : eA a = QuaternionGroup.a 2 → (a : ↥P) = zA := fun h => by
      rw [hzA, ← h, MulEquiv.symm_apply_apply]
    have hB1 : eB b = 1 → (b : ↥P) = 1 := fun h => by
      have : b = 1 := eB.injective (by rw [h, map_one])
      rw [this]; rfl
    have hB2 : eB b = QuaternionGroup.a 2 → (b : ↥P) = zA := fun h => by
      rw [hzAB, hzB, ← h, MulEquiv.symm_apply_apply]
    show ((a : ↥P) * b : G) = 1 ∨ ((a : ↥P) * b : G) = (zA : G)
    rcases hcentA a ha with h1 | h1 <;> rcases hcentB b hb with h2 | h2
    · left; rw [hA1 h1, hB1 h2]; simp
    · right; rw [hA1 h1, hB2 h2]; simp
    · right; rw [hA2 h1, hB1 h2]; simp
    · left; rw [hA2 h1, hB2 h2]; exact congrArg Subtype.val hzA2


namespace Q8Coords

variable {P : Subgroup G} (C : Q8Coords P)

theorem conj_mem {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (u : ↥P) :
    x * u * x⁻¹ ∈ P :=
  (Subgroup.mem_normalizer_iff.mp hx u).mp u.2

@[expose] def conjHom {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) : ↥P →* ↥P where
  toFun u := ⟨x * u * x⁻¹, conj_mem hx u⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem coe_conjHom {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (u : ↥P) :
    (conjHom hx u : G) = x * u * x⁻¹ := rfl

theorem ker_le_ker_comp {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G))
    (hxz : x * C.z = C.z * x) : C.θ.ker ≤ (C.θ.comp (conjHom hx)).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [MonoidHom.comp_apply]
  refine (C.ker_iff _).2 ?_
  rw [coe_conjHom]
  rcases (C.ker_iff u).1 hu with h | h
  · left
    rw [h]
    group
  · right
    rw [h, hxz]
    group

@[expose] noncomputable def actHom {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G))
    (hxz : x * C.z = C.z * x) : Multiplicative V4 →* Multiplicative V4 :=
  C.θ.liftOfRightInverse (Function.surjInv C.θ_surj) (Function.rightInverse_surjInv C.θ_surj)
    ⟨C.θ.comp (conjHom hx), C.ker_le_ker_comp hx hxz⟩

theorem actHom_θ {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (hxz : x * C.z = C.z * x)
    (u : ↥P) : C.actHom hx hxz (C.θ u) = C.θ (conjHom hx u) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ u

theorem actHom_injective {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G))
    (hxz : x * C.z = C.z * x) : Function.Injective (C.actHom hx hxz) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨u, rfl⟩ := C.θ_surj w
  rw [actHom_θ] at hw
  refine (C.ker_iff u).2 ?_
  have hz' : x⁻¹ * C.z * x = C.z := by
    calc x⁻¹ * C.z * x = x⁻¹ * (C.z * x) := by group
      _ = x⁻¹ * (x * C.z) := by rw [hxz]
      _ = C.z := by group
  have hu : (u : G) = x⁻¹ * (conjHom hx u : G) * x := by
    rw [coe_conjHom]
    group
  rcases (C.ker_iff _).1 hw with h | h
  · left
    rw [hu, h]
    group
  · right
    rw [hu, h, hz']

@[expose] noncomputable def actAut {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G))
    (hxz : x * C.z = C.z * x) : MulAut (Multiplicative V4) :=
  MulEquiv.ofBijective (C.actHom hx hxz)
    (Finite.injective_iff_bijective.mp (C.actHom_injective hx hxz))

theorem actAut_θ {x : G} (hx : x ∈ Subgroup.normalizer (P : Set G)) (hxz : x * C.z = C.z * x)
    (u : ↥P) : C.actAut hx hxz (C.θ u) = C.θ (conjHom hx u) :=
  C.actHom_θ hx hxz u

theorem actAut_one (h1 : (1 : G) ∈ Subgroup.normalizer (P : Set G)) (h1z : 1 * C.z = C.z * 1) :
    C.actAut h1 h1z = 1 := by
  apply MulEquiv.ext
  intro w
  obtain ⟨u, rfl⟩ := C.θ_surj w
  rw [actAut_θ, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp

theorem actAut_mul {x y : G} (hx : x ∈ Subgroup.normalizer (P : Set G))
    (hy : y ∈ Subgroup.normalizer (P : Set G)) (hxz : x * C.z = C.z * x)
    (hyz : y * C.z = C.z * y) (hxy : x * y ∈ Subgroup.normalizer (P : Set G))
    (hxyz : x * y * C.z = C.z * (x * y)) :
    C.actAut hxy hxyz = C.actAut hx hxz * C.actAut hy hyz := by
  apply MulEquiv.ext
  intro w
  obtain ⟨u, rfl⟩ := C.θ_surj w
  rw [MulAut.mul_apply, actAut_θ, actAut_θ, actAut_θ]
  congr 1
  apply Subtype.ext
  simp only [coe_conjHom]
  group

@[expose] noncomputable def act (X : Subgroup G) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (hXz : X ≤ Subgroup.centralizer ({C.z} : Set G)) : ↥X →* MulAut (Multiplicative V4) where
  toFun x := C.actAut (hXN x.2) (Subgroup.mem_centralizer_singleton_iff.mp (hXz x.2))
  map_one' := C.actAut_one _ _
  map_mul' _ _ := C.actAut_mul _ _ _ _ _ _

theorem act_θ (X : Subgroup G) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (hXz : X ≤ Subgroup.centralizer ({C.z} : Set G)) (x : ↥X) (u : ↥P) :
    C.act X hXN hXz x (C.θ u) = C.θ (conjHom (hXN x.2) u) :=
  C.actHom_θ (hXN x.2) (Subgroup.mem_centralizer_singleton_iff.mp (hXz x.2)) u

theorem act_mem_Oq (X : Subgroup G) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (hXz : X ≤ Subgroup.centralizer ({C.z} : Set G)) (x : ↥X) :
    C.act X hXN hXz x ∈ Oq := by
  intro v
  obtain ⟨u, hu⟩ := C.θ_surj (Multiplicative.ofAdd v)
  have hv : v = Multiplicative.toAdd (C.θ u) := by rw [hu, toAdd_ofAdd]
  rw [hv, ofAdd_toAdd, act_θ]
  have hxz := Subgroup.mem_centralizer_singleton_iff.mp (hXz x.2)
  have hsq : ((conjHom (hXN x.2) u : ↥P) : G) ^ 2 = (u : G) ^ 2 := by
    rw [coe_conjHom, conj_pow]
    rcases C.sq u with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · group
    · calc (x : G) * C.z * (x : G)⁻¹ = C.z * x * (x : G)⁻¹ := by rw [hxz]
        _ = C.z := by group
  rcases C.sq (conjHom (hXN x.2) u) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases C.sq u with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [h1, h3]
  · exact absurd (h4.symm.trans (hsq.symm.trans h2)) C.z_ne
  · exact absurd (h2.symm.trans (hsq.trans h4)) C.z_ne
  · rw [h1, h3]

theorem act_eq_one_iff (X : Subgroup G) (hXN : X ≤ Subgroup.normalizer (P : Set G))
    (hXz : X ≤ Subgroup.centralizer ({C.z} : Set G)) (x : ↥X) :
    C.act X hXN hXz x = 1 ↔
      ∀ u ∈ P, (x : G) * u * (x : G)⁻¹ * u⁻¹ = 1 ∨ (x : G) * u * (x : G)⁻¹ * u⁻¹ = C.z := by
  constructor
  · intro h u hu
    have h1 : C.θ (conjHom (hXN x.2) ⟨u, hu⟩) = C.θ ⟨u, hu⟩ := by
      rw [← act_θ C X hXN hXz x, h, MulAut.one_apply]
    have h2 : C.θ (conjHom (hXN x.2) ⟨u, hu⟩ * (⟨u, hu⟩ : ↥P)⁻¹) = 1 := by
      rw [map_mul, h1, map_inv]
      exact mul_inv_cancel _
    exact (C.ker_iff _).1 h2
  · intro h
    apply MulEquiv.ext
    intro w
    obtain ⟨⟨u, hu⟩, rfl⟩ := C.θ_surj w
    rw [act_θ, MulAut.one_apply]
    have h2 : C.θ (conjHom (hXN x.2) ⟨u, hu⟩ * (⟨u, hu⟩ : ↥P)⁻¹) = 1 :=
      (C.ker_iff _).2 (h u hu)
    rw [map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2

end Q8Coords

end CFSG.Quasithin.H13.A5.Orth
