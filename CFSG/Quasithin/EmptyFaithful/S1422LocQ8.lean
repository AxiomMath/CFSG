module

public import CFSG.Quasithin.EmptyFaithful.S143Q8Aux
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

namespace S1422Loc

open Subgroup

variable {P : Type*} [Group P]

theorem card_le_two_mul_card_inf_centralizer [Finite P] {z : P} (hz : z * z = 1)
    {A : Subgroup P} (q : P) (hcomm : ∀ a ∈ A, a * q * a⁻¹ * q⁻¹ = 1 ∨ a * q * a⁻¹ * q⁻¹ = z)
    (hcentral : ∀ a ∈ A, a * z = z * a) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set P)) := by
  classical
  by_cases hA : A ≤ Subgroup.centralizer ({q} : Set P)
  · rw [inf_eq_left.2 hA]; omega
  · obtain ⟨a₀, ha₀, ha₀C⟩ := Set.not_subset.mp hA
    have hmem : ∀ a ∈ A, a ∈ Subgroup.centralizer ({q} : Set P) ↔ a * q = q * a := by
      intro a _
      exact Subgroup.mem_centralizer_singleton_iff
    have hz0 : ∀ a ∈ A, a * q ≠ q * a → a * q = z * (q * a) := by
      intro a ha hne
      rcases hcomm a ha with h | h
      · exact absurd (by
          calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
            _ = q * a := by rw [h, one_mul]) hne
      · calc a * q = (a * q * a⁻¹ * q⁻¹) * (q * a) := by group
          _ = z * (q * a) := by rw [h]
    have hsub : (A : Set P) ⊆ ↑(A ⊓ Subgroup.centralizer ({q} : Set P)) ∪
        (fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set P)) := by
      intro a ha
      by_cases haC : a ∈ Subgroup.centralizer ({q} : Set P)
      · exact Or.inl ⟨ha, haC⟩
      · refine Or.inr ⟨a₀⁻¹ * a, ⟨A.mul_mem (A.inv_mem ha₀) ha, ?_⟩, by group⟩
        show a₀⁻¹ * a ∈ Subgroup.centralizer ({q} : Set P)
        rw [hmem _ (A.mul_mem (A.inv_mem ha₀) ha)]
        have hne : a * q ≠ q * a := fun h => haC ((hmem a ha).2 h)
        have hne₀ : a₀ * q ≠ q * a₀ := fun h => ha₀C ((hmem a₀ ha₀).2 h)
        have h1 := hz0 a ha hne
        have h2 := hz0 a₀ ha₀ hne₀
        have hza : a₀⁻¹ * z = z * a₀⁻¹ := hcentral _ (A.inv_mem ha₀)
        have hq0 : a₀⁻¹ * q = z * (q * a₀⁻¹) := by
          calc a₀⁻¹ * q = a₀⁻¹ * (q * a₀) * a₀⁻¹ := by group
            _ = a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ := by
              rw [show q * a₀ = z * (a₀ * q) from by
                calc q * a₀ = z * (z * (q * a₀)) := by rw [← mul_assoc, hz, one_mul]
                  _ = z * (a₀ * q) := by rw [h2]]
            _ = z * (q * a₀⁻¹) := by
              calc a₀⁻¹ * (z * (a₀ * q)) * a₀⁻¹ = (a₀⁻¹ * z) * (a₀ * q) * a₀⁻¹ := by group
                _ = (z * a₀⁻¹) * (a₀ * q) * a₀⁻¹ := by rw [hza]
                _ = z * q * a₀⁻¹ := by group
                _ = z * (q * a₀⁻¹) := by group
        calc a₀⁻¹ * a * q = a₀⁻¹ * (a * q) := by group
          _ = a₀⁻¹ * (z * (q * a)) := by rw [h1]
          _ = (a₀⁻¹ * z) * (q * a) := by group
          _ = (z * a₀⁻¹) * (q * a) := by rw [hza]
          _ = z * ((a₀⁻¹ * q) * a) := by group
          _ = z * ((z * (q * a₀⁻¹)) * a) := by rw [hq0]
          _ = (z * z) * (q * (a₀⁻¹ * a)) := by group
          _ = q * (a₀⁻¹ * a) := by rw [hz, one_mul]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (↑(A ⊓ Subgroup.centralizer ({q} : Set P)) : Set P)
      ((fun c => a₀ * c) '' ↑(A ⊓ Subgroup.centralizer ({q} : Set P)))
    rw [Set.ncard_image_of_injective _ (mul_right_injective a₀)] at h2
    have e1 : Nat.card ↥A = (A : Set P).ncard := Nat.card_coe_set_eq _
    have e2 : Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set P)) =
        (↑(A ⊓ Subgroup.centralizer ({q} : Set P)) : Set P).ncard := Nat.card_coe_set_eq _
    omega

theorem card_le_two_of_forall_eq {z : P} {C : Subgroup P} (hC : ∀ c ∈ C, c = 1 ∨ c = z) :
    Nat.card C ≤ 2 := by
  have hsub : (C : Set P) ⊆ {1, z} := fun c hc => by
    rcases hC c hc with h | h <;> simp [h]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, z} : Set P).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : P) ({z} : Set P)
    rw [Set.ncard_singleton] at this
    exact this
  have e : Nat.card C = (C : Set P).ncard := Nat.card_coe_set_eq _
  omega

theorem abelian_sup_of_commute {E F : Subgroup P}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hEF : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a) :
    ∀ a ∈ E ⊔ F, ∀ b ∈ E ⊔ F, a * b = b * a := by
  intro a ha b hb
  rw [Subgroup.sup_eq_closure] at ha hb
  induction ha, hb using Subgroup.closure_induction₂ with
  | mem x y hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hE x hx y hy
    · exact hEF x hx y hy
    · exact (hEF y hy x hx).symm
    · exact hF x hx y hy
  | one_left x hx => simp
  | one_right x hx => simp
  | mul_left x y z hx hy hz h1 h2 => exact (Commute.mul_left h1 h2 : Commute (x * y) z)
  | mul_right y z x hy hz hx h1 h2 => exact (Commute.mul_right h1 h2 : Commute x (y * z))
  | inv_left x y hx hy h => exact (Commute.inv_left h : Commute x⁻¹ y)
  | inv_right x y hx hy h => exact (Commute.inv_right h : Commute x y⁻¹)

section Q8

variable (d : S143.Q8SqData P)

include d in
theorem exists_central_involution :
    ∃ c : P, c ≠ 1 ∧ c * c = 1 ∧ (∀ x : P, c * x = x * c) ∧
      ∀ x : P, (∀ y : P, x * y = y * x) → x = 1 ∨ x = c := by
  obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center P)).mp d.card_center
  have hyc : ∀ x : P, (y : P) * x = x * y := fun x => (Subgroup.mem_center_iff.mp y.2 x).symm
  have hcen : ∀ x : P, (∀ w : P, x * w = w * x) → x = 1 ∨ x = y := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · right
      have : (⟨x, Subgroup.mem_center_iff.mpr fun w => (hx w).symm⟩ : Subgroup.center P) = y :=
        hy _ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this
  refine ⟨y, fun h => hy1 (Subtype.ext h), ?_, hyc, hcen⟩
  rcases hcen ((y : P) * y) (fun w => by
    calc (y : P) * y * w = y * (y * w) := by rw [mul_assoc]
      _ = y * (w * y) := by rw [hyc w]
      _ = y * w * y := by rw [mul_assoc]
      _ = w * y * y := by rw [hyc w]
      _ = w * (y * y) := by rw [mul_assoc]) with h | h
  · exact h
  · exfalso
    have : (y : P) = 1 := by
      have h2 : (y : P) * y = y * 1 := by rw [h, mul_one]
      exact (mul_left_cancel h2)
    exact hy1 (Subtype.ext this)

include d in
theorem card_abelian_le (A : Subgroup P) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 8 := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [d.card]; norm_num)
  obtain ⟨c, hc1, hc2, hcc, hcen⟩ := exists_central_involution d
  have hsq : ∀ x : P, x * x = 1 ∨ x * x = c := fun x =>
    hcen _ (fun w => (Subgroup.mem_center_iff.mp (d.sq_mem_center x) w).symm) |>.imp id id
  have hcomm : ∀ x y : P, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = c := fun x y =>
    hcen _ (fun w => (Subgroup.mem_center_iff.mp (d.commutator_mem_center x y) w).symm)
  by_contra hcon
  push Not at hcon
  have hdvd : Nat.card A ∣ 32 := d.card ▸ Subgroup.card_subgroup_dvd_card A
  have hd : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
  have h16 : Nat.card A = 16 ∨ Nat.card A = 32 := by
    have : Nat.card A ∈ Nat.divisors 32 := by simp [hdvd]
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  rcases h16 with h16 | h32
  · have hne : A ≠ ⊤ := by
      intro e; rw [e, Subgroup.card_top, d.card] at h16; omega
    obtain ⟨q, -, hqA⟩ := Set.not_subset.mp (show ¬ (⊤ : Subgroup P) ≤ A from fun hh =>
      hne (le_antisymm le_top hh))
    set B : Subgroup P := A ⊔ Subgroup.zpowers q with hB
    have hBA : A < B := by
      refine lt_of_le_of_ne le_sup_left (fun e => hqA ?_)
      have : q ∈ B := Subgroup.mem_sup_right (Subgroup.mem_zpowers q)
      rw [← e] at this; exact this
    have hdvdB : Nat.card B ∣ 32 := d.card ▸ Subgroup.card_subgroup_dvd_card B
    have hAB : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt hBA
    have hB32 : Nat.card B = 32 := by
      have : Nat.card B ∈ Nat.divisors 32 := by simp [hdvdB]
      rw [hd] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      omega
    have hBeq : B = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hB32, d.card])
    have hcent : ∀ x ∈ A ⊓ Subgroup.centralizer ({q} : Set P), x = 1 ∨ x = c := by
      intro x hx
      apply hcen x
      intro y
      have hy' : y ∈ B := hBeq ▸ Subgroup.mem_top y
      have hle : B ≤ Subgroup.centralizer ({x} : Set P) := by
        refine sup_le ?_ ?_
        · intro a ha
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hab a ha x hx.1
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hx.2).symm
      have := Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
      exact this.symm
    have hC2 := card_le_two_of_forall_eq hcent
    have hcount := card_le_two_mul_card_inf_centralizer hc2 (A := A) q
      (fun a _ => hcomm a q) (fun a _ => (hcc a).symm)
    omega
  · have hAQ : A = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h32, d.card])
    subst hAQ
    have := card_le_two_of_forall_eq (z := c) (C := ⊤) (fun q _ => hcen q (fun y => hab q trivial y trivial))
    omega

include d in
theorem center_le_of_abelian_eight (E : Subgroup P)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h8 : Nat.card E = 8) :
    Subgroup.center P ≤ E := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [d.card]; norm_num)
  intro x hx
  by_contra hxE
  have hxc : ∀ y : P, x * y = y * x := fun y => (Subgroup.mem_center_iff.mp hx y).symm
  have hX : ∀ a ∈ E ⊔ Subgroup.zpowers x, ∀ b ∈ E ⊔ Subgroup.zpowers x, a * b = b * a := by
    refine abelian_sup_of_commute hab ?_ ?_
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self x m n).eq
    · intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a x from (hxc a).symm) n).eq
  have hlt : E < E ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left (fun e => hxE ?_)
    rw [e]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have := Subgroup.card_lt_of_lt hlt
  have := card_abelian_le d _ hX
  omega

include d in
theorem mem_of_commutes_abelian_eight (E : Subgroup P)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h8 : Nat.card E = 8) {x : P}
    (hx : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [d.card]; norm_num)
  by_contra hxE
  have hX : ∀ a ∈ E ⊔ Subgroup.zpowers x, ∀ b ∈ E ⊔ Subgroup.zpowers x, a * b = b * a := by
    refine abelian_sup_of_commute hab ?_ ?_
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self x m n).eq
    · intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a x from (hx a ha).symm) n).eq
  have hlt : E < E ⊔ Subgroup.zpowers x := by
    refine lt_of_le_of_ne le_sup_left (fun e => hxE ?_)
    rw [e]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have := Subgroup.card_lt_of_lt hlt
  have := card_abelian_le d _ hX
  omega

include d in
theorem conj_mem_of_abelian_eight (E : Subgroup P)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h8 : Nat.card E = 8) (u : P) {e : P} (he : e ∈ E) :
    u * e * u⁻¹ ∈ E := by
  have h1 : u * e * u⁻¹ * e⁻¹ ∈ Subgroup.center P := d.commutator_mem_center u e
  have : u * e * u⁻¹ = (u * e * u⁻¹ * e⁻¹) * e := by group
  rw [this]
  exact E.mul_mem (center_le_of_abelian_eight d E hab h8 h1) he

end Q8

abbrev V4 : Type := Multiplicative (ZMod 2 × ZMod 2)

@[expose] def q8ToV4 : QuaternionGroup 2 →* V4 where
  toFun x := match x with
    | .a i => Multiplicative.ofAdd (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) i, (0 : ZMod 2))
    | .xa i => Multiplicative.ofAdd (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) i, (1 : ZMod 2))
  map_one' := by decide
  map_mul' := by intro x y; revert x y; decide

theorem q8ToV4_eq_one (x : QuaternionGroup 2) :
    q8ToV4 x = 1 ↔ x = QuaternionGroup.a 0 ∨ x = QuaternionGroup.a 2 := by
  revert x; decide

theorem q8_eq_of_central (x : QuaternionGroup 2) (h : ∀ y : QuaternionGroup 2, x * y = y * x) :
    x = QuaternionGroup.a 0 ∨ x = QuaternionGroup.a 2 := by
  revert x; decide

theorem q8_central_of_eq (x : QuaternionGroup 2)
    (h : x = QuaternionGroup.a 0 ∨ x = QuaternionGroup.a 2) :
    ∀ y : QuaternionGroup 2, x * y = y * x := by
  revert x; decide

theorem q8_eq_of_sq_eq_one (x : QuaternionGroup 2) (h : x * x = 1) :
    x = QuaternionGroup.a 0 ∨ x = QuaternionGroup.a 2 := by
  revert x; decide

section Count

variable (d : S143.Q8SqData P)

@[expose] def Psi : d.A × d.B →* V4 × V4 :=
  (q8ToV4.comp d.eA.toMonoidHom).prodMap (q8ToV4.comp d.eB.toMonoidHom)

theorem Psi_apply (a : d.A) (b : d.B) : Psi d (a, b) = (q8ToV4 (d.eA a), q8ToV4 (d.eB b)) := rfl

theorem q8ToV4_eA_of_mem_center (a : d.A) (ha : (a : P) ∈ Subgroup.center P) :
    q8ToV4 (d.eA a) = 1 := by
  rw [q8ToV4_eq_one]
  refine q8_eq_of_central _ fun y => ?_
  obtain ⟨a', rfl⟩ := d.eA.surjective y
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp ha a').symm

theorem q8ToV4_eB_of_mem_center (b : d.B) (hb : (b : P) ∈ Subgroup.center P) :
    q8ToV4 (d.eB b) = 1 := by
  rw [q8ToV4_eq_one]
  refine q8_eq_of_central _ fun y => ?_
  obtain ⟨b', rfl⟩ := d.eB.surjective y
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp hb b').symm

theorem mem_center_of_q8ToV4_eA (a : d.A) (h : q8ToV4 (d.eA a) = 1) : (a : P) ∈ Subgroup.center P := by
  rw [q8ToV4_eq_one] at h
  refine d.mem_center_of_central_A a.2 fun a' ha' => ?_
  have := q8_central_of_eq _ h (d.eA ⟨a', ha'⟩)
  have h2 : a * ⟨a', ha'⟩ = ⟨a', ha'⟩ * a := d.eA.injective (by rw [map_mul, map_mul]; exact this)
  exact congrArg Subtype.val h2

theorem mem_center_of_q8ToV4_eB (b : d.B) (h : q8ToV4 (d.eB b) = 1) : (b : P) ∈ Subgroup.center P := by
  rw [q8ToV4_eq_one] at h
  refine d.mem_center_of_central_B b.2 fun b' hb' => ?_
  have := q8_central_of_eq _ h (d.eB ⟨b', hb'⟩)
  have h2 : b * ⟨b', hb'⟩ = ⟨b', hb'⟩ * b := d.eB.injective (by rw [map_mul, map_mul]; exact this)
  exact congrArg Subtype.val h2

theorem ker_prodHom_le_ker_Psi : d.prodHom.ker ≤ (Psi d).ker := by
  rintro ⟨a, b⟩ hab
  rw [MonoidHom.mem_ker, S143.Q8SqData.prodHom_apply] at hab
  have hba : (b : P) = (a : P)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have haB : (a : P) ∈ d.B := by
    have : (a : P) = (b : P)⁻¹ := by rw [hba]; simp
    rw [this]; exact d.B.inv_mem b.2
  have hbA : (b : P) ∈ d.A := by rw [hba]; exact d.A.inv_mem a.2
  have hac : (a : P) ∈ Subgroup.center P := by
    rw [d.center_eq]; exact ⟨a.2, haB⟩
  have hbc : (b : P) ∈ Subgroup.center P := by
    rw [d.center_eq]; exact ⟨hbA, b.2⟩
  rw [MonoidHom.mem_ker, Psi_apply, q8ToV4_eA_of_mem_center d a hac, q8ToV4_eB_of_mem_center d b hbc]
  rfl

noncomputable def Theta : P →* V4 × V4 :=
  (d.prodHom.liftOfRightInverse (Function.surjInv d.prodHom_surjective)
    (Function.rightInverse_surjInv d.prodHom_surjective)) ⟨Psi d, ker_prodHom_le_ker_Psi d⟩

theorem Theta_mul (a : d.A) (b : d.B) :
    Theta d ((a : P) * b) = (q8ToV4 (d.eA a), q8ToV4 (d.eB b)) := by
  have := MonoidHom.liftOfRightInverse_comp_apply d.prodHom (Function.surjInv d.prodHom_surjective)
    (Function.rightInverse_surjInv d.prodHom_surjective) ⟨Psi d, ker_prodHom_le_ker_Psi d⟩ (a, b)
  rw [S143.Q8SqData.prodHom_apply] at this
  exact this

theorem ker_Theta : (Theta d).ker = Subgroup.center P := by
  ext x
  rw [MonoidHom.mem_ker]
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul x
  rw [show (a * b : P) = ((⟨a, ha⟩ : d.A) : P) * ((⟨b, hb⟩ : d.B) : P) from rfl, Theta_mul]
  constructor
  · intro h
    have h1 : q8ToV4 (d.eA ⟨a, ha⟩) = 1 := congrArg Prod.fst h
    have h2 : q8ToV4 (d.eB ⟨b, hb⟩) = 1 := congrArg Prod.snd h
    exact (Subgroup.center P).mul_mem (mem_center_of_q8ToV4_eA d _ h1) (mem_center_of_q8ToV4_eB d _ h2)
  · intro hx
    have haB : a ∈ d.B := by
      refine d.mem_B_of_central ha fun a' ha' => ?_
      have h1 := Subgroup.mem_center_iff.mp hx a'
      have h2 : b * a' = a' * b := (d.mul_comm_of_mem ha' hb).symm
      have h3 : a' * a * b = a * a' * b := by
        calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
          _ = a * b * a' := h1
          _ = a * (b * a') := by rw [mul_assoc]
          _ = a * (a' * b) := by rw [h2]
          _ = a * a' * b := by rw [mul_assoc]
      exact (mul_right_cancel h3).symm
    have hbA : b ∈ d.A := by
      refine d.mem_A_of_central hb fun b' hb' => ?_
      have h1 := Subgroup.mem_center_iff.mp hx b'
      have h2 : a * b' = b' * a := d.mul_comm_of_mem ha hb'
      have h3 : a * (b' * b) = a * (b * b') := by
        calc a * (b' * b) = a * b' * b := by rw [mul_assoc]
          _ = b' * a * b := by rw [h2]
          _ = b' * (a * b) := by rw [mul_assoc]
          _ = a * b * b' := h1
          _ = a * (b * b') := by rw [mul_assoc]
      exact (mul_left_cancel h3).symm
    have hac : a ∈ Subgroup.center P := d.inf_le_center ⟨ha, haB⟩
    have hbc : b ∈ Subgroup.center P := d.inf_le_center ⟨hbA, hb⟩
    rw [q8ToV4_eA_of_mem_center d ⟨a, ha⟩ hac, q8ToV4_eB_of_mem_center d ⟨b, hb⟩ hbc]
    rfl

theorem card_map_Theta (E : Subgroup P) (hE : Subgroup.center P ≤ E) (h8 : Nat.card E = 8) :
    Nat.card (E.map (Theta d)) = 4 := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [d.card]; norm_num)
  have hkerle : (Theta d).ker ≤ E := by rw [ker_Theta]; exact hE
  have hcardker : Nat.card ((Theta d).domRestrict E).ker = 2 := by
    rw [MonoidHom.ker_domRestrict]
    calc Nat.card ((Theta d).ker.subgroupOf E) = Nat.card (Theta d).ker :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
      _ = 2 := by rw [ker_Theta]; exact d.card_center
  have := Subgroup.card_ker_mul_card_range ((Theta d).domRestrict E)
  rw [hcardker, MonoidHom.domRestrict_range, h8] at this
  omega

theorem Theta_axis_left (E : Subgroup P) (hE : Subgroup.center P ≤ E) (hE2 : ∀ e ∈ E, e * e = 1)
    (u : V4) (h : (u, (1 : V4)) ∈ E.map (Theta d)) : u = 1 := by
  obtain ⟨e, he, hΘ⟩ := Subgroup.mem_map.mp h
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul e
  rw [show (a * b : P) = ((⟨a, ha⟩ : d.A) : P) * ((⟨b, hb⟩ : d.B) : P) from rfl, Theta_mul] at hΘ
  have h1 : q8ToV4 (d.eA ⟨a, ha⟩) = u := congrArg Prod.fst hΘ
  have h2 : q8ToV4 (d.eB ⟨b, hb⟩) = 1 := congrArg Prod.snd hΘ
  have hbc : b ∈ Subgroup.center P := mem_center_of_q8ToV4_eB d ⟨b, hb⟩ h2
  have hbE : b ∈ E := hE hbc
  have haE : a ∈ E := by
    have : a = a * b * b⁻¹ := by group
    rw [this]; exact E.mul_mem he (E.inv_mem hbE)
  have haa : a * a = 1 := hE2 a haE
  have : d.eA ⟨a, ha⟩ * d.eA ⟨a, ha⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a, ha⟩ * ⟨a, ha⟩ : d.A) = 1 := Subtype.ext haa
    rw [this, map_one]
  have hq := (q8ToV4_eq_one _).mpr (q8_eq_of_sq_eq_one _ this)
  rw [← h1]; exact hq

theorem Theta_axis_right (E : Subgroup P) (hE : Subgroup.center P ≤ E) (hE2 : ∀ e ∈ E, e * e = 1)
    (v : V4) (h : ((1 : V4), v) ∈ E.map (Theta d)) : v = 1 := by
  obtain ⟨e, he, hΘ⟩ := Subgroup.mem_map.mp h
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul e
  rw [show (a * b : P) = ((⟨a, ha⟩ : d.A) : P) * ((⟨b, hb⟩ : d.B) : P) from rfl, Theta_mul] at hΘ
  have h1 : q8ToV4 (d.eA ⟨a, ha⟩) = 1 := congrArg Prod.fst hΘ
  have h2 : q8ToV4 (d.eB ⟨b, hb⟩) = v := congrArg Prod.snd hΘ
  have hac : a ∈ Subgroup.center P := mem_center_of_q8ToV4_eA d ⟨a, ha⟩ h1
  have haE : a ∈ E := hE hac
  have hbE : b ∈ E := by
    have : b = a⁻¹ * (a * b) := by group
    rw [this]; exact E.mul_mem (E.inv_mem haE) he
  have hbb : b * b = 1 := hE2 b hbE
  have : d.eB ⟨b, hb⟩ * d.eB ⟨b, hb⟩ = 1 := by
    rw [← map_mul]
    have : (⟨b, hb⟩ * ⟨b, hb⟩ : d.B) = 1 := Subtype.ext hbb
    rw [this, map_one]
  have hq := (q8ToV4_eq_one _).mpr (q8_eq_of_sq_eq_one _ this)
  rw [← h2]; exact hq

end Count

def e1V : V4 := Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2))
def e2V : V4 := Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2))

theorem V4_cases (u : V4) : u = 1 ∨ u = e1V ∨ u = e2V ∨ u = e1V * e2V := by
  revert u; decide

theorem exists_second (X : Subgroup (V4 × V4)) (h4 : Nat.card X = 4)
    (hR : ∀ v : V4, ((1 : V4), v) ∈ X → v = 1) (u : V4) : ∃ v : V4, (u, v) ∈ X := by
  let f : X → V4 := fun x => x.1.1
  have hinj : Function.Injective f := by
    intro x y hxy
    have hmem : ((1 : V4), x.1.2 * (y.1.2)⁻¹) ∈ X := by
      have := X.mul_mem x.2 (X.inv_mem y.2)
      have e : (x.1 * (y.1)⁻¹) = ((1 : V4), x.1.2 * (y.1.2)⁻¹) :=
        Prod.ext (mul_inv_eq_one.mpr hxy) rfl
      rw [← e]; exact this
    have := hR _ hmem
    have h2 : x.1.2 = y.1.2 := mul_inv_eq_one.mp this
    exact Subtype.ext (Prod.ext hxy h2)
  have hcardV : Nat.card V4 = 4 := by
    rw [Nat.card_eq_fintype_card]; decide
  have hsurj : Function.Surjective f :=
    (Function.Injective.bijective_of_nat_card_le hinj (by rw [h4, hcardV])).2
  obtain ⟨x, hx⟩ := hsurj u
  exact ⟨x.1.2, by have := x.2; rw [show x.1 = (u, x.1.2) from Prod.ext hx rfl] at this; exact this⟩

noncomputable def secOf (X : Subgroup (V4 × V4)) (u : V4) : V4 :=
  Classical.epsilon (fun v : V4 => (u, v) ∈ X)

theorem secOf_spec (X : Subgroup (V4 × V4)) (h4 : Nat.card X = 4)
    (hR : ∀ v : V4, ((1 : V4), v) ∈ X → v = 1) (u : V4) : (u, secOf X u) ∈ X :=
  Classical.epsilon_spec (exists_second X h4 hR u)

theorem mem_iff_secOf (X : Subgroup (V4 × V4)) (h4 : Nat.card X = 4)
    (hR : ∀ v : V4, ((1 : V4), v) ∈ X → v = 1) (u v : V4) : (u, v) ∈ X ↔ v = secOf X u := by
  constructor
  · intro h
    have h2 := secOf_spec X h4 hR u
    have : ((1 : V4), v * (secOf X u)⁻¹) ∈ X := by
      have := X.mul_mem h (X.inv_mem h2)
      have e : ((u, v) * (u, secOf X u)⁻¹) = ((1 : V4), v * (secOf X u)⁻¹) :=
        Prod.ext (mul_inv_cancel u) rfl
      rw [← e]; exact this
    exact mul_inv_eq_one.mp (hR _ this)
  · rintro rfl
    exact secOf_spec X h4 hR u

theorem subgroup_ext_of_secOf (X X' : Subgroup (V4 × V4)) (h4 : Nat.card X = 4)
    (h4' : Nat.card X' = 4) (hR : ∀ v : V4, ((1 : V4), v) ∈ X → v = 1)
    (hR' : ∀ v : V4, ((1 : V4), v) ∈ X' → v = 1)
    (h1 : secOf X e1V = secOf X' e1V) (h2 : secOf X e2V = secOf X' e2V) : X = X' := by
  have hsec : ∀ u, secOf X u = secOf X' u := by
    intro u
    have hmul : ∀ a b : V4, secOf X (a * b) = secOf X a * secOf X b := by
      intro a b
      have := X.mul_mem (secOf_spec X h4 hR a) (secOf_spec X h4 hR b)
      exact ((mem_iff_secOf X h4 hR _ _).mp this).symm
    have hmul' : ∀ a b : V4, secOf X' (a * b) = secOf X' a * secOf X' b := by
      intro a b
      have := X'.mul_mem (secOf_spec X' h4' hR' a) (secOf_spec X' h4' hR' b)
      exact ((mem_iff_secOf X' h4' hR' _ _).mp this).symm
    have h1X : secOf X 1 = 1 := by
      have h11 : ((1 : V4), (1 : V4)) ∈ X := X.one_mem
      exact ((mem_iff_secOf X h4 hR 1 1).mp h11).symm
    have h1X' : secOf X' 1 = 1 := by
      have h11 : ((1 : V4), (1 : V4)) ∈ X' := X'.one_mem
      exact ((mem_iff_secOf X' h4' hR' 1 1).mp h11).symm
    rcases V4_cases u with rfl | rfl | rfl | rfl
    · rw [h1X, h1X']
    · exact h1
    · exact h2
    · rw [hmul, hmul', h1, h2]
  ext ⟨u, v⟩
  rw [mem_iff_secOf X h4 hR, mem_iff_secOf X' h4' hR', hsec]

@[expose] def elemAbelianEight (P : Type*) [Group P] : Set (Subgroup P) :=
  {E | (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ e ∈ E, e * e = 1) ∧ Nat.card E = 8}

theorem ncard_V4_graphs : {p : V4 × V4 | p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2}.ncard = 6 := by
  have : {p : V4 × V4 | p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2} =
      ↑(Finset.univ.filter fun p : V4 × V4 => p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2) := by
    ext p; simp
  rw [this, Set.ncard_coe_finset]
  decide

theorem ncard_elemAbelianEight_le (d : S143.Q8SqData P) : (elemAbelianEight P).ncard ≤ 6 := by
  classical
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [d.card]; norm_num)
  let f : Subgroup P → V4 × V4 := fun E =>
    (secOf (E.map (Theta d)) e1V, secOf (E.map (Theta d)) e2V)
  have hne1 : e1V ≠ 1 := by decide
  have hne2 : e2V ≠ 1 := by decide
  have hne12 : e1V ≠ e2V := by decide
  have hmaps : ∀ E ∈ elemAbelianEight P, f E ∈ {p : V4 × V4 | p.1 ≠ 1 ∧ p.2 ≠ 1 ∧ p.1 ≠ p.2} := by
    rintro E ⟨hab, hsq, h8⟩
    have hc := center_le_of_abelian_eight d E hab h8
    have h4 := card_map_Theta d E hc h8
    have hL := Theta_axis_left d E hc hsq
    have hR := Theta_axis_right d E hc hsq
    have hp1 := secOf_spec (E.map (Theta d)) h4 hR e1V
    have hp2 := secOf_spec (E.map (Theta d)) h4 hR e2V
    refine ⟨?_, ?_, ?_⟩
    · intro h1
      apply hne1
      apply hL
      have : (e1V, secOf (E.map (Theta d)) e1V) = (e1V, (1 : V4)) := by rw [show secOf (E.map (Theta d)) e1V = 1 from h1]
      rw [this] at hp1; exact hp1
    · intro h1
      apply hne2
      apply hL
      have : (e2V, secOf (E.map (Theta d)) e2V) = (e2V, (1 : V4)) := by rw [show secOf (E.map (Theta d)) e2V = 1 from h1]
      rw [this] at hp2; exact hp2
    · intro h12
      have hmem : (e1V * e2V⁻¹, (1 : V4)) ∈ E.map (Theta d) := by
        have := (E.map (Theta d)).mul_mem hp1 ((E.map (Theta d)).inv_mem hp2)
        have e : ((e1V, secOf (E.map (Theta d)) e1V) * (e2V, secOf (E.map (Theta d)) e2V)⁻¹) =
            (e1V * e2V⁻¹, (1 : V4)) :=
          Prod.ext rfl (by show secOf (E.map (Theta d)) e1V * (secOf (E.map (Theta d)) e2V)⁻¹ = 1
                           exact mul_inv_eq_one.mpr h12)
        rw [← e]; exact this
      exact hne12 (mul_inv_eq_one.mp (hL _ hmem))
  have hinj : Set.InjOn f (elemAbelianEight P) := by
    rintro E ⟨hab, hsq, h8⟩ E' ⟨hab', hsq', h8'⟩ h
    have hc := center_le_of_abelian_eight d E hab h8
    have hc' := center_le_of_abelian_eight d E' hab' h8'
    have h4 := card_map_Theta d E hc h8
    have h4' := card_map_Theta d E' hc' h8'
    have hR := Theta_axis_right d E hc hsq
    have hR' := Theta_axis_right d E' hc' hsq'
    have h1 : secOf (E.map (Theta d)) e1V = secOf (E'.map (Theta d)) e1V := congrArg Prod.fst h
    have h2 : secOf (E.map (Theta d)) e2V = secOf (E'.map (Theta d)) e2V := congrArg Prod.snd h
    have hX := subgroup_ext_of_secOf _ _ h4 h4' hR hR' h1 h2
    have hker : (Theta d).ker ≤ E := by rw [ker_Theta]; exact hc
    have hker' : (Theta d).ker ≤ E' := by rw [ker_Theta]; exact hc'
    rw [← Subgroup.comap_map_eq_self hker, ← Subgroup.comap_map_eq_self hker', hX]
  exact (Set.ncard_le_ncard_of_injOn f hmaps hinj (Set.toFinite _)).trans
    (le_of_eq ncard_V4_graphs)

end S1422Loc

end CFSG.Quasithin
