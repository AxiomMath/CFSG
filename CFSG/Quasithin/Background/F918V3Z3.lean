module

public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.Quasithin

open scoped commutatorElement

private theorem z3_inv_conj {G : Type*} [Group G] {b : G} (hb : b ^ 2 = 1) (y : G) :
    b * (y⁻¹ * (b * y * b⁻¹)) * b⁻¹ = (y⁻¹ * (b * y * b⁻¹))⁻¹ := by
  have hbinv : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb]
  have hbb : b * b = 1 := by rw [← pow_two, hb]
  have h1 : (y⁻¹ * (b * y * b⁻¹))⁻¹ = b * y⁻¹ * b⁻¹ * y := by group
  have h2 : b * (y⁻¹ * (b * y * b⁻¹)) * b⁻¹ = b * y⁻¹ * b * y * b⁻¹ * b⁻¹ := by group
  rw [h1, h2, hbinv]
  rw [mul_assoc (b * y⁻¹ * b * y) b b, hbb, mul_one]

private theorem z3_action_on_commutator {G : Type*} [Group G] {A : Subgroup G}
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {B : Subgroup A} (hB : B.index = 2) {y b : G} (hbA : b ∈ A)
    (hyB : ∀ c : B, ((c : A) : G) * y = y * c) (hby : b * y ≠ y * b) (a : A) :
    (a : G) * (y⁻¹ * (b * y * b⁻¹)) * (a : G)⁻¹ = y⁻¹ * (b * y * b⁻¹) ∨
      (a : G) * (y⁻¹ * (b * y * b⁻¹)) * (a : G)⁻¹ = (y⁻¹ * (b * y * b⁻¹))⁻¹ := by
  set x : G := y⁻¹ * (b * y * b⁻¹)
  have hxinv : b * x * b⁻¹ = x⁻¹ := z3_inv_conj (hA2 b hbA) y
  have hBx : ∀ c : B, ((c : A) : G) * x = x * c := by
    intro c
    have hc : ((c : A) : G) ∈ A := (c : A).2
    have h1 : Commute ((c : A) : G) y := hyB c
    have h2 : Commute ((c : A) : G) b := hAcomm _ hc b hbA
    exact (h1.inv_right.mul_right ((h2.mul_right h1).mul_right h2.inv_right)).eq
  by_cases haB : a ∈ B
  · left
    rw [hBx ⟨a, haB⟩, mul_inv_cancel_right]
  · right
    have hbB : (⟨b, hbA⟩ : A) ∉ B := fun h => hby (hyB ⟨⟨b, hbA⟩, h⟩)
    have habB : a * ⟨b, hbA⟩ ∈ B :=
      (Subgroup.mul_mem_iff_of_index_two hB).mpr (iff_of_false haB hbB)
    have hc : (a : G) * b * x = x * ((a : G) * b) := hBx ⟨a * ⟨b, hbA⟩, habB⟩
    have hbx : b * x = x⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hxinv
    have hax : (a : G) * x⁻¹ = x * a := by
      apply mul_right_cancel (b := b)
      calc (a : G) * x⁻¹ * b = (a : G) * (b * x) := by rw [hbx, mul_assoc]
        _ = (a : G) * b * x := (mul_assoc _ _ _).symm
        _ = x * ((a : G) * b) := hc
        _ = x * a * b := (mul_assoc _ _ _).symm
    have h3 : (a : G) * x⁻¹ * (a : G)⁻¹ = x := mul_inv_eq_iff_eq_mul.mpr hax
    calc (a : G) * x * (a : G)⁻¹ = ((a : G) * x⁻¹ * (a : G)⁻¹)⁻¹ := by group
      _ = x⁻¹ := by rw [h3]

private theorem z3_order_three_of_hyperplane {G : Type*} [Group G] {P A B₀ : Subgroup G}
    (hP : IsPGroup 3 P) (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hB₀A : B₀ ≤ A)
    {B : Subgroup A} (hB : B.index = 2) {y b : G} (hyP : y ∈ P)
    (hyB : ∀ c : B, ((c : A) : G) * y = y * c) (hbB₀ : b ∈ B₀) (hby : b * y ≠ y * b) :
    ∃ X : Subgroup G, X ≤ P ∧ Nat.card ↥X = 3 ∧
      A ≤ Subgroup.normalizer (X : Set G) ∧ ⁅X, B₀⁆ = X := by
  classical
  have hbA : b ∈ A := hB₀A hbB₀
  have hb2 : b ^ 2 = 1 := hA2 b hbA
  set x : G := y⁻¹ * (b * y * b⁻¹)
  have hxP : x ∈ P :=
    P.mul_mem (P.inv_mem hyP) ((Subgroup.mem_normalizer_iff.mp (hAP hbA) y).mp hyP)
  have hx1 : x ≠ 1 := by
    intro h1
    apply hby
    exact mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp h1).symm
  have hxinv : b * x * b⁻¹ = x⁻¹ := z3_inv_conj hb2 y
  have hact : ∀ a : A, (a : G) * x * (a : G)⁻¹ = x ∨ (a : G) * x * (a : G)⁻¹ = x⁻¹ :=
    z3_action_on_commutator hAcomm hA2 hB hbA hyB hby
  obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf x = 3 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hP ⟨x, hxP⟩
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hx1
    rwa [pow_zero, orderOf_eq_one_iff] at hk
  have h3dvd : 3 ∣ orderOf x := by rw [hk]; exact dvd_pow_self 3 hk0
  set x₀ : G := x ^ (orderOf x / 3) with hx₀
  have hx₀ord : orderOf x₀ = 3 :=
    orderOf_pow_orderOf_div (by rw [hk]; positivity) h3dvd
  have hx₀P : x₀ ∈ P := P.pow_mem hxP _
  have hact₀ : ∀ a : A, (a : G) * x₀ * (a : G)⁻¹ = x₀ ∨ (a : G) * x₀ * (a : G)⁻¹ = x₀⁻¹ := by
    intro a
    rcases hact a with h | h
    · left
      rw [hx₀, ← conj_pow, h]
    · right
      rw [hx₀, ← conj_pow, h, inv_pow]
  have hconj : ∀ a : A, ∀ g ∈ Subgroup.zpowers x₀,
      (a : G) * g * (a : G)⁻¹ ∈ Subgroup.zpowers x₀ := by
    intro a g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases hact₀ a with h | h
    · rw [← conj_zpow, h]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x₀) i
    · rw [← conj_zpow, h]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x₀)) i
  refine ⟨Subgroup.zpowers x₀, Subgroup.zpowers_le.mpr hx₀P, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hx₀ord]
  · intro a ha
    refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun hg => hconj ⟨a, ha⟩ g hg, fun hg => ?_⟩
    have h1 := hconj ⟨a⁻¹, A.inv_mem ha⟩ _ hg
    have h2 : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
    rwa [h2] at h1
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg c hc
      have h1 := hconj ⟨c, hB₀A hc⟩ g⁻¹ (Subgroup.inv_mem _ hg)
      have h2 : ⁅g, c⁆ = g * (c * g⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
      rw [h2]
      exact Subgroup.mul_mem _ hg h1
    · rw [Subgroup.zpowers_le]
      have hb₀ : b * x₀ * b⁻¹ = x₀⁻¹ := by rw [hx₀, ← conj_pow, hxinv, inv_pow]
      have hcomm : ⁅x₀, b⁆ = x₀ * x₀ := by
        have h1 : x₀ * b * x₀⁻¹ * b⁻¹ = x₀ * (b * x₀ * b⁻¹)⁻¹ := by group
        rw [commutatorElement_def, h1, hb₀, inv_inv]
      have hmem : x₀ * x₀ ∈ ⁅Subgroup.zpowers x₀, B₀⁆ :=
        hcomm ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x₀) hbB₀
      have hx₀3 : x₀ ^ 3 = 1 := hx₀ord ▸ pow_orderOf_eq_one x₀
      have hx₀eq : (x₀ * x₀) * (x₀ * x₀) = x₀ := by
        calc (x₀ * x₀) * (x₀ * x₀) = x₀ * x₀ ^ 3 := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = x₀ := by rw [hx₀3, mul_one]
      have h1 := Subgroup.mul_mem _ hmem hmem
      rwa [hx₀eq] at h1

section Hyperplane

variable {W : Type} [CommGroup W] [Finite W]

private theorem z3_exists_hyperplane {P A B₀ : Subgroup (MulAut W)} (hP : IsPGroup 3 P)
    (hA : IsElemAbelian2 A) (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut W)))
    (hB₀A : B₀ ≤ A) (hne : ⁅P, B₀⁆ ≠ ⊥) :
    ∃ B : Subgroup A, B.index = 2 ∧ ∃ y ∈ P,
      (∀ c : B, ((c : A) : MulAut W) * y = y * c) ∧ ∃ b ∈ B₀, b * y ≠ y * b := by
  classical
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [le_bot_iff.mp hB₀A]
    exact Subgroup.commutator_bot_right P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => Subtype.ext (hA.2 a a.2) }
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P (conjAut hAP)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  by_contra hcon
  push Not at hcon
  have hsmul : ∀ (b : A) (x : P), (((b • x : P)) : MulAut W) =
      (b : MulAut W) * x * (b : MulAut W)⁻¹ := fun b x => rfl
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P) ≤
      CFSG.fixedPointSubgroup (B₀.subgroupOf A) P := by
    refine iSup₂_le fun B hB x hx => ?_
    have hc : ∀ c : B, ((c : A) : MulAut W) * (x : MulAut W) = x * (c : MulAut W) := by
      intro c
      have h1 : (c : A) • x = x := hx c
      have h2 := congrArg (fun z : P => (z : MulAut W)) h1
      simp only [hsmul] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    intro a'
    have h3 : ((a' : A) • x : P) = x := by
      apply Subtype.ext
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr
        (hcon B hB x x.2 hc ((a' : A) : MulAut W) (Subgroup.mem_subgroupOf.mp a'.2))
    exact h3
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hy' : (⟨y, hy⟩ : P) ∈ CFSG.fixedPointSubgroup (B₀.subgroupOf A) P :=
    hle (hgen ▸ Subgroup.mem_top _)
  have h1 : (⟨b, hB₀A hb⟩ : A) • (⟨y, hy⟩ : P) = ⟨y, hy⟩ := hy' ⟨⟨b, hB₀A hb⟩, hb⟩
  have h2 := congrArg (fun z : P => (z : MulAut W)) h1
  simp only [hsmul] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem d392_order_three {P A B₀ : Subgroup (MulAut W)} (hP : IsPGroup 3 P)
    (hA : IsElemAbelian2 A) (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut W)))
    (hB₀A : B₀ ≤ A) (hne : ⁅P, B₀⁆ ≠ ⊥) :
    ∃ X : Subgroup (MulAut W), X ≤ P ∧ Nat.card ↥X = 3 ∧
      A ≤ Subgroup.normalizer (X : Set (MulAut W)) ∧ ⁅X, B₀⁆ = X := by
  obtain ⟨B, hB, y, hyP, hyB, b, hbB₀, hby⟩ := z3_exists_hyperplane hP hA hAP hB₀A hne
  exact z3_order_three_of_hyperplane hP hA.1 hA.2 hAP hB₀A hB hyP hyB hbB₀ hby

end Hyperplane

end CFSG.Quasithin
