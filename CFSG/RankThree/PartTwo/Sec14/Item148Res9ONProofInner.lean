module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONThree

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res9ON

open CFSG CFSG.ComponentClassification.OuterAutomorphisms

theorem mulAut_eq_one_of_central148 {X : Type*} [Group X] (hX : Group.IsPerfect X) (σ : MulAut X)
    (h : ∀ x : X, x⁻¹ * σ x ∈ Subgroup.center X) : σ = 1 := by
  let δ : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * σ x, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        show (x * y)⁻¹ * σ (x * y) = x⁻¹ * σ x * (y⁻¹ * σ y)
        calc (x * y)⁻¹ * σ (x * y) = y⁻¹ * (x⁻¹ * σ x) * σ y := by simp [mul_assoc]
          _ = x⁻¹ * σ x * y⁻¹ * σ y := by rw [hc]
          _ = x⁻¹ * σ x * (y⁻¹ * σ y) := by simp [mul_assoc] }
  have hker : _root_.commutator X ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hX.commutator_eq_top] at hker
  ext x
  have hx : δ x = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top x))
  have := congrArg Subtype.val hx
  simp only [OneMemClass.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

@[expose] noncomputable def centerQuotientAut {X : Type*} [Group X] (σ : MulAut X) :
    MulAut (X ⧸ Subgroup.center X) :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) σ (Subgroup.map_center_eq σ)

theorem centerQuotientAut_pow {X : Type*} [Group X] (σ : MulAut X) (n : ℕ) :
    centerQuotientAut σ ^ n = centerQuotientAut (σ ^ n) := by
  induction n with
  | zero =>
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  | succ n ih =>
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [pow_succ, pow_succ, MulAut.mul_apply, ih]
      rfl

theorem exists_conj_of_pow_three_ON
    {X : Type*} [Group X] [Finite X] (hXq : IsQuasisimple X)
    (htc : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) (σ : MulAut X)
    (hσ : σ ^ 3 = 1) : ∃ x : X, σ = MulAut.conj x := by
  obtain ⟨-, ⟨ψ⟩⟩ := htc
  set Z := Subgroup.center X with hZdef
  have hout : Nat.card (Outer (X ⧸ Z)) ∣ 2 :=
    CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨ψ⟩
  set o : Outer (X ⧸ Z) := QuotientGroup.mk' (inner (X ⧸ Z)) (centerQuotientAut σ) with hodef
  have ho3 : o ^ 3 = 1 := by
    rw [hodef, ← map_pow, centerQuotientAut_pow, hσ]
    have h1 : centerQuotientAut (1 : MulAut X) = 1 := by
      refine MulEquiv.ext fun q => ?_
      induction q using QuotientGroup.induction_on with
      | H x => rfl
    rw [h1, map_one]
  have ho : o = 1 := by
    have h1 : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one ho3
    have h2 : orderOf o ∣ 2 := (orderOf_dvd_natCard o).trans hout
    have h3 : orderOf o = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · rw [h] at h2
        norm_num at h2
    exact orderOf_eq_one_iff.mp h3
  have hmem : centerQuotientAut σ ∈ inner (X ⧸ Z) := (QuotientGroup.eq_one_iff _).mp ho
  obtain ⟨tbar, htbar⟩ := hmem
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective Z tbar
  refine ⟨t, ?_⟩
  have hτ : (MulAut.conj t)⁻¹ * σ = 1 := by
    refine mulAut_eq_one_of_central148 hXq.1 _ fun x => ?_
    have h1 := congrArg (fun f : MulAut (X ⧸ Z) => f (x : X ⧸ Z)) htbar
    simp only [MulAut.conj_apply, QuotientGroup.mk'_apply] at h1
    have h2 : (t * x * t⁻¹)⁻¹ * σ x ∈ Z := by
      rw [← QuotientGroup.eq]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact h1
    have h3 : x⁻¹ * ((MulAut.conj t)⁻¹ * σ) x = t⁻¹ * ((t * x * t⁻¹)⁻¹ * σ x) * t := by
      rw [MulAut.mul_apply, MulAut.inv_def, MulAut.conj_symm_apply]
      group
    rw [h3]
    have hw := Subgroup.mem_center_iff.mp h2 t⁻¹
    rw [hw, mul_assoc, inv_mul_cancel, mul_one]
    exact h2
  calc σ = MulAut.conj t * ((MulAut.conj t)⁻¹ * σ) := by group
    _ = MulAut.conj t := by rw [hτ, mul_one]

theorem factorization_ON_three : (460815505920 : ℕ).factorization 3 = 4 := by
  rw [show (460815505920 : ℕ) = 3 ^ 4 * 5689080320 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_elemAbelian_le_ON
    {T : Type} [Group T] [Finite T] (ψ : T ≃* CFSG.Blueprint.NativeSporadic.ON)
    {P : Subgroup T} (hP : IsPGroup 3 P) :
    ∃ S : Subgroup T, P ≤ S ∧ Nat.card S = 81 ∧ CFSG.Assembly.IsElemAbelian 3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨Q₀, hQ₀⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_sylow_elemAbelian_ON
    T ψ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T Q₀ Q
  refine ⟨Q, hPQ, ?_, ?_⟩
  · rw [Sylow.card_eq_multiplicity, Nat.card_congr ψ.toEquiv, CFSG.Sporadic.ON.card_ON,
      factorization_ON_three]
    norm_num
  · have hQeq : (Q : Subgroup T) = (Q₀ : Subgroup T).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have hconj : ∀ y ∈ (Q : Subgroup T), ∃ y₀ ∈ (Q₀ : Subgroup T), y = g * y₀ * g⁻¹ := by
      intro y hy
      rw [hQeq] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨y₀, hy₀, rfl⟩
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a₀, ha₀, ha⟩ := hconj a a.2
      obtain ⟨b₀, hb₀, hb⟩ := hconj b b.2
      have hab : a₀ * b₀ = b₀ * a₀ :=
        congrArg Subtype.val (hQ₀.1.is_comm.comm ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, hb]
      calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) = g * (a₀ * b₀) * g⁻¹ := by group
        _ = g * (b₀ * a₀) * g⁻¹ := by rw [hab]
        _ = g * b₀ * g⁻¹ * (g * a₀ * g⁻¹) := by group
    · obtain ⟨y₀, hy₀, rfl⟩ := hconj y hy
      rw [conj_pow, hQ₀.2 y₀ hy₀]
      group

end CFSG.RankThree.PartTwo.Sec14.Res9ON
