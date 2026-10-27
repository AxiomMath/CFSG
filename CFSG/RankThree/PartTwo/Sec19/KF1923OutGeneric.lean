module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.GH74.Generic.S45.LOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Out

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence centerQuotientOuterHom)

variable {X Y : Type} [Group X] [Group Y]

theorem comm_of_sq_eq_one_mem {G : Type} [Group G] (P : Subgroup G)
    (hsq : ∀ z ∈ P, z ^ 2 = 1) : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have hinv : ∀ z ∈ P, z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq z hz)
  intro x hx y hy
  have hxy : x * y ∈ P := P.mul_mem hx hy
  calc x * y = (x * y)⁻¹ := (hinv _ hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv y hy, hinv x hx]

theorem outTwoAbelian_of_outTwoExpTwo
    (h : CFSG.RankThree.PartTwo.Late.OutTwoExpTwo X) : OutTwoAbelian X := by
  intro P hP x hx y hy
  exact comm_of_sq_eq_one_mem P (fun z hz => h P hP z hz) x hx y hy

theorem outTwoAbelian_of_outTwoCyclic (h : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X) :
    OutTwoAbelian X := by
  intro P hP x hx y hy
  haveI : IsCyclic P := h P hP
  have hc := (IsCyclic.commutative (α := P)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val hc

theorem outTwoCyclic_of_isCyclic_outer (h : IsCyclic (Outer X)) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X := by
  intro P _
  haveI := h
  exact Subgroup.isCyclic P

theorem isCyclic_of_natCard_le_two {P : Type} [Group P] (hpos : 0 < Nat.card P)
    (hle : Nat.card P ≤ 2) : IsCyclic P := by
  interval_cases hc : Nat.card P
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hc).1
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card hc

theorem isCyclic_of_natCard_dvd_two {P : Type} [Group P] (hd : Nat.card P ∣ 2) : IsCyclic P :=
  isCyclic_of_natCard_le_two (Nat.pos_of_dvd_of_pos hd (by norm_num))
    (Nat.le_of_dvd (by norm_num) hd)

theorem outTwoCyclic_of_card_le_two (hpos : 0 < Nat.card (Outer X))
    (h : Nat.card (Outer X) ≤ 2) : CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X := by
  intro P _
  have hd : Nat.card P ∣ Nat.card (Outer X) := Subgroup.card_subgroup_dvd_card P
  exact isCyclic_of_natCard_le_two (Nat.pos_of_dvd_of_pos hd hpos)
    ((Nat.le_of_dvd hpos hd).trans h)

theorem finite_outer_of_card_dvd {m : ℕ} (hm : Odd m) (h : Nat.card (Outer X) ∣ 2 * m) :
    Finite (Outer X) := by
  have hm0 : 0 < m := hm.pos
  exact Nat.finite_of_card_ne_zero (fun h0 => by
    rw [h0, zero_dvd_iff] at h
    omega)

theorem natCard_dvd_two_of_card_dvd {m : ℕ} (hm : Odd m)
    (h : Nat.card (Outer X) ∣ 2 * m) (P : Subgroup (Outer X)) (hP : IsPGroup 2 P) :
    Nat.card P ∣ 2 := by
  haveI := finite_outer_of_card_dvd hm h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ 2 * m := (Subgroup.card_subgroup_dvd_card P).trans h
  rw [hk] at hdvd ⊢
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
    hdvd

theorem outTwoExpTwo_of_card_dvd {m : ℕ} (hm : Odd m) (h : Nat.card (Outer X) ∣ 2 * m) :
    CFSG.RankThree.PartTwo.Late.OutTwoExpTwo X := by
  intro P hP x hx
  haveI := finite_outer_of_card_dvd hm h
  have hd := natCard_dvd_two_of_card_dvd hm h P hP
  have h2 : (⟨x, hx⟩ : P) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hd)
  simpa using congrArg Subtype.val h2

theorem outTwoCyclic_of_card_dvd {m : ℕ} (hm : Odd m) (h : Nat.card (Outer X) ∣ 2 * m) :
    CFSG.ClassicalInvolution.Nobq.OutTwoCyclic X := by
  intro P hP
  exact isCyclic_of_natCard_dvd_two (natCard_dvd_two_of_card_dvd hm h P hP)

theorem outTwoAbelian_of_odd_commutator (h : Odd (Nat.card (commutator (Outer X)))) :
    OutTwoAbelian X := by
  intro P hP x hx y hy
  have hcP : x * y * x⁻¹ * y⁻¹ ∈ P :=
    P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
  have hcQ : x * y * x⁻¹ * y⁻¹ ∈ commutator (Outer X) := by
    rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  haveI : Finite (commutator (Outer X)) := Nat.finite_of_card_ne_zero h.pos.ne'
  obtain ⟨k, hk⟩ := hP ⟨x * y * x⁻¹ * y⁻¹, hcP⟩
  have hkc : (x * y * x⁻¹ * y⁻¹) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hd1 : orderOf (⟨x * y * x⁻¹ * y⁻¹, hcQ⟩ : commutator (Outer X)) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa using hkc
  have hd2 : orderOf (⟨x * y * x⁻¹ * y⁻¹, hcQ⟩ : commutator (Outer X)) ∣
      Nat.card (commutator (Outer X)) :=
    orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (commutator (Outer X))) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr h)
  have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h1)
  have key : x * y * (y * x)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
  exact mul_inv_eq_one.mp (key.trans hc1)

theorem sq_eq_one_of_sq_inner {A : Type} [Group A]
    (h : ∀ α : MulAut A, ∃ w : A, α ^ 2 = MulAut.conj w) : ∀ x : Outer A, x ^ 2 = 1 := by
  intro x
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  obtain ⟨w, hw⟩ := h α
  exact MonoidHom.mem_range.mpr ⟨w, hw.symm⟩

theorem sq_eq_one_of_outSq {A : Type} [Group A]
    (h : CFSG.EvenSporadicStandard.SolomonRed.OutSq A) : ∀ x : Outer A, x ^ 2 = 1 := by
  apply sq_eq_one_of_sq_inner
  intro α
  obtain ⟨a, ha⟩ := h α
  refine ⟨a, MulEquiv.ext fun y => ?_⟩
  rw [MulAut.conj_apply, pow_two, MulAut.mul_apply]
  exact ha y

theorem outTwoExpTwo_of_forall_sq {A : Type} [Group A] (h : ∀ x : Outer A, x ^ 2 = 1) :
    CFSG.RankThree.PartTwo.Late.OutTwoExpTwo A :=
  fun _ _ x _ => h x

theorem outTwoAbelian_of_mulEquiv (e : X ≃* Y) (h : OutTwoAbelian Y) : OutTwoAbelian X := by
  intro P hP x hx y hy
  have hc := h (P.map (equivalence e).toMonoidHom) (hP.map _) ((equivalence e) x)
    ⟨x, hx, rfl⟩ ((equivalence e) y) ⟨y, hy, rfl⟩
  apply (equivalence e).injective
  rw [map_mul, map_mul]
  exact hc

theorem outTwoExpTwo_of_mulEquiv (e : X ≃* Y)
    (h : CFSG.RankThree.PartTwo.Late.OutTwoExpTwo Y) :
    CFSG.RankThree.PartTwo.Late.OutTwoExpTwo X := by
  intro P hP x hx
  apply (equivalence e).injective
  rw [map_pow, map_one]
  exact h (P.map (equivalence e).toMonoidHom) (hP.map _) ((equivalence e) x) ⟨x, hx, rfl⟩

theorem outTwoExpTwo_of_injective (f : Outer X →* Outer Y) (hf : Function.Injective f)
    (h : CFSG.RankThree.PartTwo.Late.OutTwoExpTwo Y) :
    CFSG.RankThree.PartTwo.Late.OutTwoExpTwo X := by
  intro P hP x hx
  apply hf
  rw [map_pow, map_one]
  exact h (P.map f) (hP.map f) (f x) ⟨x, hx, rfl⟩

theorem isCyclic_outer_of_mulEquiv (e : X ≃* Y) (h : IsCyclic (Outer Y)) :
    IsCyclic (Outer X) :=
  haveI := h
  isCyclic_of_surjective (equivalence e).symm.toMonoidHom (equivalence e).symm.surjective

theorem natCard_outer_of_mulEquiv (e : X ≃* Y) : Nat.card (Outer X) = Nat.card (Outer Y) :=
  Nat.card_congr (equivalence e).toEquiv

noncomputable def centerQuotEquiv {M : Type} [Group M] (e : X ≃* M) :
    X ⧸ Subgroup.center X ≃* M ⧸ Subgroup.center M :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center M) e (Subgroup.map_center_eq e)

theorem outTwoAbelian_of_perfect_quotient {H : Type} [Group H] (hX : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* H) (h : Odd (Nat.card (commutator (Outer H)))) :
    OutTwoAbelian X := by
  haveI := hX
  exact outTwoAbelian_of_odd_commutator
    (CFSG.GH74.Generic.S45.odd_card_commutator_outer_of_perfect hX
      (CFSG.GH74.Generic.S45.odd_card_commutator_outer_of_equiv e h))

theorem outTwoExpTwo_of_perfect_quotient {H : Type} [Group H] (hX : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* H) (h : CFSG.RankThree.PartTwo.Late.OutTwoExpTwo H) :
    CFSG.RankThree.PartTwo.Late.OutTwoExpTwo X := by
  haveI := hX
  exact outTwoExpTwo_of_injective (centerQuotientOuterHom X)
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective X)
    (outTwoExpTwo_of_mulEquiv e h)

end CFSG.RankThree.PartTwo.Late
