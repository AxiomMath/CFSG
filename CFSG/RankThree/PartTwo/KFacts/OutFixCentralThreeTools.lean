module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence congr_conj)

@[expose] def FixCommInner (X : Type*) [Group X] (z : X) : Prop :=
  ∀ σ τ : MulAut X, σ z = z → τ z = z →
    σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range

variable {X Y : Type*} [Group X] [Group Y]

theorem congr_injective (e : X ≃* Y) : Function.Injective (MulAut.congr e) :=
  (MulAut.congr e).injective

theorem FixCommInner.of_mulEquiv (e : X ≃* Y) {z : X} (h : FixCommInner Y (e z)) :
    FixCommInner X z := by
  intro σ τ hσ hτ
  have hσ' : MulAut.congr e σ (e z) = e z := by
    change e (σ (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hσ]
  have hτ' : MulAut.congr e τ (e z) = e z := by
    change e (τ (e.symm (e z))) = e z
    rw [e.symm_apply_apply, hτ]
  obtain ⟨y, hy⟩ := h _ _ hσ' hτ'
  refine ⟨e.symm y, congr_injective e ?_⟩
  rw [congr_conj, e.apply_symm_apply, hy, map_mul, map_mul, map_mul, map_inv, map_inv]

section Quotient

variable (N : Subgroup X) [N.Normal]

@[expose] noncomputable def quotientAut (hN : ∀ σ : MulAut X, Subgroup.map (σ : X →* X) N = N) :
    MulAut X →* MulAut (X ⧸ N) where
  toFun σ := QuotientGroup.congr N N σ (hN σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

variable {N}

theorem quotientAut_mk (hN : ∀ σ : MulAut X, Subgroup.map (σ : X →* X) N = N) (σ : MulAut X)
    (x : X) : quotientAut N hN σ (x : X ⧸ N) = ((σ x : X) : X ⧸ N) :=
  rfl

theorem quotientAut_conj (hN : ∀ σ : MulAut X, Subgroup.map (σ : X →* X) N = N) (x : X) :
    quotientAut N hN (MulAut.conj x) = MulAut.conj (x : X ⧸ N) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y => rfl

theorem eq_one_of_quotientAut_eq_one [Group.IsPerfect X] (hNZ : N ≤ Subgroup.center X)
    (hN : ∀ σ : MulAut X, Subgroup.map (σ : X →* X) N = N) {ρ : MulAut X}
    (h : quotientAut N hN ρ = 1) : ρ = 1 := by
  have hc : ∀ s : X, s⁻¹ * ρ.toMonoidHom s ∈ Subgroup.center X := by
    intro s
    apply hNZ
    have hs := congrArg (fun φ : MulAut (X ⧸ N) => φ (s : X ⧸ N)) h
    simp only [quotientAut_mk, MulAut.one_apply] at hs
    exact QuotientGroup.eq.mp hs.symm
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    ρ.toMonoidHom hc
  ext s
  exact congrArg (fun f : X →* X => f s) hid

theorem FixCommInner.of_quotient [Group.IsPerfect X] (hNZ : N ≤ Subgroup.center X)
    (hN : ∀ σ : MulAut X, Subgroup.map (σ : X →* X) N = N) {z : X}
    (h : FixCommInner (X ⧸ N) (z : X ⧸ N)) : FixCommInner X z := by
  intro σ τ hσ hτ
  have hσ' : quotientAut N hN σ (z : X ⧸ N) = z := by rw [quotientAut_mk, hσ]
  have hτ' : quotientAut N hN τ (z : X ⧸ N) = z := by rw [quotientAut_mk, hτ]
  obtain ⟨y, hy⟩ := h _ _ hσ' hτ'
  induction y using QuotientGroup.induction_on with
  | H x =>
    refine ⟨x, ?_⟩
    have h1 : quotientAut N hN ((MulAut.conj x)⁻¹ * (σ * τ * σ⁻¹ * τ⁻¹)) = 1 := by
      rw [map_mul, map_inv, quotientAut_conj, map_mul, map_mul, map_mul, map_inv, map_inv, ← hy,
        inv_mul_cancel]
    have h2 := eq_one_of_quotientAut_eq_one hNZ hN h1
    exact (inv_mul_eq_one.mp h2)

end Quotient

theorem FixCommInner.of_center_quotient [Group.IsPerfect X]
    (hcomm : ∀ α β : MulAut (X ⧸ Subgroup.center X),
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X ⧸ Subgroup.center X →* _).range) (z : X) :
    FixCommInner X z :=
  FixCommInner.of_quotient le_rfl (fun σ => Subgroup.map_center_eq σ) fun α β _ _ => hcomm α β

theorem mul_comm_of_card_le_four {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 4)
    (a b : G) : a * b = b * a := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (show Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3 ∨ Nat.card G = 4 by omega) with
    h1 | h2 | h3 | h4
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card h2
    exact IsCyclic.commGroup.mul_comm a b
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic G := isCyclic_of_prime_card h3
    exact IsCyclic.commGroup.mul_comm a b
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc : IsMulCommutative G :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
    exact hc.is_comm.comm a b

theorem finite_outer (Y : Type*) [Group Y] [Finite Y] : Finite (Outer Y) := by
  have : Finite (MulAut Y) := MulEquiv.finite_left
  infer_instance

theorem commutator_mem_range_conj_of_card_outer_le_four [Finite Y]
    (h : Nat.card (Outer Y) ≤ 4) (α β : MulAut Y) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : Y →* MulAut Y).range := by
  have := finite_outer Y
  have hc := mul_comm_of_card_le_four h (QuotientGroup.mk α : Outer Y) (QuotientGroup.mk β)
  change α * β * α⁻¹ * β⁻¹ ∈ inner Y
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc]
  group

theorem fixCommInner_of_card_outer_le_four [Group.IsPerfect X] [Finite X]
    (e : X ⧸ Subgroup.center X ≃* Y) (h : Nat.card (Outer Y) ≤ 4) (z : X) :
    FixCommInner X z := by
  have h' : Nat.card (Outer (X ⧸ Subgroup.center X)) ≤ 4 := by
    rwa [Nat.card_congr (equivalence e).toEquiv]
  exact FixCommInner.of_center_quotient (commutator_mem_range_conj_of_card_outer_le_four h') z

section CenterThreePrime

variable (X)

@[expose] def centerThreePrime : Subgroup X where
  carrier := {x | x ∈ Subgroup.center X ∧ ¬ 3 ∣ orderOf x}
  mul_mem' {a b} ha hb := by
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun h3 => ?_⟩
    have hcomm : Commute a b := Subgroup.mem_center_iff.mp ha.1 b |>.symm
    have h := h3.trans hcomm.orderOf_mul_dvd_lcm
    rcases (Nat.Prime.dvd_lcm Nat.prime_three).mp h with h' | h'
    · exact ha.2 h'
    · exact hb.2 h'
  one_mem' := ⟨Subgroup.one_mem _, by rw [orderOf_one]; norm_num⟩
  inv_mem' {a} ha := ⟨Subgroup.inv_mem _ ha.1, by rw [orderOf_inv]; exact ha.2⟩

variable {X}

theorem mem_centerThreePrime {x : X} :
    x ∈ centerThreePrime X ↔ x ∈ Subgroup.center X ∧ ¬ 3 ∣ orderOf x :=
  Iff.rfl

theorem centerThreePrime_le_center : centerThreePrime X ≤ Subgroup.center X :=
  fun _ hx => hx.1

instance centerThreePrime_normal : (centerThreePrime X).Normal :=
  Subgroup.normal_of_le_center centerThreePrime_le_center

theorem map_centerThreePrime (σ : MulAut X) :
    Subgroup.map (σ : X →* X) (centerThreePrime X) = centerThreePrime X := by
  have hle : ∀ ρ : MulAut X, Subgroup.map (ρ : X →* X) (centerThreePrime X) ≤
      centerThreePrime X := by
    rintro ρ _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_center_eq ρ]
      exact Subgroup.mem_map_of_mem _ hx.1
    · change ¬ 3 ∣ orderOf (ρ x)
      rw [MulEquiv.orderOf_eq]
      exact hx.2
  refine le_antisymm (hle σ) fun x hx => ⟨σ.symm x, hle σ⁻¹ ⟨x, hx, rfl⟩, ?_⟩
  exact σ.apply_symm_apply x

theorem orderOf_mk_centerThreePrime {z : X} (hz3 : orderOf z = 3) :
    orderOf (z : X ⧸ centerThreePrime X) = 3 := by
  have h3 : ((z : X ⧸ centerThreePrime X)) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hz3, pow_orderOf_eq_one, QuotientGroup.mk_one]
  refine orderOf_eq_prime h3 fun h1 => ?_
  rw [QuotientGroup.eq_one_iff] at h1
  exact h1.2 (by rw [hz3])

theorem not_three_dvd_card_centerThreePrime [Finite X] :
    ¬ 3 ∣ Nat.card (centerThreePrime X) := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centerThreePrime X) 3 h
  have hx' : orderOf (x : X) = 3 := by rw [Subgroup.orderOf_coe, hx]
  exact x.2.2 (by rw [hx'])

theorem isPGroup_center_quotient_centerThreePrime [Finite X] (hq : CFSG.IsQuasisimple X) :
    IsPGroup 3 (Subgroup.center (X ⧸ centerThreePrime X)) := by
  obtain ⟨-, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hq (centerThreePrime X)
    centerThreePrime_le_center
  intro y
  have hy : (y : X ⧸ centerThreePrime X) ∈ (Subgroup.center X).map
      (QuotientGroup.mk' (centerThreePrime X)) := hcen ▸ y.2
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨a, m, hm3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3 (by norm_num)
  refine ⟨a, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, ← hxy, QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow,
    Subgroup.coe_one, QuotientGroup.eq_one_iff]
  refine ⟨Subgroup.pow_mem _ hx _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) ⟨m, hm⟩, hm,
    Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)]
  exact hm3

theorem FixCommInner.of_centerThreePrime (hq : CFSG.IsQuasisimple X) {z : X}
    (h : FixCommInner (X ⧸ centerThreePrime X) (z : X ⧸ centerThreePrime X)) :
    FixCommInner X z := by
  have : Group.IsPerfect X := hq.1
  exact FixCommInner.of_quotient centerThreePrime_le_center map_centerThreePrime h

theorem quotient_centerThreePrime_facts (hq : CFSG.IsQuasisimple X) {z : X}
    (hz : z ∈ Subgroup.center X) :
    CFSG.IsQuasisimple (X ⧸ centerThreePrime X) ∧
      Nonempty ((X ⧸ centerThreePrime X) ⧸ Subgroup.center (X ⧸ centerThreePrime X) ≃*
        X ⧸ Subgroup.center X) ∧
      (z : X ⧸ centerThreePrime X) ∈ Subgroup.center (X ⧸ centerThreePrime X) := by
  obtain ⟨hq', -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hq (centerThreePrime X)
    centerThreePrime_le_center
  refine ⟨hq', ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ centerThreePrime_le_center)⟩, ?_⟩
  rw [hcen]
  exact ⟨z, hz, rfl⟩

end CenterThreePrime

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
