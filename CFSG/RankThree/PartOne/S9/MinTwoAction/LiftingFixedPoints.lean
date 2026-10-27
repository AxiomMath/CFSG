module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelCore
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingStructure
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.Quotient36 SemidirectProduct
open scoped IsMulCommutative commutatorElement

section Setup

variable {p q d : ℕ} {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem orderOf_inl_dvd (hS : Nat.card S = 2 ^ d) (s : S) :
    orderOf (inl s : S ⋊[φ] A) ∣ 2 ^ d := by
  rw [orderOf_injective (inl : S →* S ⋊[φ] A) inl_injective]
  exact hS ▸ orderOf_dvd_natCard s

theorem not_dvd_orderOf_inl (hq : q.Prime) (hq2 : q ≠ 2) (hS : Nat.card S = 2 ^ d) (s : S) :
    ¬ q ∣ orderOf (inl s : S ⋊[φ] A) := fun hdvd =>
  hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
    (hq.dvd_of_dvd_pow (hdvd.trans (orderOf_inl_dvd (A := A) (φ := φ) hS s))))

theorem not_dvd_card_semidirect [Finite A] [IsElementaryAbelian p A] (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (hS : Nat.card S = 2 ^ d) :
    ¬ q ∣ Nat.card (S ⋊[φ] A) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, hS, hk]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm

theorem finite_zpowers_inl [Finite S] (s : S) : Finite (Subgroup.zpowers (inl s : S ⋊[φ] A)) := by
  refine finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card S, Nat.card_pos, ?_⟩)
  rw [← map_pow, pow_card_eq_one', map_one]

theorem isPGroup_zpowers_inl (hS : Nat.card S = 2 ^ d) (s : S) :
    IsPGroup 2 (Subgroup.zpowers (inl s : S ⋊[φ] A)) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (orderOf_inl_dvd (A := A) (φ := φ) hS s)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)

theorem dim_fixed_le_four [Finite S] {D : Type*} [Group D] [Finite D]
    [MulDistribMulAction (S ⋊[φ] A) D] (hq : q.Prime) (hq2 : q ≠ 2) (hS : Nat.card S = 2 ^ d)
    (hDq : IsPGroup q D) (hDexp : ∀ x : D, x ^ q = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hrank : ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) ≤ 3) (s : S)
    (hs : s ≠ 1) :
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : Fact (IsPGroup q D) := ⟨hDq⟩
    Module.finrank (ZMod q) ↥(Module.End.eigenspace
      (frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s)) 1) ≤ 4 := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨hDq⟩
  have := finite_zpowers_inl (A := A) (φ := φ) s
  have hp2 := isPGroup_zpowers_inl (A := A) (φ := φ) hS s
  exact (finrank_eigenspace_le_pRank q hq2 hDexp (inl s) hp2).trans
    ((pRank_quotient_commutator_le q hDexp hDcl
      (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D)).1 (hrank s hs))

theorem exists_fixed_lift [Finite S] {D : Type*} [Group D] [Finite D]
    [MulDistribMulAction (S ⋊[φ] A) D] (hq : q.Prime) (hq2 : q ≠ 2) (hS : Nat.card S = 2 ^ d)
    (hDq : IsPGroup q D) (s : S)
    (w : Additive (D ⧸ frattini D)) (hw0 : w ≠ 0) :
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : Fact (IsPGroup q D) := ⟨hDq⟩
    frattiniRep (E := S ⋊[φ] A) (X := D) q (inl s) w = w →
      ∃ x : D, (inl s : S ⋊[φ] A) • x = x ∧ x ∉ frattini D := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨hDq⟩
  intro hw
  have := finite_zpowers_inl (A := A) (φ := φ) s
  have hp2 := isPGroup_zpowers_inl (A := A) (φ := φ) hS s
  obtain ⟨v, rfl⟩ : ∃ v : D ⧸ frattini D, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
  rw [frattiniRep_apply] at hw
  have hv : (letI := frattiniQuotientAction (S ⋊[φ] A) D; (inl s : S ⋊[φ] A) • v = v) :=
    Additive.ofMul.injective hw
  have hmem := fixed_mk_eq_image (E := S ⋊[φ] A) (X := D) hq2 (inl s) hp2
  have hv' : v ∈ {v : D ⧸ frattini D | (letI := frattiniQuotientAction (S ⋊[φ] A) D;
      (inl s : S ⋊[φ] A) • v = v)} := hv
  rw [hmem] at hv'
  obtain ⟨c, hc, rfl⟩ := hv'
  refine ⟨c, hc, fun hcΦ => hw0 ?_⟩
  have : (QuotientGroup.mk' (frattini D)) c = 1 := (QuotientGroup.eq_one_iff c).mpr hcΦ
  rw [ofMul_eq_zero]
  exact this

end Setup

section CommutatorFixed

section RankSucc

variable {E : Type*} [Group E] {D : Type*} [Group D] [Finite D] [MulDistribMulAction E D] {q : ℕ}

theorem rank_succ_of_fixed (hq : q.Prime) (hDexp : ∀ x : D, x ^ q = 1) (e : E)
    {Y : Subgroup D} (hYc : Y ≤ Subgroup.center D) (hYfix : ∀ y ∈ Y, e • y = y) {m : ℕ}
    (hYcard : Nat.card Y = q ^ m) {x : D} (hxfix : e • x = x) (hx : x ∉ Y) :
    m + 1 ≤ CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers e) D) := by
  have : Fact q.Prime := ⟨hq⟩
  set Fix := fixedPointSubgroup (Subgroup.zpowers e) D with hFix
  have hmemFix : ∀ y : D, e • y = y → y ∈ Fix := fun y hy =>
    (mem_fixedPointSubgroup_zpowers_iff e y).mpr hy
  have hcomm : ∀ a ∈ Y, a * x = x * a := fun a ha =>
    (Subgroup.mem_center_iff.mp (hYc ha) x).symm
  have hYcomm : IsMulCommutative Y :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hYc b.2) a)⟩⟩
  obtain ⟨hEcomm, hEcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card (p := q) hYcomm hx
    (hDexp x) hcomm
  have hEle : Y ⊔ Subgroup.zpowers x ≤ Fix := by
    refine sup_le (fun y hy => hmemFix y (hYfix y hy)) ?_
    rw [Subgroup.zpowers_le]
    exact hmemFix x hxfix
  have hexpFix : ∀ y : ↥Fix, y ^ q = 1 := fun y => Subtype.ext (by
    rw [Subgroup.coe_pow]; exact hDexp y)
  have hcommFix : IsMulCommutative ((Y ⊔ Subgroup.zpowers x).subgroupOf Fix) :=
    ⟨⟨fun a b => by
      apply Subtype.ext
      apply Subtype.ext
      show (a.1.1 : D) * b.1.1 = b.1.1 * a.1.1
      exact congrArg Subtype.val (hEcomm.is_comm.comm (⟨a.1.1, a.2⟩ : ↥(Y ⊔ Subgroup.zpowers x))
        (⟨b.1.1, b.2⟩ : ↥(Y ⊔ Subgroup.zpowers x)))⟩⟩
  have hcard : Nat.card ((Y ⊔ Subgroup.zpowers x).subgroupOf Fix) = q ^ (m + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEle).toEquiv, hEcard, hYcard, pow_succ]
  exact CFSG.RankThree.PartTwo.le_pRank_of_isMulCommutative hq hexpFix hcommFix hcard

end RankSucc


variable {p q d : ℕ} {S : Type*} [Group S] {A : Type*} [Group A] {φ : A →* MulAut S}

theorem commutator_fixed [Finite S] [IsElementaryAbelian 2 S] [Finite A]
    {D : Type*} [Group D] [Finite D] [MulDistribMulAction (S ⋊[φ] A) D]
    (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) (hq : q.Prime) (hq2 : q ≠ 2)
    (hS : Nat.card S = 2 ^ d) (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    [NeZero (Nat.card (S ⋊[φ] A) : ZMod q)]
    (hDq : IsPGroup q D) (hDexp : ∀ x : D, x ^ q = 1) (hDcl : commutator D ≤ Subgroup.center D)
    (hrank : ∀ s : S, s ≠ 1 →
      CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers (inl s : S ⋊[φ] A)) D) ≤ 3)
    (hlift : ∀ s : S, s ≠ 1 → ∃ x : D, (inl s : S ⋊[φ] A) • x = x ∧ x ∉ frattini D) :
    ∀ s : S, ∀ y ∈ commutator D, (inl s : S ⋊[φ] A) • y = y := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨hDq⟩
  have hq2' : (2 : ZMod q) ≠ 0 := by
    intro h
    have h1 : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h1)
  by_contra hcon
  push Not at hcon
  obtain ⟨s₀, y₀, hy₀, hne⟩ := hcon
  have hinv : CFSG.IsInvariant (S ⋊[φ] A) D (commutator D) :=
    isInvariant_of_characteristic (commutator D)
  have : IsElementaryAbelian q (commutator D) :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hDcl b.2) a)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hDexp x) }
  let σ' : Representation (ZMod q) (S ⋊[φ] A) (Additive (commutator D)) :=
    Theory.Representation.ofElementaryAbelianAction (A := S ⋊[φ] A) (G := ↥(commutator D))
      (p := q)
  have hσ' : ∀ (γ : S ⋊[φ] A) (y : commutator D),
      σ' γ (Additive.ofMul y) = Additive.ofMul (γ • y) := fun γ y =>
    Theory.Representation.ofElementaryAbelianAction_apply_ofMul (A := S ⋊[φ] A)
      (G := ↥(commutator D)) (p := q) γ y
  have hnt : ∃ n ∈ (inl : S →* S ⋊[φ] A).range, ∃ v, σ' n v ≠ v := by
    refine ⟨inl s₀, ⟨s₀, rfl⟩, Additive.ofMul ⟨y₀, hy₀⟩, fun h => hne ?_⟩
    rw [hσ'] at h
    have := congrArg (fun z : Additive (commutator D) => (Additive.toMul z : commutator D).1) h
    exact this
  obtain ⟨Y, hYatom, hY⟩ := exists_atom_nontrivial σ' (inl : S →* S ⋊[φ] A).range hnt
  have hYnt : ∃ s : S, ∃ w ∈ Y, σ' (inl s) w ≠ w := by
    obtain ⟨n, ⟨s, rfl⟩, w, hw, hnw⟩ := hY
    exact ⟨s, w, hw, hnw⟩
  have hfaith := faithful_of_nontrivial hirr σ' Y hYnt
  obtain ⟨e, he1, hdimY, h7, h5, -, -⟩ := sb_of_atom hpd hS hφ hirr hq2' σ' hYatom hfaith
  have hS1 : ∃ s : S, s ≠ 1 := by
    have : 1 < Nat.card S := by
      rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hS] <;> norm_num
    obtain ⟨a, b, hab⟩ := Finite.one_lt_card_iff_nontrivial.mp this |>.exists_pair_ne
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
    · exact ⟨a, ha⟩
  obtain ⟨s, hs1, hs3⟩ : ∃ s : S, s ≠ 1 ∧ 3 ≤ Module.finrank (ZMod q)
      ↥(Y.toSubmodule ⊓ Module.End.eigenspace (σ' (inl s)) 1) := by
    rcases hpd with ⟨hp7, -⟩ | ⟨hp5, -⟩
    · obtain ⟨s, hs⟩ := hS1
      exact ⟨s, hs, by rw [h7 hp7 s hs]; omega⟩
    · obtain ⟨hc, -, -⟩ := h5 hp5
      obtain ⟨s, hs, hd⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hc]; norm_num)
      exact ⟨s, hs, by rw [hd]; omega⟩
  obtain ⟨x, hxfix, hxΦ⟩ := hlift s hs1
  set U : Submodule (ZMod q) (Additive (commutator D)) :=
    Y.toSubmodule ⊓ Module.End.eigenspace (σ' (inl s)) 1 with hU
  let T : Subgroup (commutator D) :=
    { carrier := {y | Additive.ofMul y ∈ U}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ U
        rw [ofMul_mul]
        exact U.add_mem ha hb
      one_mem' := U.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ U
        rw [ofMul_inv]
        exact U.neg_mem ha }
  have hTcard : Nat.card T = q ^ Module.finrank (ZMod q) U := by
    have h1 : Nat.card T = Nat.card U := Nat.card_congr
      { toFun := fun y => ⟨Additive.ofMul y.1, y.2⟩
        invFun := fun u => ⟨Additive.toMul u.1, u.2⟩
        left_inv := fun y => rfl
        right_inv := fun u => rfl }
    rw [h1, Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  set Yhat : Subgroup D := T.map (commutator D).subtype with hYhat
  have hYhatcard : Nat.card Yhat = q ^ Module.finrank (ZMod q) U := by
    rw [hYhat, Subgroup.card_map_of_injective (commutator D).subtype_injective, hTcard]
  have hYhatc : Yhat ≤ Subgroup.center D := by
    rintro _ ⟨y, -, rfl⟩
    exact hDcl y.2
  have hYhatfix : ∀ y ∈ Yhat, (inl s : S ⋊[φ] A) • y = y := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : σ' (inl s) (Additive.ofMul y) = Additive.ofMul y := by
      have := hy.2
      rwa [SetLike.mem_coe, Module.End.mem_eigenspace_iff, one_smul] at this
    rw [hσ'] at h1
    have := congrArg (fun z : Additive (commutator D) => (Additive.toMul z : commutator D).1) h1
    exact this
  have hxYhat : x ∉ Yhat := by
    rintro ⟨y, -, rfl⟩
    exact hxΦ (commutator_le_frattini_of_isPGroup (p := q) y.2)
  have h4 := rank_succ_of_fixed hq hDexp (inl s : S ⋊[φ] A) hYhatc hYhatfix hYhatcard hxfix hxYhat
  have h3 := hrank s hs1
  omega

end CommutatorFixed

end CFSG.RankThree.PartOne.Lifting36
