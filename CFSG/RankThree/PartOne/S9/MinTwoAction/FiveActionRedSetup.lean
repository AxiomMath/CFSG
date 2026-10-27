module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRealize
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelCore

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G]

@[expose, instance_reducible] noncomputable def conjAction {L X : Subgroup G}
    (h : L ≤ Subgroup.normalizer (X : Set G)) : MulDistribMulAction ↥L ↥X :=
  MulDistribMulAction.compHom ↥X (conjHom h)

@[expose] noncomputable def FRep [Finite G] (q : ℕ) [Fact q.Prime] {L X : Subgroup G}
    [Fact (IsPGroup q ↥X)] (h : L ≤ Subgroup.normalizer (X : Set G)) :
    Representation (ZMod q) ↥L (Additive (↥X ⧸ frattini ↥X)) :=
  letI := conjAction h
  frattiniRep (E := ↥L) (X := ↥X) q

theorem FRep_apply_mk [Finite G] (q : ℕ) [Fact q.Prime] {L X : Subgroup G}
    [Fact (IsPGroup q ↥X)] (h : L ≤ Subgroup.normalizer (X : Set G)) (l : ↥L) (x : ↥X) :
    FRep q h l (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) =
      Additive.ofMul ((conjHom h l x : ↥X) : ↥X ⧸ frattini ↥X) := by
  let _ := conjAction h
  exact frattiniRep_apply_mk q l x

section Groups

variable {q : ℕ}

theorem pow_eq_one_of_le {D X : Subgroup G} (hXD : X ≤ D) (hDexp : ∀ x ∈ D, x ^ q = 1) :
    ∀ x : ↥X, x ^ q = 1 := fun x => Subtype.ext (by
  rw [Subgroup.coe_pow]
  exact hDexp x (hXD x.2))

theorem commutator_le_center_of_le {D X : Subgroup G} (hXD : X ≤ D)
    (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) : commutator ↥X ≤ Subgroup.center ↥X := by
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro z
  have h1 : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ = 1 := by
    have : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ ∈ ⁅⁅D, D⁆, D⁆ :=
      Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator (hXD a.2) (hXD b.2)) (hXD z.2)
    rw [hDcl, Subgroup.mem_bot] at this
    exact this
  apply Subtype.ext
  have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
  have e : ((⁅a, b⁆ : ↥X) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, e]
  exact h2.symm

theorem isPGroup_of_le {D X : Subgroup G} (hXD : X ≤ D) (hDq : IsPGroup q ↥D) :
    IsPGroup q ↥X :=
  hDq.of_injective (Subgroup.inclusion hXD) (Subgroup.inclusion_injective hXD)

theorem not_dvd_card_sup (hq : q.Prime) (hq2 : q ≠ 2) {A R : Subgroup G} [Finite G]
    (hR2 : IsPGroup 2 R) (hAord : ¬ q ∣ Nat.card A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) : ¬ q ∣ Nat.card ↥(R ⊔ A) := by
  intro h
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  have h1 := h.trans (card_sup_dvd hAR)
  rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
  · rw [ha] at h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  · exact hAord h2

theorem not_dvd_orderOf_of_two_group (hq : q.Prime) (hq2 : q ≠ 2) {H : Type*} [Group H]
    [Finite H] (hH : IsPGroup 2 H) (h : H) : ¬ q ∣ orderOf h := by
  intro hdvd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hH
  have h1 : q ∣ 2 ^ a := ha ▸ hdvd.trans (orderOf_dvd_natCard h)
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))

theorem isPGroup_zpowers_of_two_group {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H)
    (h : H) : IsPGroup 2 (Subgroup.zpowers h) := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hH
  have hd : orderOf h ∣ 2 ^ a := ha ▸ orderOf_dvd_natCard h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)

theorem isPGroup_zpowers_two {R L : Subgroup G} [Finite G] (hR2 : IsPGroup 2 R) (hRL : R ≤ L)
    (r : ↥R) : IsPGroup 2 (Subgroup.zpowers (Subgroup.inclusion hRL r)) := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  have hd : orderOf (Subgroup.inclusion hRL r) ∣ 2 ^ a := by
    rw [orderOf_injective (Subgroup.inclusion hRL) (Subgroup.inclusion_injective hRL) r]
    exact ha ▸ orderOf_dvd_natCard r
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers]; exact hj)

end Groups

section Fixed

variable [Finite G]

omit [Finite G] in
theorem fixed_map_eq_conj {L X : Subgroup G} (h : L ≤ Subgroup.normalizer (X : Set G)) (r : ↥L) :
    letI := conjAction h
    (fixedPointSubgroup (Subgroup.zpowers r) ↥X).map X.subtype =
      X ⊓ Subgroup.centralizer ({(r : G)} : Set G) := by
  let _ := conjAction h
  have hfix : ∀ x : ↥X, x ∈ fixedPointSubgroup (Subgroup.zpowers r) ↥X ↔
      (r : G) * x = x * (r : G) := by
    intro x
    rw [mem_fixedPointSubgroup_zpowers_iff]
    constructor
    · intro hx
      have h1 := congrArg (fun y : ↥X => (y : G)) hx
      change (r : G) * x * (r : G)⁻¹ = x at h1
      calc (r : G) * x = ((r : G) * x * (r : G)⁻¹) * r := by group
        _ = x * r := by rw [h1]
    · intro hx
      apply Subtype.ext
      change (r : G) * x * (r : G)⁻¹ = x
      calc (r : G) * x * (r : G)⁻¹ = (x * r) * (r : G)⁻¹ := by rw [hx]
        _ = x := by group
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({(r : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hfix x).mp hx).symm
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, (hfix ⟨g, hgX⟩).mpr ?_, rfl⟩
    have hgC' : g ∈ Subgroup.centralizer ({(r : G)} : Set G) := hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC'
    exact hgC'.symm

theorem finrank_eigenspace_le_four {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {L D : Subgroup G}
    [Fact (IsPGroup q ↥D)] (hLD : L ≤ Subgroup.normalizer (D : Set G))
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) (r : ↥L)
    (hr : IsPGroup 2 (Subgroup.zpowers r))
    (hrk : CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({(r : G)} : Set G)) ≤ 3) :
    Module.finrank (ZMod q) ↥(Module.End.eigenspace (FRep q hLD r) 1) ≤ 4 := by
  let _ := conjAction hLD
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hXexp := pow_eq_one_of_le (le_refl D) hDexp
  have hXcl := commutator_le_center_of_le (le_refl D) hDcl
  have h1 := finrank_eigenspace_le_pRank q hq2 hXexp r hr
  have h2 : CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers r) ↥D) ≤ 3 := by
    rw [← pRank_map_subtype hq1, fixed_map_eq_conj hLD r]
    exact hrk
  exact h1.trans ((pRank_quotient_commutator_le q hXexp hXcl _).1 h2)

end Fixed

end CFSG.RankThree.PartOne.FiveAction.Red
