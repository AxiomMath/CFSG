module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedSetup
public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingModule

public section

namespace CFSG.RankThree.PartOne.FiveAction.Red

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Quotient36
  CFSG.RankThree.PartOne.Lifting36
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]

omit [Finite G] in
theorem pow_five_eq_one_of_mem {A : Subgroup G} (hAel : IsElementaryAbelian 5 A) {b : G}
    (hb : b ∈ A) : b ^ 5 = 1 := by
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 5 ↥A)
    ⟨b, hb⟩
  have h1 := congrArg (Subgroup.subtype A) h
  simpa using h1

omit [Finite G] in
theorem mul_comm_of_mem_inf {A R : Subgroup G} (hAel : IsMulCommutative A) {b : G}
    (hbA : b ∈ A) (hbR : b ∈ Subgroup.centralizer (R : Set G)) {g : G} (hg : g ∈ R ⊔ A) :
    g * b = b * g := by
  have h : R ⊔ A ≤ Subgroup.centralizer ({b} : Set G) := by
    refine sup_le (fun r hr => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hbR r hr
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have := hAel.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hbA⟩
      exact congrArg Subtype.val this
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hg)

theorem exists_central_atom (hq2 : q ≠ 2) {A D R : Subgroup G} [hDq : Fact (IsPGroup q ↥D)]
    (hR2 : IsPGroup 2 R) (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hq5 : 5 ≠ q) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hLD : R ⊔ A ≤ Subgroup.normalizer (D : Set G))
    (hne : ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ ≠ ⊥) :
    ∃ U : Subrepresentation (FRep q hLD), IsAtom U ∧ ∃ b : ↥A,
      (b : G) ∈ Subgroup.centralizer (R : Set G) ∧
      Subgroup.inclusion (le_sup_right : A ≤ R ⊔ A) b ∈ Subgroup.center ↥(R ⊔ A) ∧
      orderOf (Subgroup.inclusion (le_sup_right : A ≤ R ⊔ A) b) = 5 ∧
      ∃ u ∈ U, FRep q hLD (Subgroup.inclusion (le_sup_right : A ≤ R ⊔ A) b) u ≠ u := by
  classical
  have hq : q.Prime := Fact.out
  have hAord : ¬ q ∣ Nat.card A := by
    rw [hAcard]
    intro h
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact hq5 ((Nat.prime_dvd_prime_iff_eq hq this.out).mp (hq.dvd_of_dvd_pow h)).symm
  have hLq : ¬ q ∣ Nat.card ↥(R ⊔ A) := not_dvd_card_sup hq hq2 hR2 hAord hAR
  have : NeZero (Nat.card ↥(R ⊔ A) : ZMod q) :=
    ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hLq⟩
  have hcomm : IsMulCommutative A := hAel.toIsMulCommutative
  let L : Subgroup G := R ⊔ A
  let N : Subgroup ↥L := (A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf L
  have hcent : ∀ n ∈ N, ∀ g : ↥L, g * n = n * g := fun n hn g =>
    Subtype.ext (mul_comm_of_mem_inf hcomm hn.1 hn.2 g.2)
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hcent n hn g, mul_inv_cancel_right]
    exact hn⟩
  obtain ⟨b, hbB, hbD⟩ : ∃ b ∈ A ⊓ Subgroup.centralizer (R : Set G),
      b ∉ Subgroup.centralizer (D : Set G) := by
    by_contra h
    push Not at h
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)
  let bL : ↥L := ⟨b, (le_sup_right : A ≤ R ⊔ A) hbB.1⟩
  have hbN : bL ∈ N := hbB
  have hnt : ∃ v, FRep q hLD bL v ≠ v := by
    by_contra h
    push Not at h
    apply hbD
    have hb : bL ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_five_eq_one_of_mem hAel hbB.1)
    have hord : ¬ q ∣ orderOf bL := by
      intro hdvd
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact hq5 ((Nat.prime_dvd_prime_iff_eq hq this.out).mp
        (hdvd.trans (orderOf_dvd_of_pow_eq_one hb))).symm
    let _ := conjAction hLD
    have htriv : ∀ x : ↥D, (((bL • x : ↥D)) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D) := by
      intro x
      have h1 := FRep_apply_mk q hLD bL x
      rw [h] at h1
      exact (Additive.ofMul.injective h1).symm
    have hfix := smul_eq_of_smul_mk_eq hDq.out bL hord htriv
    exact (mem_ker_conjHom hLD bL).mp (MulEquiv.ext hfix)
  obtain ⟨U, hU, n, hnN, u, hu, hnu⟩ := exists_atom_nontrivial (FRep q hLD) N ⟨bL, hbN, hnt⟩
  refine ⟨U, hU, ⟨(n : G), hnN.1⟩, hnN.2, ?_, ?_, ?_⟩
  · exact Subgroup.mem_center_iff.mpr fun g => hcent n hnN g
  · have hn5 : n ^ 5 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_five_eq_one_of_mem hAel hnN.1)
    have hn1 : n ≠ 1 := by
      rintro rfl
      apply hnu
      rw [map_one]
      rfl
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime hn5 hn1
  · exact ⟨u, hu, hnu⟩

end CFSG.RankThree.PartOne.FiveAction.Red
