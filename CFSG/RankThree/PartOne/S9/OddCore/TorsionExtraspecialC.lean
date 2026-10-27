module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionExtraspecialA
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionExtraspecialB
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG Subgroup
open scoped commutatorElement

theorem mem_of_pow_eq_one_of_centralized {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    {R Q D : Subgroup G} (hDQ : D ≤ Q) (hDexp : ∀ x ∈ D, x ^ q = 1)
    (hZne : D ⊓ Subgroup.centralizer (D : Set G) ≠ ⊥) {s : G} (hsR : s ∈ R)
    (hrank : CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({s} : Set G)) ≤ 2) {x : G} (hxD : x ∈ D)
    (hxZ : x ∉ D ⊓ Subgroup.centralizer (D : Set G)) (hxs : x ∈ Subgroup.centralizer ({s} : Set G))
    (hRZ : R ≤ Subgroup.centralizer ((D ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G))
    (hRC : R ≤ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :
      Set G)) :
    ∀ c ∈ Q ⊓ Subgroup.centralizer (D : Set G), c ^ q = 1 → c ∈ D := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  intro c hc hcq
  by_contra hcD
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ D ⊓ Subgroup.centralizer (D : Set G), z ≠ 1 := by
    obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZne
    exact ⟨z, z.2, fun h => hz (Subtype.ext h)⟩
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ one_mem _)
  have hox : orderOf x = q := orderOf_eq_prime (hDexp x hxD) hx1
  have hzx : z ∉ Subgroup.zpowers x := by
    intro hz
    apply hxZ
    have h1 := zpowers_eq_of_mem_of_ne_one hq hox hz hz1
    have h2 : x ∈ Subgroup.zpowers z := by rw [h1]; exact Subgroup.mem_zpowers x
    exact Subgroup.zpowers_le.2 hzZ h2
  have hcxz : c ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers z := fun h =>
    hcD (sup_le (Subgroup.zpowers_le.2 hxD) (Subgroup.zpowers_le.2 hzZ.1) h)
  have hzs : z * s = s * z := Subgroup.mem_centralizer_iff.1 (hRZ hsR) z hzZ
  have hcs : c * s = s * c := Subgroup.mem_centralizer_iff.1 (hRC hsR) c hc
  have h3 := three_le_pRank_of_commuting hq (H := Q ⊓ Subgroup.centralizer ({s} : Set G))
    (x := x) (z := z) (c := c) ⟨hDQ hxD, hxs⟩
    ⟨hDQ hzZ.1, Subgroup.mem_centralizer_singleton_iff.2 hzs⟩
    ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.2 hcs⟩
    (Subgroup.mem_centralizer_iff.1 hzZ.2 x hxD) (Subgroup.mem_centralizer_iff.1 hc.2 x hxD)
    (Subgroup.mem_centralizer_iff.1 hc.2 z hzZ.1) (hDexp x hxD) (hDexp z hzZ.1) hcq hx1 hz1 hzx
    hcxz
  omega

theorem omegaOne_eq_of_extraspecial (hET32 : ExtraspecialThirtyTwoFixedRankTwoAction)
    {G : Type} [Group G] [Finite G] {q : ℕ} {A R Q D : Subgroup G} (hq : q.Prime)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) (hA : Nat.card A = 5)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R)
    (hR : IsExtraspecialPGroup 2 R) (hR32 : Nat.card R = 32)
    (ha : ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
      ⁅a, r⁆ ∉ inSubgroup Subgroup.center R)
    (hs : ∃ s ∈ R, orderOf s = 2 ∧ s ∉ inSubgroup Subgroup.center R)
    [hQn : Q.Normal] (hQp : IsPGroup q Q) (hDQ : D ≤ Q) [hDn : D.Normal]
    (hRD : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcard : Nat.card D = q ^ 5)
    (hcomm : Nat.card (⁅D, D⁆ : Subgroup G) = q)
    (hZ : D ⊓ Subgroup.centralizer (D : Set G) = ⁅D, D⁆)
    (hΦ : inSubgroup frattini D = ⁅D, D⁆)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(Q ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    omegaOne q Q = D := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hDq : IsPGroup q D := hQp.to_le hDQ
  have hshape : IsQDShape q D := Or.inr ⟨hDexp, hDcard, hcomm, hZ, hΦ⟩
  have hrel := OddCore37.isQDShape_relIndex_frattini hq hshape
  obtain ⟨hirr, hfix⟩ := frattini_module_facts hq hq2 hDq hrel hR hR32 hRD
  have hExt := isExtraspecialPGroup_of_shape hDq hcomm hZ hΦ
  have hΦZ : inSubgroup frattini D = D ⊓ Subgroup.centralizer (D : Set G) := hΦ.trans hZ.symm
  have hmul := exists_mul_of_central_product hq hQp hDQ hExt hΦZ hirr
  have hZn : (D ⊓ Subgroup.centralizer (D : Set G)).Normal := by
    rw [hZ]
    infer_instance
  have hZcard : Nat.card (D ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) = q := by
    rw [hZ]
    exact hcomm
  have hRZ : R ≤ Subgroup.centralizer ((D ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :
      Set G) := le_centralizer_of_commutator_eq hq hZcard hRA
  have hZne : D ⊓ Subgroup.centralizer (D : Set G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    exact hq.one_lt.ne hZcard
  have hDcl : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hZ]
    exact inf_le_right
  have hRC := le_centralizer_of_critical hET32 hq hq2 hq5 hA hAR hR hR32 ha hQp hDQ hRD hDexp
    hDcl hDcard hZne hRZ hrank
  obtain ⟨s, hsR, hs2, hsc⟩ := hs
  have hs1 : s ≠ 1 := fun h => by
    rw [h, orderOf_one] at hs2
    omega
  obtain ⟨x, hxD, hxΦ, hxs⟩ := hfix s hsR hs2 hsc
  have hxZ : x ∉ D ⊓ Subgroup.centralizer (D : Set G) := fun h => hxΦ (hΦZ ▸ h)
  have hC := mem_of_pow_eq_one_of_centralized hq hDQ hDexp hZne hsR (hrank s hsR hs1) hxD hxZ
    hxs hRZ hRC
  refine omegaOne_eq_of_forall hDQ hDexp fun y hyQ hyq => ?_
  obtain ⟨d, hd, c, hc, rfl⟩ := hmul y hyQ
  have hdc : d * c = c * d := Subgroup.mem_centralizer_iff.1 hc.2 d hd
  have hcq : c ^ q = 1 := by
    have h1 : (d * c) ^ q = d ^ q * c ^ q := (show Commute d c from hdc).mul_pow q
    rw [h1, hDexp d hd, one_mul] at hyq
    exact hyq
  exact mul_mem hd (hC c hc hcq)

end CFSG.RankThree.PartOne.Torsion37
