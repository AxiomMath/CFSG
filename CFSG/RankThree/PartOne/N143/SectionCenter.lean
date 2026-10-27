module

public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.S12.InputsFischer
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne (Sec6EightMultipliers TauCetiCatalogBridge)

theorem not_dvd_card_center_theta_quotient {L : Type} [Group L] [Finite L] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hrp : r ≠ p) :
    ¬ r ∣ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore p L)) := by
  intro hdvd
  have : Fact r.Prime := ⟨hr⟩
  set θ := aschbacherSolvableCore p L with hθ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (L ⧸ θ)) r hdvd
  let T : Subgroup (L ⧸ θ) := Subgroup.zpowers (z : L ⧸ θ)
  have hTz : ∀ t ∈ T, t ∈ Subgroup.center (L ⧸ θ) := fun t ht => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
    exact Subgroup.zpow_mem _ z.2 k
  have hTnormal : T.Normal :=
    ⟨fun t ht g => by
      have h1 := Subgroup.mem_center_iff.1 (hTz t ht) g
      rw [h1, mul_inv_cancel_right]
      exact ht⟩
  let π : L →* L ⧸ θ := QuotientGroup.mk' θ
  let T' : Subgroup L := T.comap π
  have hT'normal : T'.Normal := Subgroup.normal_comap π
  have hθT' : θ ≤ T' := fun x hx => by
    show π x ∈ T
    rw [show π x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact T.one_mem
  have hθsol : Group.IsSolvable θ := (solvable_prime_complement_core_characterization hp).1
  have hpθ : ¬ p ∣ Nat.card θ := (solvable_prime_complement_core_characterization hp).2.2.1
  let g : T' →* T := π.subgroupComap T
  have hgsurj : Function.Surjective g := MonoidHom.subgroupComap_surjective π T
    (QuotientGroup.mk'_surjective θ)
  have hgker : g.ker = θ.subgroupOf T' := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have : π x = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (x : L)).1 this
    · intro hx
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : L)).2 hx)
  have hTcom : ∀ a b : T, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.1 (hTz b b.2) a)
  have hTsol : Group.IsSolvable T := Group.isSolvable_of_comm hTcom
  have hsol : Group.IsSolvable T' := by
    have : Group.IsSolvable θ := hθsol
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθT') g ?_
    rw [hgker]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have hTcard : Nat.card T = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hcard : Nat.card T' = Nat.card θ * r := by
    have h1 := Subgroup.card_ker_mul_card_range g
    rw [MonoidHom.range_eq_top.2 hgsurj, Subgroup.card_top, hTcard, hgker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθT').toEquiv] at h1
    exact h1.symm
  have hpT' : ¬ p ∣ Nat.card T' := by
    rw [hcard]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hpθ h1
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h1).symm
  have hle : T' ≤ θ := (solvable_prime_complement_core_characterization hp).2.2.2.1 T' hT'normal
    hsol hpT'
  have hz1 : (z : L ⧸ θ) = 1 := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (z : L ⧸ θ)
    have hxT' : x ∈ T' := by
      show π x ∈ T
      rw [show π x = (z : L ⧸ θ) from hx]
      exact Subgroup.mem_zpowers _
    rw [← hx]
    exact (QuotientGroup.eq_one_iff x).2 (hle hxT')
  have hz1' : z = 1 := Subtype.ext hz1
  rw [hz1', orderOf_one] at hz
  exact hr.one_lt.ne hz

end CFSG.RankThree.PartOne.N143
