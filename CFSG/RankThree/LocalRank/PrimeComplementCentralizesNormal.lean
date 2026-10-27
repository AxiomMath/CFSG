module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.RankThree.LocalRank

theorem local_prime_complement_centralizes_normal_prime_group {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {P A S : Subgroup G} [P.Normal] (hP : IsPGroup p P)
    (hA : IsPGroup p A) (hSA : S ≤ Subgroup.centralizer (A : Set G))
    (hSnormal : (S.subgroupOf (Subgroup.centralizer (A : Set G))).Normal)
    (hS : ¬p ∣ Nat.card S) : ⁅S, P⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  let α : S →* MulAut P := MulAut.conjNormal.comp S.subtype
  let β : A →* MulAut P := MulAut.conjNormal.comp A.subtype
  have hcomm : ∀ s a, α s * β a = β a * α s := by
    intro s a
    simp only [α, β, MonoidHom.comp_apply, Subgroup.coe_subtype, ← map_mul]
    rw [Subgroup.mem_centralizer_iff.mp (hSA s.2) a a.2]
  have hdisj : Disjoint S P := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hS))
  have hfix : ∀ s r, (∀ a, β a r = r) → α s r = r := by
    intro s r hr
    have hrA : (r : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := congrArg Subtype.val (hr ⟨a, ha⟩)
      simp only [β, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at h
      calc a * (r : G) = a * r * a⁻¹ * a := by group
        _ = r * a := by rw [h]
    have hsA : (s : G) ∈ Subgroup.centralizer (A : Set G) := hSA s.2
    have hconj : (r : G) * (s : G)⁻¹ * (r : G)⁻¹ ∈ S := by
      have h := hSnormal.conj_mem ⟨(s : G)⁻¹, inv_mem hsA⟩
        (Subgroup.mem_subgroupOf.mpr (inv_mem s.2)) ⟨r, hrA⟩
      simpa using Subgroup.mem_subgroupOf.mp h
    have hcS : (s : G) * r * (s : G)⁻¹ * (r : G)⁻¹ ∈ S := by
      have := mul_mem s.2 hconj
      simpa [mul_assoc] using this
    have hcP : (s : G) * r * (s : G)⁻¹ * (r : G)⁻¹ ∈ P :=
      mul_mem (‹P.Normal›.conj_mem _ r.2 _) (inv_mem r.2)
    have h1 := Subgroup.disjoint_def.mp hdisj hcS hcP
    apply Subtype.ext
    simp only [α, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    exact mul_inv_eq_one.mp h1
  have htriv := CFSG.GroupTheory.thompson_A_times_B hP hS hA α β hcomm hfix
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun φ : MulAut P => ((φ ⟨x, hx⟩ : P) : G)) (htriv ⟨s, hs⟩)
  simp only [α, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
    MulAut.one_apply] at h
  calc x * s = s * x * s⁻¹ * s := by rw [h]
    _ = s * x := by group

end CFSG.RankThree.LocalRank
