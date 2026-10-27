module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeOddFactor
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd fixed-point-free subgroups over a Klein-four-by-odd kernel

This is the cardinality step suppressed in Bender's restriction (7).  An
odd nontrivial subgroup of a group with quotient of order six embeds in that
quotient as soon as it has no fixed points under the normal Klein four in the
kernel.  Its order is therefore three.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- Let `V U` be a normal Klein-four-by-odd subgroup of `H`, with `V`
centralizing `U` and `[H : VU] = 6`.  If a nontrivial odd subgroup `F ≤ H`
has trivial centralizer intersection with `V`, then `|F| = 3`. -/
public theorem odd_fixedPointFree_subgroup_card_three_of_kleinFour_quotient
    {G : Type u} [Group G] [Finite G]
    (H V U F : Subgroup G)
    (hVleH : V ≤ H) (hUleH : U ≤ H)
    (hVnormal : IsNormalIn V H) (hUnormal : IsNormalIn U H)
    (hVK : IsKleinFour V)
    (hUodd : Odd (Nat.card U))
    (hVUcent : V ≤ Subgroup.centralizer (U : Set G))
    (hFleH : F ≤ H) (hFodd : Odd (Nat.card F)) (hFne : F ≠ ⊥)
    (hFfree : F ⊓ Subgroup.centralizer (V : Set G) = ⊥)
    (hindex : ((V ⊔ U).subgroupOf H).index = 6) :
    Nat.card F = 3 := by
  classical
  let B : Subgroup G := V ⊔ U
  have hBleH : B ≤ H := sup_le hVleH hUleH
  have hVnormU : V ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv u hu
    exact hUnormal.2 v (hVleH hv) u hu
  have hBset : (B : Set G) = (V : Set G) * (U : Set G) := by
    rw [show B = V ⊔ U by rfl,
      Subgroup.coe_mul_of_left_le_normalizer_right V U hVnormU]
  have hBnormal : IsNormalIn B H := by
    refine ⟨hBleH, ?_⟩
    intro h hh b hb
    have hb' : b ∈ (V : Set G) * (U : Set G) := by
      rw [← hBset]
      exact hb
    rcases Set.mem_mul.mp hb' with ⟨v, hv, u, hu, hvub⟩
    rw [← hvub]
    have hv' : h * v * h⁻¹ ∈ V := hVnormal.2 h hh v hv
    have hu' : h * u * h⁻¹ ∈ U := hUnormal.2 h hh u hu
    have hprod : (h * v * h⁻¹) * (h * u * h⁻¹) ∈ B :=
      B.mul_mem ((show V ≤ B from le_sup_left) hv')
        ((show U ≤ B from le_sup_right) hu')
    convert hprod using 1 <;> group
  have hVnormalB : IsNormalIn V B := by
    refine ⟨le_sup_left, ?_⟩
    intro b hb v hv
    exact hVnormal.2 b (hBleH hb) v hv
  have hUnormalB : IsNormalIn U B := by
    refine ⟨le_sup_right, ?_⟩
    intro b hb u hu
    exact hUnormal.2 b (hBleH hb) u hu
  have hVUcomm : ∀ v : G, v ∈ V → ∀ u : G, u ∈ U → v * u = u * v := by
    intro v hv u hu
    exact (Subgroup.mem_centralizer_iff.mp (hVUcent hv) u hu).symm
  have hVp : IsPGroup 2 V := by
    apply IsPGroup.of_card (n := 2)
    rw [hVK.card_four]
    norm_num
  have hdisjVU : Disjoint V U := by
    have hcop : Nat.Coprime (Nat.card V) (Nat.card U) := by
      rw [hVK.card_four]
      exact (Nat.coprime_two_left.mpr hUodd).pow_left 2
    exact Subgroup.disjoint_of_coprime_natCard hcop
  let K : Subgroup G := F ⊓ B
  have hKleU : K ≤ U := by
    apply odd_order_subgroup_le_of_le_sup_of_twoPGroup V U K
      hVnormalB hUnormalB hVUcomm
    · exact inf_le_right
    · exact hVp
    · exact Odd.of_dvd_nat hFodd (Subgroup.card_dvd_of_le inf_le_left)
    · exact hdisjVU
  have hKleCent : K ≤ Subgroup.centralizer (V : Set G) := by
    intro k hk
    have hkU : k ∈ U := hKleU hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hVUcent hv) k hkU).symm
  have hKbot : K = ⊥ := by
    apply le_antisymm
    · intro k hk
      have hkFC : k ∈ F ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨hk.1, hKleCent hk⟩
      rw [hFfree] at hkFC
      exact hkFC
    · exact bot_le
  let B0 : Subgroup H := B.subgroupOf H
  have hB0normal : B0.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hBleH).2
    intro b h hb hh
    exact hBnormal.2 h hh b hb
  let : B0.Normal := hB0normal
  let q : H →* (H ⧸ B0) := QuotientGroup.mk' B0
  let i : F →* H :=
    { toFun := fun f => ⟨(f : G), hFleH f.2⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  let f : F →* (H ⧸ B0) := q.comp i
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hq : f a * (f b)⁻¹ = 1 := by rw [hab]; simp
    have hmemB : (a : G) * (b : G)⁻¹ ∈ B := by
      have hq' : q (i a * (i b)⁻¹) = 1 := by
        simpa [f, q] using hq
      have hmem : (i a * (i b)⁻¹ : H) ∈ B0 :=
        (QuotientGroup.eq_one_iff _).mp hq'
      exact Subgroup.mem_subgroupOf.mp hmem
    have hmemK : (a : G) * (b : G)⁻¹ ∈ K :=
      ⟨F.mul_mem a.2 (F.inv_mem b.2), hmemB⟩
    rw [hKbot] at hmemK
    apply Subtype.ext
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmemK)
  have hdiv : Nat.card F ∣ Nat.card (H ⧸ B0) := by
    have hdiv' : Nat.card f.range ∣ Nat.card (H ⧸ B0) :=
      Subgroup.card_subgroup_dvd_card f.range
    have hcardrange : Nat.card f.range = Nat.card F :=
      (Nat.card_congr (MonoidHom.ofInjective hf_inj).toEquiv).symm
    rw [hcardrange] at hdiv'
    exact hdiv'
  have hqcard : Nat.card (H ⧸ B0) = 6 := by
    rw [← Subgroup.index_eq_card]
    simpa [B0, B] using hindex
  rw [hqcard] at hdiv
  have hle : Nat.card F ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne1 : Nat.card F ≠ 1 := by
    intro h
    exact hFne (Subgroup.eq_bot_of_card_eq F h)
  have hne2 : Nat.card F ≠ 2 := by
    intro h
    rw [h] at hFodd
    norm_num at hFodd
  have hne6 : Nat.card F ≠ 6 := by
    intro h
    rw [h] at hFodd
    norm_num at hFodd
  interval_cases hcard : Nat.card F <;> simp_all

end CFSG.GorensteinWalter
