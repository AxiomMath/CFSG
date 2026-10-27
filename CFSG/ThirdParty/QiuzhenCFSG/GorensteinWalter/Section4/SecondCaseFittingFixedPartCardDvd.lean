module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: divisibility of the fixed-part cardinality

The equation-(6) transfer `|F| <= |K0|` is upgraded to genuine
divisibility `|F| | |K0|`: the same injective map `FgY -> Y / F` and the
surjective map `K0Y -> Y / F` show `|F| = |FgY|` divides the quotient
cardinality, which divides `|K0Y| = |K0|`.  The divisibility (not mere
`<=`) is what allows choosing the same prime `p` in the cyclic factor
`K0` once `p` was chosen in `F`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A disjoint conjugate of the normal fixed part has cardinality dividing
that of the inverted factor. -/
public theorem secondCase_fitting_fixed_part_card_dvd_of_conjugate_disjoint
    {G : Type u} [Group G] [Finite G]
    (K0 F Y : Subgroup G)
    (hFnormal : IsNormalIn F Y)
    (hjoin : K0 ⊔ F = Y)
    (g : G)
    (hYnormg : g ∈ Subgroup.normalizer (Y : Set G))
    (hdisj : F ⊓ conjugateSubgroup F g = ⊥) :
    Nat.card F ∣ Nat.card K0 := by
  classical
  have hK0leY : K0 ≤ Y := by
    rw [← hjoin]
    exact le_sup_left
  have hFleY : F ≤ Y := by
    rw [← hjoin]
    exact le_sup_right
  let FY : Subgroup Y := F.subgroupOf Y
  have hFYnormal : FY.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFleY]
    intro f y hf hy
    exact hFnormal.2 y hy f hf
  let q : Y →* Y ⧸ FY := QuotientGroup.mk' FY
  let K0Y : Subgroup Y := K0.subgroupOf Y
  have hK0Ytop : K0Y ⊔ FY = ⊤ := by
    have hsub : (K0 ⊔ F).subgroupOf Y = ⊤ := by
      rw [hjoin]
      exact Subgroup.subgroupOf_self Y
    simpa [K0Y, FY, Subgroup.subgroupOf_sup hK0leY hFleY] using hsub
  have hq_surj : Function.Surjective (q.comp K0Y.subtype) := by
    intro z
    rcases QuotientGroup.mk'_surjective FY z with ⟨y, rfl⟩
    have hyTop : y ∈ K0Y ⊔ FY := by
      rw [hK0Ytop]
      trivial
    rcases (@Subgroup.mem_sup_of_normal_right Y _ K0Y FY hFYnormal y).mp hyTop
      with ⟨k, hk, f, hf, hy⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change q (K0Y.subtype ⟨k, hk⟩) = q y
    rw [← hy]
    rw [map_mul]
    have hqf : q f = 1 :=
      (QuotientGroup.eq_one_iff (N := FY) f).2 hf
    rw [hqf]
    simp
  have hFg_leY : conjugateSubgroup F g ≤ Y := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨f, hf, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hYnormg f).1 (hFleY hf)
  let FgY : Subgroup Y := (conjugateSubgroup F g).subgroupOf Y
  let qFg : FgY →* (Y ⧸ FY) := q.comp FgY.subtype
  have hqFg_inj : Function.Injective qFg := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have habF : (a : G)⁻¹ * (b : G) ∈ F := by
      have habq : q a.1 = q b.1 := by
        simpa [qFg, FgY] using hab
      have hone : q (a.1⁻¹ * b.1) = 1 := by
        rw [map_mul, map_inv]
        rw [habq]
        simp
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (N := FY)
          (a.1⁻¹ * b.1)).mp hone)
    have habFg : (a : G)⁻¹ * (b : G) ∈ conjugateSubgroup F g := by
      have ha : (a : G) ∈ conjugateSubgroup F g :=
        Subgroup.mem_subgroupOf.mp a.2
      have hb : (b : G) ∈ conjugateSubgroup F g :=
        Subgroup.mem_subgroupOf.mp b.2
      exact (conjugateSubgroup F g).mul_mem
        ((conjugateSubgroup F g).inv_mem ha) hb
    have hbot : (a : G)⁻¹ * (b : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact Subgroup.mem_inf.mpr ⟨habF, habFg⟩
    have hone : (a : G)⁻¹ * (b : G) = 1 := Subgroup.mem_bot.mp hbot
    exact eq_of_inv_mul_eq_one hone
  let conjF : F →* G := (MulAut.conj g).toMonoidHom.comp F.subtype
  let conjY : F →* Y :=
    conjF.codRestrict Y (by
      intro f
      exact hFg_leY (Subgroup.mem_map.mpr ⟨(f : G), f.2, rfl⟩))
  let phi : F →* FgY :=
    conjY.codRestrict FgY (by
      intro f
      apply Subgroup.mem_subgroupOf.mpr
      change (MulAut.conj g) (f : G) ∈ conjugateSubgroup F g
      exact Subgroup.mem_map.mpr ⟨(f : G), f.2, rfl⟩)
  have hphi_surj : Function.Surjective phi := by
    intro y
    rcases Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp y.2) with
      ⟨f, hf, hfy⟩
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [phi, conjY, conjF, MulAut.conj_apply] using hfy
  have hphi_inj : Function.Injective phi := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj g).injective
    simpa [phi, conjY, conjF, MulAut.conj_apply] using
      congrArg (fun z : FgY => (z : G)) hab
  let eF : F ≃* FgY := MulEquiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩
  have hFcard : Nat.card F = Nat.card FgY := Nat.card_congr eF.toEquiv
  have hFgQ : Nat.card FgY ∣ Nat.card (Y ⧸ FY) :=
    Subgroup.card_dvd_of_injective qFg hqFg_inj
  have hQK0Y : Nat.card (Y ⧸ FY) ∣ Nat.card K0Y :=
    Subgroup.card_dvd_of_surjective hq_surj
  have hK0Ycard : Nat.card K0Y = Nat.card K0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0leY).toEquiv
  rw [hFcard, ← hK0Ycard]
  exact hFgQ.trans hQK0Y

end CFSG.GorensteinWalter
