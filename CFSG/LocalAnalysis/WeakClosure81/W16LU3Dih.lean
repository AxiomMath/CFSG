module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped Pointwise

theorem w16l_dihedral_inv_conj {m : ℕ} (hm : Odd m) {u v : DihedralGroup m}
    (hu : u * u = 1) (hu1 : u ≠ 1) (hv : Odd (orderOf v)) : u * v * u⁻¹ = v⁻¹ := by
  cases u with
  | r i =>
    exfalso
    have hii : i + i = 0 := by
      have h := hu
      rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at h
      exact DihedralGroup.r.inj h
    have hi : i = 0 := (ZMod.add_self_eq_zero_iff_eq_zero hm).mp hii
    exact hu1 (by rw [DihedralGroup.one_def, hi])
  | sr i =>
    cases v with
    | r j =>
      rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r, DihedralGroup.r.injEq]
      ring
    | sr j =>
      exfalso
      rw [DihedralGroup.orderOf_sr] at hv
      exact (by decide : ¬ Odd 2) hv

theorem w16l_inverts_of_dihedral_complement {G : Type*} [Group G] {A N D H : Subgroup G}
    {m : ℕ} (hm : Odd m) (hND : N ⊓ D = ⊥) (hsup : N ⊔ D = A) (hN : (N.subgroupOf A).Normal)
    (e : D ≃* DihedralGroup m) (hHA : H ≤ A) (hH : Odd (Nat.card H))
    {a : G} (haA : a ∈ A) (ha2 : a * a = 1) (haN : a ∉ N) :
    ∀ h ∈ H, a * h * a⁻¹ * h ∈ N := by
  classical
  let N' : Subgroup A := N.subgroupOf A
  let D' : Subgroup A := D.subgroupOf A
  haveI hN' : N'.Normal := hN
  have hDA : D ≤ A := by rw [← hsup]; exact le_sup_right
  have hNA : N ≤ A := by rw [← hsup]; exact le_sup_left
  have hsup' : D' ⊔ N' = ⊤ := by
    have h : D ⊔ N = A := by rw [← sup_comm]; exact hsup
    rw [← Subgroup.subgroupOf_sup hDA hNA, h]
    exact Subgroup.subgroupOf_self A
  have hinf : D' ⊓ N' = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx.1
    have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx.2
    have hx0 : (x : G) ∈ N ⊓ D := ⟨hxN, hxD⟩
    rw [hND] at hx0
    exact Subtype.ext (Subgroup.mem_bot.mp hx0)
  have hdisj : Disjoint D' N' := disjoint_iff.mpr hinf
  have hmul : (D' : Set A) * (N' : Set A) = Set.univ := by
    rw [← Subgroup.mul_normal D' N', hsup']
    simp
  have hcomp : D'.IsComplement' N' := isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  let e' : D' ≃* DihedralGroup m := (Subgroup.subgroupOfEquivOfLe hDA).trans e
  let iso : A ⧸ N' ≃* DihedralGroup m := (IsComplement'.QuotientMulEquiv hcomp).trans e'
  let ψ : A →* DihedralGroup m := iso.toMonoidHom.comp (QuotientGroup.mk' N')
  have hker : ∀ x : A, ψ x = 1 ↔ x ∈ N' := by
    intro x
    change iso (QuotientGroup.mk' N' x) = 1 ↔ x ∈ N'
    rw [← iso.map_one, iso.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let aA : A := ⟨a, haA⟩
  have haN' : aA ∉ N' := fun hx => haN (Subgroup.mem_subgroupOf.mp hx)
  have hψa1 : ψ aA ≠ 1 := fun h => haN' ((hker aA).mp h)
  have hψa2 : ψ aA * ψ aA = 1 := by
    rw [← map_mul, show aA * aA = 1 by ext; simpa using ha2, map_one]
  intro h hh
  let hA : A := ⟨h, hHA hh⟩
  have hodd : Odd (orderOf (ψ hA)) := by
    have hcard : Nat.card (H.subgroupOf A) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv
    have hmem : hA ∈ H.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      exact hh
    have hdiv : orderOf (ψ hA) ∣ Nat.card H := by
      rw [← hcard]
      exact (orderOf_map_dvd ψ hA).trans
        (Subgroup.orderOf_dvd_natCard (H.subgroupOf A) hmem)
    exact Odd.of_dvd_nat hH hdiv
  have hconj := w16l_dihedral_inv_conj hm (u := ψ aA) (v := ψ hA) hψa2 hψa1 hodd
  have hmap : ψ (aA * hA * aA⁻¹ * hA) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hconj, inv_mul_cancel]
  have hmemN' : aA * hA * aA⁻¹ * hA ∈ N' := (hker _).mp hmap
  have hfin : ((aA * hA * aA⁻¹ * hA : A) : G) ∈ N := Subgroup.mem_subgroupOf.mp hmemN'
  simpa using hfin

end CFSG.LocalAnalysis.WeakClosure81

end
