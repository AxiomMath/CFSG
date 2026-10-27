module

public import CFSG.Quasithin.H13.L32NM22Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.M22Rank

open CFSG.Blueprint CFSG.Quasithin

theorem card_le_of_hat
    {G : Type} [Group G] [Finite G] {M N E : Subgroup G} (hidx : N.relIndex M = 2)
    (hEM : E ≤ M) (hHat : IsHat ↥N ↥NativeSporadic.M22) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ 5 := by
  classical
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx' : x⁻¹ = x := (eq_inv_of_mul_eq_one_left (hsq x hx)).symm
    have hy' : y⁻¹ = y := (eq_inv_of_mul_eq_one_left (hsq y hy)).symm
    have hxy : (x * y)⁻¹ = x * y := (eq_inv_of_mul_eq_one_left (hsq _ (E.mul_mem hx hy))).symm
    rw [← hxy, mul_inv_rev, hx', hy']
  obtain ⟨-, hZ3, ⟨φ⟩⟩ := hHat
  have hFE : ∀ x : ↥((N ⊓ E).subgroupOf N), (((x : ↥N) : G)) ∈ E := fun x =>
    (Subgroup.mem_subgroupOf.mp x.2).2
  let ι : ↥((N ⊓ E).subgroupOf N) →* ↥NativeSporadic.M22 :=
    φ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥N)).comp
      ((N ⊓ E).subgroupOf N).subtype)
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : ↥N) ∈ Subgroup.center ↥N := by
      have h2 : (QuotientGroup.mk' (Subgroup.center ↥N)) (x : ↥N) = 1 := by
        apply φ.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hx2 : (x : ↥N) * (x : ↥N) = 1 := Subtype.ext (hsq _ (hFE x))
    obtain ⟨z, hz⟩ : ∃ z : Subgroup.center ↥N, (z : ↥N) = x := ⟨⟨x, h1⟩, rfl⟩
    have hz2 : z ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hz, sq, hx2]; rfl)
    have h3 : orderOf z ∣ 3 := hZ3 ▸ orderOf_dvd_natCard z
    have h2' : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have h1' : orderOf z = 1 := Nat.dvd_one.mp (by
      have h := Nat.dvd_gcd h3 h2'
      rwa [show Nat.gcd 3 2 = 1 by norm_num] at h)
    have hz1 : z = 1 := orderOf_eq_one_iff.mp h1'
    apply Subtype.ext
    rw [← hz, hz1]
    rfl
  have hrange := CFSG.QuasithinUnique.Setup.X1.m22_rank_le ι.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      exact hcomm _ (hFE a) _ (hFE b))
    (by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have ha : a * a = 1 := Subtype.ext (Subtype.ext (hsq _ (hFE a)))
      rw [ha, map_one])
  have hcF : Nat.card ↥((N ⊓ E).subgroupOf N) ≤ 2 ^ 4 := by
    rw [← Nat.card_range_of_injective hinj]
    exact hrange
  have hcNE : Nat.card ↥(N ⊓ E) ≤ 2 ^ 4 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ E ≤ N)).toEquiv
    rw [← h]
    exact hcF
  have hrel : N.relIndex E ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right hEM (by rw [hidx]; norm_num)
    rwa [hidx] at h
  have hmul := Subgroup.relIndex_mul_card N E
  calc Nat.card E = N.relIndex E * Nat.card ↥(N ⊓ E) := hmul.symm
    _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul hrel hcNE
    _ = 2 ^ 5 := by norm_num

theorem m22_card_le_of
    {N : Subgroup (GL (Fin 12) (ZMod 2))}
    (hN : N ≤ L1442M.m22) (hcard : Nat.card N = 1330560) (hHat : IsHat ↥N ↥NativeSporadic.M22)
    {E : Subgroup (GL (Fin 12) (ZMod 2))} (hE : E ≤ L1442M.m22) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ 5 := by
  have hidx : N.relIndex L1442M.m22 = 2 := by
    have h := Subgroup.relIndex_mul_card N L1442M.m22
    rw [inf_eq_left.mpr hN, hcard, M22Cert.card_m22] at h
    omega
  exact card_le_of_hat hidx hE hHat hsq

end CFSG.Quasithin.H13.M22Rank
