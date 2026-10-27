module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallHall
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The Sylow structure in the order-four Brauer--Suzuki--Wall branch

When the distinguished abelian subgroup `K` has order four, its unique
involution condition makes `K` cyclic.  Thus `H = K ⊔ ⟨s⟩` is dihedral of
order eight.  Since `H` is a Hall subgroup, it is an ambient Sylow
`2`-subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

private theorem BrauerSuzukiWallHypotheses.eq_one_or_t_of_mem_K_of_sq_eq_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (x : h.K) (hx : x ^ 2 = 1) :
    x = 1 ∨ x = ⟨h.t, h.t_mem_K⟩ := by
  have hxGsq : (x : G) * (x : G) = 1 := by
    simpa [pow_two] using congrArg Subtype.val hx
  have hxGinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hxGsq
  have hsxConj : h.s * (x : G) * h.s⁻¹ = x := by
    rw [h.s_inverts_K (x : G) x.property, hxGinv]
  have hsx : h.s * (x : G) = (x : G) * h.s := by
    have hsx' := congrArg (fun y : G => y * h.s) hsxConj
    simpa [mul_assoc] using hsx'
  have hxCent : (x : G) ∈ Subgroup.centralizer ({h.s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = h.s := by simpa using hy
    simpa [hy'] using hsx
  have hxZ : (x : G) ∈ Subgroup.zpowers h.t := by
    rw [← h.fixed_subgroup_eq]
    exact ⟨x.property, hxCent⟩
  let Z : Subgroup G := Subgroup.zpowers h.t
  have htOrder : orderOf h.t = 2 :=
    orderOf_eq_prime h.t_involution.2 h.t_involution.1
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, htOrder]
  have htZ : h.t ∈ Z := Subgroup.mem_zpowers h.t
  have htZne : (⟨h.t, htZ⟩ : Z) ≠ 1 := by
    intro ht1
    exact h.t_involution.1 (congrArg Subtype.val ht1)
  have hxZ' : (x : G) ∈ Z := hxZ
  by_cases hx1 : (⟨(x : G), hxZ'⟩ : Z) = 1
  · left
    apply Subtype.ext
    exact congrArg (fun z : Z => (z : G)) hx1
  · right
    rcases (Nat.card_eq_two_iff' (1 : Z)).mp hZcard with
      ⟨z, _hz, huniq⟩
    have hxt : (⟨(x : G), hxZ'⟩ : Z) = ⟨h.t, htZ⟩ :=
      (huniq _ hx1).trans (huniq _ htZne).symm
    apply Subtype.ext
    exact congrArg (fun z : Z => (z : G)) hxt

private theorem BrauerSuzukiWallHypotheses.centralizer_dihedral_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4) :
    Nonempty (h.H ≃* DihedralGroup 4) := by
  classical
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  have hthree : 3 ≤ ENat.card h.K := by
    rw [ENat.card_eq_coe_natCard, hk]
    norm_num
  obtain ⟨rho, hrho1, hrhot⟩ :=
    ENat.exists_ne_ne_of_three_le hthree (1 : h.K) tK
  have hrhoSqNe : rho ^ 2 ≠ 1 := by
    intro hrhoSq
    rcases h.eq_one_or_t_of_mem_K_of_sq_eq_one rho hrhoSq with h1 | ht
    · exact hrho1 h1
    · exact hrhot ht
  have hrhoOrderDvd : orderOf rho ∣ 4 := by
    simpa [hk] using orderOf_dvd_natCard rho
  have hrhoOrder : orderOf rho = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two
      (m := 2) (i := orderOf rho)).mp (by
        norm_num
        exact hrhoOrderDvd) with ⟨i, hi, hord⟩
    interval_cases i
    · simp only [pow_zero] at hord
      exact False.elim (hrho1 (orderOf_eq_one_iff.mp hord))
    · simp only [pow_one] at hord
      have hrhoSq : rho ^ 2 = 1 := by
        rw [← hord]
        exact pow_orderOf_eq_one rho
      exact False.elim (hrhoSqNe hrhoSq)
    · simpa using hord
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact (le_sup_right : Subgroup.zpowers h.s ≤
      h.K ⊔ Subgroup.zpowers h.s) (Subgroup.mem_zpowers h.s)
  let rhoH : h.H := ⟨(rho : G), hKleH rho.property⟩
  let sH : h.H := ⟨h.s, hsH⟩
  let KH : Subgroup h.H := h.K.subgroupOf h.H
  have hrhoHOrder : orderOf rhoH = 4 := by
    rw [← Subgroup.orderOf_coe rhoH, show (rhoH : G) = rho by rfl,
      Subgroup.orderOf_coe rho, hrhoOrder]
  have hzpLe : Subgroup.zpowers rhoH ≤ KH := by
    apply Subgroup.zpowers_le.mpr
    exact rho.property
  have hKHcard : Nat.card KH = 4 := by
    rw [natCard_subgroupOf_eq h.K h.H hKleH, hk]
  have hzpCard : Nat.card (Subgroup.zpowers rhoH) = 4 := by
    rw [Nat.card_zpowers, hrhoHOrder]
  have hzpEq : Subgroup.zpowers rhoH = KH :=
    Subgroup.eq_of_le_of_card_ge hzpLe (by rw [hKHcard, hzpCard])
  have hZleH : Subgroup.zpowers h.s ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_right
  have hZsub : (Subgroup.zpowers h.s).subgroupOf h.H =
      Subgroup.zpowers sH := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, Subtype.ext ?_⟩
      simpa [sH] using hn
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      exact congrArg Subtype.val hn
  have hgen0 : ⊤ = KH ⊔ (Subgroup.zpowers h.s).subgroupOf h.H := by
    have hsub := congrArg (fun L : Subgroup G => L.subgroupOf h.H)
      h.H_eq_join
    simpa [KH, Subgroup.subgroupOf_self,
      Subgroup.subgroupOf_sup hKleH hZleH] using hsub
  have hgen : ⊤ = Subgroup.zpowers rhoH ⊔ Subgroup.zpowers sH := by
    simpa [hzpEq, hZsub] using hgen0
  have hsHsq : sH ^ 2 = 1 := by
    apply Subtype.ext
    exact h.s_involution.2
  have hrel : sH * rhoH * sH⁻¹ = rhoH⁻¹ := by
    apply Subtype.ext
    exact h.s_inverts_K (rho : G) rho.property
  have hsNot : sH ∉ Subgroup.zpowers rhoH := by
    rw [hzpEq]
    exact h.s_not_mem_K
  have hd :=
    dihedral_of_generators_of_not_mem rhoH sH hgen hsHsq hrel hsNot
  rw [hrhoHOrder] at hd
  exact hd

/-- In the order-four Brauer--Suzuki--Wall branch, `H = C_G(t)` is a
dihedral Sylow `2`-subgroup of order eight, so every Sylow `2`-subgroup of
`G` is dihedral. -/
public theorem BrauerSuzukiWallHypotheses.hasDihedralSylowTwo_of_card_K_eq_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4) :
    HasDihedralSylowTwo G := by
  have hHcard : Nat.card h.H = 8 := by
    rw [h.card_H, hk]
  have hHp : IsPGroup 2 h.H := by
    apply IsPGroup.of_card (n := 3)
    norm_num [hHcard]
  have hnotIndex : ¬ 2 ∣ h.H.index := by
    intro hdvd
    have htwoOne : 2 = 1 :=
      Nat.eq_one_of_dvd_coprimes h.hall_H
        (by omega : 2 ∣ Nat.card h.H) hdvd
    omega
  let S0 : Sylow 2 G := hHp.toSylow hnotIndex
  have eH : Nonempty (h.H ≃* DihedralGroup 4) :=
    h.centralizer_dihedral_four hk
  intro S
  refine ⟨2, by omega, ?_⟩
  have eS0H : S0 ≃* h.H := by
    exact MulEquiv.subgroupCongr (IsPGroup.toSylow_coe hHp hnotIndex)
  simpa using (show Nonempty (S ≃* DihedralGroup 4) from
    ⟨(Sylow.equiv S S0).trans eS0H |>.trans eH.some⟩)

end CFSG.GorensteinWalter
