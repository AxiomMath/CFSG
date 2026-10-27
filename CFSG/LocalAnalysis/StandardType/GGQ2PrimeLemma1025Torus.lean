module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Basic
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Coords

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models

theorem lem1025_elemAbelian_of_le {G : Type} [Group G] {B T : Subgroup G}
    (hB : IsElemAbelian 3 B) (hTB : T ≤ B) : IsElemAbelian 3 T :=
  ⟨⟨⟨fun u v => Subtype.ext (elemAbelian_comm' hB (hTB u.2) (hTB v.2))⟩⟩,
    fun a ha => hB.2 a (hTB ha)⟩

private theorem lem1025_orderOf_ω3 : orderOf (ω3 : Multiplicative (ZMod 3)) = 3 := by
  unfold ω3
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem lem1025_card_closure_pair {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut Bs)} {x zn : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m n : Fin 7} (hW : WeylCoords Bs A x κ m) (hnm : n ≠ m) (hBab : IsElemAbelian 3 Bs)
    (hzn : zn ∈ Bs) (hcn : ∀ j, κ j ⟨zn, hzn⟩ = if j = n then 1 else ω3) :
    Nat.card (closure ({x, x * zn⁻¹} : Set G)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx := hW.x_mem
  have hb : x * zn⁻¹ ∈ Bs := Bs.mul_mem hx (Bs.inv_mem hzn)
  have hκa : ∀ j, κ j ⟨x, hx⟩ = if j = m then 1 else ω3 := hW.x_coord
  have hκb : κ m ⟨x * zn⁻¹, hb⟩ = ω3⁻¹ := by
    have : (⟨x * zn⁻¹, hb⟩ : Bs) = ⟨x, hx⟩ * ⟨zn, hzn⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hκa, hcn, if_pos rfl, if_neg (Ne.symm hnm), one_mul]
  have hab : x * (x * zn⁻¹) = (x * zn⁻¹) * x := elemAbelian_comm' hBab hx hb
  have hord_a : orderOf x = 3 := by
    refine orderOf_eq_prime (hBab.2 x hx) fun h1 => ?_
    have := hκa n
    rw [if_neg hnm] at this
    have h2 : (⟨x, hx⟩ : Bs) = 1 := Subtype.ext h1
    rw [h2, map_one] at this
    exact one_ne_ω3 this
  have hord_b : orderOf (x * zn⁻¹) = 3 := by
    refine orderOf_eq_prime (hBab.2 _ hb) fun h1 => ?_
    have h2 : (⟨x * zn⁻¹, hb⟩ : Bs) = 1 := Subtype.ext h1
    rw [h2, map_one] at hκb
    exact one_ne_ω3 (inv_eq_one.1 hκb.symm).symm
  have hcl : closure ({x, x * zn⁻¹} : Set G) = zpowers x ⊔ zpowers (x * zn⁻¹) := by
    rw [Set.insert_eq, Subgroup.closure_union, zpowers_eq_closure, zpowers_eq_closure]
  have hcomm : ∀ h ∈ zpowers x, ∀ k ∈ zpowers (x * zn⁻¹), h * k = k * h := by
    intro h hh k hk
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hk
    exact (Commute.zpow_zpow hab i j).eq
  have hdisj : ∀ g ∈ zpowers x, g ∈ zpowers (x * zn⁻¹) → g = 1 := by
    intro g hga hgb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hga
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hgb
    have hmem : x ^ i ∈ Bs := zpow_mem hx i
    have e1 : κ m ⟨x ^ i, hmem⟩ = 1 := by
      have : (⟨x ^ i, hmem⟩ : Bs) = (⟨x, hx⟩ : Bs) ^ i := Subtype.ext (by simp)
      rw [this, map_zpow, hκa, if_pos rfl, one_zpow]
    have e2 : κ m ⟨x ^ i, hmem⟩ = (ω3⁻¹) ^ j := by
      have : (⟨x ^ i, hmem⟩ : Bs) = (⟨x * zn⁻¹, hb⟩ : Bs) ^ j := Subtype.ext (by simp [hj])
      rw [this, map_zpow, hκb]
    rw [e1] at e2
    have hdvd : ((orderOf (ω3⁻¹ : Multiplicative (ZMod 3)) : ℕ) : ℤ) ∣ j :=
      orderOf_dvd_iff_zpow_eq_one.2 e2.symm
    rw [orderOf_inv, lem1025_orderOf_ω3] at hdvd
    rw [← hj]
    exact orderOf_dvd_iff_zpow_eq_one.1 (hord_b ▸ hdvd)
  rw [hcl, lem1025_card_sup hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers, hord_a, hord_b]

theorem lem1025_torus_data {G : Type} [Group G] [Finite G] {Bs X U : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hBab : IsElemAbelian 3 Bs) (hBX : Bs ≤ normalizer (X : Set G))
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hBU : Bs ≤ normalizer (U : Set G))
    (hXU : X ≤ normalizer (U : Set G)) (hrank : twoLocalPrimeRank 3 G ≤ 6)
    (hBs : Nat.card Bs = 3 ^ 6) (hC : Nat.card (Bs ⊓ centralizer (X : Set G) : Subgroup G) = 9) :
    Nat.card (Bs ⊓ X : Subgroup G) = 3 ^ 4 ∧
      ∀ b ∈ Bs, ∃ s ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ centralizer (X : Set G), b = s * c := by
  have hdec := o1pp_B_eq_of_model hX hBab hBX hU hU2 hBU hXU hrank hBs
  have hcomm : ∀ s ∈ Bs ⊓ X, ∀ c ∈ Bs ⊓ centralizer (X : Set G), s * c = c * s :=
    fun s hs c hc => mem_centralizer_iff.1 hc.2 s hs.2
  have hdisj : ∀ g ∈ Bs ⊓ X, g ∈ Bs ⊓ centralizer (X : Set G) → g = 1 := fun g hg hg' =>
    center_trivial_of_U52 hX g hg.2 fun y hy => (mem_centralizer_iff.1 hg'.2 y hy).symm
  refine ⟨?_, fun b hb => ?_⟩
  · have hcard := lem1025_card_sup hcomm hdisj
    rw [← hdec, hBs, hC] at hcard
    omega
  · obtain ⟨s, hs, c, hc, hsc⟩ := lem1025_exists_mul_of_mem_sup hcomm (hdec ▸ hb)
    exact ⟨s, hs, c, hc, hsc⟩

theorem lem1025_not_mem_closure {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut Bs)} {x zn zk : G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m n k p : Fin 7} (hW : WeylCoords Bs A x κ m) (hkm : k ≠ m) (hkn : k ≠ n) (hpm : p ≠ m)
    (hpn : p ≠ n) (hpk : p ≠ k) (hzn : zn ∈ Bs)
    (hcn : ∀ j, κ j ⟨zn, hzn⟩ = if j = n then 1 else ω3) (hzk : zk ∈ Bs)
    (hck : ∀ j, κ j ⟨zk, hzk⟩ = if j = k then 1 else ω3) :
    zk ∉ closure ({x, x * zn⁻¹} : Set G) := by
  have hx := hW.x_mem
  have hb : x * zn⁻¹ ∈ Bs := Bs.mul_mem hx (Bs.inv_mem hzn)
  set E : Subgroup G := (MonoidHom.eqLocus (κ k) (κ p)).map Bs.subtype with hE
  have hxE : x ∈ E := ⟨⟨x, hx⟩, by
    show κ k ⟨x, hx⟩ = κ p ⟨x, hx⟩
    rw [hW.x_coord, hW.x_coord, if_neg hkm, if_neg hpm], rfl⟩
  have hbE : x * zn⁻¹ ∈ E := ⟨⟨x * zn⁻¹, hb⟩, by
    show κ k ⟨x * zn⁻¹, hb⟩ = κ p ⟨x * zn⁻¹, hb⟩
    have : (⟨x * zn⁻¹, hb⟩ : Bs) = ⟨x, hx⟩ * ⟨zn, hzn⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, hW.x_coord, hW.x_coord, hcn, hcn, if_neg hkm,
      if_neg hpm, if_neg hkn, if_neg hpn], rfl⟩
  have hle : closure ({x, x * zn⁻¹} : Set G) ≤ E := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hxE
    · exact hbE
  intro hmem
  obtain ⟨y, hy, hyz⟩ := hle hmem
  have hy' : y = ⟨zk, hzk⟩ := Subtype.ext hyz
  rw [hy'] at hy
  have h : κ k ⟨zk, hzk⟩ = κ p ⟨zk, hzk⟩ := hy
  rw [hck, hck, if_pos rfl, if_neg hpk] at h
  exact one_ne_ω3 h

end CFSG.GGQ2Prime
