module

public import CFSG.RankThree.PartTwo.Sec12.Hering129GHJ
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem Cfg129.gen_facts {A L K S : Subgroup G} {c b a : G} (cfg : Cfg129 G A c L b a K S)
    {x : G} (hxD : x ∈ D129 a b) (hxb : x ∉ Subgroup.zpowers b) :
    A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c ∧
      b ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c := by
  obtain ⟨hbA, haA, -, hb1, ha1, -, -, hab, -⟩ := cfg.point_facts
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := cfg.std.isE27.1
  have hA27 : Nat.card A = 27 := cfg.std.isE27.2
  have hcA : c ∈ A := cfg.std.mem_A
  have hc1 : c ≠ 1 := cfg.std.ne_one
  have hcD : c ∉ D129 a b := cfg.not_mem_D
  have hexp : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hsub : ∀ S : Subgroup G, S ≤ A → IsMulCommutative S := fun S hS =>
    isMulCommutative_iff_of_setLike.mpr fun p hp q hq => hcomm p (hS hp) q (hS hq)
  have hcent : ∀ S : Subgroup G, S ≤ A → ∀ v ∈ A, v ∈ Subgroup.centralizer (S : Set G) :=
    fun S hS v hv => Subgroup.mem_centralizer_iff.mpr fun s hs => hcomm s (hS hs) v hv
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hbD : b ∈ D129 a b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hexp x hxA) hx1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hexp b hbA) hb1
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hexp a haA) ha1
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcA) hc1
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one hx3 h hb1 (Subgroup.mem_zpowers b))
  have hdisjx : Subgroup.zpowers x ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    exact hxb (mem_of_mem_zpowers_of_ne_one hx3 hy.1 hy1 hy.2)
  have hdisja : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    exact hab (mem_of_mem_zpowers_of_ne_one ha3 hy.1 hy1 hy.2)
  have hdisjc : D129 a b ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    exact hcD (mem_of_mem_zpowers_of_ne_one hc3 hy.2 hy1 hy.1)
  have hcardx : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers b : Subgroup G) = 9 := by
    have hWA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.mpr hxA
    obtain ⟨h, -, -⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint
      (hcent _ hWA b hbA) (hsub _ hWA) (fun w hw => hexp w (hWA hw)) hb3 hdisjx
    rw [Nat.card_zpowers, hx3] at h
    omega
  have hcardD : Nat.card (D129 a b : Subgroup G) = 9 := by
    have haA' : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
    obtain ⟨h, -, -⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint
      (hcent _ haA' b hbA) (hsub _ haA') (fun w hw => hexp w (haA' hw)) hb3 hdisja
    rw [Nat.card_zpowers, ha3] at h
    exact h
  have hsupx : Subgroup.zpowers x ⊔ Subgroup.zpowers b = D129 a b :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hbD))
      (hcardD.trans hcardx.symm).le
  have hcardDc : Nat.card (D129 a b ⊔ Subgroup.zpowers c : Subgroup G) = 27 := by
    obtain ⟨h, -, -⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint
      (hcent _ hDA c hcA) (hsub _ hDA) (fun w hw => hexp w (hDA hw)) hc3 hdisjc
    rw [hcardD] at h
    omega
  have hDc : D129 a b ⊔ Subgroup.zpowers c = A :=
    Subgroup.eq_of_le_of_card_ge (sup_le hDA (Subgroup.zpowers_le.mpr hcA))
      (hA27.trans hcardDc.symm).le
  have hA_eq : A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
    rw [hsupx]
    exact hDc.symm
  refine ⟨hA_eq, ?_⟩
  intro hb
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hcomm x hxA c hcA) hb
  have hcj : c ^ j = (x ^ i)⁻¹ * b := by rw [hij, inv_mul_cancel_left]
  have hcjD : c ^ j ∈ D129 a b := by
    rw [hcj]
    exact (D129 a b).mul_mem ((D129 a b).inv_mem ((D129 a b).zpow_mem hxD i)) hbD
  by_cases hj1 : c ^ j = 1
  · apply hbx
    rw [hij, hj1, mul_one]
    exact Subgroup.zpow_mem_zpowers x i
  · exact hcD (mem_of_mem_zpowers_of_ne_one hc3 (Subgroup.zpow_mem_zpowers c j) hj1 hcjD)

end CFSG.RankThree.PartTwo.Sec12
