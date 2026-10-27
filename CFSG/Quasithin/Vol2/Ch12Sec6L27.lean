module

public import CFSG.Quasithin.Vol2.Ch12Sec6L24d
public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126L1a S126P S126L19 S126L19a
open scoped IsMulCommutative

theorem lemma12_6_27_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (h1219 : Lemma12_6_19) (h1221 : Lemma12_6_21) (h1226 : Lemma12_6_26) : Lemma12_6_27 := by
  intro G _ _ T L V _ F hH hZ g hne
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  have hfus := (h1219 G T L V F hH).1
  have hinj := S126L24.beta_injective F hZ
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => S126L1b.comm_of_mem ha hb
  by_cases hgV : g ∈ Subgroup.normalizer (V : Set G)
  · rw [conjSubgroup_eq_iff_mem_normalizer.2 hgV, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hVc w hw v hv
  obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨hxV, hx4⟩ := S126L20.wt4_of_mem_inter h331 h1222 h1262 F hH hfus hgV hx hx1
  obtain ⟨zv, hzv⟩ := F.β_surj e0123
  have hz1 : (zv : G) ∈ F.V1 := (S126L24.mem_preV zv.2).2 (hzv ▸ e0123_mem_W1)
  have hxne : F.β ⟨x, hxV⟩ ≠ 1 := fun h => hx1 (by
    have := hinj (h.trans (map_one F.β).symm)
    exact congrArg Subtype.val this)
  have hzne : F.β zv ≠ 1 := by
    rw [hzv]
    exact e0123_ne_one
  have hxs : ¬ IsNonsing (F.β ⟨x, hxV⟩) := fun h => not_nonsing_and_wt4 h hx4
  have hzs : ¬ IsNonsing (F.β zv) := fun h => not_nonsing_and_wt4 h (hzv ▸ hasWt_e0123)
  obtain ⟨l, hlL, hl, hlz⟩ := (part1 F ⟨x, hxV⟩ zv hxne hzne).2 (iff_of_false hxs hzs)
  have hlx : l * x * l⁻¹ = zv := congrArg Subtype.val (hinj hlz)
  have hzg : (zv : G) ∈ V ⊓ conjSubgroup V (g * l⁻¹) := by
    refine ⟨zv.2, mem_conjSubgroup_iff.2 ?_⟩
    rw [← hlx, show g * l⁻¹ * (l * x * l⁻¹) * (g * l⁻¹)⁻¹ = g * x * g⁻¹ by group]
    exact mem_conjSubgroup_iff.1 hx.2
  obtain ⟨c, hc, hgc⟩ := S126L20.exists_centralizer_conj hLV hfus hzg
  have hcard : Nat.card F.V1 = 2 := (S126L23d.part2 h1222 F hH hZ).2
  have hzne1 : (zv : G) ≠ 1 := fun h => hzne (by rw [show zv = 1 from Subtype.ext h, map_one])
  have hcN : c ∈ Subgroup.normalizer (F.V1 : Set G) := by
    rw [normalizer_eq_centralizer_of_card_eq_two hcard, Subgroup.mem_centralizer_iff]
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, one_mul, mul_one]
    · rw [S126L23d.eq_of_card_two hcard hw hz1 hw1 hzne1]
      exact (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  have hab := h1226 G T L V F hH hZ _ (S126L24.inHz_G1 h1222 h1221 F hH hZ)
  have hcomm : ∀ v ∈ V, ∀ y ∈ conjSubgroup V c, v * y = y * v := by
    intro v hv y hy
    have hv' : v ∈ conjClosure V (Subgroup.normalizer (F.V1 : Set G)) :=
      le_conjClosure V _ hv
    have hy' : y ∈ conjClosure V (Subgroup.normalizer (F.V1 : Set G)) := by
      have h1 := mem_conjSubgroup_iff.1 hy
      have h2 := mem_conjClosure (Subgroup.inv_mem _ hcN) h1
      rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h2
    have := hab
    exact congrArg Subtype.val (mul_comm' (⟨v, hv'⟩ :
      ↥(conjClosure V (Subgroup.normalizer (F.V1 : Set G)))) ⟨y, hy'⟩)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy1 : l * y * l⁻¹ ∈ conjSubgroup V c := by
    rw [← hgc, mem_conjSubgroup_iff,
      show g * l⁻¹ * (l * y * l⁻¹) * (g * l⁻¹)⁻¹ = g * y * g⁻¹ by group]
    exact mem_conjSubgroup_iff.1 hy
  have hv1 : l * v * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hlL) v).1 hv
  have h := hcomm _ hv1 _ hy1
  have e : l * (v * y) * l⁻¹ = l * (y * v) * l⁻¹ := by
    calc l * (v * y) * l⁻¹ = l * v * l⁻¹ * (l * y * l⁻¹) := by group
      _ = l * y * l⁻¹ * (l * v * l⁻¹) := h
      _ = l * (y * v) * l⁻¹ := by group
  calc y * v = l⁻¹ * (l * (y * v) * l⁻¹) * l := by group
    _ = l⁻¹ * (l * (v * y) * l⁻¹) * l := by rw [e]
    _ = v * y := by group

end CFSG.Quasithin.H13

