module

public import CFSG.Quasithin.Vol2.Ch10SecB6Bar
public import CFSG.Quasithin.Vol2.Ch10SecQ4A15
public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ4

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem sl2_commute_neg_one {p : ℕ} (a : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    Commute a (-1) := by
  show a * -1 = -1 * a
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_neg]

omit [Finite G] in
theorem mem_pCoreOf_of_mk_eq_one {H : Subgroup G} {x : ↥H}
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = 1) : (x : G) ∈ pCoreOf 2 H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact ⟨x, hx, rfl⟩

theorem false_of_isQuasisimple {VK K K1 D : Subgroup G} {z : G}
    (hK1 : K1 ∈ cComp (Subgroup.normalizer (VK : Set G)))
    (hK1n : Subgroup.normalizer (VK : Set G) ≤ Subgroup.normalizer (K1 : Set G))
    (hKK1 : K ≤ K1) (hKp : ⁅K, K⁆ = K) (hKV : ¬ K ≤ Subgroup.centralizer (VK : Set G))
    (hDK1 : D ≤ K1) (hDC : D ≤ Subgroup.centralizer (VK : Set G)) (hDodd : Odd (Nat.card D))
    (hD1 : D ≠ ⊥) (hDD : ⁅D, Subgroup.zpowers z⁆ = D) (hzK : z ∈ K)
    (hq : CFSG.IsQuasisimple ↥(modO2Image (Subgroup.normalizer (VK : Set G)) K1)) : False := by
  set H := Subgroup.normalizer (VK : Set G) with hHdef
  have hK1H : K1 ≤ H := le_of_mem_cComp hK1
  have hzK1 : z ∈ K1 := hKK1 hzK
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set Kb := modO2Image H K1 with hKb
  have hmemKb : ∀ {x : G} (hx : x ∈ K1), π ⟨x, hK1H hx⟩ ∈ Kb := fun hx =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  set N : Subgroup G := K1 ⊓ Subgroup.centralizer (VK : Set G) with hN
  set Nb := modO2Image H N with hNb
  have hNH : N ≤ H := inf_le_left.trans hK1H
  have hNn : (N.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hK1n hh, mem_normalizer_centralizer hh⟩
  have hNbn : Nb.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
  have hNbK : Nb ≤ Kb := SecB.modO2Image_mono' inf_le_left
  have hsub : (Nb.subgroupOf Kb).Normal := hNbn.subgroupOf Kb
  have hmemNb : ∀ {x : G} (hx : x ∈ N), π ⟨x, hNH hx⟩ ∈ Nb := fun hx =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  rcases C10E4.normal_le_center_or_eq_top' hq (Nb.subgroupOf Kb) with hc | htop
  ·
    apply hD1
    have hDQ : D ≤ pCoreOf 2 H := by
      rw [← hDD, Subgroup.commutator_le]
      intro d hd y hy
      have hdN : d ∈ N := ⟨hDK1 hd, hDC hd⟩
      have hyK1 : y ∈ K1 := (Subgroup.zpowers_le.mpr hzK1) hy
      have hdc : (⟨π ⟨d, hNH hdN⟩, hNbK (hmemNb hdN)⟩ : ↥Kb) ∈ Subgroup.center ↥Kb :=
        hc (Subgroup.mem_subgroupOf.mpr (hmemNb hdN))
      have h1 := congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hdc ⟨π ⟨y, hK1H hyK1⟩, hmemKb hyK1⟩)
      have h2 : π (⁅(⟨d, hNH hdN⟩ : ↥H), (⟨y, hK1H hyK1⟩ : ↥H)⁆) = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1.symm
      exact mem_pCoreOf_of_mk_eq_one h2
    have h2 := SecB.inf_eq_bot_of_two_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hDodd
    exact le_bot_iff.mp (h2 ▸ le_inf hDQ le_rfl)
  ·
    apply hKV
    have hKN : K ≤ Subgroup.centralizer (VK : Set G) ⊔ pCoreOf 2 H := by
      intro k hk
      have hkK1 := hKK1 hk
      have hkb : (⟨π ⟨k, hK1H hkK1⟩, hmemKb hkK1⟩ : ↥Kb) ∈ Nb.subgroupOf Kb :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hkb)
      have h1 : π (n⁻¹ * ⟨k, hK1H hkK1⟩) = 1 := by
        rw [map_mul, map_inv, hnk, inv_mul_cancel]
      have hk' : k = (n : G) * ((n⁻¹ * ⟨k, hK1H hkK1⟩ : ↥H) : G) := by simp
      rw [hk']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hn).2)
        (Subgroup.mem_sup_right (mem_pCoreOf_of_mk_eq_one h1))
    exact le_of_perfect_of_le_sup hKp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
      (fun k hk => mem_normalizer_centralizer ((hKK1.trans hK1H) hk))
      (fun x hx => mem_normalizer_centralizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H hx)) hKN

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
