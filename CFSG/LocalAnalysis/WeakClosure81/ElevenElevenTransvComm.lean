module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenTransv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_mul_self_mem_oTwoIn {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G} (ht : t ∈ L ⊓ Q) :
    t * t ∈ oTwoIn L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, -, p, -, hαk, -, -, -, hαS, -⟩ := eleven11_exists_model hd h8
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have htα : α ⟨t, htL⟩ ∈ CFSG.QuasithinUnique.Setup.Campbell.rootGrp p := by
    rw [← hαS]
    exact Subgroup.mem_map_of_mem α (Subgroup.mem_subgroupOf.2 ht)
  have hsq : α ⟨t, htL⟩ * α ⟨t, htL⟩ = 1 :=
    CFSG.QuasithinUnique.Setup.Campbell.mul_self_eq_one_of_mem_rootGrp htα
  have hker : (⟨t, htL⟩ * ⟨t, htL⟩ : ↥L) ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hsq
  rw [hαk, Subgroup.mem_subgroupOf] at hker
  exact hker

private noncomputable def commMapAux (W : Subgroup G) (t : G)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hn : ∀ w ∈ W, t * w * t⁻¹ ∈ W) : ↥W →* G :=
  MonoidHom.mk' (fun w => t * (w : G) * t⁻¹ * (w : G)⁻¹) (by
    intro a b
    have hc : (t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹) :=
      hab _ (W.mul_mem (hn b b.2) (W.inv_mem b.2)) _ (W.inv_mem a.2)
    calc t * ((a * b : ↥W) : G) * t⁻¹ * ((a * b : ↥W) : G)⁻¹
        = (t * (a : G) * t⁻¹) * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (t * (a : G) * t⁻¹) * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by rw [hc]
      _ = (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹) := by group)

private theorem commMapAux_apply (W : Subgroup G) (t : G)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hn : ∀ w ∈ W, t * w * t⁻¹ ∈ W) (w : ↥W) :
    commMapAux W t hab hn w = t * (w : G) * t⁻¹ * (w : G)⁻¹ := rfl

theorem eleven11_mem_commutator_zpowers_iff
    {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G}
    (ht : t ∈ L ⊓ Q) {r : G} :
    r ∈ ⁅Subgroup.zpowers t, blockU L⁆ ↔ ∃ w ∈ blockU L, t * w * t⁻¹ * w⁻¹ = r := by
  classical
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have hsq : t * t ∈ oTwoIn L := eleven11_mul_self_mem_oTwoIn hd h8 ht
  have hcen : ∀ w ∈ blockU L, ∀ s ∈ oTwoIn L, w * s = s * w := fun w hw s hs =>
    Subgroup.mem_centralizer_iff.1 (ThmOne.oTwoIn_le_centralizer_blockU hLb.2.2.1 hs) w hw
  have hn : ∀ w ∈ blockU L, t * w * t⁻¹ ∈ blockU L := fun w hw =>
    conj_mem_blockU (Subgroup.le_normalizer htL) hw
  let f := commMapAux (blockU L) t (eleven11_blockU_comm hd) hn
  have hR : ⁅Subgroup.zpowers t, blockU L⁆ = f.range := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro a ha w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · refine ⟨1, ?_⟩
        have hs : (t * t) ^ m ∈ oTwoIn L := Subgroup.zpow_mem _ hsq m
        have h1 : t ^ k = (t * t) ^ m := by rw [hm, zpow_mul, zpow_two]
        have h2 := hcen w hw _ hs
        rw [map_one, h1, commutatorElement_def, ← h2]
        group
      · refine ⟨⟨w, hw⟩, ?_⟩
        have hs : (t * t) ^ m ∈ oTwoIn L := Subgroup.zpow_mem _ hsq m
        have h1 : t ^ k = t * (t * t) ^ m := by
          rw [hm, show 2 * m + 1 = 1 + 2 * m by omega, zpow_add, zpow_one, zpow_mul, zpow_two]
        have h2 := hcen w hw _ hs
        rw [commMapAux_apply, h1, commutatorElement_def]
        have : t * (t * t) ^ m * w * (t * (t * t) ^ m)⁻¹ * w⁻¹
            = t * ((t * t) ^ m * w * ((t * t) ^ m)⁻¹) * t⁻¹ * w⁻¹ := by group
        rw [this, ← h2]
        group
    · rintro _ ⟨w, rfl⟩
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t) w.2
  rw [hR]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem eleven11_commutator_zpowers_le_line
    {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G}
    (ht : t ∈ L ⊓ Q) (ht0 : t ∉ oTwoIn L) :
    ⁅Subgroup.zpowers t, blockU L⁆ ≤ ⁅V, X⁆ ⊔ blockZ L := by
  classical
  intro r hr
  obtain ⟨w, hw, rfl⟩ := (eleven11_mem_commutator_zpowers_iff hd h8 ht).1 hr
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have hsq : t * t ∈ oTwoIn L := eleven11_mul_self_mem_oTwoIn hd h8 ht
  have hcen : w * (t * t) = (t * t) * w :=
    Subgroup.mem_centralizer_iff.1 (ThmOne.oTwoIn_le_centralizer_blockU hLb.2.2.1 hsq) w hw
  have htw : t * w * t⁻¹ ∈ blockU L := conj_mem_blockU (Subgroup.le_normalizer htL) hw
  have hcW : t * w * t⁻¹ * w⁻¹ ∈ blockU L := (blockU L).mul_mem htw ((blockU L).inv_mem hw)
  have hcc : t * (t * w * t⁻¹ * w⁻¹) * t⁻¹ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by
    calc t * (t * w * t⁻¹ * w⁻¹) * t⁻¹ = (t * t * w) * t⁻¹ * w⁻¹ * t⁻¹ := by group
      _ = (w * (t * t)) * t⁻¹ * w⁻¹ * t⁻¹ := by rw [hcen]
      _ = (t * w * t⁻¹ * w⁻¹)⁻¹ := by group
  have hc2 : (t * w * t⁻¹ * w⁻¹) * (t * w * t⁻¹ * w⁻¹) = 1 := by
    have := ThmOne.pow_two_eq_one_of_mem_blockU hLb.2.2.1 hcW
    rwa [pow_two] at this
  have h1 : t * (t * w * t⁻¹ * w⁻¹) * t⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ ∈ blockZ L := by
    rw [hcc]
    have : (t * w * t⁻¹ * w⁻¹)⁻¹ * (t * w * t⁻¹ * w⁻¹)⁻¹ = 1 := by
      rw [← mul_inv_rev, hc2, inv_one]
    rw [this]
    exact (blockZ L).one_mem
  exact eleven11_mem_of_comm_mem_blockZ hd h8 ht ht0 hcW h1

theorem eleven11_card_commutator_zpowers
    {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {t : G}
    (ht : t ∈ L ⊓ Q) (ht0 : t ∉ oTwoIn L) :
    Nat.card (⁅Subgroup.zpowers t, blockU L⁆ : Subgroup G) = 4 := by
  classical
  have htL : t ∈ L := (Subgroup.mem_inf.1 ht).1
  have hn : ∀ w ∈ blockU L, t * w * t⁻¹ ∈ blockU L := fun w hw =>
    conj_mem_blockU (Subgroup.le_normalizer htL) hw
  let f := commMapAux (blockU L) t (eleven11_blockU_comm hd) hn
  have hR : ⁅Subgroup.zpowers t, blockU L⁆ = f.range := by
    ext r
    rw [eleven11_mem_commutator_zpowers_iff hd h8 ht]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, w.2, rfl⟩
  have hle : ⁅V, X⁆ ⊔ blockZ L ≤ blockU L :=
    sup_le ((eleven11_commutator_VX hd h8).1.trans inf_le_right) (blockZ_le_blockU L)
  have hker : f.ker = (⁅V, X⁆ ⊔ blockZ L).subgroupOf (blockU L) := by
    ext ⟨w, hw⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← eleven11_blockU_inf_centralizer hd h8 ht ht0,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, commMapAux_apply]
    constructor
    · intro h
      refine ⟨hw, ?_⟩
      have h' : t * w * t⁻¹ * w⁻¹ = 1 := h
      exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h')).symm
    · rintro ⟨-, h⟩
      have h' : w * t = t * w := h
      show t * w * t⁻¹ * w⁻¹ = 1
      rw [← h']
      group
  have hkercard : Nat.card f.ker = Nat.card (⁅V, X⁆ ⊔ blockZ L : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 := eleven11_card_blockU_eq_four_mul hd h8
  have hpos : 0 < Nat.card (⁅V, X⁆ ⊔ blockZ L : Subgroup G) := Nat.card_pos
  rw [hkercard] at h1
  rw [hR]
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, show Nat.card ↥(blockU L) = Nat.card (blockU L : Subgroup G) from rfl, h2, mul_comm]

end CFSG.LocalAnalysis.WeakClosure81
