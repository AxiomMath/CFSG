module

public import CFSG.Quasithin.Vol2.Ch10SecD12I

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem faithful_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    ∀ x ∈ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G),
      (∀ v ∈ fsuUL T L I, x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) →
        x ∈ Subgroup.centralizer (fsuUL T L I : Set G) := by
  intro x hx hcomm
  have hxV : x ∈ Subgroup.normalizer (fsuUL T L I : Set G) := hx.2
  have hmem : ∀ v ∈ fsuUL T L I, x * v * x⁻¹ * v⁻¹ ∈ fsuUL T L I := fun v hv =>
    (fsuUL T L I).mul_mem ((Subgroup.mem_normalizer_iff.mp hxV v).mp hv)
      ((fsuUL T L I).inv_mem hv)
  have hCL : Subgroup.centralizer (fsuL0 T L : Set G) ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.centralizer_le (SecA.le_fsuL0 T L)
  by_cases hZ : fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : x * v * x⁻¹ * v⁻¹ ∈ fsuUL T L I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨hmem v hv, hCL (hcomm v hv)⟩
    rw [hZ, Subgroup.mem_bot] at h1
    calc v * x = (x * v * x⁻¹ * v⁻¹)⁻¹ * x * v := by group
      _ = x * v := by rw [h1]; group
  · obtain ⟨-, hc2⟩ := card_V1_eq h37 h38 hI16 h h3 hZ
    have h3' := h3
    obtain ⟨-, hcm, -⟩ := h3'
    set c : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨x, hxV⟩ with hc
    have hfixx : fixV (Subgroup.zpowers c) =
        (Subgroup.centralizer ({x} : Set G)).subgroupOf (fsuUL T L I) := by
      ext v
      rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hv
        have h1 : x * (v : G) * x⁻¹ = v := congrArg Subtype.val hv
        calc (v : G) * x = x * v * x⁻¹ * x := by rw [h1]
          _ = x * v := by group
      · intro hv
        apply Subtype.ext
        show x * (v : G) * x⁻¹ = v
        rw [← hv]
        group
    have hcomV : commV (Subgroup.zpowers c) ≤ cV1 T L I := by
      rw [commV_zpowers_eq_map]
      rintro _ ⟨v, -, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      show ((c v : ↥(fsuUL T L I)) : G) * (v : G)⁻¹ ∈ _
      rw [hc, A1b.conjAct_coe]
      exact hcomm v v.2
    have h1 := card_commV_mul_card_fixV (SecC.sq_eq_one_fsuUL h) c
    have h2 := Subgroup.card_le_of_le hcomV
    rw [hc2] at h2
    have h4 := Subgroup.card_mul_index (fixV (Subgroup.zpowers c))
    have hidx : (Subgroup.centralizer ({x} : Set G)).relIndex (fsuUL T L I) ≤ 2 := by
      show ((Subgroup.centralizer ({x} : Set G)).subgroupOf (fsuUL T L I)).index ≤ 2
      rw [← hfixx]
      have hpos : 0 < Nat.card (fixV (Subgroup.zpowers c)) := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : 3 * Nat.card (fixV (Subgroup.zpowers c)) ≤
          Nat.card (commV (Subgroup.zpowers c)) * Nat.card (fixV (Subgroup.zpowers c)) := by
        rw [h1, ← h4, mul_comm]
        exact Nat.mul_le_mul_left _ hlt
      have := Nat.le_of_mul_le_mul_right this hpos
      omega
    exact mem_centralizer_V1 h37 h38 hI16 h h3 hZ (mem_normalizer_L h37 h38 h hx) hxV hidx

theorem gen_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (Y : Subgroup G) (hY : ∀ v ∈ fsuUL T L I, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) →
      L ⊓ Subgroup.centralizer ({v} : Set G) ≤ Y) : L ≤ Y := by
  have h8 := card_V1_eq_eight_mul h3
  have hcV := card_cV1_le_two h37 h38 hI16 h h3
  have hcV' : Nat.card ↥(cV1 T L I) =
      Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
    rw [cV1, card_subgroupOf_eq, inf_comm]
  obtain ⟨-, hcomm, hnat⟩ := h3
  have hfix := fixV_autOn_V1 h37 h38 h
  have hb : Nat.card ↥(cV1 T L I) * Nat.card ↥(cV1 T L I) < Nat.card ↥(fsuUL T L I) := by
    rw [h8, ← hcV']
    have := Nat.card_pos (α := ↥(cV1 T L I))
    nlinarith
  rw [← hfix] at hnat hb
  obtain ⟨D⟩ := hnat.toL3Coord
  have hLN : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1
  have key : ∀ γ : L3.Γ, L3.IsInvol γ → D.rho γ ∈ autOn (L ⊓ Y) (fsuUL T L I) := by
    intro γ hγ
    have h2 : (D.rho γ) ^ 2 = 1 := by rw [← map_pow, pow_two, hγ.1, map_one]
    obtain ⟨w, hw, hwZ⟩ := exists_fix_not_mem (SecC.sq_eq_one_fsuUL h) h2 hb
    obtain ⟨⟨l, hlN⟩, hl, hlρ⟩ := D.rho_mem γ
    have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hwL : (w : G) ∉ Subgroup.centralizer (fsuL0 T L : Set G) := by
      rw [hfix] at hwZ
      exact fun h' => hwZ (Subgroup.mem_subgroupOf.mpr h')
    have hlw : l ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : l * (w : G) * l⁻¹ = w := by
        rw [← A1b.conjAct_coe (fsuUL T L I) ⟨l, hlN⟩ w]
        have := hw
        rw [← hlρ] at this
        exact congrArg Subtype.val this
      calc l * (w : G) = l * w * l⁻¹ * l := by group
        _ = w * l := by rw [h1]
    refine ⟨⟨l, hlN⟩, Subgroup.mem_subgroupOf.mpr ⟨hlL, hY w w.2 hwL ⟨hlL, hlw⟩⟩, ?_⟩
    exact hlρ
  have hGS := D.le_of_gens (key _ L3.x12_invol) (key _ L3.x23_invol) (key _ L3.x31_invol)
  obtain ⟨v0, hv0, hv0L⟩ : ∃ v0 ∈ fsuUL T L I, v0 ∉ Subgroup.centralizer (fsuL0 T L : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : fsuUL T L I ≤ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) :=
      fun v hv => ⟨hv, hcon v hv⟩
    have := Subgroup.card_le_of_le hle
    have hpos : 0 < Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :=
      Nat.card_pos
    omega
  intro l hl
  obtain ⟨⟨y, hyN⟩, hy, hyl⟩ := hGS ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hyLY := Subgroup.mem_subgroupOf.mp hy
  have hyl' : conjAct (fsuUL T L I) (⟨y, hyN⟩⁻¹ * ⟨l, hLN hl⟩) = 1 := by
    rw [map_mul, map_inv, hyl, inv_mul_cancel]
  have hC := A1b.conjAct_eq_one_iff.mp hyl'
  have hyl2 : y⁻¹ * l ∈ L ⊓ Subgroup.centralizer ({v0} : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hyLY.1) hl, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hC v0 hv0).symm
  have := Y.mul_mem hyLY.2 (hY v0 hv0 hv0L hyl2)
  simpa using this

theorem genFaithful_three (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hI16 : ASInputs.AS_I_1_6) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) :
    GenFaithful T L I := by
  refine ⟨faithful_three h37 h38 hI16 h h3, gen_three h37 h38 hI16 h h3, 3, Nat.prime_three,
    by norm_num, ?_⟩
  obtain ⟨⟨e⟩, -⟩ := h3
  rw [Nat.card_congr e.toEquiv, L3.card_Γ]
  norm_num

end CFSG.Quasithin.Vol2.Ch10.SecD
