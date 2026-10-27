module

public import CFSG.Quasithin.Background.I62Pair
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.I62

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

namespace Hyp

variable {V A : Subgroup G} (h : Hyp V A)
include h

theorem card_tiU_eq : Nat.card (tiU V A) = Nat.card (tiB V A) := by
  obtain ⟨v, hv, hvU⟩ := h.exists_mem_not_mem
  obtain ⟨a, ha, haB⟩ := h.exists_mem_not_mem'
  exact le_antisymm (h.toBase.symm.card_tiB_le ha haB) (h.toBase.card_tiB_le hv hvU)

theorem tiU_eq_commutator {v : G} (hv : v ∈ V) (hvU : v ∉ tiU V A) :
    tiU V A = ⁅tiY V A, Subgroup.zpowers v⁆ := by
  have hb := h.toBase
  have hvX : v ∈ tiX V A := Subgroup.mem_sup_left hv
  have hv2 := hb.mul_self_V hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  apply le_antisymm
  ·
    set φ := hb.commHom hvX hv2 with hφ
    have hker : φ.ker = (tiU V A).subgroupOf (tiY V A) := by
      ext y
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hb.inf_centralizer_tiY hv hvU]
      constructor
      · intro hy1
        have h1 : ⁅(y : G), v⁆ = 1 := congrArg Subtype.val hy1
        exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
          (commutatorElement_eq_one_iff_mul_comm.mp h1)⟩
      · rintro ⟨-, hyv⟩
        apply Subtype.ext
        show ⁅(y : G), v⁆ = 1
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hyv)
    have hrange : φ.range ≤ (tiU V A).subgroupOf (tiY V A) := by
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_subgroupOf, hb.commHom_apply, ← hb.inf_centralizer_tiY hv hvU]
      exact hb.commutatorElement_mem_centralizer hvX hv2 y.2
    have hUY : tiU V A ≤ tiY V A := le_sup_left
    have hcU : Nat.card ↥((tiU V A).subgroupOf (tiY V A)) = Nat.card (tiU V A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUY).toEquiv
    have e1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hcU] at e1
    have e3 : Nat.card (tiY V A) = Nat.card (tiU V A) * Nat.card (tiB V A) := by
      have := B2F.card_sup_mul_card_inf_of_commute (A := tiU V A) (B := tiB V A)
        fun _ hu _ hb' => hb.comm_tiU_tiB hu hb'
      rw [hb.tiU_inf_tiB, Subgroup.card_bot, mul_one] at this
      exact this
    have hpos : 0 < Nat.card (tiU V A) := Nat.card_pos
    have hcard : Nat.card ↥φ.range = Nat.card ↥((tiU V A).subgroupOf (tiY V A)) := by
      rw [hcU]
      have : Nat.card (tiU V A) * Nat.card ↥φ.range =
          Nat.card (tiU V A) * Nat.card (tiU V A) := by
        rw [e1, e3, h.card_tiU_eq]
      exact Nat.eq_of_mul_eq_mul_left hpos this
    have hreq : φ.range = (tiU V A).subgroupOf (tiY V A) :=
      Subgroup.eq_of_le_of_card_ge hrange hcard.ge
    intro u hu
    have hu' : (⟨u, hUY hu⟩ : ↥(tiY V A)) ∈ φ.range := by
      rw [hreq]
      exact hu
    obtain ⟨y, hy⟩ := hu'
    have e : ⁅(y : G), v⁆ = u := congrArg Subtype.val hy
    rw [← e]
    exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers v)
  · rw [Subgroup.commutator_le]
    intro y hy w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hk : v ^ k = 1 ∨ v ^ k = v := by
      have hv2' : v ^ (2 : ℤ) = 1 := by
        rw [zpow_two, hv2]
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left
        rw [← two_mul, zpow_mul, hv2', one_zpow]
      · right
        rw [zpow_add, zpow_mul, hv2', one_zpow, one_mul, zpow_one]
    rcases hk with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact (tiU V A).one_mem
    · rw [hk, ← hb.inf_centralizer_tiY hv hvU]
      exact hb.commutatorElement_mem_centralizer hvX hv2 hy

theorem mem_normalizer_of_conj_mem {g c : G} (hg : g ∈ tiX V A) (hc : c ∈ V)
    (hcU : c ∉ tiU V A) (hgc : g * c * g⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  have hb := h.toBase
  have hcX : c ∈ tiX V A := Subgroup.mem_sup_left hc
  have hc'X : g * c * g⁻¹ ∈ tiX V A :=
    (tiX V A).mul_mem ((tiX V A).mul_mem hg hcX) ((tiX V A).inv_mem hg)
  have hc'Y := hb.tiX_le_normalizer_tiY hc'X
  have hc'U : g * c * g⁻¹ ∈ Subgroup.normalizer ((tiU V A : Subgroup G) : Set G) := by
    rw [hb.tiU_eq_inf_centralizer hc hcU]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hc'Y, B2F.normalizer_le_normalizer_centralizer V hgc⟩
  have h2 : 2 ∣ Nat.card (tiU V A) :=
    two_dvd_card_of_ne_bot (B2F.isPGroup_of_isElemAbelian hb.isElemAbelian_tiU) h.ne
  have hc'2 : (g * c * g⁻¹) ^ (2 ^ 1) = 1 := by
    rw [pow_one, conj_pow, hb.hV.2 c hc, mul_one, mul_inv_cancel]
  obtain ⟨d, hdU, hd1, hdc⟩ := exists_ne_one_comm_of_normalizes h2 hc'U hc'2
  have hdY : g⁻¹ * d * g ∈ tiY V A := by
    have hgY := hb.tiX_le_normalizer_tiY ((tiX V A).inv_mem hg)
    have := (Subgroup.mem_normalizer_iff.mp hgY d).mp (Subgroup.mem_sup_left hdU)
    simpa using this
  have hdc' : g⁻¹ * d * g ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * d * g * c = g⁻¹ * (g * c * g⁻¹ * d) * g := by
          rw [hdc]; group
      _ = c * (g⁻¹ * d * g) := by group
  have hdU' : g⁻¹ * d * g ∈ tiU V A := by
    rw [← hb.inf_centralizer_tiY hc hcU]
    exact ⟨hdY, hdc'⟩
  have hne : V ⊓ conjSubgroup V g⁻¹ ≠ ⊥ := by
    intro hbot
    apply hd1
    have : d ∈ V ⊓ conjSubgroup V g⁻¹ :=
      ⟨hdU.1, mem_conjSubgroup_iff.mpr (by rw [inv_inv]; exact hdU'.1)⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  have := (Subgroup.normalizer (V : Set G)).inv_mem (hb.mem_normalizer_of_inf_ne_bot hne)
  rwa [inv_inv] at this

theorem eq_conjSubgroup_of_conj_mem {g a : G} (hg : g ∈ tiX V A) (ha : a ∈ A)
    (haB : a ∉ tiB V A) (hga : g * a * g⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    V = conjSubgroup A g⁻¹ := by
  have hb := h.toBase
  obtain ⟨v, hv, hvU⟩ := h.exists_mem_not_mem
  have haX : a ∈ tiX V A := Subgroup.mem_sup_right ha
  have ha'X : g * a * g⁻¹ ∈ tiX V A :=
    (tiX V A).mul_mem ((tiX V A).mul_mem hg haX) ((tiX V A).inv_mem hg)
  have ha'Y := hb.tiX_le_normalizer_tiY ha'X
  have ha'U : g * a * g⁻¹ ∈ Subgroup.normalizer ((tiU V A : Subgroup G) : Set G) := by
    rw [hb.tiU_eq_inf_centralizer hv hvU]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨ha'Y, B2F.normalizer_le_normalizer_centralizer V hga⟩
  have h2 : 2 ∣ Nat.card (tiU V A) :=
    two_dvd_card_of_ne_bot (B2F.isPGroup_of_isElemAbelian hb.isElemAbelian_tiU) h.ne
  have ha'2 : (g * a * g⁻¹) ^ (2 ^ 1) = 1 := by
    rw [pow_one, conj_pow, hb.hA.2 a ha, mul_one, mul_inv_cancel]
  obtain ⟨d, hdU, hd1, hda⟩ := exists_ne_one_comm_of_normalizes h2 ha'U ha'2
  have hdY : g⁻¹ * d * g ∈ tiY V A := by
    have hgY := hb.tiX_le_normalizer_tiY ((tiX V A).inv_mem hg)
    have := (Subgroup.mem_normalizer_iff.mp hgY d).mp (Subgroup.mem_sup_left hdU)
    simpa using this
  have hda' : g⁻¹ * d * g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * d * g * a = g⁻¹ * (g * a * g⁻¹ * d) * g := by
          rw [hda]; group
      _ = a * (g⁻¹ * d * g) := by group
  have hdB : g⁻¹ * d * g ∈ tiB V A := by
    rw [← hb.inf_centralizer_tiY' ha haB]
    exact ⟨hdY, hda'⟩
  by_contra hne
  have hbot := h.cross g⁻¹ hne
  apply hd1
  have : d ∈ conjSubgroup A g⁻¹ ⊓ V :=
    ⟨mem_conjSubgroup_iff.mpr (by rw [inv_inv]; exact hdB.1), hdU.1⟩
  rw [hbot] at this
  exact Subgroup.mem_bot.mp this

theorem le_normalizer_of_le {S : Subgroup G} (hSX : S ≤ tiX V A) (hS : IsPGroup 2 S)
    (hVS : V ≤ S) : S ≤ Subgroup.normalizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hcU⟩ := h.exists_mem_not_mem
  by_contra hSN
  set N₀ : Subgroup ↥S := (S ⊓ Subgroup.normalizer (V : Set G)).subgroupOf S with hN₀
  have hlt : N₀ < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hSN fun s hs => ?_
    have : (⟨s, hs⟩ : ↥S) ∈ N₀ := by rw [htop]; exact Subgroup.mem_top _
    exact this.2
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  obtain ⟨s, hsN, hsN₀⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent N₀ hlt)
  have hsV : (s : G) ∉ Subgroup.normalizer (V : Set G) := fun h' => hsN₀ ⟨s.2, h'⟩
  apply hsV
  refine h.mem_normalizer_of_conj_mem (hSX s.2) hc hcU ?_
  have hcN₀ : (⟨c, hVS hc⟩ : ↥S) ∈ N₀ := ⟨hVS hc, Subgroup.le_normalizer hc⟩
  have := (Subgroup.mem_normalizer_iff.mp hsN _).mp hcN₀
  exact this.2

theorem exists_conjSubgroup_eq : ∃ x ∈ tiX V A, conjSubgroup A x⁻¹ = V := by
  have hb := h.toBase
  obtain ⟨S, hS, hVS⟩ := A4.exists_isSylowTwoOf_ge (le_sup_left : V ≤ tiX V A)
    (B2F.isPGroup_of_isElemAbelian hb.hV)
  have hSN := h.le_normalizer_of_le hS.1 hS.2.1 hVS
  obtain ⟨x, hx, hxA⟩ := exists_conj_le_of_isSylowTwoOf hS (le_sup_right : A ≤ tiX V A)
    (B2F.isPGroup_of_isElemAbelian hb.hA)
  obtain ⟨a, ha, haB⟩ := h.exists_mem_not_mem'
  have hxa : x * a * x⁻¹ ∈ cjSub x A := by
    rw [mem_cjSub, show x⁻¹ * (x * a * x⁻¹) * x = a by group]
    exact ha
  exact ⟨x, hx, (h.eq_conjSubgroup_of_conj_mem hx ha haB (hSN (hxA hxa))).symm⟩

theorem conjSubgroup_eq_of_le_centralizer {x t : G} (hx : x ∈ tiX V A) (ht : t ∈ V)
    (ht1 : t ≠ 1) (hle : conjSubgroup V x ≤ Subgroup.centralizer ({t} : Set G)) :
    conjSubgroup V x = V := by
  have hb := h.toBase
  obtain ⟨c, hc, hcU⟩ := h.exists_mem_not_mem
  rw [conjSubgroup_eq_iff_mem_normalizer]
  have hx' : x⁻¹ ∈ tiX V A := (tiX V A).inv_mem hx
  have hmem : x⁻¹ * c * x⁻¹⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    have hcx : x⁻¹ * c * x ∈ conjSubgroup V x :=
      mem_conjSubgroup_iff.mpr (by rw [show x * (x⁻¹ * c * x) * x⁻¹ = c by group]; exact hc)
    have := hle hcx
    rw [inv_inv]
    exact hb.mem_normalizer_of_comm ht ht1 (Subgroup.mem_centralizer_singleton_iff.mp this)
  have := h.mem_normalizer_of_conj_mem hx' hc hcU hmem
  have := (Subgroup.normalizer (V : Set G)).inv_mem this
  rwa [inv_inv] at this

end Hyp

end CFSG.Quasithin.I62

end
