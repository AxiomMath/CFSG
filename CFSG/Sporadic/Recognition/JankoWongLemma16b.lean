module

public import CFSG.Sporadic.Recognition.JankoWongLemma16

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

structure IsW (W : Subgroup G) : Prop where
  isPGroup : IsPGroup 3 W
  card : Nat.card W = 3 ^ 6
  OG_le : c.OG ≤ W
  le_NG : W ≤ c.NG
  comm_a : ∀ w ∈ W, w * (c.a : G) = (c.a : G) * w
  le_card : ∀ R : Subgroup G, R ≤ c.NG → IsPGroup 3 R → Nat.card R ≤ 3 ^ 6

theorem exists_isW
    : ∃ W : Subgroup G, c.IsW W := by
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := c.exists_sylow_three_NG
  exact ⟨W, ⟨h1, h2, h3, h4, h5, h6⟩⟩

theorem aG_mem_OG
    : (c.a : G) ∈ c.OG := c.PG_le_OG c.card_OG_eq_81 c.a_mem_PG

@[expose] def centerW (W : Subgroup G) : Subgroup G := W ⊓ centralizer (W : Set G)

omit [Finite G] in
theorem mem_centerW {W : Subgroup G} {y : G} :
    y ∈ centerW W ↔ y ∈ W ∧ ∀ w ∈ W, w * y = y * w := by
  unfold centerW
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

variable {c}

theorem IsW.centerW_le_OG
    {W : Subgroup G} (hW : c.IsW W) : centerW W ≤ c.OG := by
  intro y hy
  obtain ⟨-, hyc⟩ := mem_centerW.mp hy
  exact c.centralizer_OG_le y (fun n hn => hyc n (hW.OG_le hn))

theorem IsW.aG_mem_centerW
    {W : Subgroup G} (hW : c.IsW W) : (c.a : G) ∈ centerW W :=
  mem_centerW.mpr ⟨hW.OG_le c.aG_mem_OG, hW.comm_a⟩

theorem IsW.exists_not_mem_OG
    {W : Subgroup G} (hW : c.IsW W) : ∃ w ∈ W, w ∉ c.OG := by
  by_contra hall
  push Not at hall
  have hle : W ≤ c.OG := hall
  have := Subgroup.card_le_of_le hle
  rw [hW.card, c.card_OG_eq_81] at this
  norm_num at this

theorem IsW.card_centerW_le_nine
    {W : Subgroup G} (hW : c.IsW W) : Nat.card (centerW W) ≤ 9 := by
  obtain ⟨w, hwW, hwN⟩ := hW.exists_not_mem_OG
  have h3 : ∃ n : ℕ, w ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hW.isPGroup ⟨w, hwW⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have h9 := c.card_centralizer_le_nine h3 hwN
  have hle : centerW W ≤ c.OG ⊓ centralizer ({w} : Set G) := fun y hy =>
    ⟨hW.centerW_le_OG hy, Subgroup.mem_centralizer_singleton_iff.mpr
      ((mem_centerW.mp hy).2 w hwW).symm⟩
  exact (Subgroup.card_le_of_le hle).trans h9

theorem IsW.exists_conj_a_of_mem_centerW
    {W : Subgroup G} (hW : c.IsW W) {x : G} (hx : x ∈ centerW W) (hx1 : x ≠ 1) :
    ∃ g ∈ c.NG, x = g * (c.a : G) * g⁻¹ := by
  have hxO : x ∈ (c.OG : Set G) \ {1} := ⟨hW.centerW_le_OG hx, hx1⟩
  rw [c.OG_sdiff_one_eq] at hxO
  rcases hxO with hs | ha
  · exfalso
    obtain ⟨g, hg, rfl⟩ := hs
    have hn1 : ∀ y ∈ c.NG, g * y * g⁻¹ ∈ c.NG := fun y hy =>
      c.NG.mul_mem (c.NG.mul_mem hg hy) (c.NG.inv_mem hg)
    have hn2 : ∀ y ∈ c.NG, g⁻¹ * y * g ∈ c.NG := fun y hy =>
      c.NG.mul_mem (c.NG.mul_mem (c.NG.inv_mem hg) hy) hg
    have hcard := card_inf_centralizer_conj_of_normalizes (A := c.NG) (g := g) hn1 hn2 c.s
    rw [c.NG_inf_centralizer_s] at hcard
    obtain ⟨-, hCg, -, -⟩ := c.lemma14
    have hWle : W ≤ c.NG ⊓ centralizer ({g * c.s * g⁻¹} : Set G) := fun w hw =>
      ⟨hW.le_NG hw, Subgroup.mem_centralizer_singleton_iff.mpr ((mem_centerW.mp hx).2 w hw)⟩
    have hdvd := Subgroup.card_dvd_of_le hWle
    rw [hW.card, hcard, hCg] at hdvd
    norm_num at hdvd
  · exact ha

variable (c)

theorem false_of_involution_centralizes {q : G} (hq2 : q ^ 2 = 1) (hq1 : q ≠ 1)
    {Z : Subgroup G} (hZ : Nat.card Z = 9) (hZq : ∀ y ∈ Z, y * q = q * y)
    (hZa : ∀ y ∈ Z, y ≠ 1 → IsConj (c.a : G) y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := isConj_iff.mp (S.oneClass S.z q S.order_z (orderOf_eq_prime hq2 hq1))
  have hmemH : ∀ y ∈ Z, k⁻¹ * y * k ∈ S.H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k⁻¹ * y * k * S.z = k⁻¹ * y * (k * S.z * k⁻¹) * k := by group
      _ = k⁻¹ * (y * q) * k := by rw [hk]; group
      _ = k⁻¹ * (q * y) * k := by rw [hZq y hy]
      _ = S.z * (k⁻¹ * y * k) := by rw [← hk]; group
  have hconj : ∀ y : G, (MulAut.conj k⁻¹).toMonoidHom y = k⁻¹ * y * k := by
    intro y; simp
  let Y' : Subgroup G := Z.map (MulAut.conj k⁻¹).toMonoidHom
  have hY'H : Y' ≤ S.H := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hconj]; exact hmemH y hy
  have hY'mem : ∀ x : G, x ∈ Y' ↔ ∃ y ∈ Z, k⁻¹ * y * k = x := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hconj y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hconj y⟩
  have hY'card : Nat.card Y' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hZ]
  let YH : Subgroup S.H := Y'.subgroupOf S.H
  have hYHcard : Nat.card YH = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY'H).toEquiv, hY'card]
  have hH3 : 3 ^ (Nat.card S.H).factorization 3 = 9 := by
    rw [S.card_H, factorization_three_40320]; norm_num
  let YS : Sylow 3 S.H := Sylow.ofCard YH (by rw [hYHcard, hH3])
  let PS : Sylow 3 S.H := Sylow.ofCard c.P (by rw [c.hP9, hH3])
  obtain ⟨h, hh⟩ := sylow_conj_mem PS YS
  simp only [YS, PS, Sylow.coe_ofCard] at hh
  have hxP : c.x ∈ c.P := c.P.mul_mem c.haP c.hbP
  have h1 : h * c.x * h⁻¹ ∈ YH := (hh (h * c.x * h⁻¹)).mpr (by
    have : h⁻¹ * (h * c.x * h⁻¹) * h = c.x := by group
    rw [this]; exact hxP)
  have h2 : ((h * c.x * h⁻¹ : S.H) : G) ∈ Y' := Subgroup.mem_subgroupOf.mp h1
  obtain ⟨y, hyZ, hye⟩ := (hY'mem _).mp h2
  have e : ((h * c.x * h⁻¹ : S.H) : G) = (h : G) * (c.x : G) * (h : G)⁻¹ := by simp
  rw [e] at hye
  have hy : y = k * ((h : G) * (c.x : G) * (h : G)⁻¹) * k⁻¹ := by
    rw [← hye]; group
  have hy1 : y ≠ 1 := by
    intro hy1
    rw [hy1] at hye
    have h3 : (h : G) * (c.x : G) * (h : G)⁻¹ = 1 := by
      rw [← hye]; group
    have h4 : (c.x : G) = 1 := by
      calc (c.x : G) = (h : G)⁻¹ * ((h : G) * (c.x : G) * (h : G)⁻¹) * (h : G) := by group
        _ = 1 := by rw [h3]; group
    exact c.x_ne_one (Subtype.ext h4)
  obtain ⟨m, hm⟩ := isConj_iff.mp (hZa y hyZ hy1)
  refine S.not_isConj_type3_type33 c.ha3 c.x_cube c.cycleType_a c.x_type
    (isConj_iff.mpr ⟨(k * (h : G))⁻¹ * m, ?_⟩)
  calc (k * (h : G))⁻¹ * m * (c.a : G) * ((k * (h : G))⁻¹ * m)⁻¹
      = (k * (h : G))⁻¹ * (m * (c.a : G) * m⁻¹) * (k * (h : G)) := by group
    _ = (k * (h : G))⁻¹ * y * (k * (h : G)) := by rw [hm]
    _ = (c.x : G) := by rw [hy]; group

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
