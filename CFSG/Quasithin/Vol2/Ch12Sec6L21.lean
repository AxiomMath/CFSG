module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.Quasithin.Vol2.Ch12Sec6L20

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19b S126L19d S126L20 Equiv
open scoped IsMulCommutative

namespace S126L21

theorem card_of_lieModel_psl52 {Y : Type} [Group Y] (h : LieModel Y .PSL 5 2 1) :
    Nat.card Y = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two (h.statedClassicalModel (by decide))

theorem card_SL3 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [Nat.card_congr (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).toEquiv,
    Matrix.card_GL_field, ZMod.card]
  decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem V_le_L (hH : Hyp126 G T L V) (hVT : V ≤ T) : V ≤ L := by
  have hVL : ⁅V, L⁆ = V := hH.hyp.irrPlus.2.2.2.1
  rw [← hVL, Subgroup.commutator_le]
  intro x hx l hl
  have hxN := hH.hyp.normalizes (hVT hx)
  have h1 : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hxN l).1 hl
  exact L.mul_mem h1 (L.inv_mem hl)

theorem two_pow_dvd_card (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    2 ^ 12 ∣ Nat.card L := by
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hVL := V_le_L hH (facts h1222 hH).1
  have h1 : Nat.card L = Nat.card (alternatingGroup (Fin 8)) * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  have h2 : Nat.card V ∣ Nat.card φ.ker := by
    rw [hker]
    have hle : V.subgroupOf L ≤ (Subgroup.centralizer (V : Set G)).subgroupOf L := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := mul_comm (⟨y, hy⟩ : ↥V) ⟨x, hx⟩
      exact congrArg Subtype.val this
    have h3 := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv] at h3
  have h3 : 64 ∣ Nat.card V := by
    rw [card_V F]
    exact dvd_mul_right 64 _
  obtain ⟨a, ha⟩ := h3
  obtain ⟨b, hb⟩ := h2
  rw [h1, card_A8, hb, ha]
  exact ⟨315 * a * b, by ring⟩

omit [IsMulCommutative ↥V] in
theorem card_A8_dvd (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    20160 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_reduced hyp.normalizes hVT hred
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hle : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hO2
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by
      exact hx
    exact ⟨x, hx', rfl⟩
  rw [← card_A8]
  exact Subgroup.card_dvd_of_surjective (f := QuotientGroup.lift _ φ hle)
    (QuotientGroup.lift_surjective_of_surjective _ _ hφ _)

theorem exists_conj_wt4 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {u w : G} (hu : F.Wt4 u) (hw : F.Wt4 w) : ∃ l ∈ L, l * u * l⁻¹ = w := by
  obtain ⟨huV, hu4⟩ := hu
  obtain ⟨hwV, hw4⟩ := hw
  by_cases hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · have hu1 : F.β ⟨u, huV⟩ ≠ 1 := fun h => not_hasWt4_one (h ▸ hu4)
    have hw1 : F.β ⟨w, hwV⟩ ≠ 1 := fun h => not_hasWt4_one (h ▸ hw4)
    have hiff : IsNonsing (F.β ⟨u, huV⟩) ↔ IsNonsing (F.β ⟨w, hwV⟩) :=
      iff_of_false (fun h => not_nonsing_and_wt4 h hu4) (fun h => not_nonsing_and_wt4 h hw4)
    obtain ⟨l, hlL, hl, hlw⟩ := (part1 F _ _ hu1 hw1).2 hiff
    exact ⟨l, hlL, congrArg Subtype.val (beta_inj F hZ hlw)⟩
  · obtain ⟨E⟩ := exists_frame126E h1222 F hH hZ
    have h : ew E ⟨u, huV⟩ = ew E ⟨w, hwV⟩ := by rw [ew_of_wt4 E hu4, ew_of_wt4 E hw4]
    exact exists_L_conj E h

omit [Finite G] [IsMulCommutative ↥V] in
theorem centralizer_conj_le {M : Subgroup G} {l v : G} (hl : l ∈ M)
    (h : Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (M : Set G)) :
    Subgroup.centralizer ({l * v * l⁻¹} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  intro c hc
  have h1 : l⁻¹ * c * l ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    calc l⁻¹ * c * l * v = l⁻¹ * (c * (l * v * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * v * l⁻¹) * c) * l := by rw [hc]
      _ = v * (l⁻¹ * c * l) := by group
  have h2 := h h1
  have hlN : l ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hl
  have h3 := Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN h2) (Subgroup.inv_mem _ hlN)
  rwa [show l * (l⁻¹ * c * l) * l⁻¹ = c by group] at h3

theorem centralizer_le_of_not_wt4' (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G} (hxV : x ∈ V)
    (hx1 : x ≠ 1) (hx4 : ¬ F.Wt4 x) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  by_cases hβ : F.β ⟨x, hxV⟩ = 1
  · have hxL : x ∈ Subgroup.centralizer (L : Set G) := (F.β_ker _).1 hβ
    have hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := fun h => hx1 (by
      have hm : x ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hxV, hxL⟩
      rw [h] at hm
      exact hm)
    have hxT : x ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
      rw [← (part2 h1222 hH hZ).2]
      exact ⟨hxV, hxL⟩
    exact centralizer_le_M h331 hH hx1 ((facts h1222 hH).1 hxV) hxL hxT.2
  · rcases cases_of_ne_one hβ with hn | h4
    · exact h1262 G T L V F hH x ⟨hxV, hn⟩
    · exact absurd ⟨hxV, h4⟩ hx4

end S126L21

theorem lemma12_6_21_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (h1213 : Stmt12_2_13) : Lemma12_6_21 := by
  intro G _ _ T L V _ F hH v hv1 hv4 hC
  have hyp := hH.hyp
  have hall : ∀ w ∈ V, w ≠ 1 →
      Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro w hwV hw1
    by_cases h4 : F.Wt4 w
    · obtain ⟨l, hlL, hl⟩ := S126L21.exists_conj_wt4 h1222 F hH hv4 h4
      rw [← hl]
      exact S126L21.centralizer_conj_le hlL hC
    · exact S126L21.centralizer_le_of_not_wt4' h331 h1222 h1262 F hH hwV hw1 h4
  have hdvdL := S126L21.two_pow_dvd_card h1222 F hH
  have hLG : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
  have hA8 := S126L21.card_A8_dvd h1222 hH
  rcases h1213 G T L V hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.notAlt hyp.maximal
      hyp.faithful hyp.quasisimple hyp.normalizes hyp.irrPlus with
    ⟨w, hwV, hw1, hw⟩ | ⟨n, hn, ⟨e⟩, hLie⟩ | ⟨⟨e⟩, -⟩ | ⟨-, ⟨e⟩⟩
  · exact hw (hall w hwV hw1)
  · rcases hn with rfl | rfl
    · rw [Nat.card_congr e.toEquiv, S126L21.card_SL3] at hA8
      exact absurd hA8 (by decide)
    · rw [S126L21.card_of_lieModel_psl52 hLie] at hLG
      exact absurd (hdvdL.trans hLG) (by decide)
  · rw [Nat.card_congr e.toEquiv, S126L21.card_SL3] at hA8
    exact absurd hA8 (by decide)
  · rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24] at hLG
    exact absurd (hdvdL.trans hLG) (by decide)

end CFSG.Quasithin.H13
