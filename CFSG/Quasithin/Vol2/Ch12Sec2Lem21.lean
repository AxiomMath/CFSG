module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem21Stmts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem21

variable {G : Type} [Group G]

theorem eq_or_le_of_relIndex_eq_two {A B V : Subgroup G} (hAB : A ≤ B) (hBV : B ≤ V)
    (hA : A.relIndex V = 2) : B = A ∨ V ≤ B := by
  have h := Subgroup.relIndex_mul_relIndex A B V hAB hBV
  rw [hA] at h
  rcases Nat.prime_mul_iff.mp (h ▸ Nat.prime_two) with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact Or.inr (Subgroup.relIndex_eq_one.mp h1)
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAB)

theorem eq_zpowers_of_card_eq_prime [Finite G] {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hP : Nat.card P = p) {h : G} (hh : h ∈ P) (h1 : h ≠ 1) :
    P = Subgroup.zpowers h ∧ orderOf h = p := by
  have hdvd : orderOf h ∣ p := hP ▸ Subgroup.orderOf_dvd_natCard P hh
  have hord : orderOf h = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left fun h' => h1 (orderOf_eq_one_iff.mp h')
  refine ⟨(Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hh) ?_).symm, hord⟩
  rw [hP, Nat.card_zpowers, hord]

theorem not_le_pCoreOf_of_pre [Finite G] {T L V H P U I : Subgroup G} {h : G} {p : ℕ}
    (hpre : Pre12_2_21 T L V H P U I h p) : ¬ V ≤ pCoreOf 2 H := by
  obtain ⟨-, -, hp, hp2, -, hPH, -, -, -, hhP, -, hI, -, -, -, -, -, ⟨hN, ⟨e⟩⟩, -⟩ := hpre
  intro hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hhN : h⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem (hPH hhP))
  have hVh : CFSG.conjugate V h ≤ pCoreOf 2 H := by
    rintro _ ⟨y, hy, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hhN y).mp (hV hy)
    simpa using this
  have h2 : IsPGroup 2 ↥I :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le (by rw [hI]; exact sup_le hV hVh)
  have hq : IsPGroup 2 (↥I ⧸ U.subgroupOf I) := h2.to_quotient _
  obtain ⟨k, hk⟩ := (hq.of_equiv e) (DihedralGroup.r 1)
  have hdvd : p ∣ 2 ^ k := DihedralGroup.orderOf_r_one (n := p) ▸ orderOf_dvd_of_pow_eq_one hk
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

end Lem21

open Lem21

theorem lem12220Pick_of_full (hpick : Lem12220PickFull) : Lem12220Pick := by
  intro G _ _ T L V H hyp hNE hH hsol
  obtain ⟨P, U, I, h, p, hpre⟩ := hpick G T L V H hyp hNE hH hsol
  obtain ⟨-, -, -, -, -, hPH, -, -, -, hhP, hhM, rfl, rfl, -, -, -, -, -, hidx, hcomm, htr⟩ :=
    hpre
  exact ⟨h, hPH hhP, hhM, hidx, hcomm, htr⟩

theorem lem12221_23_of (hpick : Lem12220PickFull) (h21 : Lem12221) (h22 : Lem12222)
    (h23 : Lem12223) (hpost : Lem12223Post) : Lem12221_23 := by
  intro G _ _ T L V H hyp hNE hH hsol n hn hV hLV hnat hTL
  have hC : Concl12_2_20 T L V n := ⟨hn, hV, hLV, hnat, hTL⟩
  obtain ⟨P₀, U₀, I₀, h₀, p, hpre₀⟩ := hpick G T L V H hyp hNE hH hsol
  have hU₀ := h21 G T L V H P₀ U₀ I₀ h₀ n p hyp hNE hC hpre₀
  obtain ⟨P, U, I, W, h, v, hpre, hU, hdata⟩ :=
    h22 G T L V H P₀ U₀ I₀ h₀ n p hyp hNE hC hpre₀ hU₀
  have hcard := h23 G T L V H P U I W h v n p hyp hNE hC hpre hU hdata
  have hVO := not_le_pCoreOf_of_pre hpre
  obtain ⟨hUW, hHU, hHI, hIPUV, hHIT, hUCP, hQU⟩ :=
    hpost G T L V H P U I W h v n p hyp hNE hC hpre hU hdata hcard
  obtain ⟨hH', hsol', hp, hp2, -, hPH, -, -, -, hhP, hhM, hI, hUI, hUs, hUd, hUe, -, hq, hidx,
    hcomm, htr⟩ := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, hO2, -, -⟩ := hdata
  have h1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  obtain ⟨hPz, hord⟩ := eq_zpowers_of_card_eq_prime hp hcard hhP h1
  have hUV : U ⊓ V = pCoreOf 2 H ⊓ V :=
    ((eq_or_le_of_relIndex_eq_two (inf_le_inf_right V hU) inf_le_right hidx).resolve_right
      fun hle => hVO (hle.trans inf_le_left)).symm
  have hIM : ¬ I ≤ Subgroup.normalizer (L : Set G) := fun hIM =>
    hhM (hIM (hIPUV ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left hhP)))
  refine ⟨P, U, I, h, p, hH', hsol', hn, hV, hTL, hLV, hnat, hp, hp2, hPz, hord, hPH hhP, hhM, hI,
    hUI, hUs, hUd, hUe, hq, hUCP, hidx, ⟨hcomm, htr⟩, hU, hUV, ?_, hHU, hHI, hIPUV, hHIT, hIM,
    hQU⟩
  rw [hO2, hUW]

end CFSG.Quasithin.H13
