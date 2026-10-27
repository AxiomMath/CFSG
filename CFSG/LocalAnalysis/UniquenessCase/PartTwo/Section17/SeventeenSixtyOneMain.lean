module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOne
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem exists_order_seven_of_isL2_or_isSz
    {K : Subgroup G}
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) :
    ∃ X : Subgroup G, X ≤ K ∧ Nat.card X = 7 := by
  refine s13_exists_subgroup_of_dvd_card_bar (L := K) (r := 7) (by norm_num) ?_
  rcases hshape with h | h
  · rw [card_of_isL2 h]
    norm_num
  · rw [show Nat.card (Bar2 K) = CFSG.Open.ordSuzuki 8 from
      CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki]
    norm_num

theorem conjSetOf_ne_of_order_seven {D : Data G} {V₀ V : Subgroup G}
    (h55 : R17_55At D V₀ V) {K X : Subgroup G} (hKM : K ≤ D.M)
    (hKn : (K.subgroupOf D.M).Normal)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) (hXK : X ≤ K)
    (hXcard : Nat.card X = 7) :
    conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M} ≠ conjSetOf D.M X :=
  h55 K hKM hKn 3 hshape 3 (by norm_num) dvd_rfl 7 (by norm_num)
    (by norm_num : (7 : ℕ) ∣ 2 ^ 3 - 1) X hXK hXcard

theorem exists_conj_order_seven
    {D : Data G} {V₀ V : Subgroup G}
    (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V) {K : Subgroup G}
    (hKcalM : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) (hKthin : F08.Thin8 K)
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) :
    ∃ (X Y : Subgroup G) (g : G), X ≤ K ∧ Nat.card X = 7 ∧
      g ∉ D.M ∧ Y = X.map (MulAut.conj g).toMonoidHom ∧ Y ≤ D.M ∧
      Y ∉ conjSetOf D.M X ∧ Nat.card Y = 7 ∧
      Subgroup.centralizer (X : Set G) ≤ D.M := by
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  obtain ⟨X, hXK, hXcard⟩ := exists_order_seven_of_isL2_or_isSz hshape
  have hXM : X ≤ D.M := hXK.trans hKM
  have hne := conjSetOf_ne_of_order_seven (D := D) (V₀ := V₀) (V := V)
    h55 hKM hKn hshape hXK hXcard
  obtain ⟨g, hgM, hYle, hYnot⟩ := exists_conj_of_conjSetOf_ne hXM hne
  refine ⟨X, X.map (MulAut.conj g).toMonoidHom, g, hXK, hXcard, hgM, rfl, hYle, hYnot,
    ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
  · exact (Subgroup.centralizer_le_normalizer (X : Set G)).trans
      (h3 K hKcalM hKthin X ⟨7, by norm_num, by norm_num, hXcard, hXK⟩)


theorem false_of_conj_order_seven_of_normalizer {D : Data G} (P : Sylow 7 G)
    {X Y : Subgroup G} {g : G}
    (hXR : X ≤ (P : Subgroup G)) (hYR : Y ≤ (P : Subgroup G)) (hXcard : Nat.card X = 7)
    (hYeq : Y = X.map (MulAut.conj g).toMonoidHom)
    (hPcard : Nat.card (P : Subgroup G) = 49)
    (hNP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ D.M)
    (hCX : Subgroup.centralizer (X : Set G) ≤ D.M) (hgM : g ∉ D.M) : False := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : X = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      exact hy1 (h y hy)
    rw [hbot, Subgroup.card_bot] at hXcard
    norm_num at hXcard
  have hxord : orderOf x = 7 := by
    have h1 : orderOf (⟨x, hxX⟩ : ↥X) ∣ Nat.card ↥X := orderOf_dvd_natCard _
    have h2 : orderOf x ∣ 7 := by
      simpa [hXcard] using h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h2 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hx1
    · exact h2
  have hXz : X = Subgroup.zpowers x := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers x) (K := X)
      (Subgroup.zpowers_le.mpr hxX) ?_).symm
    rw [hXcard, Nat.card_zpowers, hxord]
  have hgxY : g * x * g⁻¹ ∈ Y := by
    rw [hYeq]
    exact Subgroup.mem_map.mpr ⟨x, hxX, by simp [MulAut.conj_apply]⟩
  have hgxP : g * x * g⁻¹ ∈ (P : Subgroup G) := hYR hgxY
  have hAbelP : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := by
    intro a ha b hb
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) hPcard).is_comm.comm
      (⟨a, ha⟩ : ↥(P : Subgroup G)) (⟨b, hb⟩ : ↥(P : Subgroup G))
    simpa using congrArg Subtype.val h
  have hweak : ∀ c : G,
      CFSG.conjugate (P : Subgroup G) c ≤ (P : Subgroup G) →
        CFSG.conjugate (P : Subgroup G) c = (P : Subgroup G) := by
    intro c hle
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hc : Nat.card ↥(CFSG.conjugate (P : Subgroup G) c) = Nat.card ↥(P : Subgroup G) := by
      rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact le_of_eq hc.symm
  have hxP : x ∈ (P : Subgroup G) := hXR hxX
  obtain ⟨n, hnN, hnconj⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion
    (p := 7) P (P : Subgroup G) le_rfl hAbelP hweak hxP hgxP
  have hmemC : n⁻¹ * g ∈ Subgroup.centralizer (X : Set G) := by
    rw [hXz, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    set a : G := n⁻¹ * g with ha
    have hconj : a * x * a⁻¹ = x := by
      have h := hnconj
      calc a * x * a⁻¹ = n⁻¹ * (g * x * g⁻¹) * n := by
            simp only [ha]; group
        _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [← h]
        _ = x := by group
    have hfix : (MulAut.conj a).toMonoidHom x = x := hconj
    have hzpow : a * x ^ k * a⁻¹ = x ^ k := by
      have h := map_zpow (MulAut.conj a).toMonoidHom x k
      rw [hfix] at h
      simpa [MulAut.conj_apply] using h
    have h2 : a⁻¹ * x ^ k * a = x ^ k := by
      have h := congrArg (fun t : G => a⁻¹ * t * a) hzpow
      simpa [mul_assoc] using h.symm
    have hcomm : x ^ k * a = a * x ^ k := by
      calc x ^ k * a = a * (a⁻¹ * x ^ k * a) := by group
        _ = a * x ^ k := by rw [h2]
    exact hcomm
  have hngM : n⁻¹ * g ∈ D.M := hCX hmemC
  have hnM : n ∈ D.M := hNP hnN
  exact hgM (by
    have hg : g = n * (n⁻¹ * g) := by group
    rw [hg]
    exact D.M.mul_mem hnM hngM)


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
