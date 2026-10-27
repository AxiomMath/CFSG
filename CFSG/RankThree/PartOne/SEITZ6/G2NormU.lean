module

public import CFSG.RankThree.PartOne.SEITZ6.G2BrN

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.LieType.RootSystem CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

variable {K : Type} [Field K]

theorem mem_borel_iff {b : adjointGroup .G2 K} :
    b ∈ borel (g2Datum K) (torus (τ := .G2) K) ↔
      ∃ t0 ∈ Tg K, ∃ u0 ∈ Ug K, b = t0 * u0 := by
  constructor
  · intro hb
    have hb' : b ∈ (borel (g2Datum K) (torus (τ := .G2) K) : Set (adjointGroup .G2 K)) := hb
    rw [coe_borel (g2_isCTGroupDatum K), Set.mem_mul] at hb'
    obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
    exact ⟨t0, ht0, u0, (posUnipotent_eq_Ug (K := K)).le hu0, rfl⟩
  · rintro ⟨t0, ht0, u0, hu0, rfl⟩
    exact mul_mem (iSup_le_borel ht0) (posUnipotent_le_borel ((posUnipotent_eq_Ug (K := K)).ge hu0))

theorem mem_borel_of_conj_mem_Up {b x : adjointGroup .G2 K}
    (hb : b ∈ borel (g2Datum K) (torus (τ := .G2) K)) (h : b * x * b⁻¹ ∈ Up K) :
    x ∈ borel (g2Datum K) (torus (τ := .G2) K) := by
  have h1 : b * x * b⁻¹ ∈ borel (g2Datum K) (torus (τ := .G2) K) :=
    posUnipotent_le_borel ((posUnipotent_eq_Ug (K := K)).ge (Up_le_Ug h))
  have := mul_mem (mul_mem (inv_mem hb) h1) hb
  rwa [show b⁻¹ * (b * x * b⁻¹) * b = x by group] at this

theorem reflect_1_5 : reflect .G2 e1 (rt 1) = rt 5 := by decide +kernel

theorem normalizer_Up_borel [CharP K 2] {g : adjointGroup .G2 K}
    (hg : ∀ x ∈ Up K, g * x * g⁻¹ ∈ Up K) :
    g ∈ borel (g2Datum K) (torus (τ := .G2) K) := by
  have h7 : g * xp 7 1 * g⁻¹ ∈ Up K := hg _ (mem_Up_iff.2 ⟨1, 0, by simp [xp_zero]⟩)
  rcases bruhat_stab_h one_ne_zero h7 with h | ⟨b, hb, a, rfl⟩
  · exact h
  · exfalso
    have h1 := hg (xp 1 1) (mem_Up_iff.2 ⟨0, 1, by simp [xp_zero]⟩)
    have hc : xp 1 a * xp 1 (1 : K) = xp 1 1 * xp 1 a := by
      rw [← xp_add, ← xp_add, add_comm]
    have h2 : (b * weylElement .G2 K e1 * xp 1 a) * xp 1 1 *
        (b * weylElement .G2 K e1 * xp 1 a)⁻¹ = b * xp 5 1 * b⁻¹ := by
      rw [show (b * weylElement .G2 K e1 * xp 1 a) * xp 1 1 *
          (b * weylElement .G2 K e1 * xp 1 a)⁻¹ =
          b * (weylElement .G2 K e1 * (xp 1 a * xp 1 1 * (xp 1 a)⁻¹) *
            (weylElement .G2 K e1)⁻¹) * b⁻¹ by group, hc,
        show xp 1 1 * xp 1 a * (xp 1 a)⁻¹ = xp 1 (1 : K) by group,
        weylElement_conj_xp e1 (by norm_num) reflect_1_5]
    rw [h2] at h1
    have hB := mem_borel_of_conj_mem_Up hb h1
    exact one_ne_zero (neg_root_not_mem_borel (by norm_num) (by decide +kernel) hB)

theorem exists_ne_zero_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
    by_cases h0 : x = 0
    · simp [h0]
    · simp [h x h0]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem normalizer_Up_form [CharP K 2] [Finite K] (hK : 4 ≤ Nat.card K) {g : adjointGroup .G2 K}
    (hg : ∀ x ∈ Up K, g * x * g⁻¹ ∈ Up K) :
    ∃ t0 ∈ Tg K, ∃ a b c : K, g = t0 * (xp 1 a * xp 3 b * xp 7 c) := by
  obtain ⟨t0, ht0, u0, hu0, rfl⟩ := mem_borel_iff.1 (normalizer_Up_borel hg)
  have hu0n : ∀ x ∈ Up K, u0 * x * u0⁻¹ ∈ Up K := by
    intro x hx
    have h := hg x hx
    have h' : t0 * (u0 * x * u0⁻¹) * t0⁻¹ ∈ Up K := by
      rwa [show t0 * (u0 * x * u0⁻¹) * t0⁻¹ = t0 * u0 * x * (t0 * u0)⁻¹ by group]
    exact (Tg_conj_Up_iff ht0).2 h'
  obtain ⟨c, rfl⟩ := exists_ordProd hu0
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_one hK
  have h1 := hu0n (xp 1 1) (mem_Up_iff.2 ⟨0, 1, by simp [xp_zero]⟩)
  have hs := hu0n (xp 1 s) (mem_Up_iff.2 ⟨0, s, by simp [xp_zero]⟩)
  obtain ⟨c0, c4, c8⟩ := coords_of_conj_x1 c hs0 hs1 h1 hs
  refine ⟨t0, ht0, c 1, c 3, c 7, ?_⟩
  unfold ordProd
  rw [c0, c4, c8, xp_zero, xp_zero, xp_zero]
  simp [mul_assoc]

theorem comm_xp_10_3 [CharP K 2] (s t : K) : ⁅xp 10 s, xp 3 t⁆ = xp 2 (s * t) := by
  have h : RootOps.repCheck .G2 10 3 [(1, 1, 2, -1)] = true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h s t
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_neg_one_eq, one_mul, pow_one] at this
  exact this

theorem eq_top_of_xp3 [CharP K 2] [Finite K] {H : Subgroup (adjointGroup .G2 K)}
    (hL : Lp K ≤ H) {b : K} (hb : b ≠ 0) (h3 : xp 3 b ∈ H) : H = ⊤ := by
  have hF3 : Full H 3 := by
    intro c
    by_cases hc : c = 0
    · rw [hc, xp_zero]
      exact H.one_mem
    · set s : Kˣ := Units.mk0 (b / c) (div_ne_zero hb hc) with hs
      have hsT : torusElement .G2 K e0 s ∈ H :=
        hL (Tg_le_Lp (Subgroup.mem_iSup_of_mem e0 (mem_torus.2 ⟨s, rfl⟩)))
      have h4 := H.mul_mem (H.mul_mem hsT h3) (H.inv_mem hsT)
      rw [torusElement_conj_xp e0 (by norm_num)] at h4
      have hex : (∑ j, (Tag.G2).cartan e0 j * (rt 3) j) = -1 := by decide +kernel
      rw [hex] at h4
      have e : (((s ^ (-1 : ℤ) : Kˣ) : K) * b) = c := by
        simp only [zpow_neg, zpow_one, Units.val_inv_eq_inv_val, hs, Units.val_mk0]
        field_simp
      rwa [e] at h4
  have hw1 : weylElement .G2 K e1 ∈ H := by
    rw [weylElement_e1_eq]
    exact H.mul_mem (H.mul_mem (hL (xp1_mem_Lp _)) (hL (xp5_mem_Lp _))) (hL (xp1_mem_Lp _))
  have hF0 : Full H 0 := hF3.conj e1 (by norm_num) reflect_3 hw1
  have hF2 : Full H 2 := fun c => by
    have h10 : xp 10 (1 : K) ∈ H := hL (xp10_mem_Lp 1)
    have h5 : ⁅xp 10 (1 : K), xp 3 c⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h10 (hF3 c)) (H.inv_mem h10)) (H.inv_mem (hF3 c))
    rwa [comm_xp_10_3, one_mul] at h5
  exact eq_top_of_full hF0 (fun c => hL (xp1_mem_Lp c)) hF2 (fun c => hL (xp5_mem_Lp c))

end CFSG.RankThree.PartOne.SEITZ6
