module

public import CFSG.RankThree.GF2n.Parrott.Section4Lemma41
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
import all CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.GroupTheory.CentralizerSylowFusion
public import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conj_z_eq_of_mem_H {y : G} (hy : y ∈ H z) : y * z * y⁻¹ = z := by
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hy
  rw [hy, mul_inv_cancel_right]

private theorem centerIn_H_le_centerIn_J (h : Tim79a.ParrottHyp z) :
    centerIn (H z) ≤ centerIn (J z) := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (J z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp hx.2 y (J_le_H hy)
  rw [← centralizer_J_eq_centerIn h]
  exact ⟨hx.1, hxC⟩

private theorem exists_mem_H_not_commute_centerIn_J (h : Tim79a.ParrottHyp z)
    (hne : centerIn (J z) ≠ centerIn (H z)) :
    ∃ x ∈ H z, ∃ c ∈ centerIn (J z), x * c ≠ c * x := by
  by_contra hcon
  push Not at hcon
  apply hne
  apply le_antisymm
  · intro c hc
    refine ⟨centerIn_le_H z hc, ?_⟩
    show c ∈ Subgroup.centralizer (H z : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcon x hx c hc
  · exact centerIn_H_le_centerIn_J h

section Fusion


theorem mem_H_of_conj_z_mem_centerIn (h : Tim79a.ParrottHyp z) {g : G}
    (hg : g * z * g⁻¹ ∈ centerIn (J z)) : g ∈ H z := by
  classical
  set C : Subgroup G := Subgroup.centralizer (centerIn (J z) : Set G) with hC
  set Hy : Subgroup G := Subgroup.centralizer ({g * z * g⁻¹} : Set G) with hHy
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hCH : C ≤ H z := by
    rw [hC, H_eq_centralizer]
    exact Subgroup.centralizer_le fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hzZ
  have hCHy : C ≤ Hy := fun c hc => by
    rw [hHy, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc _ hg).symm
  have hCsub : Subgroup.centralizer ((centerIn (J z)).subgroupOf (H z) : Set ↥(H z)) =
      C.subgroupOf (H z) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hx
      intro w hw
      exact congrArg Subtype.val
        (hx ⟨w, centerIn_le_H (z := z) hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) (y : G)
        (Subgroup.mem_subgroupOf.mp hy))
  have hidx : (C.subgroupOf (H z)).index ≤ 2 := by
    rw [← hCsub]
    exact index_centralizer_centerIn_subgroupOf_le_two h
  have hcard : Nat.card Hy = Nat.card (H z) := by
    have := CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj
      (isConj_iff.mpr ⟨g, rfl⟩ : IsConj z (g * z * g⁻¹))
    rw [H_eq_centralizer]
    exact this.symm
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hC1 : Nat.card (C.subgroupOf Hy) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCHy).toEquiv
  have hC2 : Nat.card (C.subgroupOf (H z)) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv
  have hm1 := Subgroup.card_mul_index (C.subgroupOf Hy)
  have hm2 := Subgroup.card_mul_index (C.subgroupOf (H z))
  have e1 : Nat.card C * (C.subgroupOf Hy).index = Nat.card Hy := by
    rw [← hC1]
    exact hm1
  have e2 : Nat.card C * (C.subgroupOf (H z)).index = Nat.card (H z) := by
    rw [← hC2]
    exact hm2
  have hidx' : (C.subgroupOf Hy).index = (C.subgroupOf (H z)).index :=
    Nat.eq_of_mul_eq_mul_left hCpos (e1.trans (hcard.trans e2.symm))
  have hnormal : (C.subgroupOf Hy).Normal := by
    have hne : (C.subgroupOf Hy).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : (C.subgroupOf Hy).index ≤ 2 := hidx'.symm ▸ hidx
    rcases (by omega : (C.subgroupOf Hy).index = 1 ∨ (C.subgroupOf Hy).index = 2) with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have hHyN : Hy ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCHy).mp hnormal
  have hHyH : Hy ≤ H z := by
    intro x hx
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) C (hHyN hx)
    rw [hC, pCore_centralizer_centerIn_eq (z := z) h] at h1
    exact mem_H_of_mem_normalizer_J (z := z) h h1
  have hHyeq : Hy = H z := Subgroup.eq_of_le_of_card_ge hHyH hcard.ge
  have key : ∀ x : G, g * x * g⁻¹ ∈ Hy ↔ x ∈ H z := by
    intro x
    rw [hHy, H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    have e : ∀ a b : G, (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
      intro a b
      group
    rw [e, e, mul_left_inj, mul_right_inj]
  have hgN : g ∈ Subgroup.normalizer (H z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact (key x).symm.trans (by rw [hHyeq])
  have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (H z) hgN
  exact mem_H_of_mem_normalizer_J (z := z) h h2

theorem normalizerControlsCenterJFusion_of_parrottHyp (h : Tim79a.ParrottHyp z) :
    NormalizerControlsCenterJFusion z := by
  classical
  haveI : ((J z).subgroupOf (H z)).Normal := J_subgroupOf_normal z
  have hz2 : orderOf z = 2 := h.1
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz2
  have hzZ : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hN : Subgroup.normalizer (centerIn (J z) : Set G) = H z := normalizer_centerIn_eq_H h
  intro a b ha hb hab
  obtain ⟨g, hg⟩ := hab
  rw [hN]
  by_cases hZ : centerIn (J z) = centerIn (H z)
  · have hab' := eq_of_isConj_of_mem_centerIn_J h hZ ha hb (isConj_iff.mpr ⟨g, hg⟩)
    exact ⟨1, Subgroup.one_mem _, by rw [hab']; group⟩
  obtain ⟨x, hxH, c, hcZ, hxc⟩ := exists_mem_H_not_commute_centerIn_J h hZ
  have hK : IsKleinFour ↥(centerIn (J z)) := isKleinFour_centerIn_J h
  have hconjZ : ∀ y ∈ H z, ∀ w ∈ centerIn (J z), y * w * y⁻¹ ∈ centerIn (J z) := by
    intro y hy w hw
    have := ((conjZ z) ⟨y, hy⟩ ⟨w, hw⟩).2
    rwa [conjZ_apply_coe] at this
  have hclass : ∀ a ∈ centerIn (J z), a ∉ Subgroup.zpowers z →
      ∀ y ∈ centerIn (J z), y = 1 ∨ y = z ∨ y = a ∨ y = z * a := by
    intro a ha haz y hy
    have ha1 : a ≠ 1 := fun h1 => haz (by rw [h1]; exact Subgroup.one_mem _)
    have haz' : a ≠ z := fun h1 => haz (by rw [h1]; exact Subgroup.mem_zpowers z)
    by_cases h1 : y = 1
    · exact Or.inl h1
    by_cases h2 : y = z
    · exact Or.inr (Or.inl h2)
    by_cases h3 : y = a
    · exact Or.inr (Or.inr (Or.inl h3))
    refine Or.inr (Or.inr (Or.inr ?_))
    have := IsKleinFour.eq_mul_of_ne_all (G := ↥(centerIn (J z))) (x := ⟨z, hzZ⟩)
      (y := ⟨a, ha⟩) (z := ⟨y, hy⟩) (fun e => hz1 (congrArg Subtype.val e))
      (fun e => ha1 (congrArg Subtype.val e)) (fun e => haz' (congrArg Subtype.val e).symm)
      (fun e => h1 (congrArg Subtype.val e)) (fun e => h2 (congrArg Subtype.val e))
      (fun e => h3 (congrArg Subtype.val e))
    exact congrArg Subtype.val this
  have hxz : x * z = z * x := by
    have := conj_z_eq_of_mem_H hxH
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [this]
  by_cases haz : a ∈ Subgroup.zpowers z
  · rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp haz with ha1 | haz'
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [ha1] at hg ⊢
      simpa using hg
    · rw [haz'] at hg
      have hgH : g ∈ H z := mem_H_of_conj_z_mem_centerIn h (by rw [hg]; exact hb)
      exact ⟨g, hgH, by rw [haz']; exact hg⟩
  have ha1 : a ≠ 1 := fun h1 => haz (by rw [h1]; exact Subgroup.one_mem _)
  have hb_not : b ∉ Subgroup.zpowers z := by
    intro hbz
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hbz with hb1 | hbz'
    · apply ha1
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [hg, hb1]; group
    · have hg' : g * a * g⁻¹ = z := hg.trans hbz'
      have haeq : g⁻¹ * z * (g⁻¹)⁻¹ = a := by
        rw [← hg']
        group
      have hgH' : g⁻¹ ∈ H z := mem_H_of_conj_z_mem_centerIn h (by rw [haeq]; exact ha)
      have haz2 : a = z := by
        rw [← haeq]
        exact conj_z_eq_of_mem_H hgH'
      exact haz (by rw [haz2]; exact Subgroup.mem_zpowers z)
  by_cases hba : b = a
  · exact ⟨1, Subgroup.one_mem _, by rw [hba]; group⟩
  have hb' : b = z * a := by
    rcases hclass a ha haz b hb with h1 | h1 | h1 | h1
    · exact absurd (by rw [h1]; exact Subgroup.one_mem _) hb_not
    · exact absurd (by rw [h1]; exact Subgroup.mem_zpowers z) hb_not
    · exact absurd h1 hba
    · exact h1
  have hxa : x * a ≠ a * x := by
    intro hcomm
    rcases hclass a ha haz c hcZ with h1 | h1 | h1 | h1
    · exact hxc (by rw [h1]; simp)
    · exact hxc (by rw [h1]; exact hxz)
    · exact hxc (by rw [h1]; exact hcomm)
    · refine hxc (by
        rw [h1]
        calc x * (z * a) = (x * z) * a := by rw [mul_assoc]
          _ = z * (x * a) := by rw [hxz, mul_assoc]
          _ = z * (a * x) := by rw [hcomm]
          _ = (z * a) * x := by rw [mul_assoc])
  have hxa' : x * a * x⁻¹ = z * a := by
    rcases hclass a ha haz _ (hconjZ x hxH a ha) with h1 | h1 | h1 | h1
    · exact absurd (by
        calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
          _ = 1 := by rw [h1]; group) ha1
    · refine absurd ?_ haz
      have haeq : a = x⁻¹ * z * (x⁻¹)⁻¹ := by
        calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
          _ = x⁻¹ * z * (x⁻¹)⁻¹ := by rw [h1]; group
      rw [haeq, conj_z_eq_of_mem_H ((H z).inv_mem hxH)]
      exact Subgroup.mem_zpowers z
    · exact absurd (by
        calc x * a = (x * a * x⁻¹) * x := by group
          _ = a * x := by rw [h1]) hxa
    · exact h1
  exact ⟨x, hxH, by rw [hxa', hb']⟩

end Fusion

end CFSG.RankThree.GF2n.Parrott
