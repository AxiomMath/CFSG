module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Cen3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

theorem conjBy_one' {G : Type} [Group G] (H : Subgroup G) : conjBy (1 : G) H = H := by
  ext x
  rw [mem_conjBy_iff]
  simp

theorem conjBy_zpowers {G : Type} [Group G] (y x : G) :
    conjBy y (Subgroup.zpowers x) = Subgroup.zpowers (y * x * y⁻¹) := by
  have := MonoidHom.map_zpowers (MulAut.conj y).toMonoidHom x
  simpa [MulAut.conj_apply] using this

theorem isElemAb_conjBy_three {G : Type} [Group G] [Finite G] {k : ℕ} {B : Subgroup G}
    (h : IsElemAb 3 k B) (c : G) : IsElemAb 3 k (conjBy c B) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.1
  exact ⟨CFSG.IsElementaryAbelian.map (A := B) (MulAut.conj c).toMonoidHom,
    (card_conjBy c B).trans h.2⟩

section Ord3

theorem exists_conj_T0 {B : Subgroup F42C}
    (hB : IsElemAb 3 4 B) : ∃ k : F42C, B = conjBy k T0 := by
  haveI : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := IsPGroup.of_card (n := 4) hB.2
  obtain ⟨k, -, hk⟩ := exists_conj_le_sylowOf_p P0_sylow le_top hBp
  have hle : conjBy k B ≤ P0 := by
    rintro _ ⟨b, hb, rfl⟩
    exact hk b hb
  have hT : conjBy k B = T0 := e81_P0 hle (isElemAb_conjBy_three hB k)
  refine ⟨k⁻¹, ?_⟩
  rw [← hT, conjBy_conjBy, inv_mul_cancel, conjBy_one']

theorem L5_C {Q : Subgroup F42C}
    (hQ : IsSylowOf 3 Q (⊤ : Subgroup F42C))
    {B₁ B₂ : Subgroup F42C} (h₁ : B₁ ≤ Q) (h₂ : B₂ ≤ Q) (e₁ : IsElemAb 3 4 B₁)
    (e₂ : IsElemAb 3 4 B₂) : B₁ = B₂ := by
  haveI : Finite F42C := finite_adjF
  obtain ⟨a, -, ha⟩ := exists_conjBy_eq_sylowOf hQ P0_sylow
  have key : ∀ B : Subgroup F42C, B ≤ Q → IsElemAb 3 4 B → conjBy a⁻¹ B = T0 := by
    intro B hBQ hB
    apply e81_P0 _ (isElemAb_conjBy_three hB a⁻¹)
    rintro _ ⟨b, hb, rfl⟩
    have hbQ : b ∈ conjBy a P0 := ha ▸ hBQ hb
    rw [mem_conjBy_iff] at hbQ
    simpa [MulAut.conj_apply] using hbQ
  have h1 := key B₁ h₁ e₁
  have h2 := key B₂ h₂ e₂
  have : conjBy a⁻¹ B₁ = conjBy a⁻¹ B₂ := h1.trans h2.symm
  exact Subgroup.map_injective (MulAut.conj a⁻¹).injective this

noncomputable def repE (i : ℕ) : F42C :=
  match i with
  | 0 => tE
  | 1 => uE
  | 2 => tuE
  | _ => vE

noncomputable def rhoE (j : ℕ) : F42C := if j = 0 then rAE else rBE

theorem order_three_AB {x : F42C} (hx : orderOf x = 3)
    (hnd : ¬ 3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set F42C))) :
    (∃ c, c * x * c⁻¹ = rAE) ∨ (∃ c, c * x * c⁻¹ = rBE) := by
  rcases order_three_cases hx with h | h | ⟨c, hcx⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply hnd
    rw [card_cen_isConj (isConj_iff.2 ⟨c, hcx⟩)]
    exact three_pow_dvd_cen_zE

theorem L6_star_C {t x : F42C} (ht : orderOf t = 2)
    (hx : orderOf x = 3)
    (hnd : ¬ 3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set F42C))) :
    ∃ y : F42C, y * x * y⁻¹ ∈ Subgroup.centralizer ({t} : Set F42C) := by
  have hsq : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have hne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  obtain ⟨r, hr, hconj⟩ := classesCover_AS (K := ZMod 2) t hsq hne
  have hrr : ∃ i < 4, r = repE i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩
  obtain ⟨i, hi, rfl⟩ := hrr
  obtain ⟨a, ha⟩ : ∃ a : F42C, a * repE i * a⁻¹ = t := isConj_iff.1 hconj
  have key : ∀ (j : ℕ) (hj : j < 2) (b : F42C), b * x * b⁻¹ = rhoE j →
      ∃ y : F42C, y * x * y⁻¹ ∈ Subgroup.centralizer ({t} : Set F42C) := by
    intro j hj b hb
    have hrep : repE i ∈ [tE, uE, tuE, vE] := by
      rw [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton]
      interval_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    have hrho : rhoE j ∈ [rAE, rBE] := by
      rw [List.mem_cons, List.mem_singleton]
      interval_cases j
      · exact Or.inl (if_pos rfl)
      · exact Or.inr (if_neg (by norm_num))
    obtain ⟨w, hcomm⟩ := inv_comm_C _ hrep _ hrho
    refine ⟨a * w * b, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← ha]
    calc a * w * b * x * (a * w * b)⁻¹ * (a * repE i * a⁻¹)
        = a * ((w * (b * x * b⁻¹) * w⁻¹) * repE i) * a⁻¹ := by group
      _ = a * (repE i * (w * (b * x * b⁻¹) * w⁻¹)) * a⁻¹ := by rw [hb, hcomm]
      _ = a * repE i * a⁻¹ * (a * w * b * x * (a * w * b)⁻¹) := by group
  rcases order_three_AB hx hnd with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact key 0 (by norm_num) b hb
  · exact key 1 (by norm_num) b hb

theorem sE_mem_T0 (i : Fin 4) : sE i ∈ T0 := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem rAE_mem_T0 : rAE ∈ T0 := sE_mem_T0 3

theorem rBE_mem_T0 : rBE ∈ T0 := Subgroup.mul_mem _ (sE_mem_T0 0) (sE_mem_T0 1)

theorem tgE_mem_T0 {a : ℕ} (ha : a < 2) : tgE a ∈ T0 := by
  interval_cases a
  · have h : tgE 0 = rAE := if_pos rfl
    rw [h]
    exact rAE_mem_T0
  · have h : tgE 1 = rBE := by unfold tgE; rw [if_neg (by norm_num), if_pos rfl]
    rw [h]
    exact rBE_mem_T0

end Ord3

section Ord3b

theorem L4_star_C {B : Subgroup F42C} (hB : IsElemAb 3 4 B)
    {x : F42C} (hx : orderOf x = 3)
    (hnd : ¬ 3 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set F42C))) :
    {D : Subgroup F42C | D ≤ B ∧ ∃ y : F42C, conjBy y (Subgroup.zpowers x) = D}.ncard ≤ 12 ∧
      ∃ y : F42C, y * x * y⁻¹ ∈ B := by
  obtain ⟨k, hk⟩ := exists_conj_T0 hB
  obtain ⟨a, ha, c, hcx⟩ : ∃ a, a < 2 ∧ ∃ c : F42C, c * x * c⁻¹ = tgE a := by
    rcases order_three_AB hx hnd with ⟨c, hc'⟩ | ⟨c, hc'⟩
    · exact ⟨0, by norm_num, c, by rw [hc']; exact (if_pos rfl).symm⟩
    · exact ⟨1, by norm_num, c, by rw [hc']; unfold tgE; rw [if_neg (by norm_num), if_pos rfl]⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hA : tgE 0 = rAE := if_pos rfl
  have hB0 : tgE 1 = rBE := by unfold tgE; rw [if_neg (by norm_num), if_pos rfl]
  obtain ⟨nAB, nAZ, nBZ⟩ := rho_not_conj
  obtain ⟨LA, LB, hLA, hLB, hL⟩ := t0_lines
  obtain ⟨L, hLc, hLm⟩ : ∃ L : Finset (Subgroup F42C), L.card ≤ 12 ∧ ∀ d ∈ T0, d ≠ 1 →
      IsConj d (tgE a) → Subgroup.zpowers d ∈ L := by
    interval_cases a
    · refine ⟨LA, hLA, fun d hd hd1 hk => ?_⟩
      rw [hA] at hk
      rcases hL d hd hd1 with ⟨-, h2⟩ | ⟨h1, -⟩ | h1
      · exact h2
      · exact absurd (hk.symm.trans h1) nAB
      · exact absurd (hk.symm.trans h1) nAZ
    · refine ⟨LB, hLB, fun d hd hd1 hk => ?_⟩
      rw [hB0] at hk
      rcases hL d hd hd1 with ⟨h1, -⟩ | ⟨-, h2⟩ | h1
      · exact absurd (h1.symm.trans hk) nAB
      · exact h2
      · exact absurd (hk.symm.trans h1) nBZ
  classical
  refine ⟨?_, ?_⟩
  · have hsub : {D : Subgroup F42C | D ≤ B ∧ ∃ y : F42C, conjBy y (Subgroup.zpowers x) = D} ⊆
        ↑(L.image fun H => conjBy k H) := by
      rintro D ⟨hDB, y, rfl⟩
      have hyx : y * x * y⁻¹ ∈ conjBy y (Subgroup.zpowers x) :=
        ⟨x, Subgroup.mem_zpowers x, rfl⟩
      have hdT : k⁻¹ * (y * x * y⁻¹) * k ∈ T0 := by
        have := hDB hyx
        rw [hk, mem_conjBy_iff] at this
        exact this
      set d := k⁻¹ * (y * x * y⁻¹) * k with hd
      have hdconj : d = (k⁻¹ * y) * x * (k⁻¹ * y)⁻¹ := by rw [hd]; group
      have hd1 : d ≠ 1 := by
        intro h
        rw [hdconj] at h
        exact hx1 (conj_eq_one_iff.1 h)
      have hkd : IsConj d (tgE a) := by
        refine isConj_iff.2 ⟨c * (k⁻¹ * y)⁻¹, ?_⟩
        rw [hdconj, ← hcx]
        group
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨Subgroup.zpowers d, hLm d hdT hd1 hkd, ?_⟩)
      rw [conjBy_zpowers, conjBy_zpowers]
      congr 1
      rw [hd]
      group
    refine le_trans (Set.ncard_le_ncard hsub (Finset.finite_toSet _)) ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le.trans hLc
  · refine ⟨k * c, ?_⟩
    have : (k * c) * x * (k * c)⁻¹ = k * (c * x * c⁻¹) * k⁻¹ := by group
    rw [this, hcx, hk]
    exact ⟨tgE a, tgE_mem_T0 ha, rfl⟩

end Ord3b

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
