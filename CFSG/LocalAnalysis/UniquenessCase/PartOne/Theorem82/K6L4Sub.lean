module

public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open Subgroup
open scoped MatrixGroups

variable {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F]

private theorem not_eight_dvd_of_two_dvd_odd_half {n : ℕ} (h2 : 2 ∣ n) (hodd : Odd (n / 2)) :
    ¬ 8 ∣ n := by
  intro h8
  obtain ⟨m, hm⟩ := h2
  have hoddm : Odd m := by
    have : n / 2 = m := by omega
    rwa [this] at hodd
  obtain ⟨k, hk⟩ := hoddm
  obtain ⟨c, hc⟩ := h8
  rw [hm, hk] at hc
  omega

private theorem card_dvd_of_map_eq_top {P : Type*} [Group P] (f : P × P →* P)
    {M : Subgroup (P × P)} (h : M.map f = ⊤) : Nat.card P ∣ Nat.card M := by
  have hrange : (f.comp M.subtype).range = M.map f := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hdvd := Subgroup.card_range_dvd (f.comp M.subtype)
  rw [hrange, h, Subgroup.card_top] at hdvd
  exact hdvd

private theorem le_prod_center_of_map_le_center {P : Type*} [Group P] {M : Subgroup (P × P)}
    (h₁ : M.map (MonoidHom.fst P P) ≤ Subgroup.center P)
    (h₂ : M.map (MonoidHom.snd P P) ≤ Subgroup.center P) :
    M ≤ (Subgroup.center P).prod (Subgroup.center P) := by
  intro x hx
  exact Subgroup.mem_prod.mpr
    ⟨h₁ (Subgroup.mem_map_of_mem (MonoidHom.fst P P) hx),
     h₂ (Subgroup.mem_map_of_mem (MonoidHom.snd P P) hx)⟩

private theorem sl2sq_le_center_prod {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hF : Nat.card F = r)
    {M : Subgroup (SL(2, F) × SL(2, F))} (hM : M.Normal) (h2 : 2 ∣ Nat.card M)
    (hodd : Odd (Nat.card M / 2)) :
    M ≤ (Subgroup.center (SL(2, F))).prod (Subgroup.center (SL(2, F))) := by
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact hr.odd_iff.mpr (by omega)
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  have h8r : 8 ∣ r ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd (by rw [← hF]; exact hoddF)
  have hcardP : Nat.card (SL(2, F)) = r * (r ^ 2 - 1) := by
    have h := CFSG.Open.StatedAPI.card_statedSL_two F
    rw [CFSG.Open.StatedAPI.card_statedSL] at h
    rw [hF] at h
    exact h
  have h8P : 8 ∣ Nat.card (SL(2, F)) := by
    rw [hcardP]; exact dvd_mul_of_dvd_right h8r r
  have hnot8 : ¬ 8 ∣ Nat.card M := not_eight_dvd_of_two_dvd_odd_half h2 hodd
  have hnot8P : ¬ Nat.card (SL(2, F)) ∣ Nat.card M := fun h => hnot8 (h8P.trans h)
  set M₁ : Subgroup (SL(2, F)) := M.map (MonoidHom.fst (SL(2, F)) (SL(2, F))) with hM₁def
  set M₂ : Subgroup (SL(2, F)) := M.map (MonoidHom.snd (SL(2, F)) (SL(2, F))) with hM₂def
  have hM₁normal : M₁.Normal :=
    hM.map (MonoidHom.fst (SL(2, F)) (SL(2, F))) (fun x => ⟨(x, 1), rfl⟩)
  have hM₂normal : M₂.Normal :=
    hM.map (MonoidHom.snd (SL(2, F)) (SL(2, F))) (fun x => ⟨(1, x), rfl⟩)
  have hM₁cases : M₁ = ⊥ ∨ M₁ = Subgroup.center (SL(2, F)) ∨ M₁ = ⊤ :=
    CFSG.ClassicalInvolution.normal_cases_of_equiv_sl2 h4 (MulEquiv.refl (SL(2, F)))
      M₁ hM₁normal
  have hM₂cases : M₂ = ⊥ ∨ M₂ = Subgroup.center (SL(2, F)) ∨ M₂ = ⊤ :=
    CFSG.ClassicalInvolution.normal_cases_of_equiv_sl2 h4 (MulEquiv.refl (SL(2, F)))
      M₂ hM₂normal
  have hM₁le : M₁ ≤ Subgroup.center (SL(2, F)) := by
    rcases hM₁cases with h | h | h
    · rw [h]; exact bot_le
    · rw [h]
    · exact absurd h (fun htop => hnot8P (card_dvd_of_map_eq_top _
        (by rw [← hM₁def]; exact htop)))
  have hM₂le : M₂ ≤ Subgroup.center (SL(2, F)) := by
    rcases hM₂cases with h | h | h
    · rw [h]; exact bot_le
    · rw [h]
    · exact absurd h (fun htop => hnot8P (card_dvd_of_map_eq_top _
        (by rw [← hM₂def]; exact htop)))
  exact le_prod_center_of_map_le_center (by rwa [← hM₁def]) (by rwa [← hM₂def])

theorem sl2sq_perfect {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hF : Nat.card F = r)
    {K₁ : Subgroup H}
    (e : K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :
    ⁅K₁, K₁⁆ = K₁ ∧ ¬ IsSolvable K₁ ∧ Nat.card K₁ = (r * (r ^ 2 - 1)) ^ 2 := by
  have h4 : 4 ≤ Nat.card F := by rw [hF]; omega
  have hperfP : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hperfPP :
      Group.IsPerfect
        (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) := by
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := hperfP
    rw [Group.isPerfect_def, _root_.commutator_def, ← Subgroup.top_prod_top,
      Subgroup.commutator_prod_prod, Subgroup.commutator_eq_self, Subgroup.top_prod_top]
  haveI : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) := hperfPP
  have hperfK : Group.IsPerfect ↥K₁ :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcardP : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = r * (r ^ 2 - 1) := by
    have h := CFSG.Open.StatedAPI.card_statedSL_two F
    rw [CFSG.Open.StatedAPI.card_statedSL] at h
    rw [hF] at h
    exact h
  have hcardK : Nat.card K₁ = (r * (r ^ 2 - 1)) ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hcardP]
    ring
  haveI : Nontrivial ↥K₁ := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hcardK]
    have h24 : 24 ≤ r ^ 2 - 1 := by
      have : 25 ≤ r ^ 2 := by nlinarith
      omega
    have h120 : 120 ≤ r * (r ^ 2 - 1) := by
      calc 120 = 5 * 24 := by norm_num
        _ ≤ r * (r ^ 2 - 1) := Nat.mul_le_mul h5 h24
    exact one_lt_pow₀ (by omega) (by norm_num)
  haveI : Group.IsPerfect ↥K₁ := hperfK
  exact ⟨Subgroup.isPerfect_iff.mp hperfK, Group.IsPerfect.not_isSolvable ↥K₁, hcardK⟩

theorem sl2sq_odd {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hF : Nat.card F = r)
    {K₁ : Subgroup H}
    (e : K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)
    {Z : Subgroup H} (hZ : Z ≤ K₁) (hZc : Z ≤ Subgroup.center H) (hZ2 : Nat.card Z = 2) :
    ∀ N : Subgroup H, N ≤ K₁ → (N.subgroupOf K₁).Normal → Z ≤ N → Odd (Nat.card N / 2) →
      N ≤ Z := by
  intro N hNK hNnorm hZN hodd
  have hoddF : Odd (Nat.card F) := by rw [hF]; exact hr.odd_iff.mpr (by omega)
  have h2dvd : 2 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hZN
    rwa [hZ2] at this
  set ψ : ↥K₁ →* SL(2, F) × SL(2, F) := e.toMonoidHom
  set N' : Subgroup (SL(2, F) × SL(2, F)) := (N.subgroupOf K₁).map ψ with hN'def
  have hN'normal : N'.Normal := hNnorm.map ψ e.surjective
  have hcardN' : Nat.card N' = Nat.card N := by
    rw [hN'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
  have h2' : 2 ∣ Nat.card N' := by rwa [hcardN']
  have hodd' : Odd (Nat.card N' / 2) := by rwa [hcardN']
  have hN'le := sl2sq_le_center_prod hr h5 hF hN'normal h2' hodd'
  have hcardC : Nat.card ((Subgroup.center (SL(2, F))).prod (Subgroup.center (SL(2, F)))) = 4 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      CFSG.ClassicalInvolution.sl2_natCard_center hoddF]
  have hle4 : Nat.card N ≤ 4 := by
    calc Nat.card N = Nat.card N' := hcardN'.symm
      _ ≤ Nat.card ((Subgroup.center (SL(2, F))).prod (Subgroup.center (SL(2, F)))) :=
          Subgroup.card_le_of_le hN'le
      _ = 4 := hcardC
  have hcardN2 : Nat.card N = 2 := by
    obtain ⟨m, hm⟩ := h2dvd
    have hmle : m ≤ 2 := by
      have : 2 * m ≤ 4 := by rw [← hm]; exact hle4
      omega
    have hoddm : Odd m := by
      have : Nat.card N / 2 = m := by omega
      rwa [this] at hodd
    obtain ⟨k, hk⟩ := hoddm
    omega
  have hNZ : Z = N := Subgroup.eq_of_le_of_card_ge hZN (by rw [hcardN2, hZ2])
  exact hNZ.ge

theorem quasisimple_facts {K₃ : Subgroup H} (hperf : ⁅K₃, K₃⁆ = K₃)
    (hsimple : IsSimpleGroup (K₃ ⧸ Subgroup.center K₃)) (hev : 2 ∣ Nat.card K₃) :
    ¬ IsSolvable K₃ ∧ ∀ N : Subgroup H, N ≤ K₃ → (N.subgroupOf K₃).Normal → Odd (Nat.card N) →
      N ≤ Subgroup.centralizer (K₃ : Set H) := by
  have hperfK : Group.IsPerfect ↥K₃ := Subgroup.isPerfect_iff.mpr hperf
  haveI : Group.IsPerfect ↥K₃ := hperfK
  haveI : Nontrivial ↥K₃ := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    obtain ⟨k, hk⟩ := hev
    have := Nat.card_pos (α := ↥K₃)
    omega
  have hcomm : commutator ↥K₃ = ⊤ := hperfK.commutator_eq_top
  refine ⟨Group.IsPerfect.not_isSolvable ↥K₃, ?_⟩
  intro N hNK hNnorm hNodd
  haveI : IsSimpleGroup (K₃ ⧸ Subgroup.center K₃) := hsimple
  letI : (N.subgroupOf K₃).Normal := hNnorm
  let f : ↥K₃ →* ↥K₃ ⧸ Subgroup.center ↥K₃ := QuotientGroup.mk' (Subgroup.center ↥K₃)
  have hker : f.ker = Subgroup.center ↥K₃ := QuotientGroup.ker_mk' _
  have hmapnorm : ((N.subgroupOf K₃).map f).Normal :=
    hNnorm.map f (QuotientGroup.mk'_surjective _)
  haveI := hmapnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K₃).map f) with h | h
  · have hle : N.subgroupOf K₃ ≤ Subgroup.center ↥K₃ := by
      rwa [Subgroup.map_eq_bot_iff, hker] at h
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hn' : (⟨n, hNK hn⟩ : ↥K₃) ∈ N.subgroupOf K₃ := hn
    have hcz : (⟨n, hNK hn⟩ : ↥K₃) ∈ Subgroup.center ↥K₃ := hle hn'
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcz) ⟨x, hx⟩)
  · exfalso
    have hsup : N.subgroupOf K₃ ⊔ Subgroup.center ↥K₃ = ⊤ := by
      have := Subgroup.comap_map_eq f (N.subgroupOf K₃)
      rw [h, Subgroup.comap_top, hker] at this
      exact this.symm
    have hle : commutator ↥K₃ ≤ N.subgroupOf K₃ :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hcomm, top_le_iff] at hle
    have hNtop : N = K₃ := by
      rw [Subgroup.subgroupOf_eq_top] at hle
      exact le_antisymm hNK hle
    rw [hNtop] at hNodd
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hev)) hNodd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
