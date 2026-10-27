module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankFix
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankTv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

section Model

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

private theorem s16_C4ModelTv_root_group (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n))
    {w : Fin 4 → F} (hw : w ∈ commSp E) (hwne : w ≠ 0) :
    ∃ B : Subgroup (SUid σ 4), B ≤ E ∧ Nat.card ↥B = 2 ^ n ∧
      (∀ a, a ∈ B ↔ a ∈ E ∧ ∀ x, herm σ w x = 0 → a • x = x) ∧
      (∀ x, (∀ b ∈ B, b • x = x) ↔ herm σ w x = 0) := by
  obtain ⟨hu, heq, hEP⟩ := eq_PW_of_card_eq hσ h2 hE2 hEc hn hF hcard
  have hti : ∀ w' ∈ commSp E, herm σ w w' = 0 := by
    intro w' hw'
    have hh : w ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hw
    rw [herm_conj σ hσ.invol w' w, mem_horth.mp hh w' hw', map_zero]
  have hww : herm σ w w = 0 := hti w hw
  have hc : ∀ c : F, σ c = c → c + σ c = 0 := fun c hc => by
    rw [hc, ← two_mul, h2, zero_mul]
  have htvE : ∀ (c : F) (hcc : c + σ c = 0), tv hσ.invol hww hcc ∈ E := by
    intro c hcc
    have hmem : tv hσ.invol hww hcc ∈ PW (commSp E) := by
      refine mem_PW.mpr ⟨fun v => ?_, fun w' hw' => ?_⟩
      · rw [tv_smul, add_sub_cancel_left]
        exact (commSp E).smul_mem _ hw
      · rw [tv_smul, hti w' hw', mul_zero, zero_smul, add_zero]
    rwa [← hEP] at hmem
  let B : Subgroup (SUid σ 4) :=
    { carrier := {a | a ∈ E ∧ ∀ x, herm σ w x = 0 → a • x = x}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, fun x hx => by
        rw [mul_smul, hb.2 x hx, ha.2 x hx]⟩
      one_mem' := ⟨E.one_mem, fun x _ => one_smul _ _⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, fun x hx => by
        rw [inv_smul_eq_iff]
        exact (ha.2 x hx).symm⟩ }
  have hBmem : ∀ a, a ∈ B ↔ a ∈ E ∧ ∀ x, herm σ w x = 0 → a • x = x := fun a => Iff.rfl
  have hfixB : ∀ x : Fin 4 → F, (∀ b ∈ B, b • x = x) ↔ herm σ w x = 0 := by
    intro x
    constructor
    · intro hx
      have hb : tv hσ.invol hww (hc 1 (map_one σ)) ∈ B :=
        ⟨htvE 1 (hc 1 (map_one σ)), fun y hy => by
          rw [tv_smul, hy, mul_zero, zero_smul, add_zero]⟩
      have := hx _ hb
      rw [tv_smul] at this
      have h3 : (1 * herm σ w x) • w = 0 := by
        have := add_eq_left.mp this
        exact this
      rcases smul_eq_zero.mp h3 with h | h
      · rwa [one_mul] at h
      · exact absurd h hwne
    · intro hx b hb
      exact hb.2 x hx
  refine ⟨B, fun a ha => ha.1, ?_, hBmem, hfixB⟩
  have hFix := card_fixedField_mul_self hσ h2
  have hq : Nat.card {c : F // σ c = c} = 2 ^ n := by
    rw [hF, ← sq] at hFix
    exact Nat.pow_left_injective (by norm_num) hFix
  rw [← hq]
  obtain ⟨x₀, hx₀⟩ := exists_herm_eq_one σ hwne
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : {c : F // σ c = c} =>
      (⟨tv hσ.invol hww (hc c.1 c.2), htvE c.1 (hc c.1 c.2), fun y hy => by
        rw [tv_smul, hy, mul_zero, zero_smul, add_zero]⟩ : ↥B)) ⟨?_, ?_⟩)).symm
  · intro c c' h
    have h1 : tv hσ.invol hww (hc c.1 c.2) = tv hσ.invol hww (hc c'.1 c'.2) :=
      congrArg Subtype.val h
    have h3 := congrArg (fun g : SUid σ 4 => g • x₀) h1
    simp only [tv_smul, hx₀, mul_one] at h3
    have h4 : (c.1 - c'.1) • w = 0 := by
      rw [sub_smul]
      have := add_left_cancel h3
      rw [this, sub_self]
    rcases smul_eq_zero.mp h4 with h | h
    · exact Subtype.ext (sub_eq_zero.mp h)
    · exact absurd h hwne
  · rintro ⟨a, haE, haf⟩
    obtain ⟨c, hcc, hac⟩ := exists_tv_of_fix_perp hσ h2 (hE2 a haE) hwne haf
    have hσc : σ c = c := by
      have : c + σ c = c + c := by rw [hcc, ← two_mul, h2, zero_mul]
      exact add_left_cancel this
    refine ⟨⟨c, hσc⟩, Subtype.ext ?_⟩
    show tv hσ.invol hww (hc c hσc) = a
    refine ext_smul σ fun x => ?_
    rw [tv_smul, hac x]

theorem s16_C4ModelTv_two_root_groups (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n)) :
    ∃ B₁ B₂ : Subgroup (SUid σ 4), B₁ ≤ E ∧ B₂ ≤ E ∧
      Nat.card ↥B₁ = 2 ^ n ∧ Nat.card ↥B₂ = 2 ^ n ∧
      (∀ a : SUid σ 4, a ∈ B₁ ↔ a ∈ E ∧ ∀ x ∈ fixSp B₁, a • x = x) ∧
      (∀ a : SUid σ 4, a ∈ B₂ ↔ a ∈ E ∧ ∀ x ∈ fixSp B₂, a • x = x) ∧
      Nat.card ↥(fixSp B₁) = 2 ^ (6 * n) ∧ Nat.card ↥(fixSp B₂) = 2 ^ (6 * n) ∧
      fixSp B₁ ⊔ fixSp B₂ = ⊤ := by
  obtain ⟨hu, heq, hEP⟩ := eq_PW_of_card_eq hσ h2 hE2 hEc hn hF hcard
  obtain ⟨⟨w₁, hw₁W⟩, hw₁ne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank F ↥(commSp E) by omega)
  have hw₁0 : w₁ ≠ 0 := fun h => hw₁ne (Subtype.ext h)
  obtain ⟨w₂, hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := F) (M := ↥(commSp E)) (by omega) (x := ⟨w₁, hw₁W⟩) (hx := hw₁ne)
  have hp := LinearIndependent.pair_iff.mp hli
  have hw₂0 : w₂ ≠ 0 := by
    intro h
    exact one_ne_zero (hp 0 1 (by rw [zero_smul, one_smul, h, add_zero])).2
  have hw₂ne : (w₂ : Fin 4 → F) ≠ 0 := fun h => hw₂0 (Subtype.ext h)
  obtain ⟨B₁, hB₁le, hB₁card, hB₁mem, hfixB₁⟩ :=
    s16_C4ModelTv_root_group hσ h2 hE2 hEc hn hF hcard hw₁W hw₁0
  obtain ⟨B₂, hB₂le, hB₂card, hB₂mem, hfixB₂⟩ :=
    s16_C4ModelTv_root_group hσ h2 hE2 hEc hn hF hcard (w := (w₂ : Fin 4 → F)) w₂.2 hw₂ne
  have hfix₁ : fixSp B₁ = LinearMap.ker (hermL σ w₁) := by
    ext x
    rw [mem_fixSp, hfixB₁ x, LinearMap.mem_ker, hermL_apply]
  have hfix₂ : fixSp B₂ = LinearMap.ker (hermL σ (w₂ : Fin 4 → F)) := by
    ext x
    rw [mem_fixSp, hfixB₂ x, LinearMap.mem_ker, hermL_apply]
  have hcardF : Nat.card F = 2 ^ (2 * n) := by
    rw [hF, ← pow_mul' (2 : ℕ) 2 n]
  have hkerfin₁ : Module.finrank F ↥(LinearMap.ker (hermL σ w₁)) = 3 := by
    have hne : hermL σ w₁ ≠ 0 := by
      intro h
      refine hw₁0 (eq_zero_of_herm σ fun y => ?_)
      have h1 := congrFun (congrArg DFunLike.coe h) y
      simpa [hermL_apply] using h1
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := hermL σ w₁) hne
    rw [Module.finrank_fin_fun] at h
    omega
  have hkerfin₂ : Module.finrank F ↥(LinearMap.ker (hermL σ (w₂ : Fin 4 → F))) = 3 := by
    have hne : hermL σ (w₂ : Fin 4 → F) ≠ 0 := by
      intro h
      refine hw₂ne (eq_zero_of_herm σ fun y => ?_)
      have h1 := congrFun (congrArg DFunLike.coe h) y
      simpa [hermL_apply] using h1
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := hermL σ (w₂ : Fin 4 → F)) hne
    rw [Module.finrank_fin_fun] at h
    omega
  have hcardfix₁ : Nat.card ↥(fixSp B₁) = 2 ^ (6 * n) := by
    calc Nat.card ↥(fixSp B₁) = Nat.card ↥(LinearMap.ker (hermL σ w₁)) := by rw [hfix₁]
      _ = Nat.card F ^ Module.finrank F ↥(LinearMap.ker (hermL σ w₁)) :=
            Module.natCard_eq_pow_finrank
      _ = Nat.card F ^ 3 := by rw [hkerfin₁]
      _ = 2 ^ (6 * n) := by
            rw [hcardF, ← pow_mul (2 : ℕ) (2 * n) 3]
            congr 1
            omega
  have hcardfix₂ : Nat.card ↥(fixSp B₂) = 2 ^ (6 * n) := by
    calc Nat.card ↥(fixSp B₂) = Nat.card ↥(LinearMap.ker (hermL σ (w₂ : Fin 4 → F))) := by
            rw [hfix₂]
      _ = Nat.card F ^ Module.finrank F ↥(LinearMap.ker (hermL σ (w₂ : Fin 4 → F))) :=
            Module.natCard_eq_pow_finrank
      _ = Nat.card F ^ 3 := by rw [hkerfin₂]
      _ = 2 ^ (6 * n) := by
            rw [hcardF, ← pow_mul (2 : ℕ) (2 * n) 3]
            congr 1
            omega
  have hsup : fixSp B₁ ⊔ fixSp B₂ = ⊤ := by
    rw [hfix₁, hfix₂]
    have hnotle : ¬ LinearMap.ker (hermL σ (w₂ : Fin 4 → F)) ≤ LinearMap.ker (hermL σ w₁) := by
      intro hle
      obtain ⟨c, hc⟩ : ∃ c : F, hermL σ w₁ = c • hermL σ (w₂ : Fin 4 → F) := by
        have hmem : hermL σ w₁ ∈ Submodule.span F
            (Set.range (fun _ : Unit => hermL σ (w₂ : Fin 4 → F))) :=
          mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => hermL σ (w₂ : Fin 4 → F))
            (K := hermL σ w₁) (by simpa using hle)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by simpa using hmem)
        exact ⟨c, hc.symm⟩
      have hw_eq : w₁ = σ c • (w₂ : Fin 4 → F) := by
        rw [← sub_eq_zero]
        apply eq_zero_of_herm σ
        intro y
        have hy : herm σ w₁ y = c * herm σ (w₂ : Fin 4 → F) y := by
          have h1 := congrFun (congrArg DFunLike.coe hc) y
          rw [LinearMap.smul_apply, smul_eq_mul, hermL_apply, hermL_apply] at h1
          exact h1
        rw [herm_sub_left, herm_smul_left, hσ.invol, hy, sub_self]
      have hsub : (⟨w₁, hw₁W⟩ : ↥(commSp E)) = σ c • w₂ := by
        apply Subtype.ext
        simpa using hw_eq
      exact one_ne_zero (hp 1 (-(σ c)) (by
        rw [one_smul, neg_smul, hsub, add_neg_cancel])).1
    obtain ⟨y, hy2, hy1⟩ : ∃ y, y ∈ LinearMap.ker (hermL σ (w₂ : Fin 4 → F)) ∧
        y ∉ LinearMap.ker (hermL σ w₁) := by
      by_contra hcon
      apply hnotle
      intro y hy
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    have hy2' : hermL σ (w₂ : Fin 4 → F) y = 0 := LinearMap.mem_ker.mp hy2
    have hy1' : hermL σ w₁ y ≠ 0 := fun h => hy1 (LinearMap.mem_ker.mpr h)
    rw [eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨x - (hermL σ w₁ x / hermL σ w₁ y) • y, ?_,
      (hermL σ w₁ x / hermL σ w₁ y) • y, ?_, ?_⟩
    · rw [LinearMap.mem_ker]
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy1', sub_self]
    · rw [LinearMap.mem_ker]
      rw [map_smul, smul_eq_mul, hy2', mul_zero]
    · rw [sub_add_cancel]
  refine ⟨B₁, B₂, hB₁le, hB₂le, hB₁card, hB₂card, ?_, ?_, hcardfix₁, hcardfix₂, hsup⟩
  · intro a
    rw [hB₁mem a]
    constructor
    · rintro ⟨haE, haf⟩
      exact ⟨haE, fun x hx => haf x ((hfixB₁ x).mp (mem_fixSp.mp hx))⟩
    · rintro ⟨haE, haf⟩
      exact ⟨haE, fun x hx => haf x (mem_fixSp.mpr ((hfixB₁ x).mpr hx))⟩
  · intro a
    rw [hB₂mem a]
    constructor
    · rintro ⟨haE, haf⟩
      exact ⟨haE, fun x hx => haf x ((hfixB₂ x).mp (mem_fixSp.mp hx))⟩
    · rintro ⟨haE, haf⟩
      exact ⟨haE, fun x hx => haf x (mem_fixSp.mpr ((hfixB₂ x).mpr hx))⟩

theorem s16_C4ModelTv_theta_eq_id (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : Nat.card ↥E = 2 ^ (4 * n))
    (τ : (Fin 4 → F) →+ (Fin 4 → F)) (θ : F →+* F)
    (hτ : ∀ (c : F) (x : Fin 4 → F), τ (c • x) = θ c • τ x) (hτinj : Function.Injective τ)
    (hcomm : ∀ a ∈ E, ∀ x : Fin 4 → F, τ (a • x) = a • τ x) : θ = RingHom.id F := by
  obtain ⟨hu, heq, hEP⟩ := eq_PW_of_card_eq hσ h2 hE2 hEc hn hF hcard
  have hti : ∀ w ∈ commSp E, ∀ w' ∈ commSp E, herm σ w w' = 0 := by
    intro w hw w' hw'
    have hh : w ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hw
    rw [herm_conj σ hσ.invol w' w, mem_horth.mp hh w' hw', map_zero]
  have hc1 : (1 : F) + σ 1 = 0 := by
    rw [map_one, one_add_one_eq_two, h2]
  have hstepA : ∀ w ∈ commSp E, w ≠ 0 → ∃ κ : F, τ w = κ • w := by
    intro w hw hwne
    have hww : herm σ w w = 0 := hti w hw w hw
    have htvE : tv hσ.invol hww hc1 ∈ E := by
      have hmem : tv hσ.invol hww hc1 ∈ PW (commSp E) := by
        refine mem_PW.mpr ⟨fun v => ?_, fun w' hw' => ?_⟩
        · rw [tv_smul, add_sub_cancel_left]
          exact (commSp E).smul_mem _ hw
        · rw [tv_smul, hti w hw w' hw', mul_zero, zero_smul, add_zero]
      rwa [← hEP] at hmem
    obtain ⟨x₀, hx₀⟩ := exists_herm_eq_one σ hwne
    have hsm : tv hσ.invol hww hc1 • x₀ = x₀ + w := by
      simp only [tv_smul, hx₀, mul_one, one_smul]
    have hcomm' := hcomm _ htvE x₀
    rw [hsm] at hcomm'
    rw [map_add, tv_smul, one_mul] at hcomm'
    exact ⟨herm σ w (τ x₀), add_left_cancel hcomm'⟩
  obtain ⟨⟨w₁, hw₁W⟩, hw₁ne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank F ↥(commSp E) by omega)
  have hw₁0 : w₁ ≠ 0 := fun h => hw₁ne (Subtype.ext h)
  obtain ⟨w₂, hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := F) (M := ↥(commSp E)) (by omega) (x := ⟨w₁, hw₁W⟩) (hx := hw₁ne)
  have hp := LinearIndependent.pair_iff.mp hli
  have hw₂0 : w₂ ≠ 0 := by
    intro h
    exact one_ne_zero (hp 0 1 (by rw [zero_smul, one_smul, h, add_zero])).2
  have hw₂ne : (w₂ : Fin 4 → F) ≠ 0 := fun h => hw₂0 (Subtype.ext h)
  obtain ⟨κ₁, hκ₁⟩ := hstepA w₁ hw₁W hw₁0
  obtain ⟨κ₂, hκ₂⟩ := hstepA (w₂ : Fin 4 → F) w₂.2 hw₂ne
  have hsum_ne : w₁ + (w₂ : Fin 4 → F) ≠ 0 := by
    intro h
    have hsub : (⟨w₁, hw₁W⟩ : ↥(commSp E)) + w₂ = 0 := by
      apply Subtype.ext
      simpa using h
    exact one_ne_zero (hp 1 1 (by rw [one_smul, one_smul]; exact hsub)).1
  obtain ⟨κ₃, hκ₃⟩ := hstepA (w₁ + (w₂ : Fin 4 → F)) ((commSp E).add_mem hw₁W w₂.2) hsum_ne
  have coeff_eq : ∀ (a b a' b' : F),
      a • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + b • w₂ =
        a' • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + b' • w₂ → a = a' ∧ b = b' := by
    intro a b a' b' hab
    have hzero : (a - a') • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + (b - b') • w₂ = 0 := by
      have h : (a - a') • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + (b - b') • w₂ =
          (a • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + b • w₂) -
          (a' • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + b' • w₂) := by
        module
      rw [h, hab, sub_self]
    have hpair := hp (a - a') (b - b') hzero
    exact ⟨sub_eq_zero.mp hpair.1, sub_eq_zero.mp hpair.2⟩
  have hκ_eq : κ₁ = κ₃ ∧ κ₂ = κ₃ := by
    apply coeff_eq
    apply Subtype.ext
    show κ₁ • w₁ + κ₂ • (w₂ : Fin 4 → F) = κ₃ • w₁ + κ₃ • (w₂ : Fin 4 → F)
    have h1 : τ (w₁ + (w₂ : Fin 4 → F)) = κ₁ • w₁ + κ₂ • (w₂ : Fin 4 → F) := by
      rw [map_add, hκ₁, hκ₂]
    rw [← h1, hκ₃, smul_add]
  have hκ₂κ₁ : κ₂ = κ₁ := hκ_eq.2.trans hκ_eq.1.symm
  have hκne : κ₁ ≠ 0 := by
    intro h0
    refine hw₁0 (hτinj ?_)
    rw [hκ₁, h0, zero_smul, map_zero]
  refine RingHom.ext fun c => ?_
  rw [RingHom.id_apply]
  have hmem_c : c • w₁ + (w₂ : Fin 4 → F) ∈ commSp E :=
    (commSp E).add_mem ((commSp E).smul_mem c hw₁W) w₂.2
  have hne_c : c • w₁ + (w₂ : Fin 4 → F) ≠ 0 := by
    intro h
    have hsub : c • (⟨w₁, hw₁W⟩ : ↥(commSp E)) + w₂ = 0 := by
      apply Subtype.ext
      simpa using h
    exact one_ne_zero (hp c 1 (by rw [one_smul]; exact hsub)).2
  obtain ⟨κ', hκ'⟩ := hstepA (c • w₁ + (w₂ : Fin 4 → F)) hmem_c hne_c
  have hc_coeff : θ c * κ₁ = κ' * c ∧ κ₂ = κ' := by
    apply coeff_eq
    apply Subtype.ext
    show (θ c * κ₁) • w₁ + κ₂ • (w₂ : Fin 4 → F) =
      (κ' * c) • w₁ + κ' • (w₂ : Fin 4 → F)
    have h1 : τ (c • w₁ + (w₂ : Fin 4 → F)) =
        (θ c * κ₁) • w₁ + κ₂ • (w₂ : Fin 4 → F) := by
      rw [map_add, hτ c w₁, hκ₁, hκ₂, smul_smul]
    have h2 : τ (c • w₁ + (w₂ : Fin 4 → F)) =
        (κ' * c) • w₁ + κ' • (w₂ : Fin 4 → F) := by
      rw [hκ', smul_add, smul_smul]
    rw [← h1, h2]
  have hκ'κ₁ : κ' = κ₁ := by rw [← hc_coeff.2, hκ₂κ₁]
  have hmul : θ c * κ₁ = κ₁ * c := by rw [hc_coeff.1, hκ'κ₁]
  exact mul_right_cancel₀ hκne (by rw [hmul, mul_comm])

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
