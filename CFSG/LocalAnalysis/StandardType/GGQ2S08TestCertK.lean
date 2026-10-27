module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCertFive

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ} {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x₀ : Vn n}

theorem TestHyp.exists_cls_of_certOKGiven (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    {sets : List (List (Vn n))} {pats : List ((Vn n × Vn n) × PatV n)}
    {reps : List (Vn n × Vn n)} {s2 : List (S2V n)} {gp : List (ℕ × ℕ)}
    (hOK : certOKGiven gens x₀ sets pats reps s2 gp = true) (hgW : ∀ l ∈ gens, letLin l ∈ W)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l})
    (hred : ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ p ∈ pats,
      ∃ h : p.1.2 ⬝ᵥ p.1.1 = 2, w * u * w⁻¹ = refl p.1.1 p.1.2 h) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine x₀ u → ∃ w ∈ W, ∃ i < reps.length,
      ∃ h : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2,
        w * u * w⁻¹ = refl (letAt reps i).1 (letAt reps i).2 h := by
  unfold certOKGiven at hOK
  simp only [Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨⟨hgOK, hrOK⟩, hsOK⟩, hpOK⟩, hs2OK⟩ := hOK
  have hgens : AlphOK gens := AlphOK.of_all hgOK
  have hreps : AlphOK reps := AlphOK.of_all hrOK
  have hinv := sets_inv_of_gens hgens hWgen hsOK
  intro u hu huR hux
  obtain ⟨w, hw, p, hp, hpc, hwu⟩ := hred u hu huR hux
  have hpA : refl p.1.1 p.1.2 hpc ∈ A := by
    rw [← hwu]
    exact A.mul_mem (A.mul_mem (hT.le (hT.W_le hw)) hu) (A.inv_mem (hT.le (hT.W_le hw)))
  obtain ⟨w', hw', i, hi, hrep, hw'p⟩ := hT.exists_rep_of_patB hgens hgW hinv hreps
    (List.all_eq_true.mp hpOK p hp) hpc hpA
  refine ⟨w' * w, W.mul_mem hw' hw, i, hi, hrep, ?_⟩
  rw [← hw'p, ← hwu, mul_inv_rev]
  group

theorem TestHyp.mem_of_s2_of_certOKGiven (hT : TestHyp W x₀ A M) {gens : List (Vn n × Vn n)}
    {sets : List (List (Vn n))} {pats : List ((Vn n × Vn n) × PatV n)}
    {reps : List (Vn n × Vn n)} {s2 : List (S2V n)} {gp : List (ℕ × ℕ)}
    (hOK : certOKGiven gens x₀ sets pats reps s2 gp = true) (hgW : ∀ l ∈ gens, letLin l ∈ W)
    (hWgen : W ≤ Subgroup.closure {g | ∃ l ∈ gens, g = letLin l}) {i j : ℕ}
    (hi : i < reps.length) (hj : j < reps.length) (hij : (i, j) ∉ gp)
    (hi2 : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
    (hj2 : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2)
    (hrM : refl (letAt reps i).1 (letAt reps i).2 hi2 ∈ M)
    (htA : refl (letAt reps j).1 (letAt reps j).2 hj2 ∈ A) :
    refl (letAt reps j).1 (letAt reps j).2 hj2 ∈ M := by
  unfold certOKGiven at hOK
  simp only [Bool.and_eq_true] at hOK
  obtain ⟨⟨⟨⟨hgOK, hrOK⟩, hsOK⟩, hpOK⟩, hs2OK⟩ := hOK
  have hgens : AlphOK gens := AlphOK.of_all hgOK
  have hreps : AlphOK reps := AlphOK.of_all hrOK
  have hinv := sets_inv_of_gens hgens hWgen hsOK
  have hB := List.all_eq_true.mp (List.all_eq_true.mp hs2OK i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  rcases Bool.or_eq_true_iff.mp hB with hg | hB
  · exact absurd (of_decide_eq_true hg) hij
  · exact hT.mem_of_s2B hgens hgW hinv hi2 hj2 hrM htA hB

@[expose] def a7fK (Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)) (u : Vn 7 ≃ₗ[ZMod 3] Vn 7) : Prop :=
  ∃ R : Set (Vn 7 ≃ₗ[ZMod 3] Vn 7), (∀ s ∈ R, IsRefl s) ∧ Subgroup.closure R ≤ Mg ∧
    (∀ h ∈ Subgroup.closure R, u * h * u⁻¹ ∈ Subgroup.closure R) ∧
    (∃ h ∈ Subgroup.closure R, h (oneN 7) ≠ oneN 7) ∧
    ∃ S : Finset (Fin 7), 5 ≤ S.card ∧ ∀ v : Vn 7, (∀ h ∈ Subgroup.closure R, h v = v) →
      ∀ a ∈ S, ∀ b ∈ S, v a = v b

private lemma isRefl_conj {g κ : Vn 7 ≃ₗ[ZMod 3] Vn 7} (hg : IsRefl g) :
    IsRefl (κ * g * κ⁻¹) := by
  obtain ⟨c, a, h, rfl⟩ := eq_refl_of_isRefl hg
  rw [conj_refl]
  exact ⟨κ c, dualVec (κ.symm : Vn 7 →ₗ[ZMod 3] Vn 7) a,
    by rw [dualVec_dotProduct]; simpa using h, fun v => by rw [refl_apply]⟩

theorem a7fK_conj {Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)} (σ : Equiv.Perm (Fin 7))
    (hσ : permN σ ∈ Mg) {u : Vn 7 ≃ₗ[ZMod 3] Vn 7} (hu : a7fK Mg u) :
    a7fK Mg (permN σ * u * (permN σ)⁻¹) := by
  obtain ⟨R, hRrefl, hRle, hNorm, hMove, S, hScard, hSconst⟩ := hu
  let κ := permN σ
  have hconj : ∀ x : Vn 7 ≃ₗ[ZMod 3] Vn 7,
      (MulEquiv.toMonoidHom (MulAut.conj κ)) x = κ * x * κ⁻¹ := fun x => rfl
  have hclosure : Subgroup.closure ((MulAut.conj κ) '' R) =
      (Subgroup.closure R).map (MulAut.conj κ).toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  refine ⟨(MulAut.conj κ) '' R, ?_, ?_, ?_, ?_, S.map σ.toEmbedding, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact isRefl_conj (hRrefl h hh)
  · rw [hclosure]
    rintro _ ⟨h, hh, rfl⟩
    rw [hconj]
    exact Mg.mul_mem (Mg.mul_mem hσ (hRle hh)) (Mg.inv_mem hσ)
  · intro h hh
    rw [hclosure] at hh ⊢
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨u * g * u⁻¹, hNorm g hg, ?_⟩
    rw [hconj, hconj g]
    dsimp only [κ]
    group
  · obtain ⟨h, hh, hhne⟩ := hMove
    refine ⟨MulAut.conj κ h, ?_, ?_⟩
    · rw [hclosure]
      exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    · change (κ * h * κ⁻¹) (oneN 7) ≠ oneN 7
      have hκinv : κ.symm (oneN 7) = oneN 7 := by
        change (permN σ)⁻¹ (oneN 7) = oneN 7
        rw [permN_inv]
        exact permN_oneN σ⁻¹
      have happ : (κ * h * κ⁻¹) (oneN 7) = κ (h (oneN 7)) := by
        simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
        rw [hκinv]
      intro heq
      apply hhne
      apply κ.injective
      rw [happ] at heq
      rw [heq, permN_oneN]
  · rw [Finset.card_map]
    exact hScard
  · intro v hv a ha b hb
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hb
    have hw : ∀ g ∈ Subgroup.closure R, g (κ⁻¹ v) = κ⁻¹ v := by
      intro g hg
      have hmem : MulAut.conj κ g ∈ Subgroup.closure ((MulAut.conj κ) '' R) := by
        rw [hclosure]
        exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
      have hfix := hv _ hmem
      rw [show MulAut.conj κ g = κ * g * κ⁻¹ from rfl] at hfix
      have := congrArg (fun w => κ⁻¹ w) hfix
      simpa using this
    have hconst := hSconst (κ⁻¹ v) hw a0 ha0 b0 hb0
    have ha' : (κ⁻¹ v) a0 = v (σ a0) := by
      change ((permN σ)⁻¹ v) a0 = v (σ a0)
      rw [permN_inv, permN_apply]
      congr 1
    have hb' : (κ⁻¹ v) b0 = v (σ b0) := by
      change ((permN σ)⁻¹ v) b0 = v (σ b0)
      rw [permN_inv, permN_apply]
      congr 1
    rw [ha', hb'] at hconst
    exact hconst

private def c17 : Vn 7 := ![1, 1, 1, 1, 2, 2, 2]
private def a17 : Vn 7 := ![2, 2, 2, 2, 0, 0, 0]
private def z17 : Vn 7 := ![2, 2, 2, 2, 0, 0, 0]
private lemma h17 : a17 ⬝ᵥ c17 = 2 := by decide +kernel
private def t17 : Vn 7 ≃ₗ[ZMod 3] Vn 7 := refl c17 a17 h17

private def c1 : Vn 7 := Pi.single 6 1
private def a1 : Vn 7 := oneN 7 + Pi.single 6 1
private lemma h1 : a1 ⬝ᵥ c1 = 2 := by decide +kernel

private def c5 : Vn 7 := oneN 7 + Pi.single 6 1
private def a5 : Vn 7 := Pi.single 6 1
private lemma h5 : a5 ⬝ᵥ c5 = 2 := by decide +kernel

private def c3 : Vn 7 := ![0, 0, 0, 1, 1, 1, 1]
private def a3 : Vn 7 := ![1, 1, 1, 2, 2, 2, 2]
private def z3 : Vn 7 := ![1, 1, 1, 2, 2, 2, 2]
private lemma h3 : a3 ⬝ᵥ c3 = 2 := by decide +kernel
private def t3 : Vn 7 ≃ₗ[ZMod 3] Vn 7 := refl c3 a3 h3

private lemma t17_one : t17 (oneN 7) = z17 := by
  rw [t17, refl_apply]
  decide +kernel

private lemma t3_one : t3 (oneN 7) = z3 := by
  rw [t3, refl_apply]
  decide +kernel

private lemma z17_ne : z17 ≠ 0 := by decide +kernel
private lemma z3_ne : z3 ≠ 0 := by decide +kernel

private lemma s17_dot : ∀ m : Fin 7,
    (oneN 7 + Pi.single m 1 : Vn 7) ⬝ᵥ Pi.single m 1 = 2 := by
  decide +kernel
private def s17 (m : Fin 7) : Vn 7 ≃ₗ[ZMod 3] Vn 7 :=
  refl (Pi.single m 1) (oneN 7 + Pi.single m 1) (s17_dot m)

private lemma s3_dot : ∀ m : Fin 7,
    (Pi.single m 1 : Vn 7) ⬝ᵥ (oneN 7 + Pi.single m 1) = 2 := by
  decide +kernel
private def s3 (m : Fin 7) : Vn 7 ≃ₗ[ZMod 3] Vn 7 :=
  refl (oneN 7 + Pi.single m 1) (Pi.single m 1) (s3_dot m)

private lemma t17_mul : t17 * t17 = 1 := refl_mul_self _ _ _
private lemma t3_mul : t3 * t3 = 1 := refl_mul_self _ _ _

private lemma check17 :
    ∀ m : Fin 7, ((oneN 7 + Pi.single m 1 : Vn 7) ⬝ᵥ c17 ≠ 0) →
      ¬ FixesLine (oneN 7) (t17 * s17 m * t17) ∧
      (∀ m' : Fin 7, ∃ j : Fin 7,
        (t17 * s17 m * t17) (Pi.single j 1) ≠ s17 m' (Pi.single j 1)) := by
  unfold FixesLine
  decide +kernel

private lemma check3 :
    ∀ m : Fin 7, ((Pi.single m 1 : Vn 7) ⬝ᵥ c3 ≠ 0) →
      ¬ FixesLine (oneN 7) (t3 * s3 m * t3) ∧
      (∀ m' : Fin 7, ∃ j : Fin 7,
        (t3 * s3 m * t3) (Pi.single j 1) ≠ s3 m' (Pi.single j 1)) := by
  unfold FixesLine
  decide +kernel

private lemma check17_ii :
    ∀ a : Vn 7, (∀ i j : Fin 7, a i = a j ↔ z17 i = z17 j) →
      a ⬝ᵥ (oneN 7) = 0 → a ⬝ᵥ c17 = 0 := by
  decide +kernel

private lemma check17_iii :
    ∀ a : Vn 7, (∀ i j : Fin 7, a i = a j) →
      a ⬝ᵥ z17 = 0 → a ⬝ᵥ c17 = 0 := by
  decide +kernel

private lemma check17_iv :
    ∀ μ ν : ZMod 3, μ • (oneN 7) = ν • z17 → μ = 0 := by
  decide +kernel

private lemma check17_noconst :
    ∀ S : Finset (Fin 7), 5 ≤ S.card → ∃ a ∈ S, ∃ b ∈ S, c17 a ≠ c17 b := by
  decide +kernel

private lemma check3_ii :
    ∀ a : Vn 7, (∀ i j : Fin 7, a i = a j ↔ z3 i = z3 j) →
      a ⬝ᵥ (oneN 7) = 0 → a ⬝ᵥ c3 = 0 := by
  decide +kernel

private lemma check3_iii :
    ∀ a : Vn 7, (∀ i j : Fin 7, a i = a j) →
      a ⬝ᵥ z3 = 0 → a ⬝ᵥ c3 = 0 := by
  decide +kernel

private lemma check3_iv :
    ∀ μ ν : ZMod 3, μ • (oneN 7) = ν • z3 → μ = 0 := by
  decide +kernel

private lemma check3_noconst :
    ∀ S : Finset (Fin 7), 5 ≤ S.card → ∃ a ∈ S, ∃ b ∈ S, c3 a ≠ c3 b := by
  decide +kernel

private lemma dot_zero_or_center_of_fixesLine {n : ℕ} {v c a : Vn n}
    (hv : v ≠ 0) (hac : a ⬝ᵥ c = 2)
    (hfix : FixesLine v (refl c a hac)) :
    a ⬝ᵥ v = 0 ∨ ∃ μ : ZMod 3, c = μ • v := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hac
    exact (by decide : (2 : ZMod 3) ≠ 0) hac.symm
  have hmul : ∀ x y : ZMod 3, x * y = 0 → x = 0 ∨ y = 0 := by decide +kernel
  rcases hfix with h | h
  · left
    have h' : (a ⬝ᵥ v) • c = 0 := by
      funext i
      have hi := congrFun h i
      simp only [refl_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [sub_eq_self] at hi
      exact hi
    by_contra hs
    apply hc0
    funext i
    have hi := congrFun h' i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    rcases hmul _ _ hi with h0 | h0
    · exact absurd h0 hs
    · exact h0
  · right
    have h2 : (a ⬝ᵥ v) • c = (2 : ZMod 3) • v := by
      funext i
      have hi := congrFun h i
      simp only [refl_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at hi ⊢
      have h1 : v i = -v i + a ⬝ᵥ v * c i := by
        rw [← hi]
        ring
      have h2i : a ⬝ᵥ v * c i = v i + v i := by
        have h := congrArg (fun t => t + v i) h1
        have h' : (-v i + a ⬝ᵥ v * c i) + v i = a ⬝ᵥ v * c i := by ring
        rw [h'] at h
        exact h.symm
      rw [h2i]
      ring
    rcases (by decide : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 2) (a ⬝ᵥ v)
      with hs | hs | hs
    · rw [hs, zero_smul] at h2
      exfalso
      apply hv
      funext i
      have hi := congrFun h2 i
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hi
      exact (by decide : ∀ x : ZMod 3, (2 : ZMod 3) * x = 0 → x = 0) (v i) hi.symm
    · refine ⟨2, ?_⟩
      rw [hs, one_smul] at h2
      exact h2
    · refine ⟨1, ?_⟩
      rw [hs] at h2
      have := congrArg (fun w => (2 : ZMod 3) • w) h2
      simpa [smul_smul, show (2 : ZMod 3) * 2 = 1 by decide +kernel] using this


private lemma a7f_K_core {W A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)}
    {x : Vn 7} (hT : TestHyp W x A Mg)
    (hperm : permGroup 7 ≤ W)
    {t : Vn 7 ≃ₗ[ZMod 3] Vn 7} (_htR : IsRefl t)
    {c_t a_t : Vn 7} (ht2 : a_t ⬝ᵥ c_t = 2) (ht_eq : t = refl c_t a_t ht2)
    (ht_inv : t * t = 1)
    {R : Set (Vn 7 ≃ₗ[ZMod 3] Vn 7)} (hRrefl : ∀ s ∈ R, IsRefl s)
    (hRle : Subgroup.closure R ≤ Mg)
    (hNorm : ∀ h ∈ Subgroup.closure R, t * h * t⁻¹ ∈ Subgroup.closure R)
    (s : Fin 7 → Vn 7 ≃ₗ[ZMod 3] Vn 7)
    (cs as : Fin 7 → Vn 7)
    (hs2 : ∀ m : Fin 7, as m ⬝ᵥ cs m = 2)
    (hs_eq : ∀ m, s m = refl (cs m) (as m) (hs2 m))
    (hA : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine x s' → ∃ m, s' = s m)
    (hB : ∀ m : Fin 7, as m ⬝ᵥ c_t ≠ 0 → ¬ FixesLine x (t * s m * t) ∧
      ∀ m' : Fin 7, ∃ j : Fin 7,
        (t * s m * t) (Pi.single j 1) ≠ s m' (Pi.single j 1))
    (hD2 : ∀ (c a : Vn 7) (hac : a ⬝ᵥ c = 2), (∀ i j : Fin 7, a i = a j ↔ c i = c j) →
      FixesLine x (refl c a hac) → FixesLine (t x) (refl c a hac) → a ⬝ᵥ c_t = 0)
    {S : Finset (Fin 7)} (hScard : 5 ≤ S.card)
    (hSconst : ∀ v : Vn 7, (∀ h ∈ Subgroup.closure R, h v = v) →
      ∀ a ∈ S, ∀ b ∈ S, v a = v b)
    (hNoConst : ¬ ∃ S' : Finset (Fin 7), 5 ≤ S'.card ∧
      ∀ a ∈ S', ∀ b ∈ S', c_t a = c_t b) :
    False := by
  have ht_inv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_inv
  have ht_sq : ∀ v : Vn 7, t (t v) = v := by
    intro v
    have := congrArg (fun f => f v) ht_inv
    simpa [LinearEquiv.mul_apply] using this
  have ht_ct : t c_t = -c_t := by
    rw [ht_eq, refl_apply, ht2]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  have hmul : ∀ x y : ZMod 3, x * y = 0 → x = 0 ∨ y = 0 := by decide +kernel
  have hC : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine x s' → s' c_t = c_t := by
    intro s' hs'H hs'R hs'move
    obtain ⟨m, hm⟩ := hA s' hs'H hs'R hs'move
    have hsR : IsRefl (s m) := by
      rw [hs_eq m]; exact ⟨_, _, hs2 m, fun v => by rw [refl_apply]⟩
    have hdot : as m ⬝ᵥ c_t = 0 := by
      by_contra hne
      have hBm := hB m hne
      have hconjH : t * s' * t ∈ Subgroup.closure R := by
        have h := hNorm s' hs'H
        rwa [ht_inv'] at h
      have hconjR : IsRefl (t * s' * t) := by
        rw [hm]
        have h := isRefl_conj (g := s m) (κ := t) hsR
        rwa [ht_inv'] at h
      have hconjmove : ¬ FixesLine x (t * s' * t) := by
        rw [hm]
        exact hBm.1
      obtain ⟨m', hm'⟩ := hA _ hconjH hconjR hconjmove
      obtain ⟨j, hj⟩ := hBm.2 m'
      rw [← hm'] at hj
      rw [hm] at hj
      exact hj rfl
    rw [hm, hs_eq m, refl_apply, hdot, zero_smul, sub_zero]
  have hD : ∀ u ∈ Subgroup.closure R, IsRefl u → FixesLine x u → u c_t = c_t := by
    intro u huH huR hu_fix
    obtain ⟨c, a, hac, hu_eq⟩ := eq_refl_of_isRefl huR
    by_contra hne
    have hdot : a ⬝ᵥ c_t ≠ 0 := by
      intro h0
      apply hne
      rw [hu_eq, refl_apply, h0, zero_smul, sub_zero]
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, dotProduct_zero] at hac
      exact (by decide : (2 : ZMod 3) ≠ 0) hac.symm
    have hu_moves_ct : u c_t ≠ c_t := by
      rw [hu_eq, refl_apply]
      intro h0
      have h' : (a ⬝ᵥ c_t) • c = 0 := by
        funext i
        have hi := congrFun h0 i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
        rw [sub_eq_self] at hi
        exact hi
      exfalso
      apply hc0
      funext i
      have hi := congrFun h' i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      rcases hmul _ _ hi with h0 | h0
      · exact absurd h0 hdot
      · exact h0
    have hu_moves_t : u (t c_t) ≠ t c_t := by
      rw [ht_ct, map_neg]
      intro h0
      exact hu_moves_ct (neg_inj.mp h0)
    have hu'_H : t * u * t ∈ Subgroup.closure R := by
      have h := hNorm u huH
      rwa [ht_inv'] at h
    have hu'_R : IsRefl (t * u * t) := by
      rw [hu_eq]
      have h := isRefl_conj (g := refl c a hac) (κ := t) ⟨c, a, hac, fun v => by rw [refl_apply]⟩
      rwa [ht_inv'] at h
    have hu'_ne : (t * u * t) c_t ≠ c_t := by
      intro heq
      apply hu_moves_t
      have := congrArg t heq
      simpa [LinearEquiv.mul_apply, ht_sq] using this
    by_cases hu'_fix : FixesLine x (t * u * t)
    · have hfixz : FixesLine (t x) u := by
        have hu_eq' : u = t * (t * u * t) * t := by
          calc u = (t * t) * u * (t * t) := by rw [ht_inv, one_mul, mul_one]
            _ = t * (t * u * t) * t := by group
        rw [hu_eq']
        unfold FixesLine
        have happ : (t * (t * u * t) * t) (t x) = t ((t * u * t) x) := by
          change t ((t * u * t) (t (t x))) = t ((t * u * t) x)
          rw [ht_sq]
        rw [happ]
        rcases hu'_fix with h | h
        · left; rw [h]
        · right; rw [h, map_neg]
      have huA : u ∈ A := hT.le (hRle huH)
      have huA' : refl c a hac ∈ A := hu_eq ▸ huA
      have hsym : ∀ i j : Fin 7, a i = a j ↔ c i = c j := fun i j =>
        TestHyp.sym_perm hperm hT huA' i j
      exact hdot (hD2 c a hac hsym (hu_eq ▸ hu_fix) (hu_eq ▸ hfixz))
    · obtain ⟨m, hm⟩ := hA _ hu'_H hu'_R hu'_fix
      have hdotm : as m ⬝ᵥ c_t ≠ 0 := by
        intro h0
        apply hu'_ne
        rw [hm, hs_eq m, refl_apply, h0, zero_smul, sub_zero]
      have hEq : t * s m * t = u := by
        rw [← hm]
        calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
          _ = u := by rw [ht_inv, one_mul, mul_one]
      have hfix' : FixesLine x (t * s m * t) := by rwa [← hEq] at hu_fix
      exact (hB m hdotm).1 hfix'
  have hRfix : ∀ s' ∈ R, s' c_t = c_t := by
    intro s' hs'
    by_cases hfix : FixesLine x s'
    · exact hD s' (Subgroup.subset_closure hs') (hRrefl s' hs') hfix
    · exact hC s' (Subgroup.subset_closure hs') (hRrefl s' hs') hfix
  have hHfix : ∀ h ∈ Subgroup.closure R, h c_t = c_t := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem s' hs' => exact hRfix s' hs'
    | one => rfl
    | mul a b ha hb iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
    | inv a ha iha =>
        apply a.injective
        change a ((LinearEquiv.symm a) c_t) = a c_t
        rw [LinearEquiv.apply_symm_apply, iha]
  exact hNoConst ⟨S, hScard, fun a ha b hb => hSconst c_t hHfix a ha b hb⟩


private lemma conj_refl_c1 (σ : Equiv.Perm (Fin 7)) :
    permN σ⁻¹ * refl c1 a1 h1 * (permN σ⁻¹)⁻¹ = s17 (σ.symm 6) := by
  rw [permN_conj_refl]
  have hc : c1 ∘ (σ⁻¹).symm = Pi.single (σ.symm 6) 1 := by
    rw [show (σ⁻¹).symm = σ from rfl]
    funext i
    rw [c1, Function.comp_apply, Pi.single_apply, Pi.single_apply]
    by_cases h : σ i = 6
    · rw [if_pos h, if_pos ((Equiv.eq_symm_apply σ).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((Equiv.eq_symm_apply σ).mp h'))]
  have ha : a1 ∘ (σ⁻¹).symm = oneN 7 + Pi.single (σ.symm 6) 1 := by
    rw [show (σ⁻¹).symm = σ from rfl]
    funext i
    rw [a1, Function.comp_apply]
    simp only [Pi.add_apply, Pi.single_apply, oneN]
    by_cases h : σ i = 6
    · rw [if_pos h, if_pos ((Equiv.eq_symm_apply σ).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((Equiv.eq_symm_apply σ).mp h'))]
  change refl (c1 ∘ (σ⁻¹).symm) (a1 ∘ (σ⁻¹).symm) _ =
    refl (Pi.single (σ.symm 6) 1) (oneN 7 + Pi.single (σ.symm 6) 1) (s17_dot _)
  exact refl_congr hc ha _ _

private lemma a7f_A17 {A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)}
    (hT : TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg)
    (hWleP : Subgroup.closure (Set.range a7fS) ≤ permGroup 7)
    (hgW : ∀ l ∈ a7fGens, letLin l ∈ Subgroup.closure (Set.range a7fS))
    (hWgen : Subgroup.closure (Set.range a7fS) ≤
      Subgroup.closure {g | ∃ l ∈ a7fGens, g = letLin l})
    (hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine (oneN 7) u → ∃ w ∈ Subgroup.closure (Set.range a7fS),
      ∃ i < a7fReps.length, ∃ h : (letAt a7fReps i).2 ⬝ᵥ (letAt a7fReps i).1 = 2,
        w * u * w⁻¹ = refl (letAt a7fReps i).1 (letAt a7fReps i).2 h)
    {R : Set (Vn 7 ≃ₗ[ZMod 3] Vn 7)} (hRle : Subgroup.closure R ≤ Mg)
    (_hiM : refl c1 a1 h1 ∈ Mg) (htA : t17 ∈ A) (htM : t17 ∉ Mg)
    {s' : Vn 7 ≃ₗ[ZMod 3] Vn 7} (hsH : s' ∈ Subgroup.closure R)
    (hsR : IsRefl s') (hsmove : ¬ FixesLine (oneN 7) s') :
    ∃ m : Fin 7, s' = s17 m := by
  have hReps1 : letAt a7fReps 1 = (c1, a1) := by decide +kernel
  have hReps7 : letAt a7fReps 7 = (c17, a17) := by decide +kernel
  have h7len : 7 < a7fReps.length := by decide +kernel
  obtain ⟨w, hw, k, hk, hrep, hwsk⟩ := hcls s' (hT.le (hRle hsH)) hsR hsmove
  by_cases hk1 : k = 1
  · subst k
    have hrep1 : a1 ⬝ᵥ c1 = 2 := by simpa [hReps1] using hrep
    have hwsk1 : w * s' * w⁻¹ = refl c1 a1 h1 := by
      rw [hwsk]
      exact refl_congr (congrArg Prod.fst hReps1) (congrArg Prod.snd hReps1) hrep h1
    have hwW : w ∈ permGroup 7 := hWleP hw
    obtain ⟨σ, rfl⟩ := hwW
    refine ⟨σ.symm 6, ?_⟩
    have hs_eq : s' = permN σ⁻¹ * refl c1 a1 h1 * (permN σ⁻¹)⁻¹ := by
      have h1eq : s' = (permN σ)⁻¹ * refl c1 a1 h1 * permN σ := by
        rw [← hwsk1]
        change s' = (permN σ)⁻¹ * permN σ * s' * (permN σ)⁻¹ * permN σ
        group
      rw [h1eq, permN_inv σ]
      rw [show permN σ = permN ((σ⁻¹)⁻¹) from congrArg permN (Equiv.symm_symm σ).symm]
      rw [← permN_inv (σ⁻¹)]
    rw [hs_eq]
    exact conj_refl_c1 σ
  · have hk7 : (k, 7) ∉ a7fGiven := by
      simp [a7fGiven]
      omega
    have h7rep : (letAt a7fReps 7).2 ⬝ᵥ (letAt a7fReps 7).1 = 2 := by
      simpa [hReps7] using h17
    have hrM : refl (letAt a7fReps k).1 (letAt a7fReps k).2 hrep ∈ Mg := by
      rw [← hwsk]
      exact Mg.mul_mem (Mg.mul_mem (hT.W_le hw) (hRle hsH)) (Mg.inv_mem (hT.W_le hw))
    have htM' := TestHyp.mem_of_s2_of_certOKGiven hT a7f_certOK hgW hWgen hk h7len hk7
      hrep h7rep hrM htA
    exact absurd htM' htM



private lemma mul_left_inj3 : ∀ x y ν : ZMod 3, ν ≠ 0 → (ν * x = ν * y ↔ x = y) := by
  decide +kernel

private lemma hD2_17 (c a : Vn 7) (hac : a ⬝ᵥ c = 2)
    (hsym : ∀ i j : Fin 7, a i = a j ↔ c i = c j)
    (hfix1 : FixesLine (oneN 7) (refl c a hac))
    (hfixz : FixesLine (t17 (oneN 7)) (refl c a hac)) :
    a ⬝ᵥ c17 = 0 := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hac
    exact (by decide : (2 : ZMod 3) ≠ 0) hac.symm
  have hfixz' : FixesLine z17 (refl c a hac) := by
    rwa [t17_one] at hfixz
  have h1 := dot_zero_or_center_of_fixesLine (by decide : (oneN 7 : Vn 7) ≠ 0) hac hfix1
  have h2 := dot_zero_or_center_of_fixesLine z17_ne hac hfixz'
  rcases h1 with h1 | ⟨μ, hμ⟩
  · rcases h2 with h2 | ⟨ν, hν⟩
    · have hz : z17 = oneN 7 + c17 := by decide +kernel
      rw [hz, dotProduct_add, h1, zero_add] at h2
      exact h2
    · have hν0 : ν ≠ 0 := by
        intro h
        apply hc0
        rw [hν, h, zero_smul]
      have hlev : ∀ i j : Fin 7, a i = a j ↔ z17 i = z17 j := by
        intro i j
        rw [hsym i j, hν]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_left_inj3 _ _ _ hν0
      exact check17_ii a hlev h1
  · rcases h2 with h2 | ⟨ν, hν⟩
    · have hconst : ∀ i j : Fin 7, a i = a j := by
        intro i j
        rw [hsym i j, hμ]
        simp [oneN]
      exact check17_iii a hconst h2
    · have hvec : μ • (oneN 7) = ν • z17 := by
        rw [← hμ, hν]
      have hmu0 := check17_iv μ ν hvec
      exfalso
      exact hc0 (by rw [hμ, hmu0, zero_smul])



private lemma test_pair17 {A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)}
    (hT : TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg)
    (hgW : ∀ l ∈ a7fGens, letLin l ∈ Subgroup.closure (Set.range a7fS))
    (hWgen : Subgroup.closure (Set.range a7fS) ≤
      Subgroup.closure {g | ∃ l ∈ a7fGens, g = letLin l})
    (hiM : refl c1 a1 h1 ∈ Mg) (hjA : t17 ∈ A)
    (hK : a7fK Mg t17) (htM : t17 ∉ Mg) : False := by
  have hperm : permGroup 7 ≤ Subgroup.closure (Set.range a7fS) :=
    permGroup_le_of_gens a7fS a7fGens (fun _ => rfl) (by norm_num) a7f_adj
  have hWleP : Subgroup.closure (Set.range a7fS) ≤ permGroup 7 :=
    closure_a7fS_le_permGroup
  have hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine (oneN 7) u →
      ∃ w ∈ Subgroup.closure (Set.range a7fS), ∃ i < a7fReps.length,
        ∃ h : (letAt a7fReps i).2 ⬝ᵥ (letAt a7fReps i).1 = 2,
          w * u * w⁻¹ = refl (letAt a7fReps i).1 (letAt a7fReps i).2 h :=
    TestHyp.exists_cls_of_certOKGiven hT a7f_certOK hgW hWgen (hT.perm_cover hperm a7f_cov)
  obtain ⟨R, hRrefl, hRle, hNorm, hMove, S, hScard, hSconst⟩ := hK
  have hA : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine (oneN 7) s' →
      ∃ m : Fin 7, s' = s17 m :=
    fun s' hsH hsR hsmove => a7f_A17 hT hWleP hgW hWgen hcls hRle hiM hjA htM hsH hsR hsmove
  have hNoConst : ¬ ∃ S' : Finset (Fin 7), 5 ≤ S'.card ∧
      ∀ a ∈ S', ∀ b ∈ S', c17 a = c17 b := by
    rintro ⟨S', hS', hconst⟩
    obtain ⟨a, ha, b, hb, hab⟩ := check17_noconst S' hS'
    exact hab (hconst a ha b hb)
  exact a7f_K_core hT hperm ⟨c17, a17, h17, fun v => by rw [refl_apply]⟩ h17 rfl t17_mul
    hRrefl hRle hNorm s17 (fun m => Pi.single m 1) (fun m => oneN 7 + Pi.single m 1)
    s17_dot (fun _ => rfl) hA check17 hD2_17 hScard hSconst hNoConst



private lemma conj_refl_c5 (σ : Equiv.Perm (Fin 7)) :
    permN σ⁻¹ * refl c5 a5 h5 * (permN σ⁻¹)⁻¹ = s3 (σ.symm 6) := by
  rw [permN_conj_refl]
  have hc : c5 ∘ (σ⁻¹).symm = oneN 7 + Pi.single (σ.symm 6) 1 := by
    rw [show (σ⁻¹).symm = σ from rfl]
    funext i
    rw [c5, Function.comp_apply]
    simp only [Pi.add_apply, Pi.single_apply, oneN]
    by_cases h : σ i = 6
    · rw [if_pos h, if_pos ((Equiv.eq_symm_apply σ).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((Equiv.eq_symm_apply σ).mp h'))]
  have ha : a5 ∘ (σ⁻¹).symm = Pi.single (σ.symm 6) 1 := by
    rw [show (σ⁻¹).symm = σ from rfl]
    funext i
    rw [a5, Function.comp_apply, Pi.single_apply, Pi.single_apply]
    by_cases h : σ i = 6
    · rw [if_pos h, if_pos ((Equiv.eq_symm_apply σ).mpr h)]
    · rw [if_neg h, if_neg (fun h' => h ((Equiv.eq_symm_apply σ).mp h'))]
  change refl (c5 ∘ (σ⁻¹).symm) (a5 ∘ (σ⁻¹).symm) _ =
    refl (oneN 7 + Pi.single (σ.symm 6) 1) (Pi.single (σ.symm 6) 1) (s3_dot _)
  exact refl_congr hc ha _ _

private lemma hD2_3 (c a : Vn 7) (hac : a ⬝ᵥ c = 2)
    (hsym : ∀ i j : Fin 7, a i = a j ↔ c i = c j)
    (hfix1 : FixesLine (oneN 7) (refl c a hac))
    (hfixz : FixesLine (t3 (oneN 7)) (refl c a hac)) :
    a ⬝ᵥ c3 = 0 := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, dotProduct_zero] at hac
    exact (by decide : (2 : ZMod 3) ≠ 0) hac.symm
  have hfixz' : FixesLine z3 (refl c a hac) := by
    rwa [t3_one] at hfixz
  have hd1 := dot_zero_or_center_of_fixesLine (by decide : (oneN 7 : Vn 7) ≠ 0) hac hfix1
  have hdz := dot_zero_or_center_of_fixesLine z3_ne hac hfixz'
  rcases hd1 with hd1 | ⟨μ, hμ⟩
  · rcases hdz with hdz | ⟨ν, hν⟩
    · have hz : z3 = oneN 7 + c3 := by decide +kernel
      rw [hz, dotProduct_add, hd1, zero_add] at hdz
      exact hdz
    · have hν0 : ν ≠ 0 := by
        intro h
        apply hc0
        rw [hν, h, zero_smul]
      have hlev : ∀ i j : Fin 7, a i = a j ↔ z3 i = z3 j := by
        intro i j
        rw [hsym i j, hν]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_left_inj3 _ _ _ hν0
      exact check3_ii a hlev hd1
  · rcases hdz with hdz | ⟨ν, hν⟩
    · have hconst : ∀ i j : Fin 7, a i = a j := by
        intro i j
        rw [hsym i j, hμ]
        simp [oneN]
      exact check3_iii a hconst hdz
    · have hvec : μ • (oneN 7) = ν • z3 := by
        rw [← hμ, hν]
      have hmu0 := check3_iv μ ν hvec
      exfalso
      exact hc0 (by rw [hμ, hmu0, zero_smul])

private lemma a7f_A53 {A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)}
    (hT : TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg)
    (hWleP : Subgroup.closure (Set.range a7fS) ≤ permGroup 7)
    (hgW : ∀ l ∈ a7fGens, letLin l ∈ Subgroup.closure (Set.range a7fS))
    (hWgen : Subgroup.closure (Set.range a7fS) ≤
      Subgroup.closure {g | ∃ l ∈ a7fGens, g = letLin l})
    (hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine (oneN 7) u → ∃ w ∈ Subgroup.closure (Set.range a7fS),
      ∃ i < a7fReps.length, ∃ h : (letAt a7fReps i).2 ⬝ᵥ (letAt a7fReps i).1 = 2,
        w * u * w⁻¹ = refl (letAt a7fReps i).1 (letAt a7fReps i).2 h)
    {R : Set (Vn 7 ≃ₗ[ZMod 3] Vn 7)} (hRle : Subgroup.closure R ≤ Mg)
    (_hiM : refl c5 a5 h5 ∈ Mg) (htA : t3 ∈ A) (htM : t3 ∉ Mg)
    {s' : Vn 7 ≃ₗ[ZMod 3] Vn 7} (hsH : s' ∈ Subgroup.closure R)
    (hsR : IsRefl s') (hsmove : ¬ FixesLine (oneN 7) s') :
    ∃ m : Fin 7, s' = s3 m := by
  have hReps5 : letAt a7fReps 5 = (c5, a5) := by decide +kernel
  have hReps3 : letAt a7fReps 3 = (c3, a3) := by decide +kernel
  have h3len : 3 < a7fReps.length := by decide +kernel
  obtain ⟨w, hw, k, hk, hrep, hwsk⟩ := hcls s' (hT.le (hRle hsH)) hsR hsmove
  by_cases hk5 : k = 5
  · subst k
    have hwsk1 : w * s' * w⁻¹ = refl c5 a5 h5 := by
      rw [hwsk]
      exact refl_congr (congrArg Prod.fst hReps5) (congrArg Prod.snd hReps5) hrep h5
    have hwW : w ∈ permGroup 7 := hWleP hw
    obtain ⟨σ, rfl⟩ := hwW
    refine ⟨σ.symm 6, ?_⟩
    have hs_eq : s' = permN σ⁻¹ * refl c5 a5 h5 * (permN σ⁻¹)⁻¹ := by
      have h1eq : s' = (permN σ)⁻¹ * refl c5 a5 h5 * permN σ := by
        rw [← hwsk1]
        change s' = (permN σ)⁻¹ * permN σ * s' * (permN σ)⁻¹ * permN σ
        group
      rw [h1eq, permN_inv σ]
      rw [show permN σ = permN ((σ⁻¹)⁻¹) from congrArg permN (Equiv.symm_symm σ).symm]
      rw [← permN_inv (σ⁻¹)]
    rw [hs_eq]
    exact conj_refl_c5 σ
  · have hk3 : (k, 3) ∉ a7fGiven := by
      simp [a7fGiven]
      omega
    have h3rep : (letAt a7fReps 3).2 ⬝ᵥ (letAt a7fReps 3).1 = 2 := by
      simpa [hReps3] using h3
    have hrM : refl (letAt a7fReps k).1 (letAt a7fReps k).2 hrep ∈ Mg := by
      rw [← hwsk]
      exact Mg.mul_mem (Mg.mul_mem (hT.W_le hw) (hRle hsH)) (Mg.inv_mem (hT.W_le hw))
    have htM' := TestHyp.mem_of_s2_of_certOKGiven hT a7f_certOK hgW hWgen hk h3len hk3
      hrep h3rep hrM htA
    exact absurd htM' htM

private lemma test_pair53 {A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7)}
    (hT : TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg)
    (hgW : ∀ l ∈ a7fGens, letLin l ∈ Subgroup.closure (Set.range a7fS))
    (hWgen : Subgroup.closure (Set.range a7fS) ≤
      Subgroup.closure {g | ∃ l ∈ a7fGens, g = letLin l})
    (hiM : refl c5 a5 h5 ∈ Mg) (hjA : t3 ∈ A)
    (hK : a7fK Mg t3) (htM : t3 ∉ Mg) : False := by
  have hperm : permGroup 7 ≤ Subgroup.closure (Set.range a7fS) :=
    permGroup_le_of_gens a7fS a7fGens (fun _ => rfl) (by norm_num) a7f_adj
  have hWleP : Subgroup.closure (Set.range a7fS) ≤ permGroup 7 :=
    closure_a7fS_le_permGroup
  have hcls : ∀ u ∈ A, IsRefl u → ¬ FixesLine (oneN 7) u →
      ∃ w ∈ Subgroup.closure (Set.range a7fS), ∃ i < a7fReps.length,
        ∃ h : (letAt a7fReps i).2 ⬝ᵥ (letAt a7fReps i).1 = 2,
          w * u * w⁻¹ = refl (letAt a7fReps i).1 (letAt a7fReps i).2 h :=
    TestHyp.exists_cls_of_certOKGiven hT a7f_certOK hgW hWgen (hT.perm_cover hperm a7f_cov)
  obtain ⟨R, hRrefl, hRle, hNorm, hMove, S, hScard, hSconst⟩ := hK
  have hA : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine (oneN 7) s' →
      ∃ m : Fin 7, s' = s3 m :=
    fun s' hsH hsR hsmove => a7f_A53 hT hWleP hgW hWgen hcls hRle hiM hjA htM hsH hsR hsmove
  have hNoConst : ¬ ∃ S' : Finset (Fin 7), 5 ≤ S'.card ∧
      ∀ a ∈ S', ∀ b ∈ S', c3 a = c3 b := by
    rintro ⟨S', hS', hconst⟩
    obtain ⟨a, ha, b, hb, hab⟩ := check3_noconst S' hS'
    exact hab (hconst a ha b hb)
  exact a7f_K_core hT hperm ⟨c3, a3, h3, fun v => by rw [refl_apply]⟩ h3 rfl t3_mul
    hRrefl hRle hNorm s3 (fun m => oneN 7 + Pi.single m 1) (fun m => Pi.single m 1)
    s3_dot (fun _ => rfl) hA check3 hD2_3 hScard hSconst hNoConst

theorem a7f_given_K : ∀ A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7),
    TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg →
    ∀ i j, (i, j) ∈ a7fGiven → ∀ (hi : (letAt a7fReps i).2 ⬝ᵥ (letAt a7fReps i).1 = 2)
      (hj : (letAt a7fReps j).2 ⬝ᵥ (letAt a7fReps j).1 = 2),
      refl (letAt a7fReps i).1 (letAt a7fReps i).2 hi ∈ Mg →
      refl (letAt a7fReps j).1 (letAt a7fReps j).2 hj ∈ A →
      a7fK Mg (refl (letAt a7fReps j).1 (letAt a7fReps j).2 hj) →
      refl (letAt a7fReps j).1 (letAt a7fReps j).2 hj ∈ Mg := by
  intro A Mg hT i j hij hi hj hiM hjA hK
  by_contra htM
  have hlen : a7fGens.length = 6 := rfl
  have hS : ∀ k : Fin 6, a7fS k = letLin (letAt a7fGens k) := fun _ => rfl
  have hgW : ∀ l ∈ a7fGens, letLin l ∈ Subgroup.closure (Set.range a7fS) := by
    rw [List.forall_mem_iff_get]
    intro k
    have hk6 : (k : ℕ) < 6 := by omega
    have hget : letAt a7fGens (k : ℕ) = a7fGens.get k := by
      unfold letAt
      rw [List.getD_eq_getElem _ _ k.isLt]
      rfl
    rw [← hget]
    change a7fS ⟨(k : ℕ), hk6⟩ ∈ Subgroup.closure (Set.range a7fS)
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range a7fS) ≤
      Subgroup.closure {g | ∃ l ∈ a7fGens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨letAt a7fGens k, ?_, hS k⟩
    have hk : k.val < a7fGens.length := by omega
    rw [show letAt a7fGens k = a7fGens[k.val] from List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have hReps1 : letAt a7fReps 1 = (c1, a1) := by decide +kernel
  have hReps7 : letAt a7fReps 7 = (c17, a17) := by decide +kernel
  have hReps5 : letAt a7fReps 5 = (c5, a5) := by decide +kernel
  have hReps3 : letAt a7fReps 3 = (c3, a3) := by decide +kernel
  simp only [a7fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hiM' : refl c1 a1 h1 ∈ Mg := by
      rw [← refl_congr (congrArg Prod.fst hReps1) (congrArg Prod.snd hReps1) hi h1]
      exact hiM
    have hjA' : t17 ∈ A := by
      change refl c17 a17 h17 ∈ A
      rw [← refl_congr (congrArg Prod.fst hReps7) (congrArg Prod.snd hReps7) hj h17]
      exact hjA
    exact test_pair17 hT hgW hWgen hiM' hjA' hK htM
  · have hiM' : refl c5 a5 h5 ∈ Mg := by
      rw [← refl_congr (congrArg Prod.fst hReps5) (congrArg Prod.snd hReps5) hi h5]
      exact hiM
    have hjA' : t3 ∈ A := by
      change refl c3 a3 h3 ∈ A
      rw [← refl_congr (congrArg Prod.fst hReps3) (congrArg Prod.snd hReps3) hj h3]
      exact hjA
    exact test_pair53 hT hgW hWgen hiM' hjA' hK htM


theorem a7f_test_K : ∀ A Mg : Subgroup (Vn 7 ≃ₗ[ZMod 3] Vn 7),
    TestHyp (Subgroup.closure (Set.range a7fS)) (oneN 7) A Mg →
    ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (oneN 7) r →
    ∀ t ∈ A, IsRefl t → ¬ FixesLine (oneN 7) t → a7fK Mg t → t ∈ Mg := by
  intro A Mg hT
  refine linTest_perm_of_certOKGiven_of a7fS a7fGens rfl (fun _ => rfl)
    (permGroup_le_of_gens a7fS a7fGens (fun _ => rfl) (by norm_num) a7f_adj)
    a7f_certOK a7f_cov (a7fK Mg) (fun w hw u hu => ?_) A Mg hT
    (fun i j hij hi hj hiM hjA hP => a7f_given_K A Mg hT i j hij hi hj hiM hjA hP)
  obtain ⟨σ, rfl⟩ := closure_a7fS_le_permGroup hw
  exact a7fK_conj σ (hT.W_le hw) hu

end CFSG.StandardType.TestLin

end
