module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CertD7Full
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestCertK

public section

namespace CFSG.StandardType.TestLin

open Matrix

attribute [-instance] Nat.fact_prime_three

variable {r : ℕ}

theorem linTest_dframe_of_certOKGiven_of (hr : 3 ≤ r) {ℓ : ℕ}
    (S : Fin ℓ → (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)))
    (gens : List (Vn (r + 1) × Vn (r + 1))) (hlen : gens.length = ℓ)
    (hS : ∀ k : Fin ℓ, S k = letLin (letAt gens k))
    {L : List ((Vn (r + 1) × Vn (r + 1)) × List ℕ × ℕ)} (hL : reflCertB gens L = true)
    (hF : dFrameB r L = true) {sets : List (List (Vn (r + 1)))}
    {pats : List ((Vn (r + 1) × Vn (r + 1)) × PatV (r + 1))} {reps : List (Vn (r + 1) × Vn (r + 1))}
    {s2 : List (S2V (r + 1))} {gp : List (ℕ × ℕ)}
    (hOK : certOKGiven gens (xLast r) sets pats reps s2 gp = true)
    (hcov : dCovB r pats = true) (P : (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)) → Prop)
    (hPW : ∀ w ∈ Subgroup.closure (Set.range S), ∀ u, P u → P (w * u * w⁻¹)) :
    ∀ A Mg : Subgroup (Vn (r + 1) ≃ₗ[ZMod 3] Vn (r + 1)),
      TestHyp (Subgroup.closure (Set.range S)) (xLast r) A Mg →
      (∀ i j, (i, j) ∈ gp → ∀ (hi : (letAt reps i).2 ⬝ᵥ (letAt reps i).1 = 2)
        (hj : (letAt reps j).2 ⬝ᵥ (letAt reps j).1 = 2),
        refl (letAt reps i).1 (letAt reps i).2 hi ∈ Mg →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ A →
        P (refl (letAt reps j).1 (letAt reps j).2 hj) →
        refl (letAt reps j).1 (letAt reps j).2 hj ∈ Mg) →
      ∀ t₁ ∈ Mg, IsRefl t₁ → ¬ FixesLine (xLast r) t₁ →
      ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast r) t → P t → t ∈ Mg := by
  intro A Mg hT hgiven r' hr' hrR hrx t ht htR htx hPt
  have hgens : AlphOK gens := by
    unfold certOKGiven at hOK
    simp only [Bool.and_eq_true] at hOK
    exact AlphOK.of_all hOK.1.1.1.1
  have hgW : ∀ l ∈ gens, letLin l ∈ Subgroup.closure (Set.range S) := by
    intro l hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hl
    have hl' : letAt gens k = gens[k] := List.getD_eq_getElem _ _ hk
    rw [← hl', ← hS ⟨k, hlen ▸ hk⟩]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  have hWgen : Subgroup.closure (Set.range S) ≤
      Subgroup.closure {g | ∃ l ∈ gens, g = letLin l} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨letAt gens k, ?_, hS k⟩
    have hk : k.val < gens.length := hlen ▸ k.isLt
    rw [show letAt gens k = gens[k.val] from List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  unfold dFrameB at hF
  rw [decide_eq_true_eq] at hF
  have hW : ∀ (i j : Fin r) (h : i ≠ j), sgnDiff i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnDiff_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).1
  have hWs : ∀ (i j : Fin r) (h : i ≠ j), sgnSum i j h ∈ Subgroup.closure (Set.range S) :=
    fun i j h => sgnSum_eq_letLin i j h ▸ mem_of_reflCertB hgens hgW hL (hF i j h).2
  exact hT.mem_of_certOKGiven_of hOK hgW hWgen (hT.dframe_cover hr hW hWs hcov) P hPW hgiven hr'
    hrR hrx ht htR htx hPt

@[expose] def d7fK (Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)) (u : Vn 8 ≃ₗ[ZMod 3] Vn 8) : Prop :=
  ∃ R : Set (Vn 8 ≃ₗ[ZMod 3] Vn 8), (∀ s ∈ R, IsRefl s) ∧ Subgroup.closure R ≤ Mg ∧
    (∀ h ∈ Subgroup.closure R, u * h * u⁻¹ ∈ Subgroup.closure R) ∧
    ¬ ((∀ h ∈ Subgroup.closure R, ∀ v, u (h v - v) = h v - v) ∧
      ∀ v, ∀ h ∈ Subgroup.closure R, h (u v - v) = u v - v)

private lemma d7_isRefl_conj {g κ : Vn 8 ≃ₗ[ZMod 3] Vn 8} (hg : IsRefl g) :
    IsRefl (κ * g * κ⁻¹) := by
  obtain ⟨c, a, h, rfl⟩ := eq_refl_of_isRefl hg
  rw [conj_refl]
  exact ⟨κ c, dualVec (κ.symm : Vn 8 →ₗ[ZMod 3] Vn 8) a,
    by rw [dualVec_dotProduct]; simpa using h, fun v => by rw [refl_apply]⟩

theorem d7fK_conj {Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)} {κ : Vn 8 ≃ₗ[ZMod 3] Vn 8}
    (hκ : κ ∈ Mg) {u : Vn 8 ≃ₗ[ZMod 3] Vn 8} (hu : d7fK Mg u) : d7fK Mg (κ * u * κ⁻¹) := by
  obtain ⟨R, hRrefl, hRle, hNorm, hNot⟩ := hu
  have hconj : ∀ y : Vn 8 ≃ₗ[ZMod 3] Vn 8,
      (MulEquiv.toMonoidHom (MulAut.conj κ)) y = κ * y * κ⁻¹ := fun y => rfl
  have hclosure : Subgroup.closure ((MulAut.conj κ) '' R) =
      (Subgroup.closure R).map (MulAut.conj κ).toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  refine ⟨(MulAut.conj κ) '' R, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact d7_isRefl_conj (hRrefl h hh)
  · rw [hclosure]
    rintro _ ⟨h, hh, rfl⟩
    rw [hconj]
    exact Mg.mul_mem (Mg.mul_mem hκ (hRle hh)) (Mg.inv_mem hκ)
  · intro h hh
    rw [hclosure] at hh ⊢
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨u * g * u⁻¹, hNorm g hg, ?_⟩
    rw [hconj, hconj g]
    group
  · rintro ⟨h1, h2⟩
    apply hNot
    have hmem : ∀ g ∈ Subgroup.closure R, κ * g * κ⁻¹ ∈ Subgroup.closure ((MulAut.conj κ) '' R) :=
      fun g hg => by
        rw [hclosure]
        exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hk : ∀ v, κ⁻¹ (κ v) = v := fun v => by simp
    refine ⟨fun g hg v => ?_, fun v g hg => ?_⟩
    · have h := h1 _ (hmem g hg) (κ v)
      simp only [LinearEquiv.mul_apply, hk] at h
      rw [← map_sub κ (g v) v, hk] at h
      exact κ.injective h
    · have h := h2 (κ v) _ (hmem g hg)
      simp only [LinearEquiv.mul_apply, hk] at h
      rw [← map_sub κ (u v) v, hk] at h
      exact κ.injective h

private lemma d7f_gens_symm : ∀ k : Fin 7, (letAt d7fGens k).2 = (letAt d7fGens k).1 := by
  decide +kernel

private lemma d7f_gens_two : ∀ k : Fin 7, (letAt d7fGens k).2 ⬝ᵥ (letAt d7fGens k).1 = 2 := by
  decide +kernel

private lemma d7f_gens_one : ∀ k : Fin 7, (letAt d7fGens k).1 ⬝ᵥ (letAt d7fGens k).1 = 2 := by
  decide +kernel

private lemma refl_symm_dot {n : ℕ} (c : Vn n) (h : c ⬝ᵥ c = 2) (u v : Vn n) :
    refl c c h u ⬝ᵥ refl c c h v = u ⬝ᵥ v := by
  simp only [refl_apply, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, h, dotProduct_comm u c]
  ring

theorem d7f_W_orth : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k),
    ∀ u v : Vn 8, w u ⬝ᵥ w v = u ⬝ᵥ v := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      intro u v
      have hl : letLin (letAt d7fGens k) = refl (letAt d7fGens k).1 (letAt d7fGens k).1
          (d7f_gens_one k) := by
        rw [letLin_of _ (d7f_gens_two k)]
        exact refl_congr rfl (d7f_gens_symm k) _ _
      simp only
      rw [d7f_S k, hl]
      exact refl_symm_dot _ _ u v
  | one => intro u v; rfl
  | mul a b _ _ iha ihb =>
      intro u v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb]
  | inv a _ iha =>
      intro u v
      rw [← iha (a⁻¹ u) (a⁻¹ v)]
      simp

@[expose] def d7c0s : Fin 14 → Vn 8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 1], ![2, 0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 1],
    ![0, 2, 0, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 2, 0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 0, 2, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 1],
    ![0, 0, 0, 0, 2, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 2, 0, 1],
    ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 2, 1]]

@[expose] def d7e1s : Fin 14 → Vn 8 :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 2, 0]]

theorem d7c0s_dot_self : ∀ m : Fin 14, d7c0s m ⬝ᵥ d7c0s m = 2 := by decide +kernel

@[expose] def d7s0 (m : Fin 14) : Vn 8 ≃ₗ[ZMod 3] Vn 8 := refl (d7c0s m) (d7c0s m) (d7c0s_dot_self m)

private lemma d7f_sets_inv :
    [List.ofFn d7c0s, List.ofFn d7e1s].all (fun S => d7fGens.all fun g => S.all fun v =>
      decide (letApp g v ∈ S)) = true := by
  decide +kernel

private lemma d7f_hgW : ∀ l ∈ d7fGens,
    letLin l ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k) := by
  rw [List.forall_mem_iff_get]
  intro k
  have hlen : d7fGens.length = 7 := rfl
  have hk7 : (k : ℕ) < 7 := by omega
  have hget : letAt d7fGens (k : ℕ) = d7fGens.get k := by
    unfold letAt
    rw [List.getD_eq_getElem _ _ k.isLt]
    rfl
  rw [← hget, show letAt d7fGens (k : ℕ) = letAt d7fGens ((⟨k, hk7⟩ : Fin 7) : ℕ) from rfl,
    ← d7f_S ⟨k, hk7⟩]
  exact Subgroup.subset_closure (Set.mem_range_self _)

private lemma d7f_hWgen : Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k) ≤
    Subgroup.closure {g | ∃ l ∈ d7fGens, g = letLin l} := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine Subgroup.subset_closure ⟨letAt d7fGens k, ?_, d7f_S k⟩
  have hk : k.val < d7fGens.length := by
    have : d7fGens.length = 7 := rfl
    omega
  rw [show letAt d7fGens k = d7fGens[k.val] from List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

private lemma d7f_alphOK : AlphOK d7fGens := AlphOK.of_all (by decide +kernel)

private lemma d7f_inv_c0 : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k),
    ∀ v ∈ List.ofFn d7c0s, w v ∈ List.ofFn d7c0s :=
  sets_inv_of_gens d7f_alphOK d7f_hWgen d7f_sets_inv _ (by simp)

private lemma d7f_inv_e1 : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k),
    ∀ v ∈ List.ofFn d7e1s, w v ∈ List.ofFn d7e1s :=
  sets_inv_of_gens d7f_alphOK d7f_hWgen d7f_sets_inv _ (by simp)

private lemma d7f_conj_c0 {w : Vn 8 ≃ₗ[ZMod 3] Vn 8}
    (hw : w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) :
    ∃ m : Fin 14, w * d7s0 12 * w⁻¹ = d7s0 m := by
  have hmem : w (d7c0s 12) ∈ List.ofFn d7c0s :=
    d7f_inv_c0 w hw _ (List.mem_ofFn.mpr ⟨12, rfl⟩)
  obtain ⟨m, hm⟩ := List.mem_ofFn.mp hmem
  refine ⟨m, ?_⟩
  simp only [d7s0]
  rw [conj_refl]
  have hwinv : w⁻¹ ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k) :=
    Subgroup.inv_mem _ hw
  have hdual : dualVec (w.symm : Vn 8 →ₗ[ZMod 3] Vn 8) (d7c0s 12) = w (d7c0s 12) := by
    funext j
    change d7c0s 12 ⬝ᵥ w.symm (Pi.single j 1) = w (d7c0s 12) j
    have h := d7f_W_orth w hw (d7c0s 12) (w.symm (Pi.single j 1))
    rw [show w (w.symm (Pi.single j 1)) = Pi.single j 1 from w.apply_symm_apply _,
      dotProduct_single, mul_one] at h
    exact h.symm
  exact refl_congr hm.symm (hdual.trans hm.symm) _ _

private def c1 : Vn 8 := ![1, 1, 1, 1, 1, 1, 1, 1]
private lemma h1 : c1 ⬝ᵥ c1 = 2 := by decide +kernel
private def t1 : Vn 8 ≃ₗ[ZMod 3] Vn 8 := refl c1 c1 h1
private def z1 : Vn 8 := ![2, 2, 2, 2, 2, 2, 2, 0]

private def c2 : Vn 8 := ![1, 1, 1, 1, 1, 1, 1, 2]
private lemma h2 : c2 ⬝ᵥ c2 = 2 := by decide +kernel
private def t2 : Vn 8 ≃ₗ[ZMod 3] Vn 8 := refl c2 c2 h2
private def z2 : Vn 8 := ![1, 1, 1, 1, 1, 1, 1, 0]

private lemma t1_x : t1 (xLast 7) = z1 := by
  rw [t1, refl_apply]
  decide +kernel

private lemma t2_x : t2 (xLast 7) = z2 := by
  rw [t2, refl_apply]
  decide +kernel

private lemma t1_mul : t1 * t1 = 1 := refl_mul_self _ _ _
private lemma t2_mul : t2 * t2 = 1 := refl_mul_self _ _ _

private lemma checkB1 : ∀ m : Fin 14, d7c0s m ⬝ᵥ c1 ≠ 0 →
    ¬ FixesLine (xLast 7) (t1 * d7s0 m * t1) ∧
      ∀ m' : Fin 14, ∃ j : Fin 8, (t1 * d7s0 m * t1) (Pi.single j 1) ≠ d7s0 m' (Pi.single j 1) := by
  unfold FixesLine
  decide +kernel

private lemma checkB2 : ∀ m : Fin 14, d7c0s m ⬝ᵥ c2 ≠ 0 →
    ¬ FixesLine (xLast 7) (t2 * d7s0 m * t2) ∧
      ∀ m' : Fin 14, ∃ j : Fin 8, (t2 * d7s0 m * t2) (Pi.single j 1) ≠ d7s0 m' (Pi.single j 1) := by
  unfold FixesLine
  decide +kernel

private lemma sgnSum01_ne : (0 : Fin 7) ≠ 1 := by decide

private lemma checkN_z1 : ∀ (ν l : ZMod 3) (h : ((l * ν) • z1) ⬝ᵥ (ν • z1) = 2),
    (refl (ν • z1) ((l * ν) • z1) h * sgnSum 0 1 sgnSum01_ne * refl (ν • z1) ((l * ν) • z1) h)
      (Pi.single 2 1) ∉ List.ofFn d7e1s := by
  decide +kernel

private lemma checkN_z2 : ∀ (ν l : ZMod 3) (h : ((l * ν) • z2) ⬝ᵥ (ν • z2) = 2),
    (refl (ν • z2) ((l * ν) • z2) h * sgnSum 0 1 sgnSum01_ne * refl (ν • z2) ((l * ν) • z2) h)
      (Pi.single 2 1) ∉ List.ofFn d7e1s := by
  decide +kernel

private lemma checkN_x1 : ∀ (μ l : ZMod 3) (h : (l • xLast 7) ⬝ᵥ (μ • xLast 7) = 2),
    ((t1 * refl (μ • xLast 7) (l • xLast 7) h * t1) * sgnSum 0 1 sgnSum01_ne *
      (t1 * refl (μ • xLast 7) (l • xLast 7) h * t1)) (Pi.single 2 1) ∉ List.ofFn d7e1s := by
  decide +kernel

private lemma checkN_x2 : ∀ (μ l : ZMod 3) (h : (l • xLast 7) ⬝ᵥ (μ • xLast 7) = 2),
    ((t2 * refl (μ • xLast 7) (l • xLast 7) h * t2) * sgnSum 0 1 sgnSum01_ne *
      (t2 * refl (μ • xLast 7) (l • xLast 7) h * t2)) (Pi.single 2 1) ∉ List.ofFn d7e1s := by
  decide +kernel

private lemma d7_mul_eq_zero : ∀ x y : ZMod 3, x * y = 0 → x = 0 ∨ y = 0 := by decide

private lemma d7_smul_eq_zero {n : ℕ} {s : ZMod 3} {c : Vn n} (h : s • c = 0) (hc : c ≠ 0) :
    s = 0 := by
  by_contra hs
  apply hc
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (d7_mul_eq_zero _ _ hi).resolve_left hs

theorem d7f_sgnDiff_mem : ∀ (i j : Fin 7) (h : i ≠ j),
    sgnDiff i j h ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k) := by
  have hF := d7f_frame
  unfold dFrameB at hF
  rw [decide_eq_true_eq] at hF
  exact fun i j h =>
    sgnDiff_eq_letLin i j h ▸ mem_of_reflCertB d7f_alphOK d7f_hgW d7f_refl (hF i j h).1

theorem d7f_sgnSum_mem : ∀ (i j : Fin 7) (h : i ≠ j),
    sgnSum i j h ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k) := by
  have hF := d7f_frame
  unfold dFrameB at hF
  rw [decide_eq_true_eq] at hF
  exact fun i j h =>
    sgnSum_eq_letLin i j h ▸ mem_of_reflCertB d7f_alphOK d7f_hgW d7f_refl (hF i j h).2

private lemma d7_dot_zero_or_center {n : ℕ} {v c a : Vn n}
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

private lemma d7f_D2 {A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)}
    (hT : TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg)
    {t : Vn 8 ≃ₗ[ZMod 3] Vn 8} {c_t z : Vn 8} (ht2 : c_t ⬝ᵥ c_t = 2)
    (ht_eq : t = refl c_t c_t ht2) (htA : t ∈ A) (ht_inv : t * t = 1)
    (htx : t (xLast 7) = z) (hz7 : z (Fin.last 7) = 0) (hz0 : z ≠ 0)
    (hxt : c_t ⬝ᵥ xLast 7 ≠ 0)
    (hN1 : ∀ (ν l : ZMod 3) (h : ((l * ν) • z) ⬝ᵥ (ν • z) = 2),
      (refl (ν • z) ((l * ν) • z) h * sgnSum 0 1 sgnSum01_ne * refl (ν • z) ((l * ν) • z) h)
        (Pi.single 2 1) ∉ List.ofFn d7e1s)
    (hN2 : ∀ (μ l : ZMod 3) (h : (l • xLast 7) ⬝ᵥ (μ • xLast 7) = 2),
      ((t * refl (μ • xLast 7) (l • xLast 7) h * t) * sgnSum 0 1 sgnSum01_ne *
        (t * refl (μ • xLast 7) (l • xLast 7) h * t)) (Pi.single 2 1) ∉ List.ofFn d7e1s) :
    ∀ u ∈ A, IsRefl u → FixesLine (xLast 7) u → FixesLine z u → u c_t = c_t := by
  intro u huA huR hfx hfz
  obtain ⟨c, a, hac, rfl⟩ := eq_refl_of_isRefl huR
  have hWA : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k), w ∈ A :=
    fun w hw => hT.le (hT.W_le hw)
  have hD : ∀ i j : Fin 7, i ≠ j → (a ⬝ᵥ (frameE 7 i - frameE 7 j) = 0 ↔
      (frameE 7 i - frameE 7 j) ⬝ᵥ c = 0) := fun i j h =>
    sym_of_noTransv hT.noTransv hac (frameE_sub_self i j h) huA
      (hWA _ (d7f_sgnDiff_mem i j h))
  have hS : ∀ i j : Fin 7, i ≠ j → (a ⬝ᵥ (frameE 7 i + frameE 7 j) = 0 ↔
      (frameE 7 i + frameE 7 j) ⬝ᵥ c = 0) := fun i j h =>
    sym_of_noTransv hT.noTransv hac (frameE_add_self i j h) huA
      (hWA _ (d7f_sgnSum_mem i j h))
  obtain ⟨l, hl⟩ := sym_frame_D (by norm_num) hD hS
  have hx0 : (xLast 7 : Vn 8) ≠ 0 := by decide +kernel
  have hsumW := d7f_sgnSum_mem 0 1 sgnSum01_ne
  have he2 : (Pi.single 2 1 : Vn 8) ∈ List.ofFn d7e1s := List.mem_ofFn.mpr ⟨4, by decide +kernel⟩
  have hinv : ∀ (c' a' : Vn 8) (h' : a' ⬝ᵥ c' = 2), (refl c' a' h')⁻¹ = refl c' a' h' :=
    fun c' a' h' => inv_eq_of_mul_eq_one_right (refl_mul_self c' a' h')
  rcases d7_dot_zero_or_center hx0 hac hfx with h1 | ⟨μ, hμ⟩
  · rcases d7_dot_zero_or_center hz0 hac hfz with h2 | ⟨ν, hν⟩
    ·
      have hz : z = xLast 7 - (c_t ⬝ᵥ xLast 7) • c_t := by rw [← htx, ht_eq, refl_apply]
      rw [hz, dotProduct_sub, h1, dotProduct_smul, smul_eq_mul, zero_sub, neg_eq_zero] at h2
      have hac0 : a ⬝ᵥ c_t = 0 := (d7_mul_eq_zero _ _ h2).resolve_left hxt
      rw [refl_apply, hac0, zero_smul, sub_zero]
    ·
      exfalso
      have ha : a = (l * ν) • z := by
        funext k
        induction k using Fin.lastCases with
        | last =>
            rw [Pi.smul_apply, hz7, smul_zero, ← dot_xLast a]
            exact h1
        | cast i =>
            rw [hl i, hν, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
      subst hν
      subst ha
      have hfixx : FixesLine (xLast 7) (refl (ν • z) ((l * ν) • z) hac) := hfx
      have hmem := hT.normW _ huA hfixx _ hsumW
      rw [hinv] at hmem
      exact hN1 ν l hac (d7f_inv_e1 _ hmem _ he2)
  · rcases d7_dot_zero_or_center hz0 hac hfz with h2 | ⟨ν, hν⟩
    ·
      exfalso
      have ha : a = (a (Fin.last 7)) • xLast 7 := by
        funext k
        induction k using Fin.lastCases with
        | last => rw [Pi.smul_apply, smul_eq_mul, xLast_apply, if_pos rfl, mul_one]
        | cast i =>
            rw [hl i, hμ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, xLast_apply,
              if_neg (Fin.castSucc_ne_last i)]
            ring
      obtain ⟨l', hl'⟩ : ∃ l' : ZMod 3, a = l' • xLast 7 := ⟨_, ha⟩
      subst hμ
      subst hl'
      have ht_inv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_inv
      have htt : ∀ v, t (t v) = v := fun v => by
        have := congrArg (fun f => f v) ht_inv
        simpa [LinearEquiv.mul_apply] using this
      have hconjA : t * refl (μ • xLast 7) (l' • xLast 7) hac * t ∈ A :=
        A.mul_mem (A.mul_mem htA huA) htA
      have hfixx : FixesLine (xLast 7) (t * refl (μ • xLast 7) (l' • xLast 7) hac * t) := by
        unfold FixesLine
        simp only [LinearEquiv.mul_apply]
        rw [htx]
        rcases hfz with h | h
        · left; rw [h, ← htx, htt]
        · right; rw [h, map_neg, ← htx, htt]
      have hmem := hT.normW _ hconjA hfixx _ hsumW
      have hinv' : (t * refl (μ • xLast 7) (l' • xLast 7) hac * t)⁻¹ =
          t * refl (μ • xLast 7) (l' • xLast 7) hac * t := by
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ht_inv', hinv, mul_assoc]
      rw [hinv'] at hmem
      exact hN2 μ l' hac (d7f_inv_e1 _ hmem _ he2)
    ·
      exfalso
      have h7 := congrFun (hμ.symm.trans hν) (Fin.last 7)
      rw [Pi.smul_apply, Pi.smul_apply, hz7, smul_zero, xLast_apply, if_pos rfl, smul_eq_mul,
        mul_one] at h7
      rw [h7, zero_smul] at hμ
      rw [hμ, dotProduct_zero] at hac
      exact (by decide : (0 : ZMod 3) ≠ 2) hac

private lemma d7f_K_core {A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)}
    (hT : TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg)
    {t : Vn 8 ≃ₗ[ZMod 3] Vn 8} {c_t : Vn 8} (ht2 : c_t ⬝ᵥ c_t = 2)
    (ht_eq : t = refl c_t c_t ht2) (ht_inv : t * t = 1) (htA : t ∈ A)
    {R : Set (Vn 8 ≃ₗ[ZMod 3] Vn 8)} (hRrefl : ∀ s ∈ R, IsRefl s)
    (hRle : Subgroup.closure R ≤ Mg)
    (hNorm : ∀ h ∈ Subgroup.closure R, t * h * t⁻¹ ∈ Subgroup.closure R)
    (hA : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine (xLast 7) s' →
      ∃ m, s' = d7s0 m)
    (hB : ∀ m : Fin 14, d7c0s m ⬝ᵥ c_t ≠ 0 → ¬ FixesLine (xLast 7) (t * d7s0 m * t) ∧
      ∀ m' : Fin 14, ∃ j : Fin 8, (t * d7s0 m * t) (Pi.single j 1) ≠ d7s0 m' (Pi.single j 1))
    (hD2 : ∀ u ∈ A, IsRefl u → FixesLine (xLast 7) u → FixesLine (t (xLast 7)) u →
      u c_t = c_t) :
    (∀ h ∈ Subgroup.closure R, ∀ v, t (h v - v) = h v - v) ∧
      ∀ v, ∀ h ∈ Subgroup.closure R, h (t v - v) = t v - v := by
  have ht_inv' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_inv
  have ht_sq : ∀ v : Vn 8, t (t v) = v := by
    intro v
    have := congrArg (fun f => f v) ht_inv
    simpa [LinearEquiv.mul_apply] using this
  have ht_ct : t c_t = -c_t := by
    rw [ht_eq, refl_apply, ht2]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  have hmul : ∀ x y : ZMod 3, x * y = 0 → x = 0 ∨ y = 0 := by decide +kernel
  have hC : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine (xLast 7) s' →
      s' c_t = c_t := by
    intro s' hs'H hs'R hs'move
    obtain ⟨m, hm⟩ := hA s' hs'H hs'R hs'move
    have hsR : IsRefl (d7s0 m) := ⟨_, _, d7c0s_dot_self m, fun v => by rw [d7s0, refl_apply]⟩
    have hdot : d7c0s m ⬝ᵥ c_t = 0 := by
      by_contra hne
      have hBm := hB m hne
      have hconjH : t * s' * t ∈ Subgroup.closure R := by
        have h := hNorm s' hs'H
        rwa [ht_inv'] at h
      have hconjR : IsRefl (t * s' * t) := by
        rw [hm]
        have h := d7_isRefl_conj (g := d7s0 m) (κ := t) hsR
        rwa [ht_inv'] at h
      have hconjmove : ¬ FixesLine (xLast 7) (t * s' * t) := by
        rw [hm]
        exact hBm.1
      obtain ⟨m', hm'⟩ := hA _ hconjH hconjR hconjmove
      obtain ⟨j, hj⟩ := hBm.2 m'
      rw [← hm', hm] at hj
      exact hj rfl
    rw [hm, d7s0, refl_apply, hdot, zero_smul, sub_zero]
  have hD : ∀ u ∈ Subgroup.closure R, IsRefl u → FixesLine (xLast 7) u → u c_t = c_t := by
    intro u huH huR hu_fix
    obtain ⟨c, a, hac, hu_eq⟩ := eq_refl_of_isRefl huR
    by_contra hne
    have hdot : a ⬝ᵥ c_t ≠ 0 := by
      intro h0
      apply hne
      rw [hu_eq, refl_apply, h0, zero_smul, sub_zero]
    have hu_moves_t : u (t c_t) ≠ t c_t := by
      rw [ht_ct, map_neg]
      intro h0
      exact hne (neg_inj.mp h0)
    have hu'_H : t * u * t ∈ Subgroup.closure R := by
      have h := hNorm u huH
      rwa [ht_inv'] at h
    have hu'_R : IsRefl (t * u * t) := by
      have h := d7_isRefl_conj (g := u) (κ := t) huR
      rwa [ht_inv'] at h
    have hu'_ne : (t * u * t) c_t ≠ c_t := by
      intro heq
      apply hu_moves_t
      have := congrArg t heq
      simpa [LinearEquiv.mul_apply, ht_sq] using this
    by_cases hu'_fix : FixesLine (xLast 7) (t * u * t)
    · have hfixz : FixesLine (t (xLast 7)) u := by
        unfold FixesLine at hu'_fix ⊢
        simp only [LinearEquiv.mul_apply] at hu'_fix
        rcases hu'_fix with h | h
        · left
          have := congrArg t h
          rwa [ht_sq] at this
        · right
          have := congrArg t h
          rwa [ht_sq, map_neg] at this
      exact hne (hD2 u (hT.le (hRle huH)) huR hu_fix hfixz)
    · obtain ⟨m, hm⟩ := hA _ hu'_H hu'_R hu'_fix
      have hdotm : d7c0s m ⬝ᵥ c_t ≠ 0 := by
        intro h0
        apply hu'_ne
        rw [hm, d7s0, refl_apply, h0, zero_smul, sub_zero]
      have hEq : t * d7s0 m * t = u := by
        rw [← hm]
        calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
          _ = u := by rw [ht_inv, one_mul, mul_one]
      have hfix' : FixesLine (xLast 7) (t * d7s0 m * t) := by rwa [hEq]
      exact (hB m hdotm).1 hfix'
  have hRfix : ∀ s' ∈ R, s' c_t = c_t := by
    intro s' hs'
    by_cases hfix : FixesLine (xLast 7) s'
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
  have hRc : ∀ s ∈ R, ∀ v, t (s v - v) = s v - v := by
    intro s hs v
    obtain ⟨c, a, hac, rfl⟩ := eq_refl_of_isRefl (hRrefl s hs)
    have hsA : refl c a hac ∈ A := hT.le (hRle (Subgroup.subset_closure hs))
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, dotProduct_zero] at hac
      exact (by decide : (2 : ZMod 3) ≠ 0) hac.symm
    have hac0 : a ⬝ᵥ c_t = 0 := by
      have h := hRfix _ hs
      rw [refl_apply, sub_eq_self] at h
      exact d7_smul_eq_zero h hc0
    have htc : c_t ⬝ᵥ c = 0 :=
      (sym_of_noTransv hT.noTransv hac ht2 hsA (ht_eq ▸ htA)).mp hac0
    have htcfix : t c = c := by rw [ht_eq, refl_apply, htc, zero_smul, sub_zero]
    have hdisp : refl c a hac v - v = (-(a ⬝ᵥ v)) • c := by
      rw [refl_apply, neg_smul]
      abel
    rw [hdisp, map_smul, htcfix]
  refine ⟨fun h hh => ?_, fun v h hh => ?_⟩
  · induction hh using Subgroup.closure_induction with
    | mem s hs => exact hRc s hs
    | one => intro v; simp
    | mul a b _ _ iha ihb =>
        intro v
        have hsplit : (a * b) v - v = (a (b v) - b v) + (b v - v) := by
          rw [LinearEquiv.mul_apply]
          abel
        rw [hsplit, map_add, iha, ihb]
    | inv a _ iha =>
        intro v
        have hsplit : a⁻¹ v - v = -(a (a⁻¹ v) - a⁻¹ v) := by
          have : a (a⁻¹ v) = v := by simp
          rw [this]
          abel
        rw [hsplit, map_neg, iha]
  · have htv : t v - v = (-(c_t ⬝ᵥ v)) • c_t := by
      rw [ht_eq, refl_apply, neg_smul]
      abel
    rw [htv, map_smul, hHfix h hh]

private lemma d7f_hcls {A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)}
    (hT : TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg) :
    ∀ u ∈ A, IsRefl u → ¬ FixesLine (xLast 7) u →
      ∃ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k), ∃ i < d7fReps.length,
        ∃ h : (letAt d7fReps i).2 ⬝ᵥ (letAt d7fReps i).1 = 2,
          w * u * w⁻¹ = refl (letAt d7fReps i).1 (letAt d7fReps i).2 h :=
  TestHyp.exists_cls_of_certOKGiven hT d7f_certOK d7f_hgW d7f_hWgen
    (hT.dframe_cover (by norm_num) d7f_sgnDiff_mem d7f_sgnSum_mem d7f_cov)

private lemma d7f_reps0 : letAt d7fReps 0 = (d7c0s 12, d7c0s 12) := by decide +kernel
private lemma d7f_reps1 : letAt d7fReps 1 = (c1, c1) := by decide +kernel
private lemma d7f_reps2 : letAt d7fReps 2 = (c2, c2) := by decide +kernel

private lemma d7f_A {A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8)}
    (hT : TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg)
    {j : ℕ} (hj : j < d7fReps.length) (hjg : ∀ k, (k, j) ∈ d7fGiven → k = 0)
    (hj2 : (letAt d7fReps j).2 ⬝ᵥ (letAt d7fReps j).1 = 2)
    (htA : refl (letAt d7fReps j).1 (letAt d7fReps j).2 hj2 ∈ A)
    (htM : refl (letAt d7fReps j).1 (letAt d7fReps j).2 hj2 ∉ Mg)
    {R : Set (Vn 8 ≃ₗ[ZMod 3] Vn 8)} (hRle : Subgroup.closure R ≤ Mg)
    {s' : Vn 8 ≃ₗ[ZMod 3] Vn 8} (hsH : s' ∈ Subgroup.closure R)
    (hsR : IsRefl s') (hsmove : ¬ FixesLine (xLast 7) s') :
    ∃ m : Fin 14, s' = d7s0 m := by
  obtain ⟨w, hw, k, hk, hrep, hwsk⟩ := d7f_hcls hT s' (hT.le (hRle hsH)) hsR hsmove
  by_cases hk0 : k = 0
  · subst hk0
    have hwsk0 : w * s' * w⁻¹ = d7s0 12 := by
      rw [hwsk]
      exact refl_congr (congrArg Prod.fst d7f_reps0) (congrArg Prod.snd d7f_reps0) hrep _
    have hs_eq : s' = w⁻¹ * d7s0 12 * w⁻¹⁻¹ := by
      rw [← hwsk0, inv_inv]
      group
    obtain ⟨m, hm⟩ := d7f_conj_c0 (Subgroup.inv_mem _ hw)
    exact ⟨m, hs_eq.trans hm⟩
  · have hkj : (k, j) ∉ d7fGiven := fun h => hk0 (hjg k h)
    have hrM : refl (letAt d7fReps k).1 (letAt d7fReps k).2 hrep ∈ Mg := by
      rw [← hwsk]
      exact Mg.mul_mem (Mg.mul_mem (hT.W_le hw) (hRle hsH)) (Mg.inv_mem (hT.W_le hw))
    exact absurd (TestHyp.mem_of_s2_of_certOKGiven hT d7f_certOK d7f_hgW d7f_hWgen hk hj hkj
      hrep hj2 hrM htA) htM

theorem d7f_given_K : ∀ A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8),
    TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg →
    ∀ i j, (i, j) ∈ d7fGiven → ∀ (hi : (letAt d7fReps i).2 ⬝ᵥ (letAt d7fReps i).1 = 2)
      (hj : (letAt d7fReps j).2 ⬝ᵥ (letAt d7fReps j).1 = 2),
      refl (letAt d7fReps i).1 (letAt d7fReps i).2 hi ∈ Mg →
      refl (letAt d7fReps j).1 (letAt d7fReps j).2 hj ∈ A →
      d7fK Mg (refl (letAt d7fReps j).1 (letAt d7fReps j).2 hj) →
      refl (letAt d7fReps j).1 (letAt d7fReps j).2 hj ∈ Mg := by
  intro A Mg hT i j hij hi hj _ hjA hK
  by_contra htM
  have hjg : ∀ k, (k, j) ∈ d7fGiven → k = 0 := by
    intro k hk
    simp only [d7fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
    rcases hk with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have hjlen : j < d7fReps.length := by
    simp only [d7fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
    rcases hij with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨R, hRrefl, hRle, hNorm, hNot⟩ := hK
  have hA : ∀ s' ∈ Subgroup.closure R, IsRefl s' → ¬ FixesLine (xLast 7) s' →
      ∃ m, s' = d7s0 m := fun s' hsH hsR hsmove =>
    d7f_A hT hjlen hjg hj hjA htM hRle hsH hsR hsmove
  simp only [d7fGiven, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hij
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have ht : refl (letAt d7fReps 1).1 (letAt d7fReps 1).2 hj = t1 :=
      refl_congr (congrArg Prod.fst d7f_reps1) (congrArg Prod.snd d7f_reps1) hj h1
    rw [ht] at hjA hNorm hNot
    have hz0 : z1 ≠ 0 := by decide +kernel
    have hD2 := d7f_D2 (t := t1) hT h1 rfl hjA t1_mul t1_x (by decide +kernel) hz0 (by decide +kernel)
      checkN_z1 checkN_x1
    exact hNot (d7f_K_core (t := t1) hT h1 rfl t1_mul hjA hRrefl hRle hNorm hA checkB1
      (by rw [t1_x]; exact hD2))
  · have ht : refl (letAt d7fReps 2).1 (letAt d7fReps 2).2 hj = t2 :=
      refl_congr (congrArg Prod.fst d7f_reps2) (congrArg Prod.snd d7f_reps2) hj h2
    rw [ht] at hjA hNorm hNot
    have hz0 : z2 ≠ 0 := by decide +kernel
    have hD2 := d7f_D2 (t := t2) hT h2 rfl hjA t2_mul t2_x (by decide +kernel) hz0 (by decide +kernel)
      checkN_z2 checkN_x2
    exact hNot (d7f_K_core (t := t2) hT h2 rfl t2_mul hjA hRrefl hRle hNorm hA checkB2
      (by rw [t2_x]; exact hD2))

theorem d7f_test_K : ∀ A Mg : Subgroup (Vn 8 ≃ₗ[ZMod 3] Vn 8),
    TestHyp (Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k)) (xLast 7) A Mg →
    ∀ r ∈ Mg, IsRefl r → ¬ FixesLine (xLast 7) r →
    ∀ t ∈ A, IsRefl t → ¬ FixesLine (xLast 7) t → d7fK Mg t → t ∈ Mg := by
  intro A Mg hT
  exact linTest_dframe_of_certOKGiven_of (by norm_num) _ d7fGens rfl d7f_S d7f_refl d7f_frame
    d7f_certOK d7f_cov (d7fK Mg) (fun w hw u hu => d7fK_conj (hT.W_le hw) hu) A Mg hT
    (fun i j hij hi hj hiM hjA hP => d7f_given_K A Mg hT i j hij hi hj hiM hjA hP)

end CFSG.StandardType.TestLin

end
