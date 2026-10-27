module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Kern
public import Mathlib.Data.List.GetD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv

private lemma s16c11a11_fin_tab_append (a : Perm (Fin 8)) (acc : List (Fin 8)) (f : Fin 8)
    (hlt : acc.length < 8) (hlast : f = a ⟨acc.length, hlt⟩)
    (hagree : ∀ i : Fin 8, (i : ℕ) < acc.length → S16C11A11Tab acc i = a i) :
    ∀ i : Fin 8, (i : ℕ) < (acc ++ [f]).length →
      S16C11A11Tab (acc ++ [f]) i = a i := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  show (acc ++ [f]).getD (i : ℕ) (0 : Fin 8) = a i
  by_cases hcase : (i : ℕ) < acc.length
  · rw [List.getD_append acc [f] (0 : Fin 8) (i : ℕ) hcase]
    exact hagree i hcase
  · have hle : acc.length ≤ (i : ℕ) := not_lt.1 hcase
    have hii : (i : ℕ) = acc.length := by omega
    rw [List.getD_append_right acc [f] (0 : Fin 8) (i : ℕ) hle,
      show (i : ℕ) - acc.length = 0 from by omega,
      show ([f] : List (Fin 8)).getD 0 (0 : Fin 8) = f from by simp, hlast]
    exact congrArg a (Fin.ext hii.symm)

theorem s16c11_a11_norm8 :
    ∀ a : Perm (Fin 8), S16C11A11Pull a s16c11A11g1 → S16C11A11Pull a s16c11A11g2 →
      S16C11A11Pull a s16c11A11g3 → S16C11A11Blk8 a := by
  intro a h1 h2 h3
  have key : ∀ k : ℕ, ∀ acc : List (Fin 8), acc.length + k = 8 →
      (∀ i : Fin 8, (i : ℕ) < acc.length → S16C11A11Tab acc i = a i) →
      S16C11A11Search k acc → S16C11A11Blk8F a := by
    intro k
    induction k with
    | zero =>
        intro acc hlen hagree hsearch
        have hlen8 : acc.length = 8 := by omega
        have htab : S16C11A11Tab acc = ⇑a := by
          funext i
          exact hagree i (by rw [hlen8]; exact i.isLt)
        simp only [S16C11A11Search] at hsearch
        simpa only [htab] using hsearch
    | succ k ih =>
        intro acc hlen hagree hsearch
        have hlt : acc.length < 8 := by omega
        let f : Fin 8 := a ⟨acc.length, hlt⟩
        have hlast : f = a ⟨acc.length, hlt⟩ := rfl
        have hagree' : ∀ i : Fin 8, (i : ℕ) < (acc ++ [f]).length →
            S16C11A11Tab (acc ++ [f]) i = a i :=
          s16c11a11_fin_tab_append a acc f hlt hlast hagree
        simp only [S16C11A11Search] at hsearch
        have hf_not : f ∉ acc := by
          intro hf
          obtain ⟨n, hn, hne⟩ := List.mem_iff_getElem.1 hf
          have h2 : a ⟨n, hn.trans hlt⟩ = f := by
            have h := (hagree ⟨n, hn.trans hlt⟩ hn).symm
            rw [show S16C11A11Tab acc ⟨n, hn.trans hlt⟩ = acc.getD n (0 : Fin 8) from rfl,
              List.getD_eq_getElem acc (0 : Fin 8) hn, hne] at h
            exact h
          have h3 : (⟨n, hn.trans hlt⟩ : Fin 8) = ⟨acc.length, hlt⟩ := by
            apply a.injective
            show a ⟨n, hn.trans hlt⟩ = a ⟨acc.length, hlt⟩
            exact h2
          have : n = acc.length := congrArg Fin.val h3
          omega
        have pull_of : ∀ (gi : Perm (Fin 8)), S16C11A11Pull a gi →
            S16C11A11PullLt (acc.length + 1) (S16C11A11Tab (acc ++ [f])) gi := by
          intro gi hgi x y hxy
          obtain ⟨hx, hy, hgx, hgy⟩ := hxy
          rw [hagree' x (by rw [List.length_append, List.length_singleton]; omega),
            hagree' y (by rw [List.length_append, List.length_singleton]; omega),
            hagree' (gi x) (by rw [List.length_append, List.length_singleton]; omega),
            hagree' (gi y) (by rw [List.length_append, List.length_singleton]; omega)]
          exact hgi x y
        have hpull : S16C11A11PullLt3 (acc.length + 1) (S16C11A11Tab (acc ++ [f])) :=
          ⟨pull_of s16c11A11g1 h1, pull_of s16c11A11g2 h2, pull_of s16c11A11g3 h3⟩
        have hrec : S16C11A11Search k (acc ++ [f]) := hsearch f hf_not hpull
        have hlen' : (acc ++ [f]).length + k = 8 := by
          rw [List.length_append, List.length_singleton]
          omega
        exact ih (acc ++ [f]) hlen' hagree' hrec
  have hblkF : S16C11A11Blk8F a :=
    key 8 [] (by simp) (by intro i hi; exact absurd hi (by simp)) s16c11_a11_search
  exact (s16c11_a11_blk8_iff_blk8F a).2 hblkF

@[expose] def s16c11A11ResFun (σ : Perm (Fin 11)) (hσ : σ ∈ s16c11A11Pres) : Perm (Fin 8) where
  toFun x := ⟨((σ (Fin.castLE (by norm_num) x) : Fin 11) : ℕ),
    (s16c11A11_mem_pres_iff.1 hσ _).2 (by simp)⟩
  invFun x := ⟨((σ⁻¹ (Fin.castLE (by norm_num) x) : Fin 11) : ℕ),
    (s16c11A11_mem_pres_iff.1 (s16c11A11Pres.inv_mem hσ) _).2 (by simp)⟩
  left_inv x := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Fin.ext
    simp

@[expose] def s16c11A11Res : ↥s16c11A11Pres →* Perm (Fin 8) where
  toFun σ := s16c11A11ResFun σ.1 σ.2
  map_one' := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    simp [s16c11A11ResFun]
  map_mul' σ τ := by
    apply Equiv.ext
    intro x
    apply Fin.ext
    simp [s16c11A11ResFun]

theorem s16c11A11_res_apply (σ : ↥s16c11A11Pres) (x : Fin 8) :
    (((s16c11A11Res σ) x : Fin 8) : ℕ) =
      ((σ.1 (Fin.castLE (by norm_num) x) : Fin 11) : ℕ) :=
  rfl

private lemma s16c11a11_fin_res_coe (σ : ↥s16c11A11Pres) (i : Fin 11) (hi : (i : ℕ) < 8) :
    (((s16c11A11Res σ) ⟨i, hi⟩ : Fin 8) : ℕ) = ((σ.1 i : Fin 11) : ℕ) := by
  have h := s16c11A11_res_apply σ ⟨i, hi⟩
  simp only [Fin.castLE_mk] at h
  refine h.trans ?_
  exact congrArg (fun z : Fin 11 => ((σ.1 z : Fin 11) : ℕ)) (Fin.ext rfl)

theorem s16c11_a11_blk_iff_res (σ : ↥s16c11A11Pres) :
    S16C11A11Blk σ.1 ↔ S16C11A11Blk8 (s16c11A11Res σ) := by
  unfold S16C11A11Blk S16C11A11Blk8
  constructor
  · intro h i j
    have h' := h (Fin.castLE (by norm_num : 8 ≤ 11) i) (Fin.castLE (by norm_num : 8 ≤ 11) j)
      (by simp) (by simp)
    simpa only [s16c11A11_res_apply, Fin.val_castLE] using h'
  · intro h i j hi hj
    simpa only [s16c11a11_fin_res_coe σ i hi, s16c11a11_fin_res_coe σ j hj] using h ⟨i, hi⟩ ⟨j, hj⟩

theorem s16c11_a11_exists_ext (w : Perm (Fin 8)) :
    ∃ σ : ↥s16c11A11Pres, (σ : Perm (Fin 11)) ∈ s16c11A11Low ∧ s16c11A11Res σ = w := by
  let f : Fin 8 ↪ Fin 11 := Fin.castLEEmb (by norm_num : 8 ≤ 11)
  let σ₀ : Perm (Fin 11) := w.viaFintypeEmbedding f
  have hf8 : ∀ x : Fin 8, ((f x : Fin 11) : ℕ) = (x : ℕ) := by
    intro x
    simp [f]
  have hrange : ∀ y : Fin 11, y ∈ Set.range f ↔ (y : ℕ) < 8 := by
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      simp [f]
    · intro hy
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Fin.ext
      simp [f]
  have hfix : ∀ y : Fin 11, ¬ (y : ℕ) < 8 → σ₀ y = y := by
    intro y hy
    exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range w f ((hrange y).not.mpr hy)
  have happly : ∀ x : Fin 8, σ₀ (f x) = f (w x) :=
    fun x => Equiv.Perm.viaFintypeEmbedding_apply_image w f x
  have hpres : σ₀ ∈ s16c11A11Pres := by
    rw [s16c11A11_mem_pres_iff]
    intro i
    by_cases hi : (i : ℕ) < 8
    · have hif : f ⟨i, hi⟩ = i := by
        apply Fin.ext
        simp [f]
      rw [← hif, happly, hf8 (w ⟨i, hi⟩), hf8 ⟨i, hi⟩]
      exact ⟨fun _ => hi, fun _ => (w ⟨i, hi⟩).isLt⟩
    · rw [hfix i hi]
  refine ⟨⟨σ₀, hpres⟩, ?_, ?_⟩
  · rw [s16c11A11Low, Subgroup.mem_inf, Subgroup.mem_inf]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hfix 8 (by decide)
    · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hfix 9 (by decide)
    · rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hfix 10 (by decide)
  · apply Equiv.ext
    intro x
    apply Fin.ext
    rw [s16c11A11_res_apply]
    have hx : Fin.castLE (by norm_num : 8 ≤ 11) x = f x := rfl
    rw [hx, happly x]
    simp [f]

theorem s16c11_a11_res_eq_one {σ : ↥s16c11A11Pres} (h : s16c11A11Res σ = 1) (x : Fin 11)
    (hx : (x : ℕ) < 8) : σ.1 x = x := by
  have hx' : (s16c11A11Res σ) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    rw [h]
    rfl
  have hcoe := s16c11a11_fin_res_coe σ x hx
  rw [hx'] at hcoe
  exact Fin.ext hcoe.symm

theorem s16c11_a11_blk_of_conj_mem {g : Perm (Fin 11)} (hg : g ∈ s16c11A11Pres)
    (h1 : g * s16c11A11k1 * g⁻¹ ∈ s16c11A11K) (h2 : g * s16c11A11k2 * g⁻¹ ∈ s16c11A11K)
    (h3 : g * s16c11A11m3 * g⁻¹ ∈ s16c11A11K) : S16C11A11Blk g := by
  let σ : ↥s16c11A11Pres := ⟨g, hg⟩
  have r1 : ∀ x : Fin 8, s16c11A11k1 (Fin.castLE (by norm_num : 8 ≤ 11) x) =
      Fin.castLE (by norm_num : 8 ≤ 11) (s16c11A11g1 x) := by decide
  have r2 : ∀ x : Fin 8, s16c11A11k2 (Fin.castLE (by norm_num : 8 ≤ 11) x) =
      Fin.castLE (by norm_num : 8 ≤ 11) (s16c11A11g2 x) := by decide
  have r3 : ∀ x : Fin 8, s16c11A11m3 (Fin.castLE (by norm_num : 8 ≤ 11) x) =
      Fin.castLE (by norm_num : 8 ≤ 11) (s16c11A11g3 x) := by decide
  have key : ∀ (k0 : Perm (Fin 11)) (gi : Perm (Fin 8)),
      (∀ x : Fin 8, k0 (Fin.castLE (by norm_num : 8 ≤ 11) x) =
        Fin.castLE (by norm_num : 8 ≤ 11) (gi x)) →
      g * k0 * g⁻¹ ∈ s16c11A11K → S16C11A11Pull (s16c11A11Res σ) gi := by
    intro k0 gi hki hk x y
    have hx8 : ((g (Fin.castLE (by norm_num : 8 ≤ 11) x) : Fin 11) : ℕ) < 8 :=
      (s16c11A11_mem_pres_iff.1 hg _).2 (by simp)
    have hy8 : ((g (Fin.castLE (by norm_num : 8 ≤ 11) y) : Fin 11) : ℕ) < 8 :=
      (s16c11A11_mem_pres_iff.1 hg _).2 (by simp)
    have hblk : S16C11A11Blk (g * k0 * g⁻¹) :=
      ((s16c11A11_mem_Y_iff.1 (s16c11A11_K_le_Y hk)).1).2
    have hcc := hblk (g (Fin.castLE (by norm_num : 8 ≤ 11) x))
      (g (Fin.castLE (by norm_num : 8 ≤ 11) y)) hx8 hy8
    have hcx : (g * k0 * g⁻¹) (g (Fin.castLE (by norm_num : 8 ≤ 11) x)) =
        g (Fin.castLE (by norm_num : 8 ≤ 11) (gi x)) := by
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, hki x]
    have hcy : (g * k0 * g⁻¹) (g (Fin.castLE (by norm_num : 8 ≤ 11) y)) =
        g (Fin.castLE (by norm_num : 8 ≤ 11) (gi y)) := by
      simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, hki y]
    have v1x : (((s16c11A11Res σ) x : Fin 8) : ℕ) =
        ((g (Fin.castLE (by norm_num : 8 ≤ 11) x) : Fin 11) : ℕ) :=
      s16c11A11_res_apply σ x
    have v2x : (((s16c11A11Res σ) (gi x) : Fin 8) : ℕ) =
        ((g (Fin.castLE (by norm_num : 8 ≤ 11) (gi x)) : Fin 11) : ℕ) :=
      s16c11A11_res_apply σ (gi x)
    have v1y : (((s16c11A11Res σ) y : Fin 8) : ℕ) =
        ((g (Fin.castLE (by norm_num : 8 ≤ 11) y) : Fin 11) : ℕ) :=
      s16c11A11_res_apply σ y
    have v2y : (((s16c11A11Res σ) (gi y) : Fin 8) : ℕ) =
        ((g (Fin.castLE (by norm_num : 8 ≤ 11) (gi y)) : Fin 11) : ℕ) :=
      s16c11A11_res_apply σ (gi y)
    have w1 : ((g (Fin.castLE (by norm_num : 8 ≤ 11) (gi x)) : Fin 11) : ℕ) =
        (((g * k0 * g⁻¹) (g (Fin.castLE (by norm_num : 8 ≤ 11) x)) : Fin 11) : ℕ) :=
      congrArg Fin.val hcx.symm
    have w2 : ((g (Fin.castLE (by norm_num : 8 ≤ 11) (gi y)) : Fin 11) : ℕ) =
        (((g * k0 * g⁻¹) (g (Fin.castLE (by norm_num : 8 ≤ 11) y)) : Fin 11) : ℕ) :=
      congrArg Fin.val hcy.symm
    rw [v1x, v2x, v1y, v2y, w1, w2]
    exact hcc
  have hp1 : S16C11A11Pull (s16c11A11Res σ) s16c11A11g1 := key s16c11A11k1 s16c11A11g1 r1 h1
  have hp2 : S16C11A11Pull (s16c11A11Res σ) s16c11A11g2 := key s16c11A11k2 s16c11A11g2 r2 h2
  have hp3 : S16C11A11Pull (s16c11A11Res σ) s16c11A11g3 := key s16c11A11m3 s16c11A11g3 r3 h3
  have hblk8 : S16C11A11Blk8 (s16c11A11Res σ) := s16c11_a11_norm8 _ hp1 hp2 hp3
  exact (s16c11_a11_blk_iff_res σ).2 hblk8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
