module

public import CFSG.LocalAnalysis.StandardType.GGTWLowMat

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmall Certificates.DepASmall Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLX_toZ_add {p d : ℕ} {a b : List ℕ} (ha : a.length = d) (hb : b.length = d) :
    ggDepANToZ p d (ggTWNAdd p a b) = ggDepANToZ p d a + ggDepANToZ p d b := by
  funext j
  simp only [ggDepANToZ, Pi.add_apply]
  rw [ggTWNAdd,
    List.getD_eq_getElem (l := List.zipWith (fun x y => (x + y) % p) a b) (d := 0) (n := j.val)
      (by rw [List.length_zipWith, ha, hb, min_self]; exact j.isLt),
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) (by rw [ha]; exact j.isLt),
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) (by rw [hb]; exact j.isLt),
    List.getElem_zipWith, ZMod.natCast_mod, Nat.cast_add]

private lemma l05nLX_toZ_replicate {p d : ℕ} :
    ggDepANToZ p d (List.replicate d 0) = 0 := by
  funext j
  simp only [ggDepANToZ, Pi.zero_apply]
  rw [List.getD_replicate (0 : ℕ) j.isLt]
  simp

private lemma l05nLX_fold_length (p d : ℕ) :
    ∀ (l : List (ℕ × List ℕ)) (acc : List ℕ), acc.length = d →
      (∀ t ∈ l, t.2.length = d) →
      (l.foldl (fun acc t => ggTWNAdd p acc (ggDepANSmul p t.1 t.2)) acc).length = d := by
  intro l
  induction l with
  | nil => intro acc hacc _; simpa using hacc
  | cons t l ih =>
      intro acc hacc hl
      rw [List.foldl_cons]
      apply ih
      · rw [ggTWNAdd, List.length_zipWith, ggDepANSmul, List.length_map, hacc,
          hl t (by simp), min_self]
      · intro t' ht'
        exact hl t' (by simp [ht'])

private lemma l05nLX_fold_toZ (p d : ℕ) [Fact p.Prime] :
    ∀ (l : List (ℕ × List ℕ)) (acc : List ℕ), acc.length = d →
      (∀ t ∈ l, t.2.length = d) →
      ggDepANToZ p d (l.foldl (fun acc t => ggTWNAdd p acc (ggDepANSmul p t.1 t.2)) acc) =
        ggDepANToZ p d acc + (l.map fun t => (t.1 : ZMod p) • ggDepANToZ p d t.2).sum := by
  intro l
  induction l with
  | nil =>
      intro acc _ _
      simp
  | cons t l ih =>
      intro acc hacc hl
      have ht : t.2.length = d := hl t (by simp)
      have hsmul : (ggDepANSmul p t.1 t.2).length = d := by
        rw [ggDepANSmul, List.length_map]; exact ht
      have hacc' : (ggTWNAdd p acc (ggDepANSmul p t.1 t.2)).length = d := by
        rw [ggTWNAdd, List.length_zipWith, hacc, hsmul, min_self]
      have hl' : ∀ t' ∈ l, t'.2.length = d := fun t' ht' => hl t' (by simp [ht'])
      rw [List.foldl_cons, List.map_cons, List.sum_cons, ih _ hacc' hl',
        l05nLX_toZ_add hacc hsmul, l05nNC_toZ_smul ht]
      abel

private lemma l05nLX_zip_sum {M : Type*} [AddCommMonoid M] (v : List ℕ) (A : List (List ℕ))
    (d : ℕ) (hv : v.length = d) (hA : A.length = d) (g : ℕ × List ℕ → M) :
    ((List.zip v A).map g).sum = ∑ k : Fin d, g (v.getD k.val 0, A.getD k.val []) := by
  have hlen : (List.zip v A).length = d := by rw [List.length_zip, hv, hA, min_self]
  rw [show (List.zip v A).map g =
      List.ofFn (fun k : Fin d => g (v.getD k.val 0, A.getD k.val [])) from ?_]
  · rw [List.sum_ofFn]
  · apply List.ext_getElem
    · rw [List.length_map, hlen, List.length_ofFn]
    · intro i h1 h2
      have hi_zip : i < (List.zip v A).length := by rwa [List.length_map] at h1
      have hi_d : i < d := by rwa [List.length_ofFn] at h2
      have hi_v : i < v.length := by rw [hv]; exact hi_d
      have hi_A : i < A.length := by rw [hA]; exact hi_d
      rw [List.getElem_map (f := g) (h := h1), List.getElem_zip (h := hi_zip),
        List.getElem_ofFn (h := h2),
        List.getD_eq_getElem (l := v) (d := 0) (n := i) hi_v,
        List.getD_eq_getElem (l := A) (d := []) (n := i) hi_A]

private lemma l05nLX_lin_apply {p d : ℕ} (A : List (List ℕ)) (v : GGDepAE p d) :
    ggTWLMatLin p d A v = ∑ k : Fin d, v k • ggDepANToZ p d (A.getD k.val []) := by
  unfold ggTWLMatLin
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [LinearMap.smulRight_apply, LinearMap.proj_apply]

private lemma l05nLX_lin_basis {p d : ℕ} (A : List (List ℕ)) (k : Fin d) :
    ggTWLMatLin p d A (Pi.single k 1) = ggDepANToZ p d (A.getD k.val []) := by
  rw [l05nLX_lin_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Pi.single_eq_of_ne hik]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma l05nLX_pi_ext_basis {p d : ℕ} {f g : Module.End (ZMod p) (GGDepAE p d)}
    (h : ∀ k : Fin d, f (Pi.single k 1) = g (Pi.single k 1)) : f = g := by
  apply LinearMap.pi_ext
  intro k x
  have hsingle : Pi.single k x = x • Pi.single k 1 := by
    funext j
    by_cases hj : j = k
    · rw [hj]; simp
    · rw [Pi.single_eq_of_ne hj, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
  calc f (Pi.single k x) = f (x • Pi.single k 1) := by rw [hsingle]
    _ = x • f (Pi.single k 1) := map_smul f x _
    _ = x • g (Pi.single k 1) := by rw [h k]
    _ = g (x • Pi.single k 1) := (map_smul g x _).symm
    _ = g (Pi.single k x) := by rw [hsingle]

private lemma l05nLX_apply_length {p d : ℕ} {A : List (List ℕ)} (hA : ggTWLMatWF d A)
    {v : List ℕ} (hv : v.length = d) : (ggTWLMatApply p d A v).length = d := by
  have hcol : ∀ t ∈ List.zip v A, t.2.length = d := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp ht
    have hiA : i < A.length := by
      have h : i < (List.zip v A).length := hi
      rw [List.length_zip] at h
      exact lt_of_lt_of_le h (min_le_right _ _)
    have hti2 : t.2 = A[i] := by rw [← hti, List.getElem_zip (h := hi)]
    rw [hti2]
    exact hA.2 _ (List.getElem_mem hiA)
  rw [ggTWLMatApply]
  exact l05nLX_fold_length p d (List.zip v A) (List.replicate d 0)
    (by rw [List.length_replicate]) hcol

private lemma l05nLX_apply_toZ {p d : ℕ} [Fact p.Prime] {A : List (List ℕ)} (hA : ggTWLMatWF d A)
    {v : List ℕ} (hv : v.length = d) :
    ggDepANToZ p d (ggTWLMatApply p d A v) = ggTWLMatLin p d A (ggDepANToZ p d v) := by
  have hcol : ∀ t ∈ List.zip v A, t.2.length = d := by
    intro t ht
    obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.mp ht
    have hiA : i < A.length := by
      have h : i < (List.zip v A).length := hi
      rw [List.length_zip] at h
      exact lt_of_lt_of_le h (min_le_right _ _)
    have hti2 : t.2 = A[i] := by rw [← hti, List.getElem_zip (h := hi)]
    rw [hti2]
    exact hA.2 _ (List.getElem_mem hiA)
  rw [ggTWLMatApply,
    l05nLX_fold_toZ p d (List.zip v A) (List.replicate d 0)
      (by rw [List.length_replicate]) hcol,
    l05nLX_toZ_replicate, zero_add,
    l05nLX_zip_sum v A d hv hA.1 (fun t => (t.1 : ZMod p) • ggDepANToZ p d t.2),
    l05nLX_lin_apply A (ggDepANToZ p d v)]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem ggTWLMatMul_lin {p d : ℕ} [Fact p.Prime] {A B : List (List ℕ)} (hA : ggTWLMatWF d A)
    (hB : ggTWLMatWF d B) :
    ggTWLMatWF d (ggTWLMatMul p d A B) ∧
      ggTWLMatLin p d (ggTWLMatMul p d A B) = ggTWLMatLin p d A * ggTWLMatLin p d B := by
  have hWF : ggTWLMatWF d (ggTWLMatMul p d A B) := by
    refine ⟨?_, ?_⟩
    · simp only [ggTWLMatMul, List.length_map, hB.1]
    · intro c hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact l05nLX_apply_length hA (hB.2 c0 hc0)
  refine ⟨hWF, ?_⟩
  apply l05nLX_pi_ext_basis
  intro k
  have hk : k.val < B.length := by rw [hB.1]; exact k.isLt
  have hBk : (B.getD k.val []).length = d := by
    rw [List.getD_eq_getElem (l := B) (d := []) (n := k.val) hk]
    exact hB.2 _ (List.getElem_mem hk)
  have hmulget : (ggTWLMatMul p d A B).getD k.val [] =
      ggTWLMatApply p d A (B.getD k.val []) := by
    rw [ggTWLMatMul,
      List.getD_eq_getElem (l := B.map (ggTWLMatApply p d A)) (d := []) (n := k.val)
        (by rw [List.length_map]; exact hk),
      List.getElem_map, List.getD_eq_getElem (l := B) (d := []) (n := k.val) hk]
  calc ggTWLMatLin p d (ggTWLMatMul p d A B) (Pi.single k 1)
      = ggDepANToZ p d ((ggTWLMatMul p d A B).getD k.val []) :=
        l05nLX_lin_basis (ggTWLMatMul p d A B) k
    _ = ggDepANToZ p d (ggTWLMatApply p d A (B.getD k.val [])) := by rw [hmulget]
    _ = ggTWLMatLin p d A (ggDepANToZ p d (B.getD k.val [])) :=
        l05nLX_apply_toZ hA hBk
    _ = ggTWLMatLin p d A (ggTWLMatLin p d B (Pi.single k 1)) := by
        rw [l05nLX_lin_basis (B) k]
    _ = (ggTWLMatLin p d A * ggTWLMatLin p d B) (Pi.single k 1) := rfl

private lemma l05nLX_basis_toZ {p d : ℕ} (k : Fin d) :
    ggDepANToZ p d (ggTWLBasis d k.val) = Pi.single k 1 := by
  funext j
  simp only [ggDepANToZ, ggTWLBasis, Pi.single_apply]
  rw [List.getD_eq_getElem (l := (List.range d).map (fun j => if j = k.val then 1 else 0))
      (d := 0) (n := j.val) (by rw [List.length_map, List.length_range]; exact j.isLt),
    List.getElem_map, List.getElem_range]
  by_cases h : j.val = k.val
  · rw [if_pos h]
    have hjk : j = k := Fin.ext h
    rw [if_pos hjk]; simp
  · rw [if_neg h]
    have hjk : ¬ (j = k) := fun hh => h (Fin.ext_iff.mp hh)
    rw [if_neg hjk]; simp

private lemma l05nLX_one_lin {p d : ℕ} :
    ggTWLMatWF d (ggTWLMatOne d) ∧ ggTWLMatLin p d (ggTWLMatOne d) = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [ggTWLMatOne]
  · intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    simp [ggTWLBasis, List.length_map]
  · apply l05nLX_pi_ext_basis
    intro k
    rw [l05nLX_lin_basis (ggTWLMatOne d) k]
    have hget : (ggTWLMatOne d).getD k.val [] = ggTWLBasis d k.val := by
      simp only [ggTWLMatOne]
      rw [List.getD_eq_getElem (l := (List.range d).map (ggTWLBasis d)) (d := []) (n := k.val)
          (by rw [List.length_map, List.length_range]; exact k.isLt),
        List.getElem_map, List.getElem_range]
    rw [hget, l05nLX_basis_toZ]
    rfl

theorem ggTWLWordMat_lin {p d : ℕ} [Fact p.Prime] {Ts : List (List (List ℕ))}
    (hT : ∀ t ∈ Ts, ggTWLMatWF d t) {w : List ℕ} (hw : ∀ k ∈ w, k < Ts.length) :
    ggTWLMatWF d (ggTWLWordMat p d Ts w) ∧
      ggTWLMatLin p d (ggTWLWordMat p d Ts w) =
        (w.map fun k => ggTWLMatLin p d (Ts.getD k [])).prod := by
  revert hw
  induction w with
  | nil =>
      intro _
      simpa [ggTWLWordMat] using l05nLX_one_lin (p := p) (d := d)
  | cons k w ih =>
      intro hw
      have hk : k < Ts.length := hw k (by simp)
      have hkw : ∀ k' ∈ w, k' < Ts.length := fun k' hk' => hw k' (by simp [hk'])
      have hTk : ggTWLMatWF d (Ts.getD k []) := by
        rw [List.getD_eq_getElem (l := Ts) (d := []) (n := k) hk]
        exact hT _ (List.getElem_mem hk)
      obtain ⟨hwf, hwl⟩ := ih hkw
      have hmul := ggTWLMatMul_lin (p := p) (d := d) hTk hwf
      have hword : ggTWLWordMat p d Ts (k :: w) =
          ggTWLMatMul p d (Ts.getD k []) (ggTWLWordMat p d Ts w) := by
        simp [ggTWLWordMat]
      rw [hword]
      refine ⟨hmul.1, ?_⟩
      rw [hmul.2, hwl]
      simp [List.map_cons, List.prod_cons]

theorem ggTWLMatPow_lin {p d : ℕ} [Fact p.Prime] {A : List (List ℕ)} (hA : ggTWLMatWF d A)
    (k : ℕ) :
    ggTWLMatWF d (ggTWLMatPow p d A k) ∧
      ggTWLMatLin p d (ggTWLMatPow p d A k) = ggTWLMatLin p d A ^ k := by
  induction k with
  | zero =>
      simpa [ggTWLMatPow] using l05nLX_one_lin (p := p) (d := d)
  | succ k ih =>
      obtain ⟨hwf, hwl⟩ := ih
      have hmul := ggTWLMatMul_lin (p := p) (d := d) hA hwf
      have hpow : ggTWLMatPow p d A (k + 1) =
          ggTWLMatMul p d A (ggTWLMatPow p d A k) := by simp [ggTWLMatPow]
      rw [hpow]
      refine ⟨hmul.1, ?_⟩
      rw [hmul.2, hwl, pow_succ']

end CFSG.StandardType

end
