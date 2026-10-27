module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisInterp
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpRootSL2
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpMono
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.Quasithin.SmithCurtis

private theorem spGL_neg_mem_L {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (i : Fin n)
    (c : K) : elt (.negativeLong i) c ∈ (spCurtisDatum n K).L := by
  rw [← CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Lower i c]
  exact longBlock_sl2Lower_mem_L i c

private theorem spGL_pos_mem_U {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (i : Fin n)
    (c : K) : elt (.positiveLong i) c ∈ (spCurtisDatum n K).U := by
  rw [← CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Upper i c]
  exact longBlock_sl2Upper_mem_U i c

private abbrev spGL_i0 (n : ℕ) (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

private abbrev spGL_i1 (n : ℕ) (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

open CFSG.StandardType in
private theorem spGL_spSgn_ne_one {n : ℕ} (i : Fin n) : spSgn i ≠ 1 := by
  intro h
  have h0 := congrFun h i
  simp only [spSgn, Pi.one_apply] at h0
  exact absurd h0 (by norm_num)

open CFSG.StandardType in
private theorem spGL_spSgn_mul_sign {n : ℕ} (i j : Fin n) :
    SpIsSign (fun c => spSgn i c * spSgn j c) := by
  have hm := (spIsSign_spSgn i).mul (spIsSign_spSgn j) (1 : Equiv.Perm (Fin n))
  simpa using hm

open CFSG.StandardType in
private theorem spGL_spSgn_mul_ne_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (fun c => spSgn i c * spSgn j c) ≠ 1 := by
  intro h
  have h0 := congrFun h i
  simp only [spSgn, Pi.one_apply, if_neg hij] at h0
  exact absurd h0 (by norm_num)

open CFSG.StandardType CFSG.LieType.RootSystem CFSG.LieType.Steinberg in
private theorem spGL_spRealizes_one_of_forall_lt {n : ℕ} (ω : List (Fin n))
    (hω : ∀ j ∈ ω, j.val + 1 < n) :
    ∃ π : Equiv.Perm (Fin n),
      SpRealizes n ((coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.wordProd ω) π 1 := by
  induction ω with
  | nil => exact ⟨1, by simpa using (spRealizes_one (m := n))⟩
  | cons s ω ih =>
      obtain ⟨π, hπ⟩ := ih fun j hj => hω j (List.mem_cons_of_mem s hj)
      have hlt := hω s List.mem_cons_self
      refine ⟨Equiv.swap s ⟨s.val + 1, hlt⟩ * π, ?_⟩
      rw [CoxeterSystem.wordProd_cons]
      exact ((spRealizes_simple_of_lt (m := n) hlt).mul hπ).congr rfl (by funext c; simp)

open CFSG.StandardType CFSG.LieType.RootSystem CFSG.LieType.Steinberg in
private theorem spGL_mem_last_of_sign_ne_one {n : ℕ} {i : Fin n} (hi : i.val + 1 = n)
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hx : SpRealizes n x π s) (hs : SpIsSign s) (hne : s ≠ 1)
    {ω : List (Fin n)}
    (hωprod : (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.wordProd ω = x) :
    i ∈ ω := by
  by_contra hmem
  have hlt : ∀ j ∈ ω, j.val + 1 < n := by
    intro j hj
    have hji : j ≠ i := fun h => hmem (h ▸ hj)
    have : j.val ≠ i.val := fun h => hji (Fin.ext h)
    omega
  obtain ⟨π', hπ'⟩ := spGL_spRealizes_one_of_forall_lt ω hlt
  rw [hωprod] at hπ'
  exact hne (spRealizes_unique hx hπ' hs).2

private theorem spGL_coinvScalar_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] {χ : StatedSp n K → k} {μ : Fin n → k} {i : Fin n}
    (hμ : μ i = (spCurtisDatum n K).dScalar χ i) {ω : List (Fin n)} (hω : i ∈ ω) :
    (spCurtisDatum n K).coinvScalar χ μ ω = 0 := by
  unfold CurtisDatum.coinvScalar
  exact List.prod_eq_zero (List.mem_map.mpr ⟨i, hω, sub_eq_zero.mpr hμ⟩)

open CFSG.StandardType CFSG.LieType.RootSystem CFSG.LieType.Steinberg in
private theorem spGL_form_nW_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    {i : Fin n} (hi : i.val + 1 = n) (hμ : μ i = (spCurtisDatum n K).dScalar χ i)
    {x : (coxeterMatrix (isFiniteType_cartanC n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (hx : SpRealizes n x π s) (hs : SpIsSign s) (hne : s ≠ 1)
    {l h u : StatedSp n K} (hl : l ∈ (spCurtisDatum n K).L) (hh : h ∈ (spCurtisDatum n K).H)
    (hu : u ∈ (spCurtisDatum n K).U) :
    f (ρ (l * (spCurtisDatum n K).nW x * h * u) y₀) = 0 := by
  obtain ⟨ω, hωred, hωprod⟩ :=
    (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.exists_isReduced x
  have hmem := spGL_mem_last_of_sign_ne_one hi hx hs hne hωprod.symm
  have hcoinv := spGL_coinvScalar_eq_zero (K := K) (n := n) (i := i) hμ hmem
  have hform := form_mul_nW_mul_mul (D := spCurtisDatum n K) ht hf hfy hωred hl hh hu
  rw [hcoinv, mul_zero] at hform
  rw [hωprod]
  exact hform

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg in
private theorem spGL_value_eq_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1)
    {l h u g : StatedSp n K} (hl : l ∈ (spCurtisDatum n K).L) (hh : h ∈ (spCurtisDatum n K).H)
    (hu : u ∈ (spCurtisDatum n K).U) (hg : g = l * h * u) :
    f (ρ g y₀) = 1 := by
  rw [hg]
  have hu' : ρ u y₀ = y₀ := ht.1 u hu
  have hh' : ρ h y₀ = χ h • y₀ := ht.2.2.1 h hh
  have hl' : ρ l y₀ - y₀ ∈ augSub ρ (spCurtisDatum n K).L := sub_mem_augSub ρ hl y₀
  calc f (ρ (l * h * u) y₀) = f (ρ l (χ h • y₀)) := by
        rw [show l * h * u = l * (h * u) by group, map_mul, map_mul,
          Module.End.mul_apply, Module.End.mul_apply, hu', hh']
    _ = f (χ h • ρ l y₀) := by rw [map_smul]
    _ = χ h * f (ρ l y₀) := by rw [map_smul, smul_eq_mul]
    _ = χ h * f y₀ := by
        rw [show ρ l y₀ = y₀ + (ρ l y₀ - y₀) by abel, map_add, hf _ hl', add_zero]
    _ = 1 := by rw [hfy, mul_one, hχ h hh]

private theorem spGL_commute_blocks {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {A B : Matrix.SpecialLinearGroup (Fin 2) K} :
    Commute (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock K n i A)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock K n j B) :=
  CFSG.ClassicalInvolution.Models.SymplecticPairs.commute_longBlock_longBlock hij A B

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_commute_pos_block {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (c : K) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (elt (.positiveLong i) c) (longBlock K n j A) := by
  rw [← longBlock_sl2Upper i c]
  exact spGL_commute_blocks hij

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_commute_pos_neg {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (c c' : K) :
    Commute (elt (.positiveLong i) c) (elt (.negativeLong j) c') := by
  rw [← longBlock_sl2Lower j c']
  exact spGL_commute_pos_block hij c _

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_commute_pos_diag {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (c : K) (u : Kˣ) :
    Commute (elt (.positiveLong i) c) (diagHom n K (Pi.mulSingle j u)) := by
  rw [← longBlock_diagUnit_eq_diagHom j u]
  exact spGL_commute_pos_block hij c _

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_commute_block_neg {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (A : Matrix.SpecialLinearGroup (Fin 2) K) (c : K) :
    Commute (longBlock K n i A) (elt (.negativeLong j) c) := by
  rw [← longBlock_sl2Lower j c]
  exact spGL_commute_blocks hij

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_commute_block_diag {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (A : Matrix.SpecialLinearGroup (Fin 2) K) (u : Kˣ) :
    Commute (longBlock K n i A) (diagHom n K (Pi.mulSingle j u)) := by
  rw [← longBlock_diagUnit_eq_diagHom j u]
  exact spGL_commute_blocks hij

private theorem spGL_rearrange {G : Type} [Group G] {A0 A1 B0 B1 : G} (h : Commute A1 B0) :
    A0 * A1 * (B0 * B1) = (A0 * B0) * (A1 * B1) := by
  calc A0 * A1 * (B0 * B1)
      = A0 * (A1 * B0) * B1 := by group
    _ = A0 * (B0 * A1) * B1 := by rw [h.eq]
    _ = (A0 * B0) * (A1 * B1) := by group

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_block_nonsing {K : Type} [Field K] {n : ℕ} {i : Fin n} {c : K}
    (h : 1 + c ≠ 0) :
    elt (.positiveLong i) 1 * elt (.negativeLong i) c =
      elt (.negativeLong i) (c / (1 + c)) *
        diagHom n K (Pi.mulSingle i (Units.mk0 (1 + c) h)) *
        elt (.positiveLong i) (1 / (1 + c)) := by
  have h' : 1 + 1 * c ≠ 0 := by simpa using h
  rw [← longBlock_sl2Upper i 1, ← longBlock_sl2Lower i c, ← map_mul,
    sl2Upper_mul_sl2Lower_of_ne h', map_mul, map_mul, longBlock_sl2Lower,
    longBlock_diagUnit_eq_diagHom, longBlock_sl2Upper]
  simp only [one_mul]

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg
  CFSG.SeitzReduction.LinearPilot in
private theorem spGL_block_sing {K : Type} [Field K] [CharP K 2] {n : ℕ} (i : Fin n) :
    elt (.positiveLong i) 1 * elt (.negativeLong i) 1 =
      longBlock K n i (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) * elt (.positiveLong i) 1 := by
  have hsing : sl2Upper (1 : K) * sl2Lower 1 =
      sl2Upper 1 * sl2Lower (-1) * sl2Upper 1 * sl2Upper 1 := by
    have hdiag : diagUnit (Units.mk0 (1 : K) one_ne_zero)⁻¹ = 1 := by
      rw [show Units.mk0 (1 : K) one_ne_zero = 1 from Units.ext rfl, inv_one]
      exact Subtype.ext (by ext a b; fin_cases a <;> fin_cases b <;> simp [diagUnit])
    rw [sl2Upper_mul_sl2Lower_of_eq (a := 1) (b := 1) one_ne_zero (by
      rw [mul_one]; exact CharTwo.add_self_eq_zero 1), hdiag,
      show sl2Upper (-1 : K) = sl2Upper 1 from congrArg sl2Upper (CharTwo.neg_eq 1)]
    group
  rw [← longBlock_sl2Upper i 1, ← longBlock_sl2Lower i 1, ← map_mul, hsing, map_mul, map_mul,
    longBlock_sl2Upper]

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Steinberg in
private theorem spGL_mat_weyl_mul {K : Type} [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} :
    mat n K (longBlock K n i (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) *
        longBlock K n j (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)) =
      Equiv.Perm.permMatrix K
        (spMonoPerm 1 (fun c => CFSG.StandardType.spSgn j c *
          CFSG.StandardType.spSgn i c)).symm := by
  rw [map_mul, mat_longBlock_weyl i, mat_longBlock_weyl j]
  change Matrix.permMatrixHom (spMonoPerm 1 (CFSG.StandardType.spSgn i)) *
      Matrix.permMatrixHom (spMonoPerm 1 (CFSG.StandardType.spSgn j)) =
    Matrix.permMatrixHom (spMonoPerm 1
      (fun c => CFSG.StandardType.spSgn j c * CFSG.StandardType.spSgn i c))
  rw [← map_mul, ← spMonoPerm_mul (CFSG.StandardType.spIsSign_spSgn i)
    (CFSG.StandardType.spIsSign_spSgn j)]
  simp only [one_mul, Equiv.Perm.one_apply]

private theorem spGL_calc_nonsing {G : Type} [Group G] {L0 H0 U0 L1 H1 U1 : G}
    (h : Commute U0 (L1 * H1)) :
    L0 * H0 * U0 * (L1 * H1 * U1) =
      L0 * (H0 * L1 * H0⁻¹) * (H0 * H1) * (U0 * U1) := by
  calc L0 * H0 * U0 * (L1 * H1 * U1)
      = L0 * H0 * (U0 * (L1 * H1)) * U1 := by group
    _ = L0 * H0 * ((L1 * H1) * U0) * U1 := by rw [h.eq]
    _ = L0 * (H0 * L1 * H0⁻¹) * (H0 * H1) * (U0 * U1) := by group

private theorem spGL_calc_left {G : Type} [Group G] {W0 U0 L1 H1 U1 : G}
    (h1 : Commute U0 (L1 * H1)) (h2 : Commute W0 L1) :
    W0 * U0 * (L1 * H1 * U1) = L1 * W0 * H1 * (U0 * U1) := by
  calc W0 * U0 * (L1 * H1 * U1)
      = W0 * (U0 * (L1 * H1)) * U1 := by group
    _ = W0 * ((L1 * H1) * U0) * U1 := by rw [h1.eq]
    _ = (W0 * L1) * H1 * (U0 * U1) := by group
    _ = (L1 * W0) * H1 * (U0 * U1) := by rw [h2.eq]

private theorem spGL_calc_right {G : Type} [Group G] {L0 H0 U0 W1 U1 : G}
    (h1 : Commute U0 W1) (h2 : Commute W1 H0) :
    L0 * H0 * U0 * (W1 * U1) = L0 * W1 * H0 * (U0 * U1) := by
  calc L0 * H0 * U0 * (W1 * U1)
      = L0 * H0 * (U0 * W1) * U1 := by group
    _ = L0 * H0 * (W1 * U0) * U1 := by rw [h1.eq]
    _ = L0 * (H0 * W1) * (U0 * U1) := by group
    _ = L0 * W1 * H0 * (U0 * U1) := by rw [h2.eq.symm]; group

private theorem spGL_calc_both {G : Type} [Group G] {W0 U0 W1 U1 : G}
    (h : Commute U0 W1) :
    W0 * U0 * (W1 * U1) = W0 * W1 * (U0 * U1) := by
  calc W0 * U0 * (W1 * U1)
      = W0 * (U0 * W1) * U1 := by group
    _ = W0 * (W1 * U0) * U1 := by rw [h.eq]
    _ = W0 * W1 * (U0 * U1) := by group

open CFSG.StandardType CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg in
private theorem spGL_value_nonsing {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1) {t v : K}
    (htne : 1 + t ≠ 0) (hvne : 1 + v ≠ 0) :
    f (ρ (elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v)) y₀) = 1 := by
  set i0 : Fin n := spGL_i0 n hn with hi0
  set i1 : Fin n := spGL_i1 n hn with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1]
  have h10 : i1 ≠ i0 := h01.symm
  have hfac0 := spGL_block_nonsing (K := K) (n := n) (i := i0) (c := t) htne
  have hfac1 := spGL_block_nonsing (K := K) (n := n) (i := i1) (c := v) hvne
  let L0 : StatedSp n K := elt (.negativeLong i0) (t / (1 + t))
  let H0 := diagHom n K (Pi.mulSingle i0 (Units.mk0 (1 + t) htne))
  let U0 : StatedSp n K := elt (.positiveLong i0) (1 / (1 + t))
  let L1 : StatedSp n K := elt (.negativeLong i1) (v / (1 + v))
  let H1 := diagHom n K (Pi.mulSingle i1 (Units.mk0 (1 + v) hvne))
  let U1 : StatedSp n K := elt (.positiveLong i1) (1 / (1 + v))
  have hL0 : L0 ∈ (spCurtisDatum n K).L := spGL_neg_mem_L i0 _
  have hH0 : H0 ∈ (spCurtisDatum n K).H := diagHom_mem_spCurtisDatum_H _
  have hU0 : U0 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i0 _
  have hL1 : L1 ∈ (spCurtisDatum n K).L := spGL_neg_mem_L i1 _
  have hH1 : H1 ∈ (spCurtisDatum n K).H := diagHom_mem_spCurtisDatum_H _
  have hU1 : U1 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i1 _
  have hcomm : Commute U0 (L1 * H1) :=
    Commute.mul_right (spGL_commute_pos_neg (K := K) h01 (1 / (1 + t)) (v / (1 + v)))
      (spGL_commute_pos_diag (K := K) h01 (1 / (1 + t)) (Units.mk0 (1 + v) hvne))
  have hrearr := spGL_rearrange (A0 := elt (.positiveLong i0) 1)
    (A1 := elt (.positiveLong i1) 1) (B0 := elt (.negativeLong i0) t)
    (B1 := elt (.negativeLong i1) v) (spGL_commute_pos_neg (K := K) h10 1 t)
  have hgfac : elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v) =
      L0 * (H0 * L1 * H0⁻¹) * (H0 * H1) * (U0 * U1) := by
    rw [hrearr, hfac0, hfac1, spGL_calc_nonsing hcomm]
  refine spGL_value_eq_one ht hf hfy hχ ?_ ?_ ?_ hgfac
  · exact mul_mem hL0 ((spCurtisDatum n K).H_normL H0 hH0 L1 hL1)
  · exact mul_mem hH0 hH1
  · exact mul_mem hU0 hU1

open CFSG.StandardType CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg in
private theorem spGL_value_left_sing {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    {i : Fin n} (hi : i.val + 1 = n) (hμ : μ i = (spCurtisDatum n K).dScalar χ i) {t v : K}
    (ht1 : 1 + t = 0) (hvne : 1 + v ≠ 0) :
    f (ρ (elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v)) y₀) = 0 := by
  have ht' : t = 1 := ((CharTwo.add_eq_zero (a := 1) (b := t)).mp ht1).symm
  set i0 : Fin n := spGL_i0 n hn with hi0
  set i1 : Fin n := spGL_i1 n hn with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1]
  have h10 : i1 ≠ i0 := h01.symm
  have hfac0 := spGL_block_sing (K := K) (n := n) i0
  have hfac1 := spGL_block_nonsing (K := K) (n := n) (i := i1) (c := v) hvne
  let W0 := longBlock K n i0 (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)
  let U0 : StatedSp n K := elt (.positiveLong i0) 1
  let L1 : StatedSp n K := elt (.negativeLong i1) (v / (1 + v))
  let H1 := diagHom n K (Pi.mulSingle i1 (Units.mk0 (1 + v) hvne))
  let U1 : StatedSp n K := elt (.positiveLong i1) (1 / (1 + v))
  have hU0 : U0 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i0 1
  have hL1 : L1 ∈ (spCurtisDatum n K).L := spGL_neg_mem_L i1 _
  have hH1 : H1 ∈ (spCurtisDatum n K).H := diagHom_mem_spCurtisDatum_H _
  have hU1 : U1 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i1 _
  obtain ⟨x, hx, hnW⟩ :=
    exists_nW_eq_of_mat_eq (n := n) (spIsSign_spSgn i0) (mat_longBlock_weyl (K := K) i0)
  have hnW' : (spCurtisDatum n K).nW x = W0 := hnW
  have hcomm1 : Commute U0 (L1 * H1) :=
    Commute.mul_right (spGL_commute_pos_neg (K := K) h01 1 (v / (1 + v)))
      (spGL_commute_pos_diag (K := K) h01 1 (Units.mk0 (1 + v) hvne))
  have hcomm2 : Commute W0 L1 := spGL_commute_block_neg (K := K) h01 _ _
  have hrearr := spGL_rearrange (A0 := elt (.positiveLong i0) 1)
    (A1 := elt (.positiveLong i1) 1) (B0 := elt (.negativeLong i0) t)
    (B1 := elt (.negativeLong i1) v) (spGL_commute_pos_neg (K := K) h10 1 t)
  have hgfac : elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v) =
      L1 * (spCurtisDatum n K).nW x * H1 * (U0 * U1) := by
    rw [hrearr, ht', hfac0, hfac1, spGL_calc_left hcomm1 hcomm2, ← hnW']
  have hne : spSgn i0 ≠ 1 := spGL_spSgn_ne_one i0
  rw [hgfac]
  exact spGL_form_nW_eq_zero ht hf hfy hi hμ hx (spIsSign_spSgn i0) hne hL1 hH1
    (mul_mem hU0 hU1)

open CFSG.StandardType CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg in
private theorem spGL_value_right_sing {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    {i : Fin n} (hi : i.val + 1 = n) (hμ : μ i = (spCurtisDatum n K).dScalar χ i) {t v : K}
    (htne : 1 + t ≠ 0) (hv1 : 1 + v = 0) :
    f (ρ (elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v)) y₀) = 0 := by
  have hv' : v = 1 := ((CharTwo.add_eq_zero (a := 1) (b := v)).mp hv1).symm
  set i0 : Fin n := spGL_i0 n hn with hi0
  set i1 : Fin n := spGL_i1 n hn with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1]
  have h10 : i1 ≠ i0 := h01.symm
  have hfac0 := spGL_block_nonsing (K := K) (n := n) (i := i0) (c := t) htne
  have hfac1 := spGL_block_sing (K := K) (n := n) i1
  let L0 : StatedSp n K := elt (.negativeLong i0) (t / (1 + t))
  let H0 := diagHom n K (Pi.mulSingle i0 (Units.mk0 (1 + t) htne))
  let U0 : StatedSp n K := elt (.positiveLong i0) (1 / (1 + t))
  let W1 := longBlock K n i1 (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)
  let U1 : StatedSp n K := elt (.positiveLong i1) 1
  have hL0 : L0 ∈ (spCurtisDatum n K).L := spGL_neg_mem_L i0 _
  have hH0 : H0 ∈ (spCurtisDatum n K).H := diagHom_mem_spCurtisDatum_H _
  have hU0 : U0 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i0 _
  have hU1 : U1 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i1 1
  obtain ⟨x, hx, hnW⟩ :=
    exists_nW_eq_of_mat_eq (n := n) (spIsSign_spSgn i1) (mat_longBlock_weyl (K := K) i1)
  have hnW' : (spCurtisDatum n K).nW x = W1 := hnW
  have hcomm1 : Commute U0 W1 := spGL_commute_pos_block (K := K) h01 _ _
  have hcomm2 : Commute W1 H0 := spGL_commute_block_diag (K := K) h10 _ _
  have hrearr := spGL_rearrange (A0 := elt (.positiveLong i0) 1)
    (A1 := elt (.positiveLong i1) 1) (B0 := elt (.negativeLong i0) t)
    (B1 := elt (.negativeLong i1) v) (spGL_commute_pos_neg (K := K) h10 1 t)
  have hgfac : elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v) =
      L0 * (spCurtisDatum n K).nW x * H0 * (U0 * U1) := by
    rw [hrearr, hv', hfac0, hfac1, spGL_calc_right hcomm1 hcomm2, ← hnW']
  have hne : spSgn i1 ≠ 1 := spGL_spSgn_ne_one i1
  rw [hgfac]
  exact spGL_form_nW_eq_zero ht hf hfy hi hμ hx (spIsSign_spSgn i1) hne hL0 hH0
    (mul_mem hU0 hU1)

open CFSG.StandardType CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg in
private theorem spGL_value_both_sing {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    {i : Fin n} (hi : i.val + 1 = n) (hμ : μ i = (spCurtisDatum n K).dScalar χ i) {t v : K}
    (ht1 : 1 + t = 0) (hv1 : 1 + v = 0) :
    f (ρ (elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v)) y₀) = 0 := by
  have ht' : t = 1 := ((CharTwo.add_eq_zero (a := 1) (b := t)).mp ht1).symm
  have hv' : v = 1 := ((CharTwo.add_eq_zero (a := 1) (b := v)).mp hv1).symm
  set i0 : Fin n := spGL_i0 n hn with hi0
  set i1 : Fin n := spGL_i1 n hn with hi1
  have h01 : i0 ≠ i1 := by simp [hi0, hi1]
  have h10 : i1 ≠ i0 := h01.symm
  have hfac0 := spGL_block_sing (K := K) (n := n) i0
  have hfac1 := spGL_block_sing (K := K) (n := n) i1
  let W0 := longBlock K n i0 (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)
  let W1 := longBlock K n i1 (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)
  let U0 : StatedSp n K := elt (.positiveLong i0) 1
  let U1 : StatedSp n K := elt (.positiveLong i1) 1
  have hU0 : U0 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i0 1
  have hU1 : U1 ∈ (spCurtisDatum n K).U := spGL_pos_mem_U i1 1
  let s : Fin n → ℤ := fun c => spSgn i1 c * spSgn i0 c
  have hs : SpIsSign s := spGL_spSgn_mul_sign i1 i0
  have hne : s ≠ 1 := spGL_spSgn_mul_ne_one h10
  obtain ⟨x, hx, hnW⟩ :=
    exists_nW_eq_of_mat_eq (n := n) hs (spGL_mat_weyl_mul (K := K))
  have hnW' : (spCurtisDatum n K).nW x = W0 * W1 := hnW
  have hcomm1 : Commute U0 W1 := spGL_commute_pos_block (K := K) h01 _ _
  have hrearr := spGL_rearrange (A0 := elt (.positiveLong i0) 1)
    (A1 := elt (.positiveLong i1) 1) (B0 := elt (.negativeLong i0) t)
    (B1 := elt (.negativeLong i1) v) (spGL_commute_pos_neg (K := K) h10 1 t)
  have hgfac : elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v) =
      (1 : StatedSp n K) * (spCurtisDatum n K).nW x * 1 * (U0 * U1) := by
    rw [hrearr, ht', hv', hfac0, hfac1, spGL_calc_both hcomm1, ← hnW']
    simp only [U0, U1]
    group
  rw [hgfac]
  exact spGL_form_nW_eq_zero ht hf hfy hi hμ hx hs hne (one_mem _) (one_mem _)
    (mul_mem hU0 hU1)

private theorem spGL_rhs_one {K : Type} [Field K] [Finite K] {k : Type} [Field k]
    (ι : K →+* k) {t : K} (htne : 1 + t ≠ 0) :
    (1 + ι t) ^ (Nat.card K - 1) = 1 := by
  have hfin : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card,
    show (1 : k) + ι t = ι (1 + t) by rw [map_add, map_one], ← map_pow,
    FiniteField.pow_card_sub_one_eq_one (1 + t) htne, map_one]

private theorem spGL_rhs_nonsing {K : Type} [Field K] [Finite K] {k : Type} [Field k]
    (ι : K →+* k) {t v : K} (htne : 1 + t ≠ 0) (hvne : 1 + v ≠ 0) :
    (1 + ι t) ^ (Nat.card K - 1) * (1 + ι v) ^ (Nat.card K - 1) = 1 := by
  rw [spGL_rhs_one ι htne, spGL_rhs_one ι hvne, mul_one]

private theorem spGL_rhs_zero {K : Type} [Field K] [Finite K] {k : Type} [Field k]
    (ι : K →+* k) {t : K} (ht1 : 1 + t = 0) :
    (1 + ι t) ^ (Nat.card K - 1) = 0 := by
  have hcard : 2 ≤ Nat.card K := by
    have hfin : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hbase : (1 : k) + ι t = 0 := by
    calc (1 : k) + ι t = ι 1 + ι t := by rw [ι.map_one]
      _ = ι (1 + t) := by rw [ι.map_add]
      _ = ι 0 := by rw [ht1]
      _ = 0 := by rw [ι.map_zero]
  rw [hbase, zero_pow (by omega)]

theorem form_long_mul_long {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    {k : Type} [Field k] (ι : K →+* k) {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (StatedSp n K) V} {y₀ : V} {χ : StatedSp n K → k} {μ : Fin n → k}
    (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ) {f : Module.Dual k V}
    (hf : ∀ z ∈ augSub ρ (spCurtisDatum n K).L, f z = 0) (hfy : f y₀ = 1)
    (hχ : ∀ h ∈ (spCurtisDatum n K).H, χ h = 1)
    (hμ : μ ⟨n - 1, by omega⟩ = (spCurtisDatum n K).dScalar χ (⟨n - 1, by omega⟩ : Fin n))
    (t v : K) :
    f (ρ (elt (.positiveLong ⟨0, by omega⟩) 1 * elt (.positiveLong ⟨1, by omega⟩) 1 *
      (elt (.negativeLong ⟨0, by omega⟩) t * elt (.negativeLong ⟨1, by omega⟩) v)) y₀) =
      (1 + ι t) ^ (Nat.card K - 1) * (1 + ι v) ^ (Nat.card K - 1) := by
  have hi : (⟨n - 1, by omega⟩ : Fin n).val + 1 = n := by
    rw [Fin.val_mk]
    omega
  by_cases ht1 : 1 + t = 0
  · by_cases hv1 : 1 + v = 0
    · rw [spGL_value_both_sing (n := n) hn ht hf hfy (i := ⟨n - 1, by omega⟩) hi hμ ht1 hv1,
        spGL_rhs_zero ι ht1, spGL_rhs_zero ι hv1, mul_zero]
    · rw [spGL_value_left_sing (n := n) hn ht hf hfy (i := ⟨n - 1, by omega⟩) hi hμ ht1 hv1,
        spGL_rhs_zero ι ht1, spGL_rhs_one ι hv1, mul_one]
  · by_cases hv1 : 1 + v = 0
    · rw [spGL_value_right_sing (n := n) hn ht hf hfy (i := ⟨n - 1, by omega⟩) hi hμ ht1 hv1,
        spGL_rhs_one ι ht1, spGL_rhs_zero ι hv1, one_mul]
    · rw [spGL_value_nonsing (n := n) hn ht hf hfy hχ ht1 hv1,
        spGL_rhs_nonsing ι ht1 hv1]

end CFSG.LocalAnalysis.WeakClosure81
