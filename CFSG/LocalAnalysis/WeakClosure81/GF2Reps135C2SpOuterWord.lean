module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.HardMathSupport.U4FF.ClassFinalConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.GH74.KGroups

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
@[expose] def spOuterPairWord {C : Type} [Field C] (φ : C → C)
    (h : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C) (ps : List (Fin 3 × Fin 3)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C :=
  (ps.map fun p => -(gram C 3 * (h p.1).transpose * gram C 3) *
    (h p.1 * -(gram C 3 * (h p.2).transpose * gram C 3)).map φ * h p.2).prod

@[expose] def spOuterConjF4 : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) GF4 :=
  ![1,
    Matrix.map (Matrix.fromBlocks !![2, 2, 1; 1, 3, 3; 2, 0, 0] !![3, 3, 3; 2, 2, 3; 1, 0, 3]
      !![2, 3, 3; 0, 2, 1; 0, 0, 1] !![0, 0, 0; 2, 0, 1; 1, 3, 0]) GF4.ofNat',
    Matrix.map (Matrix.fromBlocks !![0, 2, 3; 2, 0, 2; 2, 2, 1] !![2, 0, 3; 0, 0, 3; 0, 3, 2]
      !![1, 1, 0; 3, 0, 0; 1, 0, 2] !![1, 0, 1; 2, 1, 1; 0, 3, 3]) GF4.ofNat']

@[expose] def spOuterWordF4 : List (Fin 3 × Fin 3) :=
  [(0, 2), (0, 1), (0, 2), (1, 2), (0, 1), (2, 1), (0, 1), (0, 1)]

@[expose] def spOuterConjF16 : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) GF16 :=
  ![1,
    Matrix.map (Matrix.fromBlocks !![5, 1, 0; 14, 7, 4; 12, 9, 0] !![6, 7, 0; 4, 3, 2; 4, 3, 15]
      !![14, 9, 8; 7, 10, 4; 7, 12, 1] !![3, 6, 8; 9, 9, 8; 2, 9, 7]) GF16.ofNat',
    1]

@[expose] def spOuterWordF16 : List (Fin 3 × Fin 3) := [(0, 1), (0, 1), (0, 1), (0, 1), (0, 1)]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
theorem spOuterConjF4_symplectic :
    ∀ i : Fin 3, (spOuterConjF4 i).transpose * gram GF4 3 * spOuterConjF4 i = gram GF4 3 := by
  decide +kernel

theorem spOuterPairWordF4_pow_thirteen :
    spOuterPairWord (· ^ 2) spOuterConjF4 spOuterWordF4 ^ 13 = 1 := by
  decide +kernel

theorem spOuterPairWordF4_ne_one : spOuterPairWord (· ^ 2) spOuterConjF4 spOuterWordF4 ≠ 1 := by
  decide +kernel

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
theorem spOuterConjF16_symplectic :
    ∀ i : Fin 3, (spOuterConjF16 i).transpose * gram GF16 3 * spOuterConjF16 i = gram GF16 3 := by
  decide +kernel

theorem spOuterPairWordF16_pow_thirteen :
    spOuterPairWord (· ^ 4) spOuterConjF16 spOuterWordF16 ^ 13 = 1 := by
  decide +kernel

theorem spOuterPairWordF16_ne_one :
    spOuterPairWord (· ^ 4) spOuterConjF16 spOuterWordF16 ≠ 1 := by
  decide +kernel

theorem spOuter_gf4_pow_eight_eq_sq : ∀ c : GF4, c ^ 8 = c ^ 2 := by
  decide +kernel

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
private theorem w135c2_spWord_gram_map {C F : Type} [Field C] [Field F] (ι : C →+* F) (m : ℕ) :
    (gram C m).map ι = gram F m := by
  rw [gram, gram, Matrix.fromBlocks_map]
  simp only [Matrix.map_zero ι (map_zero ι), Matrix.map_one ι (map_zero ι) (map_one ι),
    Matrix.map_neg ι (map_neg ι)]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
private theorem w135c2_spWord_inv_map {C F : Type} [Field C] [Field F] (ι : C →+* F) {m : ℕ}
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) C) :
    (-(gram C m * M.transpose * gram C m)).map ι =
      -(gram F m * (M.map ι).transpose * gram F m) := by
  rw [Matrix.map_neg ι (map_neg ι), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    w135c2_spWord_gram_map ι m]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
private theorem w135c2_spWord_symplectic_map {C F : Type} [Field C] [Field F] (ι : C →+* F)
    (h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C)
    (hh : h.transpose * gram C 3 * h = gram C 3) :
    (h.map ι).transpose * gram F 3 * h.map ι = gram F 3 := by
  have h' := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C => M.map ι) hh
  simp only [Matrix.map_mul, Matrix.transpose_map, w135c2_spWord_gram_map ι 3] at h'
  exact h'

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedMat spIncl spIncl_apply) in
private theorem w135c2_spWord_spEmbedMat_map {F : Type} [Field F] {m n : ℕ} (s : Fin m → Fin n)
    (σ : F ≃+* F) (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    (spEmbedMat s M).map σ = spEmbedMat s (M.map σ) := by
  have hP : (spIncl (K := F) s).map σ = spIncl (K := F) s := by
    ext a b
    rw [Matrix.map_apply, spIncl_apply]
    split_ifs <;> simp
  rw [spEmbedMat, spEmbedMat, Matrix.map_add σ (map_add σ.toRingHom), Matrix.map_mul,
    Matrix.map_mul, Matrix.map_sub σ (map_sub σ.toRingHom),
    Matrix.map_one σ (map_zero σ.toRingHom) (map_one σ.toRingHom),
    Matrix.map_one σ (map_zero σ.toRingHom) (map_one σ.toRingHom), Matrix.transpose_map, hP]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
open CFSG.LieType.Universal.Symplectic.SpExtras (mat) in
private theorem w135c2_spWord_coe_fieldSp {F : Type} [Field F] {m : ℕ} (σ : F ≃+* F)
    (g : StatedSp m F) : mat m F (fieldSp m F σ g) = (mat m F g).map σ := rfl

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed mat_spEmbed) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective) in
private theorem w135c2_spWord_fieldSp_spEmbed {F : Type} [Field F] {m n : ℕ} (s : Fin m → Fin n)
    (hs : Function.Injective s) (σ : F ≃+* F) (g : StatedSp m F) :
    fieldSp n F σ (spEmbed s hs g) = spEmbed s hs (fieldSp m F σ g) := by
  apply mat_injective
  rw [w135c2_spWord_coe_fieldSp, mat_spEmbed, mat_spEmbed, w135c2_spWord_coe_fieldSp]
  exact w135c2_spWord_spEmbedMat_map s σ (mat m F g)

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram ofSymplecticMat mat_ofSymplecticMat) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
open CFSG.LieType.Universal.Symplectic.SpExtras (mat) in
private theorem w135c2_spWord_factor {C F : Type} [Field C] [Field F] (ι : C →+* F)
    {φ : C → C} {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι (φ c))
    {h : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C}
    (hh : ∀ i, (h i).transpose * gram C 3 * h i = gram C 3) :
    ∃ k : Fin 3 → StatedSp 3 F, ∀ p : Fin 3 × Fin 3,
      mat 3 F ((k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2) =
        (-(gram C 3 * (h p.1).transpose * gram C 3) *
          (h p.1 * -(gram C 3 * (h p.2).transpose * gram C 3)).map φ * h p.2).map ι := by
  let k : Fin 3 → StatedSp 3 F := fun i =>
    ofSymplecticMat ((h i).map ι) (w135c2_spWord_symplectic_map ι (h i) (hh i))
  have hk : ∀ i, mat 3 F (k i) = (h i).map ι := fun i => mat_ofSymplecticMat _ _
  have hinv : ∀ i, mat 3 F (k i)⁻¹ = (-(gram C 3 * (h i).transpose * gram C 3)).map ι := by
    intro i
    rw [show mat 3 F (k i)⁻¹ = -(gram F 3 * ((h i).map ι).transpose * gram F 3) from rfl]
    exact (w135c2_spWord_inv_map ι (h i)).symm
  have hfield : ∀ p : Fin 3 × Fin 3,
      mat 3 F (fieldSp 3 F σ (k p.1 * (k p.2)⁻¹)) =
      ((h p.1 * -(gram C 3 * (h p.2).transpose * gram C 3)).map φ).map ι := by
    intro p
    rw [w135c2_spWord_coe_fieldSp, map_mul, hinv, hk, ← Matrix.map_mul, Matrix.map_map,
      Matrix.map_map]
    congr 1
    funext c
    exact hσ c
  refine ⟨k, fun p => ?_⟩
  rw [map_mul, map_mul, hinv, hfield, hk]
  rw [← Matrix.map_mul, ← Matrix.map_mul]

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram ofSymplecticMat mat_ofSymplecticMat) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
open CFSG.LieType.Universal.Symplectic.SpExtras (mat) in
private theorem w135c2_spWord_mat_word {C F : Type} [Field C] [Field F] (ι : C →+* F)
    {φ : C → C} {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι (φ c))
    {h : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C}
    (hh : ∀ i, (h i).transpose * gram C 3 * h i = gram C 3) (ps : List (Fin 3 × Fin 3)) :
    ∃ k : Fin 3 → StatedSp 3 F,
      mat 3 F (ps.map fun p => (k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2).prod =
        (spOuterPairWord φ h ps).map ι := by
  obtain ⟨k, hfactor⟩ := w135c2_spWord_factor ι hσ hh
  let fMat : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C →*
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    { toFun := fun M => M.map ι
      map_one' := Matrix.map_one ι (map_zero ι) (map_one ι)
      map_mul' := fun M N => Matrix.map_mul }
  let FC : Fin 3 × Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C := fun p =>
    -(gram C 3 * (h p.1).transpose * gram C 3) *
      (h p.1 * -(gram C 3 * (h p.2).transpose * gram C 3)).map φ * h p.2
  let F3 : Fin 3 × Fin 3 → StatedSp 3 F := fun p =>
    (k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2
  have hfactor' : ∀ p : Fin 3 × Fin 3, mat 3 F (F3 p) = (FC p).map ι := hfactor
  refine ⟨k, ?_⟩
  have hword : mat 3 F (ps.map F3).prod = (spOuterPairWord φ h ps).map ι := by
    rw [map_list_prod]
    have hmap : (ps.map F3).map (mat 3 F) = (ps.map FC).map fMat := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p _
      exact hfactor' p
    rw [hmap]
    rw [show spOuterPairWord φ h ps = (ps.map FC).prod from rfl]
    exact List.prod_hom (ps.map FC) fMat
  exact hword

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective) in
private theorem w135c2_spWord_orderOf_three {C F : Type} [Field C] [Field F] (ι : C →+* F)
    {φ : C → C} {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι (φ c))
    {h : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C}
    (hh : ∀ i, (h i).transpose * gram C 3 * h i = gram C 3) {ps : List (Fin 3 × Fin 3)}
    (h13 : spOuterPairWord φ h ps ^ 13 = 1) (hne1 : spOuterPairWord φ h ps ≠ 1) :
    ∃ k : Fin 3 → StatedSp 3 F,
      orderOf (ps.map fun p => (k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2).prod =
        13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨k, hword⟩ := w135c2_spWord_mat_word ι hσ hh ps
  let F3 : Fin 3 × Fin 3 → StatedSp 3 F := fun p =>
    (k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2
  have hword' : mat 3 F (ps.map F3).prod = (spOuterPairWord φ h ps).map ι := hword
  have hpow : (ps.map F3).prod ^ 13 = 1 := by
    apply mat_injective
    calc mat 3 F ((ps.map F3).prod ^ 13) = mat 3 F (ps.map F3).prod ^ 13 :=
          map_pow (mat 3 F) _ 13
      _ = (spOuterPairWord φ h ps).map ι ^ 13 := by rw [hword']
      _ = ((spOuterPairWord φ h ps) ^ 13).map ι := (Matrix.map_pow _ ι 13).symm
      _ = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C).map ι := by rw [h13]
      _ = 1 := Matrix.map_one ι (map_zero ι) (map_one ι)
      _ = mat 3 F 1 := (map_one (mat 3 F)).symm
  have hne : (ps.map F3).prod ≠ 1 := by
    intro hw
    apply hne1
    have hmap : (spOuterPairWord φ h ps).map ι =
        (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C).map ι := by
      rw [← hword', hw, map_one (mat 3 F), Matrix.map_one ι (map_zero ι) (map_one ι)]
    exact Matrix.map_injective ι.injective hmap
  exact ⟨k, orderOf_eq_prime hpow hne⟩

open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram spEmbed spEmbed_injective) in
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
private theorem w135c2_spWord_transport {C F : Type} [Field C] [Field F] {n : ℕ} (hn : 3 ≤ n)
    (ι : C →+* F) {φ : C → C} {σ : F ≃+* F} (hσ : ∀ c, σ (ι c) = ι (φ c))
    {h : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) C}
    (hh : ∀ i, (h i).transpose * gram C 3 * h i = gram C 3) {ps : List (Fin 3 × Fin 3)}
    (h13 : spOuterPairWord φ h ps ^ 13 = 1) (hne1 : spOuterPairWord φ h ps ≠ 1) :
    ∃ k : Fin 3 → StatedSp n F,
      orderOf (ps.map fun p => (k p.1)⁻¹ * fieldSp n F σ (k p.1 * (k p.2)⁻¹) * k p.2).prod =
        13 := by
  obtain ⟨k, hk⟩ := w135c2_spWord_orderOf_three ι hσ hh h13 hne1
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let s : Fin 3 → Fin n := Fin.castLE hn
  have hs : Function.Injective s := Fin.castLE_injective hn
  let F3 : Fin 3 × Fin 3 → StatedSp 3 F := fun p =>
    (k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2
  let Fn : Fin 3 × Fin 3 → StatedSp n F := fun p =>
    (spEmbed s hs (k p.1))⁻¹ *
      fieldSp n F σ (spEmbed s hs (k p.1) * (spEmbed s hs (k p.2))⁻¹) * spEmbed s hs (k p.2)
  refine ⟨fun i => spEmbed s hs (k i), ?_⟩
  have hfactor : ∀ p : Fin 3 × Fin 3, spEmbed s hs (F3 p) = Fn p := by
    intro p
    show spEmbed s hs ((k p.1)⁻¹ * fieldSp 3 F σ (k p.1 * (k p.2)⁻¹) * k p.2) =
      (spEmbed s hs (k p.1))⁻¹ *
        fieldSp n F σ (spEmbed s hs (k p.1) * (spEmbed s hs (k p.2))⁻¹) * spEmbed s hs (k p.2)
    rw [map_mul, map_mul, map_inv]
    rw [← w135c2_spWord_fieldSp_spEmbed s hs σ (k p.1 * (k p.2)⁻¹)]
    rw [map_mul, map_inv]
  have hword : (ps.map Fn).prod = spEmbed s hs (ps.map F3).prod := by
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro p _
    exact (hfactor p).symm
  change orderOf (ps.map Fn).prod = 13
  have h3 : (ps.map F3).prod ^ 13 = 1 ∧ (ps.map F3).prod ≠ 1 :=
    orderOf_eq_prime_iff.mp hk
  have hpow' : (ps.map Fn).prod ^ 13 = 1 := by
    rw [hword, ← map_pow (spEmbed s hs) (ps.map F3).prod 13, h3.1, map_one]
  have hne' : (ps.map Fn).prod ≠ 1 := by
    intro h1
    apply h3.2
    apply spEmbed_injective hs
    rw [← hword, h1, map_one]
  exact orderOf_eq_prime hpow' hne'

private theorem w135c2_spWord_nonempty_ringHom_gf4 {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ∣ f) : Nonempty (GF4 →+* F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP GF4 2 := charP_of_card_eq_prime_pow (f := 2) rfl
  exact CFSG.HardMathSupport.U4FF.ClassFinal.exists_ringHom_of_dvd
    (by rw [Nat.card_eq_fintype_card]; rfl) hF hf

private theorem w135c2_spWord_nonempty_ringHom_gf16 {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 4 ∣ f) : Nonempty (GF16 →+* F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP GF16 2 := charP_of_card_eq_prime_pow (f := 4) rfl
  exact CFSG.HardMathSupport.U4FF.ClassFinal.exists_ringHom_of_dvd
    (by rw [Nat.card_eq_fintype_card]; rfl) hF hf

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
theorem w135c2_sp_exists_pairWord_orderOf_eq_thirteen {F : Type} [Field F] {n f : ℕ}
    (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ f) (hfe : Even f) (hf : f ≤ 6) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 2 ^ (f / 2)) :
    ∃ (k : Fin 3 → StatedSp n F) (ps : List (Fin 3 × Fin 3)),
      orderOf (ps.map fun p => (k p.1)⁻¹ * fieldSp n F σ (k p.1 * (k p.2)⁻¹) * k p.2).prod =
        13 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card F ≠ 0 := by rw [hF]; exact pow_ne_zero f (by norm_num)
  have : Finite F := Nat.finite_of_card_ne_zero hcard
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card]; exact hF)
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hF
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hcases : f = 2 ∨ f = 4 ∨ f = 6 := by
    obtain ⟨m, rfl⟩ := hfe
    have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm with rfl | rfl | rfl <;> norm_num
  rcases hcases with rfl | rfl | rfl
  · obtain ⟨ι⟩ := w135c2_spWord_nonempty_ringHom_gf4 hF (by norm_num)
    have hσ' : ∀ c : GF4, σ (ι c) = ι (c ^ 2) := by
      intro c
      rw [hσ, show 2 ^ (2 / 2) = 2 by norm_num]
      exact (map_pow ι c 2).symm
    obtain ⟨k, hk⟩ := w135c2_spWord_transport hn ι hσ' spOuterConjF4_symplectic
      spOuterPairWordF4_pow_thirteen spOuterPairWordF4_ne_one
    exact ⟨k, spOuterWordF4, hk⟩
  · obtain ⟨ι⟩ := w135c2_spWord_nonempty_ringHom_gf16 hF (by norm_num)
    have hσ' : ∀ c : GF16, σ (ι c) = ι (c ^ 4) := by
      intro c
      rw [hσ, show 2 ^ (4 / 2) = 4 by norm_num]
      exact (map_pow ι c 4).symm
    obtain ⟨k, hk⟩ := w135c2_spWord_transport hn ι hσ' spOuterConjF16_symplectic
      spOuterPairWordF16_pow_thirteen spOuterPairWordF16_ne_one
    exact ⟨k, spOuterWordF16, hk⟩
  · obtain ⟨ι⟩ := w135c2_spWord_nonempty_ringHom_gf4 hF (by norm_num)
    have hσ' : ∀ c : GF4, σ (ι c) = ι (c ^ 2) := by
      intro c
      rw [hσ, show 2 ^ (6 / 2) = 8 by norm_num, ← map_pow ι c 8,
        spOuter_gf4_pow_eight_eq_sq]
    obtain ⟨k, hk⟩ := w135c2_spWord_transport hn ι hσ' spOuterConjF4_symplectic
      spOuterPairWordF4_pow_thirteen spOuterPairWordF4_ne_one
    exact ⟨k, spOuterWordF4, hk⟩

end CFSG.LocalAnalysis.WeakClosure81
