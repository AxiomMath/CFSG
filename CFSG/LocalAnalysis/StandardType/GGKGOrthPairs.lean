module

public import CFSG.LocalAnalysis.StandardType.GGKGAdjDefs
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE8F CFSG.StandardType.TableBExc.E6Three
  CFSG.SeitzReduction CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem kGL_wordProd_smul_E6 (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (coxeterSystem Tag.E6).wordProd ω • v = List.foldr (fun i x => reflect Tag.E6 i x) v ω := by
  induction ω generalizing v with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul]
    rfl

private theorem kGL_wordProd_inv_smul_E6 (ω : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    ((coxeterSystem Tag.E6).wordProd ω)⁻¹ • v = List.foldl (fun x i => reflect Tag.E6 i x) v ω := by
  induction ω generalizing v with
  | nil => rw [CoxeterSystem.wordProd_nil, inv_one, one_smul]; rfl
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_inv_rev, simple_inv, mul_smul, ih, simple_smul]
    rfl

private def kGLE6PerpTable : List ((Fin Tag.E6.rank → ℤ) × List (Fin Tag.E6.rank)) :=
  [(![-1,0,-1,-1,-1,-1], [5,4,3,2,0]),
   (![-1,0,-1,-1,-1,0], [4,5,4,3,2,0]),
   (![-1,0,-1,-1,0,0], [4,5,3,4,3,2,0]),
   (![-1,0,-1,0,0,0], [4,5,3,4,2,3,2,0]),
   (![-1,0,0,0,0,0], [4,5,3,4,2,3,0,2,0]),
   (![0,0,-1,-1,-1,-1], [5,4,3,2]),
   (![0,0,-1,-1,-1,0], [4,5,4,3,2]),
   (![0,0,-1,-1,0,0], [4,5,3,4,3,2]),
   (![0,0,-1,0,0,0], [4,5,3,4,2,3,2]),
   (![0,0,0,-1,-1,-1], [5,4,3]),
   (![0,0,0,-1,-1,0], [4,5,4,3]),
   (![0,0,0,-1,0,0], [4,5,3,4,3]),
   (![0,0,0,0,-1,-1], [5,4]),
   (![0,0,0,0,-1,0], [4,5,4]),
   (![0,0,0,0,0,-1], [5]),
   (![0,0,0,0,0,1], []),
   (![0,0,0,0,1,0], [4,5]),
   (![0,0,0,0,1,1], [4]),
   (![0,0,0,1,0,0], [4,5,3,4]),
   (![0,0,0,1,1,0], [4,5,3]),
   (![0,0,0,1,1,1], [4,3]),
   (![0,0,1,0,0,0], [4,5,3,4,2,3]),
   (![0,0,1,1,0,0], [4,5,3,4,2]),
   (![0,0,1,1,1,0], [4,5,3,2]),
   (![0,0,1,1,1,1], [4,3,2]),
   (![1,0,0,0,0,0], [4,5,3,4,2,3,0,2]),
   (![1,0,1,0,0,0], [4,5,3,4,2,3,0]),
   (![1,0,1,1,0,0], [4,5,3,4,2,0]),
   (![1,0,1,1,1,0], [4,5,3,2,0]),
   (![1,0,1,1,1,1], [4,3,2,0])]

private def kGLE6PerpWords : List (List (Fin Tag.E6.rank)) := kGLE6PerpTable.map (·.2)

private theorem kGLE6PerpCheck_true :
    ∀ δ ∈ rootFinset Tag.E6, iform δ (highRoot Tag.E6) = 0 →
      ∃ ω ∈ kGLE6PerpWords,
        List.foldr (fun i x => reflect Tag.E6 i x) (highRoot Tag.E6) ω = highRoot Tag.E6 ∧
        List.foldr (fun i x => reflect Tag.E6 i x) δ ω = Pi.single 5 1 := by
  decide +kernel

private theorem kGL_exists_perpWord {δ : Fin Tag.E6.rank → ℤ} (hδ : δ ∈ rootFinset Tag.E6)
    (h0 : iform δ (highRoot Tag.E6) = 0) :
    ∃ ω ∈ kGLE6PerpWords,
      List.foldr (fun i x => reflect Tag.E6 i x) (highRoot Tag.E6) ω = highRoot Tag.E6 ∧
      List.foldr (fun i x => reflect Tag.E6 i x) δ ω = Pi.single 5 1 :=
  kGLE6PerpCheck_true δ hδ h0

private def kGLE6D4Word : List (Fin Tag.E6.rank) := [1, 3, 2, 0]

private theorem kGLE6D4Check_true :
    ∀ γ ∈ rootFinset Tag.E6,
      (((List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word) 0 = 0 ∧
        (List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word) 5 = 0) ↔
        ((iform γ (highRoot Tag.E6) + iform γ (Pi.single 5 1) : ℤ) : ZMod 3) = 0) := by
  decide +kernel


private theorem kGL_image_wordProd_D4std :
    (fun γ => (coxeterSystem Tag.E6).wordProd kGLE6D4Word • γ) ''
        {γ | IsRoot Tag.E6 γ ∧ γ 0 = 0 ∧ γ 5 = 0} =
      {γ | IsRoot Tag.E6 γ ∧
        ((iform γ (highRoot Tag.E6) + iform γ (Pi.single 5 1) : ℤ) : ZMod 3) = 0} := by
  ext γ
  simp only [Set.mem_image, Set.mem_setOf_eq]
  by_cases hγ : γ ∈ rootFinset Tag.E6
  · have hiff : (((List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word) 0 = 0 ∧
        (List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word) 5 = 0) ↔
        ((iform γ (highRoot Tag.E6) + iform γ (Pi.single 5 1) : ℤ) : ZMod 3) = 0) :=
      kGLE6D4Check_true γ hγ
    constructor
    · rintro ⟨δ, hδ, hwδ⟩
      have hpre : ((coxeterSystem Tag.E6).wordProd kGLE6D4Word)⁻¹ • γ = δ := by
        rw [← hwδ, inv_smul_smul]
      have hfold : List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word = δ := by
        rw [← hpre, kGL_wordProd_inv_smul_E6]
      refine ⟨?_, ?_⟩
      · exact hwδ ▸ IsRoot.smul hδ.1 _
      · rw [← hiff, hfold]
        exact hδ.2
    · rintro ⟨hγroot, hZ⟩
      refine ⟨((coxeterSystem Tag.E6).wordProd kGLE6D4Word)⁻¹ • γ, ⟨?_, ?_⟩, ?_⟩
      · exact IsRoot.smul hγroot _
      · have hfold : List.foldl (fun x i => reflect Tag.E6 i x) γ kGLE6D4Word =
            ((coxeterSystem Tag.E6).wordProd kGLE6D4Word)⁻¹ • γ := by
          rw [kGL_wordProd_inv_smul_E6]
        rw [← hfold]
        exact hiff.mpr hZ
      · rw [smul_inv_smul]
  · have hnr : ¬ IsRoot Tag.E6 γ := fun h => hγ (mem_rootFinset.mpr h)
    constructor
    · rintro ⟨δ, hδ, hwδ⟩
      exact absurd (hwδ ▸ IsRoot.smul hδ.1 _) hnr
    · rintro ⟨hroot, -⟩
      exact absurd hroot hnr

theorem iform_E6_eq (γ β : Fin Tag.E6.rank → ℤ) :
    iform γ β = ∑ j, γ j * (Tag.E6.cartan.mulVec β) j := by
  have hs : ∀ i j : Fin Tag.E6.rank, Tag.E6.symmetrizedCartan i j = Tag.E6.cartan i j := by
    intro i j
    rw [symmetrizedCartan_apply]
    simp [Tag.symmetrizer]
  simp only [iform, hs, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem iform_zmod_three_eq_zero_iff {γ β : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (hβ : IsRoot Tag.E6 β) :
    ((iform γ β : ℤ) : ZMod 3) = 0 ↔ iform γ β = 0 := by
  have hγ2 : iform γ γ = 2 := EPilot.iform_self_eq_two (Or.inl rfl) hγ
  have hβ2 : iform β β = 2 := EPilot.iform_self_eq_two (Or.inl rfl) hβ
  have hx : 0 ≤ iform (γ - β) (γ - β) := by
    rcases eq_or_ne (γ - β) 0 with h | h
    · rw [h]; simp [iform]
    · exact le_of_lt (iform_self_pos h)
  have hy : 0 ≤ iform (γ + β) (γ + β) := by
    rcases eq_or_ne (γ + β) 0 with h | h
    · rw [h]; simp [iform]
    · exact le_of_lt (iform_self_pos h)
  have ex : iform (γ - β) (γ - β) = 4 - 2 * iform γ β := by
    simp only [iform_sub_right, iform_sub_left, iform_comm β γ, hγ2, hβ2]
    ring
  have ey : iform (γ + β) (γ + β) = 4 + 2 * iform γ β := by
    simp only [iform_add_right, iform_add_left, iform_comm β γ, hγ2, hβ2]
    ring
  have hnlo : -2 ≤ iform γ β := by rw [ex] at hx; omega
  have hnhi : iform γ β ≤ 2 := by rw [ey] at hy; omega
  constructor
  · intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨k, hk⟩ := h
    omega
  · intro h; rw [h]; simp

private theorem kGL_rootChar_zetaVec_eq {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) (γ : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec ζ hζ x) γ =
      CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (Multiplicative.ofAdd (∑ i, ((γ i : ℤ) : ZMod 3) * x i)) := by
  simp only [rootChar]
  calc ∏ i, (zetaVec ζ hζ x i) ^ (γ i)
      = ∏ i, CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
          (Multiplicative.ofAdd (((γ i : ℤ) : ZMod 3) * x i)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [show zetaVec ζ hζ x i = CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
          (Multiplicative.ofAdd (x i)) from rfl]
        rw [zmodPowHom_zpow]
    _ = CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
          (Multiplicative.ofAdd (∑ i, ((γ i : ℤ) : ZMod 3) * x i)) := by
        rw [← map_prod, ← ofAdd_sum]

private theorem kGL_zmodPowHom_ofAdd_eq_one_iff {K : Type} [Field K] {ζ : Kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (n : ZMod 3) :
    CFSG.RankThree.CentralCover.zmodPowHom ζ hζ (Multiplicative.ofAdd n) = 1 ↔ n = 0 := by
  constructor
  · intro h
    have h1 : Multiplicative.ofAdd n = (1 : Multiplicative (ZMod 3)) :=
      (CFSG.RankThree.CentralCover.zmodPowHom_injective hζo hζ) (by rw [map_one]; exact h)
    simpa using h1
  · intro h
    rw [h]
    simpa using map_one (CFSG.RankThree.CentralCover.zmodPowHom ζ hζ)

private theorem kGL_sum_mul_kgExpVec (γ β : Fin Tag.E6.rank → ℤ) :
    (∑ i, ((γ i : ℤ) : ZMod 3) * kgExpVec β i) = ((iform γ β : ℤ) : ZMod 3) := by
  rw [iform_E6_eq]
  have h : (∑ i, ((γ i : ℤ) : ZMod 3) * kgExpVec β i) =
      ((∑ i, γ i * (Tag.E6.cartan.mulVec β) i : ℤ) : ZMod 3) := by
    simp only [kgExpVec]
    have h2 : (∑ i, ((γ i : ℤ) : ZMod 3) *
          (((Tag.E6.cartan.mulVec β) i : ℤ) : ZMod 3)) =
        ((∑ i, γ i * (Tag.E6.cartan.mulVec β) i : ℤ) : ZMod 3) := by
      rw [Int.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    exact h2
  rw [h]

private theorem kGL_sum_mul_kgExpVec_add (γ α β : Fin Tag.E6.rank → ℤ) :
    (∑ i, ((γ i : ℤ) : ZMod 3) * (kgExpVec α + kgExpVec β) i) =
      ((iform γ α + iform γ β : ℤ) : ZMod 3) := by
  rw [show (∑ i, ((γ i : ℤ) : ZMod 3) * (kgExpVec α + kgExpVec β) i) =
      (∑ i, ((γ i : ℤ) : ZMod 3) * kgExpVec α i) +
      (∑ i, ((γ i : ℤ) : ZMod 3) * kgExpVec β i) from ?_]
  · rw [kGL_sum_mul_kgExpVec, kGL_sum_mul_kgExpVec]
    push_cast
    ring
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, mul_add]

theorem rootChar_zetaVec_kgExpVec_eq_one_iff {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (β γ : Fin Tag.E6.rank → ℤ) :
    rootChar (zetaVec ζ hζ (kgExpVec β)) γ = 1 ↔ ((iform γ β : ℤ) : ZMod 3) = 0 := by
  rw [kGL_rootChar_zetaVec_eq hζ, kGL_sum_mul_kgExpVec]
  exact kGL_zmodPowHom_ofAdd_eq_one_iff hζo hζ _

theorem famKernel_kgExpVec_single {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    famKernel {zetaVec ζ hζ (kgExpVec β)} = {γ | IsRoot Tag.E6 γ ∧ iform γ β = 0} := by
  ext γ
  simp only [famKernel, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hγ, h1⟩
    exact ⟨hγ, (iform_zmod_three_eq_zero_iff hγ hβ).mp
      ((rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ β γ).mp h1)⟩
  · rintro ⟨hγ, h1⟩
    exact ⟨hγ, (rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ β γ).mpr
      ((iform_zmod_three_eq_zero_iff hγ hβ).mpr h1)⟩

theorem famKernel_kgExpVec_add {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) (α β : Fin Tag.E6.rank → ℤ) :
    famKernel {zetaVec ζ hζ (kgExpVec α + kgExpVec β)} =
      {γ | IsRoot Tag.E6 γ ∧ ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0} := by
  ext γ
  simp only [famKernel, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨hγ, h1⟩
    refine ⟨hγ, ?_⟩
    rw [kGL_rootChar_zetaVec_eq hζ, kGL_sum_mul_kgExpVec_add,
      kGL_zmodPowHom_ofAdd_eq_one_iff hζo hζ] at h1
    exact h1
  · rintro ⟨hγ, h2⟩
    refine ⟨hγ, ?_⟩
    rw [kGL_rootChar_zetaVec_eq hζ, kGL_sum_mul_kgExpVec_add]
    exact (kGL_zmodPowHom_ofAdd_eq_one_iff hζo hζ _).mpr h2

theorem famKernel_kgExpVec_pair {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (hβ : IsRoot Tag.E6 β) :
    famKernel {zetaVec ζ hζ (kgExpVec α), zetaVec ζ hζ (kgExpVec β)} =
      {γ | IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0} := by
  ext γ
  simp only [famKernel, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨hγ, h1, h2⟩
    refine ⟨hγ, ?_, ?_⟩
    · exact (iform_zmod_three_eq_zero_iff hγ hα).mp
        ((rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ α γ).mp h1)
    · exact (iform_zmod_three_eq_zero_iff hγ hβ).mp
        ((rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ β γ).mp h2)
  · rintro ⟨hγ, h1, h2⟩
    refine ⟨hγ, ?_, ?_⟩
    · exact (rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ α γ).mpr
        ((iform_zmod_three_eq_zero_iff hγ hα).mpr h1)
    · exact (rootChar_zetaVec_kgExpVec_eq_one_iff hζo hζ β γ).mpr
        ((iform_zmod_three_eq_zero_iff hγ hβ).mpr h2)

private theorem kGL_image_smul_setOf_iform (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ)
    (P : ℤ → Prop) :
    (fun γ => w • γ) '' {γ | IsRoot Tag.E6 γ ∧ P (iform γ v)} =
      {γ | IsRoot Tag.E6 γ ∧ P (iform γ (w • v))} := by
  ext γ
  constructor
  · rintro ⟨δ, ⟨hδ, hP⟩, rfl⟩
    exact ⟨IsRoot.smul hδ w, by rwa [iform_smul]⟩
  · rintro ⟨hγ, hP⟩
    refine ⟨w⁻¹ • γ, ⟨IsRoot.smul hγ w⁻¹, ?_⟩, smul_inv_smul w γ⟩
    have e : iform (w⁻¹ • γ) v = iform γ (w • v) := by
      rw [← iform_smul w, smul_inv_smul]
    rwa [e]

private theorem kGL_image_smul_setOf_iform₂ (w : WeylGroup Tag.E6)
    (u v : Fin Tag.E6.rank → ℤ) (R : ℤ → ℤ → Prop) :
    (fun γ => w • γ) '' {γ | IsRoot Tag.E6 γ ∧ R (iform γ u) (iform γ v)} =
      {γ | IsRoot Tag.E6 γ ∧ R (iform γ (w • u)) (iform γ (w • v))} := by
  ext γ
  constructor
  · rintro ⟨δ, ⟨hδ, hR⟩, rfl⟩
    exact ⟨IsRoot.smul hδ w, by rwa [iform_smul, iform_smul]⟩
  · rintro ⟨hγ, hR⟩
    refine ⟨w⁻¹ • γ, ⟨IsRoot.smul hγ w⁻¹, ?_⟩, smul_inv_smul w γ⟩
    have e1 : iform (w⁻¹ • γ) u = iform γ (w • u) := by
      rw [← iform_smul w, smul_inv_smul]
    have e2 : iform (w⁻¹ • γ) v = iform γ (w • v) := by
      rw [← iform_smul w, smul_inv_smul]
    rwa [e1, e2]

private def kGLE6Gamma0 : Fin Tag.E6.rank → ℤ := ![-1, -1, -2, -2, -1, 0]

private theorem kGL_isRoot_gamma0 : IsRoot Tag.E6 kGLE6Gamma0 := by
  rw [← mem_rootFinset]
  decide +kernel

theorem stdPair_isRoot_orth :
    IsRoot Tag.E6 (highRoot Tag.E6) ∧ IsRoot Tag.E6 (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) ∧
      iform (highRoot Tag.E6) (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = 0 := by
  refine ⟨isRoot_highRoot Tag.E6, IsRoot.basis 5, ?_⟩
  rw [EPilot.iform_highRoot (Or.inl rfl)]
  decide

theorem exists_weyl_smul_orthPair {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) :
    ∃ w : WeylGroup Tag.E6, w • highRoot Tag.E6 = α ∧
      w • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = β := by
  obtain ⟨w₁, hw₁⟩ := EPilot.exists_smul_eq_highRoot (Or.inl rfl) hα
  have hβ₁root : IsRoot Tag.E6 (w₁ • β) := IsRoot.smul hβ w₁
  have hβ₁perp : iform (w₁ • β) (highRoot Tag.E6) = 0 := by
    rw [← hw₁, iform_smul, iform_comm β α, hαβ]
  obtain ⟨ω, -, hω1, hω2⟩ := kGL_exists_perpWord (mem_rootFinset.mpr hβ₁root) hβ₁perp
  have hA : ((coxeterSystem Tag.E6).wordProd ω * w₁) • α = highRoot Tag.E6 := by
    rw [mul_smul, hw₁, kGL_wordProd_smul_E6, hω1]
  have hB : ((coxeterSystem Tag.E6).wordProd ω * w₁) • β =
      (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    rw [mul_smul, kGL_wordProd_smul_E6, hω2]
  refine ⟨((coxeterSystem Tag.E6).wordProd ω * w₁)⁻¹, ?_, ?_⟩
  · rw [← hA, inv_smul_smul]
  · rw [← hB, inv_smul_smul]

theorem exists_weyl_smul_a5 {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    ∃ u : WeylGroup Tag.E6, (fun γ => u • γ) '' {γ | IsRoot Tag.E6 γ ∧ γ 1 = 0} =
      {γ | IsRoot Tag.E6 γ ∧ iform γ β = 0} := by
  obtain ⟨w, hw⟩ := EPilot.exists_smul_eq_highRoot (Or.inl rfl) hβ
  refine ⟨w⁻¹, ?_⟩
  have hset : {γ | IsRoot Tag.E6 γ ∧ γ 1 = 0} =
      {γ | IsRoot Tag.E6 γ ∧ iform γ (highRoot Tag.E6) = 0} := by
    ext γ
    constructor
    · rintro ⟨hγ, h1⟩
      refine ⟨hγ, ?_⟩
      have h := (EPilot.mem_perpRoots_iff_iform (τ := Tag.E6) (Or.inl rfl)).mp
        (show γ ∈ EPilot.perpRoots Tag.E6 from ⟨hγ, h1⟩)
      rw [iform_comm] at h
      exact h.2
    · rintro ⟨hγ, h1⟩
      refine ⟨hγ, ?_⟩
      have h : γ ∈ EPilot.perpRoots Tag.E6 :=
        (EPilot.mem_perpRoots_iff_iform (τ := Tag.E6) (Or.inl rfl)).mpr
          ⟨hγ, by rwa [iform_comm]⟩
      exact h.2
  rw [hset, kGL_image_smul_setOf_iform (w := w⁻¹) (v := highRoot Tag.E6)
    (P := fun n => n = 0), ← hw, inv_smul_smul]

theorem exists_weyl_smul_d4 {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) :
    ∃ u : WeylGroup Tag.E6, (fun γ => u • γ) '' {γ | IsRoot Tag.E6 γ ∧ γ 0 = 0 ∧ γ 5 = 0} =
      {γ | IsRoot Tag.E6 γ ∧ ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0} := by
  obtain ⟨w, hwθ, hwα⟩ := exists_weyl_smul_orthPair hα hβ hαβ
  refine ⟨w * (coxeterSystem Tag.E6).wordProd kGLE6D4Word, ?_⟩
  have himg : (fun γ => w • γ) ''
        {γ | IsRoot Tag.E6 γ ∧
          ((iform γ (highRoot Tag.E6) + iform γ (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) : ℤ)
            : ZMod 3) = 0} =
      {γ | IsRoot Tag.E6 γ ∧ ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0} := by
    have h := kGL_image_smul_setOf_iform₂ (w := w) (u := highRoot Tag.E6)
      (v := Pi.single 5 1) (R := fun a b => ((a + b : ℤ) : ZMod 3) = 0)
    simpa [hwθ, hwα] using h
  rw [← himg, ← kGL_image_wordProd_D4std]
  simp only [Set.image_image, Function.comp_apply, mul_smul]

theorem exists_root_kgL4 {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (hαβ : iform α β = 0) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧
      ((iform γ α + iform γ β : ℤ) : ZMod 3) = 0 ∧ ((iform γ α : ℤ) : ZMod 3) ≠ 0 := by
  obtain ⟨w, hwθ, hwα⟩ := exists_weyl_smul_orthPair hα hβ hαβ
  have e1 : iform (w • kGLE6Gamma0) α = iform kGLE6Gamma0 (highRoot Tag.E6) := by
    rw [← hwθ, iform_smul]
  have e2 : iform (w • kGLE6Gamma0) β =
      iform kGLE6Gamma0 (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) := by
    rw [← hwα, iform_smul]
  refine ⟨w • kGLE6Gamma0, IsRoot.smul kGL_isRoot_gamma0 w, ?_, ?_⟩
  · rw [e1, e2]
    decide +kernel
  · rw [e1]
    decide +kernel

end CFSG.StandardType.KGL

end
