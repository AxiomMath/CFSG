module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2PairAbs
import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtC
import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtS
import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtR
import CFSG.LocalAnalysis.WeakClosure81.W183B2PairExtE
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

private noncomputable def w183b2ext_barEquiv {G G' : Type} [Group G] [Group G']
    {X : Subgroup G} {X' : Subgroup G'} (e : ↥X ≃* ↥X') : Bar2 X ≃* Bar2 X' :=
  QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥X') e (CFSG.pCore_map_iso 2 e)

private theorem w183b2ext_pairQuotOK_iff {G G' : Type} [Group G] [Group G']
    {X : Subgroup G} {X' : Subgroup G'} (e : ↥X ≃* ↥X') (k₁ k₂ : ℕ) :
    PairQuotOK k₁ k₂ X ↔ PairQuotOK k₁ k₂ X' := by
  have hp : IsPGroup 2 X ↔ IsPGroup 2 X' :=
    ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩
  have hcard : Nat.card (Bar2 X) = Nat.card (Bar2 X') :=
    Nat.card_congr (w183b2ext_barEquiv e).toEquiv
  have hdih : (∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 X ≃* DihedralGroup r)) ↔
      (∃ r : ℕ, Odd r ∧ 1 < r ∧ Nonempty (Bar2 X' ≃* DihedralGroup r)) :=
    exists_congr fun r => and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun ⟨f⟩ => ⟨(w183b2ext_barEquiv e).symm.trans f⟩,
        fun ⟨f⟩ => ⟨(w183b2ext_barEquiv e).trans f⟩⟩
  unfold PairQuotOK
  rw [hp, hcard, hdih]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem w183b2_pair_ext_abs_data
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hKsol : IsSolvable ↥(H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)))
    {g h : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) (hh : h ∈ H)
    (hnot1 : ¬ M.img (vInH V H (g * h)) ≤ Subgroup.normalizer (M.img (vInH V H g) : Set _))
    (hnot2 : ¬ M.img (vInH V H g) ≤ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _))
    (hk1 : mOfG (M.img (vInH V H g))
      (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)) ≤ 2)
    (hk2 : mOfG (M.img (vInH V H (g * h)))
      (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)) ≤ 2)
    (hO : InCalOStar (i + 2) (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) h) :
    ∃ (Lb : Type) (_ : Group Lb) (_ : Finite Lb)
      (π : ↥(vInH V H g ⊔ vInH V H (g * h)) →* Lb)
      (ψ : ↥(vInH V H g ⊔ vInH V H (g * h)) →* ↥(M.img H))
      (Ah' Bh' : Subgroup ↥(vInH V H g ⊔ vInH V H (g * h))) (k₁ k₂ d : ℕ)
      (P₁ P₂ : Subgroup Lb),
      IsPGroup 2 π.ker ∧ IsSolvable ψ.ker ∧ Ah' ⊔ Bh' = ⊤ ∧
      (1 ≤ k₁ ∧ k₁ ≤ 2) ∧ (1 ≤ k₂ ∧ k₂ ≤ 2) ∧
      (k₁ ≤ d ∧ d ≤ k₁ + 1) ∧ (k₂ ≤ d ∧ d ≤ k₂ + 1) ∧
      (IsL2 Lb d ∨ IsSz Lb d ∨ ∃ m : ℕ, Odd m ∧ Nonempty (Lb ≃* DihedralGroup m)) ∧
      IsElemAbelian 2 P₁ ∧ IsElemAbelian 2 P₂ ∧
      Nat.card P₁ = 2 ^ d ∧ Nat.card P₂ = 2 ^ d ∧ P₁ ≠ P₂ ∧
      Ah'.map π ≤ P₁ ∧ Bh'.map π ≤ P₂ ∧
      Nat.card (Ah'.map π) = 2 ^ k₁ ∧ Nat.card (Bh'.map π) = 2 ^ k₂ ∧
      k₁ = mOfG (M.img (vInH V H g))
        (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)) ∧
      k₂ = mOfG (M.img (vInH V H (g * h)))
        (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)) ∧
      Nonempty (↥(ψ.range) ≃* ↥(M.img (vInH V H g) ⊔ M.img (vInH V H (g * h)))) := by
  have hg' : Gam183 V H (eOmegaZ H D.T) i (g * h) :=
    Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) hh hg
  obtain ⟨hOcal, K, hKnorm, hKset, hQuot, hconj, -, -, -⟩ := hO
  haveI := hKnorm
  have hPe : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g
  have hQe : IsElemAbelian 2 (conjSubgroup (conjSubgroup V g) h) :=
    E3.isElemAbelian_conjSubgroup hPe h
  have hVM : V ≤ D.M := by
    rw [← x.hyp.setting.normalizer_eq]
    exact Subgroup.le_normalizer
  have hPM : conjSubgroup V g ≤ conjSubgroup D.M g := Subgroup.map_mono hVM
  have hQM : conjSubgroup (conjSubgroup V g) h ≤ conjSubgroup (conjSubgroup D.M g) h :=
    Subgroup.map_mono hPM
  have hA : vInH V H g ≤ conjSubgroup V g := inf_le_left
  have hB : vInH V H (g * h) ≤ conjSubgroup (conjSubgroup V g) h := by
    rw [conjSubgroup_conjSubgroup]
    exact inf_le_left
  have hAH : vInH V H g ≤ H := inf_le_right
  have hBH : vInH V H (g * h) ≤ H := inf_le_right
  obtain ⟨π, P₁, P₂, hπker, hP₁e, hP₂e, hcP₁, hcP₂, hmQ, hP12, hAP, hBP, hcA, hcB⟩ :=
    w183b2_pq_data hPe hQe hPM hQM hOcal.1.1 hKset hconj hA hB
  obtain ⟨ψ, hψsolv, hψrange⟩ := w183b2_pair_psi M hAH hBH hKsol
  have hshape := w183b2_shape_of_quotShape hQuot
  have hMM : conjSubgroup (conjSubgroup D.M g) h = conjSubgroup D.M (g * h) :=
    conjSubgroup_conjSubgroup D.M g h
  have hVV : conjSubgroup (conjSubgroup V g) h = conjSubgroup V (g * h) :=
    conjSubgroup_conjSubgroup V g h
  have hi : i ≤ 1 := x.hyp.i_le
  have hk₁eq := x.pair_k_eq (g₁ := g) (g₂ := g * h) M hg'
  have hk₂eq := x.pair_k_eq (g₁ := g * h) (g₂ := g) M hg
  obtain ⟨hb1lo, hb1hi⟩ := x.pair_mQuot_bounds (g₁ := g) (g₂ := g * h) hg
  obtain ⟨hb2lo, hb2hi⟩ := x.pair_mQuot_bounds (g₁ := g * h) (g₂ := g) hg'
  have hone1 := x.pair_one_le_mQuot (g₁ := g) (g₂ := g * h) M hnot2
  have hone2 := x.pair_one_le_mQuot (g₁ := g * h) (g₂ := g) M hnot1
  rw [hMM] at hcP₁ hcP₂ hcA hshape
  rw [hVV, hMM] at hmQ
  refine ⟨↥(conjSubgroup V g ⊔ conjSubgroup (conjSubgroup V g) h) ⧸
      K.subgroupOf (conjSubgroup V g ⊔ conjSubgroup (conjSubgroup V g) h),
    inferInstance, inferInstance, π, ψ,
    (vInH V H g).subgroupOf (vInH V H g ⊔ vInH V H (g * h)),
    (vInH V H (g * h)).subgroupOf (vInH V H g ⊔ vInH V H (g * h)),
    mOfG (M.img (vInH V H g))
      (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)),
    mOfG (M.img (vInH V H (g * h)))
      (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)),
    E3.mQuot (conjSubgroup V g) (conjSubgroup D.M (g * h)), P₁, P₂, hπker, hψsolv,
    w183b2_subgroupOf_sup_eq_top _ _, ⟨by rw [hk₁eq]; exact hone1, hk1⟩,
    ⟨by rw [hk₂eq]; exact hone2, hk2⟩,
    ⟨by rw [hk₁eq]; exact hb1lo, by rw [hk₁eq]; omega⟩,
    ⟨by rw [hk₂eq, ← hmQ]; exact hb2lo, by rw [hk₂eq, ← hmQ]; omega⟩,
    hshape, hP₁e, hP₂e, hcP₁, hcP₂, hP12, hAP, hBP,
    by rw [hk₁eq]; exact hcA, by rw [hk₂eq]; exact hcB, rfl, rfl, hψrange⟩

theorem pair_ext
    (hL28 : FinPairGenL28) (hSz8 : FinPairGenSz8)
    (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hK : IsSolvable ↥(H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)))
    (h13 : ¬ 13 ∣ Nat.card (M.img H))
    {g h : G} (hg : Gam183 V H (eOmegaZ H D.T) i g) (hh : h ∈ H)
    (hnot1 : ¬ M.img (vInH V H (g * h)) ≤ Subgroup.normalizer (M.img (vInH V H g) : Set _))
    (hnot2 : ¬ M.img (vInH V H g) ≤ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _))
    (hk1 : mOfG (M.img (vInH V H g))
      (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)) ≤ 2)
    (hk2 : mOfG (M.img (vInH V H (g * h)))
      (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)) ≤ 2)
    (hO : InCalOStar (i + 2) (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) h) :
    PairQuotOK
      (mOfG (M.img (vInH V H g))
        (M.img (vInH V H g) ⊓ Subgroup.normalizer (M.img (vInH V H (g * h)) : Set _)))
      (mOfG (M.img (vInH V H (g * h)))
        (M.img (vInH V H (g * h)) ⊓ Subgroup.normalizer (M.img (vInH V H g) : Set _)))
      (M.img (vInH V H g) ⊔ M.img (vInH V H (g * h))) := by
  obtain ⟨Lb, hGLb, hFLb, π, ψ, Ah', Bh', k₁, k₂, d, P₁, P₂,
    hπker, hψker, hgen, hk₁, hk₂, hd₁, hd₂, hshape, hP₁, hP₂, hc₁, hc₂, hP, hAP, hBP,
    hAc, hBc, hk₁eq, hk₂eq, e⟩ :=
    w183b2_pair_ext_abs_data (D := D) (V₀ := V₀) (V := V) (H := H) (i := i)
      x M hK hg hh hnot1 hnot2 hk1 hk2 hO
  letI := hGLb
  letI := hFLb
  obtain ⟨e⟩ := e
  have hPQ := w183b2_pair_abs hL28 hSz8 π hπker ψ hψker h13 Ah' Bh' hgen k₁ k₂ d
    hk₁ hk₂ hd₁ hd₂ hshape P₁ P₂ hP₁ hP₂ hc₁ hc₂ hP hAP hBP hAc hBc
  have h1 : PairQuotOK k₁ k₂ (M.img (vInH V H g) ⊔ M.img (vInH V H (g * h))) :=
    (w183b2ext_pairQuotOK_iff e k₁ k₂).mp hPQ
  rw [hk₁eq, hk₂eq] at h1
  exact h1

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
