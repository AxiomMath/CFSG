module

public import CFSG.RankThree.GF2n.Smith81.S81E7Hwl
public import CFSG.RankThree.GF2n.Smith81.S81E7Lam
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

@[expose] def actWord (ω : List ℕ) (a : ℕ) : ℕ :=
  ω.foldl (fun a i => e7Data.weyl a (letter i)) a

@[expose] def weightWords : List (List ℕ) :=
  [[], [6], [6, 5], [6, 5, 4], [6, 5, 4, 3], [6, 5, 4, 3, 1], [6, 5, 4, 3, 2], [6, 5, 4, 3, 1, 2], [6, 5, 4, 3, 2, 0], [6, 5, 4, 3, 1, 2, 0], [6, 5, 4, 3, 1, 2, 3], [6, 5, 4, 3, 1, 2, 0, 3], [6, 5, 4, 3, 1, 2, 3, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2], [6, 5, 4, 3, 1, 2, 0, 3, 4], [6, 5, 4, 3, 1, 2, 3, 4, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4], [6, 5, 4, 3, 1, 2, 0, 3, 4, 5], [6, 5, 4, 3, 1, 2, 3, 4, 5, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5], [6, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 2], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5], [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6]]

theorem weightWords_correct : ∀ a : Fin e7Data.d, actWord (weightWords.getD a []) 0 = a := by
  unfold actWord weightWords letter
  decide +kernel

theorem orbit_actWord [CharP K 2] (ω : List ℕ) : ∀ a : Fin e7Data.d,
    (∃ g ∈ EGrp K, (g : Module.End K (V K)) (w0 : V K) = Finsupp.single a 1) →
    ∃ b : Fin e7Data.d, (b : ℕ) = actWord ω a ∧
      ∃ g ∈ EGrp K, (g : Module.End K (V K)) (w0 : V K) = Finsupp.single b 1 := by
  induction ω with
  | nil =>
    intro a ha
    exact ⟨a, rfl, ha⟩
  | cons i ω ih =>
    rintro a ⟨g, hg, hga⟩
    have hnm : (((e7Data_valid.nm K (letter i) : e7Data_valid.minGroup K) :
        (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
        Finsupp.single (e7Data_valid.sRefl (letter i) a) 1 := by
      change e7Data_valid.endo K (e7Data_valid.nm K (letter i)) (Finsupp.single a 1) = _
      rw [e7Data_valid.endo_nm, e7Data_valid.nOp_single (R := K)]
      by_cases h : e7Data.wt a (letter i) = 1
      · rw [if_pos h, ← Finsupp.single_neg, CharTwo.neg_eq]
      · rw [if_neg h]
    have hstep : ∃ g' ∈ EGrp K, (g' : Module.End K (V K)) (w0 : V K) =
        Finsupp.single (e7Data_valid.sRefl (letter i) a) 1 := by
      refine ⟨((e7Data_valid.nm K (letter i) : e7Data_valid.minGroup K) :
        (Module.End K (V K))ˣ) * g, mul_mem (e7Data_valid.nm K (letter i)).2 hg, ?_⟩
      rw [Units.val_mul, Module.End.mul_apply, hga, hnm]
    obtain ⟨b, hb, hgb⟩ := ih _ hstep
    have hfold : actWord (i :: ω) (a : ℕ) =
        actWord ω ((e7Data_valid.sRefl (letter i) a : Fin e7Data.d) : ℕ) := by
      rw [e7Data_valid.sRefl_val]
      try rfl
    exact ⟨b, hb.trans hfold.symm, hgb⟩

theorem weight_vec_mem_orbit [CharP K 2] (ν : Fin e7Data.d) :
    ∃ g ∈ EGrp K, (g : Module.End K (V K)) (w0 : V K) = Finsupp.single ν 1 := by
  have h0 : ∃ g ∈ EGrp K, (g : Module.End K (V K)) (w0 : V K) =
      Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) 1 :=
    ⟨1, one_mem _, by simp [w0]⟩
  obtain ⟨b, hb, hg⟩ := orbit_actWord (K := K) (weightWords.getD ν []) ⟨0, by decide⟩ h0
  have hbν : b = ν := Fin.ext (hb.trans (weightWords_correct ν))
  rw [hbν] at hg
  exact hg

@[expose] def IsHWLine (K : Type) [Field K] (ℓ : Submodule K (V K)) : Prop :=
  ∃ g ∈ EGrp K, ℓ = Submodule.span K {(g : Module.End K (V K)) (w0 : V K)}

theorem isHWLine_weight [CharP K 2] (ν : Fin e7Data.d) :
    IsHWLine K (Submodule.span K {(Finsupp.single ν 1 : V K)}) := by
  obtain ⟨g, hg, hgν⟩ := weight_vec_mem_orbit (K := K) ν
  exact ⟨g, hg, by rw [hgν]⟩

theorem IsHWLine.map [CharP K 2] {ℓ : Submodule K (V K)} (hℓ : IsHWLine K ℓ)
    {g : (Module.End K (V K))ˣ} (hg : g ∈ EGrp K) :
    IsHWLine K (ℓ.map (g : Module.End K (V K))) := by
  obtain ⟨g₁, hg₁, rfl⟩ := hℓ
  refine ⟨g * g₁, mul_mem hg hg₁, ?_⟩
  rw [Submodule.map_span, Set.image_singleton, Units.val_mul, Module.End.mul_apply]

theorem UL_le_Lam : UL K ≤ Lam K := by
  rw [UL, Subgroup.closure_le]
  rintro g ⟨β, hβ, hzero, -, c, rfl⟩
  exact xu_mem_Lam (show β ∈ Perp from ⟨hβ, hzero⟩) c

theorem hwLine_V0 [CharP K 2] {ℓ : Submodule K (V K)} (hℓ : IsHWLine K ℓ) (h : ℓ ≤ V0 K) :
    ∃ l ∈ Lam K, ∃ μ ∈ idx0,
      ℓ = Submodule.span K {(l : Module.End K (V K)) (Finsupp.single μ 1)} := by
  obtain ⟨g, hg, rfl⟩ := hℓ
  have hmem : (g : Module.End K (V K)) (w0 : V K) ∈ V0 K :=
    h (Submodule.mem_span_singleton_self _)
  obtain ⟨u', hu', μ, hμ, c, hc, heq⟩ := hwVec_V0 (K := K) (g := ⟨g, hg⟩) hmem
  have heq' : (g : Module.End K (V K)) (w0 : V K) =
      c • (u' : Module.End K (V K)) (Finsupp.single μ 1) := heq
  refine ⟨u', UL_le_Lam hu', μ, hμ, ?_⟩
  rw [heq', Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.2 hc)]

theorem Lam_transitive_hwLines [CharP K 2] {ℓ ℓ' : Submodule K (V K)} (hℓ : IsHWLine K ℓ)
    (h : ℓ ≤ V0 K) (hℓ' : IsHWLine K ℓ') (h' : ℓ' ≤ V0 K) :
    ∃ l ∈ Lam K, ℓ.map (l : Module.End K (V K)) = ℓ' := by
  obtain ⟨l₁, hl₁, μ₁, hμ₁, rfl⟩ := hwLine_V0 hℓ h
  obtain ⟨l₂, hl₂, μ₂, hμ₂, rfl⟩ := hwLine_V0 hℓ' h'
  obtain ⟨m, hm, hm_eq⟩ := Lam_transitive_wt (K := K) hμ₁ hμ₂
  refine ⟨l₂ * m * l₁⁻¹, mul_mem (mul_mem hl₂ hm) (inv_mem hl₁), ?_⟩
  have hinv : ((l₁⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
      ((l₁ : Module.End K (V K)) (Finsupp.single μ₁ 1)) = Finsupp.single μ₁ 1 := by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  have key : ((l₂ * m * l₁⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
      ((l₁ : Module.End K (V K)) (Finsupp.single μ₁ 1)) =
      (l₂ : Module.End K (V K)) (Finsupp.single μ₂ 1) := by
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hinv, hm_eq]
  rw [Submodule.map_span, Set.image_singleton, key]

theorem single_mem_V0 {a : Fin e7Data.d} (ha : a ∈ idx0) :
    (Finsupp.single a (1 : K) : V K) ∈ V0 K := by
  rw [mem_V0]
  intro b hb
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact hb ha

end CFSG.RankThree.GF2n.Smith81.E7Model
