module

public import CFSG.Sporadic.Schreier.LySylow
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms
public import CFSG.Sporadic.Schreier.LyPermCheck
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.LyGroupLemmas

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier.Native CFSG.LocalAnalysis.ComponentInitial

theorem sImg_eq : ∀ k : Fin 5, ∀ x : Fin 11,
    evalWord pPerm (sylowWords[k.val]!) x = arrFun (sImgArr[k.val]!) x := by
  decide +kernel

theorem sq_eq_one_of_commute_sImg (σ : Equiv.Perm (Fin 11))
    (hσ : ∀ k : Fin 5, ∀ x, σ (arrFun (sImgArr[k.val]!) x) = arrFun (sImgArr[k.val]!) (σ x)) :
    ∀ x, σ (σ x) = x := by
  have hfold : ∀ (w : List ℕ) (y : Fin 11), (∀ k ∈ w, k < 5) →
      σ (w.foldr (fun k y => arrFun (sImgArr[k]!) y) y) =
        w.foldr (fun k y => arrFun (sImgArr[k]!) y) (σ y) := by
    intro w y hw
    induction w with
    | nil => rfl
    | cons k w ih =>
      simp only [List.foldr_cons]
      rw [hσ ⟨k, hw k List.mem_cons_self⟩, ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk'))]
  have hw5 := sWord_lt
  have hcand : ∀ x, σ x = sCand (σ 0) (σ 8) (σ 10) x := by
    intro x
    have := hfold (sWord x) (sRep x) (hw5 x)
    rw [sWord_rep] at this
    rw [this, sCand_eq]
    congr 1
    unfold sRep
    split_ifs <;> rfl
  have hcomm : ∀ k : Fin 5, ∀ x, sCand (σ 0) (σ 8) (σ 10) (arrFun (sImgArr[k.val]!) x) =
      arrFun (sImgArr[k.val]!) (sCand (σ 0) (σ 8) (σ 10) x) := by
    intro k x
    rw [← hcand, ← hcand, hσ]
  have hinj : ∀ x y, sCand (σ 0) (σ 8) (σ 10) x = sCand (σ 0) (σ 8) (σ 10) y → x = y :=
    fun x y h => σ.injective (by rw [hcand x, hcand y]; exact h)
  intro x
  rw [hcand x, hcand]
  exact sCand_check _ _ _ hcomm hinj x

@[expose] def cStarC (j : ℕ) : lyC := ⟨cStar j, cStar_mem j⟩

theorem cStar_of_ge {j : ℕ} (hj : 12 ≤ j) : cStar j = 1 := by
  rw [cStar, List.getD_eq_getElem?_getD, List.getElem?_eq_none, Option.getD_none]
  rw [cStarList, extendByWords_length]
  simp only [List.length_cons, List.length_nil, Array.length_toList]
  have : cDerivations.size = 10 := rfl
  omega

theorem imgC_cStarC
    (j : ℕ) : imgC (cStarC j) = pPerm j := by
  by_cases hj : j < 12
  · exact imgC_cStar hj
  · have h1 : cStarC j = 1 := Subtype.ext (cStar_of_ge (by omega))
    rw [h1, map_one, pPerm, dite_eq_right hj]

theorem sylowGen_mem_lyC
    (k : Fin 6) : sylowGen k ∈ lyC := by
  unfold sylowGen
  split_ifs
  · exact evalWord_mem fun l _ => cStar_mem _
  · exact lyz_mem_lyC

theorem imgC_sylowGen
    {k : ℕ} (hk : k < 5) :
    imgC ⟨sylowGen ⟨k, by omega⟩, sylowGen_mem_lyC _⟩ = evalWord pPerm (sylowWords[k]!) := by
  have h1 : (⟨sylowGen ⟨k, by omega⟩, sylowGen_mem_lyC _⟩ : lyC) =
      evalWord cStarC (sylowWords[k]!) := by
    apply Subtype.ext
    rw [← Subgroup.coe_subtype, map_evalWord]
    simp only [sylowGen, ite_eq_left hk]
    rfl
  rw [h1, map_evalWord]
  simp only [imgC_cStarC]

theorem center_lyC :
    Subgroup.center lyC = zGroup := by
  obtain ⟨-, -, -, -, -, -, -, -, hc⟩ := centralizer_double_cover
  exact hc

theorem map_zGroup
    (β : MulAut lyC) : zGroup.map (β : lyC →* lyC) = zGroup := by
  rw [← center_lyC]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hy
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := β.surjective g
    simp only [MonoidHom.coe_ofClass]
    rw [← map_mul, ← map_mul, hy g]
  · intro hx
    refine ⟨β.symm x, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    apply β.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx (β g)]

@[expose] def quotAut
    (β : MulAut lyC) : MulAut (lyC ⧸ zGroup) :=
  QuotientGroup.congr zGroup zGroup β (map_zGroup β)

theorem quotAut_mk
    (β : MulAut lyC) (c : lyC) :
    quotAut β (c : lyC ⧸ zGroup) = ((β c : lyC) : lyC ⧸ zGroup) :=
  QuotientGroup.congr_mk _ _ _ _ c

theorem sylowGen_mem_subgroupOf
    (k : Fin 6) :
    (⟨sylowGen k, sylowGen_mem_lyC k⟩ : lyC) ∈ lyS.subgroupOf lyC := by
  rw [Subgroup.mem_subgroupOf]
  exact sylowGen_mem k

theorem sq_eq_one_of_fixes_S
    (β : MulAut lyC)
    (hβ : β ∈ pointwiseFixingAut (lyS.subgroupOf lyC)) : β ^ 2 = 1 := by
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 11)
    (Or.inr (by norm_num)) (lyCoverEquiv.symm.trans ((quotAut β).trans lyCoverEquiv))
  have key : ∀ u : lyC, β u = u → imgC u = σ * imgC u * σ⁻¹ := by
    intro u hu
    have h1 := hσ (lyCoverEquiv (u : lyC ⧸ zGroup))
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, quotAut_mk, hu] at h1
    exact h1
  have hfix : ∀ k : Fin 5, ∀ x,
      σ (arrFun (sImgArr[k.val]!) x) = arrFun (sImgArr[k.val]!) (σ x) := by
    intro k x
    have h1 := key _ ((mem_pointwiseFixingAut.1 hβ) _ (sylowGen_mem_subgroupOf ⟨k.val, by omega⟩))
    rw [imgC_sylowGen k.isLt] at h1
    have h2 := congrArg (fun π : Equiv.Perm (Fin 11) => π (σ x)) h1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h2
    rw [sImg_eq k, sImg_eq k x] at h2
    exact h2.symm
  have hσ2 := sq_eq_one_of_commute_sImg σ hfix
  have hσsq : σ * σ = 1 := Equiv.ext hσ2
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσsq
  have hγ : ∀ g, (lyCoverEquiv.symm.trans ((quotAut β).trans lyCoverEquiv))
      ((lyCoverEquiv.symm.trans ((quotAut β).trans lyCoverEquiv)) g) = g := by
    intro g
    apply Subtype.ext
    rw [hσ, hσ, hσinv]
    calc σ * (σ * (g : Equiv.Perm (Fin 11)) * σ) * σ = (σ * σ) * g * (σ * σ) := by group
      _ = g := by rw [hσsq, one_mul, mul_one]
  apply eq_one_of_trivial_on_quotient zGroup zGroup_le_center commutator_lyC
  intro c
  rw [← QuotientGroup.eq]
  have := hγ (lyCoverEquiv (c : lyC ⧸ zGroup))
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
  have h := lyCoverEquiv.injective this
  rw [quotAut_mk, quotAut_mk] at h
  rw [pow_two, MulAut.mul_apply]
  exact h.symm

theorem isPGroup_fixes_S :
    IsPGroup 2 (pointwiseFixingAut (lyS.subgroupOf lyC)) := by
  intro β
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow, sq_eq_one_of_fixes_S β β.2]
  rfl

end CFSG.Sporadic.LySchreier
