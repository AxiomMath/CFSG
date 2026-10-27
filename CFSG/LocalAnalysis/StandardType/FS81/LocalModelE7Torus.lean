module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RootLineStab
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

open CFSG.Open CFSG.Assembly
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.StandardType.FrameRoute.FS81

private theorem ggTorPsi_three_three (c : ZMod 3) :
    ggTorPsi 3 3 (by norm_num) (Multiplicative.ofAdd c) = Multiplicative.ofAdd c := by
  rw [ggTorPsi_apply]
  have hz : ggZetaP 3 3 = Multiplicative.ofAdd (1 : ZMod 3) := by
    unfold ggZetaP
    norm_num
  rw [hz, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, toAdd_ofAdd]

namespace GGTorusTorWit

variable {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}

noncomputable def coordHom (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) :
    Multiplicative (Fin 7 → ZMod 3) →* L' :=
  (ggTorE (p := 3) (m := 3) (by norm_num) w.cor hcomm).comp
    (MulEquiv.piMultiplicative (fun _ : Fin 7 => ZMod 3)).toMonoidHom

theorem coordHom_ofAdd (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) (u : Fin 7 → ZMod 3) :
    w.coordHom hcomm (Multiplicative.ofAdd u) =
      (List.ofFn fun k => w.cor k (Multiplicative.ofAdd (u k))).prod := by
  change (ggTorE (p := 3) (m := 3) (by norm_num) w.cor hcomm)
      (fun k => Multiplicative.ofAdd (u k)) = _
  rw [ggTorE_apply]
  simp only [ggTorPsi_three_three]

theorem coordHom_single (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) (j : Fin 7) (c : ZMod 3) :
    w.coordHom hcomm (Multiplicative.ofAdd (Pi.single j c)) =
      w.cor j (Multiplicative.ofAdd c) := by
  change (ggTorE (p := 3) (m := 3) (by norm_num) w.cor hcomm)
      (fun k => Multiplicative.ofAdd ((Pi.single j c : Fin 7 → ZMod 3) k)) = _
  have h : (fun k => Multiplicative.ofAdd ((Pi.single j c : Fin 7 → ZMod 3) k)) =
      Pi.mulSingle j (Multiplicative.ofAdd c) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · rw [Pi.single_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk]; rfl
  rw [h, ggTorE_mulSingle, ggTorPsi_three_three]

theorem coordHom_range (w : GGTorusTorWit 3 7 L' A)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) :
    (w.coordHom hcomm).range = ⨆ k, (w.cor k).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    rw [← ofAdd_toAdd u, coordHom_ofAdd]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  · refine iSup_le fun j => ?_
    rintro _ ⟨ζ, rfl⟩
    refine ⟨Multiplicative.ofAdd (Pi.single j (Multiplicative.toAdd ζ)), ?_⟩
    rw [coordHom_single, ofAdd_toAdd]

private theorem conj_cor (w : GGTorusTorWit 3 7 L' A)
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇)
    (hZ : Subgroup.center L' = ⊥) (k j : Fin 7) (ζ : Multiplicative (ZMod 3)) :
    w.n k * w.cor j ζ * (w.n k)⁻¹ =
      w.cor j ζ * (w.cor k (ζ ^ (CartanMatrix.E 7 k j : ℤ)))⁻¹ := by
  obtain ⟨-, -, hcorT, -, -, -, -, hpair, hnT, -⟩ := hw
  have hτ : MulAut.conj (w.cor j ζ) ∈ w.T := hcorT j ζ
  have h := hnT k _ hτ
  have hL : MulAut.conj (w.n k) * MulAut.conj (w.cor j ζ) * (MulAut.conj (w.n k))⁻¹ =
      MulAut.conj (w.n k * w.cor j ζ * (w.n k)⁻¹) := by
    rw [← map_mul, ← map_inv, ← map_mul]
  have hR : MulAut.conj (w.cor j ζ) *
      (MulAut.conj (w.cor k (w.α k (MulAut.conj (w.cor j ζ)))))⁻¹ =
      MulAut.conj (w.cor j ζ *
        (w.cor k (w.α k (MulAut.conj (w.cor j ζ))))⁻¹) := by
    rw [← map_inv, ← map_mul]
  rw [hL, hR] at h
  have h2 := mulAut_conj_injective hZ h
  rwa [hpair k j ζ] at h2

noncomputable def matVecHom (M : Matrix (Fin 7) (Fin 7) (ZMod 3)) :
    Multiplicative (Fin 7 → ZMod 3) →* Multiplicative (Fin 7 → ZMod 3) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun v => M *ᵥ v
      map_zero' := by simp
      map_add' := fun v w => Matrix.mulVec_add M v w }

theorem matVecHom_ofAdd (M : Matrix (Fin 7) (Fin 7) (ZMod 3)) (u : Fin 7 → ZMod 3) :
    matVecHom M (Multiplicative.ofAdd u) = Multiplicative.ofAdd (M *ᵥ u) := by
  rw [matVecHom, AddMonoidHom.coe_toMultiplicative]
  rfl

theorem coordHom_conj (w : GGTorusTorWit 3 7 L' A)
    (hw : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇) (hZ : Subgroup.center L' = ⊥)
    (hcomm : ∀ j k ζ ξ, Commute (w.cor j ζ) (w.cor k ξ)) (k : Fin 7) (u : Fin 7 → ZMod 3) :
    w.n k * w.coordHom hcomm (Multiplicative.ofAdd u) * (w.n k)⁻¹ =
      w.coordHom hcomm (Multiplicative.ofAdd (e7CorootRefl k *ᵥ u)) := by
  have hFG : (MulAut.conj (w.n k)).toMonoidHom.comp (w.coordHom hcomm) =
      (w.coordHom hcomm).comp (matVecHom (e7CorootRefl k)) := by
    refine MonoidHom.eq_of_eqOn_dense (s := Set.range fun j : Fin 7 =>
      Multiplicative.ofAdd (Pi.single j 1)) ?_ ?_
    · rw [eq_top_iff]
      intro x _
      rw [← ofAdd_toAdd x]
      have hx : Multiplicative.ofAdd (Multiplicative.toAdd x) =
          ∏ j : Fin 7,
            (Multiplicative.ofAdd (Pi.single j 1) : Multiplicative (Fin 7 → ZMod 3)) ^
              (Multiplicative.toAdd x j).val := by
        simp only [← ofAdd_nsmul]
        rw [← ofAdd_sum]
        congr 1
        funext i
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
        · intro j _ hji
          rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hji), smul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hx]
      exact Subgroup.prod_mem _ fun j _ =>
        Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _
    · rintro _ ⟨j, rfl⟩
      show MulAut.conj (w.n k)
          (w.coordHom hcomm (Multiplicative.ofAdd (Pi.single j 1))) =
        w.coordHom hcomm (Multiplicative.ofAdd (e7CorootRefl k *ᵥ Pi.single j 1))
      have hvec : e7CorootRefl k *ᵥ (Pi.single j 1 : Fin 7 → ZMod 3) =
          Pi.single j 1 + Pi.single k (-(CartanMatrix.E 7 k j : ZMod 3)) := by
        funext i
        simp only [e7CorootRefl, Matrix.sub_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_single_one, Matrix.col_apply, Matrix.of_apply, Pi.add_apply,
          Pi.sub_apply, Matrix.one_apply]
        by_cases hik : i = k
        · rw [hik]
          by_cases hkj : k = j
          · rw [hkj]; norm_num
          · simp [hkj]
        · by_cases hij : i = j
          · rw [hij]
            by_cases hjk : j = k
            · rw [hjk]; norm_num
            · simp [hjk]
          · simp [hik, hij]
      rw [hvec, ofAdd_add, map_mul, coordHom_single, coordHom_single, MulAut.conj_apply,
        conj_cor w hw hZ k j (Multiplicative.ofAdd 1)]
      rw [show (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ^
            (CartanMatrix.E 7 k j : ℤ) =
          Multiplicative.ofAdd ((CartanMatrix.E 7 k j : ℤ) • (1 : ZMod 3)) from
        (ofAdd_zsmul (CartanMatrix.E 7 k j) (1 : ZMod 3)).symm,
        zsmul_eq_mul, mul_one, ← map_inv, ← ofAdd_neg]
  have h := congrArg (fun f : Multiplicative (Fin 7 → ZMod 3) →* L' =>
    f (Multiplicative.ofAdd u)) hFG
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    matVecHom_ofAdd] using h

end GGTorusTorWit

end CFSG.StandardType

end
