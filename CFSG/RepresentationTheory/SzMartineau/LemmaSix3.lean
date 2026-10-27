module

public import CFSG.RepresentationTheory.SzMartineau.LemmaSix2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.Assembly.GL83SuzukiModel

public section

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

variable {a : ℕ}

private lemma pow_theta_theta (x : F a) :
    (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := by
  let _ : Fintype (F a) := Fintype.ofFinite _
  have hq : x ^ (2 ^ (2 * a + 1)) = x := by
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * a + 1) (by omega)] at h
  rw [← pow_mul, show 2 ^ (a + 1) * 2 ^ (a + 1) = 2 ^ (2 * a + 1) * 2 by ring,
    pow_mul, hq]

private lemma frob_data : (2 : F a) = 0 ∧
    (∀ x y : F a, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1)) ∧
      ∀ x : F a, (x ^ 2 ^ (a + 1)) ^ 2 ^ (a + 1) = x ^ 2 := by
  refine ⟨?_, ?_, pow_theta_theta⟩
  · exact_mod_cast CharP.cast_eq_zero (F a) 2
  · intro x y
    exact add_pow_char_pow (p := 2) (n := a + 1) x y

private lemma suzukiN_shift (u v : F a) :
    CFSG.Blueprint.suzukiN a u (v + u ^ (1 + 2 ^ (a + 1))) =
      CFSG.Blueprint.suzukiN a u v := by
  obtain ⟨h2, hadd, hθθ⟩ := frob_data (a := a)
  have h1 : (u ^ (1 + 2 ^ (a + 1))) ^ 2 ^ (a + 1) = u ^ (2 + 2 ^ (a + 1)) := by
    rw [← pow_mul, show (1 + 2 ^ (a + 1)) * 2 ^ (a + 1) =
      2 ^ (a + 1) + 2 ^ (a + 1) * 2 ^ (a + 1) by ring, pow_add, pow_mul, hθθ, pow_add]
    ring
  have h3 : u * u ^ (1 + 2 ^ (a + 1)) = u ^ (2 + 2 ^ (a + 1)) := by
    rw [mul_comm, ← pow_succ]
    congr 1
    ring
  unfold CFSG.Blueprint.suzukiN
  rw [hadd, h1, mul_add, h3]
  rw [add_comm (2 : ℕ) (2 ^ (a + 1))]
  linear_combination (u ^ (2 + 2 ^ (a + 1))) * h2

private lemma torusMat_eq_suzukiD (x : (F a)ˣ) :
    torusMat a x = CFSG.Blueprint.suzukiD a x := by
  rw [← CFSG.Assembly.largeEvenSzD_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torusMat, Matrix.diagonal, inv_pow]

private lemma wMat_mul_rootMat_mul_wMat (u v : F a) :
    wMat a * rootMat a u v * wMat a =
      CFSG.Blueprint.suzukiS a u (v + u ^ (1 + 2 ^ (a + 1))) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, rootMat, CFSG.Blueprint.suzukiS,
      Matrix.mul_apply, Fin.sum_univ_four]
  · rw [add_comm]
  · rw [suzukiN_shift]
    unfold CFSG.Blueprint.suzukiN
    rw [add_comm (2 ^ (a + 1)) 2]
  · rw [show 2 ^ (a + 1) + 1 = 1 + 2 ^ (a + 1) by ring]
    rw [add_comm (u ^ (1 + 2 ^ (a + 1))) (v + u ^ (1 + 2 ^ (a + 1))), add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

private lemma wMat_mul_suzukiS_mul_wMat (u v : F a) :
    wMat a * CFSG.Blueprint.suzukiS a u v * wMat a =
      rootMat a u (v + u ^ (1 + 2 ^ (a + 1))) := by
  have hshift : (v + u ^ (1 + 2 ^ (a + 1))) + u ^ (1 + 2 ^ (a + 1)) = v := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h := wMat_mul_rootMat_mul_wMat (a := a) u (v + u ^ (1 + 2 ^ (a + 1)))
  rw [hshift] at h
  calc wMat a * CFSG.Blueprint.suzukiS a u v * wMat a
      = wMat a * (wMat a * rootMat a u (v + u ^ (1 + 2 ^ (a + 1))) * wMat a) *
          wMat a := by
        rw [← h]
    _ = rootMat a u (v + u ^ (1 + 2 ^ (a + 1))) := by
        simp only [mul_assoc]
        rw [wMat_mul_self, mul_one, ← mul_assoc, wMat_mul_self, one_mul]

private lemma det_suzukiS_eq_one (u v : F a) :
    (CFSG.Blueprint.suzukiS a u v).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_of_isUpperTriangular]
  · simp [CFSG.Blueprint.suzukiS, Fin.prod_univ_four]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [CFSG.Blueprint.suzukiS]

private lemma wMat_eq_suzukiW : wMat a = CFSG.Blueprint.suzukiW (F a) :=
  CFSG.Assembly.largeEvenSzW_eq

theorem suzukiGroup_eq_Sz :
    CFSG.Blueprint.suzukiGroup a (F a) = Sz a := by
  apply le_antisymm
  · rw [CFSG.Blueprint.suzukiGroup, Subgroup.closure_le]
    rintro A (⟨u, v, hA⟩ | ⟨x, hA⟩ | hA)
    · have hshift : (v + u ^ (1 + 2 ^ (a + 1))) + u ^ (1 + 2 ^ (a + 1)) = v := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have hA' : A = wGL a * rootGL a u (v + u ^ (1 + 2 ^ (a + 1))) * wGL a := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) =
          (wGL a : Matrix (Fin 4) (Fin 4) (F a)) *
            (rootGL a u (v + u ^ (1 + 2 ^ (a + 1))) :
              Matrix (Fin 4) (Fin 4) (F a)) *
            (wGL a : Matrix (Fin 4) (Fin 4) (F a))
        rw [hA, coe_wGL, coe_rootGL, wMat_mul_rootMat_mul_wMat, hshift]
      rw [hA']
      exact mul_mem (mul_mem (wGL_mem a) (rootGL_mem a _ _)) (wGL_mem a)
    · have hA' : A = torusGL a x := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) = torusMat a x
        rw [hA]
        exact (torusMat_eq_suzukiD x).symm
      rw [hA']
      exact Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))
    · have hA' : A = wGL a := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) = wMat a
        rw [hA]
        exact wMat_eq_suzukiW.symm
      rw [hA']
      exact wGL_mem a
  · rw [Sz, Subgroup.closure_le]
    rintro A (⟨u, v, hA⟩ | ⟨x, hA⟩ | hA)
    · let L : GL (Fin 4) (F a) :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (CFSG.Blueprint.suzukiS a u (v + u ^ (1 + 2 ^ (a + 1))))
          (by rw [det_suzukiS_eq_one]; exact one_ne_zero)
      have hL : L ∈ CFSG.Blueprint.suzukiGroup a (F a) :=
        Subgroup.subset_closure (Or.inl ⟨u, v + u ^ (1 + 2 ^ (a + 1)), rfl⟩)
      have hJ : wGL a ∈ CFSG.Blueprint.suzukiGroup a (F a) :=
        Subgroup.subset_closure (Or.inr (Or.inr (by rw [coe_wGL, wMat_eq_suzukiW])))
      have hshift : (v + u ^ (1 + 2 ^ (a + 1))) + u ^ (1 + 2 ^ (a + 1)) = v := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have hA' : A = wGL a * L * wGL a := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) =
          (wGL a : Matrix (Fin 4) (Fin 4) (F a)) *
            (L : Matrix (Fin 4) (Fin 4) (F a)) *
            (wGL a : Matrix (Fin 4) (Fin 4) (F a))
        rw [hA, coe_wGL]
        change rootMat a u v = wMat a * (L : Matrix (Fin 4) (Fin 4) (F a)) * wMat a
        rw [show (L : Matrix (Fin 4) (Fin 4) (F a)) =
          CFSG.Blueprint.suzukiS a u (v + u ^ (1 + 2 ^ (a + 1))) from rfl]
        rw [wMat_mul_suzukiS_mul_wMat, hshift]
      rw [hA']
      exact mul_mem (mul_mem hJ hL) hJ
    · have hA' : A = torusGL a x := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) = torusMat a x
        rw [hA]
        rfl
      rw [hA']
      exact Subgroup.subset_closure
        (Or.inr (Or.inl ⟨x, by rw [coe_torusGL, torusMat_eq_suzukiD]⟩))
    · have hA' : A = wGL a := by
        refine Units.ext ?_
        change (A : Matrix (Fin 4) (Fin 4) (F a)) = wMat a
        rw [hA]
        rfl
      rw [hA']
      exact Subgroup.subset_closure (Or.inr (Or.inr (by rw [coe_wGL, wMat_eq_suzukiW])))

private lemma map_suzukiGroup {K : Type} [Field K] (ψ : K ≃+* F a) :
    (CFSG.Blueprint.suzukiGroup a K).map
        (CFSG.ShultStronglyClosedTI.glFieldEquiv ψ).toMonoidHom =
      CFSG.Blueprint.suzukiGroup a (F a) := by
  rw [show CFSG.Blueprint.suzukiGroup a K = CFSG.Open.GLASzGroup a K from
      (CFSG.Assembly.largeEvenSzGroup_eq_suzukiGroup a K).symm,
    show CFSG.Blueprint.suzukiGroup a (F a) = CFSG.Open.GLASzGroup a (F a) from
      (CFSG.Assembly.largeEvenSzGroup_eq_suzukiGroup a (F a)).symm,
    CFSG.ShultStronglyClosedTI.map_glaSzGroup]

private lemma map_symm_mulVec_coord {K : Type} [Field K] (ψ : K ≃+* F a)
    (A : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → F a) :
    (fun i => ψ.symm (((A.map ψ) *ᵥ v) i)) = A *ᵥ (fun i => ψ.symm (v i)) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem biadd_eq_zero_of_suzukiGroup_equivariant {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (c₁ c₂ c₃ : ℕ)
    (β : (Fin 4 → K) →+ (Fin 4 → K) →+ (Fin 4 → K))
    (hβ : ∀ (g : ↥(CFSG.Blueprint.suzukiGroup a K)) (v w : Fin 4 → K),
      β ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₁)) *ᵥ v)
        ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₂)) *ᵥ w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c₃)) *ᵥ β v w) :
    β = 0 := by
  let ψ : K ≃+* F a :=
    CFSG.ShultStronglyClosedTI.binaryFieldEquiv (2 * a + 1) (by omega) hK
  let e : (Fin 4 → K) ≃+ (Fin 4 → F a) :=
    AddEquiv.piCongrRight fun _ => ψ.toAddEquiv
  let β' : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a) :=
    { toFun := fun v =>
        { toFun := fun w => e (β (e.symm v) (e.symm w))
          map_zero' := by simp
          map_add' := by intro w₁ w₂; simp [map_add] }
      map_zero' := by ext w; simp
      map_add' := by intro v₁ v₂; ext w; simp [map_add] }
  have hβ' : ∀ (g' : ↥(Sz a)) (v w : Fin 4 → F a),
      β' ((((g' : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map
            (· ^ 2 ^ c₁)) *ᵥ v)
        ((((g' : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map
            (· ^ 2 ^ c₂)) *ᵥ w) =
      (((g' : GL (Fin 4) (F a)) : Matrix (Fin 4) (Fin 4) (F a)).map
          (· ^ 2 ^ c₃)) *ᵥ β' v w := by
    intro g' v w
    let A : GL (Fin 4) (F a) := ↑g'
    have hA : A ∈ Sz a := g'.2
    have hA' : A ∈ CFSG.Blueprint.suzukiGroup a (F a) := by
      rw [suzukiGroup_eq_Sz]
      exact hA
    have hg' : A ∈ (CFSG.Blueprint.suzukiGroup a K).map
          (CFSG.ShultStronglyClosedTI.glFieldEquiv ψ).toMonoidHom := by
      rw [map_suzukiGroup]
      exact hA'
    obtain ⟨g, hg, hgeq⟩ := Subgroup.mem_map.mp hg'
    have hmat : (A : Matrix (Fin 4) (Fin 4) (F a)) =
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map ψ := by
      rw [← hgeq]
      exact CFSG.ShultStronglyClosedTI.coe_glFieldEquiv ψ g
    have htwist (c : ℕ) :
        ((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c)) =
          ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
            (· ^ 2 ^ c)).map ψ := by
      rw [hmat, Matrix.map_map, Matrix.map_map]
      congr 1
      funext x
      exact (map_pow ψ x (2 ^ c)).symm
    have hv : e.symm (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₁)) *ᵥ v) =
        ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
          (· ^ 2 ^ c₁)) *ᵥ e.symm v := by
      rw [htwist c₁]
      exact map_symm_mulVec_coord ψ _ v
    have hw : e.symm (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₂)) *ᵥ w) =
        ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
          (· ^ 2 ^ c₂)) *ᵥ e.symm w := by
      rw [htwist c₂]
      exact map_symm_mulVec_coord ψ _ w
    change β' (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₁)) *ᵥ v)
        (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₂)) *ᵥ w) =
      ((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₃)) *ᵥ β' v w
    calc
      β' (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₁)) *ᵥ v)
          (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₂)) *ᵥ w)
          = e (β (e.symm (((A : Matrix (Fin 4) (Fin 4) (F a)).map
                (· ^ 2 ^ c₁)) *ᵥ v))
              (e.symm (((A : Matrix (Fin 4) (Fin 4) (F a)).map
                (· ^ 2 ^ c₂)) *ᵥ w))) := rfl
      _ = e (β ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
                (· ^ 2 ^ c₁) *ᵥ e.symm v)
              ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map
                (· ^ 2 ^ c₂) *ᵥ e.symm w)) := by
          rw [hv, hw]
      _ = e ((((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).map (· ^ 2 ^ c₃) *ᵥ
              β (e.symm v) (e.symm w)) := by
          simpa using congrArg e (hβ ⟨g, hg⟩ (e.symm v) (e.symm w))
      _ = (((A : Matrix (Fin 4) (Fin 4) (F a)).map (· ^ 2 ^ c₃)) *ᵥ
              β' v w) := by
          rw [htwist c₃]
          exact funext fun i => RingHom.map_mulVec (ψ : K →+* F a) _ _ i
  have hβ'zero : β' = 0 :=
    biadd_eq_zero_of_twisted_equivariant ha c₁ c₂ c₃ β' (by
      simpa [twHom_apply, natHom_apply] using hβ')
  refine AddMonoidHom.ext fun v => AddMonoidHom.ext fun w => ?_
  have h := congrArg (fun f : (Fin 4 → F a) →+ (Fin 4 → F a) →+ (Fin 4 → F a) =>
      f (e v) (e w)) hβ'zero
  have h2 : e (β v w) = 0 := by
    simpa [β'] using h
  exact e.injective (by simpa using h2)

end CFSG.RepresentationTheory.SzMartineau

end
