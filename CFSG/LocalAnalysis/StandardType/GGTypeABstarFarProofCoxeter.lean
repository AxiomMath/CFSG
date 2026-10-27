module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeAFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem SpecialLinear

theorem coxeterMatrix_isFiniteType_A_eq (m : ℕ) :
    coxeterMatrix (isFiniteType_A m) = CoxeterMatrix.A m := by
  apply CoxeterMatrix.ext
  funext i j
  change coxeterMatrix (isFiniteType_A m) i j = (CoxeterMatrix.A m).M i j
  rw [coxeterMatrix_A_apply]
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have h' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
      simp [hij, hadj, h']
    · have h' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := fun h => hadj h.symm
      simp [hij, hadj, h']

private lemma bfCoxeter_toStd_single_eq_one {m : ℕ} (k : Fin m) (x : Fin (m + 1))
    (h : toStd m (Pi.single k (1 : ℤ)) x = 1) : x = k.castSucc := by
  rw [toStd_single] at h
  by_cases hx : x = k.castSucc
  · exact hx
  · by_cases hb : x = k.succ
    · subst hb
      simp [Pi.sub_apply, Fin.castSucc_lt_succ.ne'] at h
    · simp [Pi.sub_apply, hx, hb] at h

private lemma bfCoxeter_toStd_single_eq_neg_one {m : ℕ} (k : Fin m) (x : Fin (m + 1))
    (h : toStd m (Pi.single k (1 : ℤ)) x = -1) : x = k.succ := by
  rw [toStd_single] at h
  by_cases hb : x = k.succ
  · exact hb
  · by_cases hx : x = k.castSucc
    · subst hx
      simp [Pi.sub_apply, Fin.castSucc_lt_succ.ne] at h
    · simp [Pi.sub_apply, hx, hb] at h

theorem typeAWeylHom_injective (m : ℕ) : Function.Injective (typeAWeylHom m) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  have hreal : TypeARealizes m 1 π := by
    rw [← hπ]
    exact typeAWeylOf_spec m π
  have key : ∀ (k : Fin m) (b : Fin (m + 1)),
      toStd m (Pi.single k (1 : ℤ)) (π b) = toStd m (Pi.single k (1 : ℤ)) b := by
    intro k b
    have h := congrFun (hreal (Pi.single k 1)) (π b)
    rw [map_one, Module.End.one_apply] at h
    simpa using h
  apply Equiv.ext
  intro c
  rcases Fin.eq_castSucc_or_eq_last c with ⟨k, rfl⟩ | rfl
  · rw [bfCoxeter_toStd_single_eq_one k (π k.castSucc)
      (by rw [key k k.castSucc, toStd_single]; simp [Pi.sub_apply, Fin.castSucc_lt_succ.ne])]
    rfl
  · have hgoal : π (Fin.last m) = Fin.last m := by
      by_cases hm : m = 0
      · subst hm
        apply Fin.ext
        have h := (π (Fin.last 0)).isLt
        simp only [Fin.val_last]
        omega
      · let kk : Fin m := ⟨m - 1, by omega⟩
        have hk : kk.succ = Fin.last m := by
          ext
          simp only [Fin.val_succ, Fin.val_last, kk]
          omega
        have hx := bfCoxeter_toStd_single_eq_neg_one kk (π (Fin.last m))
          (by rw [key kk (Fin.last m), ← hk, toStd_single]
              simp [Pi.sub_apply, Fin.castSucc_lt_succ.ne'])
        rwa [hk] at hx
    rw [hgoal]
    rfl

@[expose] noncomputable def typeAWeylEquiv (m : ℕ) :
    Equiv.Perm (Fin (m + 1)) ≃* (coxeterMatrix (isFiniteType_A m)).Group :=
  MulEquiv.ofBijective (typeAWeylHom m) ⟨typeAWeylHom_injective m, typeAWeylHom_surjective m⟩

theorem typeAWeylEquiv_swap (m : ℕ) (k : Fin m) :
    typeAWeylEquiv m (Equiv.swap k.castSucc k.succ) =
      (coxeterMatrix (isFiniteType_A m)).simple k := by
  exact typeARealizes_inj m (typeAWeylOf_spec m _) (typeARealizes_simple m k)

private lemma bfCoxeter_groupEquiv_of_eq {ι : Type*} {M M' : CoxeterMatrix ι} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem exists_permEquiv_of_ggWeylOfType_A {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {m : ℕ} (h : GGWeylOfType p (CoxeterMatrix.A m) A) :
    ∃ Ê : Equiv.Perm (Fin (m + 1)) ≃* ↥A, ∀ k : Fin m,
      GGIsReflection p ((Ê (Equiv.swap k.castSucc k.succ) : ↥A) : MulAut ↥Bs) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨φ, hφ⟩ := bfCoxeter_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq m)
  refine ⟨(typeAWeylEquiv m).trans (φ.trans e), fun k => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, typeAWeylEquiv_swap, hφ k]
  exact he k

end CFSG.StandardType
