module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRootTransport
public import CFSG.RankThree.CentralLiftU.HypRankOneConj

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm noncommProd_univ_fin)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (mem_hypTorus_of_isLinePerm)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r ε : ℕ}

section Diag

theorem mem_hypTorus_of_diag {g : hypSU h r ε} {q : HypIndex r ε → K}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q) :
    g ∈ hypTorus h r ε := by
  refine mem_hypTorus_of_isLinePerm fun x y => ?_
  rw [hg, Equiv.Perm.one_apply, diagonal_apply]
  by_cases hyx : y = x
  · subst hyx
    simp [diag_entry_ne_zero h hg y]
  · simp [hyx]

theorem hypSU_eq_of_diag {g g' : hypSU h r ε} {q q' : HypIndex r ε → K}
    (hg : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (hg' : ((g' : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q')
    (he : ∀ x : Fin r, q (.inl x) = q' (.inl x))
    (hz : ∀ k : Fin ε, q (.inr (.inl k)) = q' (.inr (.inl k))) : g = g' := by
  apply Subtype.ext
  apply Units.ext
  rw [hg, hg']
  congr 1
  funext x
  rcases x with x | k | x
  · exact he x
  · exact hz k
  · have h1 := diag_entries h hg (.inl x)
    have h2 := diag_entries h hg' (.inl x)
    simp only [hypPartner_inl] at h1 h2
    rw [he x] at h1
    exact (eq_inv_of_mul_eq_one_right h1).trans (eq_inv_of_mul_eq_one_right h2).symm

theorem coe_list_prod_of_diag {ι : Type*} (g : ι → hypSU h r ε) (q : ι → HypIndex r ε → K)
    (hg : ∀ m, ((g m : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (q m)) (l : List ι) :
    (((l.map g).prod : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal fun x => (l.map fun m => q m x).prod := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Subgroup.coe_one, Units.val_one]
    exact diagonal_one.symm
  | cons m l ih =>
    simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, Units.val_mul, hg, ih,
      diagonal_mul_diagonal]

theorem coe_prod_ofFn_of_diag {n : ℕ} (g : Fin n → hypSU h r ε) (q : Fin n → HypIndex r ε → K)
    (hg : ∀ m, ((g m : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (q m)) :
    (((List.ofFn g).prod : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal fun x => ∏ m, q m x := by
  rw [List.ofFn_eq_map, coe_list_prod_of_diag h g q hg]
  refine congrArg diagonal (funext fun x => ?_)
  rw [← List.ofFn_eq_map, List.prod_ofFn]

end Diag

section Coord

theorem torus_entry_ne_zero (t : hypTorus h r ε) (x : HypIndex r ε) :
    (((t : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x ≠
      0 := by
  obtain ⟨a, d, -, -, hm⟩ := t.2
  rw [hm, diagonal_apply_eq]
  exact diag_entry_ne_zero h hm x

@[expose] noncomputable def tcoord (x : Fin r) : hypTorus h r ε →* Kˣ where
  toFun t := Units.mk0 ((((t : hypSU h r ε) : GL (HypIndex r ε) K) :
    Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl x) (.inl x)) (torus_entry_ne_zero h t _)
  map_one' := by
    ext
    simp
  map_mul' t t' := by
    obtain ⟨a, d, -, -, hm⟩ := t.2
    obtain ⟨a', d', -, -, hm'⟩ := t'.2
    ext
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul]
    rw [hm, hm', diagonal_mul_diagonal, diagonal_apply_eq, diagonal_apply_eq, diagonal_apply_eq]

theorem coe_tcoord (x : Fin r) (t : hypTorus h r ε) :
    ((tcoord h x t : Kˣ) : K) = (((t : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl x) (.inl x) :=
  rfl

theorem coe_tcoord_of_diag (x : Fin r) {t : hypTorus h r ε} {q : HypIndex r ε → K}
    (ht : (((t : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q) :
    ((tcoord h x t : Kˣ) : K) = q (.inl x) := by
  rw [coe_tcoord, ht, diagonal_apply_eq]

@[expose] noncomputable def cumCoord (m : Fin r) : hypTorus h r ε →* Kˣ where
  toFun t := ∏ l ∈ Finset.Iic m, tcoord h l t
  map_one' := by simp
  map_mul' t t' := by simp [Finset.prod_mul_distrib]

theorem cumCoord_apply (m : Fin r) (t : hypTorus h r ε) :
    cumCoord h m t = ∏ l ∈ Finset.Iic m, tcoord h l t :=
  rfl

end Coord

section Prod

variable {M G : Type*} [Monoid M] [Monoid G]

@[expose] noncomputable def prodHom {n : ℕ} (f : Fin n → M →* G)
    (hf : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) : M →* G :=
  (MonoidHom.noncommPiCoprod f hf).comp (MonoidHom.pi fun _ => MonoidHom.id M)

theorem prodHom_apply {n : ℕ} (f : Fin n → M →* G)
    (hf : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) (x : M) :
    prodHom f hf x = (List.ofFn fun i => f i x).prod := by
  rw [prodHom, MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_apply]
  exact noncommProd_univ_fin _ _

theorem prod_ofFn_eq_single : ∀ {n : ℕ} (g : Fin n → G) (i : Fin n),
    (∀ j, j ≠ i → g j = 1) → (List.ofFn g).prod = g i
  | 0, _, i, _ => i.elim0
  | n + 1, g, i, hg => by
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hi : i = 0
    · subst hi
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hg _ (Fin.succ_ne_zero j)
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hi
      rw [hg 0 (Ne.symm hi), one_mul]
      exact prod_ofFn_eq_single (fun k => g k.succ) j
        (fun k hk => hg _ (fun e => hk (Fin.succ_injective _ e)))

end Prod

theorem commute_of_conj_eq {G : Type*} [Group G] {x y : G} (hxy : x * y * x⁻¹ = y) :
    Commute x y :=
  mul_inv_eq_iff_eq_mul.mp hxy

end CFSG.RankThree.CentralLiftU
