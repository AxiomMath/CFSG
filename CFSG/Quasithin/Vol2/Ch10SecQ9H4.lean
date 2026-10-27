module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] def utM (a b c : K) : Matrix (Fin 3) (Fin 3) K := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem utM_mul (a b c a' b' c' : K) :
    utM a b c * utM a' b' c' = utM (a + a') (b + a * c' + b') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem utM_eq_one {a b c : K} (ha : a = 0) (hb : b = 0) (hc : c = 0) : utM a b c = 1 := by
  subst ha hb hc
  ext i j
  fin_cases i <;> fin_cases j <;> simp [utM]

theorem det_utM (a b c : K) : (utM a b c).det = 1 := by
  simp [utM, Matrix.det_fin_three]

@[expose] def ut3 (a b c : K) : GL (Fin 3) K :=
  ⟨utM a b c, utM (-a) (a * c - b) (-c),
    by rw [utM_mul]; exact utM_eq_one (by ring) (by ring) (by ring),
    by rw [utM_mul]; exact utM_eq_one (by ring) (by ring) (by ring)⟩

theorem coe_ut3 (a b c : K) : ((ut3 a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    utM a b c := rfl

theorem ut3_mul (a b c a' b' c' : K) :
    ut3 a b c * ut3 a' b' c' = ut3 (a + a') (b + a * c' + b') (c + c') :=
  Units.ext (utM_mul a b c a' b' c')

theorem ut3_zero : ut3 (0 : K) 0 0 = 1 :=
  Units.ext (utM_eq_one rfl rfl rfl)

theorem ut3_inv (a b c : K) : (ut3 a b c)⁻¹ = ut3 (-a) (a * c - b) (-c) := by
  rw [inv_eq_iff_mul_eq_one, ut3_mul]
  exact Units.ext (utM_eq_one (by ring) (by ring) (by ring))

theorem ut3_injective {a b c a' b' c' : K} (h : ut3 a b c = ut3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [coe_ut3] at h'
  exact ⟨by simpa [utM] using congrFun (congrFun h' 0) 1,
    by simpa [utM] using congrFun (congrFun h' 0) 2,
    by simpa [utM] using congrFun (congrFun h' 1) 2⟩

@[expose] def ut3Sub (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a b c : K, g = ut3 a b c}
  one_mem' := ⟨0, 0, 0, ut3_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, ut3_mul a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, ut3_inv a b c⟩

theorem ut3_mem (a b c : K) : ut3 a b c ∈ ut3Sub K := ⟨a, b, c, rfl⟩

theorem ut3Sub_le_statedSL : ut3Sub K ≤ StatedSL 3 K := by
  rintro _ ⟨a, b, c, rfl⟩
  exact Subgroup.subset_closure (det_utM a b c)

theorem card_ut3Sub [Finite K] : Nat.card (ut3Sub K) = Nat.card K ^ 3 := by
  have hbij : Function.Bijective (fun v : K × K × K =>
      (⟨ut3 v.1 v.2.1 v.2.2, ut3_mem _ _ _⟩ : ↥(ut3Sub K))) := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := ut3_injective (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨a, b, c, hg⟩ := g.2
      exact ⟨(a, b, c), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, Nat.card_prod]
  ring

theorem ut3_comm_centre (x a b c : K) : ut3 0 x 0 * ut3 a b c = ut3 a b c * ut3 0 x 0 := by
  rw [ut3_mul, ut3_mul]
  congr 1 <;> ring

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
