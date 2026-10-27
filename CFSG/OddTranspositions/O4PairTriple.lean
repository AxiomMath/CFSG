module

public import CFSG.OddTranspositions.O4CloseReduction
public import CFSG.OddTranspositions.Width
public import CFSG.OddTranspositions.O4PairTenAbstract

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

private instance (priority := 2000) f25tDecEqInst : DecidableEq F25t := f25tDecEq

@[expose] def Ma : Matrix.SpecialLinearGroup (Fin 2) F25t := X 0

@[expose] def Mb : Matrix.SpecialLinearGroup (Fin 2) F25t := X 1

@[expose] def uT : PSigmaL2t := SemidirectProduct.mk (CFSG.PSL2Table.mk Ma) frob25t

@[expose] def vT : PSigmaL2t := SemidirectProduct.mk (CFSG.PSL2Table.mk Mb) frob25t

@[expose] def wT : PSigmaL2t := SemidirectProduct.mk (1 : PSL2 F25t) frob25t

theorem uT_mem_class65t : uT ∈ class65t := by
  refine (mem_class65t_iff_left_right uT).mpr ⟨?_, rfl⟩
  show CFSG.PSL2Table.mk Ma ∈ St
  refine mem_St_iff.mpr ⟨P 0, ?_⟩
  simpa only [map_mul, map_inv, Ma] using x_in_twisted_class (0 : Fin 10)

theorem vT_mem_class65t : vT ∈ class65t := by
  refine (mem_class65t_iff_left_right vT).mpr ⟨?_, rfl⟩
  show CFSG.PSL2Table.mk Mb ∈ St
  refine mem_St_iff.mpr ⟨P 1, ?_⟩
  simpa only [map_mul, map_inv, Mb] using x_in_twisted_class (1 : Fin 10)

theorem wT_mem_class65t : wT ∈ class65t :=
  inr_frob25t_mem_class65t

private theorem x_zero_ne_one : x (0 : Fin 10) ≠ 1 := by
  have hmem : x (0 : Fin 10) ∈ {q : PSL2 F25t | q ∈ St ∧ q * q = 1 ∧ q ≠ 1} := by
    rw [St_involutions_nontrivial]
    exact Set.mem_range_self 0
  exact hmem.2.2

private theorem x_one_ne_one : x (1 : Fin 10) ≠ 1 := by
  have hmem : x (1 : Fin 10) ∈ {q : PSL2 F25t | q ∈ St ∧ q * q = 1 ∧ q ≠ 1} := by
    rw [St_involutions_nontrivial]
    exact Set.mem_range_self 1
  exact hmem.2.2

theorem uT_ne_vT : uT ≠ vT := by
  intro h
  have hleft : x (0 : Fin 10) = x 1 := congrArg SemidirectProduct.left h
  exact (by decide : (0 : Fin 10) ≠ 1) (x_injective hleft)

theorem uT_ne_wT : uT ≠ wT := by
  intro h
  have hleft : x (0 : Fin 10) = 1 := congrArg SemidirectProduct.left h
  exact x_zero_ne_one hleft

theorem vT_ne_wT : vT ≠ wT := by
  intro h
  have hleft : x (1 : Fin 10) = 1 := congrArg SemidirectProduct.left h
  exact x_one_ne_one hleft

private theorem commute_x_zero_one : Commute (x (0 : Fin 10)) (x 1) := by
  rw [commute_x_iff]
  decide

private theorem fixed_x_zero :
    psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk Ma) = CFSG.PSL2Table.mk Ma :=
  x_fixed 0

private theorem fixed_x_one :
    psl2FieldAut F25t frob25t (CFSG.PSL2Table.mk Mb) = CFSG.PSL2Table.mk Mb :=
  x_fixed 1

theorem commute_uT_vT : Commute uT vT :=
  (commute_mk_frob25t_iff fixed_x_zero fixed_x_one).mpr commute_x_zero_one

theorem commute_uT_wT : Commute uT wT :=
  (commute_mk_frob25t_iff fixed_x_zero (map_one (psl2FieldAut F25t frob25t))).mpr
    (Commute.one_right _)

theorem commute_vT_wT : Commute vT wT :=
  (commute_mk_frob25t_iff fixed_x_one (map_one (psl2FieldAut F25t frob25t))).mpr
    (Commute.one_right _)

noncomputable def uA : PSigmaL225 := psigmaL2Equiv uT

noncomputable def vA : PSigmaL225 := psigmaL2Equiv vT

noncomputable def wA : PSigmaL225 := psigmaL2Equiv wT

theorem three_commuting_class65 :
    uA ∈ class65 ∧ vA ∈ class65 ∧ wA ∈ class65 ∧ uA ≠ vA ∧ uA ≠ wA ∧ vA ≠ wA ∧
      Commute uA vA ∧ Commute uA wA ∧ Commute vA wA := by
  have hu : psigmaL2Equiv uT ∈ class65 := by
    rw [← psigmaL2Equiv_image_class65t]
    exact Set.mem_image_of_mem _ uT_mem_class65t
  have hv : psigmaL2Equiv vT ∈ class65 := by
    rw [← psigmaL2Equiv_image_class65t]
    exact Set.mem_image_of_mem _ vT_mem_class65t
  have hw : psigmaL2Equiv wT ∈ class65 := by
    rw [← psigmaL2Equiv_image_class65t]
    exact Set.mem_image_of_mem _ wT_mem_class65t
  exact ⟨hu, hv, hw,
    fun h => uT_ne_vT (psigmaL2Equiv.injective h),
    fun h => uT_ne_wT (psigmaL2Equiv.injective h),
    fun h => vT_ne_wT (psigmaL2Equiv.injective h),
    (psigmaL2Equiv_conj_iff uT vT).mpr commute_uT_vT,
    (psigmaL2Equiv_conj_iff uT wT).mpr commute_uT_wT,
    (psigmaL2Equiv_conj_iff vT wT).mpr commute_vT_wT⟩

theorem not_O4PairData_of_widthLe_two {Y : Type} [Group Y] {Θ : Set Y}
    (hP : O4PairData Y Θ) (hW : WidthLe Θ 2) : False := by
  classical
  obtain ⟨e, he⟩ := hP
  obtain ⟨hu, hv, hw, huv, huw, hvw, hcuv, hcuw, hcvw⟩ := three_commuting_class65
  have mem_preimage : ∀ d : PSigmaL225, d ∈ class65 → e.symm d ∈ Θ := by
    intro d hd
    have hd' : d ∈ e '' Θ := by
      rw [he]
      exact hd
    obtain ⟨y, hy, hyz⟩ := hd'
    rw [← hyz, e.symm_apply_apply]
    exact hy
  have hne₁ : e.symm uA ≠ e.symm vA := fun h => huv (e.symm.injective h)
  have hne₂ : e.symm uA ≠ e.symm wA := fun h => huw (e.symm.injective h)
  have hne₃ : e.symm vA ≠ e.symm wA := fun h => hvw (e.symm.injective h)
  have hsub : (↑({e.symm uA, e.symm vA, e.symm wA} : Finset Y) : Set Y) ⊆ Θ := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_preimage uA hu
    · exact mem_preimage vA hv
    · exact mem_preimage wA hw
  have hcomm : ∀ x ∈ ({e.symm uA, e.symm vA, e.symm wA} : Finset Y),
      ∀ y ∈ ({e.symm uA, e.symm vA, e.symm wA} : Finset Y), x ≠ y → Commute x y := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hcuv.map e.symm
    · exact hcuw.map e.symm
    · exact (hcuv.map e.symm).symm
    · exact absurd rfl hxy
    · exact hcvw.map e.symm
    · exact (hcuw.map e.symm).symm
    · exact (hcvw.map e.symm).symm
    · exact absurd rfl hxy
  have hcard : ({e.symm uA, e.symm vA, e.symm wA} : Finset Y).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, hne₁, hne₂, hne₃, rfl⟩
  have hle : ({e.symm uA, e.symm vA, e.symm wA} : Finset Y).card ≤ 2 := hW _ hsub hcomm
  omega

end CFSG.OddTranspositions.QZ
