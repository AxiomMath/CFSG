module

public import CFSG.RankThree.PartOne.SEITZQ1.Conj
public import CFSG.LieType.Ree.LocalBlockSylowAction

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)

open scoped MatrixGroups

section Matrices

variable {L : Type} [Field L]

@[expose] def q1T02 (t : L) : SL(3, L) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t

@[expose] def q1T20 (t : L) : SL(3, L) :=
  Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t

theorem q1_diag_eq_transvections (z : L) (hz : z ≠ 0) (d : SL(3, L))
    (hd : (d : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![z, 1, z⁻¹]) :
    d = q1T02 z * q1T20 (-z⁻¹) * q1T02 z * q1T02 (-1) * q1T20 1 * q1T02 (-1) := by
  apply Subtype.ext
  rw [hd]
  simp only [q1T02, q1T20, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
      Matrix.add_apply] <;>
    field_simp <;> ring

end Matrices

section Roots


@[expose] def q1BlockRoots : Set (Fin ReeTag.F4.tag.rank → ℤ) :=
  {-Pi.single 0 1, Pi.single 0 1, -Pi.single 3 1, Pi.single 3 1}

@[expose] def q1FrameRoots : Set (Fin ReeTag.F4.tag.rank → ℤ) :=
  {![1, 2, 4, 2], ![-1, -2, -4, -2], ![1, 2, 2, 1], ![-1, -2, -2, -1]}

theorem neg_single_zero_mem_q1BlockRoots :
    (-Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ q1BlockRoots :=
  Set.mem_insert _ _

theorem single_zero_mem_q1BlockRoots :
    (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ q1BlockRoots :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem neg_single_three_mem_q1BlockRoots :
    (-Pi.single 3 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ q1BlockRoots :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem single_three_mem_q1BlockRoots :
    (Pi.single 3 1 : Fin ReeTag.F4.tag.rank → ℤ) ∈ q1BlockRoots :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem isRoot_of_mem_q1BlockRoots {β : Fin ReeTag.F4.tag.rank → ℤ} (h : β ∈ q1BlockRoots) :
    IsRoot ReeTag.F4.tag β := by
  rcases h with rfl | rfl | rfl | rfl
  exacts [isRoot_neg_single _ _, isRoot_single _ _, isRoot_neg_single _ _, isRoot_single _ _]

theorem sig_zero_two_mem_q1FrameRoots : q1Sig 0 2 ∈ q1FrameRoots := by
  rw [(q1Sig_values).2.2.1]
  exact Set.mem_insert _ _

theorem sig_two_zero_mem_q1FrameRoots : q1Sig 2 0 ∈ q1FrameRoots := by
  rw [(q1Sig_values).2.2.2.2.2]
  exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem tau_mem_q1FrameRoots {s : Fin ReeTag.F4.tag.rank} (hs : s = 0 ∨ s = 3) {i j : Fin 3}
    (h : (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) : q1Tau s i j ∈ q1FrameRoots := by
  rcases hs with rfl | rfl <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [(q1Tau_zero_values).2.2.1]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · rw [(q1Tau_zero_values).2.2.2.2.2]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · rw [(q1Tau_three_values).2.2.1]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · rw [(q1Tau_three_values).2.2.2.2.2]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem isRoot_of_mem_q1FrameRoots {γ : Fin ReeTag.F4.tag.rank → ℤ} (h : γ ∈ q1FrameRoots) :
    IsRoot ReeTag.F4.tag γ := by
  rcases h with rfl | rfl | rfl | rfl
  · have := isRoot_q1Sig (i := 0) (j := 2) (by decide)
    rw [(q1Sig_values).2.2.1] at this
    exact this
  · have := isRoot_q1Sig (i := 2) (j := 0) (by decide)
    rw [(q1Sig_values).2.2.2.2.2] at this
    exact this
  · have := isRoot_q1Tau (s := 0) (i := 0) (j := 2) (by decide)
    rw [(q1Tau_zero_values).2.2.1] at this
    exact this
  · have := isRoot_q1Tau (s := 0) (i := 2) (j := 0) (by decide)
    rw [(q1Tau_zero_values).2.2.2.2.2] at this
    exact this

theorem q1_iform_block_frame {β γ : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ q1BlockRoots)
    (hγ : γ ∈ q1FrameRoots) : iform (τ := ReeTag.F4.tag) β γ = 0 := by
  rcases hβ with rfl | rfl | rfl | rfl <;> rcases hγ with rfl | rfl | rfl | rfl <;>
    decide +kernel

end Roots

section Certificate

theorem q1_root_thirtySix : Tag.F4.rootCertificate.root 36 = ![1, 2, 2, 1] := by
  funext k; fin_cases k <;> decide +kernel

theorem q1_root_three : Tag.F4.rootCertificate.root 3 = Pi.single 3 1 := by
  funext k; fin_cases k <;> decide +kernel

theorem q1_root_eleven : Tag.F4.rootCertificate.root 11 = -Pi.single 3 1 := by
  funext k; fin_cases k <;> decide +kernel

theorem q1_wordCheck_tau_e3 :
    wordCheck Tag.F4 2 [(1, 0, 36, 1), (0, 1, 3, 1)] [(0, 1, 3, 1), (1, 0, 36, 1)] = true := by
  decide +kernel

theorem q1_wordCheck_tau_neg_e3 :
    wordCheck Tag.F4 2 [(1, 0, 36, 1), (0, 1, 11, 1)] [(0, 1, 11, 1), (1, 0, 36, 1)] = true := by
  decide +kernel

end Certificate

section Conj

variable {G : Type*} [Group G]

theorem q1_commute_conj_of_commute {n a b a' b' : G} (h : Commute a b) (ha : n * a * n⁻¹ = a')
    (hb : n * b * n⁻¹ = b') : Commute a' b' := by
  subst ha hb
  show n * a * n⁻¹ * (n * b * n⁻¹) = n * b * n⁻¹ * (n * a * n⁻¹)
  calc n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by group
    _ = n * (b * a) * n⁻¹ := by rw [h.eq]
    _ = n * b * n⁻¹ * (n * a * n⁻¹) := by group

end Conj

section ShortShort

variable {L : Type} [Field L]

theorem q1_commute_block_long {β γ : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ q1BlockRoots)
    (hq : ReeTag.F4.quadForm β = 4) (hγ : γ ∈ q1FrameRoots) (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L β s) (pinnedX ReeTag.F4.tag L γ t) :=
  commute_pinnedX_of_long_orthogonal (isRoot_of_mem_q1BlockRoots hβ)
    (isRoot_of_mem_q1FrameRoots hγ) hq (q1_iform_block_frame hβ hγ) s t

theorem q1_commute_frame_long {β γ : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ q1BlockRoots)
    (hγ : γ ∈ q1FrameRoots) (hq : ReeTag.F4.quadForm γ = 4) (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L β s) (pinnedX ReeTag.F4.tag L γ t) :=
  (commute_pinnedX_of_long_orthogonal (isRoot_of_mem_q1FrameRoots hγ)
    (isRoot_of_mem_q1BlockRoots hβ) hq (by rw [iform_comm]; exact q1_iform_block_frame hβ hγ)
    t s).symm

variable [CharP L 2]

@[expose] def q1TWWord : List (Fin ReeTag.F4.tag.rank) := [1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 3]

@[expose] def q1TW : WeylGroup ReeTag.F4.tag := (coxeterSystem ReeTag.F4.tag).wordProd q1TWWord

theorem q1TW_smul (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    q1TW • γ = CFSG.RankThree.Lattice.wordMat Tag.F4 q1TWWord *ᵥ γ :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _

theorem q1TW_conj_pinnedX {γ γ' : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ)
    (h : CFSG.RankThree.Lattice.wordMat Tag.F4 q1TWWord *ᵥ γ = γ') (c : L) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) L q1TW * pinnedX ReeTag.F4.tag L γ c *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1TW)⁻¹ = pinnedX ReeTag.F4.tag L γ' c := by
  rw [canonicalRep_conj_pinnedX q1TW hγ, q1TW_smul, h]

theorem q1_commute_tau_e3 (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L ![1, 2, 2, 1] s)
      (pinnedX ReeTag.F4.tag L (Pi.single 3 1) t) := by
  have h := factorPinned_eq_of_wordCheck q1_wordCheck_tau_e3 L (CharP.cast_eq_zero L 2) s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  rw [q1_root_thirtySix, q1_root_three] at h
  exact h

theorem q1_commute_tau_neg_e3 (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L ![1, 2, 2, 1] s)
      (pinnedX ReeTag.F4.tag L (-Pi.single 3 1) t) := by
  have h := factorPinned_eq_of_wordCheck q1_wordCheck_tau_neg_e3 L (CharP.cast_eq_zero L 2) s t
  simp only [factorPinned_cons, factorPinned_nil, Int.cast_one, one_mul, pow_zero, pow_one,
    mul_one] at h
  rw [q1_root_thirtySix, q1_root_eleven] at h
  exact h

theorem q1_isRoot_tau : IsRoot ReeTag.F4.tag (![1, 2, 2, 1] : Fin ReeTag.F4.tag.rank → ℤ) :=
  isRoot_of_mem_q1FrameRoots (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert _ _)))

theorem q1_commute_neg_tau_neg_e3 (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L ![-1, -2, -2, -1] s)
      (pinnedX ReeTag.F4.tag L (-Pi.single 3 1) t) := by
  refine q1_commute_conj_of_commute (q1_commute_tau_e3 s t)
    (q1TW_conj_pinnedX q1_isRoot_tau ?_ s) (q1TW_conj_pinnedX (isRoot_single _ _) ?_ t)
  · funext k; fin_cases k <;> decide +kernel
  · funext k; fin_cases k <;> decide +kernel

theorem q1_commute_neg_tau_e3 (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L ![-1, -2, -2, -1] s)
      (pinnedX ReeTag.F4.tag L (Pi.single 3 1) t) := by
  refine q1_commute_conj_of_commute (q1_commute_tau_neg_e3 s t)
    (q1TW_conj_pinnedX q1_isRoot_tau ?_ s) (q1TW_conj_pinnedX (isRoot_neg_single _ _) ?_ t)
  · funext k; fin_cases k <;> decide +kernel
  · funext k; fin_cases k <;> decide +kernel

theorem q1_commute_block_frame {β γ : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ q1BlockRoots)
    (hγ : γ ∈ q1FrameRoots) (s t : L) :
    Commute (pinnedX ReeTag.F4.tag L β s) (pinnedX ReeTag.F4.tag L γ t) := by
  rcases id hβ with rfl | rfl | rfl | rfl
  · exact q1_commute_block_long hβ quadForm_neg_single_zero hγ s t
  · exact q1_commute_block_long hβ quadForm_single_zero hγ s t
  · rcases id hγ with rfl | rfl | rfl | rfl
    · exact q1_commute_frame_long hβ hγ (by decide +kernel) s t
    · exact q1_commute_frame_long hβ hγ (by decide +kernel) s t
    · exact (q1_commute_tau_neg_e3 t s).symm
    · exact (q1_commute_neg_tau_neg_e3 t s).symm
  · rcases id hγ with rfl | rfl | rfl | rfl
    · exact q1_commute_frame_long hβ hγ (by decide +kernel) s t
    · exact q1_commute_frame_long hβ hγ (by decide +kernel) s t
    · exact (q1_commute_tau_e3 t s).symm
    · exact (q1_commute_neg_tau_e3 t s).symm

end ShortShort

section Block

variable {L : Type} [Field L]

@[expose] def q1BlockGen (L : Type) [Field L] : Set (ModGL ReeTag.F4.tag L) :=
  {g | ∃ β ∈ q1BlockRoots, ∃ t : L, g = pinnedX ReeTag.F4.tag L β t}

@[expose] def q1BlockGroup (L : Type) [Field L] : Subgroup (ModGL ReeTag.F4.tag L) :=
  Subgroup.closure (q1BlockGen L)

theorem pinnedX_mem_q1BlockGroup {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : β ∈ q1BlockRoots)
    (t : L) : pinnedX ReeTag.F4.tag L β t ∈ q1BlockGroup L :=
  Subgroup.subset_closure ⟨β, hβ, t, rfl⟩

theorem q1_commute_of_mem_centralizer {g h : ModGL ReeTag.F4.tag L}
    (hg : g ∈ Subgroup.centralizer (q1BlockGen L)) (hh : h ∈ q1BlockGroup L) :
    h * g = g * h := by
  rw [← Subgroup.centralizer_closure] at hg
  exact Subgroup.mem_centralizer_iff.1 hg h hh

theorem q1CA_mem_q1BlockGroup (ω : L) : q1CA ω ∈ q1BlockGroup L :=
  mul_mem (mul_mem (pinnedX_mem_q1BlockGroup neg_single_zero_mem_q1BlockRoots _)
    (pinnedX_mem_q1BlockGroup single_zero_mem_q1BlockRoots _))
    (mul_mem (pinnedX_mem_q1BlockGroup neg_single_three_mem_q1BlockRoots _)
      (pinnedX_mem_q1BlockGroup single_three_mem_q1BlockRoots _))

variable [CharP L 2]

theorem q1_frame_mem_centralizer {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : γ ∈ q1FrameRoots)
    (t : L) : pinnedX ReeTag.F4.tag L γ t ∈ Subgroup.centralizer (q1BlockGen L) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨β, hβ, s, rfl⟩
  exact (q1_commute_block_frame hβ hγ s t).eq

end Block

section Centralizer

variable {L : Type} [Field L] [CharP L 2]

theorem q1V_smul_mem_q1FrameRoots {γ : Fin ReeTag.F4.tag.rank → ℤ} (h : γ ∈ q1BlockRoots) :
    q1V • γ ∈ q1FrameRoots := by
  rw [q1V_smul]
  rcases h with rfl | rfl | rfl | rfl
  · have e : CFSG.RankThree.Lattice.wordMat Tag.F4 q1VWord *ᵥ
        (-Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) = ![-1, -2, -4, -2] := by
      funext k; fin_cases k <;> decide +kernel
    rw [e]
    exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · have e : CFSG.RankThree.Lattice.wordMat Tag.F4 q1VWord *ᵥ
        (Pi.single 0 1 : Fin ReeTag.F4.tag.rank → ℤ) = ![1, 2, 4, 2] := by
      funext k; fin_cases k <;> decide +kernel
    rw [e]
    exact Set.mem_insert _ _
  · have e : CFSG.RankThree.Lattice.wordMat Tag.F4 q1VWord *ᵥ
        (-Pi.single 3 1 : Fin ReeTag.F4.tag.rank → ℤ) = ![-1, -2, -2, -1] := by
      funext k; fin_cases k <;> decide +kernel
    rw [e]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  · have e : CFSG.RankThree.Lattice.wordMat Tag.F4 q1VWord *ᵥ
        (Pi.single 3 1 : Fin ReeTag.F4.tag.rank → ℤ) = ![1, 2, 2, 1] := by
      funext k; fin_cases k <;> decide +kernel
    rw [e]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem q1CL_mem_centralizer (ω : L) : q1CL ω ∈ Subgroup.centralizer (q1BlockGen L) := by
  rw [q1CL_eq]
  exact mul_mem (mul_mem (mul_mem
    (q1_frame_mem_centralizer (q1V_smul_mem_q1FrameRoots neg_single_zero_mem_q1BlockRoots) ω)
    (q1_frame_mem_centralizer (q1V_smul_mem_q1FrameRoots single_zero_mem_q1BlockRoots) 1))
    (q1_frame_mem_centralizer (q1V_smul_mem_q1FrameRoots neg_single_three_mem_q1BlockRoots) ω))
    (q1_frame_mem_centralizer (q1V_smul_mem_q1FrameRoots single_three_mem_q1BlockRoots) 1)

variable {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem q1Psi0_diag_mem_centralizer (hF : IsReeFrob a F) (z : L) (hz : z ≠ 0) (d : SL(3, L))
    (hd : (d : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![z, 1, z⁻¹]) :
    q1Psi0 hF d ∈ Subgroup.centralizer (q1BlockGen L) := by
  have hS : ∀ (i j : Fin 3) (hij : i ≠ j), ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) → ∀ t : L,
      q1Psi0 hF (Matrix.SpecialLinearGroup.transvection hij t) ∈
        Subgroup.centralizer (q1BlockGen L) := by
    intro i j hij hij' t
    rw [q1Psi0_apply, q1Rho_transvection i j hij, q1PsiRho_transvection hF hij]
    refine mul_mem (q1_frame_mem_centralizer ?_ t) (q1_frame_mem_centralizer ?_ (t ^ 2 ^ a))
    · rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      exacts [sig_zero_two_mem_q1FrameRoots, sig_two_zero_mem_q1FrameRoots]
    · exact tau_mem_q1FrameRoots (q1Par_cases a) hij'
  have h02 : ∀ t : L, q1Psi0 hF (q1T02 t) ∈ Subgroup.centralizer (q1BlockGen L) :=
    fun t => hS 0 2 (by decide) (Or.inl ⟨rfl, rfl⟩) t
  have h20 : ∀ t : L, q1Psi0 hF (q1T20 t) ∈ Subgroup.centralizer (q1BlockGen L) :=
    fun t => hS 2 0 (by decide) (Or.inr ⟨rfl, rfl⟩) t
  rw [q1_diag_eq_transvections z hz d hd]
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h02 z) (h20 _)) (h02 z)) (h02 _)) (h20 1))
    (h02 _)

theorem q1_commute_conj (ω : L) {h : ModGL ReeTag.F4.tag L}
    (hh : h ∈ Subgroup.centralizer (q1BlockGen L)) {X : ModGL ReeTag.F4.tag L}
    (hX : X ∈ q1BlockGroup L) :
    X * (q1C ω * h * (q1C ω)⁻¹) = q1C ω * h * (q1C ω)⁻¹ * X := by
  have hcA : q1CA ω ∈ q1BlockGroup L := q1CA_mem_q1BlockGroup ω
  obtain ⟨Y, hYA, rfl⟩ : ∃ Y ∈ q1BlockGroup L, X = q1C ω * Y * (q1C ω)⁻¹ := by
    obtain ⟨Y', hY'⟩ : ∃ Y', Y' = (q1CA ω)⁻¹ * X * q1CA ω := ⟨_, rfl⟩
    have hY'A : Y' ∈ q1BlockGroup L := hY' ▸ mul_mem (mul_mem (inv_mem hcA) hX) hcA
    have hc : q1CL ω * Y' = Y' * q1CL ω :=
      (q1_commute_of_mem_centralizer (q1CL_mem_centralizer ω) hY'A).symm
    have e1 : q1CL ω * Y' * (q1CL ω)⁻¹ = Y' := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨Y', hY'A, ?_⟩
    calc X = q1CA ω * Y' * (q1CA ω)⁻¹ := by rw [hY']; group
      _ = q1CA ω * (q1CL ω * Y' * (q1CL ω)⁻¹) * (q1CA ω)⁻¹ := by rw [e1]
      _ = q1C ω * Y' * (q1C ω)⁻¹ := by rw [q1C]; group
  have hYh : Y * h = h * Y := q1_commute_of_mem_centralizer hh hYA
  calc q1C ω * Y * (q1C ω)⁻¹ * (q1C ω * h * (q1C ω)⁻¹) = q1C ω * (Y * h) * (q1C ω)⁻¹ := by
        group
    _ = q1C ω * (h * Y) * (q1C ω)⁻¹ := by rw [hYh]
    _ = q1C ω * h * (q1C ω)⁻¹ * (q1C ω * Y * (q1C ω)⁻¹) := by group

end Centralizer

section BaseChange

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L]

theorem q1_baseChange_localBlock_mem {y : ModGL ReeTag.F4.tag K}
    (hy : y ∈ ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩) :
    baseChangeGL (algebraMap K L) y ∈ q1BlockGroup L := by
  have hmap : ∀ {S : Set (Fin ReeTag.F4.tag.rank → ℤ)}, S ⊆ q1BlockRoots →
      rootSpan ReeTag.F4.tag K S ≤
        (q1BlockGroup L).comap (baseChangeGL (algebraMap K L)) := by
    intro S hS
    refine iSup₂_le fun α hα => ?_
    show rootSubgroup ReeTag.F4.tag K α ≤ _
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_pinnedX]
    exact pinnedX_mem_q1BlockGroup (hS hα) _
  have hle : ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩ ≤
      (q1BlockGroup L).comap (baseChangeGL (algebraMap K L)) := by
    refine sup_le (inf_le_left.trans (hmap ?_)) (inf_le_left.trans (hmap ?_))
    · rw [ReeTag.F4_fixedOrbitRoots_zero]
      rintro α (rfl | rfl)
      exacts [single_zero_mem_q1BlockRoots, single_three_mem_q1BlockRoots]
    · rw [ReeTag.F4_fixedOrbitRoots_zero, Set.image_insert_eq, Set.image_singleton]
      rintro α (rfl | rfl)
      exacts [neg_single_zero_mem_q1BlockRoots, neg_single_three_mem_q1BlockRoots]
  exact hle hy

variable [CharP L 2]

theorem q1_commute_localBlock (D : ReeFrameData K L a) (ω : L) (x : ReeTag.F4.reeGamma K a)
    (d : SL(3, L)) (z : L) (hz : z ≠ 0)
    (hd : (d : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![z, 1, z⁻¹])
    (hx : thetaGamma L a x = q1C ω * q1Psi0 D.isFrob d * (q1C ω)⁻¹) :
    ∀ y ∈ ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩,
      (x : ModGL ReeTag.F4.tag K) * y = y * x := by
  intro y hy
  have hyΓ : y ∈ ReeTag.F4.reeGamma K a :=
    (sup_le inf_le_right inf_le_right :
      ReeTag.F4.reeLocalBlock K a ⟨0, by decide⟩ ≤ ReeTag.F4.reeGamma K a) hy
  have hyA : thetaGamma L a ⟨y, hyΓ⟩ ∈ q1BlockGroup L := by
    rw [thetaGamma_apply]
    exact q1_baseChange_localBlock_mem hy
  have hcomm := q1_commute_conj ω (q1Psi0_diag_mem_centralizer D.isFrob z hz d hd) hyA
  rw [← hx] at hcomm
  have h : thetaGamma L a (x * ⟨y, hyΓ⟩) = thetaGamma L a (⟨y, hyΓ⟩ * x) := by
    rw [map_mul, map_mul]
    exact hcomm.symm
  exact congrArg Subtype.val (thetaGamma_injective (K := K) L h)

end BaseChange

end CFSG.RankThree.PartOne.SEITZQ1
