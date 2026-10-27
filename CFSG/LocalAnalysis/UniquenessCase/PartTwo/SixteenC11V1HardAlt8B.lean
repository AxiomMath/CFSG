module

public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.C58G64DirectCore
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.H13.VolIAltCoverEightVec
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.G6 CFSG.Quasithin.H13

@[expose] def s16c11_v1_p123_eight : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def s16c11_v1_p456_eight : Equiv.Perm (Fin 8) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def s16c11_v1_blocks_eight : Subgroup (MulAut ↥(coreMod 8)) :=
  (Subgroup.closure ({s16c11_v1_p123_eight, s16c11_v1_p456_eight} : Set (Equiv.Perm (Fin 8)))).map
    (G6.coreAct 8)

private theorem s16c11_v1_mem_fixV_closure_pair {V : Type*} [CommGroup V]
    (a b : MulAut V) (v : V) :
    v ∈ fixV (Subgroup.closure ({a, b} : Set (MulAut V))) ↔ a v = v ∧ b v = v := by
  rw [mem_fixV]
  constructor
  · intro h
    exact ⟨h a (Subgroup.subset_closure (by simp)),
      h b (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨ha, hb⟩ x hx
    refine Subgroup.closure_induction (p := fun x _ => x v = v) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    · rfl
    · intro y z _ _ hy hz
      rw [MulAut.mul_apply, hz, hy]
    · intro y _ hy
      exact MulEquiv.injective y (by rw [MulAut.inv_apply, MulEquiv.apply_symm_apply, hy])

private theorem s16c11_v1_blocks_eight_eq :
    s16c11_v1_blocks_eight =
      Subgroup.closure ({G6.coreAct 8 s16c11_v1_p123_eight,
        G6.coreAct 8 s16c11_v1_p456_eight} : Set (MulAut ↥(coreMod 8))) := by
  rw [s16c11_v1_blocks_eight, MonoidHom.map_closure, Set.image_pair]

private theorem s16c11_v1_coreAct_eight_fixed_iff (σ : Equiv.Perm (Fin 8))
    (v : ↥(coreMod 8)) :
    G6.coreAct 8 σ v = v ↔
      ∀ i : Fin 8, Multiplicative.toAdd (v : G6.PermMod 8) (σ⁻¹ i) =
        Multiplicative.toAdd (v : G6.PermMod 8) i := by
  constructor
  · intro h i
    have h' := congrArg (fun z : ↥(coreMod 8) =>
      Multiplicative.toAdd ((z : ↥(coreMod 8)) : G6.PermMod 8) i) h
    simpa only [G6.coreAct_coe, G6.permAct_apply] using h'
  · intro h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.coreAct_coe, G6.permAct_apply]
    exact h i

private theorem s16c11_v1_forall_inv_apply_iff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 2) :
    (∀ i, x (σ⁻¹ i) = x i) ↔ ∀ i, x i = x (σ i) := by
  constructor
  · intro h i
    simpa using h (σ i)
  · intro h i
    simpa using h (σ⁻¹ i)

private theorem s16c11_v1_p123_apply_zero : s16c11_v1_p123_eight 0 = 1 := by decide

private theorem s16c11_v1_p123_apply_one : s16c11_v1_p123_eight 1 = 2 := by decide

private theorem s16c11_v1_p456_apply_three : s16c11_v1_p456_eight 3 = 4 := by decide

private theorem s16c11_v1_p456_apply_four : s16c11_v1_p456_eight 4 = 5 := by decide

private theorem s16c11_v1_p123_fixed_iff (x : Fin 8 → ZMod 2) :
    (∀ i, x i = x (s16c11_v1_p123_eight i)) ↔ x 0 = x 1 ∧ x 1 = x 2 := by
  constructor
  · intro h
    exact ⟨(h 0).trans (congrArg x s16c11_v1_p123_apply_zero),
      (h 1).trans (congrArg x s16c11_v1_p123_apply_one)⟩
  · rintro ⟨h01, h12⟩ i
    fin_cases i <;> simp_all [s16c11_v1_p123_eight, Equiv.swap_apply_def]

private theorem s16c11_v1_p456_fixed_iff (x : Fin 8 → ZMod 2) :
    (∀ i, x i = x (s16c11_v1_p456_eight i)) ↔ x 3 = x 4 ∧ x 4 = x 5 := by
  constructor
  · intro h
    exact ⟨(h 3).trans (congrArg x s16c11_v1_p456_apply_three),
      (h 4).trans (congrArg x s16c11_v1_p456_apply_four)⟩
  · rintro ⟨h34, h45⟩ i
    fin_cases i <;> simp_all [s16c11_v1_p456_eight, Equiv.swap_apply_def]

private def s16c11_v1_eightConst (x : Fin 8 → ZMod 2) : Prop :=
  x 0 = x 1 ∧ x 1 = x 2 ∧ x 3 = x 4 ∧ x 4 = x 5

private def s16c11_v1_eightVecOf (v : ↥(coreMod 8)) : Fin 8 → ZMod 2 :=
  Multiplicative.toAdd (v : G6.PermMod 8)

private theorem s16c11_v1_mem_fixV_blocks_eight (v : ↥(coreMod 8)) :
    v ∈ fixV s16c11_v1_blocks_eight ↔ s16c11_v1_eightConst (s16c11_v1_eightVecOf v) := by
  rw [s16c11_v1_blocks_eight_eq]
  have h1 : v ∈ fixV (Subgroup.closure ({G6.coreAct 8 s16c11_v1_p123_eight,
      G6.coreAct 8 s16c11_v1_p456_eight} : Set (MulAut ↥(coreMod 8)))) ↔
      (G6.coreAct 8 s16c11_v1_p123_eight) v = v ∧
        (G6.coreAct 8 s16c11_v1_p456_eight) v = v :=
    s16c11_v1_mem_fixV_closure_pair _ _ v
  have h2 : (G6.coreAct 8 s16c11_v1_p123_eight) v = v ↔
      ∀ i, s16c11_v1_eightVecOf v ((s16c11_v1_p123_eight)⁻¹ i) =
        s16c11_v1_eightVecOf v i :=
    s16c11_v1_coreAct_eight_fixed_iff _ _
  have h3 : (G6.coreAct 8 s16c11_v1_p456_eight) v = v ↔
      ∀ i, s16c11_v1_eightVecOf v ((s16c11_v1_p456_eight)⁻¹ i) =
        s16c11_v1_eightVecOf v i :=
    s16c11_v1_coreAct_eight_fixed_iff _ _
  have h4 : (∀ i, s16c11_v1_eightVecOf v ((s16c11_v1_p123_eight)⁻¹ i) =
        s16c11_v1_eightVecOf v i) ↔
      ∀ i, s16c11_v1_eightVecOf v i = s16c11_v1_eightVecOf v (s16c11_v1_p123_eight i) :=
    s16c11_v1_forall_inv_apply_iff _ _
  have h5 : (∀ i, s16c11_v1_eightVecOf v ((s16c11_v1_p456_eight)⁻¹ i) =
        s16c11_v1_eightVecOf v i) ↔
      ∀ i, s16c11_v1_eightVecOf v i = s16c11_v1_eightVecOf v (s16c11_v1_p456_eight i) :=
    s16c11_v1_forall_inv_apply_iff _ _
  have h8 : (s16c11_v1_eightVecOf v 0 = s16c11_v1_eightVecOf v 1 ∧
        s16c11_v1_eightVecOf v 1 = s16c11_v1_eightVecOf v 2) ∧
      (s16c11_v1_eightVecOf v 3 = s16c11_v1_eightVecOf v 4 ∧
        s16c11_v1_eightVecOf v 4 = s16c11_v1_eightVecOf v 5) ↔
      s16c11_v1_eightConst (s16c11_v1_eightVecOf v) := by
    simp only [s16c11_v1_eightConst, and_assoc]
  exact (h1.trans (and_congr h2 h3)).trans
    ((and_congr h4 h5).trans ((and_congr (s16c11_v1_p123_fixed_iff _)
      (s16c11_v1_p456_fixed_iff _)).trans h8))

private theorem s16c11_v1_three (a : ZMod 2) : a + a + a = a := by revert a; decide

private theorem s16c11_v1_neg_two (a : ZMod 2) : -a = a := by revert a; decide

private theorem s16c11_v1_sum_eight (x : Fin 8 → ZMod 2) :
    ∑ i, x i = x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 := by
  simp [Fin.sum_univ_succ]
  abel

private theorem s16c11_v1_eight_seven (x : Fin 8 → ZMod 2)
    (hx : s16c11_v1_eightConst x) (hsum : ∑ i, x i = 0) :
    x 7 = x 0 + x 3 + x 6 := by
  obtain ⟨h01, h12, h34, h45⟩ := hx
  have hsum' : x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + x 6 + x 7 = 0 := by
    rw [← s16c11_v1_sum_eight x]; exact hsum
  have h1 : x 1 = x 0 := h01.symm
  have h2 : x 2 = x 1 := h12.symm
  have h4 : x 4 = x 3 := h34.symm
  have h5 : x 5 = x 4 := h45.symm
  rw [h1, h2, h4, h5, h1, h4] at hsum'
  have h3a : x 0 + x 0 + x 0 = x 0 := s16c11_v1_three (x 0)
  have h3b : x 3 + x 3 + x 3 = x 3 := s16c11_v1_three (x 3)
  have hkey : x 0 + x 3 + x 6 + x 7 = 0 := by
    linear_combination hsum' - h3a - h3b
  have hneg : x 0 + x 3 + x 6 = -x 7 := eq_neg_of_add_eq_zero_left hkey
  rw [s16c11_v1_neg_two] at hneg
  exact hneg.symm

private theorem s16c11_v1_eightConst_ext {x y : Fin 8 → ZMod 2}
    (hx : s16c11_v1_eightConst x) (hy : s16c11_v1_eightConst y)
    (hxs : ∑ i, x i = 0) (hys : ∑ i, y i = 0)
    (h0 : x 0 = y 0) (h3 : x 3 = y 3) (h6 : x 6 = y 6) : x = y := by
  have hx7 := s16c11_v1_eight_seven x hx hxs
  have hy7 := s16c11_v1_eight_seven y hy hys
  funext i
  fin_cases i
  · exact h0
  · show x 1 = y 1
    rw [← hx.1, h0, ← hy.1]
  · show x 2 = y 2
    rw [← hx.2.1, ← hx.1, h0, ← hy.2.1, ← hy.1]
  · exact h3
  · show x 4 = y 4
    rw [← hx.2.2.1, h3, ← hy.2.2.1]
  · show x 5 = y 5
    rw [← hx.2.2.2, ← hx.2.2.1, h3, ← hy.2.2.2, ← hy.2.2.1]
  · exact h6
  · show x 7 = y 7
    rw [hx7, h0, h3, h6, hy7]

private def s16c11_v1_eightOfTriple (y : Fin 3 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![y 0, y 0, y 0, y 1, y 1, y 1, y 2, y 0 + y 1 + y 2]

private theorem s16c11_v1_eightOfTriple_sum :
    ∀ y : Fin 3 → ZMod 2, ∑ i, s16c11_v1_eightOfTriple y i = 0 := by
  decide

private theorem s16c11_v1_eightOfTriple_const (y : Fin 3 → ZMod 2) :
    s16c11_v1_eightConst (s16c11_v1_eightOfTriple y) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [s16c11_v1_eightOfTriple, s16c11_v1_eightConst]

private def s16c11_v1_eightToTriple (v : ↥(fixV s16c11_v1_blocks_eight)) : Fin 3 → ZMod 2 :=
  ![s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 0,
    s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 3,
    s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 6]

private def s16c11_v1_eightOfFix (y : Fin 3 → ZMod 2) :
    ↥(fixV s16c11_v1_blocks_eight) :=
  ⟨⟨Multiplicative.ofAdd (s16c11_v1_eightOfTriple y),
      G6.mem_coreMod.2 (s16c11_v1_eightOfTriple_sum y)⟩,
    (s16c11_v1_mem_fixV_blocks_eight _).2 (s16c11_v1_eightOfTriple_const y)⟩

private theorem s16c11_v1_eightToTriple_injective :
    Function.Injective s16c11_v1_eightToTriple := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  have hv := (s16c11_v1_mem_fixV_blocks_eight (v : ↥(coreMod 8))).1 v.2
  have hw := (s16c11_v1_mem_fixV_blocks_eight (w : ↥(coreMod 8))).1 w.2
  have hsv : ∑ i, s16c11_v1_eightVecOf (v : ↥(coreMod 8)) i = 0 :=
    G6.mem_coreMod.mp (v : ↥(coreMod 8)).2
  have hsw : ∑ i, s16c11_v1_eightVecOf (w : ↥(coreMod 8)) i = 0 :=
    G6.mem_coreMod.mp (w : ↥(coreMod 8)).2
  have h0 : s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 0 =
      s16c11_v1_eightVecOf (w : ↥(coreMod 8)) 0 := by
    have := congrFun h 0
    simpa [s16c11_v1_eightToTriple] using this
  have h3 : s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 3 =
      s16c11_v1_eightVecOf (w : ↥(coreMod 8)) 3 := by
    have := congrFun h 1
    simpa [s16c11_v1_eightToTriple] using this
  have h6 : s16c11_v1_eightVecOf (v : ↥(coreMod 8)) 6 =
      s16c11_v1_eightVecOf (w : ↥(coreMod 8)) 6 := by
    have := congrFun h 2
    simpa [s16c11_v1_eightToTriple] using this
  exact s16c11_v1_eightConst_ext hv hw hsv hsw h0 h3 h6

private theorem s16c11_v1_eightToTriple_surjective :
    Function.Surjective s16c11_v1_eightToTriple := by
  intro y
  refine ⟨s16c11_v1_eightOfFix y, ?_⟩
  funext i
  fin_cases i <;>
    simp [s16c11_v1_eightToTriple, s16c11_v1_eightOfFix, s16c11_v1_eightVecOf,
      s16c11_v1_eightOfTriple]

theorem s16c11_v1_blocks_eight_fixV :
    Nat.card ↥(fixV s16c11_v1_blocks_eight) = 2 ^ 3 := by
  have hbij : Function.Bijective s16c11_v1_eightToTriple :=
    ⟨s16c11_v1_eightToTriple_injective, s16c11_v1_eightToTriple_surjective⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem s16c11_v1_commute_p123_p456 :
    Commute s16c11_v1_p123_eight s16c11_v1_p456_eight := by
  refine Equiv.Perm.Disjoint.commute ?_
  intro x
  fin_cases x <;> decide

private theorem s16c11_v1_p123_pow_three : s16c11_v1_p123_eight ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private theorem s16c11_v1_p456_pow_three : s16c11_v1_p456_eight ^ 3 = 1 := by
  ext i
  fin_cases i <;> decide

private theorem s16c11_v1_p123_mem_alternating :
    s16c11_v1_p123_eight ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, s16c11_v1_p123_eight, map_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 8) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 8) ≠ 2)]
  simp

private theorem s16c11_v1_p456_mem_alternating :
    s16c11_v1_p456_eight ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, s16c11_v1_p456_eight, map_mul,
    Equiv.Perm.sign_swap (by decide : (3 : Fin 8) ≠ 4),
    Equiv.Perm.sign_swap (by decide : (4 : Fin 8) ≠ 5)]
  simp

private def s16c11_v1_vec06_eight : ↥(coreMod 8) :=
  ⟨G64.pairVec (0 : Fin 8) 6, G64.pairVec_mem_coreMod 0 6⟩

private def s16c11_v1_vec36_eight : ↥(coreMod 8) :=
  ⟨G64.pairVec (3 : Fin 8) 6, G64.pairVec_mem_coreMod 3 6⟩

private theorem s16c11_v1_coreAct_p456_vec06 :
    G6.coreAct 8 s16c11_v1_p456_eight s16c11_v1_vec06_eight = s16c11_v1_vec06_eight := by
  apply Subtype.ext
  change G6.permAct 8 s16c11_v1_p456_eight (G64.pairVec (0 : Fin 8) 6) = G64.pairVec 0 6
  rw [G64.permAct_pairVec]
  congr 1 <;> decide

private theorem s16c11_v1_coreAct_p123_vec06_ne :
    G6.coreAct 8 s16c11_v1_p123_eight s16c11_v1_vec06_eight ≠ s16c11_v1_vec06_eight := by
  intro h
  have h2 := congrArg (fun v : ↥(coreMod 8) =>
    Multiplicative.toAdd (v : G6.PermMod 8) 0) h
  have h3 : Multiplicative.toAdd
      (G6.coreAct 8 s16c11_v1_p123_eight s16c11_v1_vec06_eight : G6.PermMod 8) 0 = 0 := by
    simp only [s16c11_v1_vec06_eight, G6.coreAct_coe, G6.permAct_apply,
      G64.toAdd_pairVec_apply, s16c11_v1_p123_eight]
    decide
  have h4 : Multiplicative.toAdd (s16c11_v1_vec06_eight : G6.PermMod 8) 0 = 1 := by
    simp only [s16c11_v1_vec06_eight, G64.toAdd_pairVec_apply]
    decide
  rw [h3, h4] at h2
  exact zero_ne_one h2

private theorem s16c11_v1_coreAct_p456_vec36_ne :
    G6.coreAct 8 s16c11_v1_p456_eight s16c11_v1_vec36_eight ≠ s16c11_v1_vec36_eight := by
  intro h
  have h2 := congrArg (fun v : ↥(coreMod 8) =>
    Multiplicative.toAdd (v : G6.PermMod 8) 3) h
  have h3 : Multiplicative.toAdd
      (G6.coreAct 8 s16c11_v1_p456_eight s16c11_v1_vec36_eight : G6.PermMod 8) 3 = 0 := by
    simp only [s16c11_v1_vec36_eight, G6.coreAct_coe, G6.permAct_apply,
      G64.toAdd_pairVec_apply, s16c11_v1_p456_eight]
    decide
  have h4 : Multiplicative.toAdd (s16c11_v1_vec36_eight : G6.PermMod 8) 3 = 1 := by
    simp only [s16c11_v1_vec36_eight, G64.toAdd_pairVec_apply]
    decide
  rw [h3, h4] at h2
  exact zero_ne_one h2

private theorem s16c11_v1_coreAct_p123_ne_one :
    G6.coreAct 8 s16c11_v1_p123_eight ≠ 1 := by
  intro h
  exact s16c11_v1_coreAct_p123_vec06_ne (by rw [h]; rfl)

private theorem s16c11_v1_coreAct_p456_ne_one :
    G6.coreAct 8 s16c11_v1_p456_eight ≠ 1 := by
  intro h
  exact s16c11_v1_coreAct_p456_vec36_ne (by rw [h]; rfl)

private theorem s16c11_v1_zpowers_coreAct_p123_ne_p456 :
    Subgroup.zpowers (G6.coreAct 8 s16c11_v1_p123_eight) ≠
      Subgroup.zpowers (G6.coreAct 8 s16c11_v1_p456_eight) := by
  intro heq
  have hmem : G6.coreAct 8 s16c11_v1_p123_eight ∈
      Subgroup.zpowers (G6.coreAct 8 s16c11_v1_p456_eight) :=
    heq ▸ Subgroup.mem_zpowers _
  let K : Subgroup (MulAut ↥(coreMod 8)) :=
    { carrier := {f | f s16c11_v1_vec06_eight = s16c11_v1_vec06_eight}
      one_mem' := rfl
      mul_mem' := fun {f g} hf hg => by
        show (f * g) s16c11_v1_vec06_eight = s16c11_v1_vec06_eight
        rw [MulAut.mul_apply, hg, hf]
      inv_mem' := fun {f} hf => by
        show f⁻¹ s16c11_v1_vec06_eight = s16c11_v1_vec06_eight
        rw [MulAut.inv_apply]
        exact (MulEquiv.symm_apply_eq f).2 hf.symm }
  have hbK : G6.coreAct 8 s16c11_v1_p456_eight ∈ K := s16c11_v1_coreAct_p456_vec06
  exact s16c11_v1_coreAct_p123_vec06_ne ((Subgroup.zpowers_le.2 hbK) hmem)

private theorem s16c11_v1_blocks_eight_pow_three (e : MulAut ↥(coreMod 8))
    (he : e ∈ s16c11_v1_blocks_eight) : e ^ 3 = 1 := by
  rw [s16c11_v1_blocks_eight] at he
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp he
  have hC := C58.G64D.closure_pair_core (x := s16c11_v1_p123_eight)
    (y := s16c11_v1_p456_eight) s16c11_v1_commute_p123_p456
    s16c11_v1_p123_pow_three s16c11_v1_p456_pow_three
  rw [← map_pow, hC.2 c hc, map_one]

private theorem s16c11_v1_blocks_eight_isPGroup :
    IsPGroup 3 ↥s16c11_v1_blocks_eight := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using s16c11_v1_blocks_eight_pow_three g.1 g.2)⟩

private theorem s16c11_v1_blocks_eight_not_isCyclic :
    ¬ IsCyclic ↥s16c11_v1_blocks_eight := by
  have hga : G6.coreAct 8 s16c11_v1_p123_eight ∈ s16c11_v1_blocks_eight :=
    Subgroup.mem_map.mpr ⟨s16c11_v1_p123_eight, Subgroup.subset_closure (by simp), rfl⟩
  have hgb : G6.coreAct 8 s16c11_v1_p456_eight ∈ s16c11_v1_blocks_eight :=
    Subgroup.mem_map.mpr ⟨s16c11_v1_p456_eight, Subgroup.subset_closure (by simp), rfl⟩
  refine C58.G64D.not_isCyclic_core s16c11_v1_blocks_eight_pow_three hga hgb ?_ ?_ ?_ ?_ ?_
  · exact s16c11_v1_blocks_eight_pow_three _ hga
  · exact s16c11_v1_coreAct_p123_ne_one
  · exact s16c11_v1_blocks_eight_pow_three _ hgb
  · exact s16c11_v1_coreAct_p456_ne_one
  · exact s16c11_v1_zpowers_coreAct_p123_ne_p456

theorem s16c11_v1_blocks_eight_of_realizes {J : Type} [CommGroup J] [Finite J]
    (hJ : ∀ j : J, j ^ 2 = 1) {H : Subgroup (MulAut J)}
    (hReal : (altCoreModel 8).Realizes H ⊤ ⊥) :
    ∃ E : Subgroup (MulAut J), E ≤ H ∧ IsPGroup 3 ↥E ∧ ¬ IsCyclic ↥E ∧
      Nat.card ↥(fixV E) = 2 ^ 3 := by
  obtain ⟨π, hπ⟩ := hReal
  obtain ⟨φ, hφ⟩ := G64.RealizesVia.exists_secEquiv (D := altCoreModel 8) rfl hπ
  let π' : ↥(alternatingGroup (Fin 8)) →* ↥H := π
  let φ' : J ≃* ↥(coreMod 8) := φ
  have hφ' : ∀ (γ : ↥(alternatingGroup (Fin 8))) (v : J),
      ((φ' (((π' γ : ↥H) : MulAut J) v) : ↥(coreMod 8)) : G6.PermMod 8) =
        G6.permAct 8 (γ : Equiv.Perm (Fin 8))
          ((φ' v : ↥(coreMod 8)) : G6.PermMod 8) := by
    intro γ v
    exact hφ γ v
  have hcore : ∀ γ : ↥(alternatingGroup (Fin 8)),
      MulAut.congr φ' (π' γ) = G6.coreAct 8 (γ : Equiv.Perm (Fin 8)) := by
    intro γ
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    have h := hφ' γ (φ'.symm w)
    simpa [G6.coreAct_coe] using h
  have hcore' : ∀ γ : ↥(alternatingGroup (Fin 8)),
      MulAut.congr φ'.symm (G6.coreAct 8 (γ : Equiv.Perm (Fin 8))) = π' γ := by
    intro γ
    apply MulEquiv.ext
    intro w
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
    apply φ'.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (hφ' γ w).symm
  let E : Subgroup (MulAut J) :=
    s16c11_v1_blocks_eight.map (MulAut.congr φ'.symm).toMonoidHom
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · have hpre : s16c11_v1_blocks_eight ≤ H.comap (MulAut.congr φ'.symm).toMonoidHom := by
      rw [s16c11_v1_blocks_eight_eq]
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · show MulAut.congr φ'.symm (G6.coreAct 8 s16c11_v1_p123_eight) ∈ H
        rw [hcore' ⟨s16c11_v1_p123_eight, s16c11_v1_p123_mem_alternating⟩]
        exact (π' ⟨s16c11_v1_p123_eight, s16c11_v1_p123_mem_alternating⟩).2
      · show MulAut.congr φ'.symm (G6.coreAct 8 s16c11_v1_p456_eight) ∈ H
        rw [hcore' ⟨s16c11_v1_p456_eight, s16c11_v1_p456_mem_alternating⟩]
        exact (π' ⟨s16c11_v1_p456_eight, s16c11_v1_p456_mem_alternating⟩).2
    exact Subgroup.map_le_iff_le_comap.2 hpre
  · exact IsPGroup.map s16c11_v1_blocks_eight_isPGroup (MulAut.congr φ'.symm).toMonoidHom
  · intro hc
    have he : s16c11_v1_blocks_eight ≃* E :=
      Subgroup.equivMapOfInjective s16c11_v1_blocks_eight (MulAut.congr φ'.symm).toMonoidHom
        (MulEquiv.injective _)
    exact s16c11_v1_blocks_eight_not_isCyclic (he.isCyclic.mpr hc)
  · have hfix : fixV E = (fixV s16c11_v1_blocks_eight).map φ'.symm.toMonoidHom := by
      change fixV (s16c11_v1_blocks_eight.map (MulAut.congr φ'.symm).toMonoidHom) = _
      exact E3.fixV_map_congr φ'.symm s16c11_v1_blocks_eight
    rw [hfix]
    have hcard := Subgroup.card_map_of_injective
      (K := fixV s16c11_v1_blocks_eight) (f := φ'.symm.toMonoidHom) φ'.symm.injective
    exact hcard.trans s16c11_v1_blocks_eight_fixV

private theorem s16c11_v1_coreAct_eight_injective :
    Function.Injective (G6.coreAct 8) := by
  rw [injective_iff_map_eq_one]
  intro σ h
  refine G64.symCore_faithful (by norm_num : 3 ≤ 8) σ fun m hm => ?_
  have h2 : (G6.coreAct 8 σ) ⟨m, hm⟩ = ⟨m, hm⟩ := by rw [h]; rfl
  have h3 : G6.permAct 8 σ m = m := congrArg Subtype.val h2
  exact Subgroup.mem_bot.2 (mul_inv_eq_one.2 h3)

private theorem s16c11_v1_eight_exists_index_two {A : Type*} [Group A] [Finite A]
    (hA : ∀ a b : A, a * b = b * a) (h2 : ∀ a : A, a ^ 2 = 1) {t : A} (ht : t ≠ 1) :
    ∃ B : Subgroup A, B.index = 2 ∧ t ∉ B := by
  classical
  have hnormal : ∀ S : Subgroup A, S.Normal := fun S =>
    ⟨fun n hn g => by rw [hA g n, mul_inv_cancel_right]; exact hn⟩
  have hcard2 : ∀ a : A, a ≠ 1 → Nat.card (Subgroup.zpowers a) = 2 := fun a ha => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h2 a) ha
  have hsmall : ∀ a : A, a ≠ 1 → ∀ S : Subgroup A, a ∉ S → Subgroup.zpowers a ⊓ S = ⊥ := by
    intro a ha S haS
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ S : Subgroup A) ∣ 2 :=
      hcard2 a ha ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers a ⊓ S = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard2 a ha])
      exact haS ((heq ▸ (inf_le_right : Subgroup.zpowers a ⊓ S ≤ S))
        (heq.symm ▸ Subgroup.mem_zpowers a))
  obtain ⟨B, htB, hBmax⟩ := Set.exists_max_image {B : Subgroup A | t ∉ B} (fun B => Nat.card B)
    (Set.toFinite _) ⟨⊥, fun h => ht (Subgroup.mem_bot.mp h)⟩
  refine ⟨B, ?_, htB⟩
  have hC : B ⊔ Subgroup.zpowers t = ⊤ := by
    by_contra hC
    obtain ⟨a, haC⟩ : ∃ a, a ∉ B ⊔ Subgroup.zpowers t := by
      by_contra h
      push Not at h
      exact hC (eq_top_iff.mpr fun x _ => h x)
    have ha1 : a ≠ 1 := fun h => haC (h ▸ one_mem _)
    have haB : a ∉ B := fun h => haC ((le_sup_left : B ≤ B ⊔ Subgroup.zpowers t) h)
    have htB'' : t ∉ B ⊔ Subgroup.zpowers a := by
      intro hmem
      have := hnormal (Subgroup.zpowers a)
      obtain ⟨b, hb, y, hy, hby⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
      have hyC : y ∈ B ⊔ Subgroup.zpowers t := by
        have : y = b⁻¹ * t := by rw [← hby]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hb))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      have hy1 : y = 1 := by
        have h1 : y ∈ Subgroup.zpowers a ⊓ (B ⊔ Subgroup.zpowers t) := ⟨hy, hyC⟩
        rwa [hsmall a ha1 _ haC, Subgroup.mem_bot] at h1
      apply htB
      rw [← hby, hy1, mul_one]
      exact hb
    have hlt : B < B ⊔ Subgroup.zpowers a :=
      lt_of_le_of_ne le_sup_left fun h => haB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have := hBmax _ htB''
    exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.mpr this)
  have hdisj : Disjoint B (Subgroup.zpowers t) := by
    rw [disjoint_iff, inf_comm]
    exact hsmall t ht B htB
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B
    (Subgroup.zpowers t) (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr (hnormal B)).ge) hdisj
  rw [hC, Subgroup.card_top, hcard2 t ht] at hcard
  have h := B.card_mul_index
  rw [hcard] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

private theorem s16c11_v1_eight_exists_moved (P : Subgroup (Equiv.Perm (Fin 8)))
    (hPne : P ≠ ⊥) : ∃ a : Fin 8, ∃ g ∈ P, g a ≠ a := by
  obtain ⟨g, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hg1' : (g : Equiv.Perm (Fin 8)) ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hmove : ∃ a : Fin 8, (g : Equiv.Perm (Fin 8)) a ≠ a := by
    by_contra h
    exact hg1' (Equiv.ext fun a => not_not.mp (not_exists.mp h a))
  obtain ⟨a, ha⟩ := hmove
  exact ⟨a, (g : Equiv.Perm (Fin 8)), g.2, ha⟩

private theorem s16c11_v1_eight_relIndex_map (P : Subgroup (Equiv.Perm (Fin 8)))
    (H : Subgroup ↥P) : (H.map P.subtype).relIndex P = H.index := by
  have h := Subgroup.relIndex_map_map_of_injective (f := P.subtype) H ⊤ P.subtype_injective
  simpa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] using h

private theorem s16c11_v1_eight_isPGroup_sub {A : Type*} [Group A] {p : ℕ} (h : IsPGroup p A)
    (B : Subgroup A) : IsPGroup p B := fun x => by
  obtain ⟨k, hk⟩ := h (x : A)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

private theorem s16c11_v1_eight_orbit_invariant {P : Subgroup (Equiv.Perm (Fin 8))}
    (H : Subgroup ↥P) (b : Fin 8) :
    ∀ σ ∈ H.map P.subtype, σ '' MulAction.orbit H b = MulAction.orbit H b := by
  intro σ hσ
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hσ
  refine Set.eq_of_subset_of_ncard_le ?_ ?_
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨q', hq'⟩ := MulAction.mem_orbit_iff.mp hz
    refine MulAction.mem_orbit_iff.mpr ⟨⟨q * q', H.mul_mem hq q'.2⟩, ?_⟩
    rw [← hq']
    simp [Subgroup.smul_def, Equiv.Perm.smul_def]
  · rw [Set.ncard_image_of_injective _ (P.subtype q).injective]

private noncomputable def s16c11_v1_eightInd (X : Set (Fin 8)) (hX : Even X.ncard) :
    ↥(coreMod 8) := by
  classical
  exact
    ⟨Multiplicative.ofAdd fun i => if i ∈ X then (1 : ZMod 2) else 0,
      G6.mem_coreMod.2 (by
        have hsum : ∑ i : Fin 8, (if i ∈ X then (1 : ZMod 2) else 0) = (X.ncard : ZMod 2) := by
          rw [Finset.sum_boole]
          congr 1
          rw [Set.ncard_eq_toFinset_card']
          congr 1
          ext i
          simp
        have hcast : ((X.ncard : ℕ) : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr hX
        change (∑ i : Fin 8, (if i ∈ X then (1 : ZMod 2) else 0)) = 0
        rw [hsum, hcast])⟩

private theorem s16c11_v1_zmod_two_eq_iff (a b : ZMod 2) : (a = 1 ↔ b = 1) ↔ a = b := by
  revert a b
  decide

private theorem s16c11_v1_eightInd_coreAct_iff (σ : Equiv.Perm (Fin 8)) (X : Set (Fin 8))
    (hX : Even X.ncard) :
    G6.coreAct 8 σ (s16c11_v1_eightInd X hX) = s16c11_v1_eightInd X hX ↔ σ '' X = X := by
  rw [s16c11_v1_coreAct_eight_fixed_iff]
  have hmem : ∀ i : Fin 8,
      (Multiplicative.toAdd ((s16c11_v1_eightInd X hX : ↥(coreMod 8)) : G6.PermMod 8) i = 1 ↔
        i ∈ X) := by
    intro i
    simp [s16c11_v1_eightInd]
  have h1 : ∀ i : Fin 8,
      (Multiplicative.toAdd ((s16c11_v1_eightInd X hX : ↥(coreMod 8)) : G6.PermMod 8) (σ⁻¹ i) =
        Multiplicative.toAdd ((s16c11_v1_eightInd X hX : ↥(coreMod 8)) : G6.PermMod 8) i) ↔
      (σ⁻¹ i ∈ X ↔ i ∈ X) := by
    intro i
    rw [← s16c11_v1_zmod_two_eq_iff]
    exact iff_congr (hmem (σ⁻¹ i)) (hmem i)
  have h2 : (∀ i : Fin 8,
      Multiplicative.toAdd ((s16c11_v1_eightInd X hX : ↥(coreMod 8)) : G6.PermMod 8) (σ⁻¹ i) =
        Multiplicative.toAdd ((s16c11_v1_eightInd X hX : ↥(coreMod 8)) : G6.PermMod 8) i) ↔
      ∀ i : Fin 8, (σ⁻¹ i ∈ X ↔ i ∈ X) :=
    ⟨fun h i => (h1 i).mp (h i), fun h i => (h1 i).mpr (h i)⟩
  have h3 : (∀ i : Fin 8, (σ⁻¹ i ∈ X ↔ i ∈ X)) ↔ σ '' X = X := by
    constructor
    · intro h
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (h (σ x)).mp (by simpa using hx)
      · intro hy
        exact ⟨σ⁻¹ y, (h y).mpr hy, by simp⟩
    · intro h i
      constructor
      · intro hi
        have hmem : σ (σ⁻¹ i) ∈ σ '' X := ⟨σ⁻¹ i, hi, rfl⟩
        rw [h] at hmem
        simpa using hmem
      · intro hi
        have hmem : i ∈ σ '' X := by rw [h]; exact hi
        obtain ⟨x, hx, hxeq⟩ := hmem
        have hx' : x = σ⁻¹ i := by rw [← hxeq]; simp
        rwa [hx'] at hx
  exact h2.trans h3

private theorem s16c11_v1_eightInd_fixed_iff (Q : Subgroup (Equiv.Perm (Fin 8)))
    (X : Set (Fin 8)) (hX : Even X.ncard) :
    s16c11_v1_eightInd X hX ∈ fixV (Q.map (G6.coreAct 8)) ↔
      ∀ σ ∈ Q, σ '' X = X := by
  rw [mem_fixV]
  constructor
  · intro h σ hσ
    exact (s16c11_v1_eightInd_coreAct_iff σ X hX).mp
      (h (G6.coreAct 8 σ) (Subgroup.mem_map.mpr ⟨σ, hσ, rfl⟩))
  · intro h x hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hx
    exact (s16c11_v1_eightInd_coreAct_iff σ X hX).mpr (h σ hσ)

private theorem s16c11_v1_eight_index_two_of_moved (P : Subgroup (Equiv.Perm (Fin 8)))
    (hPexp : ∀ g ∈ P, g * g = 1) {a : Fin 8}
    (hmoved : ∃ g ∈ P, g a ≠ a) :
    ∃ Q' : Subgroup ↥P, (MulAction.stabilizer ↥P a) ≤ Q' ∧ Q'.index = 2 := by
  classical
  have hcomm : ∀ x y : ↥P, x * y = y * x := by
    intro x y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hx : (x : Equiv.Perm (Fin 8)) * x = 1 := hPexp x x.2
    have hy : (y : Equiv.Perm (Fin 8)) * y = 1 := hPexp y y.2
    have hxy : ((x : Equiv.Perm (Fin 8)) * y) * ((x : Equiv.Perm (Fin 8)) * y) = 1 :=
      hPexp ((x : Equiv.Perm (Fin 8)) * y) (by simpa using P.mul_mem x.2 y.2)
    calc (x : Equiv.Perm (Fin 8)) * y
        = ((x : Equiv.Perm (Fin 8)) * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = (y : Equiv.Perm (Fin 8))⁻¹ * (x : Equiv.Perm (Fin 8))⁻¹ := mul_inv_rev _ _
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx]
  haveI : IsMulCommutative ↥P := IsMulCommutative.of_comm hcomm
  let Ep : Subgroup ↥P := MulAction.stabilizer ↥P a
  obtain ⟨g₀, hg₀P, hg₀a⟩ := hmoved
  have hg₀Ep : (⟨g₀, hg₀P⟩ : ↥P) ∉ Ep := fun h =>
    hg₀a (MulAction.mem_stabilizer_iff.mp h)
  have hcommQ : ∀ x y : ↥P ⧸ Ep, x * y = y * x := by
    intro x y
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective Ep x
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective Ep y
    rw [← map_mul, ← map_mul, hcomm x' y']
  have h2Q : ∀ x : ↥P ⧸ Ep, x ^ 2 = 1 := by
    intro x
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective Ep x
    have hx' : x' ^ 2 = 1 := Subtype.ext (by
      simpa [sq] using hPexp (x' : Equiv.Perm (Fin 8)) x'.2)
    simpa using congrArg (QuotientGroup.mk' Ep) hx'
  have ht : (QuotientGroup.mk' Ep ⟨g₀, hg₀P⟩ : ↥P ⧸ Ep) ≠ 1 := fun h =>
    hg₀Ep ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨Bq, hBqindex, _⟩ := s16c11_v1_eight_exists_index_two hcommQ h2Q ht
  let Q' : Subgroup ↥P := Bq.comap (QuotientGroup.mk' Ep)
  have hQ'index : Q'.index = 2 := by
    change (Bq.comap (QuotientGroup.mk' Ep)).index = 2
    rw [Subgroup.index_comap_of_surjective (H := Bq) (QuotientGroup.mk'_surjective Ep), hBqindex]
  have hEpQ' : Ep ≤ Q' := by
    intro x hx
    change (x : ↥P ⧸ Ep) ∈ Bq
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact Bq.one_mem
  exact ⟨Q', hEpQ', hQ'index⟩

private theorem s16c11_v1_eight_no_fixed (P : Subgroup (Equiv.Perm (Fin 8)))
    (hPexp : ∀ g ∈ P, g * g = 1) (hPne : P ≠ ⊥)
    (haSet : ∀ Q : Subgroup (Equiv.Perm (Fin 8)), Q ≤ P → Q.relIndex P = 2 →
      fixV (Q.map (G6.coreAct 8)) = fixV (P.map (G6.coreAct 8)))
    (k : Fin 8) (hk : ∀ g ∈ P, g k = k) : False := by
  classical
  obtain ⟨a, g₀, hg₀P, hg₀a⟩ := s16c11_v1_eight_exists_moved P hPne
  have hPp : IsPGroup 2 ↥P := fun x => ⟨1, by
    have h : (x : Equiv.Perm (Fin 8)) ^ 2 = 1 := hPexp x x.2
    simpa using (Subtype.ext (by simpa using h) : (x ^ 2 : ↥P) = 1)⟩
  obtain ⟨Q', hEpQ', hQ'index⟩ :=
    s16c11_v1_eight_index_two_of_moved P hPexp ⟨g₀, hg₀P, hg₀a⟩
  let Q : Subgroup (Equiv.Perm (Fin 8)) := Q'.map P.subtype
  have hQle : Q ≤ P := Subgroup.map_subtype_le Q'
  have hQrel : Q.relIndex P = 2 := by
    change (Q'.map P.subtype).relIndex P = 2
    rw [s16c11_v1_eight_relIndex_map, hQ'index]
  have hak : a ≠ k := fun h => hg₀a (by rw [h]; exact hk g₀ hg₀P)
  have hQ'apow : ∃ m : ℕ, (MulAction.orbit Q' a).ncard = 2 ^ m := by
    obtain ⟨m, hm⟩ := (s16c11_v1_eight_isPGroup_sub hPp Q').card_orbit a
    exact ⟨m, by rw [← Nat.card_coe_set_eq]; exact hm⟩
  obtain ⟨m, hm⟩ := hQ'apow
  by_cases hm0 : m = 0
  ·
    have hXq1 : (MulAction.orbit Q' a).ncard = 1 := by rw [hm, hm0, pow_zero]
    obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp hXq1
    have hba : a = b := by
      have : a ∈ MulAction.orbit Q' a := MulAction.mem_orbit_self a
      rw [hb] at this; exact this
    have horbit : MulAction.orbit Q' a = {a} := by rw [hb, ← hba]
    have hQfixa : ∀ σ ∈ Q, σ a = a := by
      intro σ hσ
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hσ
      have hqa : (⟨q, hq⟩ : ↥Q') • a = a := by
        have hmem : (⟨q, hq⟩ : ↥Q') • a ∈ MulAction.orbit Q' a :=
          MulAction.mem_orbit_iff.mpr ⟨⟨q, hq⟩, rfl⟩
        rw [horbit] at hmem; exact hmem
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hqa
    have hXeven : Even ({a, k} : Set (Fin 8)).ncard := by
      rw [Set.ncard_pair hak]; exact even_two
    have hQinv : ∀ σ ∈ Q, σ '' ({a, k} : Set (Fin 8)) = {a, k} := by
      intro σ hσ
      have hσa : σ a = a := hQfixa σ hσ
      have hσk : σ k = k := hk σ (hQle hσ)
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with hz | hz
        · left; rw [hz]; exact hσa
        · right; rw [hz]; exact hσk
      · rintro (hy | hy)
        · exact ⟨a, Or.inl rfl, by rw [hy]; exact hσa⟩
        · exact ⟨k, Or.inr rfl, by rw [hy]; exact hσk⟩
    have hPinv : ∀ σ ∈ P, σ '' ({a, k} : Set (Fin 8)) = {a, k} := by
      have hvQ : s16c11_v1_eightInd ({a, k} : Set (Fin 8)) hXeven ∈
          fixV (Q.map (G6.coreAct 8)) :=
        (s16c11_v1_eightInd_fixed_iff Q _ hXeven).mpr hQinv
      have hvP : s16c11_v1_eightInd ({a, k} : Set (Fin 8)) hXeven ∈
          fixV (P.map (G6.coreAct 8)) := by
        rw [← haSet Q hQle hQrel]; exact hvQ
      exact (s16c11_v1_eightInd_fixed_iff P _ hXeven).mp hvP
    have him : g₀ '' ({a, k} : Set (Fin 8)) = {a, k} := hPinv g₀ hg₀P
    have hmem : g₀ a ∈ ({a, k} : Set (Fin 8)) := by
      rw [← him]; exact ⟨a, Or.inl rfl, rfl⟩
    rcases (by simpa using hmem : g₀ a = a ∨ g₀ a = k) with h | h
    · exact hg₀a h
    · exact hak (g₀.injective (h.trans (hk g₀ hg₀P).symm))
  ·
    have heven : Even (MulAction.orbit Q' a).ncard := by
      rw [hm]
      exact Nat.even_pow.mpr ⟨even_two, hm0⟩
    have hQinv : ∀ σ ∈ Q, σ '' MulAction.orbit Q' a = MulAction.orbit Q' a := by
      intro σ hσ
      exact s16c11_v1_eight_orbit_invariant Q' a σ hσ
    have hPinv : ∀ σ ∈ P, σ '' MulAction.orbit Q' a = MulAction.orbit Q' a := by
      have hvQ : s16c11_v1_eightInd (MulAction.orbit Q' a) heven ∈
          fixV (Q.map (G6.coreAct 8)) :=
        (s16c11_v1_eightInd_fixed_iff Q _ heven).mpr hQinv
      have hvP : s16c11_v1_eightInd (MulAction.orbit Q' a) heven ∈
          fixV (P.map (G6.coreAct 8)) := by
        rw [← haSet Q hQle hQrel]; exact hvQ
      exact (s16c11_v1_eightInd_fixed_iff P _ heven).mp hvP
    have hOsub : MulAction.orbit ↥P a ⊆ MulAction.orbit Q' a := by
      rintro y ⟨σ, rfl⟩
      have hmem : (σ : Equiv.Perm (Fin 8)) a ∈
          (σ : Equiv.Perm (Fin 8)) '' MulAction.orbit Q' a :=
        ⟨a, MulAction.mem_orbit_self a, rfl⟩
      rw [hPinv (σ : Equiv.Perm (Fin 8)) σ.2] at hmem
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hmem
    have hXqsub : MulAction.orbit Q' a ⊆ MulAction.orbit ↥P a := by
      rintro y ⟨q, rfl⟩
      exact MulAction.mem_orbit_iff.mpr
        ⟨(q : ↥P), by simp [Subgroup.smul_def, Equiv.Perm.smul_def]⟩
    have heqO : MulAction.orbit Q' a = MulAction.orbit ↥P a := le_antisymm hXqsub hOsub
    have hEpQrel : (MulAction.stabilizer ↥P a).relIndex Q' = (MulAction.orbit Q' a).ncard := by
      have hstab : (MulAction.stabilizer ↥P a).subgroupOf Q' = MulAction.stabilizer Q' a := by
        ext q
        simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
        simp [Subgroup.smul_def]
      rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer]
    have hcard_rel : (MulAction.orbit Q' a).ncard * 2 = (MulAction.orbit ↥P a).ncard := by
      have h := Subgroup.relIndex_mul_index (H := MulAction.stabilizer ↥P a) (K := Q') hEpQ'
      rw [hEpQrel, MulAction.index_stabilizer, hQ'index] at h
      exact h
    have hcardeq : (MulAction.orbit Q' a).ncard = (MulAction.orbit ↥P a).ncard := by rw [heqO]
    have hpos : 0 < (MulAction.orbit Q' a).ncard := by
      rw [Set.ncard_pos]
      exact ⟨a, MulAction.mem_orbit_self a⟩
    omega

theorem s16c11_v1_eight_fixV_bound (P : Subgroup (Equiv.Perm (Fin 8)))
    (hPexp : ∀ g ∈ P, g * g = 1) (hPne : P ≠ ⊥)
    (haSet : ∀ Q : Subgroup (Equiv.Perm (Fin 8)), Q ≤ P → Q.relIndex P = 2 →
      fixV (Q.map (G6.coreAct 8)) = fixV (P.map (G6.coreAct 8))) :
    Nat.card ↥(fixV (P.map (G6.coreAct 8))) ≤ 2 ^ 4 := by
  classical
  have hno_fixed : ∀ k : Fin 8, ∃ g ∈ P, g k ≠ k := by
    intro k
    by_contra h
    exact s16c11_v1_eight_no_fixed P hPexp hPne haSet k (fun g hg => by
      by_contra hne
      exact h ⟨g, hg, hne⟩)
  let coord : ↥(fixV (P.map (G6.coreAct 8))) → Fin 8 → ZMod 2 :=
    fun v i => Multiplicative.toAdd ((v : ↥(coreMod 8)) : G6.PermMod 8) i
  have coord_const : ∀ (v : ↥(fixV (P.map (G6.coreAct 8)))) (g : ↥P) (i : Fin 8),
      coord v (g • i) = coord v i := by
    intro v g i
    have hfix : G6.coreAct 8 (g : Equiv.Perm (Fin 8)) (v : ↥(coreMod 8)) =
        (v : ↥(coreMod 8)) :=
      (mem_fixV.mp v.2) _ (Subgroup.mem_map.mpr ⟨(g : Equiv.Perm (Fin 8)), g.2, rfl⟩)
    have h := (s16c11_v1_coreAct_eight_fixed_iff (g : Equiv.Perm (Fin 8))
      (v : ↥(coreMod 8))).mp hfix ((g : Equiv.Perm (Fin 8)) i)
    simpa [coord, Subgroup.smul_def, Equiv.Perm.smul_def] using h.symm
  let f : ↥(fixV (P.map (G6.coreAct 8))) →
      (MulAction.orbitRel.Quotient P (Fin 8) → ZMod 2) :=
    fun v => Quotient.lift (coord v) (fun i j hij => by
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hij)
      rw [← hg]
      exact coord_const v g j)
  have f_inj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    have := congrFun h (Quotient.mk'' i)
    simpa [f, coord, Quotient.lift_mk] using this
  have hcard_le : Nat.card ↥(fixV (P.map (G6.coreAct 8))) ≤
      Nat.card (MulAction.orbitRel.Quotient P (Fin 8) → ZMod 2) :=
    Nat.card_le_card_of_injective f f_inj
  have hfun : Nat.card (MulAction.orbitRel.Quotient P (Fin 8) → ZMod 2) =
      2 ^ Nat.card (MulAction.orbitRel.Quotient P (Fin 8)) := by
    rw [Nat.card_fun, Nat.card_zmod]
  have horbit_le : Nat.card (MulAction.orbitRel.Quotient P (Fin 8)) ≤ 4 := by
    haveI : Fintype (MulAction.orbitRel.Quotient P (Fin 8)) := Fintype.ofFinite _
    have hsum : Nat.card (Fin 8) =
        ∑ ω : MulAction.orbitRel.Quotient P (Fin 8), Nat.card ω.orbit := by
      rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' P (Fin 8)), Nat.card_sigma]
    have hge : ∀ ω : MulAction.orbitRel.Quotient P (Fin 8), 2 ≤ Nat.card ω.orbit := by
      intro ω
      obtain ⟨g, hgP, hgk⟩ := hno_fixed ω.out
      have h1 : ω.out ∈ ω.orbit := by
        rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq']
        exact MulAction.mem_orbit_self ω.out
      have h2 : g • ω.out ∈ ω.orbit := by
        rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq']
        exact MulAction.mem_orbit_iff.mpr ⟨⟨g, hgP⟩, rfl⟩
      have hne : g • ω.out ≠ ω.out := by
        simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hgk
      have hpair : ({ω.out, g • ω.out} : Set (Fin 8)) ⊆ ω.orbit := by
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h
        · rwa [h]
        · rwa [h]
      have hpaircard : ({ω.out, g • ω.out} : Set (Fin 8)).ncard = 2 :=
        Set.ncard_pair (Ne.symm hne)
      calc 2 = ({ω.out, g • ω.out} : Set (Fin 8)).ncard := hpaircard.symm
        _ ≤ ω.orbit.ncard := Set.ncard_le_ncard hpair
        _ = Nat.card ω.orbit := (Nat.card_coe_set_eq _).symm
    have hsum_ge : ∑ _ω : MulAction.orbitRel.Quotient P (Fin 8), 2 ≤
        ∑ ω : MulAction.orbitRel.Quotient P (Fin 8), Nat.card ω.orbit :=
      Finset.sum_le_sum fun ω _ => hge ω
    have h2card : ∑ _ω : MulAction.orbitRel.Quotient P (Fin 8), 2 =
        Nat.card (MulAction.orbitRel.Quotient P (Fin 8)) * 2 := by
      rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
    rw [← hsum, h2card] at hsum_ge
    rw [Nat.card_fin] at hsum_ge
    omega
  calc Nat.card ↥(fixV (P.map (G6.coreAct 8)))
      ≤ Nat.card (MulAction.orbitRel.Quotient P (Fin 8) → ZMod 2) := hcard_le
    _ = 2 ^ Nat.card (MulAction.orbitRel.Quotient P (Fin 8)) := hfun
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) horbit_le

theorem s16c11_v1_coreMod_eight_dimD1 {E : Subgroup (MulAut ↥(coreMod 8))}
    (hE : E ∈ E3.aSet 2 (G6.coreAct 8).range)
    (h2 : IsPGroup 2 ↥E) (hEne : E ≠ ⊥) :
    3 ≤ rkIdx (fixV E) := by
  have hErange : E ≤ (G6.coreAct 8).range := hE.1
  let P : Subgroup (Equiv.Perm (Fin 8)) := E.comap (G6.coreAct 8)
  have hPmap : P.map (G6.coreAct 8) = E := Subgroup.map_comap_eq_self hErange
  have hPexp : ∀ g ∈ P, g * g = 1 := by
    intro g hg
    apply s16c11_v1_coreAct_eight_injective
    have hgE : G6.coreAct 8 g ∈ E := hg
    have h2' : (G6.coreAct 8 g) * (G6.coreAct 8 g) = 1 := by
      have h := hE.2.2.1.2 (G6.coreAct 8 g) hgE
      calc (G6.coreAct 8 g) * (G6.coreAct 8 g) = (G6.coreAct 8 g) ^ 2 := (sq _).symm
        _ = 1 := h
    rw [map_mul, map_one]
    exact h2'
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hEne
    rw [← hPmap, hP, Subgroup.map_bot]
  have haSet : ∀ Q : Subgroup (Equiv.Perm (Fin 8)), Q ≤ P → Q.relIndex P = 2 →
      fixV (Q.map (G6.coreAct 8)) = fixV (P.map (G6.coreAct 8)) := by
    intro Q hQP hQidx
    have hBle : Q.map (G6.coreAct 8) ≤ E := by
      rw [← hPmap]; exact Subgroup.map_mono hQP
    have hrel : (Q.map (G6.coreAct 8)).relIndex E = Q.relIndex P := by
      rw [← hPmap]
      exact Subgroup.relIndex_map_map_of_injective Q P s16c11_v1_coreAct_eight_injective
    have hmq : E3.mQuot E (Q.map (G6.coreAct 8)) < 2 := by
      rw [E3.mQuot, hrel, hQidx]
      have hpp : padicValNat 2 2 = 1 := by
        nth_rewrite 2 [show (2 : ℕ) = 2 ^ 1 by norm_num]
        rw [padicValNat.prime_pow]
      omega
    have hfix := hE.2.2.2 (Q.map (G6.coreAct 8)) hBle hmq
    rw [← hPmap] at hfix
    exact hfix
  have hbound := s16c11_v1_eight_fixV_bound P hPexp hPne haSet
  have hboundE : Nat.card ↥(fixV E) ≤ 2 ^ 4 := hPmap ▸ hbound
  have hcard8 : Nat.card ↥(coreMod 8) = 2 ^ 7 := by
    rw [CFSG.Quasithin.H13.VolI.card_coreMod_eight]; norm_num
  have hrk8 : rk ↥(coreMod 8) = 7 := by
    unfold rk; rw [hcard8, padicValNat.prime_pow]
  have hpos : Nat.card ↥(fixV E) ≠ 0 := Nat.card_pos.ne'
  have hnotdvd : ¬ 2 ^ 5 ∣ Nat.card ↥(fixV E) := by
    intro hdvd
    have hge : 2 ^ 5 ≤ Nat.card ↥(fixV E) := Nat.le_of_dvd Nat.card_pos hdvd
    have hlt : Nat.card ↥(fixV E) < 2 ^ 5 := lt_of_le_of_lt hboundE (by norm_num)
    omega
  have hle : rk ↥(fixV E) ≤ 4 := by
    unfold rk
    by_contra h
    have h5 : 5 ≤ padicValNat 2 (Nat.card ↥(fixV E)) := by omega
    exact hnotdvd ((padicValNat_dvd_iff_le hpos).2 h5)
  have hsum : rk ↥(fixV E) + rkIdx (fixV E) = 7 := (rk_add_rkIdx (fixV E)).trans hrk8
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
