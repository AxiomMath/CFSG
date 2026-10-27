
module


public import CFSG.Monster.B.Co2.MatrixCert

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem matFacts : MatFacts := by
  have h := matCheck_eq_true
  simp only [Native.matCheck, Bool.and_eq_true, beq_iff_eq, Native.deg, and_assoc,
    Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨fun j hj i hi => ?_, fun r hr k hk => ?_, fun r hr => ?_, fun r hr t ht => ?_,
    fun r hr t ht => ?_, fun j hj => ?_, fun j hj => ?_, h6, fun t ht => ?_, fun t ht => ?_,
    fun r hr j hj => ?_, fun i hi => allLt_spec h10 hi, h11, h12, h13, h14, h15, h16⟩
  · simpa using allLt_spec (allLt_spec h1 hj) hi
  · simpa using allLt_spec (allLt_spec h2 hr) hk
  · simpa using allLt_spec h3 hr
  · have := allLt_spec (allLt_spec h4 hr) ht
    simp only [Bool.and_eq_true] at this
    exact of_decide_eq_true this.1
  · have := allLt_spec (allLt_spec h4 hr) ht
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
    exact this.2
  · have := allLt_spec h5 hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact of_decide_eq_true this.1
  · have := allLt_spec h5 hj
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.2
  · exact of_decide_eq_true (allLt_spec h7 ht)
  · simpa using allLt_spec h8 ht
  · simpa using allLt_spec (allLt_spec h9 hr) hj

theorem smul_dec_frameQ_inv
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ 2) (x : ℕ) :
    (actQ (frameQ j)⁻¹).unop • dec x = dec (VisCert.Native.actRows Native.frameInv[j]! x) := by
  have hj : j < 15 := by omega
  set u := (actQ (frameQ j)).unop with hu
  have hcomp : ∀ y, u • rowsMap Native.frameInv[j]! y = y := by
    intro y
    have hlin : (u : Module.End (ZMod 2) L2) ∘ₗ rowsMap Native.frameInv[j]! = LinearMap.id := by
      apply ellBasis.ext
      intro k
      rw [LinearMap.comp_apply, ellBasis_apply, rowsMap_ellCls, ← glv_smul, hu,
        smul_dec_frameQ hj, LinearMap.id_apply]
      have := matFacts.inv (j - 1) (by omega) k k.2
      rw [show j - 1 + 1 = j by omega] at this
      rw [native_actRows_eq] at this ⊢
      rw [this, dec_one_shiftLeft]
    exact LinearMap.congr_fun hlin y
  rw [map_inv, MulOpposite.unop_inv, native_actRows_eq, ← rowsMap_dec, ← hu]
  rw [inv_smul_eq_iff, hcomp]

theorem smul_dec_pairWordQ :
    ∀ w : List ℤ, (∀ l ∈ w, l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2) → ∀ x : ℕ,
      (actQ (pairWordQ w)).unop • dec x = dec (Native.pairWordAct w x)
  | [], _, x => by
    simp [pairWordQ, Native.pairWordAct]
  | l :: w, hw, x => by
    have hl := hw l List.mem_cons_self
    have hw' : ∀ l ∈ w, l = 1 ∨ l = 2 ∨ l = -1 ∨ l = -2 := fun l' h => hw l' (List.mem_cons_of_mem _ h)
    rw [pairWordQ, actQ_mul_smul, Native.pairWordAct, ← smul_dec_pairWordQ w hw']
    congr 1
    unfold pairLetterQ Native.pairLetterAct
    rcases hl with rfl | rfl | rfl | rfl
    · simpa using smul_dec_frameQ (j := 1) (by norm_num) x
    · simpa using smul_dec_frameQ (j := 2) (by norm_num) x
    · simpa using smul_dec_frameQ_inv (j := 1) le_rfl (by norm_num) x
    · simpa using smul_dec_frameQ_inv (j := 2) (by norm_num) le_rfl x

theorem smul_dec_alpha_recordAct
    (i : Fin 24) (x : ℕ) :
    (actQ (alpha i)).unop • dec x = dec (Native.recordAct (genRecord i) x) := by
  have hok := recordWordOK_spec (dataCheck_parts.2.2.2.1 i i.2).2.2
  unfold alpha Native.recordAct
  rcases hk : (genRecord i).kind with _ | _ | _
  · exact smul_dec_pairWordQ _ (hok.1 hk) x
  · exact smul_dec_frameWordQ _ (hok.2 (by unfold genRecord at hk; rw [hk]; decide)) x
  · exact smul_dec_frameWordQ _ (hok.2 (by unfold genRecord at hk; rw [hk]; decide)) x

theorem smul_dec_alpha
    (i : Fin 24) (x : ℕ) :
    (actQ (alpha i)).unop • dec x = dec (VisCert.actRows (genMatrix i) x) := by
  refine glv_smul_dec _ _ (fun k => ?_) x
  rw [← dec_one_shiftLeft k, smul_dec_alpha_recordAct, genRecord, matFacts.recs i i.2 k k.2]
  rfl

theorem alpha_smul_vShort
    (i : Fin 24) : (actQ (alpha i)).unop • vShort = vShort := by
  rw [vShort, smul_dec_alpha, ← native_actRows_eq]
  exact congrArg dec (matFacts.fix i i.2)

theorem alpha_mem_Kstab
    (i : Fin 24) : alpha i ∈ CFSG.Monster.B.Short.Kstab vShort :=
  alpha_smul_vShort i

theorem smul_quotBasis
    (i : Fin 24) (t : Fin 22) :
    (actQ (alpha i)).unop • dec (quotBasis t) =
        dec (Native.actD 22 Native.quotientBasis (genQuotMatrix i)[(t : ℕ)]!) ∨
      (actQ (alpha i)).unop • dec (quotBasis t) =
        dec (Native.actD 22 Native.quotientBasis (genQuotMatrix i)[(t : ℕ)]!) + vShort := by
  rw [smul_dec_alpha, ← native_actRows_eq]
  rcases matFacts.quot i i.2 t t.2 with h | h
  · left
    have := xor_eq_of_xor_eq h
    rw [Nat.xor_zero] at this
    exact congrArg dec this
  · right
    have e : VisCert.Native.actRows (genMatrix i) (quotBasis t) =
        Native.actD 22 Native.quotientBasis (genQuotMatrix i)[(t : ℕ)]! ^^^ 12288 :=
      xor_eq_of_xor_eq h
    rw [e, dec_xor]
    rfl

theorem shortVec_lt
    (j : Ω) : shortVec j < 2 ^ 22 := matFacts.vec_lt j j.2

theorem shortVec_injective : Function.Injective shortVec := by
  intro i j h
  apply Fin.ext
  rw [← matFacts.vec_pos i i.2, ← matFacts.vec_pos j j.2]
  exact congrArg (fun x => Native.vecPos[x]!) h

theorem actD_genQuotMatrix
    (i : Fin 24) (j : Ω) :
    Native.actD 22 (genQuotMatrix i) (shortVec j) = shortVec (pPerm i j) := by
  rw [shortVec, shortVec, genQuotMatrix, genRecord, matFacts.perm i i.2 j j.2,
    (rep_pPerm i).apply j.2]

theorem span_shortVec :
    Submodule.span (ZMod 2) (Set.range fun j : Ω => bvec 22 (shortVec j)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun (ZMod 2) (Fin 22)).span_eq, Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  have h := matFacts.span t t.2
  have hb := congrArg (bvec 22) h
  rw [bvec_actD] at hb
  have ht : bvec 22 (1 <<< (t : ℕ)) = Pi.basisFun (ZMod 2) (Fin 22) t := by
    funext i
    rw [Pi.basisFun_apply, bvec_apply, testBit_one_shiftLeft, Pi.single_apply]
    by_cases hi : i = t
    · subst hi; simp
    · simp [hi, Fin.val_ne_of_ne hi]
  rw [← ht, ← hb]
  refine Submodule.sum_mem _ fun s hs => ?_
  split_ifs
  · have hs' : s < 22 := Finset.mem_range.1 hs
    have hsz : s < (Native.spanIdx.map fun j => Native.vectors[j]!).size := by
      simpa [matFacts.span_size] using hs'
    rw [getElem!_pos _ s hsz, Array.getElem_map]
    have hlt := matFacts.span_lt s hs'
    rw [← getElem!_pos Native.spanIdx s (by rw [matFacts.span_size]; exact hs')]
    exact Submodule.subset_span ⟨⟨_, hlt⟩, rfl⟩
  · exact Submodule.zero_mem _

theorem pa_eq :
    pa = pairWordPerm Native.pairWords[0]! :=
  (eqA_iff rep_pa (rep_wordPermA _ (dataCheck_parts.2.2.2.2.2.2 0 (by norm_num)))).1
    (matFacts.pair 0 (by norm_num))

theorem pb_eq :
    pb = pairWordPerm Native.pairWords[1]! :=
  (eqA_iff rep_pb (rep_wordPermA _ (dataCheck_parts.2.2.2.2.2.2 1 (by norm_num)))).1
    (matFacts.pair 1 (by norm_num))

theorem orderOf_pa : orderOf pa = 2 :=
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  orderOf_eq_of_rep rep_pa matFacts.ord_a matFacts.ne_a

theorem orderOf_pb : orderOf pb = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_of_rep rep_pb matFacts.ord_b matFacts.ne_b

theorem orderOf_pa_mul_pb :
    orderOf (pa * pb) = 23 :=
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  orderOf_eq_of_rep (rep_compA rep_pa rep_pb) matFacts.ord_ab matFacts.ne_ab

end CFSG.Monster.B.Co2
