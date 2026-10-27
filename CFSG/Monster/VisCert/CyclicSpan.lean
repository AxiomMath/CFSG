module

public import CFSG.Monster.VisCert.CycRows

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def orbitInvT : Array ℕ :=
  #[3041329, 1446912, 4129798, 4087814, 3670052, 12582951, 44032, 3719168, 2228224, 2359296,
    1049636, 2097200, 16774104, 1024, 6292480, 10486784, 3072, 1048576, 48, 24, 64, 1152, 1280, 512]

@[expose] def wordsOK : Bool :=
  allTo (fun t => (orbitWords[t]!).all fun g => decide (g < 14)) 24

@[expose] def orbitOK : Bool :=
  allTo (fun t => actWord cycRows orbitWords[t]! seedVec == orbitVecs[t]!) 24

@[expose] def indepOK : Bool :=
  allTo (fun t => decide (orbitVecs[t]! < 2 ^ 24) && allTo (fun s =>
    popc 24 (orbitVecs[t]! &&& orbitInvT[s]!) % 2 == if t = s then 1 else 0) 24) 24

theorem wordsOK_eq_true : wordsOK = true := by decide +kernel

theorem orbitOK_eq_true : orbitOK = true := by decide +kernel

theorem indepOK_eq_true : indepOK = true := by decide +kernel

@[expose] def orbitCls (t : Fin 24) : L2 := dec orbitVecs[(t : ℕ)]!

theorem orbitWords_lt (t : Fin 24) : ∀ g ∈ orbitWords[(t : ℕ)]!, g < 14 := by
  have h := allTo_spec wordsOK_eq_true t.2
  rw [List.all_eq_true] at h
  exact fun g hg => of_decide_eq_true (h g hg)

theorem dec_orbitVecs (t : Fin 24) :
    orbitCls t = modTwoEnd (cycWordElt orbitWords[(t : ℕ)]!) twoΩCls := by
  rw [← dec_seed, modTwoEnd_cycWordElt _ (orbitWords_lt t), orbitCls]
  have h := allTo_spec orbitOK_eq_true t.2
  rw [beq_iff_eq] at h
  rw [show seedVec = 63 from rfl] at h
  rw [h]

theorem bvec_dotProduct_orbitInvT (t s : Fin 24) :
    bvec 24 orbitVecs[(t : ℕ)]! ⬝ᵥ bvec 24 orbitInvT[(s : ℕ)]! = if t = s then 1 else 0 := by
  rw [bvec_dotProduct]
  have h := allTo_spec indepOK_eq_true t.2
  rw [Bool.and_eq_true] at h
  have h' := allTo_spec h.2 s.2
  rw [beq_iff_eq] at h'
  rw [← ZMod.natCast_mod, h']
  by_cases hts : t = s
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (congrArg Fin.val hts)),
      ite_eq_left_of_eq_true _ _ (eq_true hts)]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => hts (Fin.ext h')),
      ite_eq_right_of_eq_false _ _ (eq_false hts)]
    rfl

theorem linearIndependent_bvec_orbitVecs :
    LinearIndependent (ZMod 2) fun t : Fin 24 => bvec 24 orbitVecs[(t : ℕ)]! := by
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have h := congrArg (fun x => x ⬝ᵥ bvec 24 orbitInvT[(s : ℕ)]!) hc
  simp only [sum_dotProduct, smul_dotProduct, bvec_dotProduct_orbitInvT, smul_eq_mul,
    zero_dotProduct] at h
  simpa using h

theorem linearIndependent_orbitCls : LinearIndependent (ZMod 2) orbitCls := by
  have e : orbitCls = ellBasis.equivFun.symm ∘ fun t : Fin 24 => bvec 24 orbitVecs[(t : ℕ)]! := by
    funext t
    simp [orbitCls, dec_eq_ellBasis]
  rw [e]
  exact linearIndependent_bvec_orbitVecs.map' _ ellBasis.equivFun.symm.ker

theorem span_orbitCls : Submodule.span (ZMod 2) (Set.range orbitCls) = ⊤ :=
  linearIndependent_orbitCls.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_L2])

theorem span_ellCls : Submodule.span (ZMod 2) (Set.range ellCls) = ⊤ :=
  linearIndependent_ellCls.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, finrank_L2])

theorem cycWordElt_mem_closure (w : List ℕ) :
    cycWordElt w ∈ Subgroup.closure (Set.range cycGen) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons g w ih =>
    rw [cycWordElt, List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ ih
    unfold cycGenN
    split_ifs with h
    · exact Subgroup.subset_closure ⟨_, rfl⟩
    · exact Subgroup.one_mem _

theorem span_orbit_closure_cycGen :
    Submodule.span (ZMod 2)
      {x : L2 | ∃ g ∈ Subgroup.closure (Set.range cycGen), modTwoEnd g twoΩCls = x} = ⊤ := by
  refine eq_top_iff.2 (span_orbitCls ▸ Submodule.span_mono ?_)
  rintro _ ⟨t, rfl⟩
  exact ⟨_, cycWordElt_mem_closure _, (dec_orbitVecs t).symm⟩

theorem pCyc_coeff : ∀ j : Fin 12, permWord pCyc (B j) =
    ∑ k : Fin 12, (if (pCoeff.getD j 0).testBit k then 1 else 0) • B k := by
  decide +kernel

theorem cyclic_span_certificate :
    pCyc ∈ AutPerm ∧
    (∀ j : Fin 12, permWord pCyc (B j) =
      ∑ k : Fin 12, (if (pCoeff.getD j 0).testBit k then 1 else 0) • B k) ∧
    (∀ j k : Fin 24, QuadraticMap.polarBilin qL (ellCls j) (ellCls k) = bvec 24 (gramRow j) k) ∧
    LinearIndependent (ZMod 2) ellCls ∧ Submodule.span (ZMod 2) (Set.range ellCls) = ⊤ ∧
    (∀ (g : Fin 14) (i : Fin 24), modTwoEnd (cycGen g) (ellCls i) =
      ∑ j : Fin 24, bvec 24 (cycRows[(g : ℕ)]!)[(i : ℕ)]! j • ellCls j) ∧
    twoΩCls = ∑ j : Fin 24, bvec 24 seedVec j • ellCls j ∧
    (∀ t : Fin 24, ∑ j : Fin 24, bvec 24 orbitVecs[(t : ℕ)]! j • ellCls j =
      modTwoEnd (cycWordElt orbitWords[(t : ℕ)]!) twoΩCls) ∧
    LinearIndependent (ZMod 2)
      (fun t : Fin 24 => ∑ j : Fin 24, bvec 24 orbitVecs[(t : ℕ)]! j • ellCls j) ∧
    Submodule.span (ZMod 2)
      {x : L2 | ∃ g ∈ Subgroup.closure (Set.range cycGen), modTwoEnd g twoΩCls = x} = ⊤ :=
  ⟨pCyc_mem, pCyc_coeff, bL_ellCls, linearIndependent_ellCls, span_ellCls,
    modTwoEnd_cycGen_ellCls, dec_seed.symm, dec_orbitVecs, linearIndependent_orbitCls,
    span_orbit_closure_cycGen⟩

end CFSG.Monster.VisCert
