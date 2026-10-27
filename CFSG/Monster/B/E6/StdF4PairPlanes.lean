module

public import CFSG.Monster.B.E6.StdF4FiberFlags

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft parSmul
  parSmul_mk parMap_eq_mul betaPar thetaFirst residueFlag_parSmul_first SUFrob SUFrob_smul_def
  qSmul_mk frobAct_of_eq_one frobAct_of_eq_frobAut mem_frobGroup_iff ZSU)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Geometry CFSG.Monster.B.Classical Matrix Module
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_flag_of_le {R T : Submodule K (Fin 6 → K)} (hR : finrank K R = 1)
    (hT : T ∈ isoSubs 2) (hRT : R ≤ T) : ∃ F : IsoFlag6, F.sub 0 = R ∧ F.sub 2 = T := by
  have hlt : R < T := lt_of_le_of_ne hRT fun h => by
    have h3 := hT.1
    rw [← h, hR] at h3
    exact absurd h3 (by decide)
  obtain ⟨v, hvT, hvR⟩ := IsConcreteLE.exists_of_lt hlt
  have hv0 : v ≠ 0 := fun h => hvR (h ▸ R.zero_mem)
  have hdisj : R ⊓ K ∙ v = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwR, hwv⟩ := Submodule.mem_inf.1 hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hwv
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · refine absurd ?_ hvR
      have h1 := R.smul_mem c⁻¹ hwR
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
  have hLrank : finrank K ↥(R ⊔ K ∙ v) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq R (K ∙ v)
    rw [hdisj, finrank_bot, add_zero, hR, finrank_span_singleton hv0] at h
    exact h
  have hLT : R ⊔ K ∙ v ≤ T := sup_le hRT ((Submodule.span_singleton_le_iff_mem _ _).2 hvT)
  refine ⟨⟨![R, R ⊔ K ∙ v, T], fun k => ?_, ?_, fun x hx y hy => hT.2 x hx y hy⟩, rfl, rfl⟩
  · fin_cases k
    · exact hR
    · exact hLrank
    · exact hT.1
  · refine Fin.monotone_iff_le_succ.mpr fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact hLT

abbrev basePoint : Submodule K (Fin 6 → K) := baseFlag.sub 0

theorem finrank_basePoint : finrank K basePoint = 1 := baseFlag.finrank_sub 0

theorem exists_fibLevi_flagSub
    {T : Submodule K (Fin 6 → K)} (hT : T ∈ isoSubs 2)
    (hRT : basePoint ≤ T) :
    ∃ l : nativeParabolic firstJ, (l : ModGL Tag.E6 K) ∈ fibLevi 2 ∧ flagSub 2 l = T := by
  obtain ⟨F, hF0, hF2⟩ := exists_flag_of_le finrank_basePoint hT hRT
  obtain ⟨x, hx⟩ := residueFlag.surjective F
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  have hp0 : flagSub 0 p = baseFlag.sub 0 := by rw [flagSub, hx, hF0]
  have hpI : (p : ModGL Tag.E6 K) ∈ nativeParabolic (fibIF 2 : Set (Fin 4)) :=
    (mem_flagStabP_iff_mem (flagStab_fibKd (d := 2) (Or.inr (Or.inl rfl))) p).1 hp0
  have hpI' : (p : ModGL Tag.E6 K) ∈ ((stdRadical firstJ : Set (ModGL Tag.E6 K)) *
      (leviParabolic firstJ (fibIF 2 : Set (Fin 4)) : Set (ModGL Tag.E6 K))) := by
    rw [← coe_nativeParabolic_eq_mul (fibIF_subset 2)]
    exact hpI
  obtain ⟨u, hu, l, hl, e⟩ := hpI'
  have hlP : l ∈ nativeParabolic firstJ :=
    nativeParabolic_mono (fibIF_subset 2) (leviParabolic_le_nativeParabolic firstJ _ hl)
  have huP : u ∈ nativeParabolic firstJ := stdRadical_le_nativeParabolic' firstJ hu
  refine ⟨⟨l, hlP⟩, hl, ?_⟩
  have e' : p = ⟨u, huP⟩ * ⟨l, hlP⟩ := Subtype.ext e.symm
  rw [← flagSub_mul_left_of_mem_stdRadical 2 (u := ⟨u, huP⟩) hu, ← e', flagSub, hx, hF2]

theorem flagStab_zero_inf_two :
    flagStab 0 ⊓ flagStab 2 = nativeParabolic {2} := by
  obtain ⟨I, hI⟩ := exists_eq_nativeParabolic
    (le_inf (stdBorel_le_flagStab 0) (stdBorel_le_flagStab 2))
    (inf_le_left.trans (flagStab_le_stdGroup 0))
  have hI' : I = {2} := by
    ext i
    rw [← nativeRep_mem_nativeParabolic_iff, ← hI, Subgroup.mem_inf, nativeRep_mem_flagStab_iff,
      nativeRep_mem_flagStab_iff, Set.mem_singleton_iff]
    simp only [firstJ, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases i <;> decide
  rw [hI, hI']

@[expose] def idx2 : List ℕ := [0, 2]

theorem idx2_checks : (∀ i ∈ idx2, i < 48) ∧ idx2.Nodup ∧
    (∀ i ∈ idx2, ∀ k ∈ E6Folded.jWords.getD i [], k ∈ ({2} : Finset (Fin 4))) ∧
    E6Folded.idCode ∈ idx2.map (fun i => E6Folded.jCodes.getD i []) ∧
    (∀ i ∈ idx2, ∀ k ∈ ({2} : Finset (Fin 4)),
      E6Folded.compose (E6Folded.gc k) (E6Folded.jCodes.getD i []) ∈
        idx2.map fun i => E6Folded.jCodes.getD i []) ∧
    (idx2.map fun i => E6Folded.wordWeight (E6Folded.jWords.getD i [])).sum = 5 := by
  decide +kernel

theorem finsum_parabolic_2 :
    ∑ᶠ w ∈ (ncs.parabolic (({2} : Finset (Fin 4)) : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = 5 := by
  obtain ⟨hlt, hnd, hl, hone, hcl, hsum⟩ := idx2_checks
  rw [finsum_parabolic_of_list hlt hnd (mem_closure_iff_jElt hlt hl hone hcl), hsum]

theorem card_nativeParabolic_2 :
    Nat.card (nativeParabolic {2}) = 3 * 2 ^ 36 * 5 := by
  have h := card_nativeParabolic (({2} : Finset (Fin 4)) : Set (Fin 4))
  rw [finsum_parabolic_2, Finset.coe_singleton] at h
  exact h

@[expose] def planeQ :
    flagStabP 0 ⧸ (flagStabP 0 ⊓ flagStabP 2).subgroupOf (flagStabP 0) →
    Submodule K (Fin 6 → K) :=
  Quotient.lift (fun b => flagSub 2 b.1) fun a b hab => (flagSub_eq_flagSub_iff a.1 b.1).2
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.leftRel_apply.1 hab))).2

theorem planeQ_injective :
    Function.Injective planeQ := by
  intro x y h
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
  · exact (a⁻¹ * b).2
  · exact (flagSub_eq_flagSub_iff a.1 b.1).1 h

theorem range_planeQ :
    Set.range planeQ = {T | T ∈ isoSubs 2 ∧ basePoint ≤ T} := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with | H b => ?_
    refine ⟨flagSub_mem_isoSubs 2 b.1, ?_⟩
    have hb : flagSub 0 b.1 = baseFlag.sub 0 := b.2
    change baseFlag.sub 0 ≤ flagSub 2 b.1
    rw [← hb]
    exact (residueFlag (QuotientGroup.mk b.1)).mono (by decide)
  · rintro ⟨hT, hRT⟩
    obtain ⟨F, hF0, hF2⟩ := exists_flag_of_le finrank_basePoint hT hRT
    obtain ⟨x, hx⟩ := residueFlag.surjective F
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    have hp0 : p ∈ flagStabP 0 := by
      change flagSub 0 p = _
      rw [flagSub, hx, hF0]
    exact ⟨QuotientGroup.mk ⟨p, hp0⟩, by
      change flagSub 2 p = T
      rw [flagSub, hx, hF2]⟩

theorem card_flagStabP
    (k : Fin 3) : Nat.card (flagStabP k) = Nat.card (flagStab k) :=
  Nat.card_congr ((flagStabP k).equivMapOfInjective (nativeParabolic firstJ).subtype
    (nativeParabolic firstJ).subtype_injective).toEquiv

theorem ncard_planes_basePoint :
    {T | T ∈ isoSubs 2 ∧ basePoint ≤ T}.ncard = 27 := by
  rw [← range_planeQ, Set.ncard_range_of_injective planeQ_injective]
  have h := Subgroup.card_mul_index ((flagStabP 0 ⊓ flagStabP 2).subgroupOf (flagStabP 0))
  have h1 : Nat.card ((flagStabP 0 ⊓ flagStabP 2).subgroupOf (flagStabP 0)) =
      3 * 2 ^ 36 * 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      Nat.card_congr ((flagStabP 0 ⊓ flagStabP 2).equivMapOfInjective
        (nativeParabolic firstJ).subtype (nativeParabolic firstJ).subtype_injective).toEquiv,
      Subgroup.map_inf_eq (flagStabP 0) (flagStabP 2) (nativeParabolic firstJ).subtype
        (nativeParabolic firstJ).subtype_injective]
    change Nat.card ↥(flagStab 0 ⊓ flagStab 2) = _
    rw [flagStab_zero_inf_two, card_nativeParabolic_2]
  have hs : flagStab 0 = nativeParabolic (fibIF 2 : Set (Fin 4)) :=
    flagStab_fibKd (d := 2) (Or.inr (Or.inl rfl))
  have h2 : Nat.card (flagStabP 0) = 3 * 2 ^ 36 * 135 := by
    rw [card_flagStabP, hs, card_nativeParabolic]
    have h12 : ∑ᶠ w ∈ (ncs.parabolic (fibIF 2 : Set (Fin 4)) : Set NW),
        weylWeight ncs E6Folded.letterWeight w = 135 := finsum_parabolic_12
    rw [h12]
  rw [h1, h2] at h
  have e : (3 * 2 ^ 36 * 135 : ℕ) = 3 * 2 ^ 36 * 5 * 27 := by norm_num
  rw [e] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem frob6_injective : Function.Injective (frob6 : (Fin 6 → K) → (Fin 6 → K)) :=
  Function.LeftInverse.injective frob6_frob6

theorem SUFrob_smul_sub_le_iff (a : SUFrob) (F G : IsoFlag6) (i j : Fin 3) :
    (a • F).sub i ≤ (a • G).sub j ↔ F.sub i ≤ G.sub j := by
  rw [SUFrob_smul_def, SUFrob_smul_def]
  obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective a.left
  rw [← hh, qSmul_mk, qSmul_mk, smul_sub, smul_sub,
    Submodule.map_le_map_iff_of_injective (f := (suLin h : (Fin 6 → K) →ₗ[K] (Fin 6 → K)))
      (suLin h).injective]
  rcases mem_frobGroup_iff.mp a.right.2 with hf | hf
  · rw [frobAct_of_eq_one hf, frobAct_of_eq_one hf]
  · rw [frobAct_of_eq_frobAut hf, frobAct_of_eq_frobAut hf, frobFlag_sub, frobFlag_sub,
      Submodule.map_le_map_iff_of_injective frob6_injective]

theorem residueFlag_parLeft
    (γ : parStar firstJ) :
    residueFlag (QuotientGroup.mk (parLeft γ)) = thetaFirst γ • baseFlag := by
  have h := residueFlag_parSmul_first γ (QuotientGroup.mk 1)
  rw [parSmul_mk, parMap_eq_mul, residueFlag_one] at h
  have e : betaPar γ.1.right (1 : nativeParabolic firstJ) = 1 := by
    apply Subtype.ext
    change (((γ.1.right : MulAut stdGroup) 1 : stdGroup) : ModGL Tag.E6 K) = 1
    rw [map_one]
    rfl
  rw [e, mul_one] at h
  exact h

end CFSG.Monster.B.E6.StdF4
