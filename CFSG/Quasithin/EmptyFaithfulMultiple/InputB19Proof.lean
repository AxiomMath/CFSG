module

public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19
public import CFSG.Quasithin.Background.B19Final

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem setting_fittingOfSub {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}
    (hX : pCoreOf 2 X = ⊥) : B19.Setting X (fittingOfSub X) := by
  have hO2 := normal_two_subgroups_trivial_of_pCoreOf_eq_bot hX
  have hcore : CFSG.pCore 2 ↥X = ⊥ := by
    refine B1.pCore_eq_bot_of_normal_two_trivial fun Q hQ hQp => ?_
    have hQ' : Q.map X.subtype = ⊥ := by
      refine hO2 _ (Subgroup.map_subtype_le Q) ?_ (hQp.map X.subtype)
      have hsub : (Q.map X.subtype).subgroupOf X = Q :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
      rw [hsub]
      exact hQ
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hQ'
  refine ⟨Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro g hg f hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    have hconj := (inferInstance : (CFSG.fittingSubgroup ↥X).Normal).conj_mem f0 hf0 ⟨g, hg⟩
    exact ⟨_, hconj, by simp⟩
  · have := B1.fitting_card_odd hcore
    unfold fittingOfSub
    rwa [Subgroup.card_map_of_injective X.subtype_injective]
  · unfold fittingOfSub
    exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective X.subtype _)

theorem inputB19_holds : InputB19 := by
  intro V _ _ hV X hX hF
  classical
  set Φ := fittingOfSub X with hΦ
  have hS : B19.Setting X Φ := setting_fittingOfSub hX
  set J := ffJP {A | IsFFStarMin X A} X with hJ
  have hFeq : ⁅Φ, J⁆ = B19.FAll X Φ := hS.commutator_ffJP_eq hV
  rw [hFeq]
  obtain ⟨R, hR, hRinj, hRcov⟩ := B19.exists_reps X Φ
  let e := R.equivFin
  let T : Fin R.card → MulAut V := fun i => (e.symm i : MulAut V)
  have hT : ∀ i, T i ∈ B19.tvSet X Φ := fun i => hR _ (e.symm i).2
  have hTinj : ∀ i j, B19.FOf Φ (T i) = B19.FOf Φ (T j) → i = j := by
    intro i j h
    have := hRinj _ (e.symm i).2 _ (e.symm j).2 h
    exact e.symm.injective (Subtype.ext this)
  have hne : ∀ i j, i ≠ j → B19.FOf Φ (T i) ≠ B19.FOf Φ (T j) := fun i j hij h =>
    hij (hTinj i j h)
  have hTcov : ∀ t ∈ B19.tvSet X Φ, ∃ i, B19.FOf Φ t = B19.FOf Φ (T i) := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := hRcov t ht
    exact ⟨e ⟨r, hr⟩, by simp [T, hrt]⟩
  have hoddCore : ∀ i, oddCoreOfSub (B19.GOf Φ (T i)) = B19.FOf Φ (T i) := fun i =>
    hS.oddCore_GOf hV (hT i)
  have hoddCore' : (fun i => oddCoreOfSub (B19.GOf Φ (T i))) = fun i => B19.FOf Φ (T i) :=
    funext hoddCore
  have hFAll : B19.FAll X Φ = ⨆ i, B19.FOf Φ (T i) := by
    apply le_antisymm
    · refine iSup₂_le fun t ht => ?_
      obtain ⟨i, hi⟩ := hTcov t ht
      rw [hi]
      exact le_iSup (fun i => B19.FOf Φ (T i)) i
    · exact iSup_le fun i => B19.FOf_le_FAll (hT i)
  have hGle : ∀ t ∈ B19.tvSet X Φ, B19.GOf Φ t ≤ ⨆ i, B19.GOf Φ (T i) := by
    intro t ht
    obtain ⟨i, hi⟩ := hTcov t ht
    rw [hS.GOf_eq_of_FOf_eq hV ht (hT i) hi]
    exact le_iSup (fun i => B19.GOf Φ (T i)) i
  obtain ⟨hsupUW, hinfUW⟩ := hS.decomp_FAll hV
  have hext1 : ∀ c : MulAut V, (∀ u ∈ fixV (B19.FAll X Φ), c u = u) →
      (∀ w ∈ commV (B19.FAll X Φ), c w = w) → c = 1 := by
    intro c hcU hcW
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixV (B19.FAll X Φ) ⊔ commV (B19.FAll X Φ) := by rw [hsupUW]; trivial
    obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul, hcU u hu, hcW w hw]
    rfl
  have hGffJ : ∀ i, B19.GOf Φ (T i) ≤ ffJ X := fun i =>
    hS.GOf_le_of_forall hV (hT i) fun s hs =>
      B19.le_ffJ (B19.isFFStarMin_zpowers_tv hV hs).1 (Subgroup.mem_zpowers s)
  refine ⟨R.card, fun i => B19.GOf Φ (T i), fun i => ⟨hS.GOf_le hV (hT i), hS.GOf_iso hV (hT i)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · set K := ffJP {A | IsFFStarOffender X A}
      (X ⊓ Subgroup.centralizer ((B19.FAll X Φ : Subgroup (MulAut V)) : Set (MulAut V))) with hK
    refine ⟨?_, ?_, ?_⟩
    · rintro (_ | i) (_ | j) hij a ha b hb
      · exact absurd rfl hij
      · exact (Subgroup.mem_centralizer_iff.1 (hS.ffJP_cent_le hV (hT j) ha).1 b hb).symm
      · exact Subgroup.mem_centralizer_iff.1 (hS.ffJP_cent_le hV (hT i) hb).1 a ha
      · exact hS.pair_comm hV (hT i) (hT j) (hne i j fun h => hij (h ▸ rfl)) a ha b hb
    · refine B19.iSupIndep_of_centSub _
        (fun o => o.elim (fixV (B19.FAll X Φ)) fun i => commV (B19.FOf Φ (T i))) ?_ ?_
      · rintro (_ | i)
        · refine (Subgroup.eq_bot_iff_forall _).2 fun c hc => ?_
          exact hext1 c hc.2 (hS.ffJP_cent_le_centSub_W hV hc.1)
        · exact hS.GOf_inf_centSub hV (hT i)
      · rintro (_ | i) (_ | j) hij
        · exact absurd rfl hij
        · exact hS.GOf_le_centSub_U hV (hT j)
        · exact fun c hc => (hS.ffJP_cent_le hV (hT i) hc).2
        · exact hS.pair_centSub hV (hT i) (hT j) (hne i j fun h => hij (h ▸ rfl))
    · rw [iSup_option]
      apply le_antisymm
      · refine sup_le ?_ (iSup_le hGffJ)
        exact iSup_le fun A => iSup_le fun hA => iSup_le fun _ => B19.le_ffJ hA
      · refine (hS.ffJ_le hV).trans (sup_le ?_ le_sup_left)
        exact le_sup_of_le_right (iSup₂_le hGle)
  · rw [hoddCore']
    refine ⟨fun i j _ a ha b hb => ?_, ?_, hFAll.symm⟩
    · exact (hS.FOf_central hV (hT i) a ha b (hS.FOf_le hV (hT j) hb)).symm
    · exact B19.iSupIndep_of_centSub _ (fun i => commV (B19.FOf Φ (T i)))
        (fun i => hS.FOf_inf_centSub hV (hT i))
        (fun i j hij => B19.FOf_le_GOf.trans (hS.pair_centSub hV (hT i) (hT j) (hne i j hij)))
  · intro i
    rw [hoddCore]
    exact hS.card_FOf hV (hT i)
  · refine ⟨?_, ?_, ?_⟩
    · intro i j hij a ha b hb
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact Subgroup.mem_centralizer_iff.1 hb.2 a (hS.FAll_le_ffJP hV ha)
      · exact (Subgroup.mem_centralizer_iff.1 ha.2 b (hS.FAll_le_ffJP hV hb)).symm
      · exact absurd rfl hij
    · refine (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide) ?_).2 ?_
      · intro k
        fin_cases k <;> simp
      · exact disjoint_iff.2 (hS.FAll_inf_eq_bot hV)
    · apply le_antisymm
      · refine iSup_le fun i => ?_
        fin_cases i
        · exact hS.FAll_le hV
        · exact inf_le_left
      · refine (hS.le_FAll_sup hV).trans (sup_le ?_ ?_)
        · exact le_iSup_of_le (0 : Fin 2) le_rfl
        · exact le_iSup_of_le (1 : Fin 2) le_rfl
  · intro i
    rw [hoddCore, hS.commV_GOf hV (hT i)]
    exact ⟨rfl, hS.card_commV_FOf hV (hT i)⟩
  · simp only [hoddCore]
    refine B19.iSupIndep_of_fixV _ (fun i => B19.FOf Φ (T i)) (fun i => ?_)
      (fun i j hij => hS.pair_fixV hV (hT i) (hT j) (hne i j hij))
    rw [inf_comm]
    exact (hS.decomp_FOf hV (hT i)).2
  · simp only [hoddCore]
    rw [hFAll, B19.commV_iSup]
  · intro A
    constructor
    · rintro ⟨hA, hnt⟩
      obtain ⟨t, ht, rfl⟩ := hS.exists_tv_of_isFFStarMin hV hA hnt
      obtain ⟨i, hi⟩ := hTcov t ht
      refine ⟨i, ?_⟩
      show IsSylowTwoOf (Subgroup.zpowers t) (B19.GOf Φ (T i))
      rw [← hS.GOf_eq_of_FOf_eq hV ht (hT i) hi]
      exact hS.isSylowTwoOf_zpowers hV ht
    · rintro ⟨i, hi⟩
      obtain ⟨t', ht', rfl, -⟩ := hS.exists_tv_of_isSylowTwoOf hV (hT i) hi
      exact ⟨B19.isFFStarMin_zpowers_tv hV ht', hS.commutator_zpowers_ne_bot hV ht'⟩
  · intro A K hA hKX hKA
    exact hS.part5 hV hA hKX hKA

end CFSG.Quasithin.EmptyFaithfulMultiple
