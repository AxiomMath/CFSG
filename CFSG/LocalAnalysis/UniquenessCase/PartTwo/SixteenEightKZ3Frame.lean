module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Image
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3FrameDef

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_stableUnder_iSup_of_map_mem {W : Type*} [CommGroup W]
    {Y : Subgroup (MulAut W)} {S : Set (Subgroup W)}
    (hS : ∀ I ∈ S, ∀ y ∈ Y, I.map y.toMonoidHom ∈ S) :
    StableUnder Y (⨆ I ∈ S, I) := by
  intro y hy u hu
  have hle : (⨆ I ∈ S, I).map y.toMonoidHom ≤ ⨆ I ∈ S, I := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun I => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hI => le_iSup₂_of_le (I.map y.toMonoidHom) (hS I hI y hy) le_rfl
  exact hle (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)

private theorem s16k_sSupIndep_map_orderIso {α β : Type*} [CompleteLattice α]
    [CompleteLattice β] (f : α ≃o β) (s : Set α) : sSupIndep (f '' s) ↔ sSupIndep s := by
  constructor
  · intro h a ha
    have h1 := h (Set.mem_image_of_mem f ha)
    rw [← Set.image_singleton, ← Set.image_sdiff f.injective, ← map_sSup] at h1
    exact (disjoint_map_orderIso_iff f).1 h1
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := hb
    have h1 := (h ha).map_orderIso f
    rwa [map_sSup, Set.image_sdiff f.injective, Set.image_singleton] at h1

theorem s16k_z3_frame (h : S16kBase D V₀ V L hV) (hZ : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6) {A : Subgroup G} (hAM : A ≤ D.M)
    (hA : IsElemAbelian 3 A) (hA4 : Nat.card A = 3 ^ 4)
    (hN : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      ((barSub V₀ V hV A : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ E : Fin 3 → Subgroup (MulAut (Vtil V₀ V hV)), S16kFrame (Mbar D.M V₀ V hV) E := by
  classical
  obtain ⟨-, e, φ, hmul, hφL, hφM, hφA⟩ := s16k_z3_image_torus h hZ hrk hAM hA hA4
  have hmul' : ∀ (g : MulAut (Vtil V₀ V hV)) (w : Vtil V₀ V hV),
      Multiplicative.toAdd (e.toMonoidHom (g w)) =
        ((φ g : S16kGL6) : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
          (Multiplicative.toAdd (e.toMonoidHom w)) := by
    intro g w
    simpa only [MulEquiv.coe_toMonoidHom] using hmul g w
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let E : Fin 3 → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun i => (s16kCoord i).map φ.symm.toMonoidHom
  let U : Fin 3 → Subgroup (Vtil V₀ V hV) := fun i => commSub ⊤ (E i)
  have hD_le : ∀ i : Fin 3, s16kCoord i ≤ s16kDiag := by
    intro i
    rw [s16k_diag_eq_sup]
    fin_cases i
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hφA_symm : (s16kDiag).map φ.symm.toMonoidHom = barSub V₀ V hV A := by
    have h1 := congrArg (fun H => H.map φ.symm.toMonoidHom) hφA
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom =
      MonoidHom.id _ from by ext x; simp, Subgroup.map_id] at h1
    exact h1.symm
  have hE_le_A : ∀ i, E i ≤ barSub V₀ V hV A := fun i =>
    (Subgroup.map_mono (hD_le i)).trans (le_of_eq hφA_symm)
  have hEM : ∀ i, E i ≤ Mb := fun i =>
    (hE_le_A i).trans (barSub_mono V₀ V hV hAM)
  have hEφ : ∀ i, (E i).map φ.toMonoidHom = s16kCoord i := by
    intro i
    show ((s16kCoord i).map φ.symm.toMonoidHom).map φ.toMonoidHom = s16kCoord i
    rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom =
      MonoidHom.id _ from by ext x; simp, Subgroup.map_id]
  have hmem_coord : ∀ {i : Fin 3} {x : MulAut (Vtil V₀ V hV)},
      x ∈ E i → φ x ∈ s16kCoord i := by
    intro i x hx
    rw [← hEφ i]
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩
  have hcyc : ∀ i, IsCyclicOrd ↥(E i) 3 := by
    intro i
    have e' : ↥(s16kCoord i) ≃* ↥(E i) :=
      Subgroup.equivMapOfInjective (s16kCoord i) φ.symm.toMonoidHom φ.symm.injective
    refine ⟨?_, ?_⟩
    · exact (e'.isCyclic).mp (s16k_coord_isCyclicOrd i).1
    · exact (Nat.card_congr e'.toEquiv).symm.trans (s16k_coord_isCyclicOrd i).2
  have hAbar_el : IsElemAbelian 3 (barSub V₀ V hV A) := by
    have hel := (hA.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)
    simpa only [barSub] using hel
  have hAbar_pg : IsPGroup 3 ↥((barSub V₀ V hV A).subgroupOf Mb) :=
    hAbar_el.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe (barSub_mono V₀ V hV hAM)).symm
  have hAbar_normal : ((barSub V₀ V hV A).subgroupOf Mb).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (barSub_mono V₀ V hV hAM)).2 hN
  have hAbar_le_core : barSub V₀ V hV A ≤ pCoreOf 3 Mb := by
    intro x hx
    have hxM : x ∈ Mb := barSub_mono V₀ V hV hAM hx
    have hmem : (⟨x, hxM⟩ : ↥Mb) ∈ (barSub V₀ V hV A).subgroupOf Mb :=
      (Subgroup.mem_subgroupOf).2 hx
    have hcore : (⟨x, hxM⟩ : ↥Mb) ∈ CFSG.pCore 3 ↥Mb :=
      Subgroup.mem_sSup_of_mem (S := {K : Subgroup ↥Mb | K.Normal ∧ IsPGroup 3 K})
        (s := (barSub V₀ V hV A).subgroupOf Mb)
        ⟨hAbar_normal, hAbar_pg⟩ hmem
    exact (CFSG.mem_openPCoreOf_iff ⟨x, hxM⟩).2 hcore
  have hcore : ∀ i, E i ≤ pCoreOf 3 Mb := fun i => (hE_le_A i).trans hAbar_le_core
  have hmap_line : ∀ i, (U i).map e.toMonoidHom = s16kLine i := by
    intro i
    show (commSub ⊤ (E i)).map e.toMonoidHom = s16kLine i
    rw [s16k_line_eq_closure_comm i]
    unfold commSub
    rw [MonoidHom.map_closure]
    congr 1
    ext u
    constructor
    · rintro ⟨c, ⟨x, hx, w, -, hc⟩, hu⟩
      have hxφ : φ x ∈ s16kCoord i := hmem_coord hx
      refine ⟨φ x, hxφ, e w, ?_⟩
      rw [← hu, ← hc]
      apply Multiplicative.toAdd.injective
      simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_ofAdd]
      rw [hmul' x w]
      abel
    · rintro ⟨d, hd, v, rfl⟩
      refine ⟨(φ.symm d) (e.symm v) * (e.symm v)⁻¹, ?_, ?_⟩
      · exact ⟨φ.symm d, Subgroup.mem_map.2 ⟨d, hd, rfl⟩,
          e.symm v, Subgroup.mem_top _, rfl⟩
      · apply Multiplicative.toAdd.injective
        simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, toAdd_ofAdd]
        rw [hmul' (φ.symm d) (e.symm v)]
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        abel
  have hrk2 : ∀ i, rk ↥(U i) = 2 := by
    intro i
    have hcard : Nat.card ↥(U i) = 4 :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (U i) e.toMonoidHom
        e.injective).toEquiv).trans (by rw [hmap_line i]; exact s16k_line_card i)
    rw [rk, hcard, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
  have hindep : sSupIndep (Set.range U) := by
    have himg : (MulEquiv.mapSubgroup e) '' (Set.range U) = Set.range s16kLine := by
      ext H
      constructor
      · rintro ⟨K, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, by rw [MulEquiv.coe_mapSubgroup]; exact (hmap_line i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨U i, ⟨i, rfl⟩, by rw [MulEquiv.coe_mapSubgroup]; exact hmap_line i⟩
    exact (s16k_sSupIndep_map_orderIso (MulEquiv.mapSubgroup e) (Set.range U)).mp
      (himg ▸ s16k_line_sSupIndep)
  have hspan : (⨆ i, U i) = ⊤ := by
    have hmap : (⨆ i, U i).map e.toMonoidHom = ⊤ := by
      rw [Subgroup.map_iSup]
      rw [show (⨆ i, (U i).map e.toMonoidHom) = ⨆ i, s16kLine i from
        iSup_congr hmap_line]
      exact s16k_line_iSup
    refine eq_top_iff.2 fun u _ => ?_
    have : e u ∈ (⨆ i, U i).map e.toMonoidHom := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 this
    rw [e.injective hvu] at hv
    exact hv
  have hcomm : ∀ i j, ∀ x ∈ E i, ∀ y ∈ E j, x * y = y * x := by
    intro i j x hx y hy
    have h := s16k_coord_comm (hmem_coord hx) (hmem_coord hy)
    apply φ.injective
    simpa only [map_mul] using h
  have hfix : ∀ {i j : Fin 3}, i ≠ j → ∀ x ∈ E j, ∀ u ∈ U i, x u = u := by
    intro i j hij x hx u hu
    have hxu : e u ∈ s16kLine i := by
      rw [← hmap_line i]
      exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [hmul x u, s16k_coord_trivial_on_line hij (hmem_coord hx) hxu]
  have hcent : ∀ i j, i ≠ j → commSub (commSub ⊤ (E i)) (E j) = ⊥ := by
    intro i j hij
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro x hx
    exact hfix hij x hx u hu
  have hinj : Function.Injective E := by
    intro i j hij
    have h := congrArg (fun H => H.map φ.toMonoidHom) hij
    rw [hEφ i, hEφ j] at h
    exact s16k_coord_injective h
  have hMnormD : Mb.map φ.toMonoidHom ≤
      Subgroup.normalizer (s16kDiag : Set S16kGL6) := by
    calc Mb.map φ.toMonoidHom
        ≤ (Subgroup.normalizer (barSub V₀ V hV A :
            Set (MulAut (Vtil V₀ V hV)))).map φ.toMonoidHom :=
          Subgroup.map_mono hN
      _ = Subgroup.normalizer ((barSub V₀ V hV A).map φ.toMonoidHom) :=
          Subgroup.map_equiv_normalizer_eq _ φ
      _ = Subgroup.normalizer (s16kDiag : Set S16kGL6) := by rw [hφA]
  have hperm : ∀ g ∈ Mb, ∀ i, ∃ j, (E i).map (MulAut.conj g).toMonoidHom = E j := by
    intro g hg i
    have hgD : φ g ∈ Subgroup.normalizer (s16kDiag : Set S16kGL6) :=
      hMnormD (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)
    obtain ⟨j, hj⟩ := s16k_normalizer_diag_perm hgD i
    refine ⟨j, ?_⟩
    have h2 : ((E i).map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom = s16kCoord j := by
      rw [Subgroup.map_map]
      have hcomp : φ.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj (φ g)).toMonoidHom.comp φ.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        show φ (MulAut.conj g x) = MulAut.conj (φ g) (φ x)
        simp only [MulAut.conj_apply, map_mul, map_inv]
      rw [hcomp, ← Subgroup.map_map, hEφ i, hj]
    have h3 := congrArg (fun H => H.map φ.symm.toMonoidHom) h2
    rw [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ from
      by ext x; simp, Subgroup.map_id] at h3
    exact h3
  have hproof : h.setting.hyp16.hyp125.isElemAbelian = hV := Subsingleton.elim _ _
  have hmb_eq : Mbar D.M V₀ V h.setting.hyp16.hyp125.isElemAbelian = Mb := by
    rw [hproof]
  have hE0_ne : E 0 ≠ ⊥ := by
    intro hbot
    have hcard := (hcyc 0).2
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hMb_ne : Mb ≠ ⊥ := by
    intro hbot
    exact hE0_ne (le_bot_iff.1 ((hEM 0).trans (le_of_eq hbot)))
  have hbasic' : IsBasicModule (Mbar D.M V₀ V h.setting.hyp16.hyp125.isElemAbelian) :=
    TwelveSeventeen.isBasicModule D h.std.hx h.std.h61 h.std.h127 h.std.h1214
      h.setting.hyp16.hyp125 (by rw [hmb_eq]; exact hMb_ne)
  have hbasic : IsBasicModule Mb := hmb_eq ▸ hbasic'
  have htrans : ∀ i j, ∃ g ∈ Mb, (E i).map (MulAut.conj g).toMonoidHom = E j := by
    let S : Set (Fin 3) := {j | ∃ g ∈ Mb, (E 0).map (MulAut.conj g).toMonoidHom = E j}
    have hconj_one : (MulAut.conj (1 : MulAut (Vtil V₀ V hV))).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      simp [MulAut.conj_apply]
    have h0S : (0 : Fin 3) ∈ S := ⟨1, Mb.one_mem, by rw [hconj_one, Subgroup.map_id]⟩
    have hS_inv : ∀ j ∈ S, ∀ y ∈ Mb, ∃ j' ∈ S,
        (E j).map (MulAut.conj y).toMonoidHom = E j' := by
      rintro j ⟨g, hgM, hg⟩ y hy
      obtain ⟨j', hj'⟩ := hperm y hy j
      have h1 : ((E 0).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj y).toMonoidHom = (E 0).map (MulAut.conj (y * g)).toMonoidHom := by
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
            (MulAut.conj (y * g)).toMonoidHom := by
          apply MonoidHom.ext
          intro x
          show y * (g * x * g⁻¹) * y⁻¹ = (y * g) * x * (y * g)⁻¹
          group
        rw [hcomp]
      refine ⟨j', ⟨y * g, Mb.mul_mem hy hgM, ?_⟩, hj'⟩
      calc (E 0).map (MulAut.conj (y * g)).toMonoidHom
          = ((E 0).map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj y).toMonoidHom := h1.symm
        _ = (E j).map (MulAut.conj y).toMonoidHom := by rw [hg]
        _ = E j' := hj'
    have hrk_proper : ∀ T : Set (Fin 3), T ≠ Set.univ → rk ↥(⨆ j ∈ T, U j) ≤ 4 := by
      intro T hT
      have hproper : ∃ j₀ : Fin 3, j₀ ∉ T := by
        by_contra hc
        apply hT
        rw [Set.eq_univ_iff_forall]
        intro j
        by_contra hj
        exact hc ⟨j, hj⟩
      obtain ⟨j₀, hj₀⟩ := hproper
      obtain ⟨a, b, hSub⟩ : ∃ a b : Fin 3, T ⊆ ({a, b} : Set (Fin 3)) := by
        fin_cases j₀
        · exact ⟨1, 2, fun j hj => by fin_cases j <;> simp_all⟩
        · exact ⟨0, 2, fun j hj => by fin_cases j <;> simp_all⟩
        · exact ⟨0, 1, fun j hj => by fin_cases j <;> simp_all⟩
      have hle : (⨆ j ∈ T, U j) ≤ U a ⊔ U b := by
        refine iSup₂_le fun j hj => ?_
        have hj' : j = a ∨ j = b := by
          have := hSub hj
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
        rcases hj' with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      have h := rk_sup_add_rk_inf (U a) (U b)
      rw [hrk2 a, hrk2 b] at h
      have h4 : rk ↥(U a ⊔ U b) ≤ 4 := by omega
      exact (rk_mono hle).trans h4
    have hS_univ : S = Set.univ := by
      by_contra hne
      have hStabS : StableUnder Mb (⨆ j ∈ S, U j) := by
        have hVS_eq : (⨆ j ∈ S, U j) = ⨆ I ∈ U '' S, I := by
          rw [iSup_image]
        rw [hVS_eq]
        refine s16k_stableUnder_iSup_of_map_mem ?_
        rintro I ⟨j, hjS, rfl⟩ y hy
        obtain ⟨j', hj'S, hj'⟩ := hS_inv j hjS y hy
        refine ⟨j', hj'S, ?_⟩
        have hc := CFSG.Quasithin.Asc81c.commSub_map_conj (E j) y
        rw [hj'] at hc
        exact hc
      have hStabT : StableUnder Mb (⨆ j ∈ Sᶜ, U j) := by
        have hVT_eq : (⨆ j ∈ Sᶜ, U j) = ⨆ I ∈ U '' Sᶜ, I := by
          rw [iSup_image]
        rw [hVT_eq]
        refine s16k_stableUnder_iSup_of_map_mem ?_
        rintro I ⟨j, hjT, rfl⟩ y hy
        obtain ⟨j', hj'⟩ := hperm y hy j
        have hj'T : j' ∉ S := by
          intro hj'S
          obtain ⟨j'', hj''S, hj''⟩ := hS_inv j' hj'S y⁻¹ (Mb.inv_mem hy)
          have hEjj'' : E j = E j'' := by
            have h1 : ((E j).map (MulAut.conj y).toMonoidHom).map
                (MulAut.conj y⁻¹).toMonoidHom = E j'' := by rw [hj', hj'']
            rwa [Subgroup.map_map, show (MulAut.conj y⁻¹).toMonoidHom.comp
              (MulAut.conj y).toMonoidHom = MonoidHom.id _ from by
                apply MonoidHom.ext
                intro x
                show y⁻¹ * (y * x * y⁻¹) * y = x
                group,
              Subgroup.map_id] at h1
          exact hjT (hinj hEjj'' ▸ hj''S)
        refine ⟨j', hj'T, ?_⟩
        have hc := CFSG.Quasithin.Asc81c.commSub_map_conj (E j) y
        rw [hj'] at hc
        exact hc
      have hsupVS : (⨆ j ∈ S, U j) ⊔ (⨆ j ∈ Sᶜ, U j) = ⊤ := by
        have hunion := iSup_union (f := U) (s := S) (t := Sᶜ)
        rw [Set.union_compl_self, iSup_univ] at hunion
        exact hunion.symm.trans hspan
      have hVS_ne : (⨆ j ∈ S, U j) ≠ ⊤ := by
        intro hVS
        have h6 : rk ↥(⨆ j ∈ S, U j) = 6 := by rw [hVS]; exact hrk
        have h4 := hrk_proper S hne
        omega
      have hVT_ne : (⨆ j ∈ Sᶜ, U j) ≠ ⊤ := by
        intro hVT
        have h6 : rk ↥(⨆ j ∈ Sᶜ, U j) = 6 := by rw [hVT]; exact hrk
        have h4 : rk ↥(⨆ j ∈ Sᶜ, U j) ≤ 4 := by
          apply hrk_proper Sᶜ
          intro hc
          have hmem : (0 : Fin 3) ∈ Sᶜ := by rw [hc]; exact Set.mem_univ _
          exact hmem h0S
        omega
      rcases hbasic.1 (⨆ j ∈ S, U j) (⨆ j ∈ Sᶜ, U j) hStabS hStabT hsupVS with h | h
      · exact hVS_ne h
      · exact hVT_ne h
    intro i j
    have hi : i ∈ S := by rw [hS_univ]; exact Set.mem_univ i
    have hj : j ∈ S := by rw [hS_univ]; exact Set.mem_univ j
    obtain ⟨g₁, hg₁M, hg₁⟩ := hi
    obtain ⟨g₂, hg₂M, hg₂⟩ := hj
    refine ⟨g₂ * g₁⁻¹, Mb.mul_mem hg₂M (Mb.inv_mem hg₁M), ?_⟩
    rw [← hg₁, Subgroup.map_map]
    have hcomp : (MulAut.conj (g₂ * g₁⁻¹)).toMonoidHom.comp
        (MulAut.conj g₁).toMonoidHom = (MulAut.conj g₂).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      show (g₂ * g₁⁻¹) * (g₁ * x * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * x * g₂⁻¹
      group
    rw [hcomp, hg₂]
  have hnoninvol : ∀ t ∈ Mb, t ^ 2 = 1 → t ≠ 1 →
      ∃ i, ⁅E i, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro t htM ht2 ht1
    have htφ2 : φ t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
    have htφ1 : φ t ≠ 1 := fun hcon => ht1 (φ.injective (by rw [hcon, map_one]))
    obtain ⟨i, d, hd, hne⟩ := s16k_exists_noncomm_coord htφ2 htφ1
    refine ⟨i, fun hbot => hne ?_⟩
    have hx : φ.symm d ∈ E i := Subgroup.mem_map.2 ⟨d, hd, rfl⟩
    have hmem : ⁅φ.symm d, t⁆ ∈ ⁅E i, Subgroup.zpowers t⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t)
    rw [hbot] at hmem
    have h1 : ⁅φ.symm d, t⁆ = 1 := Subgroup.mem_bot.1 hmem
    have hcomm : φ.symm d * t = t * φ.symm d :=
      commutatorElement_eq_one_iff_commute.1 h1
    have h := congrArg (fun x => φ x) hcomm.symm
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  refine ⟨E, ?_⟩
  refine ⟨hEM, hcyc, hcore, hrk2, hcomm, hcent, hindep, hspan, hinj, hperm,
    htrans, hnoninvol⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
