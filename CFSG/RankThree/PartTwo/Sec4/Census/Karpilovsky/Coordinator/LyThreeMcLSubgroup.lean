module

public import CFSG.Sporadic.Recognition.LyonsFinalCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Sporadic.Recognition CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.LyFinal
  CFSG.CosetTable CFSG.Blueprint Subgroup

theorem isBWord_of_mem_RB : ∀ r ∈ RB, isBWord r = true := by decide +kernel

theorem RB_subset_family : ∀ r ∈ RB, r ∈ Rcore107 ++ modularLearned ++ dist2BWords := by
  intro r hr
  have : r ∈ Rcore107 := by
    revert r
    decide +kernel
  simp [this]

theorem not_isBWord_eRelOf : ∀ e ∈ eEvCore, isBWord (eRelOf e) = false := by decide +kernel

theorem not_isBWord_trRel : ∀ ev ∈ trEvCore, isBWord (trRel ev) = false := by decide +kernel

theorem lift_gBs_of_mem_RB :
    ∀ r ∈ RB, FreeGroup.lift gBs (FreeGroup.mk r) = 1 := by
  intro r hr
  have hb : isBWord r = true := isBWord_of_mem_RB r hr
  rcases famRel_core107 r (RB_subset_family r hr) with ⟨-, h⟩ | h | ⟨e, he, h, -⟩ | ⟨ev, hev, h, -⟩
  · exact h
  · subst h
    exact absurd hb (by decide)
  · subst h
    rw [not_isBWord_eRelOf e he] at hb
    exact absurd hb (by decide)
  · subst h
    rw [not_isBWord_trRel ev hev] at hb
    exact absurd hb (by decide)

theorem lift_comp_get {G : Type*} [Group G] {m : ℕ} (S : List (Fin m)) (g : Fin m → G)
    (w : List (Fin m × Bool)) (w' : List (Fin S.length × Bool)) (h : renumber S w = some w') :
    FreeGroup.lift (fun j => g (S.get j)) (FreeGroup.mk w') =
      FreeGroup.lift g (FreeGroup.mk w) := by
  rw [← map_renumber S w w' h]
  clear h
  induction w' with
  | nil => rfl
  | cons l w' ih =>
    rw [show FreeGroup.mk (l :: w') = FreeGroup.mk [l] * FreeGroup.mk w' from rfl, map_mul, ih,
      List.map_cons,
      show FreeGroup.mk ((S.get l.1, l.2) :: List.map (fun l => (S.get l.1, l.2)) w') =
        FreeGroup.mk [(S.get l.1, l.2)] *
          FreeGroup.mk (List.map (fun l => (S.get l.1, l.2)) w') from rfl,
      map_mul, lift_mk_single, lift_mk_single]

abbrev PB : Type := PG (subsetOf 6 [0, 1, 2, 3, 4]).length RB5

noncomputable def homOfRB {G : Type*} [Group G] (g : Fin 6 → G)
    (hg : ∀ r ∈ RB, FreeGroup.lift g (FreeGroup.mk r) = 1) : PB →* G :=
  PresentedGroup.toGroup (f := fun j => g ((subsetOf 6 [0, 1, 2, 3, 4]).get j)) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map, RB5, restrictWords, List.mem_filterMap] at hr
    obtain ⟨w', ⟨w, hw, hren⟩, rfl⟩ := hr
    rw [lift_comp_get _ g w w' hren]
    exact hg w hw)

theorem homOfRB_of {G : Type*} [Group G] (g : Fin 6 → G)
    (hg : ∀ r ∈ RB, FreeGroup.lift g (FreeGroup.mk r) = 1) (j : Fin (subsetOf 6 [0, 1, 2, 3, 4]).length) :
    homOfRB g hg (PresentedGroup.of j) = g ((subsetOf 6 [0, 1, 2, 3, 4]).get j) :=
  PresentedGroup.toGroup.of _

theorem gBs_zero : gBs 0 = Ly0.cB := by
  apply Subtype.ext
  show gB 0 = Ly0.cG
  simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_zero]

theorem gBs_one : gBs 1 = Ly0.dB := by
  apply Subtype.ext
  show gB 1 = Ly0.dG
  simp [gB, genZ, Ly0.letterG_pos, Ly0.gens0_one]

section Embedding

theorem exists_injective_borel_ly_of_relators {R : List (List (Fin 6 × Bool))}
    (hB : ∀ r ∈ RB, r ∈ R) (hbc : RB5Bound)
    (hM : (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
        (subsetOf 6 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk} (subsetOf 6 [0, 1])).index ≤
        9606125)
    (hLy : lyRelCheck R = true) :
    ∃ ι : Ly0.B0 →* NativeSporadic.Ly, Function.Injective ι := by
  classical
  obtain ⟨hfinX, hcardX⟩ := card_PG6_le_of_index hB hbc (T := [0, 1]) (by decide) hM.1 hM.2
  have := hfinX
  have hle : Nat.card (PG 6 R) ≤ 51765179004000000 := by
    norm_num at hcardX ⊢
    exact hcardX
  obtain ⟨e⟩ := nonempty_mulEquiv_of_lyRelCheck hle hLy
  have hXcard : Nat.card (PG 6 R) = 51765179004000000 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly'
  obtain ⟨hfi, hidx⟩ := hM
  obtain ⟨hfin1, hcd⟩ := card_cd_le hB hbc
  set Hc := genSub {r : FreeGroup (Fin 6) | r ∈ R.map FreeGroup.mk}
    (subsetOf 6 [0, 1]) with hHc
  have hmul : Nat.card Hc * Hc.index = Nat.card (PG 6 R) :=
    Subgroup.card_mul_index Hc
  have hHcCard : Nat.card Hc = 5388768000 := by
    by_contra hne
    have hlt : Nat.card Hc < 5388768000 := lt_of_le_of_ne hcd hne
    have h1 := Nat.mul_le_mul (Nat.le_pred_of_lt hlt) hidx
    rw [hmul, hXcard] at h1
    norm_num at h1
  obtain ⟨hfin5, hcard5⟩ := hbc
  have : Finite PB := hfin5
  have htab := Ly0.tabCheck_eq_true
  have hcov := Ly0.coverCheck_eq_true
  have hstr := Ly0.structCheck_eq_true
  have hRB : ∀ r ∈ RB, FreeGroup.lift gBs (FreeGroup.mk r) = 1 := lift_gBs_of_mem_RB
  have hRX : ∀ r ∈ RB, FreeGroup.lift (fun i : Fin 6 =>
      (PresentedGroup.of i : PG 6 R)) (FreeGroup.mk r) = 1 := by
    intro r hr
    have hmk : FreeGroup.lift (fun i : Fin 6 =>
        (PresentedGroup.of i : PG 6 R)) =
        PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ R.map
          FreeGroup.mk} := by
      apply FreeGroup.ext_hom
      intro i
      simp [PresentedGroup.of]
    rw [hmk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hB r hr))
  let σ : PB →* Ly0.B0 := homOfRB gBs hRB
  let θ : PB →* PG 6 R := homOfRB _ hRX
  have hσ : Function.Surjective σ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Ly0.closure_cB_dB, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · refine ⟨PresentedGroup.of ⟨0, by decide⟩, ?_⟩
      rw [homOfRB_of]
      exact gBs_zero
    · refine ⟨PresentedGroup.of ⟨1, by decide⟩, ?_⟩
      rw [homOfRB_of]
      exact gBs_one
  have hσinj : Function.Injective σ :=
    (hσ.bijective_of_nat_card_le (by rw [Ly0.card_B0 htab hcov hstr]; exact hcard5)).1
  have hHcle : Hc ≤ θ.range := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hiS : i ∈ subsetOf 6 [0, 1, 2, 3, 4] := by
      revert i
      decide
    obtain ⟨j, hj⟩ := List.get_of_mem hiS
    exact ⟨PresentedGroup.of j, by rw [homOfRB_of]; exact congrArg PresentedGroup.of hj⟩
  have hθinj : Function.Injective θ := by
    have hcardle : Nat.card PB ≤ Nat.card θ.range :=
      calc Nat.card PB ≤ 5388768000 := hcard5
        _ = Nat.card Hc := hHcCard.symm
        _ ≤ Nat.card θ.range := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hHcle)
    have := (θ.rangeRestrict_surjective.bijective_of_nat_card_le hcardle).1
    exact fun a b hab => this (Subtype.ext hab)
  let τ : Ly0.B0 ≃* PB := (MulEquiv.ofBijective σ ⟨hσinj, hσ⟩).symm
  let ι : Ly0.B0 →* NativeSporadic.Ly :=
    (MonoidHom.ofClass e.symm).comp (θ.comp (MonoidHom.ofClass τ))
  refine ⟨ι, ?_⟩
  intro a b hab
  exact τ.injective (hθinj (e.symm.injective hab))

theorem exists_injective_borel_ly :
    ∃ ι : Ly0.B0 →* NativeSporadic.Ly, Function.Injective ι :=
  exists_injective_borel_ly_of_relators rb_mem_modularR
    rb5Bound_holds index_cd_modularR lyRelCheck_modularR_eq_true

theorem exists_subgroup_ly_mclCover :
    ∃ H : Subgroup NativeSporadic.Ly, ¬ 3 ∣ H.index ∧
      Nonempty (H ≃* McLMultiplier.MclCover) := by
  obtain ⟨ι, hι⟩ := exists_injective_borel_ly
  have htab := Ly0.tabCheck_eq_true
  have hcov := Ly0.coverCheck_eq_true
  have hstr := Ly0.structCheck_eq_true
  let eH : Ly0.K0 ≃* (Ly0.K0.map ι) := Subgroup.equivMapOfInjective Ly0.K0 ι hι
  have hHcard : Nat.card (Ly0.K0.map ι) = 2694384000 := by
    rw [← Nat.card_congr eH.toEquiv]
    exact Ly0.card_K0 htab hcov hstr
  refine ⟨Ly0.K0.map ι, ?_, ⟨eH.symm.trans (Ly0.K0EquivCover htab hcov hstr)⟩⟩
  have h := Subgroup.card_mul_index (Ly0.K0.map ι)
  rw [hHcard, CFSG.Sporadic.Ly.card_Ly'] at h
  have hidx : (Ly0.K0.map ι).index = 19212250 := by omega
  rw [hidx]
  norm_num

end Embedding

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
