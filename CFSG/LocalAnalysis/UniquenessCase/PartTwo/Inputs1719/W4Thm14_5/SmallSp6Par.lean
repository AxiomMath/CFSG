module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas
import CFSG.Quasithin.EmptyFaithful.S151ZH
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Perfect
import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem spFlagLeviBlock_eq_bot_of_len_one {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ)
    {j : Fin (3 + 1)} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I)
    (hlen : (j : ℕ) - spFlagPrev I j = 1) : spFlagLeviBlock (K := K) hI t j = ⊥ := by
  rw [spFlagLeviBlock_of_mem hI hj0 hj, MonoidHom.range_comp,
    KTabD.range_toGL_eq_bot_of_eq_one hlen, Subgroup.map_bot]

omit [Finite K] [CharP K 2] in
private theorem spFlagLeviBlock_zero_eq_bot_of_three {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) :
    spFlagLeviBlock (K := K) hI 3 0 = ⊥ := by
  rw [spFlagLeviBlock_of_eq_zero hI rfl]
  have : Subsingleton ↥(StatedSp (3 - 3) K) := ⟨fun a b => Subtype.ext (Units.ext
    (Matrix.ext fun i _ => i.elim (fun i => i.elim0) fun i => i.elim0))⟩
  rw [Subgroup.eq_bot_iff_forall]
  rintro _ ⟨x, -, rfl⟩
  rw [Subsingleton.elim x 1, map_one]

private theorem pCore_statedSp_eq_bot {m : ℕ} (hm : 1 ≤ m) (hK : 4 ≤ Nat.card K) :
    CFSG.pCore 2 ↥(StatedSp m K) = ⊥ := by
  have hq := spFlag_isQuasisimple_Sp (K := K) hm (Or.inl hK)
  exact eq_bot_iff.mpr ((CFSG.Quasithin.zb_pCore_le_center hq).trans
    (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot hm).le)

theorem nonempty_bar2_hinf_spFlagStab_three_one (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {1})) ≃* ↥(StatedSp 2 K)) := by
  have hI : ∀ i ∈ ({1} : Set ℕ), i ≤ 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have hI1 : ∀ i ∈ ({1} : Set ℕ), 1 ≤ i := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have htI : (1 : ℕ) ∈ ({1} : Set ℕ) := rfl
  have hmax : ∀ c ∈ ({1} : Set ℕ), c ≤ 1 := fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 0 → spFlagLeviBlock (K := K) hI 1 j = ⊥ := by
    intro j hj0
    have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
    by_cases hj1 : (j : ℕ) = 1
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 1 hj0' (by rw [hj1]; rfl) ?_
      rw [hj1, spFlagPrev_singleton]
    · exact spFlagLeviBlock_of_not_mem hI hj0' fun h => hj1 h
  have hcomm_top : commutator (StatedSp (3 - 1) K) = ⊤ :=
    (spFlag_isQuasisimple_Sp (K := K) (m := 3 - 1) (by norm_num) (Or.inl hK)).1
  let e : ↥(spFlagLeviBlock (K := K) hI 1 0) ≃* ↥(StatedSp 2 K) :=
    (spFlagLeviBlockZeroEquiv (K := K) hI 1 (j := 0) rfl).trans
      ((MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv)
  have hperf : Group.IsPerfect ↥(StatedSp 2 K) := Group.isPerfect_def.mpr
    (spFlag_isQuasisimple_Sp (K := K) (m := 2) (by norm_num) (Or.inl hK)).1
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 0 (spFlagLeviBlock (K := K) hI 1) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e hperf (pCore_statedSp_eq_bot (by norm_num) hK)
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_spFlagStab_three_one_two (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {1, 2})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hI : ∀ i ∈ ({1, 2} : Set ℕ), i ≤ 3 := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have hI1 : ∀ i ∈ ({1, 2} : Set ℕ), 1 ≤ i := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have htI : (2 : ℕ) ∈ ({1, 2} : Set ℕ) := Or.inr rfl
  have hmax : ∀ c ∈ ({1, 2} : Set ℕ), c ≤ 2 := fun c hc => by
    rcases hc with rfl | rfl <;> omega
  have hprev1 : spFlagPrev ({1, 2} : Set ℕ) 1 = 0 := by
    have := spFlagPrev_le ({1, 2} : Set ℕ) 1
    omega
  have hprev2 : spFlagPrev ({1, 2} : Set ℕ) 2 = 1 := by
    have h1 := spFlagPrev_le ({1, 2} : Set ℕ) 2
    have h2 := le_spFlagPrev (I := ({1, 2} : Set ℕ)) (b := 2) (c := 1) (Or.inl rfl) (by norm_num)
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 0 → spFlagLeviBlock (K := K) hI 2 j = ⊥ := by
    intro j hj0
    have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
    by_cases hj1 : (j : ℕ) = 1
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 2 hj0' (by rw [hj1]; exact Or.inl rfl) ?_
      rw [hj1, hprev1]
    by_cases hj2 : (j : ℕ) = 2
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 2 hj0' (by rw [hj2]; exact Or.inr rfl) ?_
      rw [hj2, hprev2]
    · refine spFlagLeviBlock_of_not_mem hI hj0' ?_
      rintro (h | h)
      · exact hj1 h
      · exact hj2 h
  have hcomm_top : commutator (StatedSp (3 - 2) K) = ⊤ :=
    (spFlag_isQuasisimple_Sp (K := K) (m := 3 - 2) (by norm_num) (Or.inl hK)).1
  let e : ↥(spFlagLeviBlock (K := K) hI 2 0) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((spFlagLeviBlockZeroEquiv (K := K) hI 2 (j := 0) rfl).trans
      ((MulEquiv.subgroupCongr hcomm_top).trans Subgroup.topEquiv)).trans statedSpOneEquiv
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 0 (spFlagLeviBlock (K := K) hI 2) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_spFlagStab_three_one_three (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {1, 3})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hI : ∀ i ∈ ({1, 3} : Set ℕ), i ≤ 3 := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have hI1 : ∀ i ∈ ({1, 3} : Set ℕ), 1 ≤ i := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have htI : (3 : ℕ) ∈ ({1, 3} : Set ℕ) := Or.inr rfl
  have hmax : ∀ c ∈ ({1, 3} : Set ℕ), c ≤ 3 := fun c hc => by
    rcases hc with rfl | rfl <;> omega
  have hprev1 : spFlagPrev ({1, 3} : Set ℕ) 1 = 0 := by
    have := spFlagPrev_le ({1, 3} : Set ℕ) 1
    omega
  have hprev3 : spFlagPrev ({1, 3} : Set ℕ) 3 = 1 := by
    have h1 := spFlagPrev_le ({1, 3} : Set ℕ) 3
    have h2 := le_spFlagPrev (I := ({1, 3} : Set ℕ)) (b := 3) (c := 1) (Or.inl rfl) (by norm_num)
    rcases spFlagPrev_mem ({1, 3} : Set ℕ) 3 with h | h | h
    · omega
    · exact h
    · rw [Set.mem_singleton_iff] at h
      omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 3 → spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
    intro j hj3
    have hj3' : (j : ℕ) ≠ 3 := fun h => hj3 (Fin.ext h)
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext hj0
      rw [hj]
      exact spFlagLeviBlock_zero_eq_bot_of_three hI
    by_cases hj1 : (j : ℕ) = 1
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 3 hj0 (by rw [hj1]; exact Or.inl rfl) ?_
      rw [hj1, hprev1]
    · refine spFlagLeviBlock_of_not_mem hI hj0 ?_
      rintro (h | h)
      · exact hj1 h
      · exact hj3' h
  have hlen :
      ((3 : Fin (3 + 1)) : ℕ) - spFlagPrev ({1, 3} : Set ℕ) ((3 : Fin (3 + 1)) : ℕ) = 2 := by
    change 3 - spFlagPrev ({1, 3} : Set ℕ) 3 = 2
    rw [hprev3]
  let e : ↥(spFlagLeviBlock (K := K) hI 3 3) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (spFlagLeviBlockMemEquiv (K := K) hI 3 (j := 3) (by decide) htI).trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen)
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 3 (spFlagLeviBlock (K := K) hI 3) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_spFlagStab_three_two_three (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {2, 3})) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hI : ∀ i ∈ ({2, 3} : Set ℕ), i ≤ 3 := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have hI1 : ∀ i ∈ ({2, 3} : Set ℕ), 1 ≤ i := fun i hi => by
    rcases hi with rfl | rfl <;> omega
  have htI : (3 : ℕ) ∈ ({2, 3} : Set ℕ) := Or.inr rfl
  have hmax : ∀ c ∈ ({2, 3} : Set ℕ), c ≤ 3 := fun c hc => by
    rcases hc with rfl | rfl <;> omega
  have hprev2 : spFlagPrev ({2, 3} : Set ℕ) 2 = 0 := by
    have h1 := spFlagPrev_le ({2, 3} : Set ℕ) 2
    rcases spFlagPrev_mem ({2, 3} : Set ℕ) 2 with h | h | h
    · exact h
    · omega
    · rw [Set.mem_singleton_iff] at h
      omega
  have hprev3 : spFlagPrev ({2, 3} : Set ℕ) 3 = 2 := by
    have h1 := spFlagPrev_le ({2, 3} : Set ℕ) 3
    have h2 := le_spFlagPrev (I := ({2, 3} : Set ℕ)) (b := 3) (c := 2) (Or.inl rfl) (by norm_num)
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 2 → spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
    intro j hj2
    have hj2' : (j : ℕ) ≠ 2 := fun h => hj2 (Fin.ext h)
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext hj0
      rw [hj]
      exact spFlagLeviBlock_zero_eq_bot_of_three hI
    by_cases hj3 : (j : ℕ) = 3
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 3 hj0 (by rw [hj3]; exact Or.inr rfl) ?_
      rw [hj3, hprev3]
    · refine spFlagLeviBlock_of_not_mem hI hj0 ?_
      rintro (h | h)
      · exact hj2' h
      · exact hj3 h
  have hlen :
      ((2 : Fin (3 + 1)) : ℕ) - spFlagPrev ({2, 3} : Set ℕ) ((2 : Fin (3 + 1)) : ℕ) = 2 := by
    change 2 - spFlagPrev ({2, 3} : Set ℕ) 2 = 2
    rw [hprev2]
  let e : ↥(spFlagLeviBlock (K := K) hI 3 2) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (spFlagLeviBlockMemEquiv (K := K) hI 3 (j := 2) (by decide) (Or.inl rfl)).trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen)
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 2 (spFlagLeviBlock (K := K) hI 3) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)
    (pCore_specialLinearGroup_eq_bot 2)
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

private theorem hinf_eq_bot_of_leviHom_solvable {G : Type} [Group G] [Finite G] {ι : Type}
    {M : ι → Type} [∀ i, Group (M i)] (P : Subgroup G) (β : ↥P →* ∀ i, M i)
    (hker : IsPGroup 2 ↥β.ker) (B : ∀ i, Subgroup (M i))
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B)
    (hB : ∀ i, Group.IsSolvable ↥(B i)) : Hinf P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Hinf_eq_perfectCore]
  set C := CFSG.Quasithin.perfectCore P with hCdef
  have hCP : C ≤ P := CFSG.Quasithin.perfectCore_le P
  have hCperf : ⁅C, C⁆ = C := CFSG.Quasithin.perfectCore_perfect P
  set C' : Subgroup ↥P := C.subgroupOf P with hC'
  have hC'map : C'.map P.subtype = C := by
    rw [hC', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCP]
  have hC'perf : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, hC'map, hCperf]
  set D := C'.map β with hD
  have hDperf : ⁅D, D⁆ = D := by rw [hD, ← Subgroup.map_commutator, hC'perf]
  have hDB : D ≤ Subgroup.pi Set.univ B := by
    rw [← hDperf]
    exact (Subgroup.commutator_mono (Subgroup.map_le_range β C') (Subgroup.map_le_range β C')).trans
      hcomm
  have hDbot : D = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    funext i
    have hEi : D.map (Pi.evalMonoidHom M i) ≤ B i := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_pi Set.univ).mp (hDB hy) i (Set.mem_univ i)
    have hEperf : ⁅D.map (Pi.evalMonoidHom M i), D.map (Pi.evalMonoidHom M i)⁆ =
        D.map (Pi.evalMonoidHom M i) := by
      rw [← Subgroup.map_commutator, hDperf]
    have hEbot : D.map (Pi.evalMonoidHom M i) = ⊥ := by
      by_contra hne
      have : Group.IsPerfect ↥(D.map (Pi.evalMonoidHom M i)) := Subgroup.isPerfect_iff.mpr hEperf
      have : Nontrivial ↥(D.map (Pi.evalMonoidHom M i)) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      exact Group.IsPerfect.not_isSolvable ↥(D.map (Pi.evalMonoidHom M i))
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hEi)
          (Subgroup.inclusion_injective hEi))
    have hxi : Pi.evalMonoidHom M i x ∈ D.map (Pi.evalMonoidHom M i) := ⟨x, hx, rfl⟩
    rw [hEbot, Subgroup.mem_bot] at hxi
    exact hxi
  have hC'ker : C' ≤ β.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    have : β x ∈ D := ⟨x, hx, rfl⟩
    rwa [hDbot, Subgroup.mem_bot] at this
  have hC'sol : Group.IsSolvable ↥C' := by
    have := (hker.to_le hC'ker).isNilpotent
    infer_instance
  have hC'bot : C' = ⊥ := by
    by_contra hne
    have : Group.IsPerfect ↥C' := Subgroup.isPerfect_iff.mpr hC'perf
    have : Nontrivial ↥C' := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥C' hC'sol
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hCP hx⟩ : ↥P) ∈ C' := hx
  rw [hC'bot, Subgroup.mem_bot] at hx'
  exact congrArg Subtype.val hx'

omit [Finite K] [CharP K 2] in
private theorem isSolvable_spFlagLeviBlock_of_len_two [Finite K] (hK2 : Nat.card K = 2)
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (t : ℕ) {j : Fin (3 + 1)} (hj0 : (j : ℕ) ≠ 0)
    (hj : (j : ℕ) ∈ I) (hlen : (j : ℕ) - spFlagPrev I j = 2) :
    Group.IsSolvable ↥(spFlagLeviBlock (K := K) hI t j) := by
  have := CFSG.SeitzReduction.SymplecticPilot.isSolvable_SL2_of_natCard_two hK2
  let e : ↥(spFlagLeviBlock (K := K) hI t j) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (spFlagLeviBlockMemEquiv (K := K) hI t hj0 hj).trans
      (MulEquiv.cast (M := fun m : ℕ => Matrix.SpecialLinearGroup (Fin m) K) hlen)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

omit [Finite K] [CharP K 2] in
private theorem isSolvable_spFlagLeviBlock_zero_of_two [Finite K] (hK2 : Nat.card K = 2)
    {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) :
    Group.IsSolvable ↥(spFlagLeviBlock (K := K) hI 2 0) := by
  have := CFSG.SeitzReduction.SymplecticPilot.isSolvable_SL2_of_natCard_two hK2
  have hsp : Group.IsSolvable ↥(StatedSp (3 - 2) K) :=
    Group.isSolvable_of_isSolvable_injective (f := statedSpOneEquiv.toMonoidHom)
      statedSpOneEquiv.injective
  have hc : Group.IsSolvable ↥(commutator ↥(StatedSp (3 - 2) K)) := inferInstance
  let e := spFlagLeviBlockZeroEquiv (K := K) hI 2 (j := 0) rfl
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem hinf_spFlagStab_three_one_two_three :
    Hinf (SymplecticHigher.flagStabilizer 3 K {1, 2, 3}) = ⊥ := by
  have hI : ∀ i ∈ ({1, 2, 3} : Set ℕ), i ≤ 3 := fun i hi => by
    rcases hi with rfl | rfl | rfl <;> omega
  have hI1 : ∀ i ∈ ({1, 2, 3} : Set ℕ), 1 ≤ i := fun i hi => by
    rcases hi with rfl | rfl | rfl <;> omega
  have htI : (3 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := Or.inr (Or.inr rfl)
  have hprev : ∀ b : ℕ, 1 ≤ b → b ≤ 3 → spFlagPrev ({1, 2, 3} : Set ℕ) b = b - 1 := by
    intro b hb1 hb3
    have h1 := spFlagPrev_le ({1, 2, 3} : Set ℕ) b
    rcases Nat.lt_or_ge 1 b with hb | hb
    · have hmem : b - 1 ∈ ({1, 2, 3} : Set ℕ) := by
        rcases (by omega : b - 1 = 1 ∨ b - 1 = 2) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      have h2 := le_spFlagPrev hmem (by omega : b - 1 < b)
      omega
    · omega
  refine hinf_eq_bot_of_leviHom_solvable _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) (spFlagLeviBlock (K := K) hI 3)
    (commutator_range_spFlagLeviHom_le hI htI) fun j => ?_
  have hbot : spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext hj0
      rw [hj]
      exact spFlagLeviBlock_zero_eq_bot_of_three hI
    have hj3 : (j : ℕ) ≤ 3 := Nat.lt_succ_iff.mp j.2
    have hjI : (j : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by
      rcases (by omega : (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    refine spFlagLeviBlock_eq_bot_of_len_one hI 3 hj0 hjI ?_
    rw [hprev j (by omega) hj3]
    omega
  rw [hbot]
  infer_instance

theorem hinf_spFlagStab_three_eq_bot_of_card_two (hK2 : Nat.card K = 2) {I : Set ℕ}
    (hI4 : I = {2} ∨ I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3}) :
    Hinf (SymplecticHigher.flagStabilizer 3 K I) = ⊥ := by
  rcases hI4 with rfl | rfl | rfl | rfl
  ·
    have hI : ∀ i ∈ ({2} : Set ℕ), i ≤ 3 := fun i hi => by
      rw [Set.mem_singleton_iff] at hi
      omega
    have hI1 : ∀ i ∈ ({2} : Set ℕ), 1 ≤ i := fun i hi => by
      rw [Set.mem_singleton_iff] at hi
      omega
    have htI : (2 : ℕ) ∈ ({2} : Set ℕ) := rfl
    refine hinf_eq_bot_of_leviHom_solvable _ (spFlagLeviHom (K := K) hI htI)
      (isPGroup_ker_spFlagLeviHom hI htI hI1) (spFlagLeviBlock (K := K) hI 2)
      (commutator_range_spFlagLeviHom_le hI htI) fun j => ?_
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext hj0
      rw [hj]
      exact isSolvable_spFlagLeviBlock_zero_of_two hK2 hI
    by_cases hj2 : (j : ℕ) = 2
    · refine isSolvable_spFlagLeviBlock_of_len_two hK2 hI 2 hj0 hj2 ?_
      rw [hj2, spFlagPrev_singleton]
    · rw [spFlagLeviBlock_of_not_mem hI hj0 hj2]
      infer_instance
  ·
    have hI : ∀ i ∈ ({1, 2} : Set ℕ), i ≤ 3 := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have hI1 : ∀ i ∈ ({1, 2} : Set ℕ), 1 ≤ i := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have htI : (2 : ℕ) ∈ ({1, 2} : Set ℕ) := Or.inr rfl
    have hprev1 : spFlagPrev ({1, 2} : Set ℕ) 1 = 0 := by
      have := spFlagPrev_le ({1, 2} : Set ℕ) 1
      omega
    have hprev2 : spFlagPrev ({1, 2} : Set ℕ) 2 = 1 := by
      have h1 := spFlagPrev_le ({1, 2} : Set ℕ) 2
      have h2 := le_spFlagPrev (I := ({1, 2} : Set ℕ)) (b := 2) (c := 1) (Or.inl rfl)
        (by norm_num)
      omega
    refine hinf_eq_bot_of_leviHom_solvable _ (spFlagLeviHom (K := K) hI htI)
      (isPGroup_ker_spFlagLeviHom hI htI hI1) (spFlagLeviBlock (K := K) hI 2)
      (commutator_range_spFlagLeviHom_le hI htI) fun j => ?_
    by_cases hj0 : (j : ℕ) = 0
    · have hj : j = 0 := Fin.ext hj0
      rw [hj]
      exact isSolvable_spFlagLeviBlock_zero_of_two hK2 hI
    have hbot : spFlagLeviBlock (K := K) hI 2 j = ⊥ := by
      by_cases hj1 : (j : ℕ) = 1
      · refine spFlagLeviBlock_eq_bot_of_len_one hI 2 hj0 (by rw [hj1]; exact Or.inl rfl) ?_
        rw [hj1, hprev1]
      by_cases hj2 : (j : ℕ) = 2
      · refine spFlagLeviBlock_eq_bot_of_len_one hI 2 hj0 (by rw [hj2]; exact Or.inr rfl) ?_
        rw [hj2, hprev2]
      · refine spFlagLeviBlock_of_not_mem hI hj0 ?_
        rintro (h | h)
        · exact hj1 h
        · exact hj2 h
    rw [hbot]
    infer_instance
  ·
    have hI : ∀ i ∈ ({1, 3} : Set ℕ), i ≤ 3 := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have hI1 : ∀ i ∈ ({1, 3} : Set ℕ), 1 ≤ i := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have htI : (3 : ℕ) ∈ ({1, 3} : Set ℕ) := Or.inr rfl
    have hprev1 : spFlagPrev ({1, 3} : Set ℕ) 1 = 0 := by
      have := spFlagPrev_le ({1, 3} : Set ℕ) 1
      omega
    have hprev3 : spFlagPrev ({1, 3} : Set ℕ) 3 = 1 := by
      have h1 := spFlagPrev_le ({1, 3} : Set ℕ) 3
      have h2 := le_spFlagPrev (I := ({1, 3} : Set ℕ)) (b := 3) (c := 1) (Or.inl rfl)
        (by norm_num)
      rcases spFlagPrev_mem ({1, 3} : Set ℕ) 3 with h | h | h
      · omega
      · exact h
      · rw [Set.mem_singleton_iff] at h
        omega
    refine hinf_eq_bot_of_leviHom_solvable _ (spFlagLeviHom (K := K) hI htI)
      (isPGroup_ker_spFlagLeviHom hI htI hI1) (spFlagLeviBlock (K := K) hI 3)
      (commutator_range_spFlagLeviHom_le hI htI) fun j => ?_
    by_cases hj3 : (j : ℕ) = 3
    · refine isSolvable_spFlagLeviBlock_of_len_two hK2 hI 3 (by omega)
        (by rw [hj3]; exact Or.inr rfl) ?_
      rw [hj3, hprev3]
    have hbot : spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
      by_cases hj0 : (j : ℕ) = 0
      · have hj : j = 0 := Fin.ext hj0
        rw [hj]
        exact spFlagLeviBlock_zero_eq_bot_of_three hI
      by_cases hj1 : (j : ℕ) = 1
      · refine spFlagLeviBlock_eq_bot_of_len_one hI 3 hj0 (by rw [hj1]; exact Or.inl rfl) ?_
        rw [hj1, hprev1]
      · refine spFlagLeviBlock_of_not_mem hI hj0 ?_
        rintro (h | h)
        · exact hj1 h
        · exact hj3 h
    rw [hbot]
    infer_instance
  ·
    have hI : ∀ i ∈ ({2, 3} : Set ℕ), i ≤ 3 := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have hI1 : ∀ i ∈ ({2, 3} : Set ℕ), 1 ≤ i := fun i hi => by
      rcases hi with rfl | rfl <;> omega
    have htI : (3 : ℕ) ∈ ({2, 3} : Set ℕ) := Or.inr rfl
    have hprev2 : spFlagPrev ({2, 3} : Set ℕ) 2 = 0 := by
      have h1 := spFlagPrev_le ({2, 3} : Set ℕ) 2
      rcases spFlagPrev_mem ({2, 3} : Set ℕ) 2 with h | h | h
      · exact h
      · omega
      · rw [Set.mem_singleton_iff] at h
        omega
    have hprev3 : spFlagPrev ({2, 3} : Set ℕ) 3 = 2 := by
      have h1 := spFlagPrev_le ({2, 3} : Set ℕ) 3
      have h2 := le_spFlagPrev (I := ({2, 3} : Set ℕ)) (b := 3) (c := 2) (Or.inl rfl)
        (by norm_num)
      omega
    refine hinf_eq_bot_of_leviHom_solvable _ (spFlagLeviHom (K := K) hI htI)
      (isPGroup_ker_spFlagLeviHom hI htI hI1) (spFlagLeviBlock (K := K) hI 3)
      (commutator_range_spFlagLeviHom_le hI htI) fun j => ?_
    by_cases hj2 : (j : ℕ) = 2
    · refine isSolvable_spFlagLeviBlock_of_len_two hK2 hI 3 (by omega)
        (by rw [hj2]; exact Or.inl rfl) ?_
      rw [hj2, hprev2]
    have hbot : spFlagLeviBlock (K := K) hI 3 j = ⊥ := by
      by_cases hj0 : (j : ℕ) = 0
      · have hj : j = 0 := Fin.ext hj0
        rw [hj]
        exact spFlagLeviBlock_zero_eq_bot_of_three hI
      by_cases hj3 : (j : ℕ) = 3
      · refine spFlagLeviBlock_eq_bot_of_len_one hI 3 hj0 (by rw [hj3]; exact Or.inr rfl) ?_
        rw [hj3, hprev3]
      · refine spFlagLeviBlock_of_not_mem hI hj0 ?_
        rintro (h | h)
        · exact hj2 h
        · exact hj3 h
    rw [hbot]
    infer_instance

private theorem isPerfect_alt_six : Group.IsPerfect ↥(alternatingGroup (Fin 6)) :=
  Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))

private theorem pCore_alt_six_eq_bot : CFSG.pCore 2 ↥(alternatingGroup (Fin 6)) = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    CFSG.Quasithin.EmptyFaithfulMultiple.AltSix.isSimpleGroup
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (CFSG.pCore_normal (p := 2) (G := ↥(alternatingGroup (Fin 6)))).eq_bot_or_eq_top with
    hbot | htop
  · exact hbot
  · have : Group.IsPerfect ↥(alternatingGroup (Fin 6)) := isPerfect_alt_six
    exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥(alternatingGroup (Fin 6)))).of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).isNilpotent
      (Group.IsPerfect.not_isNilpotent ↥(alternatingGroup (Fin 6)))

theorem nonempty_bar2_hinf_spFlagStab_three_one_of_card_two (hK2 : Nat.card K = 2) :
    Nonempty (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K {1})) ≃*
      ↥(alternatingGroup (Fin 6))) := by
  have hI : ∀ i ∈ ({1} : Set ℕ), i ≤ 3 := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have hI1 : ∀ i ∈ ({1} : Set ℕ), 1 ≤ i := fun i hi => by
    rw [Set.mem_singleton_iff] at hi
    omega
  have htI : (1 : ℕ) ∈ ({1} : Set ℕ) := rfl
  have hmax : ∀ c ∈ ({1} : Set ℕ), c ≤ 1 := fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    omega
  have hB : ∀ j : Fin (3 + 1), j ≠ 0 → spFlagLeviBlock (K := K) hI 1 j = ⊥ := by
    intro j hj0
    have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
    by_cases hj1 : (j : ℕ) = 1
    · refine spFlagLeviBlock_eq_bot_of_len_one hI 1 hj0' (by rw [hj1]; rfl) ?_
      rw [hj1, spFlagPrev_singleton]
    · exact spFlagLeviBlock_of_not_mem hI hj0' fun h => hj1 h
  let e : ↥(spFlagLeviBlock (K := K) hI 1 0) ≃* ↥(alternatingGroup (Fin 6)) :=
    (spFlagLeviBlockZeroEquiv (K := K) hI 1 (j := 0) rfl).trans
      (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  refine KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _ (spFlagLeviHom (K := K) hI htI)
    (isPGroup_ker_spFlagLeviHom hI htI hI1) 0 (spFlagLeviBlock (K := K) hI 1) hB (fun y hy => ?_)
    (commutator_range_spFlagLeviHom_le hI htI) e isPerfect_alt_six pCore_alt_six_eq_bot
  exact pi_le_range_spFlagLeviHom hI htI hmax ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

private theorem le_three_of_two_pow_dvd_360 {k : ℕ} (h : 2 ^ k ∣ 360) : k ≤ 3 := by
  have h1 : 2 ^ k ∣ 2 ^ 3 * 45 := by norm_num [h]
  have h2 : Nat.Coprime (2 ^ k) 45 := Nat.Coprime.pow_left k (by norm_num)
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_right h1)

private theorem not_nParamSingle_of_card_eq_360 {X : Type} [Group X] [Finite X]
    (hX : Nat.card X = 360) {n : ℕ} (hn : 2 < n) : ¬ NParamSingle X n := by
  have hXZ : Nat.card (X ⧸ Subgroup.center X) ∣ 360 := by
    rw [← hX]
    exact Subgroup.card_quotient_dvd_card _
  have h360 : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  have h45 : Odd (45 : ℕ) := by decide
  rintro (hSz | hL2 | hSU3 | hSL3 | hSp4)
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hSz
      (by rw [hX]; norm_num)
  · have hc : Nat.card X = ordA 1 (2 ^ n) :=
      CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hL2
    obtain ⟨r, hr, hm⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordA (n := 1) le_rfl (by omega : 1 ≤ n)).two
    have h1 : 2 ^ (n * (1 * (1 + 1) / 2)) * r = 2 ^ 3 * 45 := by rw [← hm, ← hc, hX, h360]
    have hn3 : n * (1 * (1 + 1) / 2) = 3 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr h45 h1
    have hn3' : n = 3 := by omega
    subst hn3'
    rw [hX] at hc
    exact absurd hc (by decide)
  · have hc : Nat.card (X ⧸ Subgroup.center X) = ordTwistedA 2 (2 ^ n) :=
      CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hSU3.2
    obtain ⟨r, -, hm⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordTwistedA (n := 2) le_rfl (by omega : 1 ≤ n)).two
    have h1 : 2 ^ (n * (2 * (2 + 1) / 2)) ∣ 360 :=
      (Dvd.intro r (by rw [← hm, ← hc])).trans hXZ
    have := le_three_of_two_pow_dvd_360 h1
    omega
  · have hc : Nat.card (X ⧸ Subgroup.center X) = ordA 2 (2 ^ n) :=
      CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hSL3.2
    obtain ⟨r, -, hm⟩ :=
      (CFSG.Timmesfeld.Orders.profile_ordA (n := 2) (by norm_num) (by omega : 1 ≤ n)).two
    have h1 : 2 ^ (n * (2 * (2 + 1) / 2)) ∣ 360 :=
      (Dvd.intro r (by rw [← hm, ← hc])).trans hXZ
    have := le_three_of_two_pow_dvd_360 h1
    omega
  · have hc : Nat.card X = ordBC 2 (2 ^ n) :=
      CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hSp4
    obtain ⟨r, -, hm⟩ := (CFSG.Timmesfeld.Orders.profile_ordBC (n := 2) (by omega : 1 ≤ n)).two
    have h1 : 2 ^ (n * (2 * 2)) ∣ 360 := Dvd.intro r (by rw [← hm, ← hc, hX])
    have := le_three_of_two_pow_dvd_360 h1
    omega

private theorem isQuasisimple_alt_six : CFSG.Open.IsQuasisimple ↥(alternatingGroup (Fin 6)) := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    CFSG.Quasithin.EmptyFaithfulMultiple.AltSix.isSimpleGroup
  have hcomm : commutator ↥(alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have hZ : Subgroup.center ↥(alternatingGroup (Fin 6)) = ⊥ := by
    rcases (Subgroup.center ↥(alternatingGroup (Fin 6))).normal_of_characteristic.eq_bot_or_eq_top
      with h | h
    · exact h
    · exfalso
      have hc : commutator ↥(alternatingGroup (Fin 6)) = ⊥ :=
        (commutator_eq_bot_iff_center_eq_top _).mpr h
      rw [hcomm] at hc
      exact top_ne_bot hc
  refine ⟨hcomm, ?_⟩
  let f : ↥(alternatingGroup (Fin 6)) →* ↥(alternatingGroup (Fin 6)) ⧸
      Subgroup.center ↥(alternatingGroup (Fin 6)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.toMonoidHom
  have hf : Function.Surjective f :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.surjective
  have : Nontrivial (↥(alternatingGroup (Fin 6)) ⧸ Subgroup.center ↥(alternatingGroup (Fin 6))) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective f hf

private theorem card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have h720 : Nat.factorial 6 = 720 := by decide
  omega

private theorem exists_conj_eq_flagStabilizer {Q : Subgroup ↥(StatedSp 3 K)}
    (hQ : IsParabolicTwo ↥(StatedSp 3 K) Q) :
    ∃ (c : ↥(StatedSp 3 K)) (I : Set ℕ), (∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) ∧
      Q.map (MulAut.conj c).toMonoidHom = SymplecticHigher.flagStabilizer 3 K I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 3
  have hUset : (U : Set ↥(StatedSp 3 K)) =
      (SymplecticFlag.unipotent 3 K : Set ↥(StatedSp 3 K)) := congrArg SetLike.coe hU
  obtain ⟨S, hSN⟩ := hQ
  have hSQ : (S : Subgroup ↥(StatedSp 3 K)) ≤ Q := Subgroup.le_normalizer.trans hSN
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥(StatedSp 3 K)) S U
  have hSU : (S : Subgroup ↥(StatedSp 3 K)).map (MulAut.conj c).toMonoidHom = U := by
    have h := congrArg (fun R : Sylow 2 ↥(StatedSp 3 K) => (R : Subgroup ↥(StatedSp 3 K))) hc
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      MulDistribMulAction.toMonoidEnd_apply] at h
    exact h
  have hQ' : IsParabolicTwo ↥(StatedSp 3 K) (Q.map (MulAut.conj c).toMonoidHom) :=
    IsParabolicTwo.map ⟨S, hSN⟩ _ (MulAut.conj c).surjective
  have hUQ' : (U : Subgroup ↥(StatedSp 3 K)) ≤ Q.map (MulAut.conj c).toMonoidHom := by
    rw [← hSU]
    exact Subgroup.map_mono hSQ
  have hB : SymplecticFlag.borelSubgroup 3 K ≤ Q.map (MulAut.conj c).toMonoidHom := by
    rw [← SymplecticHigher.normalizer_unipotent]
    have h := hQ'.normalizer_le U hUQ'
    rwa [hUset] at h
  obtain ⟨hcut, -⟩ := SymplecticHigher.borel_overgroups (K := K) _ hB
  exact ⟨c, _, SymplecticHigher.borelCuts_le _, hcut⟩

theorem nParam_eq_of_lieModel_psp6_parabolic {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} {e n : ℕ} (hS : CFSG.Blueprint.LieModel ↥L .PSp 3 2 e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n)
    (hn : 2 < n) : n = e := by
  classical
  obtain ⟨K, _, _, _, hK, ⟨ψ⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hS
  obtain ⟨c, I, hI, hQ⟩ :=
    exists_conj_eq_flagStabilizer (hpar.map ψ.toMonoidHom ψ.surjective)
  let φ' : ↥(StatedSp 3 K) ≃* ↥L := (MulAut.conj c).symm.trans ψ.symm
  have hPQ : P.subgroupOf L = (SymplecticHigher.flagStabilizer 3 K I).map φ'.toMonoidHom := by
    rw [← hQ, Subgroup.map_map, Subgroup.map_map]
    have hid : (φ'.toMonoidHom.comp (MulAut.conj c).toMonoidHom).comp ψ.toMonoidHom =
        MonoidHom.id ↥L := by
      ext x
      simp [φ']
      group
    rw [hid, Subgroup.map_id]
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPL φ' hPQ
  have hQne : Hinf (SymplecticHigher.flagStabilizer 3 K I) ≠ ⊥ := by
    intro h
    apply hinf
    have hPeq : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
    rw [← hPeq, ← Hinf_map L.subtype, hPQ, Hinf_map_eq_bot φ' _ h, Subgroup.map_bot]
  have he1 : 1 ≤ e := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [hK, h0] at h2
      norm_num at h2
    · exact h0
  have hK4 : 2 ≤ e → 4 ≤ Nat.card K := fun he2 => by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
  have hK2 : e = 1 → Nat.card K = 2 := fun he1' => by rw [hK, he1', pow_one]
  have hsl2 : 2 ≤ e → (Bar2 (Hinf (SymplecticHigher.flagStabilizer 3 K I)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) → n = e := fun he2 ε =>
    kNshape_holds _ _ n e hN (Or.inl (KTabD.isL2_of_mulEquiv_sl2 he2 hK (χ.trans ε)))
  have hcut : ∀ i ∈ I, 1 ≤ i ∧ i < 4 := fun i hi => ⟨(hI i hi).1, by have := (hI i hi).2; omega⟩
  rcases cuts_four_cases hcut with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    rw [SymplecticHigher.flagStabilizer_empty] at χ
    have hq3 : CFSG.Open.IsQuasisimple ↥(StatedSp 3 K) :=
      spFlag_isQuasisimple_Sp (K := K) (m := 3) (by norm_num) (Or.inr le_rfl)
    have hperf : ⁅(⊤ : Subgroup ↥(StatedSp 3 K)), ⊤⁆ = ⊤ := hq3.1
    have hO2 : CFSG.pCore 2 ↥(⊤ : Subgroup ↥(StatedSp 3 K)) = ⊥ := by
      have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥(StatedSp 3 K)) :=
        (CFSG.Open.IsQuasisimple.congr Subgroup.topEquiv).mpr hq3
      have hZ : Subgroup.center ↥(⊤ : Subgroup ↥(StatedSp 3 K)) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : Subgroup.topEquiv x ∈ Subgroup.center ↥(StatedSp 3 K) := by
          rw [Subgroup.mem_center_iff] at hx ⊢
          intro g
          have := hx (Subgroup.topEquiv.symm g)
          simpa using congrArg Subgroup.topEquiv this
        rw [CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num),
          Subgroup.mem_bot] at hx'
        rw [Subgroup.mem_bot]
        exact Subgroup.topEquiv.injective (hx'.trans (map_one _).symm)
      exact eq_bot_iff.mpr ((CFSG.Quasithin.zb_pCore_le_center hq).trans hZ.le)
    obtain ⟨χ₀⟩ := nonempty_bar2_hinf_equiv_of_eq (rfl : (⊤ : Subgroup ↥(StatedSp 3 K)) = ⊤)
      hperf hO2
    let ε : Bar2 (Hinf P) ≃* ↥(StatedSp 3 K) := (χ.trans χ₀).trans Subgroup.topEquiv
    have hSp : IsSpn (Bar2 (Hinf P)) 6 e := ⟨⟨3, rfl⟩, K, inferInstance, inferInstance, hK, ⟨ε⟩⟩
    have hq : CFSG.Open.IsQuasisimple (Bar2 (Hinf P)) :=
      (CFSG.Open.IsQuasisimple.congr ε).mpr hq3
    exact not_nParamSingle_of_isSpn_six hSp he1 (nParamSingle_of_nParam_of_isQuasisimple hN hq)
  ·
    rcases Nat.lt_or_ge e 2 with he | he2
    · exfalso
      have he1' : e = 1 := by omega
      obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_one_of_card_two (hK2 he1')
      have hq : CFSG.Open.IsQuasisimple (Bar2 (Hinf P)) :=
        (CFSG.Open.IsQuasisimple.congr (χ.trans ε)).mpr isQuasisimple_alt_six
      have hcard : Nat.card (Bar2 (Hinf P)) = 360 := by
        rw [Nat.card_congr (χ.trans ε).toEquiv, card_alt_six]
      exact not_nParamSingle_of_card_eq_360 hcard hn (nParamSingle_of_nParam_of_isQuasisimple hN hq)
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_one (hK4 he2)
      have hSp4 : IsSp4 (Bar2 (Hinf P)) e :=
        CFSG.SeitzReduction.SymplecticPilot.lieModel_of_mulEquiv_statedSp (χ.trans ε) hK le_rfl
          (fun h => by simp at h; omega)
      exact nParam_eq_of_isSp4 hN hSp4 he2
  ·
    rcases Nat.lt_or_ge e 2 with he | he2
    · exact (hQne (hinf_spFlagStab_three_eq_bot_of_card_two (hK2 (by omega))
        (Or.inl rfl))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_two (hK4 he2)
      exact nParam_eq_of_mulEquiv_sl2_prod he2 hK hN (χ.trans ε)
  ·
    obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_three (K := K)
    rcases Nat.lt_or_ge e 2 with he | he2
    · have he1' : e = 1 := by omega
      subst he1'
      exact nParam_eq_of_isSL3 hN (isSL3_of_mulEquiv_sl3_of_card_two (hK2 rfl) (χ.trans ε))
    · exact nParam_eq_of_mulEquiv_sl3 he2 hK hN (χ.trans ε)
  ·
    rcases Nat.lt_or_ge e 2 with he | he2
    · exact (hQne (hinf_spFlagStab_three_eq_bot_of_card_two (hK2 (by omega))
        (Or.inr (Or.inl rfl)))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_one_two (hK4 he2)
      exact hsl2 he2 ε
  ·
    rcases Nat.lt_or_ge e 2 with he | he2
    · exact (hQne (hinf_spFlagStab_three_eq_bot_of_card_two (hK2 (by omega))
        (Or.inr (Or.inr (Or.inl rfl))))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_one_three (hK4 he2)
      exact hsl2 he2 ε
  ·
    rcases Nat.lt_or_ge e 2 with he | he2
    · exact (hQne (hinf_spFlagStab_three_eq_bot_of_card_two (hK2 (by omega))
        (Or.inr (Or.inr (Or.inr rfl))))).elim
    · obtain ⟨ε⟩ := nonempty_bar2_hinf_spFlagStab_three_two_three (hK4 he2)
      exact hsl2 he2 ε
  ·
    exact (hQne hinf_spFlagStab_three_one_two_three).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
