module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCoverInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverBounds
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckAction
public import CFSG.Sporadic.Recognition.ONMultiplierTables

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Recognition.CoverTransfer
open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native

abbrev OnGFacts : Prop :=
  Subgroup.closure (Set.range onGF) = ⊤ ∧
    (∀ r ∈ onRels, FreeGroup.lift onGF (FreeGroup.mk r) = 1) ∧
    (∀ i, FreeGroup.lift onGF (FreeGroup.mk (onCommWord i)) = onGF i)

@[expose] noncomputable def gH (i : Fin 4) : J :=
  if i.val < 3 then onGF i else 1

theorem lift_congr_low {G : Type*} [Group G] (f f' : Fin 4 → G)
    (hf : ∀ i : Fin 4, i.val < 3 → f i = f' i) {w : List (Fin 4 × Bool)}
    (hw : lowLetters w = true) :
    FreeGroup.lift f (FreeGroup.mk w) = FreeGroup.lift f' (FreeGroup.mk w) := by
  simp only [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro l hl
  have : l.1.val < 3 := by simpa [lowLetters] using List.all_eq_true.1 hw l hl
  rw [hf l.1 this]

theorem mem_hatS {w : List (Fin 4 × Bool)} :
    w ∈ hatS ↔ (w ∈ cov ∧ lowLetters w = true) ∨ w = [(3, false)] := by
  unfold hatS byLength
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_append, List.mem_filter, List.mem_singleton]

theorem mem_mainWs {w : List (Fin 4 × Bool)} : w ∈ mainWs ↔ w ∈ cov ∨ w ∈ rsWs := by
  unfold mainWs byLength
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_append]

theorem mem_rsWs {w : List (Fin 4 × Bool)} : w ∈ rsWs ↔ w ∈ onRels ∧ lowLetters w = true := by
  unfold rsWs
  rw [List.mem_filter]


theorem lift_onG_cov (h : OnGFacts) :
    ∀ w ∈ cov, FreeGroup.lift onGF (FreeGroup.mk w) = 1 := fun w hw =>
  lift_coverWords_eq_one (R := onRels) (cw := onCommWord) (e := onGF)
    (fun r hr => by rw [h.right.left r hr]; exact one_mem _) h.right.right _
    (List.mem_map_of_mem hw)

theorem lift_gH_hatS (h : OnGFacts) :
    ∀ w ∈ hatS, FreeGroup.lift gH (FreeGroup.mk w) = 1 := by
  intro w hw
  rcases mem_hatS.1 hw with ⟨hc, hl⟩ | rfl
  · rw [lift_congr_low gH onGF (fun i hi => by simp [gH, hi]) hl]
    exact lift_onG_cov h w hc
  · simp [gH]

abbrev Hh : Type := PG 4 hatS

@[expose] noncomputable def sigma (h : OnGFacts) :
    Hh →* J :=
  PresentedGroup.toGroup (f := gH) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_gH_hatS h w hw

theorem sigma_mk (h : OnGFacts) (w : List (Fin 4 × Bool)) :
    sigma h (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk w)) = FreeGroup.lift gH (FreeGroup.mk w) := rfl

theorem sigma_of (h : OnGFacts) (i : Fin 4) :
    sigma h (PresentedGroup.of i) = gH i := PresentedGroup.toGroup.of _

@[expose] def cwH (i : Fin 4) : List (Fin 4 × Bool) := if i.val < 3 then onCommWord i else []

theorem cwH_comm (i : Fin 4) : FreeGroup.mk (cwH i) ∈ commutator (FreeGroup (Fin 4)) := by
  unfold cwH
  split_ifs
  · exact mk_commWords_mem_commutator _
  · exact one_mem _

theorem cwH_mem (i : Fin 4) : (i, false) :: cwH i ∈ hatS := by
  rw [mem_hatS]
  by_cases hi : i.val < 3
  · left
    refine ⟨?_, ?_⟩
    · show _ ∈ coverWords onRels onCommWord
      unfold coverWords
      rw [List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨i, List.mem_finRange i, by simp [cwH, hi]⟩
    · fin_cases i <;> simp [cwH] at hi ⊢ <;> decide
  · right
    have : i = 3 := by omega
    subst this
    simp [cwH]

theorem hatPerf : Group.IsPerfect Hh := isPerfect_PG_of_cw cwH_comm cwH_mem


theorem lift_onG_onCover (h : OnGFacts) :
    ∀ w ∈ onCover, FreeGroup.lift onGF (FreeGroup.mk w) = 1 := by
  intro w hw
  rcases mem_cover₂Words.1 hw with hc | hs
  · exact lift_onG_cov h w hc
  · simp only [squareWords, List.mem_map] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    rw [← FreeGroup.mul_mk, map_mul, h.right.left r hr, mul_one]

theorem index_H0_le (h : OnGFacts) (hc : (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map
    FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧ (genSub {r : FreeGroup (Fin 4) | r ∈
    onCover.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 245520) :
    (Subgroup.closure (Set.range gH)).index ≤ 245520 := by
  let ψ₂ : PG 4 onCover →* J := PresentedGroup.toGroup (f := onGF) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_onG_onCover h w hw
  have hψs : Function.Surjective ψ₂ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← h.left, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of _⟩
  obtain ⟨hfi, hidx⟩ := hc
  have hle : genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf 4 [0, 1, 2]) ≤
      Subgroup.comap ψ₂ (Subgroup.closure (Set.range gH)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : i.val < 3 := by
      fin_cases i <;> simp [subsetOf] at hi ⊢
    rw [SetLike.mem_coe, Subgroup.mem_comap, PresentedGroup.toGroup.of]
    refine Subgroup.subset_closure ⟨i, ?_⟩
    simp [gH, hi3]
  have h2 := (Subgroup.index_antitone hle).trans hidx
  rwa [Subgroup.index_comap_of_surjective _ hψs] at h2

theorem range_sigma (h : OnGFacts) :
    (sigma h).range = Subgroup.closure (Set.range gH) := by
  have hfun : (sigma h) ∘ (PresentedGroup.of : Fin 4 → Hh) = gH := funext (sigma_of h)
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, hfun]

theorem card_range_sigma_ge (h : OnGFacts) (hc : (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map
    FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧ (genSub {r : FreeGroup (Fin 4) | r ∈
    onCover.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 245520) :
    1876896 ≤ Nat.card (sigma h).range := by
  rw [range_sigma h]
  have h1 := Subgroup.card_mul_index (Subgroup.closure (Set.range gH))
  rw [CFSG.Sporadic.ON.card_J] at h1
  have h2 := index_H0_le h hc
  have hpos : 0 < Nat.card (Subgroup.closure (Set.range gH)) := Nat.card_pos
  by_contra hlt
  have := Nat.mul_le_mul (Nat.le_of_lt_succ (not_le.mp hlt)) h2
  omega


@[expose] def zeta : Hh :=
  PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk} (FreeGroup.mk zetaWord)

theorem zetaWord_low : lowLetters zetaWord = true := by decide

theorem zetaWord_mem : zetaWord ∈ onRels := by decide

theorem sigma_zeta (h : OnGFacts) : sigma h zeta = 1 := by
  rw [zeta, sigma_mk, lift_congr_low gH onGF (fun i hi => by simp [gH, hi]) zetaWord_low]
  exact h.right.left _ zetaWord_mem

noncomputable def tauE : J := onGF 3 ^ 2

theorem lift_alphaImgs
    (key : ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1) (i : Fin 4) :
    FreeGroup.lift gH (FreeGroup.mk (alphaImgs.getD i [])) = tauE * gH i * tauE⁻¹ := by
  have k0 := key (ofCodes [6, 6, 0, 7, 7, 1]) (by simp [tauWords])
  have k1 := key (ofCodes [6, 6, 2, 7, 7, 3, 1, 3]) (by simp [tauWords])
  have k2 := key (ofCodes [6, 6, 4, 7, 7, 5]) (by simp [tauWords])
  simp [ofCodes, FreeGroup.lift_mk] at k0 k1 k2
  fin_cases i
  · simp only [alphaImgs, gH, tauE, FreeGroup.lift_mk]
    simp
    have : onGF 3 ^ 2 * onGF 0 * (onGF 3 ^ 2)⁻¹ * (onGF 0)⁻¹ = 1 := by
      rw [← k0]; simp only [pow_two]; group
    exact (mul_inv_eq_one.1 this).symm
  · simp only [alphaImgs, gH, tauE, FreeGroup.lift_mk]
    simp
    have : onGF 3 ^ 2 * onGF 1 * (onGF 3 ^ 2)⁻¹ * (onGF 1 * (onGF 0 * onGF 1))⁻¹ = 1 := by
      rw [← k1]; simp only [pow_two]; group
    exact (mul_inv_eq_one.1 this).symm
  · simp only [alphaImgs, gH, tauE, FreeGroup.lift_mk]
    simp
    have : onGF 3 ^ 2 * onGF 2 * (onGF 3 ^ 2)⁻¹ * (onGF 2)⁻¹ = 1 := by
      rw [← k2]; simp only [pow_two]; group
    exact (mul_inv_eq_one.1 this).symm
  · simp [alphaImgs, gH, tauE, FreeGroup.lift_mk]


theorem sigma_subst (h : OnGFacts)
    (hE : ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1) (w : List (Fin 4 × Bool)) :
    sigma h (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk (substWord alphaImgs w))) =
        tauE * FreeGroup.lift gH (FreeGroup.mk w) * tauE⁻¹ := by
  rw [sigma_mk, ← lift_mk_substWord gH alphaImgs w]
  have hfun : (fun i : Fin 4 => FreeGroup.lift gH (FreeGroup.mk (alphaImgs.getD i []))) =
      fun i => (MulAut.conj tauE).toMonoidHom (gH i) :=
    funext fun i => by rw [lift_alphaImgs hE i]; rfl
  rw [hfun]
  have hcomp : FreeGroup.lift (fun i => (MulAut.conj tauE).toMonoidHom (gH i)) =
      (MulAut.conj tauE).toMonoidHom.comp (FreeGroup.lift gH) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  rw [hcomp]
  rfl

@[expose] def hatImg (i : Fin 4) : Hh :=
  PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
    (FreeGroup.mk (alphaImgs.getD i []))

theorem lift_hatImg (w : List (Fin 4 × Bool)) :
    FreeGroup.lift hatImg (FreeGroup.mk w) =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk (substWord alphaImgs w)) := by
  have h1 := lift_mk_substWord (PresentedGroup.of : Fin 4 → Hh) alphaImgs w
  have hfun : hatImg = fun i : Fin 4 => FreeGroup.lift (PresentedGroup.of : Fin 4 → Hh)
      (FreeGroup.mk (alphaImgs.getD i [])) := funext fun i => mk_eq_lift_of _ _
  rw [mk_eq_lift_of, ← h1, hfun]


theorem sigma_facts (h : OnGFacts)
    (hE : ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1)
    (hc : (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf 4 [0, 1,
        2])).FiniteIndex ∧ (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf
        4 [0, 1, 2])).index ≤ 245520) (hH : Finite Hh ∧ Nat.card Hh ≤ 5630688) (hP : ∃ (Ω : Type) (ψ : Hh →*
        (Equiv.Perm Ω)ᵐᵒᵖ) (b : Ω), ∀ u ℓ, (u, ℓ) ∈ hatWords → 0 < ℓ → Function.minimalPeriod (ψ
        (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk} (FreeGroup.mk
        u))).unop b = ℓ) :
    zeta ^ 3 = 1 ∧ (sigma h).ker = Subgroup.zpowers zeta ∧
      ∃ α : Hh →* Hh, (∀ i, α (PresentedGroup.of i) = hatImg i) ∧ α zeta = zeta⁻¹ := by
  obtain ⟨hfin, hcardH⟩ := hH
  have := hfin
  have hrange := card_range_sigma_ge h hc
  have hker3 : Nat.card (sigma h).ker ≤ 3 := by
    have e := CFSG.GH74.Generic.card_eq_card_mul_card_ker (sigma h).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
    have e2 : Nat.card (sigma h).rangeRestrict.ker = Nat.card (sigma h).ker :=
      Nat.card_congr (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict _)).toEquiv
    rw [e2] at e
    by_contra hlt
    have := Nat.mul_le_mul hrange (Nat.succ_le_of_lt (not_le.mp hlt))
    omega
  obtain ⟨Ω, ψ, b, hper⟩ := hP
  have hzmem : zeta ∈ (sigma h).ker := (MonoidHom.mem_ker).2 (sigma_zeta h)
  have hper3 : Function.minimalPeriod (ψ zeta).unop b = 3 :=
    hper zetaWord 3 (by simp [hatWords]) (by norm_num)
  have h3dvd : 3 ∣ orderOf zeta := hper3 ▸ minimalPeriod_dvd_orderOf ψ zeta b
  have hord : orderOf zeta ∣ Nat.card (sigma h).ker := by
    rw [← Subgroup.orderOf_mk zeta hzmem]
    exact orderOf_dvd_natCard _
  have hKpos : 0 < Nat.card (sigma h).ker := Nat.card_pos
  have hord3 : orderOf zeta = 3 :=
    Nat.le_antisymm ((Nat.le_of_dvd hKpos hord).trans hker3)
      (Nat.le_of_dvd (orderOf_pos zeta) h3dvd)
  have hz3 : zeta ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one zeta
  have hkereq : (sigma h).ker = Subgroup.zpowers zeta :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzmem) (by
      rw [Nat.card_zpowers, hord3]; exact hker3)).symm
  have hpowmem : ∀ x ∈ (sigma h).ker, ∃ j : ℕ, x = zeta ^ j := fun x hx => by
    rw [hkereq] at hx
    obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.2 hx
    exact ⟨j, hj.symm⟩
  have htriv : ∀ w : List (Fin 4 × Bool), (w, 1) ∈ hatWords →
      sigma h (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk w)) = 1 →
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk w) = 1 := by
    intro w hw hσ
    obtain ⟨j, hj⟩ := hpowmem _ ((MonoidHom.mem_ker).2 hσ)
    have hfix := fixes_of_period_one ψ b (hper w 1 hw one_pos)
    rw [hj] at hfix ⊢
    exact pow_eq_one_of_fixes ψ b hz3 hper3 hfix
  have hsubst : ∀ ρ ∈ hatS, sigma h (PresentedGroup.mk
      {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk (substWord alphaImgs ρ))) = 1 := fun ρ hρ => by
    rw [sigma_subst h hE, lift_gH_hatS h ρ hρ]
    simp
  have hmem : ∀ ρ ∈ hatS, (substWord alphaImgs ρ, 1) ∈ hatWords := fun ρ hρ =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.2 ⟨ρ, hρ, rfl⟩))
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk},
      FreeGroup.lift hatImg r = 1 := by
    intro r hr
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hr
    rw [lift_hatImg]
    exact htriv _ (hmem ρ hρ) (hsubst ρ hρ)
  refine ⟨hz3, hkereq, PresentedGroup.toGroup hrel, fun i => PresentedGroup.toGroup.of hrel, ?_⟩
  have hαζ : PresentedGroup.toGroup hrel zeta =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk (substWord alphaImgs zetaWord)) := lift_hatImg zetaWord
  have hw2 : (substWord alphaImgs zetaWord ++ zetaWord, 1) ∈ hatWords :=
    List.mem_cons_of_mem _ (List.mem_cons_self)
  have hmul : PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk (substWord alphaImgs zetaWord ++ zetaWord)) = PresentedGroup.toGroup hrel zeta *
        zeta := by
    rw [hαζ, zeta, ← map_mul, FreeGroup.mul_mk]
  have hlz : FreeGroup.lift gH (FreeGroup.mk zetaWord) = 1 := sigma_zeta h
  have h1 := htriv _ hw2 (by
    rw [hmul, map_mul, hαζ, sigma_subst h hE, sigma_zeta h, hlz]
    simp)
  rw [hmul] at h1
  exact eq_inv_of_mul_eq_one_left h1


theorem lift_cov_ee (h : OnGFacts) {Q : Type} [Group Q]
    (q : Q →* J) (hker : q.ker ≤ Subgroup.center Q) (ee : Fin 4 → Q)
    (hee : ∀ i, q (ee i) = onGF i)
    (hfix : ∀ i, FreeGroup.lift ee (FreeGroup.mk (onCommWord i)) = ee i) :
    ∀ w ∈ cov, FreeGroup.lift ee (FreeGroup.mk w) = 1 := by
  have hqlift : q.comp (FreeGroup.lift ee) = FreeGroup.lift onGF := by
    rw [show q.comp (FreeGroup.lift ee) = FreeGroup.lift (fun i => q (ee i)) from
      FreeGroup.ext_hom _ _ fun i => by simp,
      show (fun i => q (ee i)) = onGF from funext hee]
  have hrc : ∀ r ∈ onRels, FreeGroup.lift ee (FreeGroup.mk r) ∈ Subgroup.center Q :=
    fun r hr => hker (by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hqlift]
      exact h.right.left r hr)
  exact fun w hw =>
    lift_coverWords_eq_one (R := onRels) (cw := onCommWord) hrc hfix _ (List.mem_map_of_mem hw)

theorem lift_rsWs_eq_one (h : OnGFacts)
    (hE : ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1)
    (hc : (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf 4 [0, 1,
        2])).FiniteIndex ∧ (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf
        4 [0, 1, 2])).index ≤ 245520) (hH : Finite Hh ∧ Nat.card Hh ≤ 5630688) (hP : ∃ (Ω : Type) (ψ : Hh →*
        (Equiv.Perm Ω)ᵐᵒᵖ) (b : Ω), ∀ u ℓ, (u, ℓ) ∈ hatWords → 0 < ℓ → Function.minimalPeriod (ψ
        (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk} (FreeGroup.mk
        u))).unop b = ℓ)
    {Q : Type} [Group Q] (q : Q →* J) (hker : q.ker ≤ Subgroup.center Q)
    (ee : Fin 4 → Q) (hee : ∀ i, q (ee i) = onGF i)
    (hfix : ∀ i, FreeGroup.lift ee (FreeGroup.mk (onCommWord i)) = ee i) :
    ∀ r ∈ rsWs, FreeGroup.lift ee (FreeGroup.mk r) = 1 := by
  obtain ⟨hz3, hkereq, α, hαof, hαζ⟩ := sigma_facts h hE hc hH hP
  have hcovee := lift_cov_ee h q hker ee hee hfix
  set e' : Fin 4 → Q := fun i => if i.val < 3 then ee i else 1 with he'
  have hee' : ∀ i : Fin 4, i.val < 3 → ee i = e' i := fun i hi => by simp [he', hi]
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk},
      FreeGroup.lift e' r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rcases mem_hatS.1 hw with ⟨hcw, hl⟩ | rfl
    · rw [← lift_congr_low ee e' hee' hl]
      exact hcovee w hcw
    · simp [he']
  let ι : Hh →* Q := PresentedGroup.toGroup hrel
  have hι_mk : ∀ w : List (Fin 4 × Bool),
      ι (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
        (FreeGroup.mk w)) = FreeGroup.lift e' (FreeGroup.mk w) := fun w => rfl
  have hqι : q.comp ι = sigma h := by
    refine PresentedGroup.ext fun i => ?_
    rw [MonoidHom.comp_apply, sigma_of]
    rw [show ι (PresentedGroup.of i) = e' i from PresentedGroup.toGroup.of hrel]
    by_cases hi : i.val < 3
    · simp [he', gH, hi, hee]
    · simp [he', gH, hi]
  have hα : ∀ x : Hh, q (ee 3 ^ 2 * ι x * (ee 3 ^ 2)⁻¹) = q (ι (α x)) := by
    have hhom : (MulAut.conj tauE).toMonoidHom.comp (sigma h) = (sigma h).comp α := by
      refine PresentedGroup.ext fun i => ?_
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hαof, sigma_of]
      show _ = FreeGroup.lift gH (FreeGroup.mk (alphaImgs.getD i []))
      rw [lift_alphaImgs hE i]
      rfl
    intro x
    have h1 : q (ee 3 ^ 2 * ι x * (ee 3 ^ 2)⁻¹) = tauE * sigma h x * tauE⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_pow, hee 3, ← hqι]
      rfl
    have h2 : q (ι (α x)) = sigma h (α x) := by rw [← hqι]; rfl
    rw [h1, h2]
    have h3 := congrArg (fun f : Hh →* J => f x) hhom
    simpa [MonoidHom.comp_apply, MulAut.conj_apply] using h3
  have hιζ : ι zeta = 1 :=
    iota_eq_one_of_twist hatPerf q hker (sigma h) ι hqι α (ee 3 ^ 2) hα (sigma_zeta h) hαζ hz3
  intro r hr
  obtain ⟨hr', hl⟩ := mem_rsWs.1 hr
  have hσ : sigma h (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk r)) = 1 := by
    rw [sigma_mk, lift_congr_low gH onGF (fun i hi => by simp [gH, hi]) hl]
    exact h.right.left r hr'
  have hmem := (MonoidHom.mem_ker).2 hσ
  rw [hkereq] at hmem
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have : ι (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk}
      (FreeGroup.mk r)) = 1 := by
    rw [← hj, map_zpow, hιζ, one_zpow]
  rw [hι_mk, ← lift_congr_low ee e' hee' hl] at this
  exact this


theorem card_hopfMultiplier_le_three (h : OnGFacts)
    (hE : ∀ w ∈ tauWords, FreeGroup.lift onGF (FreeGroup.mk w) = 1)
    (hc : (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf 4 [0, 1,
        2])).FiniteIndex ∧ (genSub {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (subsetOf
        4 [0, 1, 2])).index ≤
        245520) (hM : Finite (PG 4 mainWs) ∧ Nat.card (PG 4 mainWs) ≤ 1382446517760)
    (hH : Finite Hh ∧ Nat.card Hh ≤ 5630688) (hP : ∃ (Ω : Type) (ψ : Hh →* (Equiv.Perm Ω)ᵐᵒᵖ) (b :
        Ω), ∀ u ℓ, (u, ℓ) ∈ hatWords → 0 < ℓ → Function.minimalPeriod (ψ (PresentedGroup.mk {r :
        FreeGroup (Fin 4) | r ∈ hatS.map FreeGroup.mk} (FreeGroup.mk u))).unop b = ℓ) :
    0 < Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) ∧
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier J) ≤ 3 := by
  obtain ⟨hfin, hle⟩ := hM
  refine card_hopfMultiplier_le_of_forall (g := onGF) (cw := onCommWord) h.left
    (fun i => mk_commWords_mem_commutator _) h.right.right (ws := mainWs) ?_ ?_ hfin
    (p := 3) ?_ ?_
  · intro w hw
    rcases mem_mainWs.1 hw with hc' | hr
    · exact lift_onG_cov h w hc'
    · exact h.right.left w (mem_rsWs.1 hr).1
  · intro i
    rw [mem_mainWs]
    left
    show _ ∈ coverWords onRels onCommWord
    unfold coverWords
    rw [List.mem_append]
    right
    rw [List.mem_map]
    exact ⟨i, List.mem_finRange i, rfl⟩
  · rw [CFSG.Sporadic.ON.card_J]
    exact hle.trans (by norm_num)
  · intro Q _ _ hQ q hqs hker ee hee hfix w hw
    rcases mem_mainWs.1 hw with hc' | hr
    · exact lift_cov_ee h q hker ee hee hfix w hc'
    · exact lift_rsWs_eq_one h hE hc hH hP q hker ee hee hfix w hr

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
