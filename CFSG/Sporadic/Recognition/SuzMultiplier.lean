module

public import CFSG.Sporadic.Recognition.SuzMultiplierTables
public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.Sporadic.Presentation.Suz
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.Certificates.Kernel.CosetJ.GenSub
public import CFSG.Sporadic.Recognition.SuzMultiplierIndex
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SuzOddCore.SmallChain

public section

namespace CFSG.Sporadic.Recognition.SuzMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Suz CFSG.Open
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LieType.Multipliers.Tits CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Recognition.CoverTransfer
  Subgroup

theorem card_PG_R0_le :
    Finite (PG gcS R0) ∧ Nat.card (PG gcS R0) ≤ 448345497600 := by
  have h : Finite TauCeti.SporadicName.Suz.presentation.Group ∧
      Nat.card TauCeti.SporadicName.Suz.presentation.Group ≤ 448345497600 := finite_card_le
  rwa [TauCeti.GroupPresentation.Group, CFSG.Sporadic.Presentation.relatorSet_eq] at h

theorem isPresentation_suzGen
    (hTab : suzTabCheck = true) :
    IsPresentation suzGen (wordSet R0) := by
  obtain ⟨hfin, hle⟩ := card_PG_R0_le
  have : Finite (PresentedGroup (wordSet R0)) := hfin
  exact IsPresentation.of_card_le (lift_suzGen_R0 hTab) (closure_suzGen hTab) (by
    rw [suzM_card_chain]; exact hle)

abbrev SuzCover : Type := PresentedCover (wordSet R0) suzCommW

theorem coverRelators_suzCommW : coverRelators (wordSet R0) suzCommW = wordSet suzCover :=
  coverRelators_wordSet R0 suzCommWord

theorem lift_of_suzCover : ∀ w ∈ suzCover,
    FreeGroup.lift (PresentedGroup.of : Fin gcS → SuzCover) (FreeGroup.mk w) = 1 := by
  intro w hw
  rw [← mk_eq_lift_of]
  exact PresentedGroup.one_of_mem (by rw [coverRelators_suzCommW]; exact List.mem_map_of_mem hw)

abbrev suzS0 : List (Fin gcS) := subsetOf gcS [0, 1, 2, 3, 4, 6]

abbrev suzS2 : List (Fin suzS0.length) := subsetOf suzS0.length [0, 1, 2, 3, 4]

abbrev suzK : Subgroup SuzCover :=
  Subgroup.closure ((fun x => PresentedGroup.of x) '' {x | x ∈ suzS0})

abbrev SuzP1 : Type := PG suzS0.length suzCover1

abbrev SuzP2 : Type := PG suzS2.length suzCover2

noncomputable def suzχ₁ : SuzP1 →* SuzCover :=
  PresentedGroup.toGroup (lift_restrictWords suzCover suzS0 _ lift_of_suzCover)

noncomputable def suzχ₂ : SuzP2 →* SuzP1 :=
  PresentedGroup.toGroup (lift_restrictWords suzCover1 suzS2 _ fun w hw => by
    rw [← mk_eq_lift_of]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw))

noncomputable def suzψ : SuzP2 →* SuzCover := suzχ₁.comp suzχ₂

theorem index_suzK_le
    (hL0 : SuzIndexP1) :
    suzK.FiniteIndex ∧ suzK.index ≤ 5346 := by
  have key : ∀ rels : Set (FreeGroup (Fin gcS)), rels = wordSet suzCover →
      (Subgroup.closure ((fun x => PresentedGroup.of x) '' {x | x ∈ suzS0}) :
        Subgroup (PresentedGroup rels)).FiniteIndex ∧
      (Subgroup.closure ((fun x => PresentedGroup.of x) '' {x | x ∈ suzS0}) :
        Subgroup (PresentedGroup rels)).index ≤ 5346 := by
    rintro rels rfl
    exact index_le_of_genSub hL0 _ fun i hi =>
      Subgroup.subset_closure ⟨i, hi, rfl⟩
  exact key _ coverRelators_suzCommW

theorem index_range_suzχ₂_le
    (hL1 : SuzIndexP2) :
    suzχ₂.range.FiniteIndex ∧ suzχ₂.range.index ≤ 416 :=
  index_le_of_genSub hL1 _ fun i hi => by
    obtain ⟨j, rfl⟩ := List.get_of_mem hi
    exact MonoidHom.mem_range.2 ⟨PresentedGroup.of j, PresentedGroup.toGroup.of _⟩

theorem suzK_le_range : suzK ≤ suzχ₁.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨j, rfl⟩ := List.get_of_mem hx
  exact MonoidHom.mem_range.2 ⟨PresentedGroup.of j, PresentedGroup.toGroup.of _⟩

theorem card_suzCover_le_range [Finite SuzCover]
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2) :
    Nat.card SuzCover ≤ 2223936 * Nat.card suzψ.range := by
  obtain ⟨hfi0, hidx0⟩ := index_suzK_le hL0
  obtain ⟨hfi1, hidx1⟩ := index_range_suzχ₂_le hL1
  have h1 : Nat.card suzK ≤ Nat.card suzχ₁.range := Subgroup.card_le_of_le suzK_le_range
  have h2 := card_range_le_index_mul suzχ₁ suzχ₂.range
  have h3 : suzχ₂.range.map suzχ₁ = suzψ.range := by rw [suzψ, MonoidHom.range_comp]
  rw [h3] at h2
  rw [← suzK.index_mul_card]
  calc suzK.index * Nat.card suzK ≤ 5346 * (416 * Nat.card suzψ.range) :=
        Nat.mul_le_mul hidx0 (h1.trans (h2.trans (Nat.mul_le_mul_right _ hidx1)))
    _ = 2223936 * Nat.card suzψ.range := by ring

theorem card_suzCover_le
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) :
    Finite SuzCover ∧ Nat.card SuzCover ≤ 2690072985600 := by
  change Finite (PresentedGroup (coverRelators (wordSet R0) suzCommW)) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet R0) suzCommW)) ≤ 2690072985600
  rw [coverRelators_suzCommW]
  obtain ⟨f2, c2⟩ := hL2
  obtain ⟨f1, c1⟩ := card_le_of_genSub_index suzCover1 _ hL1.1 hL1.2
  obtain ⟨f0, c0⟩ := card_le_of_genSub_index suzCover _ hL0.1 hL0.2
  refine ⟨f0, ?_⟩
  have := c0.trans <| Nat.mul_le_mul_left _ <| c1.trans <| Nat.mul_le_mul_left _ c2
  exact this.trans (by norm_num)

theorem suzψ_injective [Finite SuzCover]
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2)
    (hP : Nat.card SuzCover = 2690072985600) : Function.Injective suzψ := by
  obtain ⟨hf2, hc2⟩ := hL2
  have hr := card_suzCover_le_range hL0 hL1
  rw [hP] at hr
  have hc2' : Nat.card SuzP2 ≤ 1209600 := hc2
  have hrange : Nat.card SuzP2 ≤ Nat.card suzψ.range := by omega
  have hb := suzψ.rangeRestrict_surjective.bijective_of_nat_card_le hrange
  intro x y hxy
  exact hb.1 (Subtype.ext hxy)

@[expose] def suzD2 : Fin suzS2.length := ⟨3, by decide⟩

theorem suzψ_of_suzD2 : suzψ (PresentedGroup.of suzD2) = PresentedGroup.of suzD := by
  simp only [suzψ, MonoidHom.comp_apply, suzχ₂, suzχ₁, PresentedGroup.toGroup.of]
  congr 1

section Cover

noncomputable abbrev suzπ (hTab : suzTabCheck = true) : SuzCover →* suzM :=
  coverMap (isPresentation_suzGen hTab) (lift_suzCommW hTab)

theorem suzπ_mk (hTab : suzTabCheck = true) (x : FreeGroup (Fin gcS)) :
    suzπ hTab (PresentedGroup.mk _ x) = FreeGroup.lift suzGen x :=
  coverMap_mk _ _ x

theorem suzπ_of (hTab : suzTabCheck = true) (i : Fin gcS) :
    suzπ hTab (PresentedGroup.of i) = suzGen i :=
  coverMap_of _ _ i

end Cover

section Rho0

@[expose] noncomputable def suzRho0Gen (i : ℕ) : Equiv.Perm (Fin 5346) :=
  permOfArr 5346 suzRho0Arrs[i]!

theorem rho0_facts (h : suzRho0Check = true) :
    allPermsOK 5346 suzRho0Arrs = true ∧
      (∀ w ∈ suzCover, lettersOK gcS (zword w) = true ∧
        eqA 5346 (wordArr 5346 suzRho0Arrs (zword w)) (idA 5346) = true) ∧
      lettersOK gcS (zword suzR3) = true ∧
      eqA 5346 (wordArr 5346 suzRho0Arrs (zword suzR3)) (idA 5346) = false ∧
      eqA 5346 (wordArr 5346 suzRho0Arrs (zword (suzR3 ++ suzR3 ++ suzR3))) (idA 5346) =
        true := by
  unfold suzRho0Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rep_suzRho0 (h : suzRho0Check = true) {w : List ℤ} (hw : lettersOK gcS w = true) :
    Rep 5346 (wordArr 5346 suzRho0Arrs w) (wordIn gcS suzRho0Gen w) :=
  rep_wordArr (by decide) (fun i hi => rep_of_allPermsOK (rho0_facts h).1 (by
      have : suzRho0Arrs.size = 7 := rfl
      have h7 : gcS = 7 := rfl
      omega))
    (fun i hi => isInvA_of_allPermsOK (rho0_facts h).1 (by
      have : suzRho0Arrs.size = 7 := rfl
      have h7 : gcS = 7 := rfl
      omega)) hw

theorem suzRho0_rels (h : suzRho0Check = true) :
    ∀ r ∈ coverRelators (wordSet R0) suzCommW,
      FreeGroup.lift (fun i : Fin gcS => suzRho0Gen i) r = 1 := by
  rw [coverRelators_suzCommW]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hl, he⟩ := (rho0_facts h).2.1 w hw
  rw [lift_mk_eq_wordIn]
  exact eq_of_eqA (rep_suzRho0 h hl) rep_idA he

noncomputable def suzRho0 (h : suzRho0Check = true) : SuzCover →* Equiv.Perm (Fin 5346) :=
  PresentedGroup.toGroup (suzRho0_rels h)

theorem suzRho0_mk (h : suzRho0Check = true) (w : List (Fin gcS × Bool)) :
    suzRho0 h (PresentedGroup.mk _ (FreeGroup.mk w)) = wordIn gcS suzRho0Gen (zword w) := by
  rw [suzRho0, mk_eq_lift_of, ← MonoidHom.comp_apply,
    show (PresentedGroup.toGroup (suzRho0_rels h)).comp (FreeGroup.lift PresentedGroup.of) =
      FreeGroup.lift (fun i : Fin gcS => suzRho0Gen i) from
      FreeGroup.ext_hom _ _ fun j => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
        exact PresentedGroup.toGroup.of _,
    lift_mk_eq_wordIn]

@[expose] noncomputable def suzZ : SuzCover := PresentedGroup.mk _ (FreeGroup.mk suzR3)

theorem orderOf_suzRho0_suzZ (h : suzRho0Check = true) : orderOf (suzRho0 h suzZ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hl, hne, h3⟩ := rho0_facts h
  refine orderOf_eq_prime ?_ ?_
  · have hz3 : suzZ ^ 3 = PresentedGroup.mk _ (FreeGroup.mk (suzR3 ++ suzR3 ++ suzR3)) := by
      rw [suzZ, ← map_pow, pow_three', FreeGroup.mul_mk, FreeGroup.mul_mk]
    have hl3 : lettersOK gcS (zword (suzR3 ++ suzR3 ++ suzR3)) = true := by decide
    rw [← map_pow, hz3, suzRho0_mk]
    exact eq_of_eqA (rep_suzRho0 h hl3) rep_idA h3
  · rw [suzZ, suzRho0_mk]
    intro h1
    rw [(eqA_iff (rep_suzRho0 h hl) rep_idA).2 h1] at hne
    exact absurd hne (by decide)

end Rho0

section Multiplier

theorem suzπ_suzZ (hTab : suzTabCheck = true) : suzπ hTab suzZ = 1 := by
  rw [suzZ, suzπ_mk]
  exact lift_suzGen_R3 hTab

theorem three_dvd_card_ker (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true) :
    3 ∣ Nat.card (suzπ hTab).ker := by
  have hmem : suzZ ∈ (suzπ hTab).ker := suzπ_suzZ hTab
  have h1 := orderOf_map_dvd (suzRho0 hRho0) suzZ
  rw [orderOf_suzRho0_suzZ] at h1
  have h2 := orderOf_dvd_natCard (⟨suzZ, hmem⟩ : (suzπ hTab).ker)
  rw [← Subgroup.orderOf_coe] at h2
  exact h1.trans h2

theorem card_griessHopfMultiplier_eq_card_ker (hTab : suzTabCheck = true) :
    Nat.card (griessHopfMultiplier suzM) = Nat.card (suzπ hTab).ker :=
  Nat.card_congr (griessHopfMultiplierEquivKer (isPresentation_suzGen hTab)
    suzCommW_mem_commutator (lift_suzCommW hTab)).toEquiv

theorem card_suzCover (hTab : suzTabCheck = true) :
    Nat.card SuzCover = 448345497600 * Nat.card (griessHopfMultiplier suzM) := by
  rw [card_presentedCover (isPresentation_suzGen hTab) suzCommW_mem_commutator
    (lift_suzCommW hTab), suzM_card_chain]

theorem card_griessHopfMultiplier_M (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) :
    Nat.card (griessHopfMultiplier suzM) = 3 ∨ Nat.card (griessHopfMultiplier suzM) = 6 := by
  obtain ⟨hfin, hle⟩ := card_suzCover_le hL0 hL1 hL2
  have hc := card_suzCover hTab
  have h3 := three_dvd_card_ker hTab hRho0
  rw [← card_griessHopfMultiplier_eq_card_ker] at h3
  have hpos : 0 < Nat.card SuzCover := Nat.card_pos
  rw [hc] at hle hpos
  obtain ⟨k, hk⟩ := h3
  omega

theorem card_griessHopfMultiplier_of_mulEquiv (hTab : suzTabCheck = true) {Y : Type} [Group Y]
    (e : Y ≃* suzM)
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) :
    Nat.card (griessHopfMultiplier Y) = Nat.card (griessHopfMultiplier suzM) := by
  have hP' := (isPresentation_suzGen hTab).mulEquiv e.symm
  have hwg' : ∀ i, FreeGroup.lift (fun i => e.symm (suzGen i)) (suzCommW i) = e.symm (suzGen i) :=
    fun i => by rw [lift_mulEquiv, lift_suzCommW hTab]
  have hc := card_presentedCover hP' suzCommW_mem_commutator hwg'
  have hc' := card_presentedCover (isPresentation_suzGen hTab) suzCommW_mem_commutator
    (lift_suzCommW hTab)
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  rw [Nat.card_congr e.toEquiv, hc'] at hc
  have : Finite suzM := Finite.of_surjective _
    (coverMap_surjective (isPresentation_suzGen hTab) (lift_suzCommW hTab))
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem card_griessHopfMultiplier_Suz
    (hTab : suzTabCheck = true)
    (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Suz) = 3 ∨
      Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Suz) = 6 := by
  have e := suzEquivM
  have h1 : Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.Suz) =
      Nat.card (griessHopfMultiplier suzM) :=
    card_griessHopfMultiplier_of_mulEquiv hTab e hL0 hL1 hL2
  rw [h1]
  exact card_griessHopfMultiplier_M hTab hRho0 hL0 hL1 hL2

end Multiplier

section RhoJ2

@[expose] noncomputable def suzRhoJ2Gen (i : ℕ) : Equiv.Perm (Fin 200) :=
  permOfArr 200 suzRhoJ2Arrs[i]!

theorem rhoJ2_facts (h : suzRhoJ2Check = true) :
    allPermsOK 200 suzRhoJ2Arrs = true ∧
      (∀ w ∈ suzCover2, lettersOK 5 (zword w) = true ∧
        eqA 200 (wordArr 200 suzRhoJ2Arrs (zword w)) (idA 200) = true) ∧
      eqA 200 (wordArr 200 suzRhoJ2Arrs [4, 4, 4, 4, 4, 4]) (idA 200) = false := by
  unfold suzRhoJ2Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem length_suzS2 : suzS2.length = 5 := by decide

theorem rep_suzRhoJ2 (h : suzRhoJ2Check = true) {w : List ℤ}
    (hw : lettersOK suzS2.length w = true) :
    Rep 200 (wordArr 200 suzRhoJ2Arrs w) (wordIn suzS2.length suzRhoJ2Gen w) :=
  rep_wordArr (by decide) (fun i hi => rep_of_allPermsOK (rhoJ2_facts h).1 (by
      have : suzRhoJ2Arrs.size = 5 := rfl
      have h5 := length_suzS2
      omega))
    (fun i hi => isInvA_of_allPermsOK (rhoJ2_facts h).1 (by
      have : suzRhoJ2Arrs.size = 5 := rfl
      have h5 := length_suzS2
      omega)) hw

theorem suzRhoJ2_rels (h : suzRhoJ2Check = true) :
    ∀ r ∈ {r : FreeGroup (Fin suzS2.length) | r ∈ suzCover2.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin suzS2.length => suzRhoJ2Gen i) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hl, he⟩ := (rhoJ2_facts h).2.1 w hw
  rw [← length_suzS2] at hl
  rw [lift_mk_eq_wordIn]
  exact eq_of_eqA (rep_suzRhoJ2 h hl) rep_idA he

noncomputable def suzRhoJ2 (h : suzRhoJ2Check = true) : SuzP2 →* Equiv.Perm (Fin 200) :=
  PresentedGroup.toGroup (suzRhoJ2_rels h)

theorem of_suzD2_pow_six_ne_one (h : suzRhoJ2Check = true) :
    (PresentedGroup.of suzD2 : SuzP2) ^ 6 ≠ 1 := by
  intro h1
  have hρ := congrArg (suzRhoJ2 h) h1
  rw [map_pow, map_one, suzRhoJ2, PresentedGroup.toGroup.of] at hρ
  have hw : wordIn suzS2.length suzRhoJ2Gen [4, 4, 4, 4, 4, 4] = suzRhoJ2Gen 3 ^ 6 := by
    rw [← show zword (List.replicate 6 (suzD2, true)) = [4, 4, 4, 4, 4, 4] by decide,
      ← lift_mk_eq_wordIn, mk_replicate, map_pow, FreeGroup.lift_apply_of]
    rfl
  have hne := (rhoJ2_facts h).2.2
  rw [(eqA_iff (rep_suzRhoJ2 h (by decide)) rep_idA).2 (hw.trans hρ)] at hne
  exact absurd hne (by decide)

end RhoJ2

section Lift

theorem card_ker_eq_three_of_doubleCover (hTab : suzTabCheck = true)
    (hRho0 : suzRho0Check = true)
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) {L : Type} [Group L]
    [Finite L] (q : L →* suzM) (hq : Function.Surjective q) {t : L} (ht : orderOf t = 2)
    (hker : q.ker = zpowers t) (φ : SuzCover →* L) (hφ : Function.Surjective φ) :
    Nat.card φ.ker = 3 ∧ Nat.card SuzCover = 2690072985600 := by
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  have hcardL : Nat.card L = 896690995200 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hq).toEquiv,
      suzM_card_chain, hker, Nat.card_zpowers, ht]
  have hP : Nat.card SuzCover = Nat.card φ.ker * Nat.card L := by
    rw [φ.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hφ).toEquiv, mul_comm]
  have hc := card_suzCover hTab
  rw [hcardL] at hP
  rcases card_griessHopfMultiplier_M hTab hRho0 hL0 hL1 hL2 with h | h <;> rw [h] at hc <;>
    omega

theorem sq_eq_of_lift_conj_d (hTab : suzTabCheck = true) (hRho0 : suzRho0Check = true)
    (hRhoJ2 : suzRhoJ2Check = true)
    (hL0 : SuzIndexP1)
    (hL1 : SuzIndexP2)
    (hL2 : SuzCardP2) {L : Type} [Group L]
    [Finite L] [Group.IsPerfect L] (q : L →* suzM) (hq : Function.Surjective q) {t : L}
    (ht : orderOf t = 2) (hker : q.ker = zpowers t) (hcen : zpowers t ≤ center L) {v : L}
    {h : suzM} (hv : q v = h * suzGen suzD * h⁻¹) : v ^ 2 = t := by
  obtain ⟨hfin, -⟩ := card_suzCover_le hL0 hL1 hL2
  have hkerc : q.ker ≤ center L := hker ▸ hcen
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift (isPresentation_suzGen hTab)
    suzCommW_mem_commutator (lift_suzCommW hTab) q hq hkerc
  obtain ⟨hk3, hP⟩ := card_ker_eq_three_of_doubleCover hTab hRho0 hL0 hL1 hL2 q hq ht hker φ hφ
  have hψ := suzψ_injective hL0 hL1 hL2 hP
  have hd6 : (PresentedGroup.of suzD : SuzCover) ^ 6 ≠ 1 := by
    rw [← suzψ_of_suzD2]
    intro h1
    exact of_suzD2_pow_six_ne_one hRhoJ2 (hψ (by rw [map_pow, h1, map_one]))
  have hqφ : q (φ (PresentedGroup.of suzD)) = suzGen suzD := by
    rw [← MonoidHom.comp_apply, hcomp]
    exact suzπ_of hTab suzD
  have hexp : ∀ c ∈ q.ker, c ^ 2 = 1 := by
    intro c hc
    rw [hker] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ht, pow_orderOf_eq_one,
      one_zpow]
  have hv' : q v = h * q (φ (PresentedGroup.of suzD)) * h⁻¹ := by rw [hqφ]; exact hv
  have hp' : q (φ (PresentedGroup.of suzD)) ^ 2 = 1 := by rw [hqφ]; exact suzGen_d_sq hTab
  have hsq := sq_eq_sq_of_conj q hq hkerc hexp hv' hp'
  rw [hsq, ← map_pow]
  refine eq_of_mem_zpowers_of_ne_one ht ?_ ?_
  · rw [← hker, MonoidHom.mem_ker, map_pow, map_pow, hqφ]
    exact suzGen_d_sq hTab
  · intro h1
    have hmem : (PresentedGroup.of suzD : SuzCover) ^ 2 ∈ φ.ker := h1
    have h3 := orderOf_dvd_natCard (⟨_, hmem⟩ : φ.ker)
    rw [hk3, ← Subgroup.orderOf_coe] at h3
    have h6 := orderOf_dvd_iff_pow_eq_one.1 h3
    rw [← pow_mul] at h6
    exact hd6 h6

end Lift

end CFSG.Sporadic.Recognition.SuzMultiplier
