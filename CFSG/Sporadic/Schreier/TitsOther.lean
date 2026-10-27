module

public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsStab

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.SectionRank.TitsOrder CFSG.SectionRank.TitsGen
  CFSG.Blueprint.Chevalley

theorem titsGamma_eq :
    ReeTag.titsGamma =
    (reeFixed ReeTag.F4 (ZMod 2) 0).map (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype := by
  show (ReeTag.F4.finiteReeFixedGroup (ZMod 2) 0).map
    (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype = _
  rw [ReeTag.map_subtype_finiteReeFixedGroup, reeFixedGroup_eq_map_reeFixed]

@[expose] def titsGammaEquiv :
    reeFixed ReeTag.F4 (ZMod 2) 0 ≃* ReeTag.titsGamma :=
  ((reeFixed ReeTag.F4 (ZMod 2) 0).equivMapOfInjective _
    (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype_injective).trans
    (MulEquiv.subgroupCongr titsGamma_eq.symm)

@[expose] def titsGammaIso :
    ReeTag.titsGamma ≃* titsA :=
  titsGammaEquiv.symm.trans (titsIso (K := ZMod 2))

@[expose] def titsChevGen :
    ℕ → ModGL ReeTag.F4.tag (ZMod 2)
  | 0 => ReeTag.titsGen0 (ZMod 2)
  | 1 => ReeTag.titsGen1 (ZMod 2)
  | 2 => ReeTag.titsGen2 (ZMod 2)
  | _ => ReeTag.titsGen3 (ZMod 2)

theorem coe_titsGammaEquiv
    (g : reeFixed ReeTag.F4 (ZMod 2) 0) :
    (titsGammaEquiv g : ModGL ReeTag.F4.tag (ZMod 2)) =
      ((g : adjointGroup ReeTag.F4.tag (ZMod 2)) : ModGL ReeTag.F4.tag (ZMod 2)) :=
  rfl

theorem coe_genG
    {s : ℕ} (hs : s < 4) :
    ((genG (ZMod 2) s : adjointGroup ReeTag.F4.tag (ZMod 2)) : ModGL ReeTag.F4.tag (ZMod 2)) =
      titsChevGen s := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  interval_cases s
  · exact ReeTag.coe_titsG0 (ZMod 2)
  · exact ReeTag.coe_titsG1 (ZMod 2) h2
  · exact ReeTag.coe_titsZ1 (ZMod 2)
  · exact ReeTag.coe_titsZ2 (ZMod 2)

theorem titsChevGen_mem
    {s : ℕ} (hs : s < 4) : titsChevGen s ∈ ReeTag.titsGamma := by
  rw [← coe_genG hs, ← coe_titsGammaEquiv]
  exact (titsGammaEquiv (genG (ZMod 2) s)).2

theorem titsGammaEquiv_genG
    {s : ℕ} (hs : s < 4) :
    titsGammaEquiv (genG (ZMod 2) s) = ⟨titsChevGen s, titsChevGen_mem hs⟩ :=
  Subtype.ext (coe_genG hs)

theorem titsGammaIso_gen
    {s : ℕ} (hs : s < 4) :
    (titsGammaIso ⟨titsChevGen s, titsChevGen_mem hs⟩ : Equiv.Perm (Fin 1755)) = titsGen s := by
  rw [titsGammaIso, MulEquiv.trans_apply, ← titsGammaEquiv_genG hs, MulEquiv.symm_apply_apply,
    titsIso_gen hs]

theorem map_commutator_titsGamma
    (ι : ReeTag.titsGamma ≃* titsA) :
    (commutator ReeTag.titsGamma).map (ι : ReeTag.titsGamma →* titsA) = titsD.subgroupOf titsA := by
  rw [map_commutator_of_surjective _ ι.surjective, commutator_titsA]

theorem titsD_hom_ext {M : Type*} [Group M] {φ ψ : titsD →* M}
    (h : ∀ j (hj : j < 2), φ ⟨titsDGen j, titsDGen_mem_titsD hj⟩ =
      ψ ⟨titsDGen j, titsDGen_mem_titsD hj⟩) : φ = ψ := by
  ext ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨j, rfl⟩ := ht
    exact h j j.2
  | one => exact (map_one φ).trans (map_one ψ).symm
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, mul_mem hx hy⟩ : titsD) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, map_mul,
      ihx, ihy]
  | inv x hx ih =>
    rw [show (⟨x⁻¹, inv_mem hx⟩ : titsD) = (⟨x, hx⟩)⁻¹ from rfl, map_inv, map_inv, ih]

theorem titsBeta_surjective :
    Function.Surjective titsBeta := by
  intro x
  obtain ⟨g, hg⟩ := titsDPoint_transitive x
  refine ⟨titsDFlagAct g 0, ?_⟩
  rw [titsBeta_dflag, titsBeta_zero]
  exact hg

theorem titsDFlagAct_injective :
    Function.Injective titsDFlagAct := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine Equiv.ext fun x => ?_
  obtain ⟨j, rfl⟩ := titsBeta_surjective x
  rw [← titsBeta_dflag, hg]
  rfl

theorem titsDLineAct_injective :
    Function.Injective titsDLineAct := by
  have hs := titsD_simple
  rcases hs.eq_bot_or_eq_top_of_normal titsDLineAct.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    obtain ⟨g, hg⟩ := titsDLine_transitive 1
    have : g ∈ titsDLineAct.ker := h ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at this
    rw [this] at hg
    exact absurd hg (by decide)

theorem titsKappa_fiber
    (v : Fin 2925) :
    {j : Fin 8775 | titsKappa j = v} =
      {titsLineFlag v 0, titsLineFlag v 1, titsLineFlag v 2} := by
  ext j
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    obtain ⟨k, hk, hj, -⟩ := titsLineFlag_pos j
    interval_cases k
    · exact Or.inl hj.symm
    · exact Or.inr (Or.inl hj.symm)
    · exact Or.inr (Or.inr hj.symm)
  · rintro (rfl | rfl | rfl)
    · exact (titsLineFlag_spec v (by norm_num)).1
    · exact (titsLineFlag_spec v (by norm_num)).1
    · exact (titsLineFlag_spec v (by norm_num)).1

theorem titsKappa_fiber_ncard
    (v : Fin 2925) : {j : Fin 8775 | titsKappa j = v}.ncard = 3 := by
  rw [titsKappa_fiber]
  obtain ⟨h1, h2⟩ := titsLinePt_lt v
  have hb : ∀ k < 3, titsBeta (titsLineFlag v k) = titsLinePt v k :=
    fun k hk => (titsLineFlag_spec v hk).2
  have d01 : titsLineFlag v 0 ≠ titsLineFlag v 1 := fun e => by
    have := congrArg titsBeta e
    rw [hb 0 (by norm_num), hb 1 (by norm_num)] at this
    exact absurd this (ne_of_lt h1)
  have d02 : titsLineFlag v 0 ≠ titsLineFlag v 2 := fun e => by
    have := congrArg titsBeta e
    rw [hb 0 (by norm_num), hb 2 (by norm_num)] at this
    exact absurd this (ne_of_lt (h1.trans h2))
  have d12 : titsLineFlag v 1 ≠ titsLineFlag v 2 := fun e => by
    have := congrArg titsBeta e
    rw [hb 1 (by norm_num), hb 2 (by norm_num)] at this
    exact absurd this (ne_of_lt h2)
  rw [Set.ncard_insert_of_notMem (by simp [d01, d02]), Set.ncard_pair d12]

theorem titsDFlag_eq_cmp
    {j : ℕ} (hj : j < 2) : titsDFlag j = titsDFlagCmp j :=
  eq_of_eqA (titsDFlag_rep hj)
    (rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.2.1]; exact hj)) (titsStab_check.2.2.2.1 j hj).1

theorem titsDStar_eq_cmp
    {j : ℕ} (hj : j < 2) : titsDStar j = titsDStarCmp j :=
  eq_of_eqA (titsDStar_rep hj)
    (rep_of_allPermsOK titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [titsLocalData_check.2.2.2.1]; exact hj)) (titsStab_check.2.2.2.1 j hj).2

theorem AT_Tits_other_parabolic_action :
    (∀ s (hs : s < 4),
      (titsGammaIso ⟨titsChevGen s, titsChevGen_mem hs⟩ : Equiv.Perm (Fin 1755)) = titsGen s) ∧
    (∀ ι : ReeTag.titsGamma ≃* titsA,
      (commutator ReeTag.titsGamma).map (ι : ReeTag.titsGamma →* titsA) =
        titsD.subgroupOf titsA) ∧
    Subgroup.center titsD = ⊥ ∧ Nontrivial titsD ∧ IsSimpleGroup titsD ∧
    Nat.card titsD = 17971200 ∧
    (∀ j (hj : j < 2), titsDFlagAct ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDFlag j) ∧
    (∀ ρ : titsD →* Equiv.Perm (Fin 8775),
      (∀ j (hj : j < 2), ρ ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDFlag j) →
        ρ = titsDFlagAct) ∧
    Function.Injective titsDFlagAct ∧ (∀ x : Fin 8775, ∃ g, titsDFlagAct g 0 = x) ∧
    (∀ j (hj : j < 2), titsDLineAct ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDStar j) ∧
    (∀ ρ : titsD →* Equiv.Perm (Fin 2925),
      (∀ j (hj : j < 2), ρ ⟨titsDGen j, titsDGen_mem_titsD hj⟩ = titsDStar j) →
        ρ = titsDLineAct) ∧
    Function.Injective titsDLineAct ∧ (∀ x : Fin 2925, ∃ g, titsDLineAct g 0 = x) ∧
    (∀ j < 2, titsDFlag j = titsDFlagCmp j ∧ titsDStar j = titsDStarCmp j) ∧
    Function.Surjective titsKappa ∧ (∀ v, {j : Fin 8775 | titsKappa j = v}.ncard = 3) ∧
    titsKappa 0 = 0 ∧
    (∀ g j, titsKappa (titsDFlagAct g j) = titsDLineAct g (titsKappa j)) ∧
    (∀ i < 4, ∀ v : Fin 8775, titsKappa (titsP i v) = titsAStar i (titsKappa v)) ∧
    (∀ i (hi : i < 4), titsFlagHom ⟨titsGen i, titsGen_mem_titsA hi⟩ = titsP i ∧
      titsLineHom ⟨titsGen i, titsGen_mem_titsA hi⟩ = titsAStar i) ∧
    (∀ (g : titsA) j, titsKappa (titsFlagHom g j) = titsLineHom g (titsKappa j)) ∧
    (∀ g j, titsBeta (titsDFlagAct g j) = (g : Equiv.Perm (Fin 1755)) (titsBeta j)) :=
  ⟨fun _ hs => titsGammaIso_gen hs, map_commutator_titsGamma, titsD_center, titsD_nontrivial,
    titsD_simple, card_titsD, fun _ hj => titsDFlagAct_dGen hj,
    fun ρ hρ => titsD_hom_ext fun j hj => (hρ j hj).trans (titsDFlagAct_dGen hj).symm,
    titsDFlagAct_injective, titsDFlag_transitive, fun _ hj => titsDLineAct_dGen hj,
    fun ρ hρ => titsD_hom_ext fun j hj => (hρ j hj).trans (titsDLineAct_dGen hj).symm,
    titsDLineAct_injective, titsDLine_transitive,
    fun _ hj => ⟨titsDFlag_eq_cmp hj, titsDStar_eq_cmp hj⟩,
    fun v => ⟨_, (titsLineFlag_spec v (by norm_num : 0 < 3)).1⟩, titsKappa_fiber_ncard,
    titsKappa_zero, titsKappa_dflag, fun _ hi v => titsKappa_titsP hi v,
    fun _ hi => ⟨titsFlagHom_gen hi, titsLineHom_gen hi⟩, titsKappa_flag, titsBeta_dflag⟩

end CFSG.Sporadic.Schreier.Tits
