module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LieType.Chevalley.TwistedE6EvenCoverLifts

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6rb_commute_of_mem_closure {X : Type*} [Group X] {t : X} {A : Set X}
    (hA : ∀ g ∈ A, Commute t g) {g : X} (hg : g ∈ Subgroup.closure A) : Commute t g := by
  have hle : Subgroup.closure A ≤ Subgroup.centralizer ({t} : Set X) := by
    rw [Subgroup.closure_le]
    intro a ha
    change a ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hA a ha).symm.eq
  have h1 := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  exact h1.symm

private theorem e6rb_level_check :
    (∀ β ∈ rootFinset .E6, ∀ γ ∈ rootFinset .E6,
      0 < iform β lamE → iform γ lamE = 2 → 0 ≤ iform γ β) := by
  decide +kernel

private theorem e6rb_rOne_check :
    a5Root (blk 0 0) (blk 2 0) ≠ a5Root (blk 0 1) (blk 2 1) ∧
    0 < height (a5Root (blk 0 0) (blk 2 0)) ∧
    0 < height (a5Root (blk 0 1) (blk 2 1)) := by
  decide +kernel

private theorem e6rb_iform_check :
    iform (a5Root (blk 0 0) (blk 2 0)) lamE = 2 ∧
    iform (a5Root (blk 0 1) (blk 2 1)) lamE = 2 ∧
    iform (a5Root (blk 0 0) (blk 2 1)) lamE = 2 ∧
    iform (a5Root (blk 0 1) (blk 2 0)) lamE = 2 := by
  decide +kernel

theorem z0E_le_qE : z0E ≤ qE := by
  unfold z0E qE
  refine Subgroup.subgroupOf_mono _ (rootSpan_mono ?_)
  intro β hβ
  exact ⟨hβ.1, by rw [hβ.2]; norm_num⟩

theorem z0E_central :
    z0E ≤ Subgroup.centralizer (qE : Set EC) := by
  have hcomm : ∀ γ ∈ zRoots, ∀ β ∈ qRoots, ∀ c d : F2,
      Commute (pinnedX .E6 F2 γ c) (pinnedX .E6 F2 β d) := by
    intro γ hγ β hβ c d
    refine TwistedE6Cover.commute_pinnedX_of_iform hγ.1 hβ.1 ?_ ?_ c d
    · change γ ≠ (-β : Fin Tag.E6.rank → ℤ)
      intro hneg
      have hlev : iform γ lamE = -iform β lamE := by rw [hneg, iform_neg_left]
      rw [hγ.2] at hlev
      have h2 : iform β lamE = -2 := by linarith
      have hpos : 0 < iform β lamE := hβ.2
      rw [h2] at hpos
      norm_num at hpos
    · exact e6rb_level_check β (mem_rootFinset.2 hβ.1) γ (mem_rootFinset.2 hγ.1) hβ.2 hγ.2
  have hcentral : rootSpan .E6 F2 zRoots ≤
      Subgroup.centralizer (rootSpan .E6 F2 qRoots : Set (ModGL .E6 F2)) := by
    unfold rootSpan
    refine iSup_le fun γ => iSup_le fun hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup_le fun β => iSup_le fun hβ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro x ⟨d, rfl⟩
    change pinnedX .E6 F2 β d ∈
      Subgroup.centralizer (rootSubgroup .E6 F2 γ : Set (ModGL .E6 F2))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [rootSubgroup] at hy
    exact (e6rb_commute_of_mem_closure
      (t := pinnedX .E6 F2 β d) (A := Set.range (pinnedX .E6 F2 γ))
      (by rintro _ ⟨c, rfl⟩; exact (hcomm γ hγ β hβ c d).symm) hy).symm.eq
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 (hcentral hz) (q : ModGL .E6 F2) hq

theorem qE_isPGroup :
    IsPGroup 2 qE := by
  have hcardF2 : Nat.card F2 = 2 := by
    rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num), pow_one]
  have hcard : Nat.card (parabolicRadical .E6 F2 E6Pilot.nodes16) =
      2 ^ (parabolicRadicalRoots .E6 E6Pilot.nodes16).ncard := by
    rw [card_parabolicRadical, hcardF2]
  have hpg : IsPGroup 2 (parabolicRadical .E6 F2 E6Pilot.nodes16) := IsPGroup.of_card hcard
  have hstd : IsPGroup 2 qStd := by
    have heq : qStd = (parabolicRadical .E6 F2 E6Pilot.nodes16).subgroupOf (adjointGroup .E6 F2) := by
      rw [qStd, stdQRoots, parabolicRadical, E6Pilot.parabolicRadicalRoots_nodes16]
    rw [heq, ← Subgroup.inf_subgroupOf_right]
    exact (hpg.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : parabolicRadical .E6 F2 E6Pilot.nodes16 ⊓
        adjointGroup .E6 F2 ≤ adjointGroup .E6 F2)).symm
  rw [qE_eq_map_qStd]
  exact hstd.map (MulAut.conj nQ).toMonoidHom

theorem rE_le_z0E : rE ≤ z0E := by
  have hx : ∀ β, β ∈ zRoots → xr β ∈ z0E := by
    intro β hβ
    rw [z0E]
    exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hβ 1)
  have hz1 : a5Root (blk 0 0) (blk 2 0) ∈ zRoots :=
    ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_iform_check.1⟩
  have hz2 : a5Root (blk 0 1) (blk 2 1) ∈ zRoots :=
    ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_iform_check.2.1⟩
  have hz3 : a5Root (blk 0 0) (blk 2 1) ∈ zRoots :=
    ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_iform_check.2.2.1⟩
  have hz4 : a5Root (blk 0 1) (blk 2 0) ∈ zRoots :=
    ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_iform_check.2.2.2⟩
  rw [rE, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · rw [rOne]
    exact mul_mem (hx _ hz1) (hx _ hz2)
  · rw [rOmega]
    exact mul_mem (mul_mem (hx _ hz3) (hx _ hz4)) (hx _ hz2)

theorem rE_ne_bot :
    rE ≠ ⊥ := by
  intro hbot
  have hmem : rOne 0 2 ∈ rE := Subgroup.subset_closure (Or.inl rfl)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hne : a5Root (blk 0 0) (blk 2 0) ≠ a5Root (blk 0 1) (blk 2 1) := e6rb_rOne_check.1
  have hpos : ∀ α ∈ [a5Root (blk 0 0) (blk 2 0), a5Root (blk 0 1) (blk 2 1)],
      IsRoot .E6 α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl
    · exact ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_rOne_check.2.1⟩
    · exact ⟨mem_rootFinset.1 (a5Root_check _ _ (by decide)), e6rb_rOne_check.2.2⟩
  have h1 : ((List.map fun σ => pinnedX .E6 F2 σ ((fun _ => (1 : F2)) σ))
      [a5Root (blk 0 0) (blk 2 0), a5Root (blk 0 1) (blk 2 1)]).prod =
      ((List.map fun σ => pinnedX .E6 F2 σ ((fun _ => (0 : F2)) σ))
      [a5Root (blk 0 0) (blk 2 0), a5Root (blk 0 1) (blk 2 1)]).prod := by
    have hval := congrArg Subtype.val hmem
    simpa [rOne, xr, pinnedX_zero] using hval
  exact one_ne_zero (pinnedX_list_prod_injective
    [a5Root (blk 0 0) (blk 2 0), a5Root (blk 0 1) (blk 2 1)]
    (by simpa [List.nodup_cons] using hne) hpos (fun _ => 1) (fun _ => 0) h1
    (a5Root (blk 0 0) (blk 2 0)) (by simp))

theorem rE_le_jE : rE ≤ jE :=
  Subgroup.closure_mono (by
    rintro g (rfl | rfl)
    · exact ⟨0, 2, by decide, Or.inl rfl⟩
    · exact ⟨0, 2, by decide, Or.inr rfl⟩)

theorem rmE_le_jE : rmE ≤ jE :=
  Subgroup.closure_mono (by
    rintro g (rfl | rfl)
    · exact ⟨2, 0, by decide, Or.inl rfl⟩
    · exact ⟨2, 0, by decide, Or.inr rfl⟩)

theorem j0E_le_jE : j0E ≤ jE :=
  sup_le rE_le_jE rmE_le_jE

theorem isPGroup_rE :
    IsPGroup 2 rE :=
  qE_isPGroup.to_le (rE_le_z0E.trans z0E_le_qE)

theorem qE_le_normalizer_rE :
    qE ≤ Subgroup.normalizer (rE : Set EC) := by
  have key : ∀ q ∈ qE, ∀ y ∈ rE, q * y * q⁻¹ = y := by
    intro q hq y hy
    have h := Subgroup.mem_centralizer_iff.1 (z0E_central (rE_le_z0E hy)) q hq
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [key q hq x hx]
    exact hx
  · intro hx
    have h2 := key q⁻¹ (qE.inv_mem hq) _ hx
    have h3 : q⁻¹ * (q * x * q⁻¹) * q⁻¹⁻¹ = x := by group
    rw [h3] at h2
    rw [h2]
    exact hx

theorem rE_basic :
    rE ≤ jE ∧ rE ≠ ⊥ ∧ IsPGroup 2 rE ∧ j0E ≤ jE :=
  ⟨rE_le_jE, rE_ne_bot, isPGroup_rE, j0E_le_jE⟩

end CFSG.StandardType.GGSixE6Two
