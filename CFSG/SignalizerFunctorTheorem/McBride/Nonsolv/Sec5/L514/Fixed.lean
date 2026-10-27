module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Fitting
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.HypA

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_aut_fixed_iff {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G) (hJ : J ∈ lcal G)
    (hact : ¬ A ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    ∃ f : MulAut ↥J, orderOf f = p ∧ ∀ j : ↥J, f j = j ↔
      ∀ b ∈ A ⊓ Subgroup.normalizer (J : Set Γ), b * (j : Γ) * b⁻¹ = j := by
  have hBJ : A ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.normalizer (J : Set Γ) := inf_le_right
  let ρ : ↥(A ⊓ Subgroup.normalizer (J : Set Γ)) →* MulAut ↥J :=
    J.normalizerMonoidHom.comp (Subgroup.inclusion hBJ)
  have hρ : ∀ (b : ↥(A ⊓ Subgroup.normalizer (J : Set Γ))) (j : ↥J),
      ((ρ b j : ↥J) : Γ) = b * j * b⁻¹ := fun b j => rfl
  have hcard : Nat.card ρ.range ∣ p :=
    card_range_conj_dvd h.prime h.elemAbelian h.hypB hJ inf_le_left hBJ
  obtain ⟨b, hb, hbc⟩ : ∃ b ∈ A ⊓ Subgroup.normalizer (J : Set Γ),
      b ∉ Subgroup.centralizer (J : Set Γ) := by
    by_contra hcon
    exact hact fun b hb => by_contra fun hbc => hcon ⟨b, hb, hbc⟩
  have hfR : ρ ⟨b, hb⟩ ∈ ρ.range := ⟨⟨b, hb⟩, rfl⟩
  have hne : ρ ⟨b, hb⟩ ≠ 1 := by
    intro h1
    apply hbc
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h2 : ((ρ ⟨b, hb⟩ ⟨j, hj⟩ : ↥J) : Γ) = j := by rw [h1]; rfl
    rw [hρ] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hord : orderOf (ρ ⟨b, hb⟩) = p := by
    have h1 : orderOf (ρ ⟨b, hb⟩) ∣ p := (Subgroup.orderOf_dvd_natCard ρ.range hfR).trans hcard
    rcases (Nat.dvd_prime h.prime).mp h1 with h2 | h2
    · exact absurd (orderOf_eq_one_iff.mp h2) hne
    · exact h2
  have hrange : ρ.range = Subgroup.zpowers (ρ ⟨b, hb⟩) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfR) ?_
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd h.prime.pos hcard
  refine ⟨ρ ⟨b, hb⟩, hord, fun j => ⟨fun hfj b' hb' => ?_, fun hall => ?_⟩⟩
  · have hstab : Subgroup.zpowers (ρ ⟨b, hb⟩) ≤ MulAction.stabilizer (MulAut ↥J) j := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfj
    have hmem : ρ ⟨b', hb'⟩ ∈ Subgroup.zpowers (ρ ⟨b, hb⟩) := by
      rw [← hrange]
      exact ⟨⟨b', hb'⟩, rfl⟩
    have h2 := MulAction.mem_stabilizer_iff.mp (hstab hmem)
    rw [MulAut.smul_def] at h2
    exact congrArg Subtype.val h2
  · exact Subtype.ext (hall b hb)

theorem hypA_fixed_of_not_central
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A)
    (hact : ¬ A ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    (∀ Y : Subgroup Γ, Y ≤ J → Group.IsSolvable Y → J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) ≤
        Subgroup.normalizer (Y : Set Γ) → Y = ⊥) ∧
    IsFStarSimple ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) ∧
    (∀ x ∈ Subgroup.normalizer (J : Set Γ), Nat.Coprime p (orderOf x) →
      (∀ y ∈ J ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ), x * y * x⁻¹ = y) →
      ∀ j ∈ J, x * j * x⁻¹ = j) := by
  obtain ⟨f, hord, hfix⟩ := exists_aut_fixed_iff h hJ.1 hact
  obtain ⟨-, -, -, -, -, hdisj⟩ := signalizerMcBrideHypothesisA_of_mem_lcal h.hypB hJ.1
  have hnear := not_signalizerNearPSolvable_of_not_isSolvable_smear h.prime h.elemAbelian
    h.normalizes hJ.1 hJ.2 hact
  obtain ⟨h1, h2, h3⟩ := hdisj.resolve_left hnear f hord
  have hmap : (signalizerFixedSubgroup f).map J.subtype = J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨j.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      exact mul_inv_eq_iff_eq_mul.mp ((hfix j).mp hj b hb)
    · intro hy
      obtain ⟨hyJ, hyc⟩ := Subgroup.mem_inf.mp hy
      refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
      exact (hfix ⟨y, hyJ⟩).mpr fun b hb =>
        mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hyc b hb)
  have hmem : ∀ c : ↥J, c ∈ signalizerFixedSubgroup f → (c : Γ) ∈ J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) := fun c hc =>
    hmap ▸ ⟨c, hc, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro Y hYJ hY hTN
    by_contra hne
    let Y' : Subgroup ↥J := Y.subgroupOf J
    have hY' : Group.IsSolvable Y' :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hYJ).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hYJ).injective
    have hY'ne : Y' ≠ ⊥ := by
      intro hbot
      apply hne
      rw [eq_bot_iff]
      intro y hy
      have hy' : (⟨y, hYJ hy⟩ : ↥J) ∈ Y' := hy
      rw [hbot, Subgroup.mem_bot] at hy'
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hy')
    refine h1 Y' hY'ne hY' fun c hc => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp (hTN (hmem c hc)) (y : Γ)
  · have hCf : IsFStarSimple ↥(signalizerFixedSubgroup f) := by
      refine ⟨?_, ?_⟩
      · rw [← signalizerGeneralizedFitting_eq]
        exact h2.1
      · rw [← signalizerGeneralizedFitting_eq, isMulCommutative_iff]
        push Not
        exact h2.2
    exact (isFStarSimple_congr
      ((Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap))).mp hCf
  · intro x hx hxp hfixed j hj
    have hg : J.normalizerMonoidHom ⟨x, hx⟩ = 1 := by
      refine h3 _ ?_ fun y hy => Subtype.ext (hfixed y (hmem y hy))
      refine hxp.coprime_dvd_right ?_
      have := orderOf_map_dvd J.normalizerMonoidHom (⟨x, hx⟩ : ↥(Subgroup.normalizer (J : Set Γ)))
      rwa [Subgroup.orderOf_mk] at this
    have := congrArg (fun g => ((g ⟨j, hj⟩ : ↥J) : Γ)) hg
    simpa using this

omit [Finite Γ] in
theorem hypA_fixed_of_central {p : ℕ} {A G J : Subgroup Γ} (hJ : J ∈ lcal G)
    (hcen : A ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)) :
    (∀ Y : Subgroup Γ, Y ≤ J → Group.IsSolvable Y → J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) ≤
        Subgroup.normalizer (Y : Set Γ) → Y = ⊥) ∧
    IsFStarSimple ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) ∧
    (∀ x ∈ Subgroup.normalizer (J : Set Γ), Nat.Coprime p (orderOf x) →
      (∀ y ∈ J ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ), x * y * x⁻¹ = y) →
      ∀ j ∈ J, x * j * x⁻¹ = j) := by
  have hTJ : J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) = J :=
    inf_eq_left.mpr fun j hj => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (Subgroup.mem_centralizer_iff.mp (hcen hb) j hj).symm
  rw [hTJ]
  obtain ⟨hJs, hJnc⟩ := (mem_lcal_iff.mp hJ).2.2
  refine ⟨?_, isFStarSimple_of_isSimpleGroup hJnc, fun x _ _ hfix j hj => hfix j hj⟩
  intro Y hYJ hY hJN
  have hnorm : (Y.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff hYJ).mpr fun y j hy hj =>
    (Subgroup.mem_normalizer_iff.mp (hJN hj) y).mp hy
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.subgroupOf J) with hbot | htop
  · rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hYJ hy⟩ : ↥J) ∈ Y.subgroupOf J := hy
    rw [hbot, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hy')
  · exfalso
    have hJY : J ≤ Y := Subgroup.subgroupOf_eq_top.mp htop
    have hsolv : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJY)
        (Subgroup.inclusion_injective hJY)
    exact hJnc ⟨⟨fun a b => IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b⟩⟩

theorem hypA_fixed
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G) (hJ : J ∈ lcalA G A) :
    (∀ Y : Subgroup Γ, Y ≤ J → Group.IsSolvable Y → J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) ≤
        Subgroup.normalizer (Y : Set Γ) → Y = ⊥) ∧
    IsFStarSimple ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) ∧
    (∀ x ∈ Subgroup.normalizer (J : Set Γ), Nat.Coprime p (orderOf x) →
      (∀ y ∈ J ⊓ Subgroup.centralizer
        ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ), x * y * x⁻¹ = y) →
      ∀ j ∈ J, x * j * x⁻¹ = j) := by
  by_cases hact : A ⊓ Subgroup.normalizer (J : Set Γ) ≤ Subgroup.centralizer (J : Set Γ)
  · exact hypA_fixed_of_central hJ.1 hact
  · exact hypA_fixed_of_not_central h hJ hact

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
