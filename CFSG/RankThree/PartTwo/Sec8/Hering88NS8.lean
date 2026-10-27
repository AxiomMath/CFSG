module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCore
public import CFSG.RankThree.PartTwo.Sec8.Item812Res10ProofUnitary
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.Assembly.RankThreeEven (projImage)

section Theta

variable {G : Type} [Group G] [Finite G]

theorem card_quot_theta_dvd_card_imageModTheta {W M : Subgroup G} (hWM : W ≤ M) :
    Nat.card (W ⧸ aschbacherSolvableCore 3 W) ∣ Nat.card (imageModTheta M W) := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := W) Nat.prime_three
  set ρ := Item87Proof.modThetaOnto hWM with hρ
  have hker : ρ.ker ≤ aschbacherSolvableCore 3 W :=
    hθmax _ (MonoidHom.normal_ker ρ) (Item87Proof.isSolvable_ker_modThetaOnto hWM)
      (Item87Proof.not_three_dvd_card_ker_modThetaOnto hWM)
  have h1 : Nat.card W = Nat.card (imageModTheta M W) * Nat.card ρ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ
      (Item87Proof.modThetaOnto_surjective hWM)).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
  have h2 : Nat.card W =
      Nat.card (W ⧸ aschbacherSolvableCore 3 W) * Nat.card (aschbacherSolvableCore 3 W) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card ρ.ker := Nat.card_pos
  refine ⟨t, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
  rw [← h1, h2, ht]
  ring

theorem card_quot_theta_eq_of_isSimpleGroup {W M : Subgroup G} (hWM : W ≤ M)
    {R : Subgroup (M ⧸ aschbacherSolvableCore 3 M)}
    (hW : imageModTheta M W = inSubgroup perfectResidual R)
    (hS : IsSimpleGroup (inSubgroup perfectResidual R)) :
    Nat.card (W ⧸ aschbacherSolvableCore 3 W) = Nat.card (inSubgroup perfectResidual R) := by
  haveI := hS
  have hθ : NoThetaNormal ↥(imageModTheta M W) :=
    Item87Proof.NoThetaNormal.of_mulEquiv (MulEquiv.subgroupCongr hW)
      (Item812Res10.noThetaNormal_of_isSimpleGroup_of_isPerfect (Item87Proof.isPerfect_residual R))
  obtain ⟨χ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hWM hθ
  rw [Nat.card_congr χ.toEquiv, hW]

end Theta

section PGU

variable {Q : Type} [Group Q] [Finite Q]

theorem nonempty_inSubgroup_perfectResidual_mulEquiv_of_isoPGUThree {R : Subgroup Q} {m : ℕ}
    (hm : 2 ≤ m) (h : IsoPGUThree R (2 ^ m)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (hPi : Sec4.PiField false 2 m K),
      Nonempty (inSubgroup perfectResidual R ≃* projImage (Sec4.slPi false 3 (2 ^ m) K)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hPi : Sec4.PiField false 2 m K := ⟨Nat.prime_two, by omega, hK⟩
  have hq2 : 2 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hU := hPi.unitary
  have hSP : projImage (Sec4.slPi false 3 (2 ^ m) K) ≤ projImage (Sec4.glPi false 3 (2 ^ m) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (fun _ => hU))
  refine ⟨K, inferInstance, inferInstance, hPi, ⟨?_⟩⟩
  exact ((perfectResidual R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
    ((Item8KFacts2Proof.perfectResidualEquivOfMulEquiv e).trans
      ((MulEquiv.subgroupCongr (Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hPi hq2)).trans
        (Subgroup.subgroupOfEquivOfLe hSP)))

theorem isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree {R : Subgroup Q} {m : ℕ}
    (hm : 2 ≤ m) (h : IsoPGUThree R (2 ^ m)) : IsSimpleGroup (inSubgroup perfectResidual R) := by
  obtain ⟨K, _, _, hPi, ⟨e⟩⟩ := nonempty_inSubgroup_perfectResidual_mulEquiv_of_isoPGUThree hm h
  have hq2 : 2 < 2 ^ m := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  haveI := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hPi hq2
  exact e.isSimpleGroup

theorem card_le_three_mul_card_inSubgroup_perfectResidual_of_isoPGUThree {R : Subgroup Q} {m : ℕ}
    (hm : 2 ≤ m) (h : IsoPGUThree R (2 ^ m)) :
    Nat.card R ≤ 3 * Nat.card (inSubgroup perfectResidual R) := by
  obtain ⟨k, -, hk3, hk⟩ := Item812Res10.exists_card_eq_mul_card_perfectResidual hm h
  have hc : Nat.card (inSubgroup perfectResidual R) = Nat.card (perfectResidual R) :=
    Subgroup.card_map_of_injective R.subtype_injective
  rw [hk, hc]
  exact Nat.mul_le_mul_right _ hk3

end PGU

section Tits


variable {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]

theorem perfectResidual_reeFixed_zero (hk : Nat.card k = 2) :
    perfectResidual (reeFixed ReeTag.F4 k 0) = commutator (reeFixed ReeTag.F4 k 0) := by
  have hT := CFSG.LieType.Simplicity.titsData k hk
  refine le_antisymm ?_ ((CFSG.perfect_residual_transport (MonoidHom.id _)).2.2 _
    (hT.isPerfect hk))
  have h := iInf_le (fun i => derivedSeries (reeFixed ReeTag.F4 k 0) i) 1
  rwa [derivedSeries_one] at h

theorem isSimpleGroup_commutator_reeFixed_zero (hk : Nat.card k = 2) :
    IsSimpleGroup (commutator (reeFixed ReeTag.F4 k 0)) := by
  have hT := CFSG.LieType.Simplicity.titsData k hk
  set D := commutator (reeFixed ReeTag.F4 k 0) with hD
  haveI : Nontrivial D := ⟨⟨⟨hT.g₀, hT.g₀_mem⟩, 1, fun h => hT.g₀_ne_one (congrArg Subtype.val h)⟩⟩
  refine ⟨fun N hN => ?_⟩
  rcases hT.eq_bot_or_eq_of_le hk (N.map D.subtype) (Subgroup.map_subtype_le N)
      (by
        rintro d hd _ ⟨m, hm, rfl⟩
        exact ⟨⟨d, hd⟩ * m * ⟨d, hd⟩⁻¹, hN.conj_mem m hm ⟨d, hd⟩, rfl⟩) with h | h
  · left
    rw [eq_bot_iff]
    intro m hm
    have hm' : (m : reeFixed ReeTag.F4 k 0) ∈ N.map D.subtype := ⟨m, hm, rfl⟩
    rw [h, Subgroup.mem_bot] at hm'
    exact (Subgroup.mem_bot).2 (Subtype.ext hm')
  · right
    rw [eq_top_iff]
    intro m _
    have hm' : (m : reeFixed ReeTag.F4 k 0) ∈ N.map D.subtype := by
      rw [h]
      exact m.2
    obtain ⟨m₁, hm₁, he⟩ := hm'
    rwa [← Subtype.ext he]

theorem card_commutator_reeFixed_zero (hk : Nat.card k = 2) :
    Nat.card (reeFixed ReeTag.F4 k 0) = 35942400 ∧
      Nat.card (reeFixed ReeTag.F4 k 0) ≤ 2 * Nat.card (commutator (reeFixed ReeTag.F4 k 0)) := by
  have hT := CFSG.LieType.Simplicity.titsData k hk
  set R := reeFixed ReeTag.F4 k 0 with hR
  have hk' : Nat.card k = 2 ^ (2 * 0 + 1) := by rw [hk]; norm_num
  have hcard : Nat.card R = 35942400 := by
    rw [Nat.card_congr (ReeTag.reeFixedEquivReeGamma k 0).toEquiv,
      (LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion 0 k hk').1]
    norm_num
  refine ⟨hcard, ?_⟩
  have hsup : commutator R ⊔ Subgroup.zpowers hT.g₁ = ⊤ := hT.commutator_sup_zpowers_eq_top hk
  have hg2 := hT.g₁_sq_mem
  have : (commutator R).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hQ : Nat.card (R ⧸ commutator R) ≤ 2 := by
    set g := QuotientGroup.mk' (commutator R) hT.g₁ with hgdef
    have hg2' : g ^ 2 = 1 := by
      rw [hgdef, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hg2
    have hall : ∀ y : R ⧸ commutator R, y ∈ Subgroup.zpowers g := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H y =>
        have hy : y ∈ commutator R ⊔ Subgroup.zpowers hT.g₁ := hsup ▸ Subgroup.mem_top y
        obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        refine ⟨i, ?_⟩
        have hc1 : QuotientGroup.mk' (commutator R) c = 1 :=
          (QuotientGroup.eq_one_iff c).2 hc
        change g ^ i = QuotientGroup.mk' (commutator R) (c * hT.g₁ ^ i)
        rw [map_mul, hc1, one_mul, map_zpow]
    have hcard' := orderOf_eq_card_of_forall_mem_zpowers hall
    rw [← hcard']
    exact orderOf_le_of_pow_eq_one (by norm_num) hg2'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator R)]
  exact Nat.mul_le_mul_right _ hQ

variable {Q : Type} [Group Q] [Finite Q]

theorem isSimpleGroup_inSubgroup_perfectResidual_of_reeGamma_zero {C : Subgroup Q}
    (hk : Nat.card k = 2) (φ : C ≃* ReeTag.F4.reeGamma k 0) :
    IsSimpleGroup (inSubgroup perfectResidual C) := by
  set ψ : C ≃* reeFixed ReeTag.F4 k 0 := φ.trans (ReeTag.reeFixedEquivReeGamma k 0).symm
  haveI := isSimpleGroup_commutator_reeFixed_zero hk
  have e : inSubgroup perfectResidual C ≃* commutator (reeFixed ReeTag.F4 k 0) :=
    ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      ((Item8KFacts2Proof.perfectResidualEquivOfMulEquiv ψ).trans
        (MulEquiv.subgroupCongr (perfectResidual_reeFixed_zero hk)))
  exact e.isSimpleGroup

theorem card_inSubgroup_perfectResidual_of_reeGamma_zero {C : Subgroup Q}
    (hk : Nat.card k = 2) (φ : C ≃* ReeTag.F4.reeGamma k 0) :
    17971200 ≤ Nat.card (inSubgroup perfectResidual C) ∧
      Nat.card (inSubgroup perfectResidual C) ≤ 35942400 := by
  set ψ : C ≃* reeFixed ReeTag.F4 k 0 := φ.trans (ReeTag.reeFixedEquivReeGamma k 0).symm
  have e : inSubgroup perfectResidual C ≃* commutator (reeFixed ReeTag.F4 k 0) :=
    ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      ((Item8KFacts2Proof.perfectResidualEquivOfMulEquiv ψ).trans
        (MulEquiv.subgroupCongr (perfectResidual_reeFixed_zero hk)))
  obtain ⟨hR, hle⟩ := card_commutator_reeFixed_zero hk
  have hD := Subgroup.card_le_card_group (commutator (reeFixed ReeTag.F4 k 0))
  rw [Nat.card_congr e.toEquiv]
  omega

end Tits

section G2


variable {Q : Type} [Group Q] [Finite Q]

theorem card_inSubgroup_perfectResidual_ge_of_isoGTwoEven {R : Subgroup Q} {m : ℕ} (hm : 2 ≤ m)
    (h : IsoGTwoEven R m) : 251596800 ≤ Nat.card (inSubgroup perfectResidual R) := by
  rw [Hering88F.inSubgroup_perfectResidual_eq_of_isoGTwoEven hm h]
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
  set q := 2 ^ m with hq
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h1 : 4096 ≤ q ^ 6 := by
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq4 6
  have h2 : 16 ≤ q ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
  show 251596800 ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
  calc 251596800 = 4096 * (4096 - 1) * (16 - 1) := by norm_num
    _ ≤ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)

end G2

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
