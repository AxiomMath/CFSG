module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinRed
public import CFSG.LocalAnalysis.StandardType.GGIOneExcLift
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.StandardType.S2MathAs4B2der1822

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def SympTwo (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 3 ≤ lab.rank

@[expose] def LinearLab (lab : LargeEvenLabel) : Prop := lab.tag = .A

@[expose] def UnitaryLab (lab : LargeEvenLabel) : Prop := lab.tag = .twA

@[expose] def OrthLab (lab : LargeEvenLabel) : Prop := lab.tag = .D ∨ lab.tag = .twD

@[expose] def SympLab (lab : LargeEvenLabel) : Prop := lab.tag = .B ∨ lab.tag = .C

@[expose] def ExceptionalLab (lab : LargeEvenLabel) : Prop :=
  match lab.tag with
  | .E6 | .E7 | .E8 | .F4 | .twE6 | .triD4 | .G2 | .twB2 | .twF4 => True
  | _ => False

@[expose] def SmallDerivedLab (lab : LargeEvenLabel) : Prop :=
  match lab.tag with
  | .B2der | .G2der | .twF4der => True
  | _ => False

@[expose] def SimpleA1Input (P C : LargeEvenLabel → Prop) : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → P lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
        ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
          GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) → C lab

@[expose] def SimpleNoB2derInput (P : LargeEvenLabel → Prop) : Prop :=
  SimpleA1Input P (fun _ => False)

@[expose] def LinearNoB2derInput : Prop := SimpleNoB2derInput LinearLab

@[expose] def UnitaryNoB2derInput : Prop := SimpleNoB2derInput UnitaryLab

@[expose] def OrthNoB2derInput : Prop := SimpleNoB2derInput OrthLab

@[expose] def ExceptionalNoB2derInput : Prop := SimpleNoB2derInput ExceptionalLab

@[expose] def SmallDerivedNoB2derInput : Prop := SimpleNoB2derInput SmallDerivedLab

@[expose] def SimpleSympFieldInput : Prop :=
  SimpleA1Input SympLab (fun lab => lab.n = 1 ∧ 3 ≤ lab.rank)

@[expose] def SimpleKnownInput : Prop := SimpleA1Input (fun _ => True) SympTwo

@[expose] def SymplecticBlockPositionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → ∀ (r : ℕ) [NeZero r], 3 ≤ r →
    ∀ g : LargeEvenProj (LargeEvenSpGroup K r), MulAut.conj g ≠ 1 → (MulAut.conj g) ^ 3 = 1 →
      ∀ J : Subgroup (LargeEvenProj (LargeEvenSpGroup K r)),
        IsComponentOf J (ggFixSub (MulAut.conj g)) →
        GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
          Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)) = 4 ∧
          J = ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)),
            ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))⁆

theorem ggHasLabel_congr {lab : LargeEvenLabel} {R R' : Type} [Group R] [Group R']
    (h : GGHasLabel lab R) (e : R ≃* R') : GGHasLabel lab R' :=
  largeEvenRawDatum_mono (fun _ _ _ _ hQ => ⟨e.symm.trans hQ.some⟩) h

private theorem labelAll_of_false {lab : LargeEvenLabel} {C : LargeEvenLabel → Prop}
    (h : LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
        ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
          GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) → False)) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
        ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
          GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) → C lab) := by
  refine ggNbrLabelAll_mono ?_ h
  intro R _ I F hh φ h1 h2 h3 J hJ hl
  exact (hh φ h1 h2 h3 J hJ hl).elim

private theorem labelAll_symp {lab : LargeEvenLabel} (htag : lab.tag = .B ∨ lab.tag = .C)
    (h : LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
        ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
          GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
            lab.n = 1 ∧ 3 ≤ lab.rank)) :
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ φ : MulAut R, φ ≠ 1 → φ ^ 3 = 1 → φ ∈ I →
        ∀ J : Subgroup R, IsComponentOf J (ggFixSub φ) →
          GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
            SympTwo lab) := by
  refine ggNbrLabelAll_mono ?_ h
  intro R _ I F hh φ h1 h2 h3 J hJ hl
  exact ⟨htag, (hh φ h1 h2 h3 J hJ hl).1, (hh φ h1 h2 h3 J hJ hl).2⟩

theorem simpleKnownInput_of_sources
    (hA : LinearNoB2derInput) (htwA : UnitaryNoB2derInput) (hD : OrthNoB2derInput)
    (hE : ExceptionalNoB2derInput) (hS : SmallDerivedNoB2derInput) (hBC : SimpleSympFieldInput) :
    SimpleKnownInput := by
  intro lab hlab _
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  · exact labelAll_of_false (hA ⟨.A, rank, n⟩ hlab rfl)
  · exact labelAll_of_false (htwA ⟨.twA, rank, n⟩ hlab rfl)
  · exact labelAll_symp (Or.inl rfl) (hBC ⟨.B, rank, n⟩ hlab (Or.inl rfl))
  · exact labelAll_symp (Or.inr rfl) (hBC ⟨.C, rank, n⟩ hlab (Or.inr rfl))
  · exact labelAll_of_false (hD ⟨.D, rank, n⟩ hlab (Or.inl rfl))
  · exact labelAll_of_false (hD ⟨.twD, rank, n⟩ hlab (Or.inr rfl))
  · exact labelAll_of_false (hE ⟨.E6, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.E7, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.E8, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.F4, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.twE6, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.triD4, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.G2, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.twB2, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hE ⟨.twF4, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hS ⟨.B2der, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hS ⟨.G2der, rank, n⟩ hlab trivial)
  · exact labelAll_of_false (hS ⟨.twF4der, rank, n⟩ hlab trivial)

theorem induced_nontrivial_order_three
    {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) (e : MulAut L') (he1 : e ≠ 1) (he3 : e ^ 3 = 1)
    (φ : MulAut R) (hφ : ∀ l : L', φ (ψ l) = ψ (e l)) : φ ≠ 1 ∧ φ ^ 3 = 1 := by
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  have hne : φ ≠ 1 := by
    intro hφ1
    apply he1
    refine CFSG.GorensteinWalter.perfect_central_automorphism_eq (E := L') inferInstance e 1 ?_
    intro x
    have hxe : e x * x⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have hx : ψ (e x) = ψ x := by rw [← hφ x, hφ1]; simp
      rw [hx]; simp
    exact hker hxe
  have h3 : φ ^ 3 = 1 := by
    have hiter : ∀ k : ℕ, ∀ l : L', (φ ^ k) (ψ l) = ψ ((e ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
          intro l
          rw [pow_succ', MulAut.mul_apply, ih, hφ, pow_succ', MulAut.mul_apply]
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have h := hiter 3 l
    rw [he3] at h
    simpa using h
  exact ⟨hne, h3⟩

theorem firstHalf_of_simpleKnown (h : SimpleKnownInput) :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ e : MulAut L', e ≠ 1 → e ^ 3 = 1 →
            (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
            ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
              GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
                (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 3 ≤ lab.rank := by
  intro lab hlab
  refine ggNbrLabelAll_mono ?_ (h lab hlab trivial)
  intro R _ I F hSK L' _ _ ψ hψ hker hperf e he1 he3 hφex J hJ hJlab
  obtain ⟨φ, hφI, hφcompat⟩ := hφex
  obtain ⟨hφne, hφ3⟩ := induced_nontrivial_order_three ψ hψ hker hperf e he1 he3 φ hφcompat
  obtain ⟨hJmap, ⟨eQ⟩⟩ :=
    CFSG.StandardType.S2MathAs51600.centralFixedComponentTransfer_holds ψ hψ hker e φ
      (fun x => (hφcompat x).symm) J hJ
  have hJmaplab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) := ggHasLabel_congr hJlab eQ
  exact hSK φ hφne hφ3 hφI (J.map ψ) hJmap hJmaplab

theorem center_isPGroup_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} [NeZero r]
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K r))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : IsPGroup 2 (Subgroup.center L') := by
  have hcard : ∃ k, Nat.card (Subgroup.center L') = 2 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => ?_⟩
    by_contra hd2
    exact ggCenterPrime_sp (K := K) (m := r) hd hd2 L' ψ hψ hker hperf hdd
  obtain ⟨k, hk⟩ := hcard
  exact IsPGroup.of_card hk

theorem center_eq_bot_of_four_le
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) {r : ℕ} [NeZero r]
    (hr : 4 ≤ r) {L' : Type} [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K r))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) : Subgroup.center L' = ⊥ := by
  have hker_center : ψ.ker = Subgroup.center L' :=
    ggIE_ker_eq_center hψ (TableBSymp.center_spProj_eq_bot (K := K) (m := r)) hker
  rw [← hker_center]
  exact CFSG.StandardType.SpFin.ker_eq_bot hK hr ψ hψ hker hperf

theorem secondHalf_of_block (hBlock : SymplecticBlockPositionInput) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → ∀ (r : ℕ) [NeZero r], 3 ≤ r →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K r)),
        Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        IsPGroup 2 (Subgroup.center L') ∧ (4 ≤ r → Subgroup.center L' = ⊥) ∧
        ∀ e : MulAut L', e ≠ 1 → e ^ 3 = 1 →
          ∀ g : LargeEvenProj (LargeEvenSpGroup K r), (∀ l : L', ψ (e l) = g * ψ l * g⁻¹) →
            ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
              GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
                Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)) = 4 ∧
                J.map ψ = ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)),
                  ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))⁆ := by
  intro K _ _ _ hK r _ hr L' _ _ ψ hψ hker hperf
  refine ⟨center_isPGroup_two ψ hψ hker hperf,
    fun hr4 => center_eq_bot_of_four_le hK hr4 ψ hψ hker hperf, ?_⟩
  intro e he1 he3 g hgcompat J hJ hJlab
  obtain ⟨hconj_ne, hconj3⟩ :=
    induced_nontrivial_order_three ψ hψ hker hperf e he1 he3 (MulAut.conj g)
      (fun l => by rw [MulAut.conj_apply]; exact (hgcompat l).symm)
  obtain ⟨hJmap, ⟨eQ⟩⟩ :=
    CFSG.StandardType.S2MathAs51600.centralFixedComponentTransfer_holds ψ hψ hker e
      (MulAut.conj g) (fun x => by rw [MulAut.conj_apply]; exact hgcompat x) J hJ
  have hJmaplab : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
      (↥(J.map ψ) ⧸ Subgroup.center ↥(J.map ψ)) := ggHasLabel_congr hJlab eQ
  exact hBlock K hK r hr g hconj_ne hconj3 (J.map ψ) hJmap hJmaplab

theorem ggB2derSympKnown_of_sources
    (hA : LinearNoB2derInput) (htwA : UnitaryNoB2derInput) (hD : OrthNoB2derInput)
    (hE : ExceptionalNoB2derInput) (hS : SmallDerivedNoB2derInput)
    (hSymp : SimpleSympFieldInput) (hBlock : SymplecticBlockPositionInput) :
    GGB2derSympKnown :=
  ⟨firstHalf_of_simpleKnown (simpleKnownInput_of_sources hA htwA hD hE hS hSymp),
   secondHalf_of_block hBlock⟩

end CFSG.StandardType.S2MathAs4B2der1822

end
