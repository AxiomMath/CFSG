module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Inj
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Endgame

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.TauCetiBridge.BigCell TauCeti TauCeti.F4ShortRoot.PrimeField

variable {L : Type} [Field L] [Algebra (ZMod 2) L]

theorem nodeF_surjective : Function.Surjective nodeF := fun i =>
  ⟨⟨i, i.2⟩, rfl⟩

theorem adjointGroup_le_range : adjointGroup .F4 L ≤ (adPoints L).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hx | hy⟩
  · obtain ⟨j, rfl⟩ := nodeF_surjective i
    exact ⟨_, (adPoints_rootSubgroupPoints_inl j c).trans (Units.ext hx.symm)⟩
  · obtain ⟨j, rfl⟩ := nodeF_surjective i
    exact ⟨_, (adPoints_rootSubgroupPoints_inr j c).trans (Units.ext hy.symm)⟩

variable (L) in
@[expose] def ZerosInAdjoint : Prop :=
  ∀ H : Subgroup (ModGL .F4 L), adjointGroup .F4 L ≤ H →
    (∀ h ∈ H, ∀ P, VanishesOnRat .F4 P →
      evalMat (natMat .F4 L (h : Module.End L (RootModule .F4 L))) P = 0) →
    H ≤ adjointGroup .F4 L

theorem zerosInAdjoint_of_isAlgClosed [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod 2) L] :
    ZerosInAdjoint L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) L).injective 2
  exact fun H hCH hH => CFSG.TauCetiBridge.Even.le_adjointGroup_F4_two_rankThree (p := 2) rfl H hCH hH

theorem range_adPoints (hZ : ZerosInAdjoint L) : (adPoints L).range = adjointGroup .F4 L := by
  refine le_antisymm (hZ _ adjointGroup_le_range ?_) adjointGroup_le_range
  rintro _ ⟨g, rfl⟩ P hP
  rw [coe_adPoints]
  exact evalMat_natMat_adConj_of_mem_points g.2 P hP

@[expose] def adEquiv (hZ : ZerosInAdjoint L) : points L ≃* adjointGroup .F4 L :=
  (MonoidHom.ofInjective (f := adPoints L) adPoints_injective).trans
    (MulEquiv.subgroupCongr (range_adPoints hZ))

theorem coe_adEquiv (hZ : ZerosInAdjoint L) (g : points L) :
    ((adEquiv hZ g : adjointGroup .F4 L) : ModGL .F4 L) = adPoints L g :=
  rfl

theorem adEquiv_rootSubgroupPoints_inl (hZ : ZerosInAdjoint L) (i : Fin 4) (t : L) :
    adEquiv hZ (rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd t)) = xElement (nodeF i) t :=
  Subtype.ext (adPoints_rootSubgroupPoints_inl i t)

theorem adEquiv_rootSubgroupPoints_inr (hZ : ZerosInAdjoint L) (i : Fin 4) (t : L) :
    adEquiv hZ (rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd t)) = yElement (nodeF i) t :=
  Subtype.ext (adPoints_rootSubgroupPoints_inr i t)

variable (hZ : ZerosInAdjoint L)

@[expose] def nativeSteinberg (S : points L →* points L) :
    adjointGroup .F4 L →* adjointGroup .F4 L :=
  ((adEquiv hZ).toMonoidHom.comp S).comp (adEquiv hZ).symm.toMonoidHom

theorem nativeSteinberg_comp (S : points L →* points L) :
    ((adEquiv hZ : points L ≃* adjointGroup .F4 L) : points L →* adjointGroup .F4 L).comp S =
      (nativeSteinberg hZ S).comp
        ((adEquiv hZ : points L ≃* adjointGroup .F4 L) : points L →* adjointGroup .F4 L) := by
  ext g
  simp [nativeSteinberg]

@[expose] def fixedPointCandidateEquiv (S : points L →* points L) :
    FixedPointCandidate S ≃* FixedPointCandidate (nativeSteinberg hZ S) :=
  FixedPointCandidate.congr (adEquiv hZ) (nativeSteinberg_comp hZ S)

@[expose] def IsReeSteinberg (m : ℕ) (S : points L →* points L) : Prop :=
  ∀ (k : Fin 4 ⊕ Fin 4) (u : L), S (rootSubgroupPoints k L (Multiplicative.ofAdd u)) =
    rootSubgroupPoints (TauCeti.F4ShortRoot.isogenyReverse k) L
      (Multiplicative.ofAdd (u ^ (2 ^ m * TauCeti.F4ShortRoot.isogenyExponent k)))

theorem perm_nodeF (i : Fin 4) : ReeTag.F4.perm (nodeF i) = nodeF (Fin.rev i) := by
  fin_cases i <;> rfl

theorem exponent_nodeF (i : Fin 4) :
    ReeTag.F4.exponent (nodeF i) = TauCeti.F4ShortRoot.isogenyExponent (.inl i) := by
  fin_cases i <;> decide

theorem relationExponent_nodeF (m : ℕ) (i : Fin 4) :
    ReeTag.F4.relationExponent m (nodeF i) =
      2 ^ m * TauCeti.F4ShortRoot.isogenyExponent (.inl i) := by
  refine (ReeTag.relationExponent_eq ReeTag.F4 m (nodeF i)).trans ?_
  exact congrArg (ReeTag.F4.prime ^ m * ·) (exponent_nodeF i)

theorem isogenyExponent_inr (i : Fin 4) :
    TauCeti.F4ShortRoot.isogenyExponent (.inr i) =
      TauCeti.F4ShortRoot.isogenyExponent (.inl i) := by
  fin_cases i <;> decide

variable {m : ℕ} {S : points L →* points L}

theorem nativeSteinberg_xElement (hS : IsReeSteinberg m S) (i : Fin Tag.F4.rank) (c : L) :
    nativeSteinberg hZ S (xElement i c) =
      xElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent m i) := by
  obtain ⟨j, rfl⟩ := nodeF_surjective i
  rw [← adEquiv_rootSubgroupPoints_inl hZ j c]
  simp only [nativeSteinberg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rw [hS]
  change adEquiv hZ (rootSubgroupPoints (.inl (Fin.rev j)) L _) = _
  rw [adEquiv_rootSubgroupPoints_inl, perm_nodeF, relationExponent_nodeF]
  rfl

theorem nativeSteinberg_yElement (hS : IsReeSteinberg m S) (i : Fin Tag.F4.rank) (c : L) :
    nativeSteinberg hZ S (yElement i c) =
      yElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent m i) := by
  obtain ⟨j, rfl⟩ := nodeF_surjective i
  rw [← adEquiv_rootSubgroupPoints_inr hZ j c]
  simp only [nativeSteinberg, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  rw [hS]
  change adEquiv hZ (rootSubgroupPoints (.inr (Fin.rev j)) L _) = _
  rw [adEquiv_rootSubgroupPoints_inr, perm_nodeF, relationExponent_nodeF, isogenyExponent_inr]
  rfl

end CFSG.TauCetiBridge.ReeF4
