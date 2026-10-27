module

public import CFSG.RankThree.PartTwo.Late.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

@[expose] def autIn (H X : Subgroup G) : Subgroup (MulAut X) :=
  ((H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))).map
    X.normalizerMonoidHom

theorem mem_autIn_iff {H X : Subgroup G} {σ : MulAut X} :
    σ ∈ autIn H X ↔ ∃ (h : G) (hN : h ∈ Subgroup.normalizer (X : Set G)), h ∈ H ∧
      X.normalizerMonoidHom ⟨h, hN⟩ = σ := by
  constructor
  · rintro ⟨⟨h, hN⟩, hh, rfl⟩
    exact ⟨h, hN, (Subgroup.mem_subgroupOf.mp hh).1, rfl⟩
  · rintro ⟨h, hN, hH, rfl⟩
    exact ⟨⟨h, hN⟩, Subgroup.mem_subgroupOf.mpr ⟨hH, hN⟩, rfl⟩

theorem normalizerMonoidHom_apply_coe {X : Subgroup G} {h : G}
    (hN : h ∈ Subgroup.normalizer (X : Set G)) (x : X) :
    ((X.normalizerMonoidHom ⟨h, hN⟩ x : X) : G) = h * x * h⁻¹ :=
  rfl

theorem aschbacherSolvableCore_characteristic (H : Type*) [Group H] [Finite H] :
    (aschbacherSolvableCore 3 H).Characteristic :=
  (solvable_prime_complement_core_characterization Nat.prime_three).2.1

theorem map_aschbacherSolvableCore {H : Type*} [Group H] [Finite H] (σ : MulAut H) :
    (aschbacherSolvableCore 3 H).map (σ : H →* H) = aschbacherSolvableCore 3 H :=
  (Subgroup.characteristic_iff_map_eq.mp (aschbacherSolvableCore_characteristic H)) σ

@[expose] noncomputable def thetaQuotMulAut (H : Type*) [Group H] [Finite H] :
    MulAut H →* MulAut (H ⧸ aschbacherSolvableCore 3 H) where
  toFun σ := QuotientGroup.congr _ _ σ (map_aschbacherSolvableCore σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem thetaQuotMulAut_mk {H : Type*} [Group H] [Finite H] (σ : MulAut H) (x : H) :
    thetaQuotMulAut H σ (x : H ⧸ aschbacherSolvableCore 3 H) =
      ((σ x : H) : H ⧸ aschbacherSolvableCore 3 H) :=
  rfl

@[expose] noncomputable def autThetaQuot [Finite G] (H L : Subgroup G) :
    Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
  (autIn H L).map (thetaQuotMulAut L)

theorem mem_autThetaQuot_iff [Finite G] {H L : Subgroup G}
    {τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)} :
    τ ∈ autThetaQuot H L ↔ ∃ (h : G) (hN : h ∈ Subgroup.normalizer (L : Set G)), h ∈ H ∧
      thetaQuotMulAut L (L.normalizerMonoidHom ⟨h, hN⟩) = τ := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨h, hN, hH, rfl⟩ := mem_autIn_iff.mp hσ
    exact ⟨h, hN, hH, rfl⟩
  · rintro ⟨h, hN, hH, rfl⟩
    exact ⟨_, mem_autIn_iff.mpr ⟨h, hN, hH, rfl⟩, rfl⟩

@[expose] noncomputable def thetaQuotCentralizer [Finite G] (L : Subgroup G) : Subgroup G :=
  ((thetaQuotMulAut L).comp L.normalizerMonoidHom).ker.map
    (Subgroup.normalizer (L : Set G)).subtype

@[expose] def compAction (L : Subgroup G) : Subgroup.normalizer (L : Set G) →* MulAut L :=
  L.normalizerMonoidHom

theorem compAction_ker (L : Subgroup G) :
    (compAction L).ker =
      (Subgroup.centralizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G)) :=
  Subgroup.normalizerMonoidHom_ker L

@[expose] def InducesOuter (x : G) (L : Subgroup G) : Prop :=
  ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
    compAction L ⟨x, hx⟩ ∉ (MulAut.conj : L →* MulAut L).range

@[expose] def InducesOuterTheta [Finite G] (x : G) (L : Subgroup G) : Prop :=
  ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) ∉
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →*
        MulAut (L ⧸ aschbacherSolvableCore 3 L)).range

@[expose] def HasSection (J : Type*) [Group J] (T : Type*) [Group T] : Prop :=
  ∃ (H : Subgroup J) (N : Subgroup H) (_ : N.Normal), Nonempty (H ⧸ N ≃* T)

@[expose] def IsExtOf (X : Type*) [Group X] (A : Type*) [Group A] (B : Type*) [Group B] : Prop :=
  ∃ (K : Subgroup X) (_ : K.Normal), Nonempty (K ≃* B) ∧ Nonempty (X ⧸ K ≃* A)

@[expose] def oTwoFitting (X : Type*) [Group X] : Subgroup X :=
  (fittingSubgroup (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

@[expose] def oTwoP (p : ℕ) (X : Type*) [Group X] : Subgroup X :=
  (CFSG.pCore p (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

@[expose] def oOddTwo (X : Type*) [Group X] : Subgroup X :=
  (CFSG.pCore 2 (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X))

theorem pCore_two_le_oTwoFitting (X : Type*) [Group X] : CFSG.pCore 2 X ≤ oTwoFitting X :=
  fun x hx => by
    rw [oTwoFitting, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _

theorem pCore_two_le_oTwoP (p : ℕ) (X : Type*) [Group X] : CFSG.pCore 2 X ≤ oTwoP p X :=
  fun x hx => by
    rw [oTwoP, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _

theorem oddCore_le_oOddTwo (X : Type*) [Group X] : CFSG.oddCore X ≤ oOddTwo X :=
  fun x hx => by
    rw [oOddTwo, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _

structure Ctx434 (G : Type) [Group G] [Finite G] (A M Q : Subgroup G) : Prop where
  sectionFourHyp : SectionFourHyp G
  isE27 : Late.IsE27 A
  gamma_le : gamma 2 A ≤ M
  theta_eq_bot : aschbacherSolvableCore 3 G = ⊥
  pRank_eq : CFSG.Open.pRank 3 M = 3
  mem_invariant : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3)
  ne_bot : Q ≠ ⊥
  isQuasisimple : IsQuasisimple (layer G)
  not_le : ¬ layer G ≤ M

structure Ctx444 (G : Type) [Group G] [Finite G] (A M : Subgroup G) : Prop where
  sectionFourHyp : SectionFourHyp G
  isE27 : Late.IsE27 A
  lt_top : M < ⊤
  pRank_eq : CFSG.Open.pRank 3 M = 3
  gamma_le : gamma 2 A ≤ M

end CFSG.RankThree.PartTwo.Sec4
