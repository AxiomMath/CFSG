module

public import CFSG.Quasithin.Background.A3FactsAssembly
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Background.C116Three.Main
public import CFSG.Quasithin.Background.C116Two.Main
public import CFSG.Quasithin.Background.C116Bridge.Main
public import CFSG.Quasithin.Background.GoldschmidtTDC19
public import CFSG.Quasithin.Background.GoldschmidtTDC111Main
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.EmptyFaithful.Gold14610Blocks
public import CFSG.Quasithin.Vol2.Ch11C113b
public import CFSG.Quasithin.H13.VolIC113a
public import CFSG.Quasithin.H13.VolIC113c
public import CFSG.Quasithin.H13.VolIC113d
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtC124Proved
public import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.Holt.SmallGroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.C123TwoHolds
public import CFSG.Quasithin.H13.A7Nat1236Final
public import CFSG.Quasithin.H13.GoldschmidtC137SQA6
public import CFSG.Quasithin.H13.GoldschmidtC137SQExt
public import CFSG.Quasithin.H13.GoldschmidtC137SQRk

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def IsS2 (R : Subgroup G) : Prop := IsPGroup 2 R ∧ R ≠ ⊥

@[expose] def IsCentralProductOfBlocks (H K : Subgroup G) : Prop :=
  ∃ B : Finset (Subgroup G), (∀ L ∈ B, IsBlock2 H L) ∧
    (∀ L ∈ B, ∀ L' ∈ B, L ≠ L' → L ≤ Subgroup.centralizer (L' : Set G)) ∧ K = ⨆ L ∈ B, L

@[expose] def oUpperPi (π : Set ℕ) (Y : Subgroup G) : Subgroup G :=
  ⨅ (N : Subgroup G) (_ : N ≤ Y ∧ Y ≤ Subgroup.normalizer (N : Set G) ∧
      ∀ y ∈ Y, ∃ m : ℕ, 0 < m ∧ (∀ p ∈ m.primeFactors, p ∈ π) ∧ y ^ m ∈ N), N

@[expose] def QuotQuasisimpleOrThree (L N : Subgroup G) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (φ : ↥L →* Y), Function.Surjective φ ∧ φ.ker = N.subgroupOf L ∧
    (CFSG.IsQuasisimple Y ∨ Nat.card Y = 3)

@[expose] def QuotHas (L N : Subgroup G) (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (φ : ↥L →* Y), Function.Surjective φ ∧ φ.ker = N.subgroupOf L ∧ P Y

structure HypC_1_14 (X V T : Subgroup G) : Prop where
  charTwo : CharTwo X
  reduced : IsTwoReducedIn X V
  sylow : IsSylowTwoOf T X

@[expose] def IsR2Max (H W : Subgroup G) : Prop :=
  IsTwoReducedIn H W ∧ ∀ W' : Subgroup G, IsTwoReducedIn H W' → W' ≤ W

structure InYSet (X R S Y : Subgroup G) : Prop where
  le : Y ≤ X
  perf : Y = oTwoUpper Y
  inv : S ⊔ pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G)
  sylow : IsSylowTwoOf (R ⊓ Y) Y
  natural : ∃ W : Subgroup G, IsR2Max ((S ⊔ pCoreOf 2 X) ⊔ Y) W ∧ ∃ n : ℕ, 1 ≤ n ∧
    IsNatL2Section Y (pCoreOf 2 Y) W (W ⊓ Subgroup.centralizer (Y : Set G)) n

@[expose] def IsMSPairWith [Finite G] (X R L : Subgroup G) : Prop :=
  IsMSPair X R ∧ L ∈ cComp X ∧ (X : Set G) = (L : Set G) * (R : Set G)

structure DualSplit (L U W₁ W₂ : Subgroup G) {F : Type} [Field F]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F)
    (βU : ↥U →* Multiplicative (Fin 3 → F))
    (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F))
    (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)) : Prop where
  alpha_onto : Function.Surjective α
  alpha_ker : α.ker = CFSG.pCore 2 ↥L
  le₁ : U ≤ W₁
  le₂ : U ≤ W₂
  le_Q₁ : W₁ ≤ pCoreOf 2 L
  le_Q₂ : W₂ ≤ pCoreOf 2 L
  join : W₁ ⊔ W₂ = pCoreOf 2 L
  meet : W₁ ⊓ W₂ = U
  norm₁ : L ≤ Subgroup.normalizer (W₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (W₂ : Set G)
  natU_onto : Function.Surjective βU
  natU_ker : βU.ker = ⊥
  natU_act : ∀ (ℓ : ↥L) (u v : ↥U), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (βU v) =
      ((α ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Multiplicative.toAdd (βU u))
  dual₁_onto : Function.Surjective β₁
  dual₁_ker : β₁.ker = U.subgroupOf W₁
  dual₁_act : ∀ (ℓ : ↥L) (u v : ↥W₁), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₁ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₁ u))
  dual₂_onto : Function.Surjective β₂
  dual₂_ker : β₂.ker = U.subgroupOf W₂
  dual₂_act : ∀ (ℓ : ↥L) (u v : ↥W₂), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₂ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₂ u))

@[expose] def InternalModelSection (D : FFModel) (X V U Z : Subgroup G) : Prop :=
  Z ≤ U ∧ U ≤ V ∧ X ≤ Subgroup.normalizer (U : Set G) ∧
    X ≤ Subgroup.normalizer (Z : Set G) ∧ D.ker ≤ D.sec ∧
    (∀ element : D.Gam, ∀ coordinate ∈ D.sec, D.act element coordinate ∈ D.sec) ∧
    (∀ element : D.Gam, ∀ coordinate ∈ D.ker, D.act element coordinate ∈ D.ker) ∧
    ∃ (α : ↥X →* D.Gam) (β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec),
      Function.Surjective α ∧
      α.ker = (X ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X ∧
      Function.Surjective β ∧ β.ker = Z.subgroupOf U ∧
      ∀ (element : ↥X) (original conjugate : ↥U) (coordinate : ↥D.sec)
        (stable : D.act (α element) (coordinate : D.Amb) ∈ D.sec),
        (conjugate : G) = element * original * element⁻¹ →
        β original = QuotientGroup.mk coordinate →
        β conjugate = QuotientGroup.mk ⟨D.act (α element) (coordinate : D.Amb), stable⟩

@[expose] def InternalG2TwoNatural (X V U Z : Subgroup G) : Prop :=
  InternalModelSection (FFModel.zornQ (quasithinG2 (ZMod 2))) X V U Z

@[expose] def InternalS6Natural (X V U Z : Subgroup G) : Prop :=
  InternalModelSection (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 2))) X V U Z

@[expose] def IsG2TwoBlockNatural (L : Subgroup G) : Prop :=
  IsG2Block L ∧
    InternalModelSection (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆)
      L (blockU L) (blockU L) (blockZ L)

@[expose] def IsNatVia {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (A V Z : Subgroup G) (α : ↥A →* Matrix.SpecialLinearGroup ι F)
    (β : ↥V →* Multiplicative (ι → F)) : Prop :=
  Function.Surjective β ∧ β.ker = Z.subgroupOf V ∧
    ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : Matrix.SpecialLinearGroup ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u))

@[expose] def preimageIn {F : Type} [Field F] (V : Subgroup G)
    (β : ↥V →* Multiplicative (Fin 3 → F)) (ℓ : Submodule F (Fin 3 → F)) : Subgroup G :=
  (Subgroup.comap β (AddSubgroup.toSubgroup ℓ.toAddSubgroup)).map V.subtype

structure SumOfTwoNat (L U : Subgroup G) (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (U₁ U₂ : Subgroup G) (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
    (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)) : Prop where
  alpha_onto : Function.Surjective α
  alpha_ker : α.ker = CFSG.pCore 2 ↥L
  le₁ : U₁ ≤ U
  le₂ : U₂ ≤ U
  join : U₁ ⊔ U₂ = U
  meet : U₁ ⊓ U₂ = ⊥
  norm₁ : L ≤ Subgroup.normalizer (U₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (U₂ : Set G)
  nat₁ : IsNatVia L U₁ ⊥ α β₁
  nat₂ : IsNatVia L U₂ ⊥ α β₂

@[expose] def TrivialOnDynkin (L T : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (L : Set G) ∧
  (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
    ∀ t ∈ T, ∃ l : ↥L, ∀ x y : ↥L, (y : G) = t * x * t⁻¹ →
      (QuotientGroup.mk y : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (l * x * l⁻¹)) ∧
  ((IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6))) →
    ∃ φ : ↥L →* alternatingGroup (Fin 6), Function.Surjective φ ∧
      φ.ker = (oTwoZIn L).subgroupOf L ∧
      ∀ t ∈ T, ∃ σ : Equiv.Perm (Fin 6), ∀ x y : ↥L, (y : G) = t * x * t⁻¹ →
        ((φ y : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
          σ * (φ x : Equiv.Perm (Fin 6)) * σ⁻¹)

@[expose] def IsIrrSection (X W₀ W : Subgroup G) : Prop :=
  W₀ < W ∧ X ≤ Subgroup.normalizer (W₀ : Set G) ∧ X ≤ Subgroup.normalizer (W : Set G) ∧
    ∀ K : Subgroup G, W₀ ≤ K → K ≤ W → X ≤ Subgroup.normalizer (K : Set G) → K = W₀ ∨ K = W

@[expose] def internalIrrPlus (L U : Subgroup G) : Set (Subgroup G) :=
  {I | I ≤ U ∧ ⁅I, L⁆ = I ∧
    IsIrrSection L (I ⊓ Subgroup.centralizer (L : Set G)) I}

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G), pCoreOf 2 X = ⊥ →
    IsTwoRadicalIn X R → SatisfiesPU X R

theorem as_C_1_3 : C_1_3 := by
  intro G _ _ X R hO hR
  refine ⟨hR, fun C hCR hC1 _ hXN => hC1 ?_⟩
  have hp : IsPGroup 2 C := hR.isPGroup.to_le hCR
  have h := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hCR.trans hR.1) hXN hp
  rw [hO] at h
  exact le_bot_iff.mp h

@[expose] def C_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (R : Subgroup G), IsS2 R →
    (IsSylowTwoOf R ⊤ → IsTwoRadicalIn ⊤ R) ∧
    (∃ B : Subgroup G, IsTwoRadicalIn ⊤ B ∧ R ≤ B ∧
      Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (B : Set G)) ∧
    (∀ H K : Subgroup G, H ≤ K → IsTwoRadicalIn H R →
      K ⊓ Subgroup.normalizer (R : Set G) ≤ H → IsTwoRadicalIn K R) ∧
    (∀ M L : Subgroup G, L ≤ M → (L.subgroupOf M).Normal → L = oTwoUpper L →
      IsSylowTwoOf R (centralizerSection M L (pCoreOf 2 L)) →
      IsSylowTwoOf R (conjClosure R M) ∧ IsTwoRadicalIn M R)

theorem as_C_1_2 : C_1_2 := by
  intro G _ _ R hR
  refine ⟨fun hS => ?_, ?_, fun H K hHK hRH hN => ?_, fun M L hLM hLn hL hRS => ?_⟩
  · exact CFSG.Quasithin.isTwoRadicalIn_of_sylow le_top hR.1 hS.2.2 hR.2
  · obtain ⟨B, hB, hRB, hN⟩ := CFSG.Quasithin.exists_isTwoRadicalIn_ge (le_top : R ≤ ⊤) hR.1 hR.2
    refine ⟨B, hB, hRB, ?_⟩
    simpa only [top_inf_eq] using hN
  · exact CFSG.Quasithin.isTwoRadicalIn_of_le_of_normalizer_le hHK hRH hN
  · exact CFSG.Quasithin.c1_2_four hL hLM hLn hRS hR.2

@[expose] def C_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R : Subgroup G), SatisfiesPU X R →
    pCoreOf 2 X ≤ R ∧
    ¬ thompsonJ R ≤ pCoreOf 2 X ∧
    ∀ V : Subgroup G, IsTwoReducedIn X V →
      twoPrimeResidual (X ⊓ Subgroup.centralizer (V : Set G)) = pCoreOf 2 X →
        ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) ∧
          ∃ hV : IsElemAbelian 2 V, IsFFInt X V hV

section BurnsideC1a

private theorem burnsideC1a_le_twoPrimeResidual {G : Type} [Group G] [Finite G] {H T : Subgroup G}
    (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    T ≤ CFSG.Quasithin.twoPrimeResidual H := by
  unfold CFSG.Quasithin.twoPrimeResidual
  refine le_iInf₂ fun N hN => ?_
  exact CFSG.Quasithin.B6.le_of_isPGroup_of_odd_relIndex hTH hT hN.1 hN.2.1 hN.2.2

private theorem burnsideC1a_le_pCoreOf_of_isTwoReducedIn {G : Type} [Group G] {X V : Subgroup G}
    (hV : CFSG.Quasithin.IsTwoReducedIn X V) : V ≤ pCoreOf 2 X := by
  have hp : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using hV.2.2.1.2 v v.2)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1 hp

end BurnsideC1a

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem as_C_1_4 : C_1_4 := by
  intro G _ _ X R hPU
  have hR : IsTwoRadicalIn X R := hPU.1
  have hRX : R ≤ X := hR.1
  have hRp : IsPGroup 2 R := hR.isPGroup
  have hR1 : R ≠ ⊥ := hR.2.1
  have hO : pCoreOf 2 X ≤ R := c2_1_pCore_le hR
  have hnotO : ¬ thompsonJ R ≤ pCoreOf 2 X := by
    intro hJ
    have he : thompsonJ (pCoreOf 2 X) = thompsonJ R := B6.thompsonJ_eq_of_le hJ hO
    have hnorm : X ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
      rw [← he]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
        (normalizer_le_normalizer_thompsonJ _)
    exact hPU.2 (thompsonJ R) (B6.thompsonJ_le R)
      (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hRp hR1)
      (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R) hnorm
  refine ⟨hO, hnotO, fun V hV hcop => ?_⟩
  have hVe : IsElemAbelian 2 V := hV.2.2.1
  have hVR : V ≤ R := (burnsideC1a_le_pCoreOf_of_isTwoReducedIn hV).trans hO
  have hJV : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G) := by
    intro hJC
    have hJX : thompsonJ R ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf ((B6.thompsonJ_le R).trans hRX) hJC
    have hJp : IsPGroup 2 (thompsonJ R) := hRp.to_le (B6.thompsonJ_le R)
    have h2 : thompsonJ R ≤ twoPrimeResidual (X ⊓ Subgroup.centralizer (V : Set G)) :=
      burnsideC1a_le_twoPrimeResidual hJX hJp
    rw [hcop] at h2
    exact hnotO h2
  refine ⟨hJV, hVe, ?_⟩
  obtain ⟨A, hA, hAV⟩ : ∃ A : Subgroup G, IsMaxElemAbelian R A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    apply hJV
    unfold thompsonJ
    refine iSup₂_le fun A hA => ?_
    by_contra hA'
    exact hcon ⟨A, hA, hA'⟩
  exact isFFModule_autOn hVe hVR hV.2.1 (hA.1.trans hRX) hA hAV

@[expose] def C_1_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsShort2 X →
    QuotQuasisimpleOrThree X (blockU X)

section BurnsideC1b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
open scoped commutatorElement in
private theorem burnsideC1b_quot_quasisimple_or_three {G : Type} [Group G] [Finite G] (X :
    Subgroup G)
    (hX : IsShort2 X) : QuotQuasisimpleOrThree X (blockU X) := by
  have hUX : blockU X ≤ X := by
    unfold blockU
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [commutatorElement_def]
    have h1 : g₁ ∈ X := CFSG.QuasithinUnique.C1.blockQ_le X hg₁
    exact X.mul_mem (X.mul_mem (X.mul_mem h1 hg₂) (X.inv_mem h1)) (X.inv_mem hg₂)
  haveI hN : ((blockU X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).2
      (CFSG.QuasithinUnique.C1.le_normalizer_blockU X)
  refine ⟨↥X ⧸ (blockU X).subgroupOf X, inferInstance, QuotientGroup.mk' _,
    QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _, ?_⟩
  set N : Subgroup ↥X := (blockU X).subgroupOf X with hNdef
  set π : ↥X →* ↥X ⧸ N := QuotientGroup.mk' N with hπdef
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker ≤ CFSG.pCore 2 ↥X := by
    rw [hπdef, QuotientGroup.ker_mk', hNdef]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact (CFSG.QuasithinUnique.L246.mem_blockQ_iff x).1
      (CFSG.QuasithinUnique.C1.blockU_le_blockQ hX hx)
  have hRn : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup (↥X ⧸ N), Z = (CFSG.pCore 2 ↥X).map π := ⟨_, rfl⟩
  have hZn : Z.Normal := by
    rw [hZdef]
    exact Subgroup.Normal.map hRn π hsurj
  refine CFSG.QuasithinUnique.L246C127.isQuasisimple_or_card_three_of_central_two (Z := Z)
    ?_ ?_ ?_ ?_
  ·
    intro M hMn hM
    have hcn : (M.comap π).Normal := Subgroup.Normal.comap hMn π
    have hq : IsPGroup 2 (↥X ⧸ M.comap π) := by
      refine hM.of_injective (QuotientGroup.map (M.comap π) M π le_rfl) ?_
      rw [injective_iff_map_eq_one]
      intro q hq1
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at hq1
        exact (QuotientGroup.eq_one_iff x).2 hq1
    have htop := hX.1 (M.comap π) hq
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨k, rfl⟩ := hsurj a
    have : k ∈ M.comap π := htop ▸ Subgroup.mem_top k
    exact this
  ·
    rw [hZdef]
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨k, rfl⟩ := hsurj a
    have hcomm : (⁅(r : G), (k : G)⁆ : G) ∈ blockU X :=
      Subgroup.commutator_mem_commutator ((CFSG.QuasithinUnique.L246.mem_blockQ_iff r).2 hr) k.2
    have hc1 : (⁅r, k⁆ : ↥X) ∈ N := by
      rw [hNdef, Subgroup.mem_subgroupOf]
      have e : (((⁅r, k⁆ : ↥X)) : G) = ⁅(r : G), (k : G)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact hcomm
    have hc2 : π ⁅r, k⁆ = 1 := by
      rw [← MonoidHom.mem_ker, hπdef, QuotientGroup.ker_mk']
      exact hc1
    have hc3 : ⁅π r, π k⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hc2
    exact (commutatorElement_eq_one_iff_mul_comm.1 hc3).symm
  · rw [hZdef]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map π
  ·
    let ψ : ↥X →* (↥X ⧸ N) ⧸ Z := (QuotientGroup.mk' Z).comp π
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective Z).comp hsurj
    have hψker : ψ.ker = CFSG.pCore 2 ↥X := by
      have h1 : ψ.ker = Z.comap π := by
        ext k
        simp [ψ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
      rw [h1, hZdef]
      rw [Subgroup.comap_map_eq, sup_eq_left.2 hker]
    let e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* (↥X ⧸ N) ⧸ Z :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    exact hX.2.2.2.1.imp (fun h => CFSG.LocalCores.isQuasisimple_of_mulEquiv e h)
      (fun h => by rw [← Nat.card_congr e.toEquiv]; exact h)

end BurnsideC1b

theorem as_C_1_8 : C_1_8 := by
  intro G _ _ X hX
  exact burnsideC1b_quot_quasisimple_or_three X hX

@[expose] def C_1_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G),
    ((∃ L : Subgroup G, IsBlock2 X L ∧ IsAltType L 3) → CharTwo (oTwoThreeIn X)) →
    ∀ K L : Subgroup G, IsBlock2 X K → IsBlock2 X L → K ≠ L →
      K ≤ Subgroup.centralizer (L : Set G)

theorem as_C_1_9 : C_1_9 := by
  intro G _ _ X hA3 K L hK hL hKL
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.Quasithin.asc19Statement_holds G X K L hA3 hK hL hKL)

@[expose] def C_1_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X Y : Subgroup G),
    IsBlock2 H X → (X.subgroupOf H).Normal →
    ∀ (W : Type) [AddCommGroup W] (β : ↥(blockU X) →* Multiplicative W) (ρ : ↥X → AddAut W),
      Function.Surjective β → β.ker = (blockZ X).subgroupOf (blockU X) →
      (∀ (x : ↥X) (u v : ↥(blockU X)), (v : G) = x * u * x⁻¹ →
        Multiplicative.toAdd (β v) = ρ x (Multiplicative.toAdd (β u))) →
      Y ≤ H → Y = oTwoUpper Y →
      Y = oUpperPi {p : ℕ | p.Prime ∧
        p ∣ Nat.card {f : W →+ W // (∀ (x : ↥X) (w : W), f (ρ x w) = ρ x (f w)) ∧ f ≠ 0}} Y ⊔
        ⁅Y, Y⁆ →
      Y ≤ centralizerSection H X (pCoreOf 2 X) →
      Y ≤ Subgroup.centralizer (X : Set G)

section BurnsideC1d

private theorem burnsideC1d_card_groupCohomology_one {G V : Type} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V) :
    Nat.card (groupCohomology (Rep.of ρ) 1) =
      2 ^ Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) := by
  classical
  set A := Rep.of ρ
  have hZ : CFSG.Quasithin.JonesParshall.Z1 ρ = groupCohomology.cocycles₁ A := by
    ext f
    rw [groupCohomology.mem_cocycles₁_iff]
    change (∀ g h, f (g * h) = f g + ρ g (f h)) ↔ _
    constructor <;> intro h g k <;> rw [h g k, add_comm]
  have hB : CFSG.Quasithin.JonesParshall.B1 ρ = groupCohomology.coboundaries₁ A := rfl
  have hsurj : Function.Surjective (groupCohomology.H1π A) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  let φ := (groupCohomology.H1π A).hom
  have hker : LinearMap.ker φ =
      (groupCohomology.coboundaries₁ A).comap (groupCohomology.cocycles₁ A).subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    exact groupCohomology.H1π_eq_zero_iff x
  let e1 : CFSG.Quasithin.JonesParshall.H1 ρ ≃ₗ[ZMod 2]
      (↥(groupCohomology.cocycles₁ A) ⧸ LinearMap.ker φ) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ hZ) (by
      rw [hker]
      ext x
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hB]
        exact hy
      · intro hx
        refine ⟨(LinearEquiv.ofEq _ _ hZ).symm x, ?_, (LinearEquiv.ofEq _ _ hZ).apply_symm_apply x⟩
        rw [hB]
        exact hx)
  let e2 := φ.quotKerEquivOfSurjective hsurj
  have hfin : Finite (CFSG.Quasithin.JonesParshall.H1 ρ) :=
    Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
  let := Fintype.ofFinite (CFSG.Quasithin.JonesParshall.H1 ρ)
  rw [← Nat.card_congr (e1.trans e2).toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

private theorem burnsideC1d_quotHas {G : Type} [Group G] {L N : Subgroup G} [(N.subgroupOf
    L).Normal]
    (P : ∀ (Y : Type) [Group Y], Prop) (h : P (↥L ⧸ N.subgroupOf L)) : ChC.QuotHas L N P :=
  ⟨_, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
    QuotientGroup.ker_mk' _, h⟩

private theorem burnsideC1d_schur {W : Type} [AddCommGroup W] [Finite W] [Nontrivial W]
    {ι : Type} (ρ : ι → AddAut W)
    (hirr : ∀ V : AddSubgroup W, (∀ i, ∀ w ∈ V, ρ i w ∈ V) → V = ⊥ ∨ V = ⊤)
    {Γ : Type} [Group Γ] (e : Γ → (W →+ W))
    (he : ∀ (γ : Γ) i w, e γ (ρ i w) = ρ i (e γ w))
    (hmul : ∀ (γ δ : Γ) w, e (γ * δ) w = e γ (e δ w)) (hone : ∀ w, e 1 w = w) :
    (∀ (γ δ : Γ) w, e (γ * δ * γ⁻¹ * δ⁻¹) w = w) ∧
    0 < Nat.card {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0} ∧
    ∀ (γ : Γ) w, e (γ ^ Nat.card {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0}) w = w := by
  classical
  let E : Subring (AddMonoid.End W) :=
    Subring.centralizer (Set.range fun i => ((ρ i : W ≃+ W).toAddMonoidHom : AddMonoid.End W))
  have hmemE : ∀ f : AddMonoid.End W, f ∈ E ↔ ∀ i w, f (ρ i w) = ρ i (f w) := by
    intro f
    rw [Subring.mem_centralizer_iff]
    constructor
    · intro h i w
      exact (congrArg (fun φ : AddMonoid.End W => φ w) (h _ ⟨i, rfl⟩)).symm
    · rintro h _ ⟨i, rfl⟩
      ext w
      exact (h i w).symm
  haveI : Finite E := by
    have : Finite (AddMonoid.End W) :=
      Finite.of_injective (fun f : AddMonoid.End W => (f : W → W)) DFunLike.coe_injective
    infer_instance
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  haveI : Nontrivial E := ⟨⟨1, 0, fun h => hw₀ (by
    have := congrArg (fun x : E => (x : AddMonoid.End W) w₀) h
    simpa using this)⟩⟩
  have hsurj : ∀ f : E, f ≠ 0 → ∀ w : W, ∃ v, (f : AddMonoid.End W) v = w := by
    intro f hf w
    let R : AddSubgroup W := AddMonoidHom.range (f : AddMonoid.End W)
    have hinv : ∀ i, ∀ x ∈ R, ρ i x ∈ R := by
      rintro i _ ⟨v, rfl⟩
      exact ⟨ρ i v, ((hmemE f).1 f.2 i v)⟩
    rcases hirr R hinv with h | h
    · exact absurd (Subtype.ext (AddMonoidHom.ext fun v => by
        have : (f : AddMonoid.End W) v ∈ R := ⟨v, rfl⟩
        rw [h] at this
        exact (AddSubgroup.mem_bot.mp this))) hf
    · have : w ∈ R := by rw [h]; exact AddSubgroup.mem_top _
      exact this
  haveI : NoZeroDivisors E := ⟨fun {a b} hab => by
    by_contra hcon
    obtain ⟨ha, hb⟩ := not_or.mp hcon
    refine ha (Subtype.ext (AddMonoidHom.ext fun w => ?_))
    obtain ⟨v, hv⟩ := hsurj b hb w
    have h2 := congrArg (fun x : E => (x : AddMonoid.End W) v) hab
    have h3 : (a : AddMonoid.End W) w = 0 := by
      rw [← hv]
      exact h2
    exact h3⟩
  haveI : IsDomain E := NoZeroDivisors.to_isDomain E
  have hfield : IsField E := Finite.isDomain_to_isField E
  have hcomm : ∀ a b : E, a * b = b * a := hfield.mul_comm
  let ε : Γ → E := fun γ => ⟨e γ, (hmemE (e γ)).2 (he γ)⟩
  have hεmul : ∀ γ δ : Γ, ε (γ * δ) = ε γ * ε δ := fun γ δ =>
    Subtype.ext (AddMonoidHom.ext fun w => hmul γ δ w)
  have hε1 : ε 1 = 1 := Subtype.ext (AddMonoidHom.ext fun w => hone w)
  let ε' : Γ →* E := { toFun := ε, map_one' := hε1, map_mul' := hεmul }
  have hεinv : ∀ γ : Γ, ε γ * ε γ⁻¹ = 1 := fun γ => by
    rw [← hεmul, mul_inv_cancel]
    exact hε1
  refine ⟨fun γ δ w => ?_, ?_, ?_⟩
  · have h1 : ε (γ * δ * γ⁻¹ * δ⁻¹) = 1 := by
      have : ε (γ * δ * γ⁻¹ * δ⁻¹) = ε γ * ε δ * ε γ⁻¹ * ε δ⁻¹ := by
        rw [hεmul, hεmul, hεmul]
      rw [this, mul_assoc (ε γ), hcomm (ε δ) (ε γ⁻¹), ← mul_assoc (ε γ), mul_assoc (ε γ * ε γ⁻¹),
        hεinv, hεinv, one_mul]
    have := congrArg (fun x : E => (x : AddMonoid.End W) w) h1
    exact this
  all_goals
    let eS : {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0} ≃ {x : E // x ≠ 0} :=
      { toFun := fun f => ⟨⟨f.1, (hmemE f.1).2 f.2.1⟩, fun h => f.2.2 (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨x.1.1, (hmemE x.1.1).1 x.1.2, fun h => x.2 (Subtype.ext h)⟩
        left_inv := fun f => rfl
        right_inv := fun x => rfl }
    let uE : Eˣ ≃ {x : E // x ≠ 0} :=
      { toFun := fun u => ⟨u.1, u.ne_zero⟩
        invFun := fun x => Units.mk x.1 (hfield.mul_inv_cancel x.2).choose
          (hfield.mul_inv_cancel x.2).choose_spec
          (by rw [hcomm]; exact (hfield.mul_inv_cancel x.2).choose_spec)
        left_inv := fun u => Units.ext rfl
        right_inv := fun x => Subtype.ext rfl }
    have hcard : Nat.card {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0} = Nat.card Eˣ :=
      (Nat.card_congr eS).trans (Nat.card_congr uE).symm
  · have : Nonempty {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0} :=
      ⟨eS.symm ⟨1, one_ne_zero⟩⟩
    have : Finite {f : W →+ W // (∀ i w, f (ρ i w) = ρ i (f w)) ∧ f ≠ 0} :=
      Finite.of_equiv _ eS.symm
    exact Nat.card_pos
  · intro γ w
    have hu : (ε γ) ^ Nat.card Eˣ = 1 := by
      have := pow_card_eq_one' (x := (Units.mk (ε γ) (ε γ⁻¹) (hεinv γ)
        (by rw [hcomm]; exact hεinv γ)))
      exact congrArg Units.val this
    rw [hcard]
    have h1 : ε (γ ^ Nat.card Eˣ) = 1 := by
      have : ε (γ ^ Nat.card Eˣ) = (ε γ) ^ Nat.card Eˣ := map_pow ε' γ _
      rw [this, hu]
    exact congrArg (fun x : E => (x : AddMonoid.End W) w) h1

open CFSG.QuasithinUnique in
private theorem burnsideC1d_nontrivial {G : Type} [Group G] {X : Subgroup G}
    (hX : IsShort2 X) {W : Type} [AddCommGroup W] (β : ↥(blockU X) →* Multiplicative W)
    (hβk : β.ker = (blockZ X).subgroupOf (blockU X)) : Nontrivial W := by
  obtain ⟨u, huU, huZ⟩ := SetLike.exists_of_lt hX.2.2.2.2.1
  refine ⟨⟨Multiplicative.toAdd (β ⟨u, huU⟩), 0, fun h => huZ ?_⟩⟩
  have h1 : β ⟨u, huU⟩ = 1 := by
    have := congrArg Multiplicative.ofAdd h
    simpa using this
  have h2 : (⟨u, huU⟩ : ↥(blockU X)) ∈ β.ker := h1
  rw [hβk] at h2
  exact h2

open CFSG.QuasithinUnique in
private theorem burnsideC1d_irr {G : Type} [Group G] {X : Subgroup G} (hX : IsShort2 X)
    {W : Type} [AddCommGroup W] (β : ↥(blockU X) →* Multiplicative W) (ρ : ↥X → AddAut W)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ X).subgroupOf (blockU X))
    (hβa : ∀ (x : ↥X) (u v : ↥(blockU X)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) = ρ x (Multiplicative.toAdd (β u)))
    (V : AddSubgroup W) (hV : ∀ (x : ↥X), ∀ w ∈ V, ρ x w ∈ V) : V = ⊥ ∨ V = ⊤ := by
  let V' : Subgroup (Multiplicative W) :=
    { carrier := {m | Multiplicative.toAdd m ∈ V}
      mul_mem' := fun {a b} ha hb => by
        have ha' : Multiplicative.toAdd a ∈ V := ha
        have hb' : Multiplicative.toAdd b ∈ V := hb
        show Multiplicative.toAdd (a * b) ∈ V
        rw [toAdd_mul]
        exact V.add_mem ha' hb'
      one_mem' := by
        show Multiplicative.toAdd (1 : Multiplicative W) ∈ V
        rw [toAdd_one]
        exact V.zero_mem
      inv_mem' := fun {a} ha => by
        have ha' : Multiplicative.toAdd a ∈ V := ha
        show Multiplicative.toAdd a⁻¹ ∈ V
        rw [toAdd_inv]
        exact V.neg_mem ha' }
  let W' : Subgroup G := (V'.comap β).map (blockU X).subtype
  have hmem : ∀ g : G, g ∈ W' ↔
      ∃ u : ↥(blockU X), Multiplicative.toAdd (β u) ∈ V ∧ (u : G) = g := by
    intro g
    simp only [W', Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
    exact Iff.rfl
  have hZU : blockZ X ≤ blockU X := inf_le_left
  have hZW : blockZ X ≤ W' := fun z hz => by
    refine (hmem z).2 ⟨⟨z, hZU hz⟩, ?_, rfl⟩
    have h1 : (⟨z, hZU hz⟩ : ↥(blockU X)) ∈ β.ker := by
      rw [hβk]
      exact hz
    have h2 : β ⟨z, hZU hz⟩ = 1 := h1
    rw [h2]
    simpa using V.zero_mem
  have hWU : W' ≤ blockU X := fun g hg => by
    obtain ⟨u, -, rfl⟩ := (hmem g).1 hg
    exact u.2
  have hfwd : ∀ x ∈ X, ∀ g ∈ W', x * g * x⁻¹ ∈ W' := by
    intro x hx g hg
    obtain ⟨u, hu, rfl⟩ := (hmem g).1 hg
    have hxU : x * (u : G) * x⁻¹ ∈ blockU X :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.Quasithin.ASInputs.C113.L_le_normalizer_blockU X hx) u).mp u.2
    refine (hmem _).2 ⟨⟨_, hxU⟩, ?_, rfl⟩
    rw [hβa ⟨x, hx⟩ u ⟨_, hxU⟩ rfl]
    exact hV ⟨x, hx⟩ _ hu
  have hXN : X ≤ Subgroup.normalizer (W' : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hfwd x hx g hg, fun hg => ?_⟩
    have := hfwd x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  rcases hX.2.2.2.2.2 W' hZW hWU hXN with h | h
  · left
    refine (AddSubgroup.eq_bot_iff_forall V).2 fun w hw => ?_
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have huW : (u : G) ∈ W' := (hmem _).2 ⟨u, by rw [hu]; exact hw, rfl⟩
    rw [h] at huW
    have h1 : u ∈ β.ker := by
      rw [hβk]
      exact huW
    have h2 : β u = 1 := h1
    rw [h2] at hu
    exact (congrArg Multiplicative.toAdd hu).symm
  · right
    refine (AddSubgroup.eq_top_iff' V).2 fun w => ?_
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have huW : (u : G) ∈ W' := by
      rw [h]
      exact u.2
    obtain ⟨u', hu', hu'u⟩ := (hmem _).1 huW
    have : u' = u := Subtype.ext hu'u
    rw [this, hu] at hu'
    simpa using hu'

open CFSG.QuasithinUnique in
private theorem burnsideC1d_exists_act {G : Type} [Group G] {X : Subgroup G}
    {W : Type} [AddCommGroup W] (β : ↥(blockU X) →* Multiplicative W)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ X).subgroupOf (blockU X))
    {y : G} (hyU : ∀ u ∈ blockU X, y * u * y⁻¹ ∈ blockU X)
    (hyZ : ∀ z ∈ blockZ X, y * z * y⁻¹ ∈ blockZ X) :
    ∃ f : W →+ W, ∀ (u : ↥(blockU X)) (hu : y * (u : G) * y⁻¹ ∈ blockU X),
      f (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β ⟨y * u * y⁻¹, hu⟩) := by
  let c : ↥(blockU X) →* ↥(blockU X) :=
    { toFun := fun u => ⟨y * u * y⁻¹, hyU u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hker : β.ker ≤ (β.comp c).ker := by
    intro u hu
    rw [hβk] at hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have : c u ∈ β.ker := by
      rw [hβk]
      exact hyZ u hu
    exact this
  let ψ : Multiplicative W →* Multiplicative W := β.liftOfSurjective hβs ⟨β.comp c, hker⟩
  have hψ : ∀ u : ↥(blockU X), ψ (β u) = β (c u) := fun u =>
    β.liftOfRightInverse_comp_apply _ _ ⟨β.comp c, hker⟩ u
  refine ⟨AddMonoidHom.mk' (fun w => Multiplicative.toAdd (ψ (Multiplicative.ofAdd w)))
    (fun a b => ?_), fun u hu => ?_⟩
  · simp [ofAdd_add, map_mul]
  · show Multiplicative.toAdd (ψ (β u)) = _
    rw [hψ]
    rfl

open CFSG.QuasithinUnique CFSG.Quasithin in
private theorem burnsideC1d_acts_trivially {G : Type} [Group G] [Finite G] {H X Y : Subgroup G}
    (hX : IsShort2 X) (hXH : H ≤ Subgroup.normalizer (X : Set G))
    {W : Type} [AddCommGroup W] (β : ↥(blockU X) →* Multiplicative W) (ρ : ↥X → AddAut W)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ X).subgroupOf (blockU X))
    (hβa : ∀ (x : ↥X) (u v : ↥(blockU X)), (v : G) = x * u * x⁻¹ →
      Multiplicative.toAdd (β v) = ρ x (Multiplicative.toAdd (β u)))
    (hYH : Y ≤ H) (hYsec : ∀ y ∈ Y, ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 X)
    (hY : ∀ K : Subgroup G, K ≤ Y → Y ≤ Subgroup.normalizer (K : Set G) →
      (∀ y ∈ Y, ∃ m : ℕ, 0 < m ∧ (∀ p ∈ m.primeFactors, p ∈ {p : ℕ | p.Prime ∧
        p ∣ Nat.card {f : W →+ W // (∀ (x : ↥X) (w : W), f (ρ x w) = ρ x (f w)) ∧ f ≠ 0}}) ∧
        y ^ m ∈ K) → ⁅Y, Y⁆ ≤ K → Y ≤ K) :
    ∀ y ∈ Y, ∀ u ∈ blockU X, y * u * y⁻¹ * u⁻¹ ∈ blockZ X := by
  classical
  have : Finite W := by
    have : Finite (Multiplicative W) := Finite.of_surjective β hβs
    exact Finite.of_equiv _ Multiplicative.toAdd
  have : Nontrivial W := burnsideC1d_nontrivial hX β hβk
  have hirr := burnsideC1d_irr hX β ρ hβs hβk hβa
  have hyN : ∀ y ∈ Y, y ∈ Subgroup.normalizer (X : Set G) := fun y hy => hXH (hYH hy)
  have hyQ : ∀ y ∈ Y, y ∈ Subgroup.normalizer ((blockQ X : Subgroup G) : Set G) := fun y hy =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hyN y hy)
  have hyUN : ∀ y ∈ Y, y ∈ Subgroup.normalizer ((blockU X : Subgroup G) : Set G) := fun y hy =>
    CFSG.Quasithin.ASInputs.C113.mem_normalizer_commutator (hyQ y hy) (hyN y hy)
  have hyZN : ∀ y ∈ Y, y ∈ Subgroup.normalizer ((blockZ X : Subgroup G) : Set G) := fun y hy =>
    CFSG.Quasithin.ASInputs.C113.mem_normalizer_inf' (hyUN y hy)
      (CFSG.Quasithin.ASInputs.C113.mem_normalizer_centralizer' (hyN y hy))
  have hyU : ∀ y ∈ Y, ∀ u ∈ blockU X, y * u * y⁻¹ ∈ blockU X := fun y hy u hu =>
    (Subgroup.mem_normalizer_iff.mp (hyUN y hy) u).mp hu
  have hyZ : ∀ y ∈ Y, ∀ z ∈ blockZ X, y * z * y⁻¹ ∈ blockZ X := fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp (hyZN y hy) z).mp hz
  have hUQ : ∀ u ∈ blockU X, ∀ q ∈ pCoreOf 2 X, q * u = u * q := fun u hu q hq =>
    Subgroup.mem_centralizer_iff.mp (hX.2.2.1.1 hu).2 q hq
  have hconjU : ∀ q ∈ pCoreOf 2 X, ∀ u ∈ blockU X, q * u * q⁻¹ = u := fun q hq u hu => by
    rw [hUQ u hu q hq]
    group
  have hex : ∀ y : ↥Y, ∃ f : W →+ W,
      ∀ (u : ↥(blockU X)) (hu : (y : G) * (u : G) * (y : G)⁻¹ ∈ blockU X),
        f (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β ⟨(y : G) * u * (y : G)⁻¹, hu⟩) :=
    fun y => burnsideC1d_exists_act β hβs hβk (hyU y y.2) (hyZ y y.2)
  choose e he using hex
  have hw : ∀ w : W, ∃ u : ↥(blockU X), Multiplicative.toAdd (β u) = w := fun w => by
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    exact ⟨u, by rw [hu]; rfl⟩
  have hmul : ∀ (γ δ : ↥Y) w, e (γ * δ) w = e γ (e δ w) := by
    intro γ δ w
    obtain ⟨u, rfl⟩ := hw w
    have hδu := hyU δ δ.2 u u.2
    have hγδu := hyU γ γ.2 _ hδu
    rw [he δ u hδu, he γ ⟨_, hδu⟩ hγδu, he (γ * δ) u (hyU _ (γ * δ).2 u u.2)]
    congr 2
    apply Subtype.ext
    simp [mul_assoc]
  have hone : ∀ w, e 1 w = w := by
    intro w
    obtain ⟨u, rfl⟩ := hw w
    rw [he 1 u (hyU _ (1 : ↥Y).2 u u.2)]
    congr 2
    apply Subtype.ext
    simp
  have heq : ∀ (γ : ↥Y) (x : ↥X) w, e γ (ρ x w) = ρ x (e γ w) := by
    intro γ x w
    obtain ⟨u, rfl⟩ := hw w
    have hxN := CFSG.Quasithin.ASInputs.C113.L_le_normalizer_blockU X x.2
    have hxu : (x : G) * u * (x : G)⁻¹ ∈ blockU X := (Subgroup.mem_normalizer_iff.mp hxN u).mp u.2
    have hγu := hyU γ γ.2 u u.2
    have hγxu := hyU γ γ.2 _ hxu
    have hxγu : (x : G) * ((γ : G) * u * (γ : G)⁻¹) * (x : G)⁻¹ ∈ blockU X :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp hγu
    have h1 : ρ x (Multiplicative.toAdd (β u)) =
        Multiplicative.toAdd (β ⟨(x : G) * (u : G) * (x : G)⁻¹, hxu⟩) :=
      (hβa x u ⟨_, hxu⟩ rfl).symm
    have h2 : ρ x (Multiplicative.toAdd (β ⟨(γ : G) * (u : G) * (γ : G)⁻¹, hγu⟩)) =
        Multiplicative.toAdd (β ⟨(x : G) * ((γ : G) * (u : G) * (γ : G)⁻¹) * (x : G)⁻¹, hxγu⟩) :=
      (hβa x ⟨_, hγu⟩ ⟨_, hxγu⟩ rfl).symm
    rw [h1, he γ ⟨_, hxu⟩ hγxu, he γ u hγu, h2]
    congr 2
    apply Subtype.ext
    have hq := hYsec γ γ.2 x x.2
    have hc := hconjU _ hq _ hγxu
    have key : ∀ a b c : G, a * (b * c * b⁻¹) * a⁻¹ =
        (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹) * b⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
      intro a b c
      group
    show (γ : G) * ((x : G) * (u : G) * (x : G)⁻¹) * (γ : G)⁻¹ =
      (x : G) * ((γ : G) * (u : G) * (γ : G)⁻¹) * (x : G)⁻¹
    exact hc.symm.trans (key (x : G) (γ : G) (u : G)).symm
  obtain ⟨hcommE, hpos, hpowE⟩ := burnsideC1d_schur ρ hirr e heq hmul hone
  let K : Subgroup ↥Y :=
    { carrier := {γ | ∀ w, e γ w = w}
      mul_mem' := fun {a b} ha hb w => by rw [hmul, hb, ha]
      one_mem' := hone
      inv_mem' := fun {a} ha w => by
        have := hmul a a⁻¹ w
        rw [mul_inv_cancel, hone, ha] at this
        exact this.symm }
  have hKconj : ∀ (a κ : ↥Y), κ ∈ K → a * κ * a⁻¹ ∈ K := by
    intro a κ hκ w
    have hκ' : ∀ w, e κ w = w := hκ
    show e (a * κ * a⁻¹) w = w
    rw [hmul, hmul, hκ', ← hmul, mul_inv_cancel, hone]
  have hfwd : ∀ y ∈ Y, ∀ k ∈ K.map Y.subtype, y * k * y⁻¹ ∈ K.map Y.subtype := by
    intro y hy k hk
    obtain ⟨κ, hκ, rfl⟩ := hk
    exact ⟨⟨y, hy⟩ * κ * ⟨y, hy⟩⁻¹, hKconj _ _ hκ, by simp⟩
  have hnorm : Y ≤ Subgroup.normalizer ((K.map Y.subtype : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hfwd y hy k, fun hk => ?_⟩
    have := hfwd y⁻¹ (Y.inv_mem hy) _ hk
    simpa [mul_assoc] using this
  have hpowK : ∀ y ∈ Y, ∃ m : ℕ, 0 < m ∧ (∀ p ∈ m.primeFactors, p ∈ {p : ℕ | p.Prime ∧
        p ∣ Nat.card {f : W →+ W // (∀ (x : ↥X) (w : W), f (ρ x w) = ρ x (f w)) ∧ f ≠ 0}}) ∧
        y ^ m ∈ K.map Y.subtype := by
    intro y hy
    set m := Nat.card {f : W →+ W // (∀ (x : ↥X) (w : W), f (ρ x w) = ρ x (f w)) ∧ f ≠ 0}
    have hmK : (⟨y, hy⟩ : ↥Y) ^ m ∈ K := hpowE ⟨y, hy⟩
    refine ⟨m, hpos, fun p hp => ?_, ⟨⟨y, hy⟩ ^ m, hmK, by simp⟩⟩
    obtain ⟨hp1, hp2, -⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hp1, hp2⟩
  have hcommK : ⁅Y, Y⁆ ≤ K.map Y.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact ⟨⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹, fun w => hcommE _ _ w, by simp⟩
  have hYK := hY _ (Subgroup.map_subtype_le K) hnorm hpowK hcommK
  intro y hy u hu
  obtain ⟨κ, hκ, hκy⟩ := hYK hy
  have hκ' : κ = ⟨y, hy⟩ := Subtype.ext hκy
  have h1 : e κ (Multiplicative.toAdd (β ⟨u, hu⟩)) = Multiplicative.toAdd (β ⟨u, hu⟩) := hκ _
  rw [hκ', he _ ⟨u, hu⟩ (hyU y hy u hu)] at h1
  have h2 : β ⟨y * u * y⁻¹, hyU y hy u hu⟩ = β ⟨u, hu⟩ := Multiplicative.toAdd.injective h1
  have h3 : (⟨y * u * y⁻¹, hyU y hy u hu⟩ * (⟨u, hu⟩ : ↥(blockU X))⁻¹ : ↥(blockU X)) ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  rw [hβk] at h3
  exact h3

private theorem burnsideC1d_conj_comm {G : Type} [Group G] {y u x d e : G}
    (hyu : y * u * y⁻¹ = d * u) (hyx : y * x * y⁻¹ = e * x)
    (hdu : Commute d u) (hde : Commute d e) (hdx : Commute d x)
    (hue : Commute u e) (hce : Commute (u * x * u⁻¹ * x⁻¹) e) :
    y * (u * x * u⁻¹ * x⁻¹) * y⁻¹ = u * x * u⁻¹ * x⁻¹ := by
  have hT : Commute d (u * e * x * u⁻¹) :=
    ((hdu.mul_right hde).mul_right hdx).mul_right hdu.inv_right
  have hT' : d * (u * e * x * u⁻¹) * d⁻¹ = u * e * x * u⁻¹ := mul_inv_eq_iff_eq_mul.mpr hT.eq
  have hc' : e * (u * x * u⁻¹ * x⁻¹) * e⁻¹ = u * x * u⁻¹ * x⁻¹ :=
    mul_inv_eq_iff_eq_mul.mpr hce.symm.eq
  calc y * (u * x * u⁻¹ * x⁻¹) * y⁻¹
      = (y * u * y⁻¹) * (y * x * y⁻¹) * (y * u * y⁻¹)⁻¹ * (y * x * y⁻¹)⁻¹ := by group
    _ = d * (u * e * x * u⁻¹) * d⁻¹ * x⁻¹ * e⁻¹ := by rw [hyu, hyx]; group
    _ = (u * e * x * u⁻¹) * x⁻¹ * e⁻¹ := by rw [hT']
    _ = e * (u * x * u⁻¹ * x⁻¹) * e⁻¹ := by rw [hue.eq]; group
    _ = u * x * u⁻¹ * x⁻¹ := hc'

open CFSG.QuasithinUnique CFSG.Quasithin in
private theorem burnsideC1d_centralizes_U {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsShort2 X) (y : G)
    (hsec : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 X)
    (hact : ∀ u ∈ blockU X, y * u * y⁻¹ * u⁻¹ ∈ blockZ X) :
    ∀ u ∈ blockU X, y * u * y⁻¹ = u := by
  have hUQ : ∀ u ∈ blockU X, ∀ q ∈ pCoreOf 2 X, q * u = u * q := fun u hu q hq =>
    Subgroup.mem_centralizer_iff.mp (hX.2.2.1.1 hu).2 q hq
  have hUC : blockU X ≤ Subgroup.centralizer ({y} : Set G) := by
    refine (CFSG.Quasithin.ASInputs.C113.blockU_eq_commutator hX).le.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have hcU := CFSG.Quasithin.ASInputs.C113.commutator_blockU_le X
      (Subgroup.commutator_mem_commutator hu hx)
    rw [commutatorElement_def] at hcU ⊢
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdZ := hact u hu
    have hdU : y * u * y⁻¹ * u⁻¹ ∈ blockU X := hdZ.1
    have heQ : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 X := by
      have := (pCoreOf 2 X).inv_mem (hsec x hx)
      simpa [mul_assoc] using this
    have hcomm : ∀ a b, a ∈ blockU X → b ∈ blockU X → Commute a b := fun a b ha hb =>
      (CFSG.Quasithin.ASInputs.C113.blockU_comm hX ha hb : a * b = b * a)
    have hmain := burnsideC1d_conj_comm (y := y) (u := u) (x := x)
      (d := y * u * y⁻¹ * u⁻¹) (e := y * x * y⁻¹ * x⁻¹) (by group) (by group)
      (hcomm _ _ hdU hu)
      (hUQ _ hdU _ heQ).symm
      (Subgroup.mem_centralizer_iff.mp hdZ.2 x hx).symm
      (hUQ u hu _ heQ).symm (hUQ _ hcU _ heQ).symm
    exact (mul_inv_eq_iff_eq_mul.mp hmain).symm
  intro u hu
  have := Subgroup.mem_centralizer_singleton_iff.mp (hUC hu)
  exact mul_inv_eq_iff_eq_mul.mpr this.symm

open CFSG.QuasithinUnique in
private theorem burnsideC1d_odd_centralizes {G : Type} [Group G] {X : Subgroup G}
    (hX : IsShort2 X) {y : G} (hodd : Odd (orderOf y))
    (hU : ∀ u ∈ blockU X, y * u * y⁻¹ = u)
    (hcomm : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ blockU X) :
    ∀ x ∈ X, y * x * y⁻¹ = x := by
  intro x hx
  have hdU := hcomm x hx
  have hd2 : (y * x * y⁻¹ * x⁻¹) * (y * x * y⁻¹ * x⁻¹) = 1 :=
    CFSG.Quasithin.ASInputs.C113.blockU_sq hX hdU
  have hyd : y * (y * x * y⁻¹ * x⁻¹) * y⁻¹ = y * x * y⁻¹ * x⁻¹ := hU _ hdU
  generalize hd : y * x * y⁻¹ * x⁻¹ = d at hd2 hyd
  have hyx : y * x * y⁻¹ = d * x := by rw [← hd]; group
  have hpow : ∀ k : ℕ, y ^ k * x * (y ^ k)⁻¹ = d ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : y * d ^ k * y⁻¹ = d ^ k := by rw [← conj_pow, hyd]
      calc y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (d ^ k * x) * y⁻¹ := by rw [ih]
        _ = (y * d ^ k * y⁻¹) * (y * x * y⁻¹) := by group
        _ = d ^ k * (d * x) := by rw [h1, hyx]
        _ = d ^ (k + 1) * x := by group
  obtain ⟨j, hj⟩ := hodd
  have h1 := hpow (orderOf y)
  rw [pow_orderOf_eq_one, hj] at h1
  have h2 : d ^ (2 * j + 1) = 1 := by
    have : x = d ^ (2 * j + 1) * x := by simpa using h1
    exact right_eq_mul.mp this
  have h3 : d = 1 := by
    have : d ^ (2 * j + 1) = d := by
      rw [pow_succ, pow_mul, sq, hd2, one_pow, one_mul]
    rw [← this]
    exact h2
  rw [hyx, h3, one_mul]

open CFSG.QuasithinUnique CFSG.Quasithin in
private theorem burnsideC1d_comm_mem_U {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hX : IsShort2 X) (y : G)
    (hsec : ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 X) :
    ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ blockU X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 X
  have hεQ : ∀ a : ↥X, y * a * y⁻¹ * (a : G)⁻¹ ∈ Q := fun a => by
    have := Q.inv_mem (hsec a a.2)
    simpa [mul_assoc] using this
  have hUQ : ∀ u ∈ blockU X, ∀ q ∈ Q, q * u * q⁻¹ = u := fun u hu q hq => by
    rw [Subgroup.mem_centralizer_iff.mp (hX.2.2.1.1 hu).2 q hq]
    group
  haveI hN : ((blockU X).subgroupOf Q).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hUQ _ hn _ g.2]
    exact hn⟩
  let ε : ↥X → ↥Q := fun a => ⟨y * a * y⁻¹ * (a : G)⁻¹, hεQ a⟩
  have key : ∀ a b y : G, (y * (a * b) * y⁻¹ * (a * b)⁻¹)⁻¹ *
      ((y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹)) =
      ((y * b * y⁻¹ * b⁻¹)⁻¹ * a * ((y * b * y⁻¹ * b⁻¹)⁻¹)⁻¹ * a⁻¹)⁻¹ := by
    intro a b y
    group
  let φ : ↥X →* ↥Q ⧸ (blockU X).subgroupOf Q :=
    MonoidHom.mk' (fun a => QuotientGroup.mk (ε a)) (fun a b => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      show ((y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹)⁻¹ *
        ((y * a * y⁻¹ * (a : G)⁻¹) * (y * b * y⁻¹ * (b : G)⁻¹))) ∈ blockU X
      rw [key]
      exact Subgroup.inv_mem _ (CFSG.Quasithin.ASInputs.C113.commutator_mem_blockU
        (Q.inv_mem (hεQ b)) a.2))
  have hker : φ.ker = ⊤ := by
    apply hX.1 φ.ker
    have hQp : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hQU : IsPGroup 2 (↥Q ⧸ (blockU X).subgroupOf Q) := hQp.to_quotient _
    exact hQU.of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    have : (⟨x, hx⟩ : ↥X) ∈ φ.ker := by
      rw [hker]
      exact Subgroup.mem_top _
    exact this
  have h2 : (QuotientGroup.mk (ε ⟨x, hx⟩) : ↥Q ⧸ (blockU X).subgroupOf Q) = 1 := h1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  exact h2

end BurnsideC1d

theorem as_C_1_10 : C_1_10 := by
  intro G _ _ H X Y hXb hXn W _ β ρ hβs hβk hβa hYH hY2 hYpi hYsec
  have hX : CFSG.QuasithinUnique.IsShort2 X := hXb.1
  have hXH : H ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXb.2.1).mp hXn
  have hsec : ∀ y ∈ Y, ∀ x ∈ X, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 X := fun y hy x hx =>
    (CFSG.Quasithin.mem_centralizerSection.mp (hYsec hy)).2.2.2 x hx
  have hY : ∀ K : Subgroup G, K ≤ Y → Y ≤ Subgroup.normalizer (K : Set G) →
      (∀ y ∈ Y, ∃ m : ℕ, 0 < m ∧ (∀ p ∈ m.primeFactors, p ∈ {p : ℕ | p.Prime ∧
        p ∣ Nat.card {f : W →+ W // (∀ (x : ↥X) (w : W), f (ρ x w) = ρ x (f w)) ∧ f ≠ 0}}) ∧
        y ^ m ∈ K) → ⁅Y, Y⁆ ≤ K → Y ≤ K := by
    intro K hKY hKn hpow hcomm
    exact hYpi.le.trans (sup_le (iInf₂_le K ⟨hKY, hKn, hpow⟩) hcomm)
  have hact := burnsideC1d_acts_trivially hX hXH β ρ hβs hβk hβa hYH hsec hY
  have hcentU : ∀ y ∈ Y, ∀ u ∈ CFSG.QuasithinUnique.blockU X, y * u * y⁻¹ = u := fun y hy =>
    burnsideC1d_centralizes_U hX y (hsec y hy) (hact y hy)
  have hcomm : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ CFSG.QuasithinUnique.blockU X := fun y hy =>
    burnsideC1d_comm_mem_U hX y (hsec y hy)
  refine hY2.le.trans ((Subgroup.closure_le _).mpr ?_)
  rintro y ⟨hy, hodd⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro x hx
  have h := burnsideC1d_odd_centralizes hX hodd (hcentU y hy) (hcomm y hy) x hx
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

@[expose] def C_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K S : Subgroup G),
    IsCentralProductOfBlocks H K → IsSylowTwoOf S H → (H : Set G) = (K : Set G) * (S : Set G) →
    H ⊓ Subgroup.centralizer ((⁅pCoreOf 2 K, K⁆ : Subgroup G) : Set G) = pCoreOf 2 H

open scoped Pointwise in
theorem as_C_1_11 : C_1_11 := by
  intro G _ _ H K S hKc hS hprod
  obtain ⟨B, hB, hcomm, hKB⟩ := hKc
  have hKH : K ≤ H := by
    intro k hk
    have hmem : k ∈ (H : Set G) := by
      rw [hprod]
      exact Set.mem_mul.2 ⟨k, hk, 1, S.one_mem, mul_one k⟩
    exact hmem
  have hK : K = ⨆ i : ↥B, (i : Subgroup G) := by
    rw [hKB]
    exact iSup_subtype'
  have hcov : ∀ h ∈ H, ∃ k ∈ K, ∃ s ∈ S, h = k * s := by
    intro h hh
    have hmem : h ∈ (K : Set G) * (S : Set G) := by
      rw [← hprod]
      exact hh
    obtain ⟨k, hk, s, hs, hks⟩ := Set.mem_mul.1 hmem
    exact ⟨k, hk, s, hs, hks.symm⟩
  have hdisj : ∀ i j : ↥B, i ≠ j → ⁅(i : Subgroup G), (j : Subgroup G)⁆ = ⊥ := by
    intro i j hij
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hcomm i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h))
  exact CFSG.Quasithin.asc111Statement_holds G H K S ↥B (fun i => (i : Subgroup G))
    inferInstance (fun i => hB i.1 i.2) hdisj hK hKH hS hcov

@[expose] def C_1_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G),
    IsShort2 L → T ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf T (L ⊔ T) →
    ((frattini ↥(pCoreOf 2 (L ⊔ T))).map (pCoreOf 2 (L ⊔ T)).subtype ≤
        T ⊓ Subgroup.centralizer (L : Set G)) ∧
    ((∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) (↥L ⧸ CFSG.pCore 2 ↥L) W)
        (β : ↥(blockU L) →* Multiplicative W), Function.Surjective β →
        β.ker = (blockZ L).subgroupOf (blockU L) →
        (∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
          Multiplicative.toAdd (β v) = ρ (QuotientGroup.mk ℓ) (Multiplicative.toAdd (β u))) →
        (blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G))).relIndex (pCoreOf 2 (L ⊔ T)) ≤
          Nat.card (groupCohomology (Rep.of ρ) 1)) ∧
      (CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
        ∃ (A : Type) (_ : Group A) (π : ↥(pCoreOf 2 L) →* A), Function.Surjective π ∧
          π.ker = (blockU L).subgroupOf (pCoreOf 2 L) ∧
          ∃ φ : quasithinHopfMultiplier (↥L ⧸ CFSG.pCore 2 ↥L) →* A, Function.Surjective φ) ∧
      (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 → pCoreOf 2 L = blockU L)) ∧
    (∀ m : ℕ, (m = 3 ∨ m = 5) → IsAltType L m →
      (pCoreOf 2 (L ⊔ T) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ ∧
        blockU L ≤ Subgroup.centralizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G)) ∧
      blockZ L = ⊥ ∧
      (m = 3 → Nonempty (↥L ≃* alternatingGroup (Fin 4))) ∧
      (m = 5 → (QuotHas L (blockU L) (fun Y _ => IsAlt 5 Y) ∨
        (QuotHas L (blockU L) (fun Y _ => IsSL2 5 Y) ∧ Nat.card (Subgroup.center ↥L) = 2))) ∧
      pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G)) ∧
    (IsAltBlockType L 6 → pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (pCoreOf 2 L : Set G))

theorem as_C_1_13 : C_1_13 := by
  intro G _ _ L T hL hTN hT
  have ha := CFSG.Quasithin.H13.VolI.frattini_pCoreOf_le hT hTN hL
  have hb := CFSG.Quasithin.ASInputs.as_C_1_13_b_holds G L T hT hTN hL
  have hc := CFSG.Quasithin.H13.VolI.asC113c_holds G L T hT hTN hL
  have hd := fun h6 => CFSG.Quasithin.H13.VolI.pCoreOf_le_centralizer_of_alt6 hL hT hTN h6
  refine ⟨ha, ⟨?_, ?_, hb.2.2⟩, ?_, hd⟩
  · intro W _ _ ρ β hβs hβk hβa
    haveI : Finite W := by
      have : Finite (Multiplicative W) := Finite.of_surjective β hβs
      exact Finite.of_equiv _ Multiplicative.toAdd
    rw [burnsideC1d_card_groupCohomology_one ρ]
    exact hb.1 W ρ β hβs hβk hβa
  · intro hq
    obtain ⟨hN, f, hf⟩ := hb.2.1 hq
    exact ⟨_, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
      QuotientGroup.ker_mk' _, f, hf⟩
  · intro m hm hA
    obtain ⟨hQ, hUC, -, h4, h5, hcen⟩ := hc m hm hA
    have hZ : CFSG.QuasithinUnique.blockZ L = ⊥ := by
      rcases hm with rfl | rfl
      · exact CFSG.Quasithin.H13.VolI.blockZ_eq_bot_of_alt3 hL hA
      · exact CFSG.QuasithinUnique.AppC.blockZ_eq_bot_of_alt5 hL hA
    refine ⟨⟨hQ, hUC, fun u hu c hc' => ?_⟩, hZ, h4, fun h5' => ?_, hcen⟩
    · have huL : u ∈ L :=
        (CFSG.QuasithinUnique.C1.blockQ_le L)
          ((CFSG.QuasithinUnique.C1.blockU_le_blockQ hL) hu)
      exact (Subgroup.mem_centralizer_iff.mp hc'.2 u huL).symm
    · obtain ⟨hN, h⟩ := h5 h5'
      rcases h with h | ⟨h, hc2⟩
      · exact Or.inl (burnsideC1d_quotHas _ h)
      · exact Or.inr ⟨burnsideC1d_quotHas _ h, hc2⟩

@[expose] def C_1_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V T : Subgroup G), HypC_1_14 X V T →
    ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) → ∃ hV : IsElemAbelian 2 V, IsFFInt X V hV

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem as_C_1_15 : C_1_15 := by
  intro G _ _ X V T h hJ
  have hVT : V ≤ T :=
    (burnsideC1a_le_pCoreOf_of_isTwoReducedIn h.reduced).trans
      (CFSG.QuasithinUnique.IsSylowTwoOf.pCoreOf_le h.sylow)
  obtain ⟨A, hA, hAV⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    apply hJ
    unfold thompsonJ
    refine iSup₂_le fun A hA => ?_
    by_contra hA'
    exact hcon ⟨A, hA, hA'⟩
  exact ⟨h.reduced.2.2.1,
    isFFModule_autOn h.reduced.2.2.1 hVT h.reduced.2.1 (hA.1.trans h.sylow.1) hA hAV⟩

@[expose] def C_1_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V T : Subgroup G), HypC_1_14 X V T →
    (∀ K : Subgroup (MulAut ↥V), CFSG.Open.IsComponentOf K (autOn X V) →
      autOn (thompsonJ T) V ≤ Subgroup.normalizer (K : Set (MulAut ↥V))) ∧
    (∀ L : Subgroup G, IsChiBlock2 X L →
      ⁅autOn L V, autOn (thompsonJ T) V⁆ ≠ ⊥ → baum T ≤ Subgroup.normalizer (L : Set G)) ∧
    (IsSQTKIn X → ∀ L : Subgroup G, L ∈ cComp X → CFSG.IsQuasisimple ↥(autOn L V) →
      ⁅autOn L V, autOn (thompsonJ T) V⁆ ≠ ⊥ → baum T ≤ Subgroup.normalizer (L : Set G))

section as_C_1_16

theorem as_C_1_16
    : C_1_16 :=
  fun _ _ _ _ _ _ h => CFSG.Quasithin.C116Bridge.c116_of CFSG.Quasithin.C116Two.theoremC116Two
    (CFSG.Quasithin.C116Three.theoremC116Three CFSG.Quasithin.asB56_holds
      (CFSG.Quasithin.A3Facts.a3_inputs_of_a134_schreier CFSG.Quasithin.A3Facts.a134ForSQTK
        CFSG.Quasithin.A3Facts.schreierSQTK).2.1) h.charTwo h.reduced h.sylow

end as_C_1_16

@[expose] def C_1_18 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω), IsPGroup 2 S → S ≠ ⊥ →
    ∃ C₁ C₂ : Subgroup Ω, IsC118Pair S C₁ C₂

theorem as_C_1_18 : C_1_18 := CFSG.Quasithin.theoremC118

@[expose] def C_1_19 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (S : Subgroup Ω), IsPGroup 2 S → S ≠ ⊥ →
    ∀ C₁ C₂ : Subgroup Ω, IsC118Pair (baum S) C₁ C₂ → IsC118Pair S (centerOf S ⊓ C₁) C₂

theorem as_C_1_19 : C_1_19 := by
  intro Ω _ _ S hS _ C₁ C₂ h
  exact CFSG.Quasithin.isC118Pair_of_baum hS h

@[expose] def C_1_21 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (C₁ C₂ : Subgroup Ω → Subgroup Ω), IsGNChoice C₁ C₂ →
  ∀ (X L T R : Subgroup Ω),
    CharTwo X → L = oTwoUpper X → L ∈ cComp X →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    IsPGroup 2 T → baum T ≤ R → R ≤ T → pCoreOf 2 X ≤ R → R ≤ X →
    (∀ Y : Subgroup Ω, InYSet X R (baum T) Y →
        (Y ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
          (Y ≤ Subgroup.centralizer (C₁ T : Set Ω) ∧
            Y ≤ Subgroup.centralizer (C₁ (baum T) : Set Ω)) ∨
          IsL2OrA3Block Y Y) ∧
        (Y ≤ Subgroup.normalizer (baum T : Set Ω) ∨
          (IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧ ⁅Y, thompsonJ R⁆ = Y))) ∧
    (∀ 𝒴 : Set (Subgroup Ω), (∀ Y ∈ 𝒴, InYSet X R (baum T) Y) →
        X = (⨆ Y ∈ 𝒴, Y) ⊔ (X ⊓ Subgroup.centralizer (omegaOneCenterOf R : Set Ω)) →
        (∀ Y ∈ 𝒴, X = (X ⊓ Subgroup.normalizer (baum T : Set Ω)) ⊔ Y) →
        (C₁ T ≤ centerOf X ∨ X ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
          (IsShort2 L ∧ ∃ hU : IsElemAbelian 2 (blockU L),
            IsFFInt (L ⊔ baum T) (blockU L) hU))) ∧
    (∀ Y : Subgroup Ω, InYSet X R (baum T) Y →
        X = (X ⊓ Subgroup.normalizer (baum T : Set Ω)) ⊔ Y →
        ((∃ D : Subgroup Ω, D ≠ ⊥ ∧ D ≤ baum T ∧ (D.subgroupOf (baum T)).Characteristic ∧
            X ≤ Subgroup.normalizer (D : Set Ω)) ∨
          (IsShort2 L ∧ ∃ hU : IsElemAbelian 2 (blockU L),
            IsFFInt (L ⊔ baum T) (blockU L) hU))) ∧
    (∀ V : Subgroup Ω, IsTwoReducedIn X V →
        autOn (thompsonJ R) V =
          autOn (R ⊓ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) :
            Subgroup Ω) : Set Ω)) V →
        ∀ Y : Subgroup Ω, Y = oTwoUpper Y → Y ≤ X →
          thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) ≤
            Subgroup.normalizer (Y : Set Ω) →
          Y ⊓ Subgroup.centralizer (V : Set Ω) = pCoreOf 2 Y →
          ((∃ n : ℕ, IsPSL 2 2 n
              (↥(autOn (Y ⊔ thompsonJ R) V) ⧸ CFSG.pCore 2 ↥(autOn (Y ⊔ thompsonJ R) V))) ∨
            Nonempty ((↥(autOn (Y ⊔ thompsonJ R) V) ⧸ CFSG.pCore 2 ↥(autOn (Y ⊔ thompsonJ R) V)) ≃*
              Equiv.Perm (Fin 3))) →
          IsSylowTwoOf (autOn (thompsonJ R) V) (autOn (Y ⊔ thompsonJ R) V) →
          ⁅V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω), Y⁆ ≠ ⊥ →
          autOn (baum T) V = autOn (thompsonJ R) V ∧ InYSet X R (baum T) Y)

@[expose] def C_1_22 : Prop :=
  (∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsExcA7Block L →
    blockZ L = ⊥ ∧ Nat.card (blockU L) = 2 ^ 4 ∧
      L ≤ Subgroup.normalizer (blockU L : Set G) ∧
      ∃ hU : IsElemAbelian 2 (blockU L), A7Four (autI hU L) ⊤ ⊥) ∧
  (∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsHatA6Block L →
    L ≤ Subgroup.normalizer (blockU L : Set G) ∧
      ∃ hU : IsElemAbelian 2 (blockU L), TripleA6Six (autI hU L) ⊤ ⊥)

section BurnsideC1c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
private theorem burnsideC1c_inf_centralizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hsh : IsShort2 L) : pCoreOf 2 L = L ⊓ Subgroup.centralizer (blockU L : Set G) :=
  (C1.inf_centralizer_blockU_eq hsh le_rfl Subgroup.le_normalizer
    (fun g hg => ⟨0, by simpa using hg⟩)).symm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
noncomputable def burnsideC1c_iso {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hsh : IsShort2 L) (hU : IsElemAbelian 2 (blockU L)) :
    (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(autI hU L) :=
  (QuotientGroup.quotientMulEquivOfEq (C124.ker_starHom_eq_pCore hU
      (C1.le_normalizer_blockU L) (burnsideC1c_inf_centralizer hsh)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (C124.starHom_surjective hU (C1.le_normalizer_blockU L)))

end BurnsideC1c

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_1_22 : C_1_22 := by
  refine ⟨fun G _ _ L hE => ?_, fun G _ _ L hL => ?_⟩
  · have hsh : IsShort2 L := hE.1
    have hZ : blockZ L = ⊥ := CFSG.QuasithinUnique.L246.C123.blockZ_eq_bot_of_isExcA7Block hE
    have hcard : Nat.card (blockU L) = 2 ^ 4 := CFSG.Quasithin.Gold14610.card_blockU_exc hE
    have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
    have hU : IsElemAbelian 2 (blockU L) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hsh)
    refine ⟨hZ, hcard, hLN, hU, ?_⟩
    obtain ⟨α, hα, hαker⟩ := hE.2.1
    let e7 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have hA7 : Nonempty (↥(autI hU L) ≃* alternatingGroup (Fin 7)) :=
      ⟨(burnsideC1c_iso hsh hU).symm.trans e7⟩
    have hcard' : Nat.card (⊤ : Subgroup (IntMod (blockU L) hU)) = 2 ^ 4 := by
      rw [Subgroup.card_top]
      exact hcard
    have hnt : ∃ h ∈ autI hU L, ∃ u ∈ (⊤ : Subgroup (IntMod (blockU L) hU)), h u ≠ u := by
      by_contra hcon
      push Not at hcon
      have hcen : blockU L ≤ Subgroup.centralizer (L : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have h1 := hcon (convI hU ⟨g, hLN hg⟩) (convI_mem_autI hU hg (hLN hg))
          (IntMod.mk hU ⟨u, hu⟩) (Subgroup.mem_top _)
        have h2 := congrArg IntMod.val h1
        rw [convI_apply_val] at h2
        have h3 : g * u * (g : G)⁻¹ = u := h2
        exact mul_inv_eq_iff_eq_mul.1 h3
      have hbz : blockU L ≤ blockZ L := fun u hu => Subgroup.mem_inf.2 ⟨hu, hcen hu⟩
      rw [hZ] at hbz
      have hbot : blockU L = ⊥ := le_bot_iff.1 hbz
      rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    exact CFSG.Quasithin.H.A7.a7Four_of_nontrivial hA7 (fun _ _ _ _ => Subgroup.mem_top _)
      (fun u _ => by
        rw [← pow_two]
        exact CFSG.Quasithin.IntMod.sq_eq_one u) hcard' hnt
  · have hsh : IsShort2 L := hL.1
    have hU : IsElemAbelian 2 (blockU L) := C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hsh)
    have hLN : L ≤ Subgroup.normalizer (blockU L : Set G) := C1.le_normalizer_blockU L
    refine ⟨hLN, hU, ?_⟩
    have hI : CFSG.Quasithin.IsHat ↥(autI hU L) (alternatingGroup (Fin 6)) :=
      IsHat.of_mulEquiv (burnsideC1c_iso hsh hU) hL.2.1
    obtain ⟨hq, hc, ⟨e6⟩⟩ := hI
    have hV2 : ∀ v : IntMod (blockU L) hU, v ^ 2 = 1 := fun v =>
      CFSG.Quasithin.IntMod.sq_eq_one v
    have hVc : Nat.card (IntMod (blockU L) hU) = 2 ^ 6 := hL.2.2.1
    exact CFSG.Quasithin.HatA6.hatA6SixModel (IntMod (blockU L) hU) hV2 hVc (autI hU L) hq.1 hc
      ⟨e6⟩

end

@[expose] def C_1_23 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (C₁ C₂ : Subgroup Ω → Subgroup Ω), IsGNChoice C₁ C₂ →
  ∀ (T R X L : Subgroup Ω),
    IsPGroup 2 T → baum T ≤ R → R ≤ T → IsSylowTwoOf R X → L ∈ cComp X →
    (X : Set Ω) = (L : Set Ω) * (R : Set Ω) → CharTwo X →
    (IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsAlt 7 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    (IsAlt 5 (↥L ⧸ CFSG.pCore 2 ↥L) →
      (C₁ T ≤ centerOf X ∨ X ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
        (IsBlock2 X L ∧ (IsAltType L 5 ∨ IsLin2Type L 2) ∧ ⁅L, thompsonJ T⁆ = L))) ∧
    (IsBlock2 X L → IsExcA7Block L →
      X = (X ⊓ Subgroup.centralizer (C₁ T : Set Ω)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set Ω)))

@[expose] def C_1_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V T L R : Subgroup G), HypC_1_14 X V T →
    (X : Set G) = (L : Set G) * (T : Set G) → L ∈ cComp X → CharTwo L → ⁅V, L⁆ ≠ ⊥ →
    pCoreOf 2 X ≤ R → R ≤ T →
    ∀ m : ℕ, IsAltQuotient L (oTwoZIn L) m →
      ((m = 5 ∨ m = 7) ∨ (m = 6 ∧ autOn R V ≤ autOn L V) ∨
        (m = 6 ∧ Nat.card ↥(autOn R V) = 2)) →
      ((∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum R ∧ (D.subgroupOf (baum R)).Characteristic ∧
          X ≤ Subgroup.normalizer (D : Set G)) ∨
        IsChiBlock2 X L ∨ (IsBlock2 X L ∧ IsExcA7Block L) ∨
          (IsBlock2 X L ∧ IsAltBlockType L 6) ∨ (IsBlock2 X L ∧ IsHatA6Block L))

section BurnsideC124

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_addRight_pow_apply (n : ℕ) (x : ZMod 7) :
    ((Equiv.addRight (1 : ZMod 7)) ^ n) x = x + (n : ZMod 7) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Perm.mul_apply, Equiv.coe_addRight, ih]
    push_cast
    ring

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_finRotate_eq : (finRotate 7 : Perm (Fin 7)) =
    (Equiv.addRight (1 : ZMod 7) : Perm (Fin 7)) := by
  refine Equiv.ext fun z => ?_
  revert z
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_affine_of_shift {g : Perm (ZMod 7)} {j : ZMod 7}
    (h : ∀ x, g (x + 1) = g x + j) (x : ZMod 7) : g x = g 0 + j * x := by
  have key : ∀ n : ℕ, g (n : ZMod 7) = g 0 + j * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [h, ih]
      ring
  have := key x.val
  rwa [ZMod.natCast_zmod_val] at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_orderOf_addRight : orderOf (Equiv.addRight (1 : ZMod 7)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : (Equiv.addRight (1 : ZMod 7)) ^ 7 = 1 := by
    refine Equiv.ext fun x => ?_
    rw [burnsideC124_addRight_pow_apply]
    simp only [Perm.coe_one, id_eq]
    rw [ZMod.natCast_self, add_zero]
  refine orderOf_eq_prime h7 fun h => ?_
  have := congrArg (fun f : Perm (ZMod 7) => f 0) h
  simp at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sign_mulLeft (k : ZMod 7) (hk : k ≠ 0) :
    sign (Equiv.mulLeft₀ k hk) = 1 ↔ k = 1 ∨ k = 2 ∨ k = 4 := by
  revert k
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sign_addRight (b : ZMod 7) : sign (Equiv.addRight b) = 1 := by
  revert b
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_slope_of_even {g : Perm (ZMod 7)} {b j : ZMod 7}
    (hg : ∀ x, g x = b + j * x) (hs : sign g = 1) : j = 1 ∨ j = 2 ∨ j = 4 := by
  have hj : j ≠ 0 := by
    intro h0
    have h01 : g 0 = g 1 := by rw [hg, hg, h0]; simp
    exact absurd (g.injective h01) (by decide)
  have : g = (Equiv.mulLeft₀ j hj).trans (Equiv.addRight b) := by
    refine Equiv.ext fun x => ?_
    simp [hg, add_comm]
  rw [this, Perm.sign_trans, burnsideC124_sign_addRight, one_mul] at hs
  exact (burnsideC124_sign_mulLeft j hj).1 hs

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normalizer_affine {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1) (g : ↥M)
    (hg : g ∈ Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) :
    ∃ b j : ZMod 7, (j = 1 ∨ j = 2 ∨ j = 4) ∧ ∀ x, (g : Perm (ZMod 7)) x = b + j * x := by
  classical
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hmem : g * z * g⁻¹ ∈ zpowers z :=
    (Subgroup.mem_normalizer_iff.1 hg z).1 (mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf, hzo] at hmem
  obtain ⟨n, hn, hnz⟩ := Finset.mem_image.1 hmem
  have hn' := congrArg (fun a : ↥M => (a : Perm (ZMod 7))) hnz
  have hcz : ((z : ↥M) : Perm (ZMod 7)) = Equiv.addRight (1 : ZMod 7) := rfl
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, hcz] at hn'
  have hshift : ∀ x : ZMod 7,
      (g : Perm (ZMod 7)) (x + 1) = (g : Perm (ZMod 7)) x + (n : ZMod 7) := by
    intro x
    have h1 : (g : Perm (ZMod 7)) * Equiv.addRight (1 : ZMod 7) =
        (Equiv.addRight (1 : ZMod 7)) ^ n * (g : Perm (ZMod 7)) := by
      rw [hn']
      group
    have h2 := congrArg (fun f : Perm (ZMod 7) => f x) h1
    simp only [Perm.mul_apply, Equiv.coe_addRight, burnsideC124_addRight_pow_apply] at h2
    rw [h2]
  have haff := burnsideC124_affine_of_shift hshift
  refine ⟨(g : Perm (ZMod 7)) 0, (n : ZMod 7), ?_, haff⟩
  exact burnsideC124_slope_of_even (fun x => haff x) (hA g g.2)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normalizer_card {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1) :
    Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 7 ∨
    Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 21 := by
  classical
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  set N : Subgroup ↥M := Subgroup.normalizer ((zpowers z : Subgroup ↥M) : Set ↥M) with hN
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have h7 : 7 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := zpowers z))
    rwa [Nat.card_zpowers, hzo] at this
  have hle : Nat.card N ≤ 21 := by
    let S : Finset (ZMod 7 × ZMod 7) := ({1, 2, 4} : Finset (ZMod 7)) ×ˢ Finset.univ
    have hS : S.card = 21 := by decide
    let F : ↥N → ↥S := fun g =>
      ⟨(((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0,
        ((g : ↥M) : Perm (ZMod 7)) 0), by
        obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA g g.2
        have e0 := hg 0
        have e1 := hg 1
        simp only [S, Finset.mem_product, Finset.mem_univ, and_true]
        have : ((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0 = j := by
          rw [e1, e0]; ring
        rw [this]
        rcases hj with rfl | rfl | rfl <;> decide⟩
    have hF : Function.Injective F := by
      intro g g' h
      have hh := Subtype.mk.inj h
      simp only [Prod.mk.injEq] at hh
      obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA g g.2
      obtain ⟨b', j', hj', hg'⟩ := burnsideC124_normalizer_affine hc hA g' g'.2
      have e : ∀ x, ((g : ↥M) : Perm (ZMod 7)) x = ((g' : ↥M) : Perm (ZMod 7)) x := by
        intro x
        have a0 : ((g : ↥M) : Perm (ZMod 7)) 0 = b := by rw [hg 0]; ring
        have a0' : ((g' : ↥M) : Perm (ZMod 7)) 0 = b' := by rw [hg' 0]; ring
        have a1 : ((g : ↥M) : Perm (ZMod 7)) 1 - ((g : ↥M) : Perm (ZMod 7)) 0 = j := by
          rw [hg 1, a0]; ring
        have a1' : ((g' : ↥M) : Perm (ZMod 7)) 1 - ((g' : ↥M) : Perm (ZMod 7)) 0 = j' := by
          rw [hg' 1, a0']; ring
        have hb : b = b' := by rw [← a0, ← a0']; exact hh.2
        have hj : j = j' := by rw [← a1, ← a1']; exact hh.1
        rw [hg x, hg' x, hb, hj]
      exact Subtype.ext (Subtype.ext (Equiv.ext e))
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_eq_fintype_card (α := ↥S), Fintype.card_coe, hS] at this
  have hodd : ¬ 2 ∣ Nat.card N := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 h2
    have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    obtain ⟨b, j, hj, hg⟩ := burnsideC124_normalizer_affine hc hA (t : ↥M) t.2
    have hsq : ∀ x, ((t : ↥M) : Perm (ZMod 7)) (((t : ↥M) : Perm (ZMod 7)) x) = x := by
      intro x
      have h3 : ((t : ↥M) : Perm (ZMod 7)) * ((t : ↥M) : Perm (ZMod 7)) = 1 := by
        have := congrArg (fun a : ↥N => ((a : ↥M) : Perm (ZMod 7))) ht2
        simpa [pow_two] using this
      have := congrArg (fun f : Perm (ZMod 7) => f x) h3
      simpa using this
    have e0 := hsq 0
    have e1 := hsq 1
    rw [hg 0, hg (b + j * 0)] at e0
    rw [hg 1, hg (b + j * 1)] at e1
    have key : ∀ b j : ZMod 7, (j = 1 ∨ j = 2 ∨ j = 4) → b + j * (b + j * 0) = 0 →
        b + j * (b + j * 1) = 1 → j = 1 ∧ b = 0 := by decide
    obtain ⟨hj1, hb0⟩ := key b j hj (by simpa using e0) (by simpa using e1)
    have : (t : ↥M) = 1 := by
      refine Subtype.ext (Equiv.ext fun x => ?_)
      rw [hg x, hj1, hb0]
      simp
    have ht1 : t = 1 := Subtype.ext this
    rw [ht1, orderOf_one] at ht
    omega
  obtain ⟨m, hm⟩ := h7
  rw [hm] at hle hodd ⊢
  have hm3 : m ≤ 3 := by omega
  interval_cases m <;> omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sylow_count {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hdvd : Nat.card M ∣ 2520) (h7 : 7 ∣ Nat.card M) :
    ∃ n : ℕ, n ≡ 1 [MOD 7] ∧ Nat.card M = n * Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hfac : (Nat.card M).factorization 7 = 1 := by
    have hpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card M).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 h7
    by_contra hne
    have h2 : 2 ≤ (Nat.card M).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card M := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    have := this.trans hdvd
    norm_num at this
  let P : Sylow 7 ↥M := Sylow.ofCard (zpowers z) (by
    rw [Nat.card_zpowers, hzo, hfac, pow_one])
  refine ⟨Nat.card (Sylow 7 ↥M), card_sylow_modEq_one 7 ↥M, ?_⟩
  rw [Sylow.card_eq_index_normalizer P]
  have := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M))
  rw [mul_comm] at this
  exact this.symm

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isPretransitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) : MulAction.IsPretransitive M (ZMod 7) := by
  refine ⟨fun x y => ?_⟩
  have hmem : Equiv.addRight (y - x) ∈ M := by
    have : Equiv.addRight (y - x) = (Equiv.addRight (1 : ZMod 7)) ^ (y - x).val := by
      refine Equiv.ext fun w => ?_
      rw [burnsideC124_addRight_pow_apply, ZMod.natCast_zmod_val]
      rfl
    rw [this]
    exact pow_mem hc _
  refine ⟨⟨Equiv.addRight (y - x), hmem⟩, ?_⟩
  show (Equiv.addRight (y - x)) x = y
  simp only [Equiv.coe_addRight]
  ring

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isPreprimitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) : MulAction.IsPreprimitive M (ZMod 7) := by
  haveI := burnsideC124_isPretransitive hc
  refine MulAction.IsPreprimitive.of_prime_card ?_
  rw [Nat.card_zmod]
  norm_num

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_normal_eq_bot {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (K : Subgroup ↥M) [K.Normal]
    (hK : ¬ 7 ∣ Nat.card K) : K = ⊥ := by
  haveI := burnsideC124_isPretransitive hc
  haveI := burnsideC124_isPreprimitive hc
  by_cases hfix : MulAction.fixedPoints K (ZMod 7) = Set.univ
  · rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine Subtype.ext (Equiv.ext fun x => ?_)
    have hx : x ∈ MulAction.fixedPoints K (ZMod 7) := by rw [hfix]; exact Set.mem_univ x
    exact hx ⟨k, hk⟩
  · exfalso
    haveI : MulAction.IsPretransitive K (ZMod 7) :=
      MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
    have h1 := Subgroup.index_dvd_card (MulAction.stabilizer K (0 : ZMod 7))
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_zmod] at h1
    exact hK h1

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_selfNormalizing {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hdvd : Nat.card M ∣ 2520) (h7 : 7 ∣ Nat.card M)
    (hN : Nat.card (Subgroup.normalizer
      ((zpowers (⟨Equiv.addRight (1 : ZMod 7), hc⟩ : ↥M) : Subgroup ↥M) : Set ↥M)) = 7) :
    Nat.card M = 7 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set z : ↥M := ⟨Equiv.addRight (1 : ZMod 7), hc⟩ with hz
  have hzo : orderOf z = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact burnsideC124_orderOf_addRight
  have hfac : (Nat.card M).factorization 7 = 1 := by
    have hpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card M).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 h7
    by_contra hne
    have h2 : 2 ≤ (Nat.card M).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card M := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    have := this.trans hdvd
    norm_num at this
  let P : Sylow 7 ↥M := Sylow.ofCard (zpowers z) (by
    rw [Nat.card_zpowers, hzo, hfac, pow_one])
  have hPz : (P : Subgroup ↥M) = zpowers z := rfl
  have hNP : Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M) = (P : Subgroup ↥M) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.le_normalizer) ?_).symm
    rw [hPz, Nat.card_zpowers, hzo]
    omega
  have hcomm : ∀ a ∈ (P : Subgroup ↥M), ∀ b ∈ (P : Subgroup ↥M), b * a = a * b := by
    intro a ha b hb
    rw [hPz, mem_zpowers_iff] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact (Commute.zpow_zpow_self z j i).eq
  have hP : Subgroup.normalizer ((P : Subgroup ↥M) : Set ↥M) ≤
      Subgroup.centralizer ((P : Subgroup ↥M) : Set ↥M) := by
    rw [hNP]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hcomm a ha b hb
  have hK := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hKbot : (MonoidHom.transferSylow P hP).ker = ⊥ :=
    burnsideC124_normal_eq_bot hc _ hK
  have hcard := hcompl.card_mul
  rw [hKbot, Subgroup.card_bot, one_mul, hPz, Nat.card_zpowers, hzo] at hcard
  exact hcard.symm

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_le_of_free {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M)
    (hfree : ∀ g ∈ M, g ≠ 1 → ∀ x y : ZMod 7, x ≠ y → g x = x → g y = y → False) :
    Nat.card M ≤ 42 := by
  haveI := burnsideC124_isPretransitive hc
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer M (0 : ZMod 7))
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_zmod] at hmul
  have hle : Nat.card (MulAction.stabilizer M (0 : ZMod 7)) ≤ 6 := by
    let F : ↥(MulAction.stabilizer M (0 : ZMod 7)) → {x : ZMod 7 // x ≠ 0} := fun g =>
      ⟨((g : ↥M) : Perm (ZMod 7)) 1, by
        intro h0
        have hg0 : ((g : ↥M) : Perm (ZMod 7)) 0 = 0 := g.2
        exact absurd (((g : ↥M) : Perm (ZMod 7)).injective (h0.trans hg0.symm)) (by decide)⟩
    have hF : Function.Injective F := by
      intro g g' h
      have h1 : ((g : ↥M) : Perm (ZMod 7)) 1 = ((g' : ↥M) : Perm (ZMod 7)) 1 :=
        congrArg Subtype.val h
      have hg0 : ((g : ↥M) : Perm (ZMod 7)) 0 = 0 := g.2
      have hg0' : ((g' : ↥M) : Perm (ZMod 7)) 0 = 0 := g'.2
      by_contra hne
      have hne' : ((g' : ↥M) : Perm (ZMod 7))⁻¹ * ((g : ↥M) : Perm (ZMod 7)) ≠ 1 := by
        intro h2
        apply hne
        have : ((g : ↥M) : Perm (ZMod 7)) = ((g' : ↥M) : Perm (ZMod 7)) := by
          have := congrArg (fun f : Perm (ZMod 7) => ((g' : ↥M) : Perm (ZMod 7)) * f) h2
          simpa using this
        exact Subtype.ext (Subtype.ext this)
      refine hfree _ (M.mul_mem (M.inv_mem (g' : ↥M).2) (g : ↥M).2) hne' 0 1 (by decide) ?_ ?_
      · have hinv0 : ((g' : ↥M) : Perm (ZMod 7))⁻¹ 0 = 0 := by
          rw [Perm.inv_eq_iff_eq]
          exact hg0'.symm
        rw [Perm.mul_apply, hg0, hinv0]
      · rw [Perm.mul_apply, h1]
        simp
    have := Nat.card_le_card_of_injective F hF
    have h6 : Nat.card {x : ZMod 7 // x ≠ 0} = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_multiset_six {s : Multiset ℕ} (hmem : ∀ n ∈ s, 2 ≤ n ∧ n ∣ 6)
    (hsum : s.sum ≤ 7) (hlcm : s.lcm = 6) (hev : Even (s.sum + Multiset.card s)) :
    s = {3, 2, 2} := by
  have hcard : Multiset.card s ≤ 3 := by
    have h2 : Multiset.card s • 2 ≤ s.sum := Multiset.card_nsmul_le_sum (fun x hx => (hmem x hx).1)
    simp only [smul_eq_mul] at h2
    omega
  have hdvd : ∀ n ∈ s, n = 2 ∨ n = 3 ∨ n = 6 := by
    intro n hn
    obtain ⟨h2, hd⟩ := hmem n hn
    have h6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases n <;> first | omega | (exfalso; norm_num at hd)
  generalize hc : Multiset.card s = c at hcard
  interval_cases c
  · rw [Multiset.card_eq_zero] at hc
    subst hc
    simp at hlcm
  · rw [Multiset.card_eq_one] at hc
    obtain ⟨a, rfl⟩ := hc
    simp at hlcm hev hsum
    subst hlcm
    exact absurd hev (by decide)
  · rw [Multiset.card_eq_two] at hc
    obtain ⟨a, b, rfl⟩ := hc
    have ha := hdvd a (by simp)
    have hb := hdvd b (by simp)
    simp at hlcm hev hsum
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> first
      | omega
      | (exfalso; revert hlcm; decide)
      | (exfalso; revert hev; decide)
  · rw [Multiset.card_eq_three] at hc
    obtain ⟨a, b, c, rfl⟩ := hc
    have ha := hdvd a (by simp)
    have hb := hdvd b (by simp)
    have hc' := hdvd c (by simp)
    simp at hlcm hev hsum
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc' with rfl | rfl | rfl <;> first
      | omega
      | (exfalso; revert hlcm; decide)
      | (exfalso; revert hev; decide)
      | decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_cycleType_six {g : Perm (ZMod 7)} (hs : sign g = 1) (ho : orderOf
    g = 6) :
    g.cycleType = {3, 2, 2} := by
  have hlcm := Equiv.Perm.lcm_cycleType g
  rw [ho] at hlcm
  have hsum : g.cycleType.sum ≤ 7 := by
    have := Equiv.Perm.sum_cycleType_le g
    rwa [ZMod.card] at this
  have hmem : ∀ n ∈ g.cycleType, 2 ≤ n ∧ n ∣ 6 := fun n hn =>
    ⟨Equiv.Perm.two_le_of_mem_cycleType hn, ho ▸ Equiv.Perm.dvd_of_mem_cycleType hn⟩
  have hsign := Equiv.Perm.sign_of_cycleType g
  rw [hs] at hsign
  have hev : Even (g.cycleType.sum + Multiset.card g.cycleType) :=
    (neg_one_pow_eq_one_iff_even (by decide)).1 hsign.symm
  exact burnsideC124_multiset_six hmem hsum hlcm hev

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_g0_sq :
    ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4 * swap 5 6) ^ 2 =
      (swap (0 : ZMod 7) 1 * swap 0 2) * (swap 0 1 * swap 0 2) := by
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_disj1 : Disjoint (swap (0 : ZMod 7) 1 * swap 0 2) (swap 3 4) := by
  intro x
  revert x
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_disj2 :
    Disjoint ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4) (swap 5 6) := by
  intro x
  revert x
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_g0_cycleType :
    ((swap (0 : ZMod 7) 1 * swap 0 2) * swap 3 4 * swap 5 6).cycleType = {3, 2, 2} := by
  have h3 : (swap (0 : ZMod 7) 1 * swap 0 2).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  have h3ct : (swap (0 : ZMod 7) 1 * swap 0 2).cycleType = {3} := h3
  have h34 : (swap (3 : ZMod 7) 4).cycleType = {2} := by
    rw [(isCycle_swap (by decide)).cycleType, support_swap (by decide)]
    decide
  have h56 : (swap (5 : ZMod 7) 6).cycleType = {2} := by
    rw [(isCycle_swap (by decide)).cycleType, support_swap (by decide)]
    decide
  rw [burnsideC124_disj2.cycleType_mul, burnsideC124_disj1.cycleType_mul, h3ct, h34, h56]
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_sq_threeCycle {g : Perm (ZMod 7)} (hs : sign g = 1) (ho : orderOf
    g = 6) :
    (g ^ 2).IsThreeCycle := by
  have hct := burnsideC124_cycleType_six hs ho
  have h3 : (swap (0 : ZMod 7) 1 * swap 0 2).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2
    (hct.trans burnsideC124_g0_cycleType.symm))
  have hct2 : (c * (g ^ 2) * c⁻¹).cycleType = (g ^ 2).cycleType := cycleType_conj
  have : c * (g ^ 2) * c⁻¹ = (swap (0 : ZMod 7) 1 * swap 0 2) * (swap 0 1 * swap 0 2) := by
    rw [← burnsideC124_g0_sq, ← hc, conj_pow]
  rw [this] at hct2
  exact hct2.symm.trans h3.isThreeCycle_sq

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_no_order_six {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hsmall : Nat.card M < 2520) (g : ↥M) : orderOf g ≠ 6 := by
  intro ho
  have ho' : orderOf ((g : ↥M) : Perm (ZMod 7)) = 6 := by rw [Subgroup.orderOf_coe]; exact ho
  have h3 := burnsideC124_sq_threeCycle (hA g g.2) ho'
  have hmem : ((g : ↥M) : Perm (ZMod 7)) ^ 2 ∈ M := pow_mem g.2 2
  have hle := Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (burnsideC124_isPreprimitive hc) h3 hmem
  have hcard := Subgroup.card_le_of_le hle
  rw [nat_card_alternatingGroup, Nat.card_zmod] at hcard
  have h7 : Nat.factorial 7 / 2 = 2520 := by decide
  rw [h7] at hcard
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_solvable_card_84 {Q : Type*} [Group Q] [Finite Q] (h : Nat.card Q
    = 84) :
    Group.IsSolvable Q := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 Q) := inferInstance
  have hfac : (Nat.card Q).factorization 7 = 1 := by
    have hpos : Nat.card Q ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card Q).factorization 7 :=
      (Nat.Prime.dvd_iff_one_le_factorization (Fact.out) hpos).1 (by rw [h]; norm_num)
    by_contra hne
    have h2 : 2 ≤ (Nat.card Q).factorization 7 := by omega
    have : 7 ^ 2 ∣ Nat.card Q := (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) hpos).2 h2
    rw [h] at this
    norm_num at this
  have hPcard : Nat.card P = 7 := by rw [Sylow.card_eq_multiplicity, hfac, pow_one]
  have hidx : (P : Subgroup Q).index = 12 := by
    have := Subgroup.card_mul_index (P : Subgroup Q)
    rw [h] at this
    have hP' : Nat.card (P : Subgroup Q) = 7 := hPcard
    rw [hP'] at this
    omega
  have hn : Nat.card (Sylow 7 Q) ∣ 12 := hidx ▸ Sylow.card_dvd_index P
  have hmod : Nat.card (Sylow 7 Q) % 7 = 1 := card_sylow_modEq_one 7 Q
  have hn1 : Nat.card (Sylow 7 Q) = 1 := by
    have hle : Nat.card (Sylow 7 Q) ≤ 12 := Nat.le_of_dvd (by norm_num) hn
    have hpos : 0 < Nat.card (Sylow 7 Q) := Nat.card_pos
    generalize Nat.card (Sylow 7 Q) = n at hn hmod hle hpos
    interval_cases n <;> first | rfl | omega | (exfalso; norm_num at hn)
  haveI : Subsingleton (Sylow 7 Q) := (Nat.card_eq_one_iff_unique.1 hn1).1
  haveI : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  haveI : Group.IsSolvable (P : Subgroup Q) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by
      have : Nat.card (P : Subgroup Q) = 7 := hPcard
      omega)
  haveI : Group.IsSolvable (Q ⧸ (P : Subgroup Q)) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by
      have : Nat.card (Q ⧸ (P : Subgroup Q)) = 12 := by rw [← Subgroup.index, hidx]
      omega)
  exact Group.isSolvable_of_subgroup_quotient (P : Subgroup Q)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_solvable_of_card_dvd_168 {Q : Type*} [Group Q] [Finite Q]
    (h : Nat.card Q ∣ 168) (hlt : Nat.card Q < 168) : Group.IsSolvable Q := by
  by_cases h60 : Nat.card Q < 60
  · exact CFSG.GroupTheory.groups_order_below_sixty_solvable h60
  · have hpos : 0 < Nat.card Q := Nat.card_pos
    have h84 : Nat.card Q = 84 := by
      obtain ⟨k, hk⟩ := h
      have hk3 : k ≤ 2 := by
        by_contra hk3
        have : 60 * 3 ≤ Nat.card Q * k := Nat.mul_le_mul (by omega) (by omega)
        omega
      interval_cases k <;> omega
    exact burnsideC124_solvable_card_84 h84

open Equiv Equiv.Perm Subgroup CFSG.ProperTwoGeneratedCore.CosetNormalizer in
private theorem burnsideC124_isKGroupCat_168 {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hcard : Nat.card M = 168) :
    CFSG.SectionRank.IsKGroupCat ↥M := by
  classical
  by_cases hsolv : Group.IsSolvable ↥M
  · exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable hsolv
  · have hnt : Nontrivial ↥M := Finite.one_lt_card_iff_nontrivial.1 (by
      have : 0 < Nat.card M := Nat.card_pos
      omega)
    have hsimple : IsSimpleGroup ↥M := by
      refine ⟨fun N hN => ?_⟩
      by_contra hne
      push Not at hne
      apply hsolv
      have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hne.1
      have hQ1 : 1 < Nat.card (↥M ⧸ N) := Subgroup.one_lt_index_of_ne_top hne.2
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hcard] at hmul
      have hNlt : Nat.card N < 168 := by
        rw [hmul]
        exact lt_mul_left (by omega) hQ1
      have hQlt : Nat.card (↥M ⧸ N) < 168 := by
        rw [hmul]
        exact lt_mul_right (by omega) hN1
      have hNd : Nat.card N ∣ 168 := ⟨Nat.card (↥M ⧸ N), by rw [hmul, mul_comm]⟩
      have hQd : Nat.card (↥M ⧸ N) ∣ 168 := ⟨Nat.card N, by rw [hmul]⟩
      haveI := burnsideC124_solvable_of_card_dvd_168 hNd hNlt
      haveI := burnsideC124_solvable_of_card_dvd_168 hQd hQlt
      exact Group.isSolvable_of_subgroup_quotient N
    have hnonab : ∃ a b : ↥M, a * b ≠ b * a := by
      by_contra hcomm
      push Not at hcomm
      exact hsolv (Group.isSolvable_of_comm hcomm)
    have hsix : ∀ g : ↥M, orderOf g ≠ 6 :=
      burnsideC124_no_order_six hc hA (by omega)
    obtain ⟨-, -, -, -, -, -, -, hmodel⟩ :=
      simple_order_168_without_six_projective_seven_recognition ↥M hnonab hcard hsix
    have hcat : CFSG.Blueprint.Catalog ↥M :=
      CFSG.Blueprint.lieModel_catalog ↥M .PSL 2 7 1 (Or.inl ⟨by decide, hmodel⟩)
    exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_card_168 hcard hcat

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_addRight_mem {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (a : ZMod 7) : Equiv.addRight a ∈ M := by
  have : Equiv.addRight a = (Equiv.addRight (1 : ZMod 7)) ^ a.val := by
    refine Equiv.ext fun w => ?_
    rw [burnsideC124_addRight_pow_apply, ZMod.natCast_zmod_val]
    rfl
  rw [this]
  exact pow_mem hc _

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_alt7 : Nat.card (alternatingGroup (ZMod 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_zmod]
  decide

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_card_dvd_2520 {M : Subgroup (Perm (ZMod 7))}
    (hA : ∀ g ∈ M, sign g = 1) : Nat.card M ∣ 2520 := by
  have hle : M ≤ alternatingGroup (ZMod 7) := fun g hg => Perm.mem_alternatingGroup.2 (hA g hg)
  have := Subgroup.card_dvd_of_le hle
  rwa [burnsideC124_card_alt7] at this

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_order_cases' {m n : ℕ} (hdvd : m ∣ 2520) (h42 : 42 ∣ m) (hlt : m <
    2520)
    (hn : n ≡ 1 [MOD 7]) (hm : m = n * 21) : m = 168 := by
  have hn' : n % 7 = 1 := hn
  have hn120 : n ∣ 120 := by
    rw [hm] at hdvd
    have : n * 21 ∣ 120 * 21 := by simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hn2 : 2 ∣ n := by omega
  have hn119 : n < 120 := by omega
  interval_cases n <;> first | omega | (exfalso; norm_num at hn120) | (exfalso; norm_num at hn2)

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_transitive {M : Subgroup (Perm (ZMod 7))}
    (hc : Equiv.addRight (1 : ZMod 7) ∈ M) (hA : ∀ g ∈ M, sign g = 1)
    (hlt : Nat.card M < 2520) : CFSG.SectionRank.IsKGroupCat ↥M := by
  classical
  by_cases h2 : ∃ g ∈ M, g ≠ 1 ∧ ∃ x y : ZMod 7, x ≠ y ∧ g x = x ∧ g y = y
  · obtain ⟨g, hg, hg1, x, y, hxy, hx, hy⟩ := h2
    have h42 : 42 ∣ Nat.card M :=
      CFSG.Holt.SmallGroups.forty_two_dvd_card_zmod (burnsideC124_addRight_mem hc) hg hg1 hxy hx hy
    have hdvd := burnsideC124_card_dvd_2520 hA
    have h7 : 7 ∣ Nat.card M := (Dvd.intro 6 (by norm_num : 7 * 6 = 42)).trans h42
    obtain ⟨n, hn, hm⟩ := burnsideC124_sylow_count hc hdvd h7
    rcases burnsideC124_normalizer_card hc hA with hN | hN
    · exfalso
      have h := burnsideC124_selfNormalizing hc hdvd h7 hN
      rw [h] at h42
      omega
    · rw [hN] at hm
      have h168 := burnsideC124_order_cases' hdvd h42 hlt hn hm
      exact burnsideC124_isKGroupCat_168 hc hA h168
  · push Not at h2
    have hle := burnsideC124_card_le_of_free hc
      (fun g hg hg1 x y hxy hx hy => h2 g hg hg1 x y hxy hx hy)
    exact CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable
      (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_stab (b : Fin 7) :
    CFSG.SectionRank.IsKGroupCat (MulAction.stabilizer (alternatingGroup (Fin 7)) b) := by
  have hK6 : CFSG.SectionRank.IsKGroupCat (alternatingGroup {x : Fin 7 // x ≠ b}) := by
    have hcard : Fintype.card {x : Fin 7 // x ≠ b} = Fintype.card (Fin 6) := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin]
      simp
    obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard |>.nonempty
    exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv
      CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_alternatingGroup_six e.altCongrHom
  let f₁ : alternatingGroup {x : Fin 7 // x ≠ b} →* Perm (Fin 7) :=
    Equiv.Perm.ofSubtype.comp (alternatingGroup _).subtype
  have hf₁ : ∀ a, f₁ a ∈ alternatingGroup (Fin 7) := fun a => by
    rw [mem_alternatingGroup]
    simpa [f₁, sign_ofSubtype] using mem_alternatingGroup.mp a.2
  let f₂ := f₁.codRestrict (alternatingGroup (Fin 7)) hf₁
  have hf₂ : ∀ a, f₂ a ∈ MulAction.stabilizer (alternatingGroup (Fin 7)) b := fun a => by
    rw [MulAction.mem_stabilizer_iff]
    exact ofSubtype_apply_of_not_mem _ (by simp)
  have hsurj : Function.Surjective (f₂.codRestrict _ hf₂) := by
    rintro ⟨⟨τ, hτ⟩, hτ0⟩
    have h0 : τ b = b := hτ0
    have h₁ : ∀ x, τ x ≠ b ↔ x ≠ b := fun x =>
      not_congr ⟨fun h => τ.injective (h.trans h0.symm), fun h => h ▸ h0⟩
    have hsub : ofSubtype (τ.subtypePerm (p := fun y => y ≠ b) h₁) = τ :=
      ofSubtype_subtypePerm (p := fun y => y ≠ b) h₁ fun x hx h => hx (h.symm ▸ h0)
    refine ⟨⟨τ.subtypePerm (p := fun y => y ≠ b) h₁, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, ← sign_ofSubtype, hsub]
      exact mem_alternatingGroup.mp hτ
    · exact Subtype.ext (Subtype.ext hsub)
  exact CFSG.SectionRank.IsKGroupCat.of_surjective hK6 _ hsurj

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_of_small_orbit
    {H : Subgroup (alternatingGroup (Fin 7))} {b : Fin 7}
    (hO : Nat.card (MulAction.orbit H b) ≤ 3) : CFSG.SectionRank.IsKGroupCat ↥H := by
  let ψ : ↥H →* Perm (MulAction.orbit H b) := MulAction.toPermHom H _
  refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_ker ψ ?_ ?_
  · let f : ψ.ker →* MulAction.stabilizer (alternatingGroup (Fin 7)) b :=
      ((H.subtype.comp ψ.ker.subtype).codRestrict
        (MulAction.stabilizer (alternatingGroup (Fin 7)) b) (fun g => by
          have hg := g.2
          rw [MonoidHom.mem_ker] at hg
          have := congrArg
            (fun p : Perm (MulAction.orbit H b) => (p ⟨b, MulAction.mem_orbit_self b⟩ : Fin 7)) hg
          rw [MulAction.mem_stabilizer_iff]
          simpa [ψ, MulAction.toPermHom_apply, Subgroup.smul_def] using this))
    refine CFSG.SectionRank.IsKGroupCat.of_injective (burnsideC124_isKGroupCat_stab b) f ?_
    intro g g' h
    have := congrArg (fun a : MulAction.stabilizer (alternatingGroup (Fin 7)) b =>
      ((a : alternatingGroup (Fin 7)) : Perm (Fin 7))) h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  · refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_solvable
      (CFSG.GroupTheory.groups_order_below_sixty_solvable ?_)
    rw [Nat.card_perm]
    have : (Nat.card (MulAction.orbit H b)).factorial ≤ Nat.factorial 3 := Nat.factorial_le hO
    have h6 : Nat.factorial 3 = 6 := by decide
    omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_exists_small_orbit {H : Subgroup (alternatingGroup (Fin 7))}
    (h : ¬ MulAction.IsPretransitive H (Fin 7)) :
    ∃ b : Fin 7, Nat.card (MulAction.orbit H b) ≤ 3 := by
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  push Not at hxy
  have hy : y ∉ MulAction.orbit H x := fun ⟨g, hg⟩ => hxy g hg
  have hdisj : Disjoint (MulAction.orbit H x) (MulAction.orbit H y) := by
    rw [Set.disjoint_left]
    intro z hzx hzy
    apply hy
    have h1 : MulAction.orbit H z = MulAction.orbit H x := MulAction.orbit_eq_iff.2 hzx
    have h2 : MulAction.orbit H z = MulAction.orbit H y := MulAction.orbit_eq_iff.2 hzy
    have := MulAction.mem_orbit_self (M := H) y
    rwa [← h2, h1] at this
  have hx4 := hcon x
  have hy4 := hcon y
  rw [Nat.card_coe_set_eq] at hx4 hy4
  have hunion := Set.ncard_union_eq hdisj
  have hle : (MulAction.orbit H x ∪ MulAction.orbit H y).ncard ≤ 7 := by
    have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit H x ∪ MulAction.orbit H y))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_of_transitive {H : Subgroup (alternatingGroup (Fin 7))}
    (hH : H ≠ ⊤) (htr : MulAction.IsPretransitive H (Fin 7)) :
    CFSG.SectionRank.IsKGroupCat ↥H := by
  classical
  have hinj1 : Function.Injective (alternatingGroup (Fin 7)).subtype := Subtype.val_injective
  set H' : Subgroup (Perm (Fin 7)) := H.map (alternatingGroup (Fin 7)).subtype with hH'
  have hH'card : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective hinj1
  have h7 : 7 ∣ Nat.card H := by
    have h1 := Subgroup.index_dvd_card (MulAction.stabilizer H (0 : Fin 7))
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := CFSG.Holt.SmallGroups.exists_finRotate_mem_map_conj (M := H') (hH'card ▸ h7)
  set M : Subgroup (Perm (Fin 7)) := H'.map (MulAut.conj σ).toMonoidHom with hMdef
  have hc : (Equiv.addRight (1 : ZMod 7) : Perm (Fin 7)) ∈ M := by
    have h := hσ
    rw [burnsideC124_finRotate_eq] at h
    exact h
  have hA : ∀ g ∈ M, sign g = 1 := by
    intro g hg
    obtain ⟨h, ⟨a, ha, rfl⟩, rfl⟩ := hg
    have hs : sign (a : Perm (Fin 7)) = 1 := Perm.mem_alternatingGroup.1 a.2
    show sign (σ * (a : Perm (Fin 7)) * σ⁻¹) = 1
    rw [map_mul, map_mul, hs, mul_one, map_inv, mul_inv_cancel]
  have hMcard : Nat.card M = Nat.card H := by
    rw [hMdef, Subgroup.card_map_of_injective (MulAut.conj σ).injective, hH'card]
  have hlt : Nat.card M < 2520 := by
    rw [hMcard]
    have hle := Subgroup.card_le_card_group H
    have hne : Nat.card H ≠ Nat.card (alternatingGroup (Fin 7)) := fun h =>
      hH (Subgroup.eq_top_of_card_eq H h)
    have h2520 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega
  have hK : CFSG.SectionRank.IsKGroupCat ↥M := burnsideC124_isKGroupCat_transitive hc hA hlt
  exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv hK
    ((Subgroup.equivMapOfInjective H _ hinj1).trans
      (Subgroup.equivMapOfInjective H' (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective))

open Equiv Equiv.Perm Subgroup in
private theorem burnsideC124_isKGroupCat_alt7 :
    CFSG.SectionRank.IsKGroupCat (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine CFSG.Quasithin.H13.U3.GC137.SQ.isKGroupCat_of_simple
    (Or.inr (Or.inl ⟨7, by norm_num, ⟨MulEquiv.refl _⟩⟩)) fun H hH N _ hs hnab => ?_
  have hKH : CFSG.SectionRank.IsKGroupCat ↥H := by
    by_cases htr : MulAction.IsPretransitive H (Fin 7)
    · exact burnsideC124_isKGroupCat_of_transitive hH htr
    · obtain ⟨b, hb⟩ := burnsideC124_exists_small_orbit htr
      exact burnsideC124_isKGroupCat_of_small_orbit hb
  haveI := hs
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hKH ⊤
    ((QuotientGroup.mk' N).comp (⊤ : Subgroup ↥H).subtype) (by
      intro q
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨⟨h, trivial⟩, rfl⟩)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_ker_dvd {E : Type} [Group E]
    [Finite E]
    [Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker ∣ 6 := by
  have hsurj := hopfMultiplierToKer_surjective q hq hker
  have key := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (hopfMultiplierToKer q hq hker).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv] at key
  have hdvd : Nat.card q.ker ∣ Nat.card (hopfMultiplier (alternatingGroup (Fin m))) :=
    Dvd.intro _ key.symm
  rcases hm with rfl | rfl | rfl
  · rw [hopfMultiplier_alternatingGroup_five.2] at hdvd
    exact hdvd.trans (by norm_num)
  · rwa [hopfMultiplier_alternatingGroup_six.2] at hdvd
  · rwa [hopfMultiplier_alternatingGroup_seven.2] at hdvd

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_alt {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7) :
    Nat.card (alternatingGroup (Fin m)) = 60 ∨ Nat.card (alternatingGroup (Fin m)) = 360 ∨
      Nat.card (alternatingGroup (Fin m)) = 2520 := by
  rcases hm with rfl | rfl | rfl
  · left
    have := nat_card_alternatingGroup_fin 3
    simpa [Nat.factorial] using this
  · right; left
    have := nat_card_alternatingGroup_fin 4
    simpa [Nat.factorial] using this
  · right; right
    have := nat_card_alternatingGroup_fin 5
    simpa [Nat.factorial] using this

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_card_dvd {E : Type} [Group E] [Finite E]
    [Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) :
    Nat.card E = Nat.card (alternatingGroup (Fin m)) * Nat.card q.ker ∧ Nat.card E ∣ 15120 := by
  have hK := burnsideC124_card_ker_dvd hm q hq hker
  have hcard : Nat.card E = Nat.card (alternatingGroup (Fin m)) * Nat.card q.ker := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
  refine ⟨hcard, ?_⟩
  rw [hcard]
  have hA : Nat.card (alternatingGroup (Fin m)) ∣ 2520 := by
    rcases burnsideC124_card_alt hm with h | h | h <;> rw [h] <;> norm_num
  exact (Nat.mul_dvd_mul hA hK).trans (by norm_num)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_not_cube_dvd {N p : ℕ} (hN : N ∣ 15120) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : ¬ p ^ 3 ∣ N := by
  intro hd
  have h1 : p ^ 3 ∣ 15120 := hd.trans hN
  have h2 : p ∣ 15120 := (dvd_pow_self p (by norm_num)).trans h1
  have h3 : p ≤ 15120 := Nat.le_of_dvd (by norm_num) h2
  have : p ^ 3 ≤ 15120 := Nat.le_of_dvd (by norm_num) h1
  have hp25 : p < 25 := by
    by_contra h
    have : 25 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases p <;> first
    | (exfalso; revert hp; norm_num; done)
    | omega
    | (exfalso; revert h1; norm_num; done)

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.RankThree.PerfectCover CFSG.Alternating.Multipliers CFSG.RankThree.PartTwo in
private theorem burnsideC124_rankLeTwo {E : Type} [Group E]
    [Finite E]
    [hperf : Group.IsPerfect E] {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (q : E →* alternatingGroup (Fin m)) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : RankLeTwo E := by
  obtain ⟨hcard, hdvd⟩ := burnsideC124_card_dvd hm q hq hker
  have hK := burnsideC124_card_ker_dvd hm q hq hker
  intro p hp hp2 F hF
  by_cases hp3 : p = 3
  · subst hp3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ :=
      (CFSG.Quasithin.H13.U3.GC137.SQ.isPGroup_of_isElemAbelian (p := 3) hF).exists_card_eq
    have hFdvd : 3 ^ n ∣ Nat.card E := hn ▸ Subgroup.card_subgroup_dvd_card F
    have hn3 : n ≤ 3 := by
      by_contra h
      have h4 : 3 ^ 4 ∣ 15120 := (pow_dvd_pow 3 (by omega)).trans (hFdvd.trans hdvd)
      norm_num at h4
    rw [hn]
    by_cases h3 : n = 3
    · exfalso
      subst h3
      have h27 : 27 ∣ Nat.card E := by simpa using hFdvd
      have h3K : 3 ∣ Nat.card q.ker := by
        rw [hcard] at h27
        have hk6 : Nat.card q.ker ≤ 6 := Nat.le_of_dvd (by norm_num) hK
        have hkpos : 0 < Nat.card q.ker := Nat.card_pos
        rcases burnsideC124_card_alt hm with h | h | h <;> rw [h] at h27 <;>
          interval_cases hk : Nat.card q.ker <;> omega
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := q.ker) 3 h3K
      have hzo : orderOf (x : E) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
      have hzc : (x : E) ∈ Subgroup.center E := hker x.2
      have hFab : ∀ a b : F, a * b = b * a := fun a b => hF.1.is_comm.comm a b
      have hpow := KFacts.KS14.pow_index_eq_one_of_isPerfect F hFab hzc
      have hmul := F.card_mul_index
      rw [hn] at hmul
      have h81 : ¬ 3 ∣ F.index := by
        intro h3i
        have : 3 ^ 4 ∣ Nat.card E := by
          rw [← hmul]
          obtain ⟨c, hc⟩ := h3i
          rw [hc]
          exact ⟨c, by ring⟩
        have := this.trans hdvd
        norm_num at this
      exact h81 (hzo ▸ orderOf_dvd_of_pow_eq_one hpow)
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · exact card_le_of_cube_free hp (burnsideC124_not_cube_dvd hdvd hp hp2 hp3) hF

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have := CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 3
  simpa [Nat.factorial] using this

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_five_le_of_dvd_factorial {k : ℕ} (h : 60 ∣ k.factorial) : 5 ≤ k := by
  by_contra hk
  have : k ≤ 4 := by omega
  interval_cases k <;> simp [Nat.factorial] at h

open CFSG.Quasithin.H13.U3.GC137.SQ CFSG.Blueprint CFSG.SectionRank in
private theorem burnsideC124_isKGroupCat_alt5 : IsKGroupCat (alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine isKGroupCat_of_simple (Or.inr (Or.inl ⟨5, le_rfl, ⟨MulEquiv.refl _⟩⟩))
    fun H hH N _ hs hnab => ?_
  exfalso
  have hdvd := card_dvd_factorial_index hH
  rw [burnsideC124_card_alt_five] at hdvd
  have h5 := burnsideC124_five_le_of_dvd_factorial hdvd
  have hmul := H.card_mul_index
  rw [burnsideC124_card_alt_five] at hmul
  obtain ⟨h60, hle⟩ := sixty_le_card_section N hs hnab
  have hH12 : Nat.card H ≤ 12 := by
    by_contra h
    have : 13 * 5 ≤ Nat.card H * H.index := Nat.mul_le_mul (by omega) h5
    omega
  omega

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_mem_oTwoZIn_iff {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (x : ↥L) :
    (x : G) ∈ oTwoZIn L ↔
      (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  unfold oTwoZIn preimageModTwoCore
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    subst this
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_exists_hom {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}
    (halt : IsAltQuotient L (oTwoZIn L) m) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin m), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨φ, hφ, hker⟩ := halt
  have hmem : ∀ x : ↥L, φ x = 1 ↔ (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro x
    rw [← burnsideC124_mem_oTwoZIn_iff, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hOle : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hmem]
    have : (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [this]
    exact Subgroup.one_mem _
  refine ⟨QuotientGroup.lift _ φ hOle, ?_, ?_⟩
  · intro a
    obtain ⟨x, rfl⟩ := hφ a
    exact ⟨QuotientGroup.mk x, rfl⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MonoidHom.mem_ker] at hz
    exact (hmem x).1 hz

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U3.GC137.SQ CFSG.SectionRank in
private theorem burnsideC124_sqtkGroup
    {G : Type} [Group G] [Finite G] {X T L : Subgroup G} {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 7)
    (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hL : L ∈ cComp X)
    (halt : IsAltQuotient L (oTwoZIn L) m) : SQTKGroup ↥X := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hN : X ≤ Subgroup.normalizer (L : Set G) := C124.le_normalizer_of_prod hT hprod hL
  have hnorm : (L.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hN
  have : (Subgroup.inclusion hLX).range.Normal := by
    rw [Subgroup.inclusion_range]
    exact hnorm
  have hq := isPGroup_quotient_of_prod hT hprod hLX
  have hO : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨ψ, hψ, hψker⟩ := burnsideC124_exists_hom halt
  have hLperf : Group.IsPerfect ↥L := C124.isPerfect_of_comm_eq (perfect_of_mem_cComp hL)
  have hperf : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) := inferInstance
  have hKm : IsKGroupCat (alternatingGroup (Fin m)) := by
    rcases hm with rfl | rfl | rfl
    · exact burnsideC124_isKGroupCat_alt5
    · exact isKGroupCat_alternatingGroup_six
    · exact burnsideC124_isKGroupCat_alt7
  have hK : IsKGroupCat (↥L ⧸ CFSG.pCore 2 ↥L) := by
    refine isKGroupCat_of_ker ψ ?_ hKm
    refine isKGroupCat_of_solvable (Group.isSolvable_of_comm fun a b => Subtype.ext ?_)
    exact (Subgroup.mem_center_iff.1 (hψker a.2) b.1).symm
  have hR : RankLeTwo (↥L ⧸ CFSG.pCore 2 ↥L) := burnsideC124_rankLeTwo hm ψ hψ hψker
  exact ⟨stronglyQuasithin_of_rankLeTwo (rankLeTwo_of_hom (Subgroup.inclusion hLX)
      (Subgroup.inclusion_injective hLX) hq (CFSG.pCore 2 ↥L) hO hR),
    isKGroupCat_of_ext (Subgroup.inclusion hLX) (Subgroup.inclusion_injective hLX) hq
      (CFSG.pCore 2 ↥L) hO hK⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideC124_le_of_autOn_le {G : Type} [Group G] [Finite G] {X V L R : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X) (hRX : R ≤ X)
    (h : autOn R V ≤ autOn L V) : R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G)) := by
  intro r hr
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := hXN (hRX hr)
  obtain ⟨n, hnL, hn⟩ :=
    AutOn.mem_autOn_iff.1 (h (AutOn.conjAct_mem_autOn_of_mem hrN hr))
  have hc : (n : G)⁻¹ * r ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) hn
    simp only [AutOn.coe_conjAct_apply] at h1
    calc v * ((n : G)⁻¹ * r) = (n : G)⁻¹ * ((n : G) * v * (n : G)⁻¹) * r := by group
      _ = (n : G)⁻¹ * (r * v * r⁻¹) * r := by rw [h1]
      _ = (n : G)⁻¹ * r * v := by group
  have hr' : r = (n : G) * ((n : G)⁻¹ * r) := by group
  rw [hr']
  exact Subgroup.mul_mem_sup hnL ⟨X.mul_mem (X.inv_mem (hLX hnL)) (hRX hr), hc⟩

open CFSG.Quasithin CFSG.QuasithinUnique in
private theorem burnsideC124_isChiBlock2 {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (h : IsChiBlock X L) : IsChiBlock2 X L := by
  obtain ⟨hb, hn | ⟨m, hmo, -, hmt⟩⟩ := h
  · exact ⟨hb, Or.inl hn⟩
  · exact ⟨hb, Or.inr ⟨m, hmo, hmt⟩⟩

end BurnsideC124

section

open CFSG.ASVolI.ChC CFSG.Quasithin CFSG.QuasithinUnique in
theorem as_C_1_24
    : C_1_24 := by
  intro G _ _ X V T L R hHyp hXLT hL hCL hVL hQR hRT m halt hm
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t := by
    intro x hx
    have hx' : x ∈ (X : Set G) := hx
    rw [hXLT] at hx'
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨l, hl, t, ht, rfl⟩
  have hmm : m = 5 ∨ m = 6 ∨ m = 7 := by
    rcases hm with (h | h) | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hSQ : SQTKGroup ↥X := burnsideC124_sqtkGroup hmm hHyp.sylow hprod hL halt
  have hRX : R ≤ X := hRT.trans hHyp.sylow.1
  have hm' : m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R V) = 2) := by
    rcases hm with (h | h) | ⟨h, hle⟩ | ⟨h, hc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h, burnsideC124_le_of_autOn_le hHyp.reduced.2.1 hLX hRX hle⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, hc⟩))
  rcases C124.c124StatementSQTK_holds G X T V L R m hHyp.charTwo hSQ hHyp.reduced hHyp.sylow
    hprod hL hCL hVL halt hQR hRT hm' with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (burnsideC124_isChiBlock2 h))
  · obtain ⟨hb, h1 | h2 | h3⟩ := h
    · exact Or.inr (Or.inr (Or.inl ⟨hb, h1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, h3⟩)))

end

@[expose] def C_1_26 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (C₁ C₂ : Subgroup Ω → Subgroup Ω), IsGNChoice C₁ C₂ →
  ∀ (H T : Subgroup Ω), IsSQTKIn H → IsSylowTwoOf T H → CharTwo H → H ∈ uFamHat H T →
    (C₁ T ≤ centerOf H ∨
    H ≤ Subgroup.normalizer (C₂ T : Set Ω) ∨
    ∃ K : Subgroup Ω, IsChi0Block H K ∧ ⁅K, thompsonJ T⁆ = K ∧
      twoResidual H = ⨆ t ∈ T, conjByElt t K ∧
      ∀ t ∈ T, ∀ t' ∈ T, conjByElt t K ≠ conjByElt t' K →
        conjByElt t K ≤ Subgroup.centralizer (conjByElt t' K : Set Ω))

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_1_26
    : C_1_26 := by
  intro Ω _ _ C₁ C₂ hGN H T hS hT hC hH
  have hSTC : CFSG.Quasithin.IsSQTKTC H := (CFSG.Quasithin.C1GN.isSQTKTC_iff_sqtkGroup).2 hS
  have hMin : CFSG.Quasithin.IsMinParabolicOf H H := ⟨T, hT, hH⟩
  rcases CFSG.Quasithin.theoremC126_proved Ω C₁ C₂ hGN H T hSTC hT hC hMin with
    h1 | h2 | ⟨r, K, hr, hK, hcomm, hres, hact, hpair⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · have hr0 : 0 < r := by omega
    refine Or.inr (Or.inr ⟨K ⟨0, hr0⟩, (hK _).1, (hK _).2, ?_, ?_⟩)
    · rw [hres]
      apply le_antisymm
      · refine iSup_le fun i => ?_
        obtain ⟨t, ht, hti⟩ := hpair ⟨0, hr0⟩ i
        refine le_trans (le_of_eq hti.symm) ?_
        exact le_iSup₂ (f := fun (t : Ω) (_ : t ∈ T) => conjByElt t (K ⟨0, hr0⟩)) t ht
      · refine iSup₂_le fun t ht => ?_
        obtain ⟨j, hj⟩ := hact t ht ⟨0, hr0⟩
        exact le_trans (le_of_eq hj) (le_iSup K j)
    · intro t ht t' ht' hne
      obtain ⟨i, hi⟩ := hact t ht ⟨0, hr0⟩
      obtain ⟨j, hj⟩ := hact t' ht' ⟨0, hr0⟩
      have hij : i ≠ j := by
        rintro rfl
        apply hne
        exact hi.trans hj.symm
      have e1 : conjByElt t (K ⟨0, hr0⟩) = K i := hi
      have e2 : conjByElt t' (K ⟨0, hr0⟩) = K j := hj
      rw [e1, e2]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i j hij)

end

@[expose] def C_1_27 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (X T H K : Subgroup Ω),
    CharTwo X → IsSylowTwoOf T X → CFSG.SectionRank.IsKGroupCat ↥X → H ∈ uFamHat X T →
    IsBlock2 H K → ⁅K, thompsonJ T⁆ = K → H = T ⊔ conjClosure K T →
    ∃ L : Subgroup Ω, IsBlock2 X L ∧ K ≤ L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set Ω)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set Ω)) n)

@[expose] def C_1_28 : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (C₁ C₂ : Subgroup Ω → Subgroup Ω), IsGNChoice C₁ C₂ →
  ∀ (X T : Subgroup Ω), CharTwo X → IsSQTKIn X → IsSylowTwoOf T X →
    (X = (X ⊓ Subgroup.centralizer (C₁ T : Set Ω)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set Ω)) ∨
    (∃ L₁ : Subgroup Ω, IsChiBlock2 X L₁ ∧ ⁅L₁, thompsonJ T⁆ = L₁ ∧
      (X : Set Ω) = (((X ⊓ Subgroup.centralizer (C₁ T : Set Ω)) ⊔
        (X ⊓ Subgroup.normalizer (C₂ T : Set Ω)) : Subgroup Ω) : Set Ω) * (L₁ : Set Ω)) ∨
    (∃ L₁ L₂ : Subgroup Ω, IsChiBlock2 X L₁ ∧ ⁅L₁, thompsonJ T⁆ = L₁ ∧
      IsChiBlock2 X L₂ ∧ ⁅L₂, thompsonJ T⁆ = L₂ ∧
      (X : Set Ω) = (((X ⊓ Subgroup.centralizer (C₁ T : Set Ω)) ⊔
        (X ⊓ Subgroup.normalizer (C₂ T : Set Ω)) : Subgroup Ω) : Set Ω) * (L₁ : Set Ω) *
          (L₂ : Set Ω)))

section BurnsideA38b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 in
private theorem burnsideA38b_c127ND {G : Type} [Group G] [Finite G]
    (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (hodd : AltEvenExcluded)
    (X T P K : Subgroup G) (hX : CharTwo X) (hT : IsSylowTwoOf T X)
    (hSQ : CFSG.SectionRank.IsSQTKCat ↥X) (hP : P ∈ uFamHat X T) (hK : IsChi0Block P K)
    (hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hKJ : ⁅K, thompsonJ T⁆ = K) :
    ∃ L : Subgroup G, IsBlock2 X L ∧ K ≤ L ∧ blockU K ≤ blockU L ∧ blockU L ≤ VZ T X ∧
      (K = L ∨ ∃ m n : ℕ, Odd m ∧ Odd n ∧ 3 ≤ m ∧ 3 ≤ n ∧
        IsAltQuotient L (Subgroup.centralizer (VZ T X : Set G)) m ∧
        IsAltQuotient K (Subgroup.centralizer (VZ T X : Set G)) n) := by
  have S : Setting X T P K := ⟨hX, hT, hP.1.1, hP.1.2.1.le, hK.1⟩
  have hUV := S.blockU_le_VZ hKZ
  have hV : IsElemAbelian 2 (VZ T X) := S.hred.2.2.1
  have hne := Setting.commutator_VZ_ne_bot (X := X) hKZ
  exact S.exists_block_of_concl hSQ hodd hV hUV hK.2 (S.b113_concl h113 hSQ hV hUV hKJ hne)

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank in
private theorem burnsideA38b_exists_chiBlock {G : Type} [Group G] [Finite G]
    {C₁ C₂ : Subgroup G → Subgroup G}
    (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (hodd : AltEvenExcluded)
    (h123 : C123TwoStatement C₁ C₂) (hB42 : L238.AltBlockStatementJCat (G := G))
    {X T U K M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hC1 : C₁ T ≤ quasithinOmegaOneCenter T)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hU : U ∈ uFamHat X T) (hK : IsChi0Block U K) (hKJ : ⁅K, thompsonJ T⁆ = K)
    (hKM : ¬ K ≤ M) :
    ∃ L : Subgroup G, IsChiBlock X L ∧ ⁅L, thompsonJ T⁆ = L ∧ K ≤ L ∧ ¬ L ≤ M := by
  have hSQT : IsSQTKTC X :=
    C1GN.isSQTKTC_iff_sqtkGroup.mpr ⟨isStronglyQuasithin_iff.mp hSQ.1, hSQ.2⟩
  have hKX : K ≤ X := hK.1.2.1.trans hU.1.1
  have hKZ : ¬ K ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun hKC =>
    hKM ((le_inf hKX (hKC.trans (Subgroup.centralizer_le hC1))).trans (le_sup_left.trans hM))
  obtain ⟨L, hLblock, hKL, -, hULV, hcases⟩ :=
    burnsideA38b_c127ND h113 hodd X T U K hX hT hSQ hU hK hKZ hKJ
  rcases hcases with hKL' | ⟨m, n, hm, hn, hm3, hn3, hmL, hnK⟩
  · subst hKL'
    exact ⟨K, C1GN.isChiBlock_of_isChi0Block hLblock hK, hKJ, le_rfl, hKM⟩
  · have hnotKC : ¬ K ≤ Subgroup.centralizer (VZ T X : Set G) :=
      C1GN.not_le_of_isAltQuotient hnK hn3
    have hKLJ : K ≤ ⁅L, thompsonJ T⁆ :=
      calc K = ⁅K, thompsonJ T⁆ := hKJ.symm
        _ ≤ ⁅L, thompsonJ T⁆ := Subgroup.commutator_mono hKL le_rfl
    have hnotLJ : ¬ ⁅L, thompsonJ T⁆ ≤ Subgroup.centralizer (VZ T X : Set G) := fun h =>
      hnotKC (hKLJ.trans h)
    have hJT : thompsonJ T ≤ T := (C1GN.thompsonJ_le_baum T).trans (C1GN.baum_le T)
    have hJN : thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
      L238.le_normalizer_of_isAltQuotient hX h38 hT hLblock hULV hm hm3 hmL hKL
        (L238.not_isPGroup_two_of_isShort2 hK.1.1) hJT (hKJ.le.trans hKL)
    have hLchi : IsChiBlock X L := by
      rcases hB42 X T L hX hSQ hT hLblock hULV hJN hnotLJ ⟨m, hm, hm3, hmL⟩ with h | hexc
      · exact h
      · exact absurd (hKL.trans (C1GN.le_of_isExceptionalA7Block h123 hX hSQT h38 hT hM hLblock hexc))
          hKM
    have hNL : ⁅L, thompsonJ T⁆ ≤ L := C1GN.commutator_le_of_le_normalizer hJN
    have hLN : L ≤ Subgroup.normalizer ((⁅L, thompsonJ T⁆ : Subgroup G) : Set G) :=
      A3.le_normalizer_commutator_left L (thompsonJ T)
    have hEq : ⁅L, thompsonJ T⁆ = L :=
      C1GN.isShort2_eq_of_isAltQuotient hLblock.1 hm hm3 hmL hNL hLN hnotLJ
    exact ⟨L, hLchi, hEq, hKL, fun hLM => hKM (hKL.trans hLM)⟩

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank in
private theorem burnsideA38b_uFamHat_le {G : Type} [Group G] [Finite G]
    {C₁ C₂ : Subgroup G → Subgroup G} (h126 : C126Statement C₁ C₂)
    (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (hodd : AltEvenExcluded)
    (h123 : C123TwoStatement C₁ C₂) (hB42 : L238.AltBlockStatementJCat (G := G))
    {X T M U : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X)
    (hC1 : C₁ T ≤ quasithinOmegaOneCenter T)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hTM : T ≤ M) (hU : U ∈ uFamHat X T) :
    U ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
  by_cases hUM : U ≤ M
  · exact hUM.trans le_sup_left
  have hSQT : IsSQTKTC X :=
    C1GN.isSQTKTC_iff_sqtkGroup.mpr ⟨isStronglyQuasithin_iff.mp hSQ.1, hSQ.2⟩
  have hUX : U ≤ X := hU.1.1
  have hTU : T < U := hU.1.2.1
  have hTSyl : IsSylowTwoOf T U := C1GN.isSylowTwoOf_of_le hT hTU.le hUX
  have hUmin : IsMinParabolicOf U U := ⟨T, hTSyl, ⟨le_rfl, hTU, hU.1.2.2⟩, hU.2⟩
  have hUchar : CharTwo U := C1GN.charTwo_of_le hX hT hTU.le hUX
  rcases h126 U T (C1GN.IsSQTKTC.mono hUX hSQT) hTSyl hUchar hUmin with
    h1 | h2 | ⟨r, K, -, hK, -, hres, hperm, htrans⟩
  · exfalso
    apply hUM
    have hUC : U ≤ X ⊓ Subgroup.centralizer (C₁ T : Set G) :=
      le_inf hUX fun u hu => Subgroup.mem_centralizer_iff.2 fun c hc =>
        (Subgroup.mem_centralizer_iff.1 (h1 hc).2 u hu).symm
    exact (hUC.trans le_sup_left).trans hM
  · exfalso
    apply hUM
    exact ((le_inf hUX h2).trans le_sup_right).trans hM
  · have hUeq : U = T ⊔ twoResidual U := (sup_twoResidual_eq hTSyl).symm
    have hex : ∃ i₀, ¬ K i₀ ≤ M := by
      by_contra hall
      push Not at hall
      apply hUM
      calc U = T ⊔ twoResidual U := hUeq
        _ = T ⊔ ⨆ i, K i := by rw [hres]
        _ ≤ M := sup_le hTM (iSup_le hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hall : ∀ i, ¬ K i ≤ M := by
      intro i hi
      obtain ⟨t, ht, hconj⟩ := htrans i i₀
      exact hi₀ (hconj ▸ C1GN.conjSub_le_of_mem (hTM ht) hi)
    have hKle : ∀ i, K i ≤ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L := by
      intro i
      obtain ⟨L, hL, hLJ, hKL, hLM⟩ := burnsideA38b_exists_chiBlock h113 hodd h123 hB42 hX hSQ h38
        hT hC1 hM hU (hK i).1 (hK i).2 (hall i)
      exact hKL.trans (le_iSup₂_of_le L ⟨hL, hLJ, hLM⟩ le_rfl)
    calc U = T ⊔ twoResidual U := hUeq
      _ = T ⊔ ⨆ i, K i := by rw [hres]
      _ ≤ M ⊔ ⨆ L ∈ C1GN.chiBlocksOutside X T M, L :=
        sup_le (hTM.trans le_sup_left) (le_sup_of_le_right (iSup_le hKle))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank CFSG.LieType.BorelTits in
open scoped Pointwise in
private theorem burnsideA38b_c128_set {G : Type} [Group G] [Finite G] {C₁ C₂ : Subgroup G →
    Subgroup G}
    (hC : IsGNChoice C₁ C₂) (h126 : C126Statement C₁ C₂)
    (h113 : Bridge.AsB113With CFSG.SectionRank.IsKGroupCat) (hodd : AltEvenExcluded)
    (h123 : C123TwoStatement C₁ C₂) (hB42 : L238.AltBlockStatementJCat (G := G))
    {X T M : Subgroup G} (hX : CharTwo X) (hSQ : IsSQTKCat ↥X)
    (h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X)) (hT : IsSylowTwoOf T X) (hT0 : T ≠ ⊥)
    (hM : (X ⊓ Subgroup.centralizer (C₁ T : Set G)) ⊔ (X ⊓ Subgroup.normalizer (C₂ T : Set G)) ≤ M)
    (hMX : M ≤ X) :
    ∃ (r : ℕ) (L : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChiBlock X (L i) ∧ ⁅L i, thompsonJ T⁆ = L i ∧ ¬ L i ≤ M) ∧
      ∀ x ∈ X, ∃ m ∈ M, ∃ y : Fin r → G, (∀ i, y i ∈ L i) ∧ x = m * (List.ofFn y).prod := by
  classical
  have hSQT : IsSQTKTC X :=
    C1GN.isSQTKTC_iff_sqtkGroup.mpr ⟨isStronglyQuasithin_iff.mp hSQ.1, hSQ.2⟩
  obtain ⟨-, h1Z, -, -, hC₂B, hC₂char, -⟩ := hC.pair T hT.2.1 hT0
  have hC1 : C₁ T ≤ quasithinOmegaOneCenter T := h1Z
  have hNC₂ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₂ T : Set G) :=
    (normalizer_le_normalizer_baum T).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂B hC₂char)
  have hTM : T ≤ M := fun t ht =>
    hM (Subgroup.mem_sup_right ⟨hT.1 ht, hNC₂ (Subgroup.le_normalizer ht)⟩)
  have hNTM : X ⊓ Subgroup.normalizer (T : Set G) ≤ M := fun x hx =>
    hM (Subgroup.mem_sup_right ⟨hx.1, hNC₂ hx.2⟩)
  set 𝔊 : Set (Subgroup G) := C1GN.chiBlocksOutside X T M with h𝔊
  set G₀ : Subgroup G := ⨆ B : 𝔊, (B : Subgroup G) with hG₀
  have hBle : ∀ B ∈ 𝔊, B ≤ G₀ := fun B hB => le_iSup (fun B : 𝔊 => (B : Subgroup G)) ⟨B, hB⟩
  have hXle : X ≤ M ⊔ G₀ := by
    obtain ⟨-, -, hXeq⟩ := uHat_normal_and_eq_sup hT.1
    calc X = uHat X T ⊔ (X ⊓ Subgroup.normalizer (T : Set G)) := hXeq
      _ ≤ M ⊔ G₀ := by
        refine sup_le (iSup₂_le fun U hU => ?_) (hNTM.trans le_sup_left)
        exact (burnsideA38b_uFamHat_le h126 h113 hodd h123 hB42 hX hSQ h38 hT hC1 hM hTM hU).trans
          (sup_le_sup_left (iSup₂_le fun L hL => hBle L hL) M)
  have hconj : ∀ x ∈ X, ∀ g ∈ G₀, x * g * x⁻¹ ∈ G₀ := by
    intro x hx g hg
    refine Subgroup.iSup_induction (fun B : 𝔊 => (B : Subgroup G))
      (C := fun g => x * g * x⁻¹ ∈ G₀) hg (fun B b hb => ?_) (by simp) (fun g h hg hh => ?_)
    · have hmem := C1Pack.conj_mem_chiBlocksOutside hX hSQT hT hTM B.2 hx
      have hxb : x * b * x⁻¹ ∈ B.1.map (MulAut.conj x).toMonoidHom := ⟨b, hb, rfl⟩
      exact hBle _ hmem hxb
    · have := G₀.mul_mem hg hh
      simpa [mul_assoc] using this
  have hnorm : X ≤ Subgroup.normalizer (G₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj x hx g hg, fun hg => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ hg
    simpa [mul_assoc] using this
  have hset : ((M ⊔ G₀ : Subgroup G) : Set G) = (M : Set G) * (G₀ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right M G₀ (hMX.trans hnorm)
  have hXmul : ∀ x ∈ X, ∃ m ∈ M, ∃ g ∈ G₀, x = m * g := by
    intro x hx
    have : x ∈ ((M ⊔ G₀ : Subgroup G) : Set G) := hXle hx
    rw [hset] at this
    obtain ⟨m, hm, g, hg, rfl⟩ := this
    exact ⟨m, hm, g, hg, rfl⟩
  rcases Set.eq_empty_or_nonempty 𝔊 with h0 | ⟨A, hA⟩
  ·
    have hG₀bot : G₀ = ⊥ := by
      refine le_antisymm (iSup_le fun B => ?_) bot_le
      have hB' : (B : Subgroup G) ∈ 𝔊 := B.2
      exact absurd hB' (Set.eq_empty_iff_forall_notMem.mp h0 _)
    refine ⟨0, Fin.elim0, Nat.zero_le _, fun i => i.elim0, fun x hx => ?_⟩
    obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
    rw [hG₀bot, Subgroup.mem_bot] at hg
    exact ⟨m, hm, Fin.elim0, fun i => i.elim0, by simp [hg]⟩
  · by_cases hB : ∃ B ∈ 𝔊, B ≠ A
    · obtain ⟨B, hB𝔊, hBA⟩ := hB
      have hall : ∀ C ∈ 𝔊, C = A ∨ C = B := fun C hC' => by
        rcases C1Pack.chiBlocks_eq_of_three hX hSQT hA.1 hB𝔊.1 hC'.1 with h | h | h
        · exact absurd h.symm hBA
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      have hG₀eq : G₀ = A ⊔ B := by
        refine le_antisymm (iSup_le fun C => ?_) (sup_le (hBle A hA) (hBle B hB𝔊))
        rcases hall C.1 C.2 with h | h
        · rw [h]
          exact le_sup_left
        · rw [h]
          exact le_sup_right
      have hcomm : ⁅A, B⁆ = ⊥ := distinctBlocksCommuteStatement X A B hX hA.1.1 hB𝔊.1.1 hBA.symm
      have hAN : A ≤ Subgroup.normalizer (B : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
          (Subgroup.centralizer_le_normalizer _)
      have hABset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right A B hAN
      refine ⟨2, ![A, B], le_rfl, fun i => ?_, fun x hx => ?_⟩
      · fin_cases i
        · exact hA
        · exact hB𝔊
      · obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
        rw [hG₀eq] at hg
        have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
        rw [hABset] at hg'
        obtain ⟨a, ha, b, hb, rfl⟩ := hg'
        refine ⟨m, hm, ![a, b], fun i => ?_, ?_⟩
        · fin_cases i
          · exact ha
          · exact hb
        · simp [List.ofFn_succ]
    · push Not at hB
      have hG₀eq : G₀ = A := by
        refine le_antisymm (iSup_le fun C => (hB C.1 C.2).le) (hBle A hA)
      refine ⟨1, fun _ => A, by norm_num, fun _ => hA, fun x hx => ?_⟩
      obtain ⟨m, hm, g, hg, rfl⟩ := hXmul x hx
      rw [hG₀eq] at hg
      exact ⟨m, hm, fun _ => g, fun _ => hg, by simp⟩

private theorem burnsideA38b_chiBlock2 {G : Type} [Group G] {X L : Subgroup G}
    (h : CFSG.Quasithin.IsChiBlock X L) : CFSG.Quasithin.IsChiBlock2 X L :=
  ⟨h.1, h.2.imp id fun ⟨m, hm, _, hA⟩ => ⟨m, hm, hA⟩⟩

end BurnsideA38b

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank in
open scoped Pointwise in
theorem as_C_1_28
    : C_1_28 := by
  intro Ω _ _ C₁ C₂ hGN X T hX hSQ hT
  have hSQc : IsSQTKCat ↥X := ⟨isStronglyQuasithin_iff.mpr hSQ.1, hSQ.2⟩
  have hM₀X : (X ⊓ Subgroup.centralizer (C₁ T : Set Ω)) ⊔
      (X ⊓ Subgroup.normalizer (C₂ T : Set Ω)) ≤ X :=
    sup_le inf_le_left inf_le_left
  by_cases hT0 : T = ⊥
  ·
    left
    refine le_antisymm (fun h hh => ?_) hM₀X
    have hO : pCoreOf 2 X ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
    rw [hT0, le_bot_iff] at hO
    have hmem : h ∈ X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set Ω) := by
      refine ⟨hh, ?_⟩
      rw [hO]
      exact Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [show g = 1 from by simpa using hg]
        simp
    have h2 := hX hmem
    rw [hO] at h2
    have h1 : h = 1 := by simpa using h2
    rw [h1]
    exact Subgroup.one_mem _
  · have h38 : A38Part3 (↥X ⧸ CFSG.pCore 2 ↥X) :=
      CFSG.Quasithin.H13.A7.a38ForSQTKCat_holds (↥X ⧸ CFSG.pCore 2 ↥X)
        (Vol2Native.SQTKHypCat.quotient_pCore ↥X hSQc)
    obtain ⟨r, L, hr, hL, hprod⟩ := burnsideA38b_c128_set hGN
      (theoremC126_proved Ω C₁ C₂ hGN)
      (Bridge.asB113_of_timmesfeld CFSG.Quasithin.B15P4.asB15Part4) L246C127.altEvenExcluded
      (L246.C123.theoremC123Two_holds Ω C₁ C₂ hGN) L238.altBlockStatementJCat_holds hX hSQc h38 hT
      hT0 le_rfl hM₀X
    have hLX : ∀ i, L i ≤ X := fun i => (hL i).1.1.2.1
    interval_cases r
    · left
      refine le_antisymm (fun x hx => ?_) hM₀X
      obtain ⟨m, hm, y, -, hxm⟩ := hprod x hx
      have hp : (List.ofFn y).prod = 1 := by simp
      rw [hp, mul_one] at hxm
      rw [hxm]
      exact hm
    · right
      left
      refine ⟨L 0, burnsideA38b_chiBlock2 (hL 0).1, (hL 0).2.1, ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨m, hm, y, hy, hxm⟩ := hprod x hx
        have hp : (List.ofFn y).prod = y 0 := by simp
        rw [hp] at hxm
        exact Set.mem_mul.2 ⟨m, hm, y 0, hy 0, hxm.symm⟩
      · intro hx
        obtain ⟨m, hm, l, hl, rfl⟩ := Set.mem_mul.1 hx
        exact X.mul_mem (hM₀X hm) (hLX 0 hl)
    · right
      right
      refine ⟨L 0, L 1, burnsideA38b_chiBlock2 (hL 0).1, (hL 0).2.1, burnsideA38b_chiBlock2 (hL 1).1,
        (hL 1).2.1, ?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨m, hm, y, hy, hxm⟩ := hprod x hx
        have hp : (List.ofFn y).prod = y 0 * y 1 := by simp [List.ofFn_succ]
        rw [hp] at hxm
        exact Set.mem_mul.2 ⟨m * y 0, Set.mem_mul.2 ⟨m, hm, y 0, hy 0, rfl⟩, y 1, hy 1,
          by rw [hxm, mul_assoc]⟩
      · intro hx
        obtain ⟨a, ha, l₂, hl₂, rfl⟩ := Set.mem_mul.1 hx
        obtain ⟨m, hm, l₁, hl₁, rfl⟩ := Set.mem_mul.1 ha
        exact X.mul_mem (X.mul_mem (hM₀X hm) (hLX 0 hl₁)) (hLX 1 hl₂)

end

@[expose] def C_1_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T M : Subgroup G),
    CharTwo X → IsSylowTwoOf T X → IsSQTKIn X → cgsIn X T ≤ M → M ≤ X →
    (X = M ∨
    (∃ L₁ : Subgroup G, IsChi0Block X L₁ ∧ IsBorelOfBlock L₁ (L₁ ⊓ M) ∧
      ⁅L₁, thompsonJ T⁆ = L₁ ∧ (X : Set G) = (M : Set G) * (L₁ : Set G)) ∨
    (∃ L₁ L₂ : Subgroup G, IsChi0Block X L₁ ∧ IsBorelOfBlock L₁ (L₁ ⊓ M) ∧
      ⁅L₁, thompsonJ T⁆ = L₁ ∧ IsChi0Block X L₂ ∧ IsBorelOfBlock L₂ (L₂ ⊓ M) ∧
      ⁅L₂, thompsonJ T⁆ = L₂ ∧ (X : Set G) = (M : Set G) * (L₁ : Set G) * (L₂ : Set G)))

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_1_29
    : C_1_29 := by
  intro G _ _ X T M hC hT hS hcgs hMX
  obtain ⟨r, Lb, hr, hLb, hcov⟩ :=
    CFSG.Quasithin.H13.VolI.asc129Statement_holds G X T M hS hC hT hcgs hMX
  have hLX : ∀ i, Lb i ≤ X := fun i => (hLb i).1.1.2.1
  interval_cases r
  · left
    refine le_antisymm ?_ hMX
    intro h hh
    obtain ⟨m, hm, x, -, hxm⟩ := hcov h hh
    have hp : (List.ofFn x).prod = 1 := by simp
    rw [hp, mul_one] at hxm
    rw [hxm]
    exact hm
  · right; left
    refine ⟨Lb 0, (hLb 0).1, (hLb 0).2.1, (hLb 0).2.2, ?_⟩
    ext h
    constructor
    · intro hh
      obtain ⟨m, hm, x, hx, hxm⟩ := hcov h hh
      have hp : (List.ofFn x).prod = x 0 := by simp
      rw [hp] at hxm
      exact Set.mem_mul.2 ⟨m, hm, x 0, hx 0, hxm.symm⟩
    · intro hh
      obtain ⟨m, hm, l, hl, rfl⟩ := Set.mem_mul.1 hh
      exact X.mul_mem (hMX hm) (hLX 0 hl)
  · right; right
    refine ⟨Lb 0, Lb 1, (hLb 0).1, (hLb 0).2.1, (hLb 0).2.2, (hLb 1).1, (hLb 1).2.1,
      (hLb 1).2.2, ?_⟩
    ext h
    constructor
    · intro hh
      obtain ⟨m, hm, x, hx, hxm⟩ := hcov h hh
      have hp : (List.ofFn x).prod = x 0 * x 1 := by simp [List.ofFn_succ]
      rw [hp] at hxm
      exact Set.mem_mul.2 ⟨m * x 0, Set.mem_mul.2 ⟨m, hm, x 0, hx 0, rfl⟩, x 1, hx 1,
        by rw [hxm, mul_assoc]⟩
    · intro hh
      obtain ⟨a, ha, l₂, hl₂, rfl⟩ := Set.mem_mul.1 hh
      obtain ⟨m, hm, l₁, hl₁, rfl⟩ := Set.mem_mul.1 ha
      exact X.mul_mem (X.mul_mem (hMX hm) (hLX 0 hl₁)) (hLX 1 hl₂)

end

@[expose] def C_1_35 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R L S : Subgroup G) (n : ℕ),
    IsMSPairWith X R L → IsSylowTwoOf S X →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F)) →
    X ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) 3 →
    ((∃ a b : ℕ, IsSpecial2Group a b ↥(pCoreOf 2 L)) ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        ∃ (W₁ W₂ : Subgroup G) (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F)
          (βU : ↥(centerOf (pCoreOf 2 L)) →* Multiplicative (Fin 3 → F))
          (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)) (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)),
          DualSplit L (centerOf (pCoreOf 2 L)) W₁ W₂ α βU β₁ β₂) ∧
    (∀ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n →
      ∀ (W₁ W₂ : Subgroup G) (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F)
        (βU : ↥(centerOf (pCoreOf 2 L)) →* Multiplicative (Fin 3 → F))
        (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)) (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)),
        DualSplit L (centerOf (pCoreOf 2 L)) W₁ W₂ α βU β₁ β₂ →
        IsE2 (6 * n) ↥W₁ ∧ IsE2 (6 * n) ↥W₂ ∧
        ∀ w : ↥W₁, (w : G) ∉ centerOf (pCoreOf 2 L) →
          W₁.relIndex (pCoreOf 2 L ⊓ Subgroup.centralizer ({(w : G)} : Set G)) = 2 ^ n ∧
          ∀ v : Fin 3 → F,
            (∃ x : ↥W₂, (x : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) ∧
              Multiplicative.toAdd (β₂ x) = v) ↔
            ∃ c : F, v = c • Multiplicative.toAdd (β₁ w)) ∧
    pCoreOf 2 X = pCoreOf 2 L ∧
    (∃ A : Subgroup G, IsMaxElemAbelian X A ∧ Nat.card ↥A = 2 ^ (6 * n)) ∧
    (Subgroup.upperCentralSeries ↥S 2).map S.subtype ≤ centerOf (pCoreOf 2 L)

@[expose] def C_1_36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R L S : Subgroup G) (n : ℕ),
    IsMSPairWith X R L → IsSylowTwoOf S X →
    (∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F)) →
    X ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) 2 →
    X ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L ∧
    ∃ A : Subgroup G, A ≤ L ∧ {B : Subgroup G | IsMaxElemAbelian S B} = {pCoreOf 2 L, A} ∧
      Nat.card ↥(A ⊓ pCoreOf 2 L) = 2 ^ (4 * n)

@[expose] def C_1_37 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X T L P M V : Subgroup G),
    (X : Set G) = (L : Set G) * (T : Set G) → IsSylowTwoOf T X → L ∈ cComp X → CharTwo X →
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∨
      IsPSU 3 3 1 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    TrivialOnDynkin L T →
    T ≤ P → P ≤ M → IsMaxSubgroupIn X M →
    (P = M ∨ (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∧ P.relIndex M = 3 ∧
      ¬ oTwoUpper P ≤ oTwoZIn L)) →
    IsTwoReducedIn X V → ⁅V, L⁆ ≠ ⊥ →
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) →
      (∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (U₁ U₂ : Subgroup G)
          (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
          (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)), SumOfTwoNat L ⁅V, L⁆ α U₁ U₂ β₁ β₂) ∨
      ((∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
          (β : ↥⁅V, L⁆ →* Multiplicative (Fin 3 → ZMod 2)),
          Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧ IsNatVia L ⁅V, L⁆ ⊥ α β) ∧
        ∃ u ∈ ⁅V, L⁆, u ≠ 1 ∧ P = X ⊓ Subgroup.centralizer ({u} : Set G))) →
    ((∃ D : Subgroup G, D ≠ ⊥ ∧ D ≤ baum (pCoreOf 2 P) ∧
        (D.subgroupOf (baum (pCoreOf 2 P))).Characteristic ∧
        X ≤ Subgroup.normalizer (D : Set G)) ∨
    ((IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsHatA6Block L ∨ IsG2TwoBlockNatural L) ∧
      (IsHatA6Block L → ∃ E : Subgroup G, E ≤ ⁅V, L⁆ ∧ IsE2 4 ↥E ∧
        autOn M V = autOn (X ⊓ Subgroup.normalizer (E : Set G)) V)) ∨
    (IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ⁅V, L⁆ = ⁅pCoreOf 2 L, L⁆ ∧
      ∃ (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (U₁ U₂ : Subgroup G)
        (β₁ : ↥U₁ →* Multiplicative (Fin 3 → ZMod 2))
        (β₂ : ↥U₂ →* Multiplicative (Fin 3 → ZMod 2)),
        SumOfTwoNat L ⁅V, L⁆ α U₁ U₂ β₁ β₂ ∧
        ∃ (ℓ : Submodule (ZMod 2) (Fin 3 → ZMod 2))
          (coordinates : ∀ I : {I : Subgroup G // I ∈ internalIrrPlus L ⁅V, L⁆},
            ↥I.val →* Multiplicative (Fin 3 → ZMod 2)),
          Module.finrank (ZMod 2) ℓ = 2 ∧
          (∀ I, IsNatVia L I.val ⊥ α (coordinates I)) ∧
          P = X ⊓ ⨅ I : {I : Subgroup G // I ∈ internalIrrPlus L ⁅V, L⁆},
            Subgroup.normalizer (preimageIn I.val (coordinates I) ℓ : Set G)) ∨
    (IsG2Two ↥(autOn X V) ∧
      InternalG2TwoNatural X V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ∧
      (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, L⁆ = 2 ^ 6 ∧
      IsIrrSection X (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ⁅V, L⁆ ∧
      ∃ l : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
        (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex l = 4 ∧
        P = X ⊓ Subgroup.normalizer (l : Set G)) ∨
    (Nonempty (↥(autOn X V) ≃* Equiv.Perm (Fin 6)) ∧
      InternalS6Natural X V ⁅V, L⁆ (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ∧
      (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex ⁅V, L⁆ = 2 ^ 4 ∧
      IsIrrSection X (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)) ⁅V, L⁆ ∧
      (∃ l : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ l ∧ l ≤ ⁅V, L⁆ ∧
        (⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G)).relIndex l = 4 ∧
        autOn P V = autOn (X ⊓ Subgroup.normalizer (l : Set G)) V) ∧
      (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) →
        ¬ oTwoUpper (oTwoZIn L) ≤ P) ∧
      ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V)))

end CFSG.ASVolI
