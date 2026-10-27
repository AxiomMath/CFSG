module

public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146F10
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F9
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def AllComps24 (T M : Subgroup G) : Prop :=
  ∀ L ∈ cComp (mcOf T), Conc14621 T L ∧ Conc14622 T M L

@[expose] def Full24 (T M K U₁ U₂ : Subgroup G) (s u : G) (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T))
    (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)) : Prop :=
  Ctx24 T M K U₁ U₂ s u ∧ AllComps24 T M ∧ Geom24 T M γ γ' g

structure Comps24 (T M K Kp : Subgroup G) : Prop where
  mem : Kp ∈ cComp (mcOf T)
  ne : Kp ≠ K
  comps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp
  kz : perfectCore (mcOf T) = K ⊔ Kp
  l3 : KbarIsL3Two K ∧ KbarIsL3Two Kp
  rank : mIdx (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 6 ∧
    mIdx (⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 6

@[expose] def Norm24 (T M K Kp : Subgroup G) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)) : Prop :=
  F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (K : Set G) ∧
    F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ Subgroup.normalizer (Kp : Set G) ∧
    (K ≤ ⁅K, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ⊔ pCoreOf 2 (mcOf T) ∨
      Kp ≤ ⁅Kp, F8.Uγ (VZ T M) (mcOf T) (g : G)⁆ ⊔ pCoreOf 2 (mcOf T))

@[expose] def Claim24 (T M K Kp : Subgroup G) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)) : Prop :=
  F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T ∨
    F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ ⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T

end Defs

@[expose] def Input14624U1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) ∧
        (tZero T u).relIndex T = 2

@[expose] def Input14624U3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      Subgroup.normalizer (tZero T u : Set G) ⊓ mcOf T = T

@[expose] def Input14624U2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      u ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ∧
        ∀ t ∈ T, t ∉ tZero T u →
          u * (t * u * t⁻¹) ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)

@[expose] def Input14624ThreeA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u → AllComps24 T M →
      K ≠ perfectCore (mcOf T) → ∃ Kp : Subgroup G, Comps24 T M K Kp

@[expose] def Input14624ThreeB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → ∀ Kp : Subgroup G, Comps24 T M K Kp → Norm24 T M K Kp g

@[expose] def Input14624ThreeC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → ∀ Kp : Subgroup G, Comps24 T M K Kp → Norm24 T M K Kp g →
        Claim24 T M K Kp g

@[expose] def Input14624ThreeD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → ∀ Kp : Subgroup G, Comps24 T M K Kp → Norm24 T M K Kp g →
        Claim24 T M K Kp g → False

@[expose] def Input14624NotTwoGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u →
      K = perfectCore (mcOf T) → KbarIsL3Two K → IsInvU T M (mcOf T) u →
        ¬ IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ({u} : Set G))

@[expose] def Input14624FourRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → K = perfectCore (mcOf T) → KbarIsL3Two K →
        mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) ≤ 2

@[expose] def Input14624FourA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → K = perfectCore (mcOf T) → KbarIsL3Two K →
        IsInvU T M (mcOf T) u →
          mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
            (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 1 →
            ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T

@[expose] def Input14624FourB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G)
      (γ γ' : F8.Geom T (yOfL22 T M) (mcOf T)) (g : ↥(((yOfL22 T M) ⊔ T) ⊔ mcOf T)),
      Full24 T M K U₁ U₂ s u γ γ' g → K = perfectCore (mcOf T) → KbarIsL3Two K →
        IsInvU T M (mcOf T) u →
          mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
            (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 2 →
            ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T

section Steps

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem Ctx24.mem_U {K U₁ U₂ : Subgroup G} {s u : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) (hch : IsChoiceU T M K U₁ u) :
    u ∈ conjClosure (VZ T M) (mcOf T) := by
  have hKN : K ≤ Subgroup.normalizer ((conjClosure (VZ T M) (mcOf T) : Subgroup G) : Set G) :=
    (le_of_mem_cComp hK).trans (le_normalizer_conjClosure _ _)
  have hcomm : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) := by
    rw [Subgroup.commutator_le]
    intro x hx k hk
    have h1 : k * x⁻¹ * k⁻¹ ∈ conjClosure (VZ T M) (mcOf T) :=
      (Subgroup.mem_normalizer_iff.mp (hKN hk) x⁻¹).mp ((conjClosure (VZ T M) (mcOf T)).inv_mem hx)
    have e : ⁅x, k⁆ = x * (k * x⁻¹ * k⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (conjClosure (VZ T M) (mcOf T)).mul_mem hx h1
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) := fun z hz =>
    Z_le_conjClosure_VZ T M (mcOf T) hz
  have hle : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) :=
    sup_le hcomm hZU
  have hu : u ∈ ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T := by
    rcases hch with ⟨-, hu1, -⟩ | ⟨-, hu2, -⟩
    · rw [hdec.sup]
      exact Subgroup.mem_sup_left hu1
    · exact Subgroup.mem_sup_left hu2
  exact hle hu

omit [Finite G] in
theorem IsChoiceU.not_mem_Z {K U₁ : Subgroup G} {u : G} (hK : K ≤ mcOf T)
    (hch : IsChoiceU T M K U₁ u) : u ∉ quasithinOmegaOneCenter T := by
  rcases hch with ⟨-, -, hnc, -⟩ | ⟨-, -, huZ, -⟩
  · intro huZ
    apply hnc
    rw [Subgroup.commutator_le]
    intro x hx k hk
    have hxZ : x ∈ quasithinOmegaOneCenter T := (Subgroup.zpowers_le.mpr huZ) hx
    have hc : k * x = x * k := S146T.comm_Z (hK hk) hxZ
    have : ⁅x, k⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [← hc]
      group
    rw [this]
    exact Subgroup.one_mem _
  · exact huZ

omit [Finite G] in
theorem isInvU24_of_parts {K U₁ U₂ : Subgroup G} {s u : G}
    (hK : K ∈ cComp (mcOf T)) (hdec : IsDecompUK T M K U₁ U₂ s) (hch : IsChoiceU T M K U₁ u)
    (h1 : IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) ∧
      (tZero T u).relIndex T = 2)
    (h3 : Subgroup.normalizer (tZero T u : Set G) ⊓ mcOf T = T)
    (h2 : u ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ∧
      ∀ t ∈ T, t ∉ tZero T u →
        u * (t * u * t⁻¹) ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)) :
    IsInvU T M (mcOf T) u :=
  ⟨Ctx24.mem_U hK hdec hch, h1.1, h1.2, h2.1, h2.2, h3⟩

theorem isI24_of_parts {K : Subgroup G} {u : G} (S : Setting146 G T M) (c23 : Conc14623 T M)
    (hKG : K ≤ mcOf T) (huU : u ∈ conjClosure (VZ T M) (mcOf T))
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (hnot2 : ¬ IsPGroup 2 ↥(K ⊓ Subgroup.centralizer ({u} : Set G)))
    (hG : ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T) :
    IsI T M u (Subgroup.centralizer ({u} : Set G)) := by
  have hH : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTG : T ≤ mcOf T := hH.1.1
  have hu2 : u ^ 2 = 1 := isElemAbelian_pow_eq_one (S.lemma_14_5_15_two hH) huU
  have hu1 : u ≠ 1 := fun h => huZ (h ▸ (quasithinOmegaOneCenter T).one_mem)
  have huC : u ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
  refine ⟨⟨inf_le_right, ?_⟩, hG, ?_⟩
  · intro hbot
    apply hu1
    have hp2 : IsPGroup 2 ↥(Subgroup.zpowers u) := by
      intro x
      refine ⟨1, Subtype.ext ?_⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
      have h1 : ((x : G)) ^ 2 = 1 := by
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu2, one_zpow]
      simpa using h1
    have hmem : u ∈ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 (Subgroup.zpowers_le.mpr huC)
        (centralizer_le_normalizer_zpowers' u) hp2 (Subgroup.mem_zpowers u)
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · intro hle
    apply hnot2
    have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTG
    have hKT : K ⊓ Subgroup.centralizer ({u} : Set G) ≤ T := by
      rw [c23.2.1.2]
      exact le_inf (inf_le_right.trans hle) (inf_le_left.trans hKG)
    exact hTsyl.isPGroup.to_le hKT

end Steps

theorem stage14624_of_fine_inputs (h21 : Stage14621) (h22 : Stage14622)
    (iU1 : Input14624U1) (iU3 : Input14624U3) (iU2 : Input14624U2) (iG : Input14624Geom)
    (i3A : Input14624ThreeA) (i3B : Input14624ThreeB) (i3C : Input14624ThreeC)
    (i3D : Input14624ThreeD) (i2 : Input14624Two) (iNT : Input14624NotTwoGroup)
    (iRk : Input14624FourRank) (i4A : Input14624FourA) (i4B : Input14624FourB) :
    Stage14624 := by
  intro G _ _ T M S hB c19 c20 c23 K hK c21 c22 U₁ U₂ s hdec u hu
  have hctx : Ctx24 T M K U₁ U₂ s u := ⟨c19, c20, c23, hK, c21, c22, hdec, hu⟩
  have hall : AllComps24 T M := fun L hL =>
    ⟨h21 G T M S hB c19 c20 L hL, h22 G T M S hB c19 c20 L hL (h21 G T M S hB c19 c20 L hL)⟩
  obtain ⟨γ, γ', g, hgeom⟩ := iG G T M S hB K U₁ U₂ s u hctx
  have hfull : Full24 T M K U₁ U₂ s u γ γ' g := ⟨hctx, hall, hgeom⟩
  have hinv : IsInvU T M (mcOf T) u :=
    isInvU24_of_parts hK hdec hu (iU1 G T M S hB K U₁ U₂ s u hctx)
      (iU3 G T M S hB K U₁ U₂ s u hctx) (iU2 G T M S hB K U₁ U₂ s u hctx)
  have h3 : K = perfectCore (mcOf T) := by
    by_contra hne
    obtain ⟨Kp, hC⟩ := i3A G T M S hB K U₁ U₂ s u hctx hall hne
    have hN := i3B G T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC
    have hCl := i3C G T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hN
    exact i3D G T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC hN hCl
  have h2 : KbarIsL3Two K := i2 G T M S hB K U₁ U₂ s u hctx γ γ' g hgeom h3
  have hG1 : ¬ Subgroup.centralizer ({u} : Set G) ≤ mcOf T := by
    have hrk := iRk G T M S hB K U₁ U₂ s u γ γ' g hfull h3 h2
    have hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) :=
      lt_of_lt_of_le hgeom.2.2.1 hgeom.2.2.2.1
    rcases (by omega : mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
        (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 1 ∨
        mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
          (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) = 2) with h1 | h1
    · exact i4A G T M S hB K U₁ U₂ s u γ γ' g hfull h3 h2 hinv h1
    · exact i4B G T M S hB K U₁ U₂ s u γ γ' g hfull h3 h2 hinv h1
  have hnot2 := iNT G T M S hB K U₁ U₂ s u hctx h3 h2 hinv
  exact ⟨hinv, h2, h3,
    isI24_of_parts S c23 (le_of_mem_cComp hK) hinv.mem (IsChoiceU.not_mem_Z (le_of_mem_cComp hK) hu)
      hnot2 hG1⟩

end CFSG.Quasithin
