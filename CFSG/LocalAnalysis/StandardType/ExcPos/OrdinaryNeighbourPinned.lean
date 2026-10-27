module

public import CFSG.LocalAnalysis.StandardType.ExcPos.OrdinaryNeighbour
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
import CFSG.Assembly.Subnormal
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization
import CFSG.LieType.Simplicity.ExceptionalConverse
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamField
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentOrbit
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentPacket
import CFSG.LocalAnalysis.StandardType.ExcPos.NeighbourComponentSelect
import CFSG.LocalAnalysis.StandardType.ExcPos.PacketBasic
import CFSG.LocalAnalysis.StandardType.ExcPos.TwistedE6Factors
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.StandardType.GGJ4dKernel24
import CFSG.LocalAnalysis.StandardType.GGLangExhaust
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCGroup
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCRootGroupTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCompPairIncidence
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCStdEnvelope
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassical
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputs
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveCover

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

theorem map_subgroupOf_comp_inclusion {X Y : Type*} [Group X] [Group Y] {G₀ K R : Subgroup X}
    (η : ↥G₀ →* Y) (hKG : K ≤ G₀) (hRK : R ≤ K) :
    (R.subgroupOf K).map (η.comp (Subgroup.inclusion hKG)) = (R.subgroupOf G₀).map η := by
  have h : R.subgroupOf G₀ ≤ K.subgroupOf G₀ := Subgroup.comap_mono hRK
  rw [← Subgroup.map_map, ← Subgroup.comap_inclusion_subgroupOf hKG R, Subgroup.map_comap_eq,
    Subgroup.inclusion_range, inf_eq_right.2 h]

theorem eq_map_of_map_eq_of_isPGroup {X Y U : Type*} [Group X] [Group Y] [Group U]
    {K : Subgroup X} [Finite ↥K] (c : ↥K →* Y) (hcen : c.ker ≤ Subgroup.center ↥K)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) (α : U →* ↥K) {H : Subgroup U}
    (hH : IsPGroup 2 H) {R : Subgroup X} (hRK : R ≤ K) (hR : IsPGroup 2 R)
    (h : (R.subgroupOf K).map c = H.map (c.comp α)) : R = H.map (K.subtype.comp α) := by
  have hT : IsPGroup 2 (R.subgroupOf K) := IsPGroup.comap_subtype hR
  have hT' : IsPGroup 2 (H.map α) := hH.map α
  have hodd' : Odd (Nat.card c.ker) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hcen)
  have heq : R.subgroupOf K = H.map α := by
    refine RCKRP.rck_rootUnique c hcen hodd' _ _ hT hT' ?_
    rwa [← Subgroup.map_map] at h
  rw [← Subgroup.map_subgroupOf_eq_of_le hRK, heq, Subgroup.map_map]

theorem eq_of_ratOrbit_eq_of_componentOrbitLength_eq_one {τ : Tag} {N : Type*} [CommGroup N]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* N} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {i j : KernelComponent χ} (hj : componentOrbitLength ρ (componentRoots χ j) = 1)
    (h : LieCore.ratOrbit ρ (componentRoots χ i) = LieCore.ratOrbit ρ (componentRoots χ j)) :
    i = j := by
  have hmaps : Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (componentRoots χ j)
      (componentRoots χ j) :=
    Set.mapsTo_iff_image_subset.2 (LangRat.j4d_image_eq_of_componentOrbitLength_eq_one hj).le
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
  have hαi : α ∈ componentRoots χ (⟦⟨α, hα⟩⟧ : KernelComponent χ) := ⟨hα, rfl⟩
  obtain ⟨k, δ, hδ, rfl⟩ : α ∈ LieCore.ratOrbit ρ (componentRoots χ j) := by
    rw [← h]
    exact ⟨0, α, hαi, rfl⟩
  exact eq_of_mem_componentRoots hαi (hmaps.iterate k hδ)

theorem ExcPacket.q_facts
    {X : Type} [Group X] {τ : Tag} {f p : ℕ} {G₀ B₁ D J : Subgroup X} {x : X}
    {R Rm : Subgroup X} (P : ExcPacket τ f p G₀ B₁ D J x R Rm) :
    P.Δ.q = 2 ^ f ∧ IsPrimePow P.Δ.q ∧ ((P.Δ.q : ℕ) : ExcOmega f) = 0 ∧ ¬ 5 ∣ P.Δ.q := by
  have hf : f ≠ 0 := Nat.ne_of_gt P.one_le_f
  have hq : P.Δ.q = 2 ^ f := P.hq.trans (GaloisField.card 2 f hf)
  refine ⟨hq, hq ▸ Nat.prime_two.isPrimePow.pow hf, ?_, fun h5 => ?_⟩
  · rw [hq]
    exact (CharP.cast_eq_zero_iff (ExcOmega f) 2 _).2 (dvd_pow_self 2 hf)
  · rw [hq] at h5
    have := Nat.prime_five.dvd_of_dvd_pow h5
    omega

theorem ExcPacket.rootDiagUnit_coord_ne_one_of_component
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X} (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    {R Rm : Subgroup X} (P : ExcPacket (GGFinModel.langTag t) f p G₀ B₁ D J x R Rm)
    {e : X} (he : e ∈ D) {K : Subgroup X} (hKG : K ≤ G₀)
    (hKc : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e})) (hKG₀ : K ≠ G₀) :
    rootDiagUnit (GGFinModel.langTag t) (P.coord e) ≠ 1 := by
  intro hΘ1
  obtain ⟨-, -, hDB, -⟩ := ggSixPosHyp_excUK_facts hH
  have heCent : e ∈ Subgroup.centralizer (G₀ : Set X) := by
    refine (P.Θ_eq_one ⟨e, hDB he⟩).1 ?_
    rw [P.Θ_eq_coord ⟨e, hDB he⟩ he, hΘ1]
  have hpos : GGPosTag t := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGPosTag]
  have hUperf : commutator (ggU t n f).K = ⊤ :=
    RCKK1I.rckK1I_ggU_perfect hpos hH.2.2.1.admissible
  have hrangePerf : commutator ↥ψ.range = ⊤ :=
    Group.isPerfect_def.mp
      (@Group.IsPerfect.ofSurjective (ggU t n f).K ↥ψ.range _ _
        (MonoidHom.rangeRestrict ψ) (Group.isPerfect_def.mpr hUperf)
        (MonoidHom.rangeRestrict_surjective ψ))
  have hG0perf : commutator ↥G₀ = ⊤ := by
    rwa [hH.1] at hrangePerf
  have hChev : t ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [CFSG.Blueprint.chevalleyExceptionalTags]
  have hG0simple : IsSimpleGroup (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    (CFSG.LieType.Simplicity.fam_chevalley_exceptional_simplicity
      (↥G₀ ⧸ Subgroup.center ↥G₀) t 2 f
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hH.2.2.1 hChev)).2
  have hG₀c : G₀ ≤ Subgroup.centralizer {e} := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 heCent g hg)
  exact hKG₀ (GGHalf.eq_of_isComponentOf_isQuasisimple ⟨hG0perf, hG0simple⟩
    (hKc.of_le_of_le hKG hG₀c))

theorem isPGroup_two_of_ggRootPosG0
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    {X : Type} [Group X] [Finite X] {n f : ℕ} {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ B₁ D J L : Subgroup X} {x : X} (hH : GGSixPosHyp t n f ψ p G₀ B₁ D J L x)
    {R Rm : Subgroup X} (hpos : GGRootPosG0 t n f p ψ R Rm) :
    IsPGroup 2 R ∧ IsPGroup 2 Rm := by
  obtain ⟨β, hβ, -, u, hR, hRm⟩ := hpos
  have htag : GGPosTag t := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGPosTag]
  have hstd : StandardReturnAt (ggU t n f) f :=
    Or.inl ⟨t, n, htag, hH.2.2.1.admissible, rfl⟩
  have hβ2 : IsPGroup 2 ((ggU t n f).D.rootGroup β) :=
    RCKRP.rckRootGroupTwo_holds (ggU t n f) f hstd β hβ
  have hβ2' : IsPGroup 2 ((ggU t n f).D.rootGroup (-β)) :=
    RCKRP.rckRootGroupTwo_holds (ggU t n f) f hstd (-β)
      (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (hA := (ggU t n f).D.isFiniteType)
        (D := (ggU t n f).D.divisible) hβ)
  constructor
  · rw [hR]
    exact (hβ2.map (MulAut.conj u).toMonoidHom).map ψ
  · rw [hRm]
    exact (hβ2'.map (MulAut.conj u).toMonoidHom).map ψ

section Model


theorem exists_ggLongRoot_of_rckADEModel {M : LieUniversal} {g : ℕ} (h : RCKRP.RCKADEModel M g) :
    ∃ β ∈ M.D.roots, GGLongRoot M.D β := by
  have hpos : 0 < M.D.rank := by
    rcases h with ⟨t, n, htag, hadm, rfl⟩ | ⟨F, _, _, σ, _, rfl⟩
    · rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [StatedLieAdmissible] at hadm
        have hn : 2 ≤ n := hadm.2.2.1
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        change 0 < (lieUniversal .PSL (m + 1) 2 g Nat.prime_two).D.rank
        change 0 < m
        omega
      · simp only [StatedLieAdmissible] at hadm
        have hn : 3 ≤ n := hadm.2.2.1
        rw [ggU_PSU_rank n g hadm.2.1]
        omega
      · have hn : 4 ≤ n := by simpa only [StatedLieAdmissible] using hadm.2.2
        have h3 : 3 ≤ bnRank .POmegaPlus n := by
          simp only [bnRank]
          omega
        rw [lieUniversal_rank_eq_bnRank .POmegaPlus n 2 g Nat.prime_two hadm h3]
        simp only [bnRank]
        omega
      · have hn : 4 ≤ n := by simpa only [StatedLieAdmissible] using hadm.2.2
        have h3 : 3 ≤ bnRank .POmegaMinus n := by
          simp only [bnRank]
          omega
        rw [lieUniversal_rank_eq_bnRank .POmegaMinus n 2 g Nat.prime_two hadm h3]
        simp only [bnRank]
        omega
      · change 0 < 6
        norm_num
      · change 0 < 7
        norm_num
      · change 0 < 8
        norm_num
      · change 0 < 4
        norm_num
    · change 0 < 2
      norm_num
  exact RCKK1I.rckExists_longRoot M hpos

theorem excReturnFamily_of_carrierMod {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {a : Fin τ.rank → GGFinModel.GGLˣ} {i : KernelComponent (rootCharHom a)} {M : LieUniversal}
    {g : ℕ} (h3 : 3 ≤ compRank (componentRoots (rootCharHom a) i))
    (hMod : (compRank (componentRoots (rootCharHom a) i) = 1 ∧ M = ggU .PSL 2 g) ∨
        (twistKind ρ (rootCharHom a) i = .inner ∧
          2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1) ∧
          M = ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
        (twistKind ρ (rootCharHom a) i = .suN ∧
          M = ggU .PSU (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
        (twistKind ρ (rootCharHom a) i = .inner ∧
          4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) ∧
          M = ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) g) ∨
        (twistKind ρ (rootCharHom a) i = .twoD ∧
          M = ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) g) ∨
        (twistKind ρ (rootCharHom a) i = .inner ∧
          ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
              (componentRoots (rootCharHom a) i).ncard = 72 ∧ M = ggU .E6 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 7 ∧
              (componentRoots (rootCharHom a) i).ncard = 126 ∧ M = ggU .E7 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 8 ∧
              (componentRoots (rootCharHom a) i).ncard = 240 ∧ M = ggU .E8 0 g))) ∨
        (twistKind ρ (rootCharHom a) i = .exc ∧
          ((compRank (componentRoots (rootCharHom a) i) = 6 ∧ M = ggU .twistedE6 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 4 ∧
              ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
                TriField F σ g ∧ M = triD4Universal F σ)))) :
    ExcReturnFamily M g (compRank (componentRoots (rootCharHom a) i)) := by
  rcases hMod with ⟨hr1, -⟩ | ⟨-, -, -, hM⟩ | ⟨-, hM⟩ | ⟨-, hr4, -, hM⟩ |
    ⟨hkind, hM⟩ | ⟨-, hE⟩ | ⟨-, hE⟩
  · omega
  · exact Or.inl hM
  · exact Or.inr (Or.inl hM)
  · exact Or.inr (Or.inr (Or.inl ⟨hr4, hM⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(CrossChar.twoD_kind_unpack hkind).2.1, hM⟩)))
  · rcases hE with ⟨h6, -, hM⟩ | ⟨h7, -, hM⟩ | ⟨h8, -, hM⟩
    · rw [h6]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hM⟩)))))
    · rw [h7]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨rfl, hM⟩)))))))
    · rw [h8]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨rfl, hM⟩)))))))
  · rcases hE with ⟨h6, hM⟩ | ⟨h4, F, hF, hFin, σ, hT, hM⟩
    · rw [h6]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hM⟩))))))
    · rw [h4]
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨rfl, F, hF, hFin, σ, hT, hM⟩))))

end Model

theorem excU5Pinned_of_pieces
    (hPair : RCKRP.RCKCarrierPairADE) : ExcU5Pinned := by
  intro t ht X _ _ n f ψ p G₀ B₁ D J L x hH R Rm P hRJ hRmJ hpos hb e he he1 K hKG hKc hJK hKJ
    hodd hKG₀ iK hsub hne hspan horb h2
  obtain ⟨hp, hp2, hDB, -⟩ := ggSixPosHyp_excUK_facts hH
  have hτ : GGFinModel.langTag t = .D4 ∨ GGFinModel.langTag t = .E6 ∨
      GGFinModel.langTag t = .E7 ∨ GGFinModel.langTag t = .E8 := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGFinModel.langTag]
  have hτG2 : GGFinModel.langTag t ≠ .G2 := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [GGFinModel.langTag]
  obtain ⟨hq2, hqpow, hqL, hq5⟩ := P.q_facts
  let S : LangSetup (GGFinModel.langTag t) GGFinModel.GGL 5 :=
    P.Δ.toSetup 5 P.ρ P.frob Nat.prime_five (Or.inl le_rfl) ⟨hqpow, hqL⟩ hq5 P.finite
  have hT : rootDiagUnit (GGFinModel.langTag t) (P.coord e) ∈ S.D.torus := P.coord_torus e he
  have hap : ∀ j, P.coord e j ^ p = 1 := P.coord_pow e he
  have hap1 : rootDiagUnit (GGFinModel.langTag t) (P.coord e) ^ p = 1 :=
    P.rootDiagUnit_coord_pow he
  have hpL : ((p : ℕ) : GGFinModel.GGL) ≠ 0 := RCKRP.rck_natCast_ne_zero_GGL hp hp2
  have h1 : rootDiagUnit (GGFinModel.langTag t) (P.coord e) ≠ 1 :=
    ExcPacket.rootDiagUnit_coord_ne_one_of_component ht hH P he hKG hKc hKG₀
  have hKc' : CFSG.Open.IsComponentOf ((K.subgroupOf G₀).map P.η)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit (GGFinModel.langTag t) (P.coord e)}) :=
    CFSG.Assembly.isComponentOf_iff_open.1 (P.attach_nbr e he K hKG hKc)
  obtain ⟨i, hqs, hKeq⟩ :=
    LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 S hτG2 hp hpL hT hap h1 hKc'
  have hJKmap : (J.subgroupOf G₀).map P.η ≤ (K.subgroupOf G₀).map P.η :=
    Subgroup.map_mono (Subgroup.comap_mono hJK)
  have hRi_le : rationalComponent S.ρ S.Γ (rootCharHom (P.coord e)) i ≤
      rootSpan (GGFinModel.langTag t) GGFinModel.GGL
        (rationalRoots S.ρ (rootCharHom (P.coord e)) i) :=
    (Subgroup.commutator_le_self _).trans inf_le_left
  have hJi : (J.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
      (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) i)) :=
    hJKmap.trans (hKeq.le.trans hRi_le)
  have hJiK : (J.subgroupOf G₀).map P.η ≤ rootSpan (GGFinModel.langTag t) (ExcOmega f)
      (LieCore.ratOrbit P.ρ (componentRoots (P.chiAt e) iK)) :=
    P.map_J_le.trans (rootSpan_mono (ratOrbit_mono P.ρ hsub))
  have horbit := ratOrbit_eq_of_isQuasisimple_le (fun γ hγ => P.mapsTo_rho_chiAt he hγ)
    P.frob.iform_eq P.attach_J.2.2 hJi hJiK
  have hiK : i = iK := eq_of_ratOrbit_eq_of_componentOrbitLength_eq_one horb horbit
  rw [hiK] at hqs hKeq
  have hstd : RCKRP.RCKADEShape S.ρ (rootCharHom (P.coord e)) iK :=
    RCKRP.rckStdEnvelope_holds (GGFinModel.langTag t) hτ S p hp hp2 (P.coord e) hT h1 hap iK hqs
  have hcp := hPair (GGFinModel.langTag t) 5 S (P.coord e) hT p hp hp2 hap1 iK f hq2 hstd hqs
  obtain ⟨M, φ, hMod, hADE, hrange, hker, _, _, hsplit, hpairc⟩ := hcp
  have horb' : componentOrbitLength S.ρ (componentRoots (rootCharHom (P.coord e)) iK) = 1 := horb
  simp only [horb', mul_one] at hMod hADE
  have hr3 : 3 ≤ compRank (componentRoots (rootCharHom (P.coord e)) iK) :=
    three_le_compRank_of_ssubset hτ (Ψ := P.rootsJ) (isRootComponent_componentRoots P.iJ)
      (isRootComponent_componentRoots iK) h2 (Set.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm hne⟩)
  have hfam : ExcReturnFamily M f (compRank (componentRoots (rootCharHom (P.coord e)) iK)) :=
    excReturnFamily_of_carrierMod hr3 hMod
  obtain ⟨β, hβ, hlong⟩ := exists_ggLongRoot_of_rckADEModel hADE
  obtain ⟨γ, hγ, z, hz, hUst, hVst, hφβ, hφβ'⟩ := hpairc horb' β hβ hlong
  obtain ⟨-, hReqR, -, hReqRm, hWst, hWmst⟩ := P.pair_one hb
  have hα : P.α ∈ componentRoots (rootCharHom (P.coord e)) iK := hsub P.α_mem
  have hw : P.wD ∈ torusGroup (GGFinModel.langTag t) GGFinModel.GGL ⊔
      rootSpan (GGFinModel.langTag t) GGFinModel.GGL (kernelRoots (rootCharHom (P.coord e))) :=
    sup_le_sup_left (rootSpan_mono (P.kernelRoots_chiD_subset hDB he)) _ P.wD_mem
  obtain ⟨k, hk, hks, hk1, hk2⟩ :=
    RCKRP.rckCompPairIncidence hτ S hT hγ hα hz hw hUst hVst hWst hWmst
  let φ' : M.K →* ModGL (GGFinModel.langTag t) GGFinModel.GGL :=
    (MulAut.conj k).toMonoidHom.comp φ
  have hrange' : φ'.range = rationalComponent S.ρ S.Γ (rootCharHom (P.coord e)) iK := by
    change ((MulAut.conj k).toMonoidHom.comp φ).range = _
    rw [MonoidHom.range_comp, hrange,
      RCKRP.conj_rationalComponent_eq_of_mem_torus_sup_rootSpan S horb' hk hks]
  have hker' : φ'.ker ≤ Subgroup.center M.K :=
    (MonoidHom.ker_comp_of_injective φ _ (MulAut.conj k).injective).le.trans hker
  have : Group.IsPerfect ↥K := ⟨hKc.2.2.1⟩
  have hcen : (P.η.comp (Subgroup.inclusion hKG)).ker ≤ Subgroup.center ↥K :=
    CFSG.SeitzReduction.OmegaPilot.ker_comp_inclusion_le_center hKG P.η P.ker_η
  have hrng' : φ'.range = (K.subgroupOf K).map (P.η.comp (Subgroup.inclusion hKG)) := by
    rw [hrange', map_subgroupOf_comp_inclusion P.η hKG le_rfl, hKeq]
  obtain ⟨α', hαs, hαc⟩ := RCKRP.rck_exists_lift K K le_rfl
    (P.η.comp (Subgroup.inclusion hKG)) hcen hodd M.K hsplit φ' hrng'
  have hcomp : (P.η.comp (Subgroup.inclusion hKG)).comp α' = φ' :=
    MonoidHom.ext fun s => hαc s
  have hcov : α'.ker ≤ Subgroup.center M.K := fun s hs => hker' (by
    rw [MonoidHom.mem_ker, ← hcomp, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one])
  have hwAdj : P.wD ∈ adjointGroup (GGFinModel.langTag t) GGFinModel.GGL :=
    torus_sup_rootSpan_le_adjointGroup _ hw
  have hcurve : ∀ δ, excCurve δ P.wD ≤ adjointGroup (GGFinModel.langTag t) GGFinModel.GGL :=
    fun δ => (Subgroup.map_mono (rootSubgroup_le_adjointGroup δ)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hwAdj)).le
  have hφ'β : (M.D.rootGroup β).map φ' = excCurve P.α P.wD ⊓ P.Δ.model := by
    rw [← Subgroup.map_map, hφβ]
    exact S.D.map_conj_inf_eqLocus_eq_inf_model hks hk1 (hcurve P.α)
  have hφ'β' : (M.D.rootGroup (-β)).map φ' = excCurve (-P.α) P.wD ⊓ P.Δ.model := by
    rw [← Subgroup.map_map, hφβ']
    exact S.D.map_conj_inf_eqLocus_eq_inf_model hks hk2 (hcurve (-P.α))
  have hRK : R ≤ K := hRJ.trans hJK
  have hRmK : Rm ≤ K := hRmJ.trans hJK
  obtain ⟨hR2, hRm2⟩ := isPGroup_two_of_ggRootPosG0 ht hH hpos
  have hstdM := RCKRP.rckNC_adeModel_standard hADE
  have hβ2 : IsPGroup 2 (M.D.rootGroup β) := RCKRP.rckRootGroupTwo_holds M f hstdM β hβ
  have hβ2' : IsPGroup 2 (M.D.rootGroup (-β)) :=
    RCKRP.rckRootGroupTwo_holds M f hstdM (-β)
      (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (hA := M.D.isFiniteType)
        (D := M.D.divisible) hβ)
  have hconj1 : ((1 : MulAut M.K) : M.K →* M.K) = MonoidHom.id M.K := by
    ext x
    rfl
  have hReq : R = ggRootSub M.D (K.subtype.comp α') β 1 := by
    have h := eq_map_of_map_eq_of_isPGroup (P.η.comp (Subgroup.inclusion hKG)) hcen hodd α'
      hβ2 hRK hR2 (by
        rw [map_subgroupOf_comp_inclusion P.η hKG hRK, hReqR, hcomp, ← hφ'β])
    simpa [ggRootSub, hconj1, Subgroup.map_id] using h
  have hRmeq : Rm = ggRootSub M.D (K.subtype.comp α') (-β) 1 := by
    have h := eq_map_of_map_eq_of_isPGroup (P.η.comp (Subgroup.inclusion hKG)) hcen hodd α'
      hβ2' hRmK hRm2 (by
        rw [map_subgroupOf_comp_inclusion P.η hKG hRmK, hReqRm, hcomp, ← hφ'β'])
    simpa [ggRootSub, hconj1, Subgroup.map_id] using h
  exact ⟨M, (M.D.rootGroup β).map ((P.η.comp (Subgroup.inclusion hKG)).comp α'),
    (M.D.rootGroup (-β)).map ((P.η.comp (Subgroup.inclusion hKG)).comp α'),
    { model_at := hstdM
      beta := β
      root_mem := hβ
      long := hlong
      cover := α'
      surj := hαs
      central := hcov
      positive := rfl
      negative := rfl }, hfam, 1, hReq, hRmeq⟩

end CFSG.StandardType.LieKnownR2.ExcPos
