module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagPair
public import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs
public import CFSG.LocalAnalysis.StandardType.GGA2Conj
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Helpers

variable {K G : Type} [Group K] [Group G]

private lemma rootGroup_map_conj_weylLift (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (γ : Fin D.rank → ℤ)
    (hγ : γ ∈ D.roots) :
    (D.rootGroup (weylAction D.isFiniteType u γ)).map ψ =
      (D.rootGroup γ).map ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨(ν u)⁻¹ * y * ν u, ?_, ?_⟩
    · have h := hν.conj_mem (u⁻¹) (weylAction D.isFiniteType u γ)
        (weylAction_mem_roots D.isFiniteType u hγ) y hy
      rw [map_inv ν u, inv_inv, weylAction_inv_apply_apply] at h
      exact h
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
      group
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨ν u * z * (ν u)⁻¹, hν.conj_mem u γ hγ z hz, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

private lemma ggRootLevi_map_conj_weylLift (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (i : Fin D.rank) :
    (ggRootLevi D (weylAction D.isFiniteType u (Pi.single i 1))).map ψ =
      ((ggRootLevi D (Pi.single i 1 : Fin D.rank → ℤ)).map ψ).map
        (MulAut.conj (ψ (ν u))).toMonoidHom := by
  have hsingle : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (isCTRootSystem D.isFiniteType D.divisible).single_mem i
  have h1 := rootGroup_map_conj_weylLift D ν hν ψ u (Pi.single i 1) hsingle
  have hsingle' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hsingle
  have h2 := rootGroup_map_conj_weylLift D ν hν ψ u (-(Pi.single i 1)) hsingle'
  change (D.rootGroup (weylAction D.isFiniteType u (Pi.single i 1)) ⊔
      D.rootGroup (-(weylAction D.isFiniteType u (Pi.single i 1)))).map ψ =
    ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-(Pi.single i 1))).map ψ).map
      (MulAut.conj (ψ (ν u))).toMonoidHom
  rw [← map_neg (weylAction D.isFiniteType u) (Pi.single i 1)]
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map,
    h1, h2]

end Helpers

section Rk2

private lemma ggRk2_core {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3t : 3 ≤ bnRank t n)
    (ψ : (ggU t n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs))
    (hεlevi : ∀ (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group)
        (i : Fin (ggU t n f).D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ)
    {r r' : MulAut ↥Bs}
    (hrC : r ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε)
    (hr'C : r' ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε)
    (hne : r ≠ r') :
    (r * r' = r' * r →
      ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs r', a * b = b * a) ∧
    (GGSplitLie p X → r * r' ≠ r' * r →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (W : Subgroup G), CharP F 2 ∧
        LinearBlockStandardPair F W (ggRankOneIn X Bs r) (ggRankOneIn X Bs r')) := by
  have hW := (ggTag_weylMatrix ht hadm).1
  have h3ψ := (ggTag_weylMatrix ht hadm).2
  have hmul : ∀ a b : (coxeterMatrix (ggU t n f).D.isFiniteType).Group,
      ((ε (a * b) : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        ((ε a : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) *
          ((ε b : ↥(ggAutomizer X Bs)) : MulAut ↥Bs) :=
    fun a b => by rw [map_mul, Subgroup.coe_mul]
  constructor
  · intro hcomm a ha b hb
    obtain ⟨w, i, hw⟩ := hrC
    obtain ⟨w', j, hw'⟩ := hr'C
    have hr_eq : ggRankOneIn X Bs r =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ := by
      rw [hw]; exact hεlevi w i
    have hr'_eq : ggRankOneIn X Bs r' =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w' (Pi.single j 1))).map ψ := by
      rw [hw']; exact hεlevi w' j
    have ha' : a ∈ (ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ := by
      rw [← hr_eq]; exact ha
    obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.mp ha'
    have hb' : b ∈ (ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w' (Pi.single j 1))).map ψ := by
      rw [← hr'_eq]; exact hb
    obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.mp hb'
    have hne_w : w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹ ≠
        w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹ := by
      intro heq
      apply hne
      rw [hw, hw', heq]
    have hcomm_w : Commute
        (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)
        (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹) := by
      apply ε.injective
      apply Subtype.ext
      rw [hmul (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)
          (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹),
        hmul (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹)
          (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)]
      rw [← hw, ← hw']
      exact hcomm
    have hlevi := ggTag_levi_comm ht hadm h3t w w' i j hne_w hcomm_w a0 ha0 b0 hb0
    simpa only [map_mul] using congrArg ψ hlevi
  · intro _ hnc
    obtain ⟨w, i, hw⟩ := hrC
    obtain ⟨w', j, hw'⟩ := hr'C
    have hne_w : w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹ ≠
        w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹ := by
      intro heq
      apply hne
      rw [hw, hw', heq]
    have hncomm : ¬ Commute
        (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)
        (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹) := by
      intro hcw
      apply hnc
      rw [hw, hw']
      rw [← hmul (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)
          (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹),
        ← hmul (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹)
          (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹)]
      exact congrArg (fun x => ((ε x : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)) hcw
    have hord : ((w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) *
        (w' * (coxeterMatrix (ggU t n f).D.isFiniteType).simple j * w'⁻¹)) ^ 3 = 1 :=
      ggWeyl_refl_order3 (ggU t n f).D.isFiniteType
        (ggSimplyLacedConnected_of_weyl hW h3ψ) w w' i j hncomm
    obtain ⟨a, b, hab, hstdmap⟩ := ggTag_adjStdPair ht hadm h3t
    obtain ⟨u, hu1, hu2⟩ :=
      ggA2_conj hW h3ψ ⟨w, i, rfl⟩ ⟨w', j, rfl⟩ hne_w hord hab
    obtain ⟨ν, hν⟩ := (ggTagFacts_of_admissible hadm h3t).2.1
    have hr_eq : ggRankOneIn X Bs r =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType u (Pi.single a 1))).map ψ := by
      rw [hw, ← hu1]; exact hεlevi u a
    have hr'_eq : ggRankOneIn X Bs r' =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType u (Pi.single b 1))).map ψ := by
      rw [hw', ← hu2]; exact hεlevi u b
    have hconj_a := ggRootLevi_map_conj_weylLift (ggU t n f).D ν hν ψ u a
    have hconj_b := ggRootLevi_map_conj_weylLift (ggU t n f).D ν hν ψ u b
    obtain ⟨W₀, hW₀⟩ := hstdmap ψ hker
    have hf : 1 ≤ f := hadm.2.1
    haveI : NeZero f := ⟨by omega⟩
    refine ⟨GaloisField 2 f, inferInstance, inferInstance,
      W₀.map (MulAut.conj (ψ (ν u))).toMonoidHom, inferInstance, ?_⟩
    have hpair := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW₀
      (ψ (ν u))
    rw [hr_eq, hconj_a, hr'_eq, hconj_b]
    exact hpair

theorem ggSecFiveRk2Input_of_kgPos (hKG : GGSecFiveKGPosInput) (hNbr : GGSecFiveSplitNbrInput) :
    GGSecFiveRk2Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 X hX r hrA hrC r' hrA' hrC' hne
  have hXs : GGSplitLie p X := by
    rcases hX with rfl | hK
    · exact hL
    · exact hNbr G p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 X hK
  obtain ⟨t, n, f, ψ, hadm, h3t, hker, _, ht, _, hpos⟩ :=
    hKG G p B Bs x L D J 𝒦 hcfg hL ι M e hpres h3 X hX hXs
  obtain ⟨ε, hεrefl, hεlevi, _⟩ := hpos
  have hW := (ggTag_weylMatrix ht hadm).1
  have h3ψ := (ggTag_weylMatrix ht hadm).2
  have hpresψ : GGCoxeterPres p (ggAutomizer X Bs)
      (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨hW, hεrefl⟩
  have hrefl : GGIsReflection p r :=
    ggCoxRefl_isReflection (fun i => hpres.2 i) hrC
  have hrCox : r ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpresψ h3ψ hrA hrefl
  have hrefl' : GGIsReflection p r' :=
    ggCoxRefl_isReflection (fun i => hpres.2 i) hrC'
  have hrCox' : r' ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpresψ h3ψ hrA' hrefl'
  exact ggRk2_core ht hadm h3t ψ hker ε hεlevi hrCox hrCox' hne

end Rk2

end CFSG.StandardType
