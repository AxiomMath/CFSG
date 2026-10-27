module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Pieces

variable {Y : Type} [Group Y]

@[expose] def GGSubnormalPiece (p : ℕ) (V S : Subgroup Y) : Prop :=
  S ≤ V ∧ (IsComponentOf (S.map (QuotientGroup.mk' (LargeEvenPPrimeCore p Y))) ⊤ ∨
    ∃ R : Subgroup Y, R.Normal ∧ R ≤ V ∧ S ≤ R)

omit [Group Y] in
theorem ggLargeEvenPPrimeCore_eq (p : ℕ) (Y : Type) [Group Y] :
    LargeEvenPPrimeCore p Y = CFSG.pPrimeCore p Y :=
  rfl

theorem ggIsSubnormal_sup_normal {A R : Subgroup Y} (hA : IsSubnormal A ⊤) (hR : R.Normal) :
    IsSubnormal (A ⊔ R) ⊤ := by
  have h1 := ggIsSubnormal_map (QuotientGroup.mk' R) hA
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective R)] at h1
  have h2 := ggIsSubnormal_comap (QuotientGroup.mk' R) h1
  rwa [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

variable [Finite Y]

theorem ggExists_subnormal_of_pieces {p : ℕ} {V : Subgroup Y}
    (hO : LargeEvenPPrimeCore p Y ≤ V) {𝒮 : Set (Subgroup Y)}
    (h𝒮 : ∀ S ∈ 𝒮, GGSubnormalPiece p V S) :
    ∃ X : Subgroup Y, X ≤ V ∧ IsSubnormal X ⊤ ∧ sSup 𝒮 ≤ X := by
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p Y)
  set 𝒜 : Set (Subgroup Y) := {S | S ∈ 𝒮 ∧ IsComponentOf (S.map π) ⊤}
  set Xt : Subgroup (Y ⧸ LargeEvenPPrimeCore p Y) := sSup ((fun S => S.map π) '' 𝒜)
  have hXt : IsSubnormal Xt ⊤ := ggIsSubnormal_sSup_components (by
    rintro _ ⟨S, hS, rfl⟩
    exact hS.2)
  set R₀ : Subgroup Y := sSup {R : Subgroup Y | R.Normal ∧ R ≤ V}
  have hR₀ : R₀.Normal := Subgroup.sSup_normal _ fun _ hR => hR.1
  have hX₁ : IsSubnormal (Xt.comap π) ⊤ := by
    have h := ggIsSubnormal_comap π hXt
    rwa [Subgroup.comap_top] at h
  refine ⟨Xt.comap π ⊔ R₀, sup_le ?_ (sSup_le fun R hR => hR.2), ggIsSubnormal_sup_normal hX₁ hR₀,
    sSup_le fun S hS => ?_⟩
  · have hXtV : Xt ≤ V.map π := sSup_le (by
      rintro _ ⟨S, hS, rfl⟩
      exact Subgroup.map_mono (h𝒮 S hS.1).1)
    refine (Subgroup.comap_mono hXtV).trans ?_
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_le le_rfl hO
  · rcases (h𝒮 S hS).2 with hc | ⟨R, hRn, hRV, hSR⟩
    · refine le_sup_of_le_left ((Subgroup.le_comap_map π S).trans (Subgroup.comap_mono ?_))
      exact le_sSup ⟨S, ⟨hS, hc⟩, rfl⟩
    · exact le_sup_of_le_right (hSR.trans (le_sSup ⟨hRn, hRV⟩))

end Pieces

section Bar

variable {G : Type} [Group G]

theorem ggBarE_elem_card {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N E : Subgroup G} (hEN : E ≤ N)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p ((E.subgroupOf N).map (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N))) ∧
      Nat.card ((E.subgroupOf N).map (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N))) =
        Nat.card E := by
  set π := QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)
  refine ⟨ggIsElemAbelian_map (ggIsElemAbelian_subgroupOf hE N) π, ?_⟩
  have h2 : IsPGroup 2 (pCoreOf 2 N) := ggIsPGroup_pCoreOf 2 N
  have hinj : Function.Injective (π.comp (E.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have hk : ((s : ↥N)) ∈ CFSG.Assembly.pCore 2 ↥N := by
      rw [← QuotientGroup.ker_mk' (CFSG.Assembly.pCore 2 ↥N)]
      exact hs
    have hsP : ((s : ↥N) : G) ∈ pCoreOf 2 N := ⟨_, hk, rfl⟩
    obtain ⟨k, hk2⟩ := h2 ⟨_, hsP⟩
    have hk2' : ((s : ↥N) : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk2
      simpa using this
    have hsp : ((s : ↥N) : G) ^ p = 1 := hE.2 _ (Subgroup.mem_subgroupOf.mp s.2)
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have h1 : orderOf ((s : ↥N) : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hsp) hcop)
        (orderOf_dvd_of_pow_eq_one hk2')
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext (orderOf_eq_one_iff.mp h1))
  have hmap : (E.subgroupOf N).map π = (π.comp (E.subgroupOf N).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv]

end Bar

section Inputs

theorem ggSixRootCentralizer_pPrimeCore_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    LargeEvenPPrimeCore p (↥(Subgroup.centralizer {r}) ⧸
        CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})) ≤
      ((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
        (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))) := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hEr := hch.le_centralizer
  obtain ⟨-, hE, hEcard, -⟩ := hch
  obtain ⟨hEel, hEc⟩ := ggBarE_elem_card hp hp2 hEr hE
  rw [ggLargeEvenPPrimeCore_eq]
  exact hfus.pPrimeCore_le hp hEel (hEc.trans hEcard)

@[expose] def GGSixRootCentralizerPiecesInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ 𝒮 : Set (Subgroup (↥(Subgroup.centralizer {r}) ⧸
            CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))),
          (∀ S ∈ 𝒮, GGSubnormalPiece p
            (((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
              (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})))) S) ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ sSup 𝒮

theorem ggSixRootCentralizerQuotientInput_of_pieces (h : GGSixRootCentralizerPiecesInput) :
    GGSixRootCentralizerQuotientInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨𝒮, h𝒮, hcov⟩ := h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨X, hXV, hXsn, hle⟩ :=
    ggExists_subnormal_of_pieces (ggSixRootCentralizer_pPrimeCore_le hctx hch) h𝒮
  exact ⟨X, hXV, hXsn, fun y hy hyp => hle (hcov y hy hyp)⟩

theorem ggSixStepThreeBInput_of_pieces (hcyc : GGRootCentralizerCyclicInput)
    (h : GGSixRootCentralizerPiecesInput) : GGSixStepThreeBInput :=
  ggSixStepThreeBInput_of_quotient hcyc (ggSixRootCentralizerQuotientInput_of_pieces h)

end Inputs

end CFSG.StandardType
