module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def ggTorusPseudoReflSet (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) :
    Set (MulAut ↥A) :=
  {φ | ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    GGTorusWeylElt p A n ∧ φ = ggConjAut A hn ∧ GGIsPseudoReflection p φ}

@[expose] def GGTorusPseudoReflGen (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
        Subgroup.closure (ggTorusPseudoReflSet p A)

@[expose] def GGTorusWeylNormInner (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ φ ∈ Subgroup.normalizer
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A)),
        ∃ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
          ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, φ * v * φ⁻¹ = w * v * w⁻¹

theorem ggTorusPseudoReflGen_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusPseudoReflGen p r R' I') :
    GGTorusPseudoReflGen p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφI, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφI, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

theorem ggTorusWeylNormInner_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusWeylNormInner p r R' I') :
    GGTorusWeylNormInner p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφI, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφI, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

section Transport

variable {G : Type} [Group G] [Finite G]

theorem ggGamma_range_hyps {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hX : commutator X = ⊤) {R : Type}
    [Group R] (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) :
    IsElemAbelian p (ggGamma X hBsN).range ∧
      (∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : X,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ r ≤ Nat.card (ggGamma X hBsN).range ∧ p ^ 3 ≤ Nat.card (ggGamma X hBsN).range := by
  obtain ⟨hp, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hcard : Nat.card (ggGamma X hBsN).range = Nat.card Bs :=
    (Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv).symm
  refine ⟨isElemAbelian_range hBc hBp _, ?_, hcard ▸ pow_le_card_bstar_of_torusLift hcfg hX θ hlift,
    ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  · rw [hcard]
    exact le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h4

theorem image_ggTorusPseudoReflSet_subset {p : ℕ} {Bs X : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hγinj : Function.Injective (ggGamma X hBsN))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    (MulAut.congr (MonoidHom.ofInjective hγinj).symm).toMonoidHom ''
        ggTorusPseudoReflSet p (ggGamma X hBsN).range ⊆
      {φ | φ ∈ ggAutomizer X Bs ∧ GGIsPseudoReflection p φ} := by
  rintro _ ⟨ψ, ⟨m, hm, hmW, rfl, hψp⟩, rfl⟩
  have hmN := mem_normalizer_of_ggTorusWeylElt hBsN hSC hmW
  have he := congr_ggConjAut_ggGamma hBsN hγinj m.2 hmN hm
  refine ⟨?_, hψp.congr _⟩
  show MulAut.congr (MonoidHom.ofInjective hγinj).symm (ggConjAut _ hm) ∈ _
  rw [he]
  exact ggConjAut_mem_ggAutomizer m.2 hmN

omit [Finite G] in
theorem ggAutomizer_le_map_inn {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hγinj : Function.Injective (ggGamma X hBsN)) :
    ggAutomizer X Bs ≤
      (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range).map
        (MulAut.congr (MonoidHom.ofInjective hγinj).symm).toMonoidHom := by
  intro φ hφ
  obtain ⟨g, hgX, hg, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  have hφeq : φ = ggConjAut Bs hg := MulEquiv.ext fun b => Subtype.ext (hφg b)
  have hn := conj_mem_normalizer_range_ggGamma hBsN hgX hg
  have hc : MulAut.conj (⟨g, hgX⟩ : X) ∈ (MulAut.conj : X →* MulAut X).range := ⟨_, rfl⟩
  refine ⟨_, ggConjAut_mem_ggAutomizer hc hn, ?_⟩
  rw [hφeq]
  exact congr_ggConjAut_ggGamma hBsN hγinj hgX hg hn

theorem map_ggAutomizer_inn_eq {p : ℕ} {Bs X : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hγinj : Function.Injective (ggGamma X hBsN))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hgen : ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range ≤
      Subgroup.closure (ggTorusPseudoReflSet p (ggGamma X hBsN).range)) :
    (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range).map
        (MulAut.congr (MonoidHom.ofInjective hγinj).symm).toMonoidHom = ggAutomizer X Bs := by
  refine le_antisymm ?_ (ggAutomizer_le_map_inn hBsN hγinj)
  refine (Subgroup.map_mono hgen).trans ?_
  rw [MonoidHom.map_closure]
  refine (Subgroup.closure_mono (image_ggTorusPseudoReflSet_subset hBsN hγinj hSC)).trans ?_
  exact (Subgroup.closure_le _).mpr fun φ hφ => hφ.1

theorem ggPseudoReflGenerated_of_ggTorusPseudoReflGen {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusPseudoReflGen p r R I) :
    GGPseudoReflGenerated p (ggAutomizer X Bs) := by
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hA, hAI, hr, h3⟩ := ggGamma_range_hyps hcfg hX θ hBsN hγinj hBs3 hlift
  have hgen := hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX _ hA hAI
    hr h3
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun φ hφ => hφ.1)
  refine (ggAutomizer_le_map_inn hBsN hγinj).trans ((Subgroup.map_mono hgen).trans ?_)
  rw [MonoidHom.map_closure]
  exact Subgroup.closure_mono (image_ggTorusPseudoReflSet_subset hBsN hγinj hSC)

theorem exists_inner_of_ggTorusWeylNormInner {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusPseudoReflGen p r R I)
    (hN : GGTorusWeylNormInner p r R I) (φ : MulAut ↥Bs)
    (hφ : φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs))) :
    ∃ w ∈ ggAutomizer X Bs, ∀ v ∈ ggAutomizer X Bs, φ * v * φ⁻¹ = w * v * w⁻¹ := by
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hA, hAI, hr, h3⟩ := ggGamma_range_hyps hcfg hX θ hBsN hγinj hBs3 hlift
  have hgen := hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX _ hA hAI
    hr h3
  set Φ := MulAut.congr (MonoidHom.ofInjective hγinj).symm with hΦ
  have hW := map_ggAutomizer_inn_eq hBsN hγinj hSC hgen
  rw [← hΦ] at hW
  have hmemW : ∀ v, v ∈ ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range ↔
      Φ v ∈ ggAutomizer X Bs := by
    intro v
    rw [← hW]
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v', hv', hvv'⟩
      have h1 : v' = v := Φ.injective hvv'
      rwa [← h1]
  have hφ' : Φ.symm φ ∈ Subgroup.normalizer
      (ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range :
        Set (MulAut ↥(ggGamma X hBsN).range)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [hmemW, hmemW, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_normalizer_iff.mp hφ (Φ v)
  obtain ⟨w, hw, hwv⟩ := hN X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX _
    hA hAI hr h3 _ hφ'
  refine ⟨Φ w, (hmemW w).mp hw, fun v hv => ?_⟩
  have hv' : Φ.symm v ∈ ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range := by
    rw [hmemW, MulEquiv.apply_symm_apply]
    exact hv
  have h1 := congrArg Φ (hwv _ hv')
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
  exact h1

end Transport

theorem ggWeylPseudoReflGenInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I) :
    GGWeylPseudoReflGenInputOn S := by
  intro G _ _ p B Bs x L D J hH hM
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, r, hlift, hgen⟩ := largeEvenRawDatum_exists hraw
  exact ggPseudoReflGenerated_of_ggTorusPseudoReflGen hH.1 hX θ hBsN
    (ggGamma_injective_of_inf_eq_bot hBsN (bstar_inf_centralizer_ggG0_eq_bot hH.1)) hBs3 hlift hgen

theorem ggInnerOnWeylInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧
        GGTorusWeylNormInner p r R I) :
    GGInnerOnWeylInputOn S := by
  intro G _ _ p B Bs x L D J hH hM φ _ hφ
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, r, hlift, hgen, hN⟩ :=
    largeEvenRawDatum_exists hraw
  exact exists_inner_of_ggTorusWeylNormInner hH.1 hX θ hBsN
    (ggGamma_injective_of_inf_eq_bot hBsN (bstar_inf_centralizer_ggG0_eq_bot hH.1)) hBs3 hlift
    hgen hN φ hφ

theorem ggCorFiveTwentyOuterInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPseudoReflGen p r R I ∧
        GGTorusWeylNormInner p r R I) :
    GGCorFiveTwentyOuterInputOn S :=
  ggCorFiveTwentyOuterInputOn_of_inner (ggInnerOnWeylInputOn_of_labels h)

end CFSG.StandardType

end
