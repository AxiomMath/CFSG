module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTorusSelfCent (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∀ n : L', (∀ a ∈ A, a n = n) → n ^ p = 1 → MulAut.conj n ∈ A

@[expose] def GGTorusPseudoReflGenSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A ≤
        Subgroup.closure (ggTorusPseudoReflSet p A)

@[expose] def GGTorusSchurSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L', (∀ n ∈ W, GGTorusWeylElt p A n) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ A, f a ∈ A) →
          (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ A, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) →
          ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c

@[expose] def GGTorusWeylNormInnerSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∀ φ ∈ Subgroup.normalizer
        (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A)),
        ∃ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
          ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, φ * v * φ⁻¹ = w * v * w⁻¹

section Transport

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggTorusSelfCent_ggGamma {p : ℕ} {Bs X : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    GGTorusSelfCent p (ggGamma X hBsN).range := by
  intro n hn hnp
  have hnC : (n : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 : b * (n : G) * b⁻¹ = n := by
      have := congrArg Subtype.val (hn (ggGamma X hBsN ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩)
      rw [ggGamma_coe] at this
      exact this
    calc b * (n : G) = b * n * b⁻¹ * b := by group
      _ = n * b := by rw [h1]
  have hnp' : (n : G) ^ p = 1 := by
    have := congrArg Subtype.val hnp
    simpa using this
  refine ⟨⟨n, hSC _ hnC hnp'⟩, ?_⟩
  ext l
  simp [ggGamma_coe, MulAut.conj_apply]

theorem ggGamma_range_hypsSC {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggGamma X hBsN).range ∧
      (∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : X,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ 3 ≤ Nat.card (ggGamma X hBsN).range ∧ GGTorusSelfCent p (ggGamma X hBsN).range := by
  obtain ⟨hp, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hcard : Nat.card (ggGamma X hBsN).range = Nat.card Bs :=
    (Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv).symm
  refine ⟨isElemAbelian_range hBc hBp _, ?_, ?_, ggTorusSelfCent_ggGamma hBsN hcfg.2.1.2.2.2⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  · rw [hcard]
    exact le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h4

theorem ggPseudoReflGenerated_of_ggTorusPseudoReflGenSC {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : GGTorusPseudoReflGenSC p R I) :
    GGPseudoReflGenerated p (ggAutomizer X Bs) := by
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hA, hAI, h3, hsc⟩ := ggGamma_range_hypsSC hcfg θ hBsN hγinj hBs3
  have hgen := hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX _ hA hAI
    h3 hsc
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun φ hφ => hφ.1)
  refine (ggAutomizer_le_map_inn hBsN hγinj).trans ((Subgroup.map_mono hgen).trans ?_)
  rw [MonoidHom.map_closure]
  exact Subgroup.closure_mono (image_ggTorusPseudoReflSet_subset hBsN hγinj hSC)

theorem ggIsScalar_of_ggTorusSchurSC {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hX : commutator X = ⊤)
    (hinj : Bs ⊓ Subgroup.centralizer (X : Set G) = ⊥) {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : GGTorusSchurSC p R I) (ψ : MulAut ↥Bs)
    (hψ : ∀ w ∈ ggAutomizer X Bs, ψ * w = w * ψ) : GGIsScalar ψ := by
  classical
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hγinj : Function.Injective (ggGamma X hBsN) := ggGamma_injective_of_inf_eq_bot hBsN hinj
  obtain ⟨hA, hAI, h3, hsc⟩ := ggGamma_range_hypsSC hcfg θ hBsN hγinj hBs3
  obtain ⟨W, hW1, hW4⟩ := hT X (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hX (ggGamma X hBsN).range hA hAI h3 hsc
  have hWN : ∀ n ∈ W, (n : G) ∈ Subgroup.normalizer (Bs : Set G) := fun n hn =>
    mem_normalizer_of_ggTorusWeylElt hBsN hSC (hW1 n hn)
  let f : MulAut X → MulAut X := fun a =>
    if ha : ∃ b, ggGamma X hBsN b = a then ggGamma X hBsN (ψ ha.choose) else a
  have hf : ∀ b, f (ggGamma X hBsN b) = ggGamma X hBsN (ψ b) := by
    intro b
    have hex : ∃ b', ggGamma X hBsN b' = ggGamma X hBsN b := ⟨b, rfl⟩
    have hch : hex.choose = b := hγinj hex.choose_spec
    show (if ha : ∃ b', ggGamma X hBsN b' = ggGamma X hBsN b then
      ggGamma X hBsN (ψ ha.choose) else ggGamma X hBsN b) = _
    rw [dite_eq_left hex, hch]
  obtain ⟨c, hc⟩ := hW4 f
    (by
      rintro _ ⟨b, rfl⟩
      rw [hf]
      exact ⟨_, rfl⟩)
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have e : ggGamma X hBsN a * ggGamma X hBsN b = ggGamma X hBsN (a * b) :=
        (map_mul _ a b).symm
      rw [e, hf, hf, hf, map_mul, map_mul])
    (by
      rintro n hn _ ⟨b, rfl⟩
      have hnN := hWN n hn
      have hcomm := congrArg (fun φ : MulAut Bs => φ b)
        (hψ (ggConjAut Bs hnN) (ggConjAut_mem_ggAutomizer n.2 hnN))
      simp only [MulAut.mul_apply] at hcomm
      rw [← ggGamma_conj X hBsN n b ((Subgroup.mem_normalizer_iff.mp hnN b).mp b.2), hf, hf,
        ← ggGamma_conj X hBsN n (ψ b) ((Subgroup.mem_normalizer_iff.mp hnN (ψ b)).mp (ψ b).2)]
      exact congrArg (ggGamma X hBsN) hcomm)
  refine ⟨c, fun b => hγinj ?_⟩
  rw [map_pow, ← hf]
  exact hc _ ⟨b, rfl⟩

theorem exists_inner_of_ggTorusWeylNormInnerSC {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hγinj : Function.Injective (ggGamma X hBsN))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hT : GGTorusPseudoReflGenSC p R I) (hN : GGTorusWeylNormInnerSC p R I) (φ : MulAut ↥Bs)
    (hφ : φ ∈ Subgroup.normalizer (ggAutomizer X Bs : Set (MulAut ↥Bs))) :
    ∃ w ∈ ggAutomizer X Bs, ∀ v ∈ ggAutomizer X Bs, φ * v * φ⁻¹ = w * v * w⁻¹ := by
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hA, hAI, h3, hsc⟩ := ggGamma_range_hypsSC hcfg θ hBsN hγinj hBs3
  have hgen := hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX _ hA hAI
    h3 hsc
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
    hA hAI h3 hsc _ hφ'
  refine ⟨Φ w, (hmemW w).mp hw, fun v hv => ?_⟩
  have hv' : Φ.symm v ∈ ggAutomizer (MulAut.conj : X →* MulAut X).range (ggGamma X hBsN).range := by
    rw [hmemW, MulEquiv.apply_symm_apply]
    exact hv
  have h1 := congrArg Φ (hwv _ hv')
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
  exact h1

end Transport

theorem ggWeylPseudoReflGenInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusPseudoReflGenSC p R I) :
    GGWeylPseudoReflGenInputOn S := by
  intro G _ _ p B Bs x L D J hH hM
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, hgen⟩ := largeEvenRawDatum_exists hraw
  exact ggPseudoReflGenerated_of_ggTorusPseudoReflGenSC hH.1 hX θ hBsN
    (ggGamma_injective_of_inf_eq_bot hBsN (bstar_inf_centralizer_ggG0_eq_bot hH.1)) hBs3 hgen

theorem ggWeylCentralizerScalarInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusSchurSC p R I) :
    GGWeylCentralizerScalarInputOn S := by
  intro G _ _ p B Bs x L D J hH hM ψ _ hψ
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, hirr⟩ := largeEvenRawDatum_exists hraw
  exact ggIsScalar_of_ggTorusSchurSC hH.1 hX (bstar_inf_centralizer_ggG0_eq_bot hH.1) θ hBsN hBs3
    hirr ψ hψ

theorem ggInnerOnWeylInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusPseudoReflGenSC p R I ∧ GGTorusWeylNormInnerSC p R I) :
    GGInnerOnWeylInputOn S := by
  intro G _ _ p B Bs x L D J hH hM φ _ hφ
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, hgen, hN⟩ := largeEvenRawDatum_exists hraw
  exact exists_inner_of_ggTorusWeylNormInnerSC hH.1 hX θ hBsN
    (ggGamma_injective_of_inf_eq_bot hBsN (bstar_inf_centralizer_ggG0_eq_bot hH.1)) hBs3 hgen hN
    φ hφ

theorem ggCorFiveTwentyOuterInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ =>
        GGTorusPseudoReflGenSC p R I ∧ GGTorusWeylNormInnerSC p R I) :
    GGCorFiveTwentyOuterInputOn S :=
  ggCorFiveTwentyOuterInputOn_of_inner (ggInnerOnWeylInputOn_of_labelsSC h)

end CFSG.StandardType

end
