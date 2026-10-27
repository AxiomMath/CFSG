module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Transport

variable {G : Type} [Group G] [Finite G]

theorem ggIsScalar_of_ggTorusIrred {p r : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {X : Subgroup G} (hX : commutator X = ⊤)
    (hinj : Bs ⊓ Subgroup.centralizer (X : Set G) = ⊥) {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusIrred p r R I) (ψ : MulAut ↥Bs)
    (hψ : ∀ w ∈ ggAutomizer X Bs, ψ * w = w * ψ) : GGIsScalar ψ := by
  classical
  obtain ⟨hp, hBs, -, -, h4⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hγinj : Function.Injective (ggGamma X hBsN) := ggGamma_injective_of_inf_eq_bot hBsN hinj
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p (ggGamma X hBsN).range := isElemAbelian_range hBc hBp _
  have hAI : ∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : X,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  have hcard : Nat.card (ggGamma X hBsN).range = Nat.card Bs :=
    (Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv).symm
  have hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range :=
    hcard ▸ pow_le_card_bstar_of_torusLift hcfg hX θ hlift
  have h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range := by
    rw [hcard]
    exact le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) h4
  obtain ⟨W, hW1, -, -, hW4⟩ := hT X (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hX (ggGamma X hBsN).range hA hAI hr h3
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

end Transport

theorem ggWeylCentralizerScalarInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I) :
    GGWeylCentralizerScalarInputOn S := by
  intro G _ _ p B Bs x L D J hH hM ψ _ hψ
  have hp : p.Prime := hH.1.tableB_facts.1
  obtain ⟨hX, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, hBs3⟩, r, hlift, hirr⟩ := largeEvenRawDatum_exists hraw
  exact ggIsScalar_of_ggTorusIrred hH.1 hX (bstar_inf_centralizer_ggG0_eq_bot hH.1) θ hBsN hBs3
    hlift hirr ψ hψ

theorem ggWeylCentralizerScalarInputOn_typeA : GGWeylCentralizerScalarInputOn GGTypeALabel :=
  ggWeylCentralizerScalarInputOn_of_labels fun _ _ hp hlab h =>
    TypeA.largeEvenLabelAll_tableBIrred_typeA hp hlab h

theorem ggWeylCentralizerScalarInput_of_rest
    (h : GGWeylCentralizerScalarInputOn fun p lab => ¬ GGTypeALabel p lab) :
    GGWeylCentralizerScalarInput :=
  ggWeylCentralizerScalarInput_of_on ggWeylCentralizerScalarInputOn_typeA h

end CFSG.StandardType

end
