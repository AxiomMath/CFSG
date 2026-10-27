module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGNoInvariantLineSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Λ : Subgroup (MulAut L'), Λ ≤ A → Nat.card Λ = p →
          ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ

theorem ggNoInvariantLineSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGNoInvariantLineSCr p r R' I') :
    GGNoInvariantLineSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

section Config

variable {G : Type} [Group G] [Finite G]

theorem not_normalizer_le_of_noInvariantLineSCr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGNoInvariantLineSCr p r R I) {E : Subgroup G}
    (hEBs : E ≤ Bs) (hxE : x ∈ E) (hE : Nat.card E = p ^ 2) :
    ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  classical
  intro hNE
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
  obtain ⟨W, hW1, hW2⟩ := hT L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hL γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
  set EB : Subgroup Bs := E.subgroupOf Bs with hEB
  set Λ : Subgroup (MulAut L) := EB.map γ with hΛ
  have hΛA : Λ ≤ γ.range := Subgroup.map_le_range _ _
  have hEA : IsElemAbelian p E := isElemAbelian_mono hBs hEBs
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEBs.trans hN
  have hcE := card_range_ggGamma_mul_of hp hEA hxE hS.2.2.1 hLx hS.2.2.2.2 hEN
  have hΛE : Λ = ((ggGamma L hEN).range) := by
    ext a
    constructor
    · rintro ⟨⟨b, hb⟩, hbE, rfl⟩
      exact ⟨⟨b, Subgroup.mem_subgroupOf.mp hbE⟩, rfl⟩
    · rintro ⟨⟨b, hb⟩, rfl⟩
      exact ⟨⟨b, hEBs hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hΛcard : Nat.card Λ = p := by
    rw [hΛE]
    rw [hE, pow_two] at hcE
    exact Nat.eq_of_mul_eq_mul_right hp.pos hcE
  obtain ⟨n, hnW, e, he, hne⟩ := hW2 Λ hΛA hΛcard
  apply hne
  obtain ⟨⟨b, hbBs⟩, hbE, rfl⟩ := he
  have hbE' : b ∈ E := Subgroup.mem_subgroupOf.mp hbE
  have hnN := mem_normalizer_of_weyl hN hSC (hW1 n hnW)
  have hnb : (n : G) * b * (n : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hNE hnN) b).mp hbE'
  have hnbBs : (n : G) * b * (n : G)⁻¹ ∈ Bs := hEBs hnb
  refine ⟨⟨_, hnbBs⟩, Subgroup.mem_subgroupOf.mpr hnb, ?_⟩
  exact ggGamma_conj L hN n ⟨b, hbBs⟩ hnbBs

end Config

theorem ggLNoInvariantLineInputOn_of_labelsSCr {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I) :
    GGLNoInvariantLineInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM E hEBs hxE hE
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact not_normalizer_le_of_noInvariantLineSCr hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift hT hEBs hxE hE

end CFSG.StandardType

end
