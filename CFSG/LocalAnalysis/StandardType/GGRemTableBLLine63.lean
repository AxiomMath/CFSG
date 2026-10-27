module

public import CFSG.LocalAnalysis.StandardType.GGUnitDvdLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCover
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel

public section

namespace CFSG.StandardType.Line63

open CFSG CFSG.Assembly CFSG.StandardType TableB

@[expose] def GGUnitDvd63BstarRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab GGUnitDvd63Label p Bs L →
      p ^ 5 ≤ Nat.card Bs

@[expose] def GGUnitDvd63LineSCr4 : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGUnitDvd63Label p lab →
    LargeEvenLabelAll lab fun R _ I _ => GGNoInvariantLineSCr p 4 R I

variable {G : Type} [Group G] [Finite G]

theorem not_normalizer_le_of_noInvariantLineSCr_card {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma L hN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hT : GGNoInvariantLineSCr p r R I) {E : Subgroup G}
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

theorem ggLNoInvariantLineInputOn_unitDvd63_of (h5 : GGUnitDvd63BstarRankInput)
    (h4 : GGUnitDvd63LineSCr4) : GGLNoInvariantLineInputOn GGUnitDvd63Label := by
  intro G _ _ p B Bs x L D J hcfg hM E hEBs hxE hE
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hcard := h5 G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => GGUnitDvd63Label p lab)
    (fun lab hlab hs => h4 p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hBsN
  have h4' : p ^ 4 ≤ Nat.card (ggGamma L hBsN).range := by
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  exact not_normalizer_le_of_noInvariantLineSCr_card hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4'
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4') hT hEBs hxE hE


section LineU63

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType.LineU
open scoped commutatorElement

theorem noInvariantLineSCr_unitary63 {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hcov : UnitaryCoverAt n 6 K)
    (hpq : 3 ∣ 2 ^ n + 1) :
    CFSG.StandardType.GGNoInvariantLineSCr 3 4
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _h3 _hsc
  have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by simpa using hr
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    exists_diagModel hK hn (by norm_num) Nat.prime_three hpq (by norm_num) hcov hψ hker hperf
      hA hAI hcard
  have h := TableBU.unitaryFieldData_of_card hK hn
  haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
    DFunLike.coe_injective
  refine ⟨{x | ∃ σ : Equiv.Perm (Fin 6), x = φ (permSU h σ)},
    weyl_W_prop h (by norm_num) hφker hA.2 hdiag, fun Λ hΛA hΛp => ?_⟩
  obtain ⟨σ, e, heΛ, hmv⟩ := moved_of_diag h (by norm_num) hφs hφker Nat.prime_three hA.2 hdiag
    hΛA hΛp
  exact ⟨φ (permSU h σ), ⟨σ, rfl⟩, e, heΛ, hmv⟩

theorem largeEvenLabelAll_unitDvd63_line (hU : UnitaryUniversalCover) {p : ℕ}
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab)
    (hn1 : lab.n ≠ 1) :
    LargeEvenLabelAll lab fun R _ I _ => CFSG.StandardType.GGNoInvariantLineSCr p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3 hn1
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', noInvariantLineSCr_unitary63 hK hn
    (hU n 6 K hK (by norm_num) (by intro h; exact hn1 (congrArg Prod.snd h))) hpn⟩⟩

end LineU63

end CFSG.StandardType.Line63

end
