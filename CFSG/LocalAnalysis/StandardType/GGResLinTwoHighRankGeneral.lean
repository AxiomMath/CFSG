module

public import CFSG.LocalAnalysis.StandardType.GGResLinTwoStableTorus
public import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem largeEvenRawDatumLegacy_exists_general {lab : LargeEvenLabel}
    {Q : LargeEvenRawCont} (h : LargeEvenRawDatumLegacy lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [LargeEvenRawDatumLegacy] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, _, b, c, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, _, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

private lemma aut_of_torus_data_general
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hCfg : GGConfig 3 B Bs x L D J)
    (hLperf : commutator ↥L = ⊤)
    (hZL : Subgroup.center ↥L = ⊥)
    (hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹)
    {R : Type} [Group R] (I : Set (MulAut R))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' => (l' : G) = b⁻¹ * (l : G) * b) φ)
    {r N : ℕ} (hSC : GGTorusAutCardSC 3 R I r N) :
    Nat.card ↥(ggAutomizer L Bs) = N := by
  classical
  have hAh : CFSG.Open.IsElemAbelian 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).1
  have hAI : ∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : ↥L,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.1
  have h3A : 3 ^ 3 ≤ Nat.card ↥(ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.1
  have hscA : GGTorusSelfCent 3 (ggGamma L hBsN).range :=
    (ggGamma_range_hypsSC_L hCfg θ hBsN hBs3).2.2.2
  let ψ : ↥L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have hq' : (QuotientGroup.mk' (Subgroup.center ↥L)) q = 1 := by
      apply θ.injective
      simpa [ψ] using hq
    exact (QuotientGroup.eq_one_iff q).mp hq'
  have hSCapp := hSC ↥L ψ hψsurj hψker hLperf (ggGamma L hBsN).range
    hAh hAI h3A hscA
  have hZL' : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [hZL] at hg
    have hg1 : g = 1 := Subgroup.mem_bot.mp hg
    subst hg1
    simp
  have hcard1 : Nat.card ↥(ggAutomizer L Bs) =
      Nat.card ↥(ggAutomizer L (Bs ⊓ L)) :=
    (ggLemma47c hCfg.tableB_facts.2.1 hCfg.2.1.2.2.2 hZL' hInnL).2.2.2.2
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hCfg.tableB_facts.2.1
  have hBXea : CFSG.Open.IsElemAbelian 3 (Bs ⊓ L) := by
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      exact CFSG.Open.IsElemAbelian.comm hBsEA
        (Subgroup.mem_inf.mp a.2).1 (Subgroup.mem_inf.mp b.2).1
    · intro a ha
      exact hBsEA.2 a (Subgroup.mem_inf.mp ha).1
  have hcard2 : Nat.card ↥(ggAutomizer L (Bs ⊓ L)) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) :=
    ggAutomizer_card_eq_inn inf_le_right hBXea hZL'
  have hrange := range_ggGamma_eq_map hCfg hZL' hInnL hBsN
  calc Nat.card ↥(ggAutomizer L Bs)
      = Nat.card ↥(ggAutomizer L (Bs ⊓ L)) := hcard1
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (Subgroup.map MulAut.conj ((Bs ⊓ L).subgroupOf L))) := hcard2
    _ = Nat.card ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (ggGamma L hBsN).range) := by rw [← hrange]
    _ = N := hSCapp.2

theorem GGResHyp.linTwo_rank_ge_five_automizerL_card
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : GGLinTwoLabel 3 lab)
    (hrank : 5 ≤ lab.rank)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hL : GGInnerDiagOnLabel (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L) :
    Nat.card ↥(ggAutomizer L Bs) =
      2 ^ ((lab.rank + 1) / 2) * ((lab.rank + 1) / 2).factorial := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨s, T, hTA, hZinj, hEq, hcardE, hsd, hcardBs⟩ :=
    GGResHyp.linTwo_stable_torus hH lab hlab hN hL
  obtain ⟨hperf, lab', hlab', hraw⟩ := hL
  let Q : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥L ⧸ Subgroup.center ↥L ≃* R,
        (fun p lab' => p = 3 ∧ lab' = lab) 3 lab' ∧
          Bs ≤ Subgroup.normalizer (L : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' : ↥L =>
              (l' : G) = b⁻¹ * (l : G) * b) φ
  obtain ⟨R0, hR0, I0, F0, hQ0⟩ :=
    largeEvenRawDatumLegacy_exists_general (Q := Q) hraw
  have hlab'_eq : lab' = lab := hQ0.2.2.choose_spec.1.2
  subst lab'
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn, hp3⟩ := hlab
  subst ht
  subst hn
  have hl5 : 5 ≤ l := by simpa using hrank
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hfield, hfinite, hK, hrawP⟩ := hraw
  obtain ⟨θ, hP⟩ := hrawP.2.2
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hCharP : CharP K 2 := by
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1) (by simpa using hK)
  letI : CharP K 2 := hCharP
  let d : ℕ := l + 1
  have hsd' : s = (l + 1) / 2 := by simpa using hsd
  have hd : 2 * s ≤ d ∧ d ≤ 2 * s + 1 := by
    dsimp [d]
    omega
  have hs3 : 3 ≤ s := by
    have := hrank
    omega
  have hBs3 : ∀ b ∈ Bs, ∃ φ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      LargeEvenInduces (θ := θ) (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ := by
    simpa [d] using hP.2.2
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hfacts := ggTwSL_facts_rec (K := K) (d := d) (r := s) hs3 hd (by
    simpa [hK2])
  have hsigned : GGTorusSignedEltSC 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    ggKGLn_signedEltSC_linearNonsplit (p := 3) Nat.prime_three (by norm_num)
      ggTw_cast_three_ne_zero (by norm_num [hK2]) (by omega)
  have hrankle : GGElemAbelianRankLE (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) 3 s :=
    ggTwSL_rankLE_rec (K := K) (d := d) (r := s) hs3 hd (by
      simpa [hK2])
  have hscRank : GGSelfCentRankGE 3 s (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    ggTwSL_scRank_rec (K := K) (d := d) (r := s) hs3 hd (by
      simpa [hK2])
  have hSC : GGTorusAutCardSC 3
      (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      s (2 ^ s * s.factorial) :=
    ggTwTorus_recipe_of_pieces Nat.prime_three (by norm_num)
      hfacts.1 hfacts.2.1 hfacts.2.2 hsigned hrankle hscRank
  have hZL : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hZinj z 1
    ext l
    have hcomm : z * l = l * z := (Subgroup.mem_center_iff.mp hz l).symm
    simpa [MulAut.conj_apply, hcomm]
  have hInnL : ∀ b ∈ Bs, ∃ k ∈ L, ∀ l ∈ L, b * l * b⁻¹ = k * l * k⁻¹ := by
    intro b hb
    obtain ⟨v, hv⟩ := (hTA (ggGamma L hN ⟨b, hb⟩)).mp ⟨⟨b, hb⟩, rfl⟩
    refine ⟨(T.el v : G), (T.el v).2, ?_⟩
    intro l hl
    have h := congrArg (fun f : MulAut ↥L => (((f ⟨l, hl⟩ : ↥L) : G))) hv
    simpa [ggGamma_coe, MulAut.conj_apply] using h
  have hcard := aut_of_torus_data_general hH.1 hperf hZL hInnL
    (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    θ hN hBs3 hSC
  simpa [hsd] using hcard

end CFSG.StandardType

end
