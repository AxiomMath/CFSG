module

public import CFSG.LocalAnalysis.StandardType.GGTBRowUdSetup
public import CFSG.LocalAnalysis.StandardType.GGTBRowUdFrame
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatum
public import CFSG.LocalAnalysis.StandardType.GGExcReflTBWeylDatumOfWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBRowUCartan
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0
import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem ggUdD_tb_normal {G : Type} [Group G] {Bs L J : Subgroup G} {c : MulAut ↥Bs}
    (hc : c ∈ ggAutomizer L Bs)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutNormalClosure L J Bs) :
    c * φ * c⁻¹ ∈ ggAutNormalClosure L J Bs := by
  have hcI : c ∈ ggInduced L Bs := by
    rw [ggAutomizer_eq] at hc
    exact hc
  refine Subgroup.closure_induction
    (p := fun φ _ => c * φ * c⁻¹ ∈ ggAutNormalClosure L J Bs) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨c', hc', a, ha, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨c * c', mul_mem_ggInduced hcI hc', a, ha, ?_⟩
    group
  · simp
  · intro x y _ _ hx hy
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

private theorem ggUdD_tb_le_normalClosure {G : Type} [Group G] {Bs L J : Subgroup G}
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer J Bs) : a ∈ ggAutNormalClosure L J Bs := by
  have haI : a ∈ ggInduced J Bs := by
    rw [ggAutomizer_eq] at ha
    exact ha
  apply Subgroup.subset_closure
  exact ⟨1, one_mem_ggInduced L Bs, a, haI, by group⟩

private theorem ggUdD_tb_lift {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {c : MulAut ↥Bs} (hc : c ∈ ggAutomizer K Bs) :
    ∃ a ∈ ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range (ggGamma K hN).range,
      GGOverGamma hN c a := by
  obtain ⟨g, hgK, hg, hcg⟩ := mem_ggAutomizer_iff.mp hc
  have hceq : c = ggConjAut Bs hg := MulEquiv.ext fun b => Subtype.ext (hcg b)
  refine ⟨ggConjAut (ggGamma K hN).range (conj_mem_normalizer_range_ggGamma hN hgK hg),
    ggConjAut_mem_ggAutomizer (H := (MulAut.conj : ↥K →* MulAut ↥K).range)
      (Bs := (ggGamma K hN).range) (g := MulAut.conj (⟨g, hgK⟩ : ↥K))
      (MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, rfl⟩) (conj_mem_normalizer_range_ggGamma hN hgK hg), ?_⟩
  rw [hceq]
  exact ggOverGamma_conjAut (hN := hN) hgK hg

private theorem ggUdD_ker_card_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(ggGamma L hN).ker ≤ p := by
  have hker : (ggGamma L hN).ker =
      (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact le_of_eq hcfg.card_bstar_inf_centralizer_L

private theorem ggUdD_frame_reflSet {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {k : ℕ}
    (hF : GGWeylFrame p (ggGamma L hN).range (CoxeterMatrix.A k)) :
    ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma L hN).range) := by
  obtain ⟨n, hn, hnW, hrefl, e, he⟩ := hF
  intro g hg
  obtain ⟨w, hw⟩ := e.surjective ⟨g, hg⟩
  have hval : ((e w : ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
      (ggGamma L hN).range)) : MulAut ↥(ggGamma L hN).range) = g := congrArg Subtype.val hw
  rw [← hval]
  have hw' : w ∈ Subgroup.closure (Set.range (CoxeterMatrix.A k).simple) := by
    rw [show Subgroup.closure (Set.range (CoxeterMatrix.A k).simple) = ⊤ by
      simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
        (CoxeterMatrix.A k).toCoxeterSystem.subgroup_closure_range_simple]
    exact Subgroup.mem_top w
  refine Subgroup.closure_induction
    (p := fun w _ => ((e w : ↥(ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
      (ggGamma L hN).range)) : MulAut ↥(ggGamma L hN).range) ∈
        Subgroup.closure (ggTorusReflSet p (ggGamma L hN).range)) ?_ ?_ ?_ ?_ hw'
  · rintro _ ⟨i, rfl⟩
    rw [he i]
    exact Subgroup.subset_closure ⟨n i, hn i, hnW i, rfl, hrefl i⟩
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    rw [map_inv]
    exact Subgroup.inv_mem _ hx

theorem ggUdRow_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ k : ℕ, 4 ≤ k ∧ GGWeylFrame p (ggGamma L hN).range (CoxeterMatrix.A k) ∧
      ∀ N : Subgroup (MulAut ↥(ggGamma L hN).range),
        N ≤ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range →
        (∀ g ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range,
          ∀ m ∈ N, g * m * g⁻¹ ∈ N) →
        N ≠ ⊥ → ∀ v : ↥(ggGamma L hN).range, (∀ m ∈ N, m v = v) → v = 1 := by
  classical
  obtain ⟨hp, -, -, -, -⟩ := hHyp.1.tableB_facts
  obtain ⟨d, n, K, hKf, hKn, ψ, I, hd, hn, hpd, hpq, hK, hI, hTB, hcard⟩ :=
    ggSudRow_tbGroup hHyp hL hN
  letI : Field K := hKf
  letI : Finite K := hKn
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hsc⟩ := hTB
  have hAI' : ∀ a ∈ (ggGamma L hN).range,
      ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : ↥L, x (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨x, hxI, hx⟩ := hAI a ha
    exact ⟨x, hI hxI, hx⟩
  obtain ⟨hframe, hfix⟩ :=
    ggUdTB_frame hK hn hd hp hpq hpd hψ hker hperf hA hAI' hcard hsc
  exact ⟨d - 1, by omega, hframe, hfix⟩

theorem ggUdRow_tbHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab) p Bs L)
    (hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ιV : Additive ↥Bs ≃+ V) :
    Module.finrank (ZMod p) (ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) ≤ 1 := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨k, -, hF, hfixN⟩ := ggUdRow_frame hHyp hL hN
  have hW := ggUdD_frame_reflSet hN hF
  have hS3 := existsUnique_overGamma_of_weylReflSet (K := L) hp hp2 hBs hSC hNoTr hN hZ hW
  have hker : Nat.card ↥(ggGamma L hN).ker ≤ p := ggUdD_ker_card_le hcfg hN
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutNormalClosure L J Bs, φ b = b) → ggGamma L hN b = 1 := by
    intro b hb
    let N' : Subgroup (MulAut ↥(ggGamma L hN).range) :=
      { carrier := {a | a ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
            (ggGamma L hN).range ∧ ∃ c ∈ ggAutNormalClosure L J Bs, GGOverGamma hN c a}
        one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, GGOverGamma.one⟩
        mul_mem' := by
          rintro a₁ a₂ ⟨ha₁, c₁, hc₁, h₁⟩ ⟨ha₂, c₂, hc₂, h₂⟩
          exact ⟨Subgroup.mul_mem _ ha₁ ha₂, c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, h₁.mul h₂⟩
        inv_mem' := by
          rintro a ⟨ha, c, hc, h⟩
          exact ⟨Subgroup.inv_mem _ ha, c⁻¹, Subgroup.inv_mem _ hc, h.inv⟩ }
    have hle : N' ≤ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (ggGamma L hN).range := fun a ha => ha.1
    have hnorm : ∀ g ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
        (ggGamma L hN).range, ∀ n ∈ N', g * n * g⁻¹ ∈ N' := by
      intro g hgA n hn
      obtain ⟨cg, ⟨hcgA, hcg⟩, -⟩ := hS3 g hgA
      obtain ⟨hnA, cn, hcn, hcnov⟩ := hn
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA hnA) (Subgroup.inv_mem _ hgA),
        cg * cn * cg⁻¹, ggUdD_tb_normal hcgA hcn, (hcg.mul hcnov).mul hcg.inv⟩
    have hne : N' ≠ ⊥ := by
      obtain ⟨a, haJ, ha1⟩ := hJ
      have haL : a ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL haJ
      obtain ⟨g, hgA, hov⟩ := ggUdD_tb_lift hN haL
      intro hbot
      have hgN' : g ∈ N' := ⟨hgA, a, ggUdD_tb_le_normalClosure haJ, hov⟩
      rw [hbot, Subgroup.mem_bot] at hgN'
      subst hgN'
      exact ha1 (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ haL hov)
    have hfixed : ∀ n ∈ N',
        n ((ggGamma L hN).rangeRestrict b) = (ggGamma L hN).rangeRestrict b := by
      rintro n ⟨-, c, hc, hov⟩
      rw [← hov b, hb c hc]
    exact congrArg Subtype.val (hfixN N' hle hnorm hne _ hfixed)
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hmem : ∀ v : ↥(ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)),
      Additive.toMul (ιV.symm (v : V)) ∈ (ggGamma L hN).ker := by
    intro v
    rw [MonoidHom.mem_ker]
    apply hfix
    intro φ hφ
    have hv := mem_ggFixedSubmodule_iff.mp v.2 φ hφ
    have hb : ιV (Additive.ofMul (Additive.toMul (ιV.symm (v : V)))) = (v : V) := by simp
    refine (ggLin_fix_iff (p := p) ιV φ _).mpr ?_
    rw [hb]
    exact hv
  have hcard : Nat.card ↥(ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun v => (⟨Additive.toMul (ιV.symm (v : V)), hmem v⟩ : ↥(ggGamma L hN).ker)) ?_) hker
    intro v₁ v₂ h12
    have h12' : Additive.toMul (ιV.symm (v₁ : V)) = Additive.toMul (ιV.symm (v₂ : V)) :=
      congrArg (fun k : ↥(ggGamma L hN).ker => (k : ↥Bs)) h12
    exact Subtype.ext (ιV.symm.injective (Additive.toMul.injective h12'))
  have hpow : Nat.card ↥(ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) =
      p ^ Module.finrank (ZMod p)
        ↥(ggFixedSubmodule (p := p) ιV (ggAutNormalClosure L J Bs)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rw [hpow] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (by simpa using hcard)

theorem ggExcReflTBWeylDatumQFourOn_rowR5Ud
    (hnc : GGTBJNoncommReflOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab) :
    GGExcReflTBWeylDatumQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab := by
  intro G _ _ p B Bs x L D J hHyp hq hNb hL _
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNT : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  obtain ⟨k, hk, hF, -⟩ := ggUdRow_frame hHyp hL hNL
  have hW : GGWeylOfType p (CoxeterMatrix.A k) (ggAutomizer L Bs) :=
    ggWeylOfType_of_frame hp hp2 hBs hSC hNT hNL hZ hF
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  obtain ⟨hno6, hpar, hdepth⟩ := ggCartanA_pathTree (k := k) ⟨0, by omega⟩ rfl
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, b, -, -, -, hab⟩ := hnc G p B Bs x L D J hHyp hq hNb hL
  have hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1 :=
    ⟨a, ha, fun h => hab (by rw [h, one_mul, mul_one])⟩
  exact ggExcReflTBWeylDatum_of_weylOfType hp2 hNT (M := CoxeterMatrix.A k)
    (Or.inl ⟨k, Equiv.refl _, by omega,
      Or.inl (CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)).symm⟩)
    (by rw [Fintype.card_fin]; omega) (ggIntCartan_A k) hno6 (ggPathPar k) ⟨0, by omega⟩
    (fun i => i.1)
    hpar hdepth hW ιV (Or.inr (ggUdRow_tbHyp hHyp hL hJ ιV))

end CFSG.StandardType

end
