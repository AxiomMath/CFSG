module

public import CFSG.LocalAnalysis.StandardType.GGTwE6BadModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcReflLinear
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyHypG0
import CFSG.LocalAnalysis.StandardType.GGE6ThreeAdInvariant
import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem tb_normal {G : Type} [Group G] {Bs L J : Subgroup G} {c : MulAut ↥Bs}
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

private theorem tb_le_normalClosure {G : Type} [Group G] {Bs L J : Subgroup G} {a : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer J Bs) : a ∈ ggAutNormalClosure L J Bs := by
  have haI : a ∈ ggInduced J Bs := by
    rw [ggAutomizer_eq] at ha
    exact ha
  apply Subgroup.subset_closure
  exact ⟨1, one_mem_ggInduced L Bs, a, haI, by group⟩

private theorem tb_lift {G : Type} [Group G] {Bs K : Subgroup G}
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

theorem ggTwE6Bad_tbHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGTwE6BadLabel p Bs L) (hJ : ∃ a ∈ ggAutomizer J Bs, a ≠ 1)
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
  have hp3 : p = 3 := by
    obtain ⟨-, _, _, hraw⟩ := hL
    obtain ⟨_, _, _, _, _, _, _, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP.2.1
  subst hp3
  obtain ⟨Φ, T, w, h⟩ := ggTwE6Bad_model hHyp hL hN
  have hW : ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range (ggGamma L hN).range ≤
      Subgroup.closure (ggTorusReflSet 3 (ggGamma L hN).range) :=
    h.automizer_le_reflGen.trans
      (Subgroup.closure_mono (Set.range_subset_iff.mpr h.conjAut_mem_ggTorusReflSet))
  have hS3 := existsUnique_overGamma_of_weylReflSet (K := L) hp hp2 hBs hSC hNoTr hN hZ hW
  have hker : Nat.card ↥(ggGamma L hN).ker ≤ 3 := by
    have hpow : ∀ g : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)), g ^ 3 = 1 :=
      fun g => Subtype.ext (hBs.2 g g.2.1)
    have hPG : IsPGroup 3 ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      fun g => ⟨1, by rw [pow_one]; exact hpow g⟩
    have hcyc : IsCyclic ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      hcfg.1.2.2.2.2.2.2.1.2.2.2.2 _ inf_le_right hPG
    have hexp : Monoid.exponent ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    rw [IsCyclic.exponent_eq_card] at hexp
    have hS3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hexp
    exact le_trans (Nat.card_le_card_of_injective
      (fun k : ↥(ggGamma L hN).ker =>
        (⟨(k.1 : G), k.1.2, (ggGamma_eq_one_iff L hN k.1).mp k.2⟩ :
          ↥(Bs ⊓ Subgroup.centralizer (L : Set G))))
      (fun k₁ k₂ hk => Subtype.ext (Subtype.ext (congrArg
        (fun s : ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) => (s : G)) hk)))) hS3
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
    have hle : N' ≤ Subgroup.closure (Set.range h.conjAut) := by
      intro a ha
      rw [← h.automizer_eq_reflGen]
      exact ha.1
    have hnorm : ∀ g ∈ Subgroup.closure (Set.range h.conjAut), ∀ n ∈ N', g * n * g⁻¹ ∈ N' := by
      intro g hg n hn
      have hgA : g ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
          (ggGamma L hN).range := by
        rw [h.automizer_eq_reflGen]
        exact hg
      obtain ⟨cg, ⟨hcgA, hcg⟩, -⟩ := hS3 g hgA
      obtain ⟨hnA, cn, hcn, hcnov⟩ := hn
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA hnA) (Subgroup.inv_mem _ hgA),
        cg * cn * cg⁻¹, tb_normal hcgA hcn, (hcg.mul hcnov).mul hcg.inv⟩
    have hne : N' ≠ ⊥ := by
      obtain ⟨a, haJ, ha1⟩ := hJ
      have haL : a ∈ ggAutomizer L Bs := ggAutomizer_mono Bs hJL haJ
      obtain ⟨g, hgA, hov⟩ := tb_lift hN haL
      intro hbot
      have hgN' : g ∈ N' := ⟨hgA, a, tb_le_normalClosure haJ, hov⟩
      rw [hbot, Subgroup.mem_bot] at hgN'
      subst hgN'
      exact ha1 (eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ haL hov)
    have hfixed : ∀ n ∈ N',
        n ((ggGamma L hN).rangeRestrict b) = (ggGamma L hN).rangeRestrict b := by
      rintro n ⟨-, c, hc, hov⟩
      rw [← hov b, hb c hc]
    exact congrArg Subtype.val (h.eq_one_of_fixed_normal hle hnorm hne hfixed)
  have hfin : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  have : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hmem : ∀ v : ↥(ggFixedSubmodule (p := 3) ιV (ggAutNormalClosure L J Bs)),
      Additive.toMul (ιV.symm (v : V)) ∈ (ggGamma L hN).ker := by
    intro v
    rw [MonoidHom.mem_ker]
    apply hfix
    intro φ hφ
    have hv := mem_ggFixedSubmodule_iff.mp v.2 φ hφ
    have hb : ιV (Additive.ofMul (Additive.toMul (ιV.symm (v : V)))) = (v : V) := by simp
    refine (ggLin_fix_iff (p := 3) ιV φ _).mpr ?_
    rw [hb]
    exact hv
  have hcard : Nat.card ↥(ggFixedSubmodule (p := 3) ιV (ggAutNormalClosure L J Bs)) ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun v => (⟨Additive.toMul (ιV.symm (v : V)), hmem v⟩ : ↥(ggGamma L hN).ker)) ?_) hker
    intro v₁ v₂ h12
    have h12' : Additive.toMul (ιV.symm (v₁ : V)) = Additive.toMul (ιV.symm (v₂ : V)) :=
      congrArg (fun k : ↥(ggGamma L hN).ker => (k : ↥Bs)) h12
    exact Subtype.ext (ιV.symm.injective (Additive.toMul.injective h12'))
  have hpow : Nat.card ↥(ggFixedSubmodule (p := 3) ιV (ggAutNormalClosure L J Bs)) =
      3 ^ Module.finrank (ZMod 3) ↥(ggFixedSubmodule (p := 3) ιV (ggAutNormalClosure L J Bs)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  rw [hpow] at hcard
  have h31 : 3 ^ Module.finrank (ZMod 3)
      ↥(ggFixedSubmodule (p := 3) ιV (ggAutNormalClosure L J Bs)) ≤ 3 ^ 1 := by
    simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h31

end CFSG.StandardType

end
