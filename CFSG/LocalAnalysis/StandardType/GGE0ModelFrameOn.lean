module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrame
public import CFSG.LocalAnalysis.StandardType.GGOuterInvModelData
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.Open (IsElemAbelian)

@[expose] def GGE0AtOn
    (t : StatedLieTag) (R : ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J → R f p →
      ∀ (b : G), b ∈ Bs → b ≠ 1 →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∀ C₀ : Subgroup G, IsComponentOf C₀ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
            GGE0Concl (D.map (MulAut.conj m⁻¹).toMonoidHom) C₀

theorem ggE0At_of_on
    {t : StatedLieTag} {R : ℕ → ℕ → Prop} (h₁ : GGE0AtOn t R)
    (h₂ : GGE0AtOn t (fun f p => ¬ R f p)) : GGE0At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 b hb hb1 m hm hEC C₀ hC₀
  by_cases hR : R f p
  · exact h₁ G p B Bs x L D J n f ψ hctx s1 hR b hb hb1 m hm hEC C₀ hC₀
  · exact h₂ G p B Bs x L D J n f ψ hctx s1 hR b hb hb1 m hm hEC C₀ hC₀

@[expose] def GGE0ModelOn (R : ℕ → Prop) (C : Type) [Group C] (I : Subgroup (MulAut C)) : Prop :=
  ∀ (p : ℕ) (β : MulAut C) (E : Subgroup (MulAut C)), p.Prime → p ≠ 2 → R p → β ≠ 1 →
    β ^ p = 1 → β ∈ I → E ≤ I → (∀ ε ∈ E, ε ^ p = 1) → E ≤ Subgroup.centralizer {β} →
    ∀ X : Subgroup (MulAut C),
      IsComponentOf X ((MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β}) →
        GGE0Concl E X

@[expose] def GGE0ModelDataAtOn
    (t : StatedLieTag) (R : ℕ → ℕ → Prop) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C) (I : Subgroup (MulAut C)),
      Function.Surjective π ∧ π.ker = Subgroup.center (ggU t n f).K ∧ Subgroup.center C = ⊥ ∧
      (MulAut.conj : C →* MulAut C).range ≤ I ∧
      (∀ (G : Type) [Group G] (ψ : (ggU t n f).K →* G), ψ.ker = Subgroup.center (ggU t n f).K →
        ∀ c ∈ Subgroup.normalizer (ψ.range : Set G), GGPsiInnerDiag (ggU t n f).D ψ c →
          ∃ φ ∈ I, ∀ u u', c * ψ u * c⁻¹ = ψ u' → φ (π u) = π u') ∧
      GGE0ModelOn (R f) C I

theorem ggE0AtOn_of_modelData
    {t : StatedLieTag} {R : ℕ → ℕ → Prop} (hG1 : GGE0InG1At t)
    (h : GGE0ModelDataAtOn t R) : GGE0AtOn t R := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hR b hb hb1 m hm hEC C₀ hC₀
  obtain ⟨C, _, π, I, hπ, hπker, hCcen, hInn, hact, hmodel⟩ :=
    h n f hctx.2.2.2.1.1 hctx.2.2.2.1.2
  let N : Subgroup G := Subgroup.normalizer (ggG0 p B x L D J : Set G)
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]; exact s1.1
  have hψ : ψ.ker = Subgroup.center (ggU t n f).K :=
    ggOuterInv_ker_eq_center_of_centralizer ψ hctx.2.2.2.2.1.2 hC'
  obtain ⟨Θ, Φ, hΘ, hΦinj, hΦ⟩ :=
    ggOuterInv_exists_modelHom ψ hctx.range_eq π hπ (hπker.trans hψ.symm) s1.1
  have hΦ_mem : ∀ (y : N) (hy : (y : G) ∈ ggG0 p B x L D J),
      Φ y = MulAut.conj (Θ.symm (⟨(y : G), hy⟩ : ↥(ggG0 p B x L D J))) := by
    intro y hy
    have h1 := ggOuterInv_modelHom_of_mem Θ Φ hΦ (⟨(y : G), hy⟩ : ↥(ggG0 p B x L D J))
    rw [show (⟨(y : G), Subgroup.le_normalizer hy⟩ : N) = y from Subtype.ext rfl] at h1
    exact h1
  have hΦI : ∀ c : N, (c : G) ∈ ggG1 ψ → Φ c ∈ I := by
    intro c hc
    have hcN : (c : G) ∈ Subgroup.normalizer (ψ.range : Set G) := by
      rw [hctx.range_eq]; exact c.2
    obtain ⟨φ, hφI, hφ⟩ := hact G ψ hψ c hcN hc.2
    suffices Φ c = φ by rw [this]; exact hφI
    ext y
    obtain ⟨u, rfl⟩ := hπ y
    obtain ⟨u', hu'⟩ : (c : G) * ψ u * (c : G)⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hcN (ψ u)).mp ⟨u, rfl⟩
    rw [hφ u u' hu'.symm]
    apply Θ.injective
    apply Subtype.ext
    rw [hΦ, hΘ, hΘ, hu']
  have hbG1 : b ∈ ggG1 ψ := ggBs_le_ggG1 hctx hb
  have hbN : b ∈ N := ggG1_le_ggM hctx.range_eq hbG1
  let bN : N := ⟨b, hbN⟩
  let β : MulAut C := Φ bN
  have hβ1 : β ≠ 1 := by
    intro h1
    have h2 : bN = 1 := hΦinj (h1.trans (map_one Φ).symm)
    exact hb1 (Subtype.ext_iff.mp h2)
  have hβp : β ^ p = 1 := by
    have hbN_pow : bN ^ p = 1 := by
      apply Subtype.ext
      simpa using hctx.bstar.2.1.2 b hb
    change (Φ bN) ^ p = 1
    rw [← map_pow, hbN_pow, map_one]
  have hβI : β ∈ I := hΦI bN hbG1
  set E₀ : Subgroup G := D.map (MulAut.conj m⁻¹).toMonoidHom
  have hE₀G1 : E₀ ≤ ggG1 ψ := hG1 G p B Bs x L D J n f ψ hctx s1 m hm
  have hE₀N : E₀ ≤ N := hE₀G1.trans (ggG1_le_ggM hctx.range_eq)
  let E₀' : Subgroup N := E₀.subgroupOf N
  let E : Subgroup (MulAut C) := E₀'.map Φ
  have hE₀_pow : ∀ g ∈ E₀, g ^ p = 1 := by
    rintro g ⟨d, hd, rfl⟩
    rw [← map_pow (MulAut.conj m⁻¹).toMonoidHom d p,
      hctx.bstar.2.1.2 d (hctx.bstar.1 (hctx.stdSub.1.1 hd)), map_one]
  have hE'_pow : ∀ y ∈ E₀', y ^ p = 1 := by
    intro y hy
    apply Subtype.ext
    simpa using hE₀_pow (y : G) hy
  have hEI : E ≤ I := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΦI y (hE₀G1 hy)
  have hEp : ∀ ε ∈ E, ε ^ p = 1 := by
    rintro ε ⟨y, hy, rfl⟩
    rw [← map_pow Φ y p, hE'_pow y hy, map_one]
  have hEβ : E ≤ Subgroup.centralizer {β} := by
    rintro ε ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change Φ y * Φ bN = Φ bN * Φ y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_singleton_iff.mp (hEC hy)
  let K : Subgroup G := ggG0 p B x L D J ⊓ Subgroup.centralizer {b}
  have hKN : K ≤ N := fun x hx => Subgroup.le_normalizer (Subgroup.mem_inf.mp hx).1
  have hC₀N : IsComponentOf (C₀.subgroupOf N) (K.subgroupOf N) :=
    ggIsComponentOf_subgroupOf hC₀ hKN
  let X : Subgroup (MulAut C) := (C₀.subgroupOf N).map Φ
  have hXcomp_map : IsComponentOf X ((K.subgroupOf N).map Φ) :=
    isComponentOf_map_of_injective Φ hΦinj hC₀N
  have hKmap : (K.subgroupOf N).map Φ =
      (MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β} := by
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyK : (y : G) ∈ K := hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hΦ_mem (y := y) (Subgroup.mem_inf.mp hyK).1]
        exact ⟨_, rfl⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        change Φ y * Φ bN = Φ bN * Φ y
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simpa using Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyK).2
    · rintro ⟨hφr, hφc⟩
      obtain ⟨c, rfl⟩ := hφr
      let g : ↥(ggG0 p B x L D J) := Θ c
      let y : N := ⟨(g : G), Subgroup.le_normalizer g.2⟩
      have hΦy : Φ y = MulAut.conj c := by
        have h1 := ggOuterInv_modelHom_of_mem Θ Φ hΦ g
        rw [MulEquiv.symm_apply_apply] at h1
        exact h1
      have hcy : (y : G) ∈ Subgroup.centralizer {b} := by
        have hcβ : Φ y * β = β * Φ y := by
          rw [hΦy]
          exact Subgroup.mem_centralizer_singleton_iff.mp hφc
        have hcommN : y * bN = bN * y := by
          apply hΦinj
          simpa only [map_mul] using hcβ
        have hcommG : (y : G) * b = b * (y : G) := by
          simpa using congrArg (fun w : N => (w : G)) hcommN
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcommG
      exact ⟨y, ⟨g.2, hcy⟩, hΦy⟩
  have hXcomp : IsComponentOf X
      ((MulAut.conj : C →* MulAut C).range ⊓ Subgroup.centralizer {β}) := by
    rw [← hKmap]
    exact hXcomp_map
  have hconcl_model : GGE0Concl E X :=
    hmodel p β E hctx.prime hctx.ne_two hR hβ1 hβp hβI hEI hEp hEβ X hXcomp
  have h_in_N : GGE0Concl E₀' (C₀.subgroupOf N) :=
    (ggE0Concl_map_iff Φ hΦinj E₀' (C₀.subgroupOf N)).mp hconcl_model
  have h_back : GGE0Concl (E₀'.map N.subtype) ((C₀.subgroupOf N).map N.subtype) :=
    (ggE0Concl_map_iff N.subtype N.subtype_injective E₀' (C₀.subgroupOf N)).mpr h_in_N
  rw [Subgroup.map_subgroupOf_eq_of_le hE₀N,
    Subgroup.map_subgroupOf_eq_of_le (hC₀.1.trans hKN)] at h_back
  exact h_back

end CFSG.StandardType
