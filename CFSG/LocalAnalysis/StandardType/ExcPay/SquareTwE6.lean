module

public import CFSG.LocalAnalysis.StandardType.ExcPay.SquareGen
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

import CFSG.LocalAnalysis.StandardType.ExcPay.WeylTwE6

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] noncomputable def excPayTp {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) : Subgroup ↥M.D.Γ :=
  ((powMonoidHom p : (Fin (langTag t).rank → GGLˣ) →* (Fin (langTag t).rank → GGLˣ)).ker.map
    (rootDiagUnitHom (langTag t) GGL)).subgroupOf M.D.Γ

private lemma excPayY6_center_top_eq_bot {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) : Subgroup.center ↥(⊤ : Subgroup G) = ⊥ := by
  have hmap := Subgroup.map_center_eq
    (Subgroup.topEquiv (G := G) : ↥(⊤ : Subgroup G) ≃* G)
  rw [hZ] at hmap
  have hinj : Function.Injective
      ((Subgroup.topEquiv (G := G) : ↥(⊤ : Subgroup G) ≃* G) :
        ↥(⊤ : Subgroup G) →* G) :=
    (Subgroup.topEquiv (G := G) : ↥(⊤ : Subgroup G) ≃* G).injective
  exact (Subgroup.map_eq_bot_iff_of_injective
    (Subgroup.center ↥(⊤ : Subgroup G)) hinj).mp hmap

private lemma excPayY6_mem_tp_iff {p f : ℕ} {ht : GGExcFive .twistedE6}
    (M : GGDatumModel .twistedE6 f p ht) (z : ↥M.D.Γ) :
    z ∈ excPayTp M ↔ ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
      (∀ i, a i ^ p = 1) ∧
        rootDiagUnit (langTag .twistedE6) a = (z : ModGL (langTag .twistedE6) GGL) := by
  rw [excPayTp, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    refine ⟨a, fun i => ?_, hay⟩
    have h := MonoidHom.mem_ker.1 ha
    simpa [powMonoidHom_apply] using congrFun h i
  · rintro ⟨a, ha, haz⟩
    exact ⟨a, MonoidHom.mem_ker.2 (funext fun i => by
      simpa [powMonoidHom_apply] using ha i), haz⟩

theorem exists_excPaySquareY_TwE6 {p f : ℕ} {ht : GGExcFive .twistedE6} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .twistedE6 f p ht)
    [Finite ↥M.D.Γ] (hZ : Subgroup.center ↥M.D.Γ = ⊥)
    (hTp : ∀ a : Fin (langTag .twistedE6).rank → GGLˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit (langTag .twistedE6) a ∈ M.D.Γ) :
    ∃ S : ExcPaySquare .twistedE6 ht f p (excPayTp M) ⊤, ∀ k,
      ∃ (g : ↥M.D.Γ) (hg : g ∈ Subgroup.normalizer (excPayTp M : Set ↥M.D.Γ)),
        S.s k = ggConjAut (excPayTp M) hg := by
  have hp2 : p ≠ 2 := by omega
  have hZtop : Subgroup.center ↥(⊤ : Subgroup ↥M.D.Γ) = ⊥ :=
    excPayY6_center_top_eq_bot hZ
  have hsplit : ∀ b ∈ excPayTp M,
      ∃ x ∈ (⊤ : Subgroup ↥M.D.Γ) ⊓ excPayTp M,
        b * x⁻¹ ∈ Subgroup.centralizer ((⊤ : Subgroup ↥M.D.Γ) : Set ↥M.D.Γ) := by
    intro b hb
    refine ⟨b, ⟨Subgroup.mem_top b, hb⟩, ?_⟩
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  have hη : ∀ z : ModGL (langTag .twistedE6) GGL,
      (∃ x : ↥(⊤ : Subgroup ↥M.D.Γ), (x : ↥M.D.Γ) ∈ excPayTp M ∧
        ((Subgroup.topEquiv x : ↥M.D.Γ) : ModGL (langTag .twistedE6) GGL) = z) ↔
        ∃ a : Fin (langTag .twistedE6).rank → GGLˣ,
          (∀ i, a i ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) a = z := by
    intro z
    constructor
    · rintro ⟨x, hx, hxz⟩
      obtain ⟨a, ha, hay⟩ := (excPayY6_mem_tp_iff M (x : ↥M.D.Γ)).mp hx
      exact ⟨a, ha, hay.trans (by simpa using hxz)⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨⟨rootDiagUnit (langTag .twistedE6) a, hTp a ha⟩, Subgroup.mem_top _⟩,
        ?_, ?_⟩
      · exact (excPayY6_mem_tp_iff M _).mpr ⟨a, ha, rfl⟩
      · rfl
  have hnk : ∀ k, canonicalRep (coxeterSystem (langTag .twistedE6)) GGL
      (simple (langTag .twistedE6) k) ∈ M.D.Γ :=
    fun k => canonicalRep_simple_mem_Γ_TwE6 hf hplus M k
  obtain ⟨S, hS⟩ := exists_excPaySquare_of_model (G := ↥M.D.Γ) (X := ⊤)
    (Bs := excPayTp M) (ht := ht) hp hp2 M
    (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥M.D.Γ) ≃* ↥M.D.Γ) hη hsplit hZtop hnk
  refine ⟨S, fun k => ?_⟩
  obtain ⟨g, hg, -, hgk⟩ := hS k
  exact ⟨g, hg, hgk⟩

end CFSG.StandardType.ExcPay
