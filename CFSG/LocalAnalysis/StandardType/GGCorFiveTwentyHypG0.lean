module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Closure

variable {G : Type} [Group G]

@[expose] def ggAutNormalClosure (L J Bs : Subgroup G) : Subgroup (MulAut ↥Bs) :=
  Subgroup.closure {φ | ∃ c ∈ ggInduced L Bs, ∃ a ∈ ggInduced J Bs, φ = c * a * c⁻¹}

theorem exists_ggConjAut_eq_of_mem_ggInduced {H Bs : Subgroup G} {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggInduced H Bs) :
    ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)), g ∈ H ∧ ggConjAut Bs hg = φ := by
  obtain ⟨g, hgH, hgN, hg⟩ := hφ
  exact ⟨g, hgN, hgH, MulEquiv.ext fun b => Subtype.ext (hg b).symm⟩

end Closure

section Gen

variable {G : Type} [Group G] [Finite G]

theorem commutes_ggAutNormalClosure_of_not_le {p : ℕ} (hp : p.Prime) {Bs L J G₀ : Subgroup G}
    (hLG₀ : L ≤ G₀)
    (hD : ∀ (t : MulAut ↥Bs) (Jt : Subgroup G), GGIsReflection p t → t ∈ ggInduced Jt Bs →
      Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) →
      IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))) →
      Jt ≤ G₀ ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t)
    {t : MulAut ↥Bs} {Jt : Subgroup G} (hr : GGIsReflection p t) (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))))
    (hJt : ¬ Jt ≤ G₀) :
    ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t := by
  have hle : ggAutNormalClosure L J Bs ≤ Subgroup.centralizer ({t} : Set (MulAut ↥Bs)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨c, hc, a, ha, rfl⟩
    have hc' : c⁻¹ ∈ ggInduced L Bs := (ggInducedSubgroup L Bs).inv_mem hc
    obtain ⟨w, hwN, hwL, hw⟩ := exists_ggConjAut_eq_of_mem_ggInduced hc'
    have hf : Function.Injective (MulAut.conj w).toMonoidHom := (MulAut.conj w).injective
    rcases hD (ggConjAut Bs hwN * t * (ggConjAut Bs hwN)⁻¹) (Jt.map (MulAut.conj w).toMonoidHom)
        (hr.conj' _) (mem_ggInduced_map_conj hwN hind)
        (by rw [ggFixG_conj hwN, centralizer_map_conj]; exact Subgroup.map_mono hJC)
        (by
          rw [ggFixG_conj hwN, centralizer_map_conj]
          exact (CFSG.ComponentClassification.Burgoyne.isPComponent_subgroupOf_map_iff p hp
            hf).mp hpc) with hle | hcomm
    ·
      refine absurd (fun y hy => ?_) hJt
      have h1 : w * y * w⁻¹ ∈ G₀ := hle ⟨y, hy, rfl⟩
      have h2 : w⁻¹ * (w * y * w⁻¹) * w ∈ G₀ :=
        G₀.mul_mem (G₀.mul_mem (G₀.inv_mem (hLG₀ hwL)) h1) (hLG₀ hwL)
      rwa [show w⁻¹ * (w * y * w⁻¹) * w = y by group] at h2
    ·
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff] at hs
      subst hs
      have h := hcomm a ha
      rw [hw, inv_inv] at h
      calc s * (c * a * c⁻¹) = c * ((c⁻¹ * s * c) * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * s * c)) * c⁻¹ := by rw [h]
        _ = c * a * c⁻¹ * s := by group
  intro φ hφ
  exact Subgroup.mem_centralizer_iff.mp (hle hφ) t rfl

end Gen

@[expose] def GGHypDichotomyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        ∀ (t : MulAut ↥Bs) (Jt : Subgroup G), GGIsReflection p t → t ∈ ggInduced Jt Bs →
          Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) →
          IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))) →
          Jt ≤ ggG0 p B x L D J ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t

@[expose] def GGExcReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDom p B Bs x L D J →
        ∃ ρ : MulAut ↥Bs, ∀ t : MulAut ↥Bs, GGIsReflection p t → t ∈ ggAutomizer ⊤ Bs →
          (∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) → t = ρ

theorem ggHypG0Input_of_dichotomy (hD : GGHypDichotomyInput) (hE : GGExcReflInput) :
    GGHypG0Input := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW
  obtain ⟨ρ, hρ⟩ := hE G p B Bs x L D J hHyp hq hN hW
  refine ⟨ρ, fun t Jt htρ hr hind hJC hpc => ?_⟩
  by_contra hJt
  refine htρ (hρ t hr ?_ ?_)
  · obtain ⟨g, -, hgN, hg⟩ := hind
    exact mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top g, hgN, hg⟩
  · exact commutes_ggAutNormalClosure_of_not_le hHyp.1.1.2.2.2.2.2.1.1 (le_ggG0_left p B x L D J)
      (hD G p B Bs x L D J hHyp hq hN hW) hr hind hJC hpc hJt

end CFSG.StandardType
