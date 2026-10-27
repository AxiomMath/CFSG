module

public import CFSG.LocalAnalysis.StandardType.GGTBWInputDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProofFork

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRealized {G : Type} [Group G] [Finite G] (p : ℕ) (Bs : Subgroup G)
    (t : MulAut ↥Bs) : Prop :=
  ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧
    Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) ∧
    IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G)))

@[expose] def GGFixedRealizedInL {G : Type} [Group G] [Finite G] (p : ℕ) (Bs L : Subgroup G)
    (x : G) : Prop :=
  ∀ t : MulAut ↥Bs, GGIsReflection p t → t ∈ ggInduced ⊤ Bs → x ∈ ggFixG Bs t →
    GGRealized p Bs t → t ∈ ggAutomizer L Bs

theorem eq_ggConjAut_of_mem_ggAutomizer {G : Type} [Group G] [Finite G] {Bs H : Subgroup G}
    {w : MulAut ↥Bs} (hw : w ∈ ggAutomizer H Bs) :
    ∃ g ∈ H, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G), w = ggConjAut Bs hg := by
  obtain ⟨g, hgH, hgN, hw⟩ := mem_ggAutomizer_iff.mp hw
  exact ⟨g, hgH, hgN, MulEquiv.ext fun b => Subtype.ext (hw b)⟩

theorem GGRealized.conj {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) {t : MulAut ↥Bs} (ht : GGRealized p Bs t) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    GGRealized p Bs (ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) := by
  obtain ⟨Jt, hind, hJC, hpc⟩ := ht
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨Jt.map (MulAut.conj g).toMonoidHom, mem_ggInduced_map_conj hg hind, ?_, ?_⟩
  · rw [ggFixG_conj hg, centralizer_map_conj]
    exact Subgroup.map_mono hJC
  · rw [ggFixG_conj hg, centralizer_map_conj]
    exact (CFSG.ComponentClassification.Burgoyne.isPComponent_subgroupOf_map_iff p hp hf).mp hpc

theorem GGRealized.mem_ggInduced_top {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    {t : MulAut ↥Bs} (ht : GGRealized p Bs t) : t ∈ ggInduced ⊤ Bs := by
  obtain ⟨Jt, ⟨g, -, hgN, hg⟩, -, -⟩ := ht
  exact ⟨g, Subgroup.mem_top g, hgN, hg⟩

theorem ggCell_false_of_witness {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}
    (hp : p.Prime) {x : G} {L : Subgroup G} (h847 : GGFixedRealizedInL p Bs L x) {Λ : Type}
    {φ : Λ → MulAut ↥Bs} (hW : GGReflConjSimple p (ggAutomizer L Bs) φ) {ψ r : MulAut ↥Bs}
    (hψ : ψ ∈ ggAutomizer ⊤ Bs) (hr : GGIsReflection p r) (hrR : GGRealized p Bs r)
    (hx : x ∈ ggFixG Bs (ψ * r * ψ⁻¹))
    (hnot : ∀ w ∈ ggAutomizer L Bs, ∀ i, ψ * r * ψ⁻¹ ≠ w * φ i * w⁻¹) : False := by
  obtain ⟨g, -, hg, rfl⟩ := eq_ggConjAut_of_mem_ggAutomizer hψ
  have hR := hrR.conj hp hg
  have hL := h847 _ (hr.conj' _) hR.mem_ggInduced_top hx hR
  obtain ⟨w, hw, i, he⟩ := hW _ hL (hr.conj' _)
  exact hnot w hw i he

end CFSG.StandardType
