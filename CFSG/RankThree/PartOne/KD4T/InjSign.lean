module

public import CFSG.RankThree.PartOne.KD4T.Emb
public import CFSG.LieType.Chevalley.AllRootWeylConjugation

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} [hτ : E6Sub τ]

theorem weylElt_comp_e6Emb {K : Type} [Field K] (k : Fin Tag.E6.rank) (t : Kˣ) :
    (weylElt τ K (e6Idx k) t : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (weylElt Tag.E6 K k t : Module.End K (RootModule Tag.E6 K)) := by
  rw [LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_comp_e6Emb (mul_comp_e6Emb (xOp_comp_e6Emb k _) (yOp_comp_e6Emb k _))
    (xOp_comp_e6Emb k _)

theorem exists_sign_pinnedX_comp_e6Emb {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      (pinnedX τ L (e6Lat τ α) c : Module.End L (RootModule τ L)) ∘ₗ e6Emb τ L =
        e6Emb τ L ∘ₗ (pinnedX Tag.E6 L α ((ε : L) * c) : Module.End L (RootModule Tag.E6 L)) := by
  induction hα with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun L _ c => ?_⟩
    rw [e6Lat_single, pinnedX_single, pinnedX_single, Int.cast_one, one_mul]
    exact xOp_comp_e6Emb j c
  | @reflect i v hv ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hv6 : IsRoot τ (e6Lat τ v) := isRoot_e6Lat_iff.2 hv
    have h6 := (all_root_weyl_infinitesimal.{0} τ).2.2.2.1 (e6Idx i) _ hv6
    have h4 := (all_root_weyl_infinitesimal.{0} Tag.E6).2.2.2.1 i _ hv
    refine ⟨allRootWeylSign Tag.E6 i v * ε * allRootWeylSign τ (e6Idx i) (e6Lat τ v), ?_,
      fun L _ c => ?_⟩
    · rcases h4 with h4 | h4 <;> rcases hε with hε | hε <;> rcases h6 with h6 | h6 <;>
        simp [h4, hε, h6]
    have hσ6 : ((allRootWeylSign τ (e6Idx i) (e6Lat τ v) : L) *
        allRootWeylSign τ (e6Idx i) (e6Lat τ v)) = 1 := by
      rcases h6 with h6 | h6 <;> simp [h6]
    have e6 := weylElt_one_mul_pinnedX_mul_inv L (e6Idx i) hv6
      ((allRootWeylSign τ (e6Idx i) (e6Lat τ v) : L) * c)
    rw [← mul_assoc, hσ6, one_mul, ← e6Lat_reflect] at e6
    have e4 := weylElt_one_mul_pinnedX_mul_inv L i hv
      ((ε : L) * ((allRootWeylSign τ (e6Idx i) (e6Lat τ v) : L) * c))
    have hc : ((allRootWeylSign Tag.E6 i v * ε * allRootWeylSign τ (e6Idx i) (e6Lat τ v) :
        ℤ) : L) * c = (allRootWeylSign Tag.E6 i v : L) *
          ((ε : L) * ((allRootWeylSign τ (e6Idx i) (e6Lat τ v) : L) * c)) := by
      push_cast
      ring
    rw [← e6, hc, ← e4]
    exact mul_comp_e6Emb (mul_comp_e6Emb (weylElt_comp_e6Emb i 1) (h L _))
      (inv_comp_e6Emb (weylElt_comp_e6Emb i 1))

end CFSG.RankThree.PartOne.KD4T
