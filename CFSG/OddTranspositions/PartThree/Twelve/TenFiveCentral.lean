module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModel
public import CFSG.OddTranspositions.PartThree.Twelve.Four
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.OddTranspositions.FusionStep
public import CFSG.GroupTheory.ClosureDiffImage
public import CFSG.GroupTheory.LocalLift.NormalizerQuotient
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

theorem mem_commutator_or_mul_mem_of_setup {H : Type} [Group H] {E : Set H}
    (hH : Setup H E) {d : H} (hd : d ∈ E) :
    ∀ h : H, h ∈ commutator H ∨ d * h ∈ commutator H := by
  intro h
  set t : Abelianization H := Abelianization.of d with ht
  have ht2 : t * t = 1 := by
    rw [ht, ← map_mul, hH.oddT.mul_self_eq_one hd, map_one]
  have htop : (⊤ : Subgroup (Abelianization H)) = Subgroup.zpowers t := by
    refine (eq_top_iff.mpr ?_).symm
    rintro x -
    obtain ⟨g, rfl⟩ : ∃ g : H, Abelianization.of g = x := QuotientGroup.mk_surjective x
    have hg : g ∈ Subgroup.closure E := hH.gen ▸ Subgroup.mem_top g
    have hle : Subgroup.closure E ≤ (Subgroup.zpowers t).comap Abelianization.of := by
      rw [Subgroup.closure_le]
      intro y hy
      show Abelianization.of y ∈ Subgroup.zpowers t
      rw [hH.abelianization_eq hy hd, ← ht]
      exact Subgroup.mem_zpowers _
    exact hle hg
  have hmem : Abelianization.of h ∈ Subgroup.zpowers t := htop ▸ Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hzpow : ∀ n : ℤ, t ^ n = 1 ∨ t ^ n = t := by
    intro n
    induction n using Int.induction_on with
    | zero => exact Or.inl (zpow_zero t)
    | succ n ih =>
      rw [zpow_add_one]
      rcases ih with h1 | h1 <;> rw [h1]
      · exact Or.inr (one_mul t)
      · exact Or.inl ht2
    | pred n ih =>
      rw [zpow_sub_one, show t⁻¹ = t from inv_eq_of_mul_eq_one_right ht2]
      rcases ih with h1 | h1 <;> rw [h1]
      · exact Or.inr (one_mul t)
      · exact Or.inl ht2
  rcases hzpow n with h1 | h1
  · left
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hn ▸ h1
  · right
    rw [← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, ← hn, h1, ht2]

theorem mem_closure_commSet_of_frame {G : Type} [Group G] [Finite G] {D : Set G}
    (hS : Setup G D) {u : G} (hu : u ∈ D) {F : Set G} (hF : F ⊆ commSet D u)
    (hFc : ∀ a ∈ F, ∀ b ∈ F, Commute a b) {f : G} (hf : f ∈ F)
    (hfF : f ∈ Subgroup.closure (F \ {f})) :
    u ∈ Subgroup.closure (commSet D u) := by
  classical
  have hPpair : ∀ x ∈ ({u} ∪ F : Set G), ∀ y ∈ ({u} ∪ F : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | hxF <;> rcases hy with rfl | hyF
    · rfl
    · exact (hF hyF).2.1.eq.symm
    · exact (hF hxF).2.1.eq
    · exact (hFc x hxF y hyF).eq
  have hPsq : ∀ s ∈ ({u} ∪ F : Set G), s * s = 1 := by
    intro s hs
    rcases hs with rfl | hsF
    · exact hS.oddT.mul_self_eq_one hu
    · exact hS.oddT.mul_self_eq_one (hF hsF).1
  have hP2 : IsPGroup 2 (Subgroup.closure ({u} ∪ F : Set G)) :=
    CFSG.EvenSmallLie.ThreeTransposition.isPGroup_closure_of_pairwise hPpair hPsq
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hfP : f ∈ Subgroup.closure ({u} ∪ F : Set G) :=
    Subgroup.subset_closure (Or.inr hf)
  have huP : u ∈ Subgroup.closure ({u} ∪ F : Set G) :=
    Subgroup.subset_closure (Or.inl rfl)
  have hfS : f ∈ S := hPS hfP
  have huS : u ∈ S := hPS huP
  have hfD : f ∈ D := (hF hf).1
  obtain ⟨n, hn, hnf⟩ := sylow_inter_D_transitive hS.isClass hS.oddT S
    (e := f) (f := u) ⟨hfS, hfD⟩ ⟨huS, hu⟩
  have hΔ : MulAut.conj n '' ((S : Set G) ∩ D) = (S : Set G) ∩ D :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hn
  have hsub : F \ {f} ⊆ ((S : Set G) ∩ D) \ {f} := by
    intro x hx
    exact ⟨⟨hPS (Subgroup.subset_closure (Or.inr hx.1)), (hF hx.1).1⟩, hx.2⟩
  have hf_closure : f ∈ Subgroup.closure (((S : Set G) ∩ D) \ {f}) :=
    Subgroup.closure_mono hsub hfF
  have hconj := CFSG.GroupTheory.conj_mem_closure_diff hΔ hf_closure
  rw [hnf] at hconj
  have hΔcomm : ((S : Set G) ∩ D) \ {u} ⊆ commSet D u := by
    intro x hx
    exact ⟨hx.1.2, hS.oddT.commute_of_isPGroup S.isPGroup' hx.1.2 hu hx.1.1 huS, hx.2⟩
  exact Subgroup.closure_mono hΔcomm hconj

end CFSG.OddTranspositions.PartThree
