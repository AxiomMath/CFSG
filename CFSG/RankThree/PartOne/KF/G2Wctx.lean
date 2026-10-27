module

public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog

variable {p : ℕ} {K : Type} [Field K]

@[expose] noncomputable def weylM
    (K : Type) [Field K] (i : Fin Tag.G2.rank) : ↥(adjointGroup .G2 K) :=
  ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩

theorem exists_wctx_g2
    [Finite K] (σ : Fin Tag.G2.rank → MulAut (Fin Tag.G2.rank → rootsOfUnity p K))
    (hσ : ∀ i b, tpHom p K (σ i b) =
      weylElt .G2 K i 1 * tpHom p K b * (weylElt .G2 K i 1)⁻¹) :
    Nonempty (WCtx (Subgroup.closure (Set.range σ)).subtype (⊤ : Subgroup ↥(adjointGroup .G2 K))
      (Tp p K)) := by
  classical
  set D := Subgroup.closure (Set.range σ) with hD
  let tor : (Fin Tag.G2.rank → rootsOfUnity p K) ≃* ↥(Tp p K) :=
    MonoidHom.ofInjective tpM_injective
  have htor : ∀ b, ((tor b : ↥(Tp p K)) : ↥(adjointGroup .G2 K)) = tpM p K b := fun b => rfl
  have hconjM : ∀ (i : Fin Tag.G2.rank) (b : Fin Tag.G2.rank → rootsOfUnity p K),
      weylM K i * tpM p K b * (weylM K i)⁻¹ = tpM p K (σ i b) := fun i b =>
    Subtype.ext (hσ i b).symm
  have hnorm : ∀ i : Fin Tag.G2.rank, weylM K i ∈
      Subgroup.normalizer
        ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K)) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨b, rfl⟩
      rw [hconjM]
      exact tpM_mem_Tp _
    · rintro ⟨b, hb⟩
      refine ⟨(σ i).symm b, ?_⟩
      have h1 := hconjM i ((σ i).symm b)
      rw [MulEquiv.apply_symm_apply, hb] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hact : ∀ (i : Fin Tag.G2.rank) (hg : weylM K i ∈ Subgroup.normalizer
      ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K))),
      (Tp p K).normalizerMonoidHom ⟨weylM K i, hg⟩ = MulAut.congr tor (σ i) := by
    intro i hg
    refine MulEquiv.ext fun t => ?_
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    exact hconjM i b
  have key : ∀ γ ∈ D, ∃ (g : ↥(adjointGroup .G2 K)) (hg : g ∈ Subgroup.normalizer
      ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K))),
      (Tp p K).normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨weylM K i, hnorm i, hact i (hnorm i)⟩
    | one => exact ⟨1, Subgroup.one_mem _, by
        rw [show (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer
          ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K))) = 1 from rfl,
          map_one, map_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨g₁, hg₁, h₁⟩ := ihx
      obtain ⟨g₂, hg₂, h₂⟩ := ihy
      exact ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, by
        rw [show (⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂⟩ : Subgroup.normalizer
          ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K))) =
          ⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ from rfl, map_mul, map_mul, h₁, h₂]⟩
    | inv x _ ih =>
      obtain ⟨g, hg, h⟩ := ih
      exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by
        rw [show (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : Subgroup.normalizer
          ((Tp p K : Subgroup ↥(adjointGroup .G2 K)) : Set ↥(adjointGroup .G2 K))) =
          (⟨g, hg⟩)⁻¹ from rfl, map_inv, map_inv, h]⟩
  have hprod : ∀ ω : List (Fin Tag.G2.rank), ∃ δ ∈ D, ∀ b,
      (ω.map fun i => weylElt .G2 K i 1).prod * tpHom p K b *
        ((ω.map fun i => weylElt .G2 K i 1).prod)⁻¹ = tpHom p K (δ b) := by
    intro ω
    induction ω with
    | nil => exact ⟨1, Subgroup.one_mem _, fun b => by simp⟩
    | cons i ω ih =>
      obtain ⟨δ, hδ, h⟩ := ih
      refine ⟨σ i * δ, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hδ, fun b => ?_⟩
      have e : (((i :: ω).map fun i => weylElt .G2 K i 1).prod) *
          tpHom p K b * (((i :: ω).map fun i => weylElt .G2 K i 1).prod)⁻¹ =
          weylElt .G2 K i 1 * ((ω.map fun i => weylElt .G2 K i 1).prod * tpHom p K b *
            ((ω.map fun i => weylElt .G2 K i 1).prod)⁻¹) * (weylElt .G2 K i 1)⁻¹ := by
        simp only [List.map_cons, List.prod_cons, mul_inv_rev]
        group
      rw [e, h b, ← hσ i]
      rfl
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, hg, h⟩ := key γ hγ
    exact ⟨g, hg, Subgroup.mem_top _, h⟩
  · intro g hg _
    obtain ⟨w, hw⟩ := exists_weyl_conj_of_mem_adjointGroup g.2
    obtain ⟨ω, hω⟩ := exists_list_canonicalRep_eq (K := K) w
    obtain ⟨δ, hδ, hδb⟩ := hprod ω
    refine ⟨⟨δ, hδ⟩, MulEquiv.ext fun t => ?_⟩
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    have h1 : g * tpM p K b * g⁻¹ ∈ Tp p K := (Subgroup.mem_normalizer_iff.mp hg _).mp
      (tpM_mem_Tp b)
    obtain ⟨b', hb'⟩ := h1
    have h2 : (g : ModGL .G2 K) * tpHom p K b * (g : ModGL .G2 K)⁻¹ = tpHom p K b' :=
      (congrArg Subtype.val hb').symm
    have h3 := hw (fun i => ((b' i : rootsOfUnity p K) : Kˣ))
      (fun i => ((b i : rootsOfUnity p K) : Kˣ)) h2
    rw [hω] at h3
    have h4 : tpHom p K b' = tpHom p K (δ b) := h3.trans (hδb b)
    have h5 : b' = δ b := tpHom_injective h4
    show g * ((tor b : ↥(Tp p K)) : ↥(adjointGroup .G2 K)) * g⁻¹ =
      ((tor (δ b) : ↥(Tp p K)) : ↥(adjointGroup .G2 K))
    rw [htor, htor, ← h5]
    exact hb'.symm

end CFSG.RankThree.PartOne.KFU
