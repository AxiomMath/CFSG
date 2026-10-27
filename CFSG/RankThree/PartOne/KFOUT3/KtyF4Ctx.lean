module

public import CFSG.RankThree.PartOne.KF.F4Wctx

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.SectionRank.LargeRee
  CFSG.LieType.Ree.LargeReeCover CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Simplicity

variable {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_wctx_f4'
    (h : F4Param p a K)
    (τ : Fin 2 → MulAut (Fin 2 → rootsOfUnity p K))
    (hτ : ∀ i b, tp4Hom p a K (τ i b) =
      ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K) * tp4Hom p a K b *
        ((nGamma (blockGen i) : ↥(F4.reeGamma K a)) : ModGL F4.tag K)⁻¹) :
    ∃ S : WCtx (Subgroup.closure (Set.range τ)).subtype (⊤ : Subgroup ↥(F4.reeGamma K a))
      (Tp4 h), ∀ b, ((S.tor b : ↥(Tp4 h)) : ↥(F4.reeGamma K a)) = tp4M h b := by
  classical
  set D := Subgroup.closure (Set.range τ) with hD
  let tor : (Fin 2 → rootsOfUnity p K) ≃* ↥(Tp4 h) := MonoidHom.ofInjective (tp4M_injective h)
  have htor : ∀ b, ((tor b : ↥(Tp4 h)) : ↥(F4.reeGamma K a)) = tp4M h b := fun b => rfl
  let n : Fin 2 → ↥(F4.reeGamma K a) := fun i => nGamma (blockGen i)
  have hconjM : ∀ i b, n i * tp4M h b * (n i)⁻¹ = tp4M h (τ i b) := fun i b =>
    Subtype.ext (hτ i b).symm
  have hnorm : ∀ i, n i ∈ Subgroup.normalizer
      ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a)) := by
    intro i
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨b, rfl⟩
      rw [hconjM]
      exact tp4M_mem_Tp4 h _
    · rintro ⟨b, hb⟩
      refine ⟨(τ i).symm b, ?_⟩
      have h1 := hconjM i ((τ i).symm b)
      rw [MulEquiv.apply_symm_apply, hb] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hact : ∀ (i : Fin 2) (hg : n i ∈ Subgroup.normalizer
      ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))),
      (Tp4 h).normalizerMonoidHom ⟨n i, hg⟩ = MulAut.congr tor (τ i) := by
    intro i hg
    refine MulEquiv.ext fun t => ?_
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    exact hconjM i b
  have key : ∀ γ ∈ D, ∃ (g : ↥(F4.reeGamma K a))
      (hg : g ∈ Subgroup.normalizer
        ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))),
      (Tp4 h).normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨n i, hnorm i, hact i (hnorm i)⟩
    | one => exact ⟨1, Subgroup.one_mem _, by
        rw [show (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer
          ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))) = 1 from rfl,
          map_one, map_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨g₁, hg₁, h₁⟩ := ihx
      obtain ⟨g₂, hg₂, h₂⟩ := ihy
      exact ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, by
        rw [show (⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂⟩ : Subgroup.normalizer
          ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))) =
          ⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ from rfl, map_mul, map_mul, h₁, h₂]⟩
    | inv x _ ih =>
      obtain ⟨g, hg, h'⟩ := ih
      exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by
        rw [show (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : Subgroup.normalizer
          ((Tp4 h : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a))) =
          (⟨g, hg⟩)⁻¹ from rfl, map_inv, map_inv, h']⟩
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }, fun b => rfl⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, hg, hγg⟩ := key γ hγ
    exact ⟨g, hg, Subgroup.mem_top _, hγg⟩
  · intro g hg _
    have hg1 : (g : ModGL F4.tag K) ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := g.2
    rw [reeGamma_eq_iUnion_reeFixedBruhatCell, Set.mem_iUnion] at hg1
    obtain ⟨w, hw⟩ := hg1
    have hw' := reeFixedBruhatCell_subset_bruhatCell (K := K) (a := a) w.1 hw
    obtain ⟨δ, hδ, hδb⟩ := exists_action_nGamma (a := a) τ hτ w
    refine ⟨⟨δ, hδ⟩, MulEquiv.ext fun t => ?_⟩
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    have h1 : g * tp4M h b * g⁻¹ ∈ Tp4 h :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (tp4M_mem_Tp4 h b)
    obtain ⟨b', hb'⟩ := h1
    have h2 : (g : ModGL F4.tag K) * tp4Hom p a K b * (g : ModGL F4.tag K)⁻¹ =
        tp4Hom p a K b' := (congrArg Subtype.val hb').symm
    obtain ⟨c, hc⟩ := exists_eq_rootDiagUnit_of_mem_torusGroup
      (tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) b)
    obtain ⟨c', hc'⟩ := exists_eq_rootDiagUnit_of_mem_torusGroup
      (tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) b')
    have h3 := rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell_of_mem_torus c' c
      (hc' ▸ tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) b')
      (hc ▸ tp4Hom_mem_torusGroup (p := p) (a := a) (K := K) b) hw'
      (by rw [← hc, ← hc']; exact h2)
    rw [← hc, ← hc'] at h3
    have h4 : tp4Hom p a K b' = tp4Hom p a K (δ b) := h3.trans (hδb b)
    have h5 : b' = δ b := tp4M_injective h (Subtype.ext h4)
    show g * ((tor b : ↥(Tp4 h)) : ↥(F4.reeGamma K a)) * g⁻¹ =
      ((tor (δ b) : ↥(Tp4 h)) : ↥(F4.reeGamma K a))
    rw [htor, htor, ← h5]
    exact hb'.symm

end CFSG.RankThree.PartOne.KFOUT3
