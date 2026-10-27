module

public import CFSG.RankThree.PartOne.KF.D4Sylow
public import CFSG.RankThree.PartOne.KF.WCtx
public import CFSG.RankThree.PartOne.KF.G2Torus

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {p f : ℕ} {K : Type} [Field K] {σ : K →+* K}

theorem exists_action_canonicalRep_d4
    (τ : Fin TwistTag.D4.foldedTag.rank → MulAut (Fin 2 → rootsOfUnity p K))
    (hτ : ∀ a b, tp3Hom p K (τ a b) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
        tp3Hom p K b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a))⁻¹)
    {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ Subgroup.closure (Set.range TwistTag.D4.orbitReflection)) :
    ∃ δ ∈ Subgroup.closure (Set.range τ), ∀ b,
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * tp3Hom p K b *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ = tp3Hom p K (δ b) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨τ a, Subgroup.subset_closure ⟨a, rfl⟩, fun b => (hτ a b).symm⟩
  | one =>
    refine ⟨1, Subgroup.one_mem _, fun b => ?_⟩
    rw [canonicalRep_one, one_mul, inv_one, mul_one]
    rfl
  | mul x y _ _ ihx ihy =>
    obtain ⟨δx, hδx, hx⟩ := ihx
    obtain ⟨δy, hδy, hy⟩ := ihy
    obtain ⟨k, hk, hkxy⟩ := canonicalRep_mul_mem (R := K) (τ := TwistTag.D4.tag) x y
    refine ⟨δx * δy, Subgroup.mul_mem _ hδx hδy, fun b => ?_⟩
    have hcomm : tp3Hom p K (δx (δy b)) * k = k * tp3Hom p K (δx (δy b)) :=
      rootDiagUnit_mul_comm_of_mem_torusGroup
        (d4Tuple ((δx (δy b) 1 : rootsOfUnity p K) : Kˣ) ((δx (δy b) 0 : rootsOfUnity p K) : Kˣ))
        hk
    have e : canonicalRep (coxeterSystem TwistTag.D4.tag) K (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem TwistTag.D4.tag) K x *
          canonicalRep (coxeterSystem TwistTag.D4.tag) K y) := by
      rw [hkxy, inv_mul_cancel_left]
    calc canonicalRep (coxeterSystem TwistTag.D4.tag) K (x * y) * tp3Hom p K b *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K (x * y))⁻¹ =
        k⁻¹ * (canonicalRep (coxeterSystem TwistTag.D4.tag) K x *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K y * tp3Hom p K b *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) K y)⁻¹) *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K x)⁻¹) * k := by
          rw [e]
          group
      _ = k⁻¹ * tp3Hom p K (δx (δy b)) * k := by rw [hy b, hx (δy b)]
      _ = tp3Hom p K ((δx * δy) b) := by
          rw [mul_assoc, hcomm, inv_mul_cancel_left]
          rfl
  | inv x _ ih =>
    obtain ⟨δ, hδ, hx⟩ := ih
    obtain ⟨k, hk, hkx⟩ := canonicalRep_mul_mem (R := K) (τ := TwistTag.D4.tag) x x⁻¹
    rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkx
    refine ⟨δ⁻¹, Subgroup.inv_mem _ hδ, fun b => ?_⟩
    have hb : tp3Hom p K ((δ⁻¹) b) =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K x)⁻¹ * tp3Hom p K b *
          canonicalRep (coxeterSystem TwistTag.D4.tag) K x := by
      have h1 := hx ((δ⁻¹) b)
      rw [show δ ((δ⁻¹) b) = b from by simp] at h1
      rw [← h1]
      group
    have hcomm : tp3Hom p K b * k = k * tp3Hom p K b :=
      rootDiagUnit_mul_comm_of_mem_torusGroup
        (d4Tuple ((b 1 : rootsOfUnity p K) : Kˣ) ((b 0 : rootsOfUnity p K) : Kˣ)) hk
    have h3 : k * tp3Hom p K b * k⁻¹ = tp3Hom p K b := by
      rw [← hcomm, mul_inv_cancel_right]
    have e : canonicalRep (coxeterSystem TwistTag.D4.tag) K x⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K x)⁻¹ * k := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hkx
    calc canonicalRep (coxeterSystem TwistTag.D4.tag) K x⁻¹ * tp3Hom p K b *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K x⁻¹)⁻¹ =
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K x)⁻¹ * (k * tp3Hom p K b * k⁻¹) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) K x := by
          rw [e, mul_inv_rev, inv_inv]
          group
      _ = (canonicalRep (coxeterSystem TwistTag.D4.tag) K x)⁻¹ * tp3Hom p K b *
          canonicalRep (coxeterSystem TwistTag.D4.tag) K x := by rw [h3]
      _ = tp3Hom p K ((δ⁻¹) b) := hb.symm

theorem exists_wctx_d4
    (h : D4Param p f K σ)
    (τ : Fin TwistTag.D4.foldedTag.rank → MulAut (Fin 2 → rootsOfUnity p K))
    (hτ : ∀ a b, tp3Hom p K (τ a b) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
        tp3Hom p K b * (canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a))⁻¹) :
    Nonempty (WCtx (Subgroup.closure (Set.range τ)).subtype
      (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) (Tp3 h)) := by
  classical
  have hfin := h.finite
  set D := Subgroup.closure (Set.range τ) with hD
  let tor : (Fin 2 → rootsOfUnity p K) ≃* ↥(Tp3 h) := MonoidHom.ofInjective (tp3M_injective h)
  have htor : ∀ b, ((tor b : ↥(Tp3 h)) : ↥(graphFixedRootGroup TwistTag.D4 K σ)) =
      tp3M h b := fun b => rfl
  let n : Fin TwistTag.D4.foldedTag.rank → ↥(graphFixedRootGroup TwistTag.D4 K σ) := fun a =>
    ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a),
      canonicalRep_orbitReflection_mem_graphFixedRootGroup a⟩
  have hconjM : ∀ a b, n a * tp3M h b * (n a)⁻¹ = tp3M h (τ a b) := fun a b =>
    Subtype.ext (hτ a b).symm
  have hnorm : ∀ a, n a ∈ Subgroup.normalizer
      ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ)) := by
    intro a
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨b, rfl⟩
      rw [hconjM]
      exact tp3M_mem_Tp3 h _
    · rintro ⟨b, hb⟩
      refine ⟨(τ a).symm b, ?_⟩
      have h1 := hconjM a ((τ a).symm b)
      rw [MulEquiv.apply_symm_apply, hb] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hact : ∀ (a : Fin TwistTag.D4.foldedTag.rank) (hg : n a ∈ Subgroup.normalizer
      ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ))),
      (Tp3 h).normalizerMonoidHom ⟨n a, hg⟩ = MulAut.congr tor (τ a) := by
    intro a hg
    refine MulEquiv.ext fun t => ?_
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    exact hconjM a b
  have key : ∀ γ ∈ D, ∃ (g : ↥(graphFixedRootGroup TwistTag.D4 K σ))
      (hg : g ∈ Subgroup.normalizer
        ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ))),
      (Tp3 h).normalizerMonoidHom ⟨g, hg⟩ = MulAut.congr tor γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨n a, hnorm a, hact a (hnorm a)⟩
    | one => exact ⟨1, Subgroup.one_mem _, by
        rw [show (⟨1, Subgroup.one_mem _⟩ : Subgroup.normalizer
          ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 K σ))) = 1 from rfl, map_one, map_one]⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨g₁, hg₁, h₁⟩ := ihx
      obtain ⟨g₂, hg₂, h₂⟩ := ihy
      exact ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, by
        rw [show (⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂⟩ : Subgroup.normalizer
          ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 K σ))) =
          ⟨g₁, hg₁⟩ * ⟨g₂, hg₂⟩ from rfl, map_mul, map_mul, h₁, h₂]⟩
    | inv x _ ih =>
      obtain ⟨g, hg, h'⟩ := ih
      exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by
        rw [show (⟨g⁻¹, Subgroup.inv_mem _ hg⟩ : Subgroup.normalizer
          ((Tp3 h : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ)) :
            Set ↥(graphFixedRootGroup TwistTag.D4 K σ))) =
          (⟨g, hg⟩)⁻¹ from rfl, map_inv, map_inv, h']⟩
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }⟩
  · rintro ⟨γ, hγ⟩
    obtain ⟨g, hg, hγg⟩ := key γ hγ
    exact ⟨g, hg, Subgroup.mem_top _, hγg⟩
  · intro g hg _
    have hgΓ : (g : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ :=
      graphFixedRootGroup_le TwistTag.D4 K σ g.2
    have hgA : (g : ModGL TwistTag.D4.tag K) ∈
        (adjointGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) :=
      (Subgroup.mem_inf.1 hgΓ).1
    rw [adjointGroup_eq_iUnion_bruhatCell, Set.mem_iUnion] at hgA
    obtain ⟨w, hw⟩ := hgA
    have hσs : Function.Surjective σ := Finite.surjective_of_injective σ.injective
    obtain ⟨hwt, -⟩ := exists_fixed_bruhat_factor hσs hgΓ hw
    have hwrel : w ∈ Subgroup.closure (Set.range TwistTag.D4.orbitReflection) := by
      rw [← relWeylTwist_eq_closure TwistTag.D4]
      exact hwt
    obtain ⟨δ, hδ, hδb⟩ := exists_action_canonicalRep_d4 τ hτ hwrel
    refine ⟨⟨δ, hδ⟩, MulEquiv.ext fun t => ?_⟩
    obtain ⟨b, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    have h1 : g * tp3M h b * g⁻¹ ∈ Tp3 h :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp (tp3M_mem_Tp3 h b)
    obtain ⟨b', hb'⟩ := h1
    have h2 : (g : ModGL TwistTag.D4.tag K) * tp3Hom p K b * (g : ModGL TwistTag.D4.tag K)⁻¹ =
        tp3Hom p K b' := (congrArg Subtype.val hb').symm
    have h3 := rootDiagUnit_eq_conj_canonicalRep_of_mem_bruhatCell_of_mem_torus
      (d4Tuple ((b' 1 : rootsOfUnity p K) : Kˣ) ((b' 0 : rootsOfUnity p K) : Kˣ))
      (d4Tuple ((b 1 : rootsOfUnity p K) : Kˣ) ((b 0 : rootsOfUnity p K) : Kˣ))
      (tp3Hom_mem_torusGroup h.ringChar_eq_two b') (tp3Hom_mem_torusGroup h.ringChar_eq_two b)
      hw h2
    have h4 : tp3Hom p K b' = tp3Hom p K (δ b) := h3.trans (hδb b)
    have h5 : b' = δ b := tp3Hom_injective h4
    show g * ((tor b : ↥(Tp3 h)) : ↥(graphFixedRootGroup TwistTag.D4 K σ)) * g⁻¹ =
      ((tor (δ b) : ↥(Tp3 h)) : ↥(graphFixedRootGroup TwistTag.D4 K σ))
    rw [htor, htor, ← h5]
    exact hb'.symm

end CFSG.RankThree.PartOne.KFU
