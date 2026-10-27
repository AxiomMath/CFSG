module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDForm
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier SpinFrame
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.LowTwoRank
open QuadraticMap
open scoped Matrix

theorem statedQuadMinus_map {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n L (f b) (f c) (f ∘ v) = f (StatedQuadMinus n K b c v) := by
  simp only [StatedQuadMinus, Function.comp_apply, map_add, map_mul, map_pow, map_sum]

section Coef

variable {L : Type} [Field L] (θ : L →+* L) (S : Subfield L) (hS : ∀ x, x ∈ S ↔ θ x = x)
  {ω : L} (hθω : θ (θ ω) = ω)

@[expose] def coefB : S :=
  ⟨-(ω + θ ω), (hS _).2 (by rw [map_neg, map_add, hθω, add_comm])⟩

@[expose] def coefC : S :=
  ⟨ω * θ ω, (hS _).2 (by rw [map_mul, hθω, mul_comm])⟩

theorem coe_coefB : (coefB θ S hS hθω : L) = -(ω + θ ω) :=
  rfl

theorem coe_coefC : (coefC θ S hS hθω : L) = ω * θ ω :=
  rfl

theorem coef_irreducible (hω : ω ≠ θ ω) :
    ∀ s : S, s ^ 2 + coefB θ S hS hθω * s + coefC θ S hS hθω ≠ 0 := by
  intro s h
  have h' : ((s : L) - ω) * ((s : L) - θ ω) = 0 := by
    have h1 := congrArg S.subtype h
    simp only [map_add, map_mul, map_pow, map_zero, Subfield.coe_subtype, coe_coefB,
      coe_coefC] at h1
    linear_combination h1
  have hs : θ s = s := (hS s).1 s.2
  rcases mul_eq_zero.1 h' with h1 | h1
  · have e : (s : L) = ω := sub_eq_zero.1 h1
    exact hω (by rw [← e, hs])
  · have e : (s : L) = θ ω := sub_eq_zero.1 h1
    exact hω (calc ω = θ (θ ω) := hθω.symm
      _ = θ s := by rw [e]
      _ = s := hs
      _ = θ ω := e)

end Coef

section Twisted

variable {m : ℕ} (hn : 4 ≤ m + 1) {L : Type} [Field L] (θ : L →+* L) (S : Subfield L)
  (hS : ∀ x, x ∈ S ↔ θ x = x) {ω : L} (hω : ω ≠ θ ω) (hθω : θ (θ ω) = ω)
  (H : Subgroup (points (m + 1) hn L))
  (hH : ∀ g : points (m + 1) hn L, g ∈ H ↔
    (((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) :
      Matrix (DI (m + 1)) (DI (m + 1)) L).map θ).submatrix (tauM m) (tauM m) =
        ((orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) : Matrix (DI (m + 1)) (DI (m + 1)) L))

@[expose] def psiL : H →* GL (MI m) L :=
  (conjGL (phi ω (θ ω) hω)).comp ((orthPoints (m + 1) hn L).comp H.subtype)

theorem psiL_apply (g : H) :
    psiL hn θ hω H g = conjGL (phi ω (θ ω) hω) (orthPoints (m + 1) hn L g) :=
  rfl

include hS hθω hH in
theorem psiL_entry_mem (g : H) (i j : MI m) :
    ((psiL hn θ hω H g : GL (MI m) L) : Matrix (MI m) (MI m) L) i j ∈ S := by
  rw [hS]
  exact map_conjGL_entry (phi ω (θ ω) hω) θ (tauM m) (Equiv.symm_swap _ _)
    (fun v => phiV_comp ω (θ ω) θ rfl hθω v) _ ((hH g).1 g.2) i j

@[expose] def psiS : H →* GL (MI m) S :=
  liftGL S (psiL hn θ hω H) (psiL_entry_mem hn θ S hS hω hθω H hH)

theorem map_psiS (g : H) :
    Matrix.GeneralLinearGroup.map S.subtype (psiS hn θ S hS hω hθω H hH g) = psiL hn θ hω H g :=
  map_liftGL _ _ _ g

theorem psiS_injective (h2 : (2 : L) = 0) : Function.Injective (psiS hn θ S hS hω hθω H hH) :=
  liftGL_injective _ _ _ ((conjGL_injective _).comp
    ((orthPoints_injective (m + 1) hn h2).comp Subtype.val_injective))

theorem statedQuadMinus_eq_plus (x : MI m → L) :
    StatedQuadMinus (m + 1) L (S.subtype (coefB θ S hS hθω)) (S.subtype (coefC θ S hS hθω)) x =
      StatedQuadPlus (m + 1) L (phi ω (θ ω) hω x) :=
  (statedQuadPlus_phiV ω (θ ω) x).symm

theorem coe_psiS_mulVec (g : H) (v : MI m → S) :
    S.subtype ∘ (((psiS hn θ S hS hω hθω H hH g : GL (MI m) S) : Matrix (MI m) (MI m) S) *ᵥ v) =
      ((psiL hn θ hω H g : GL (MI m) L) : Matrix (MI m) (MI m) L) *ᵥ (S.subtype ∘ v) := by
  funext k
  rw [Function.comp_apply, RingHom.map_mulVec, ← map_psiS hn θ S hS hω hθω H hH g]
  rfl

theorem psiS_mem_isometries (g : H) :
    psiS hn θ S hS hω hθω H hH g ∈ Subgroup.closure {A : GL (MI m) S | ∀ v,
      StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)
        ((A : Matrix (MI m) (MI m) S) *ᵥ v) =
      StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω) v} := by
  apply Subgroup.subset_closure
  intro v
  apply S.subtype_injective
  rw [← statedQuadMinus_map S.subtype (m + 1) _ _ v,
    ← statedQuadMinus_map S.subtype (m + 1) _ _ (_ *ᵥ v), coe_psiS_mulVec, psiL_apply,
    conjGL_apply]
  rw [statedQuadMinus_eq_plus θ S hS hω hθω, statedQuadMinus_eq_plus θ S hS hω hθω,
    LinearEquiv.apply_symm_apply, coe_orthPoints]
  unfold StatedQuadPlus
  exact (frame (m + 1)).plusQuad_rho (points_le_normGroup (m + 1) hn L (g : points _ hn L).2) _

theorem quadPlus_comp_tau (v : DI (m + 1) → L) :
    quadPlus (m + 1) L (θ ∘ v ∘ tauM m) = θ (quadPlus (m + 1) L v) := by
  rw [coe_quadPlus]
  simp only [StatedQuadPlus, Fin.sum_univ_castSucc, Function.comp_apply, map_add, map_sum,
    map_mul]
  have h1 : ∀ j : Fin m, tauM m (.inl j.castSucc) = .inl j.castSucc := fun j =>
    Equiv.swap_apply_of_ne_of_ne (fun h => Fin.castSucc_ne_last j (Sum.inl_injective h))
      Sum.inl_ne_inr
  have h2 : ∀ j : Fin m, tauM m (.inr j.castSucc) = .inr j.castSucc := fun j =>
    Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl
      (fun h => Fin.castSucc_ne_last j (Sum.inr_injective h))
  simp only [h1, h2, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

theorem quadMinus_map (v : MI m → S) :
    quadMinus (m + 1) L ((coefB θ S hS hθω : S) : L) ((coefC θ S hS hθω : S) : L)
        (S.subtype ∘ v) =
      S.subtype (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω) v) := by
  rw [coe_quadMinus, coe_quadMinus]
  exact statedQuadMinus_map S.subtype (m + 1) (coefB θ S hS hθω) (coefC θ S hS hθω) v

theorem toLinEquiv_symm_eichler_map_id {K K' : Type} [Field K] [Field K'] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {Q' : QuadraticForm K' (ι → K')}
    (f : K →+* K') (hQ : ∀ v, Q' (f ∘ v) = f (Q v)) (u w : ι → K) :
    (((toLinEquiv ι K).symm (eichler Q u w) : GL ι K) : Matrix ι ι K).map f =
      (((toLinEquiv ι K').symm (eichler Q' (f ∘ u) (f ∘ w)) : GL ι K') : Matrix ι ι K') :=
  toLinEquiv_symm_eichler_map f (Equiv.refl ι) (fun v => hQ v) u w

include hH in
theorem eichler_mem_map_range (u w : MI m → S) :
    eichler (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) u w ∈
      (psiS hn θ S hS hω hθω H hH).range.map (toLinEquiv (MI m) S).toMonoidHom := by
  set Φ := phi ω (θ ω) hω
  set QL := quadMinus (m + 1) L ((coefB θ S hS hθω : S) : L) ((coefC θ S hS hθω : S) : L)
  have hQL : ∀ x, quadPlus (m + 1) L (Φ x) = QL x := fun x => quadPlus_phi ω (θ ω) hω x
  have hι : ∀ v : MI m → S, QL (S.subtype ∘ v) =
      S.subtype (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω) v) :=
    quadMinus_map θ S hS hθω
  set U := Φ (S.subtype ∘ u)
  set W := Φ (S.subtype ∘ w)
  have hfix : ∀ v : MI m → S, θ ∘ Φ (S.subtype ∘ v) ∘ tauM m = Φ (S.subtype ∘ v) := by
    intro v
    have hθv : θ ∘ (S.subtype ∘ v) = S.subtype ∘ v := by
      funext k
      exact (hS _).1 (v k).2
    have h := phiV_comp ω (θ ω) θ rfl hθω (S.subtype ∘ v)
    rw [hθv] at h
    exact h.symm
  have hEU : eichler (quadPlus (m + 1) L) U W ∈ imageLin (m + 1) hn L :=
    elementaryGroup_le_of_simple (by omega) (simpleMem_imageLin (m + 1) hn)
      (eichler_mem_elementaryGroup _ U W)
  obtain ⟨A, ⟨g, rfl⟩, hA⟩ := hEU
  rw [MulEquiv.coe_toMonoidHom] at hA
  have hgA : (orthPoints (m + 1) hn L g : GL (DI (m + 1)) L) =
      (toLinEquiv (DI (m + 1)) L).symm (eichler (quadPlus (m + 1) L) U W) := by
    rw [← hA, MulEquiv.symm_apply_apply]
  have hgH : g ∈ H := by
    rw [hH, hgA, toLinEquiv_symm_eichler_map θ (tauM m) (quadPlus_comp_tau θ), hfix u, hfix w]
  refine ⟨psiS hn θ S hS hω hθω H hH ⟨g, hgH⟩, ⟨_, rfl⟩, ?_⟩
  rw [MulEquiv.coe_toMonoidHom]
  have hmap : Matrix.GeneralLinearGroup.map S.subtype (psiS hn θ S hS hω hθω H hH ⟨g, hgH⟩) =
      Matrix.GeneralLinearGroup.map S.subtype ((toLinEquiv (MI m) S).symm
        (eichler (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) u w)) := by
    rw [map_psiS, psiL_apply]
    apply Units.ext
    have e1 := toLinEquiv_symm_eichler_map_id S.subtype hι u w
    rw [show ((Matrix.GeneralLinearGroup.map S.subtype ((toLinEquiv (MI m) S).symm
        (eichler (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) u w)) :
          GL (MI m) L) : Matrix (MI m) (MI m) L) = (((toLinEquiv (MI m) S).symm
        (eichler (quadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) u w) :
          GL (MI m) S) : Matrix (MI m) (MI m) S).map S.subtype from rfl, e1]
    congr 1
    apply (toLinEquiv (MI m) L).injective
    rw [MulEquiv.apply_symm_apply, toLinEquiv_conjGL, Subtype.coe_mk, hA]
    exact eichler_isometry Φ hQL _ _
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := MI m) S.subtype) := by
    intro x y hxy
    apply Units.ext
    exact Matrix.map_injective S.subtype_injective (congrArg Units.val hxy)
  rw [hinj hmap, MulEquiv.apply_symm_apply]

include hH in
theorem statedOmega_le_range_psiS [Finite S] :
    StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) ≤
      (psiS hn θ S hS hω hθω H hH).range := by
  rw [statedOmega_quadMinus_eq_map hn (coef_irreducible θ S hS hθω hω)]
  rintro _ ⟨B, hB, rfl⟩
  have hle := elementaryGroup_le_of_eichler_mem (H := (psiS hn θ S hS hω hθω H hH).range.map
      (toLinEquiv (MI m) S).toMonoidHom)
    (fun u w _ _ => eichler_mem_map_range hn θ S hS hω hθω H hH u w)
  obtain ⟨C, hC, hCB⟩ := hle hB
  have e : (toLinEquiv (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) S).symm.toMonoidHom B = C := by
    rw [← hCB]
    exact (toLinEquiv (MI m) S).symm_apply_apply C
  rw [e]
  exact hC

include hH in
theorem commutator_range_psiS [Finite S] :
    ⁅(psiS hn θ S hS hω hθω H hH).range, (psiS hn θ S hS hω hθω H hH).range⁆ =
      StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) := by
  have hle : (psiS hn θ S hS hω hθω H hH).range ≤ Subgroup.closure {A : GL (MI m) S | ∀ v,
      StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)
        ((A : Matrix (MI m) (MI m) S) *ᵥ v) =
      StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω) v} := by
    rintro _ ⟨g, rfl⟩
    exact psiS_mem_isometries hn θ S hS hω hθω H hH g
  apply le_antisymm
  · exact Subgroup.commutator_mono hle hle
  · have hperf := isPerfect_statedOmega_quadMinus (K := S) (n := m + 1) hn
      (coef_irreducible θ S hS hθω hω)
    have e : ⁅StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)),
        StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω))⁆ =
        StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω) (coefC θ S hS hθω)) := by
      rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← e]
    exact Subgroup.commutator_mono (statedOmega_le_range_psiS hn θ S hS hω hθω H hH)
      (statedOmega_le_range_psiS hn θ S hS hω hθω H hH)

def dcqEquivTwisted [Finite S] (h2 : (2 : L) = 0) :
    DerivedCentralQuotient H ≃*
      StatedProj (StatedOmega (StatedQuadMinus (m + 1) S (coefB θ S hS hθω)
        (coefC θ S hS hθω))) :=
  (dcqEquivOfInjective (psiS hn θ S hS hω hθω H hH) (psiS_injective hn θ S hS hω hθω H hH h2)
    (commutator_range_psiS hn θ S hS hω hθω H hH)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedOmega_quadMinus hn
      (coef_irreducible θ S hS hθω hω)))

end Twisted

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
