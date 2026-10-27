module

public import CFSG.Quasithin.Background.SmithB45ExcHSRuLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin.B45Exc.HSRu

variable {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)} {G : Type*} [Group G]
  {R P : Subgroup G}

noncomputable def liftSub (ψ : Lift L Y R P) : ↥L →* ↥P where
  toFun l := ⟨((ψ.hom (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y) l) : ↥R) : G),
    (ψ.mem_iff _).2 l.2⟩
  map_one' := by
    apply Subtype.ext
    have h1 : (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) (1 : ↥L) = 1 := map_one _
    simp only [h1, map_one, OneMemClass.coe_one]
  map_mul' a b := by
    apply Subtype.ext
    have h1 : (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) (a * b) =
        (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) a *
          (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) b := map_mul _ a b
    simp only [h1, map_mul, Subgroup.coe_mul]

theorem liftSub_injective (ψ : Lift L Y R P) : Function.Injective (liftSub ψ) := by
  intro a b hab
  have h1 : (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) a =
      (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) b := by
    apply ψ.inj
    exact Subtype.ext (congrArg (fun x : ↥P => (x : G)) hab)
  have h2 : ((Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) a : MulAut W) =
      ((Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) b : MulAut W) :=
    congrArg (fun x : ↥(L ⊔ Y) => (x : MulAut W)) h1
  exact Subtype.ext (by simpa only [Subgroup.coe_inclusion] using h2)

theorem liftSub_surjective (ψ : Lift L Y R P) : Function.Surjective (liftSub ψ) := by
  intro p
  obtain ⟨x, hxL, hxp⟩ := ψ.surj p p.2
  refine ⟨⟨(x : MulAut W), hxL⟩, ?_⟩
  apply Subtype.ext
  have hx : (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)) ⟨(x : MulAut W), hxL⟩ = x :=
    Subtype.ext rfl
  show ((ψ.hom (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y) ⟨(x : MulAut W), hxL⟩) : ↥R) : G) =
    (p : G)
  rw [hx]
  exact hxp

noncomputable def liftEquiv (ψ : Lift L Y R P) : ↥L ≃* ↥P :=
  MulEquiv.ofBijective (liftSub ψ) ⟨liftSub_injective ψ, liftSub_surjective ψ⟩

theorem liftEquiv_symm_apply (ψ : Lift L Y R P) (p : ↥P) :
    ((ψ.hom (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y) ((liftEquiv ψ).symm p)) : ↥R) : G) =
      (p : G) := by
  have h : (liftEquiv ψ) ((liftEquiv ψ).symm p) = p := MulEquiv.apply_symm_apply _ p
  have h2 : liftSub ψ ((liftEquiv ψ).symm p) = p := h
  exact congrArg (fun x : ↥P => (x : G)) h2

noncomputable def psiOfLift (ψ : Lift L Y R P) : ↥P →* MulAut W :=
  L.subtype.comp (liftEquiv ψ).symm.toMonoidHom

theorem psiOfLift_injective (ψ : Lift L Y R P) : Function.Injective (psiOfLift ψ) :=
  (Subgroup.subtype_injective L).comp (liftEquiv ψ).symm.injective

theorem psiOfLift_mem (ψ : Lift L Y R P) (p : ↥P) : psiOfLift ψ p ∈ L :=
  ((liftEquiv ψ).symm p).2

theorem conj_psiOfLift_eq_inv (hPR : P ≤ R) (ψ : Lift L Y R P) {t : MulAut W} (ht : t ∈ Y)
    {p : ↥P}
    (hinv : ((ψ.hom ⟨t, Subgroup.mem_sup_right ht⟩ : ↥R) : G) * (p : G) *
        ((ψ.hom ⟨t, Subgroup.mem_sup_right ht⟩ : ↥R) : G)⁻¹ = (p : G)⁻¹) :
    t * psiOfLift ψ p * t⁻¹ = (psiOfLift ψ p)⁻¹ := by
  let u : ↥(L ⊔ Y) := Subgroup.inclusion (le_sup_left : L ≤ L ⊔ Y)
    ⟨psiOfLift ψ p, psiOfLift_mem ψ p⟩
  have hzR : ψ.hom u = ⟨(p : G), hPR p.2⟩ := by
    have h1 : (liftEquiv ψ).symm p = ⟨psiOfLift ψ p, psiOfLift_mem ψ p⟩ := Subtype.ext rfl
    have h2 := liftEquiv_symm_apply ψ p
    rw [h1] at h2
    exact Subtype.ext h2
  let t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right ht⟩
  have hinvZ : ψ.hom (t' * u * t'⁻¹) = ψ.hom u⁻¹ := by
    rw [map_inv]
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hzR]
    exact hinv
  have hconj : t' * u * t'⁻¹ = u⁻¹ := ψ.inj hinvZ
  have h := congrArg (fun x : ↥(L ⊔ Y) => (x : MulAut W)) hconj
  simpa [u, t', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using h

theorem index_fixV_hom_conj (ψ : ↥P →* MulAut W) (x y : ↥P) {m : G} (hm : m ∈ P)
    (hmx : m * (x : G) * m⁻¹ = y) :
    (CFSG.Quasithin.fixV (Subgroup.zpowers (ψ y))).index =
      (CFSG.Quasithin.fixV (Subgroup.zpowers (ψ x))).index := by
  have hP : y = (⟨m, hm⟩ : ↥P) * x * (⟨m, hm⟩ : ↥P)⁻¹ := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmx.symm
  rw [hP, map_mul, map_mul, map_inv]
  exact CFSG.QuasithinUnique.Setup.X1.index_fixV_conj (ψ ⟨m, hm⟩) (ψ x)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
