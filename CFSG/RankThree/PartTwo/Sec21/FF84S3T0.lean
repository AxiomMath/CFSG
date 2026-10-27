module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3B
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTheta

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.QuasithinUnique.Claim2526

section T
variable {G : Type} [Group G] [Finite G]

private theorem center_char_of_aut (L : Subgroup G) (α : ↥L ≃* ↥L) (z : ↥L)
    (hz : z ∈ Subgroup.center ↥L) : α z ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have h2 := congrArg α (hz (α.symm g))
  simpa [map_mul] using h2

private noncomputable def T0Quot (L : Subgroup G) (n : ↥(Nor L)) :
    ↥L ⧸ Subgroup.center ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L)
    (L.normalizerMonoidHom n : ↥L ≃* ↥L)
    (by
      apply le_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact center_char_of_aut L _ z hz
      · intro z hz
        exact ⟨(L.normalizerMonoidHom n : ↥L ≃* ↥L).symm z,
          center_char_of_aut L _ z hz, MulEquiv.apply_symm_apply _ z⟩)

private theorem T0Quot_mk (L : Subgroup G) (n : ↥(Nor L)) (x : ↥L) :
    T0Quot L n (QuotientGroup.mk x) = QuotientGroup.mk (L.normalizerMonoidHom n x) :=
  QuotientGroup.congr_mk _ _ _ _ x

private theorem T0_coe_Cn (L : Subgroup G) (n : ↥(Nor L)) (x : ↥L) :
    ((L.normalizerMonoidHom n x : ↥L) : G) = (n : G) * x * (n : G)⁻¹ := by
  simp

private theorem T0Quot_one (L : Subgroup G) (q : ↥L ⧸ Subgroup.center ↥L) :
    T0Quot L 1 q = q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [T0Quot_mk, map_one, MulAut.one_apply]

private theorem T0Quot_mul (L : Subgroup G) (n m : ↥(Nor L))
    (q : ↥L ⧸ Subgroup.center ↥L) : T0Quot L (n * m) q = T0Quot L n (T0Quot L m q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [T0Quot_mk, T0Quot_mk, T0Quot_mk, map_mul, MulAut.mul_apply]

private noncomputable def T0Aut (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (n : ↥(Nor L)) :
    MulAut (alternatingGroup (Fin 8)) :=
  e.symm.trans ((T0Quot L n).trans e)

private theorem T0Aut_apply (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (n : ↥(Nor L))
    (y : alternatingGroup (Fin 8)) :
    T0Aut L e n y = e (T0Quot L n (e.symm y)) := rfl

private noncomputable def T0Hom (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    ↥(Nor L) →* MulAut (alternatingGroup (Fin 8)) where
  toFun := T0Aut L e
  map_one' := by
    apply MulEquiv.ext
    intro y
    rw [MulAut.one_apply, T0Aut_apply, T0Quot_one, MulEquiv.apply_symm_apply]
  map_mul' := fun n m => by
    apply MulEquiv.ext
    intro y
    rw [MulAut.mul_apply, T0Aut_apply, T0Aut_apply, T0Aut_apply, MulEquiv.symm_apply_apply,
      T0Quot_mul]

private theorem T0Hom_apply (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (n : ↥(Nor L)) :
    T0Hom L e n = T0Aut L e n := rfl

private noncomputable def T0Theta (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) : ↥(Nor L) →* P8 :=
  (conjEquiv8.symm : MulAut (alternatingGroup (Fin 8)) ≃* Equiv.Perm (Fin 8)).toMonoidHom.comp
    (T0Hom L e)

private theorem T0Theta_conj (L : Subgroup G)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (n : ↥(Nor L)) :
    MulAut.conjNormal (T0Theta L e n) = T0Hom L e n :=
  conjEquiv8.apply_symm_apply _

private theorem conjNormal_val (σ : Equiv.Perm (Fin 8)) (h : alternatingGroup (Fin 8)) :
    ((MulAut.conjNormal σ h : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
      σ * (h : Equiv.Perm (Fin 8)) * σ⁻¹ := by
  simp [MulAut.conjNormal_apply]

private theorem T0Quot_mk_conj (L : Subgroup G) (x w : ↥L) (hx : (x : G) ∈ Nor L) :
    T0Quot L ⟨(x : G), hx⟩ (QuotientGroup.mk w) =
      QuotientGroup.mk x * QuotientGroup.mk w * (QuotientGroup.mk x)⁻¹ := by
  have h : L.normalizerMonoidHom ⟨(x : G), hx⟩ w = x * w * x⁻¹ :=
    Subtype.ext (by simp)
  rw [T0Quot_mk, h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

private theorem cen_of_quot_trivial (L : Subgroup G) (hL : ⁅L, L⁆ = L) (n : ↥(Nor L))
    (hfix : ∀ x : ↥L, x⁻¹ * L.normalizerMonoidHom n x ∈ Subgroup.center ↥L) :
    (n : G) ∈ CenS L := by
  have hxL : ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 n.2 l).1 hl
  have hz : ∀ l ∈ L, (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ CenS L := by
    intro l hl
    obtain ⟨u, hu_def⟩ : ∃ u : ↥L, u = (⟨l, hl⟩ : ↥L)⁻¹ * L.normalizerMonoidHom n ⟨l, hl⟩ :=
      ⟨_, rfl⟩
    have hu : u ∈ Subgroup.center ↥L := by
      rw [hu_def]
      exact hfix _
    have hu_coe : (u : G) = l⁻¹ * ((n : G) * l * (n : G)⁻¹) := by
      rw [hu_def, Subgroup.coe_mul, Subgroup.coe_inv, T0_coe_Cn]
    have hcomm : (l : G) * (u : G) = (u : G) * l :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hu ⟨l, hl⟩)
    have key : (n : G) * l * (n : G)⁻¹ * l⁻¹ = (u : G) := by
      calc (n : G) * l * (n : G)⁻¹ * l⁻¹ = l * (u : G) * l⁻¹ := by
            rw [hu_coe]
            group
        _ = (u : G) := by
            rw [hcomm]
            group
    rw [key]
    refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hu ⟨h, hh⟩)
  refine Subgroup.mem_centralizer_iff.2 (fun l hl => ?_)
  exact (perfect_centralizes_of_comm_central L hL (n : G) hxL hz l hl).symm

private theorem T0Hom_eq_one_iff (L : Subgroup G) (hL : ⁅L, L⁆ = L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) (n : ↥(Nor L)) :
    T0Hom L e n = 1 ↔ (n : G) ∈ CenS L := by
  constructor
  · intro h
    apply cen_of_quot_trivial L hL n
    intro x
    have h1 : e (T0Quot L n (QuotientGroup.mk x)) = e (QuotientGroup.mk x) := by
      have := congrArg (fun φ : MulAut (alternatingGroup (Fin 8)) => φ (e (QuotientGroup.mk x))) h
      simpa [T0Hom_apply, T0Aut_apply] using this
    have h2 : T0Quot L n (QuotientGroup.mk x) = QuotientGroup.mk x := e.injective h1
    rw [T0Quot_mk] at h2
    have h3 := (QuotientGroup.eq).1 h2
    simpa using Subgroup.inv_mem _ h3
  · intro h
    apply MulEquiv.ext
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hc : (n : G) * (w : G) = (w : G) * (n : G) :=
      (Subgroup.mem_centralizer_iff.1 h (w : G) w.2).symm
    have hw : L.normalizerMonoidHom n w = w :=
      Subtype.ext (by rw [T0_coe_Cn, hc]; group)
    rw [MulAut.one_apply, T0Hom_apply, T0Aut_apply, MulEquiv.symm_apply_apply, T0Quot_mk, hw]

theorem T0_thetaBar (L : Subgroup G) (hL : ⁅L, L⁆ = L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :
    ∃ θ : ↥(Nor L) →* P8,
      (∀ (n : ↥(Nor L)) (x : ↥L),
        ((e (QuotientGroup.mk (L.normalizerMonoidHom n x)) : alternatingGroup (Fin 8)) : P8) =
          θ n * ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8) * (θ n)⁻¹) ∧
      (∀ x : ↥L, θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ =
        ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8)) ∧
      (∀ n : ↥(Nor L), θ n = 1 ↔ (n : G) ∈ CenS L) := by
  refine ⟨T0Theta L e, ?_, ?_, ?_⟩
  · intro n x
    have h1 : T0Theta L e n * ((e (QuotientGroup.mk x) : alternatingGroup (Fin 8)) : P8) *
        (T0Theta L e n)⁻¹ =
        ((MulAut.conjNormal (T0Theta L e n) (e (QuotientGroup.mk x)) :
          alternatingGroup (Fin 8)) : P8) := by
      rw [conjNormal_val]
    rw [h1, T0Theta_conj, T0Hom_apply, T0Aut_apply, MulEquiv.symm_apply_apply, T0Quot_mk]
  · intro x
    apply conjNormal_bijective8.1
    rw [T0Theta_conj]
    apply MulEquiv.ext
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    apply Subtype.ext
    rw [conjNormal_val, T0Hom_apply, T0Aut_apply, MulEquiv.symm_apply_apply, T0Quot_mk_conj]
    simp
  · intro n
    have key : T0Theta L e n = 1 ↔ T0Hom L e n = 1 := by
      constructor
      · intro h
        have := T0Theta_conj L e n
        rw [h, map_one] at this
        exact this.symm
      · intro h
        apply conjEquiv8.injective
        rw [map_one]
        exact (T0Theta_conj L e n).trans h
    rw [key, T0Hom_eq_one_iff L hL e n]

end T

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
