module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {S : Set (Subgroup G)} {K : Subgroup G}

namespace IsDirectProduct

theorem equiv_symm_of_mem [Finite G] [DecidableEq S] (hK : IsDirectProduct S K) {J : Subgroup G}
    (hJ : J ∈ S) {x : G} (hx : x ∈ J) :
    hK.equiv.symm ⟨x, hK.le hJ hx⟩ = Pi.mulSingle (⟨J, hJ⟩ : S) ⟨x, hx⟩ := by
  have h : hK.equiv (Pi.mulSingle (⟨J, hJ⟩ : S) ⟨x, hx⟩) = ⟨x, hK.le hJ hx⟩ := by
    apply Subtype.ext
    rw [hK.equiv_apply_of_eq_one ⟨J, hJ⟩ _ (fun J' hJ' => Pi.mulSingle_eq_of_ne hJ' _)]
    simp
  rw [MulEquiv.symm_apply_eq, h]

noncomputable def ofFamily [Finite G] (hK : IsDirectProduct S K) :
    ((J : S) → MulAut (J : Subgroup G)) →* MulAut ↥K where
  toFun a := hK.equiv.symm.trans ((MulEquiv.piCongrRight a).trans hK.equiv)
  map_one' := by
    ext x
    have : ∀ y, (MulEquiv.piCongrRight (1 : (J : S) → MulAut (J : Subgroup G))) y = y :=
      fun y => funext fun _ => rfl
    simp [this]
  map_mul' a a' := by
    ext x
    have : ∀ y, (MulEquiv.piCongrRight (a * a')) y =
        (MulEquiv.piCongrRight a) ((MulEquiv.piCongrRight a') y) := fun y => funext fun _ => rfl
    simp [this]

theorem ofFamily_apply_of_mem [Finite G] (hK : IsDirectProduct S K)
    (a : (J : S) → MulAut (J : Subgroup G)) {J : Subgroup G} (hJ : J ∈ S) {x : G} (hx : x ∈ J) :
    ((hK.ofFamily a ⟨x, hK.le hJ hx⟩ : K) : G) = ((a ⟨J, hJ⟩ ⟨x, hx⟩ : J) : G) := by
  classical
  have hpi : (MulEquiv.piCongrRight a) (Pi.mulSingle (⟨J, hJ⟩ : S) ⟨x, hx⟩) =
      Pi.mulSingle (⟨J, hJ⟩ : S) (a ⟨J, hJ⟩ ⟨x, hx⟩) := by
    funext i
    by_cases hi : i = ⟨J, hJ⟩
    · subst hi
      simp
    · simp [Pi.mulSingle_eq_of_ne hi]
  show ((hK.equiv ((MulEquiv.piCongrRight a) (hK.equiv.symm ⟨x, hK.le hJ hx⟩)) : K) : G) = _
  rw [hK.equiv_symm_of_mem hJ hx, hpi,
    hK.equiv_apply_of_eq_one ⟨J, hJ⟩ _ (fun J' hJ' => Pi.mulSingle_eq_of_ne hJ' _)]
  simp

theorem ext_of_forall_mem [Finite G] (hK : IsDirectProduct S K) {φ ψ : MulAut ↥K}
    (h : ∀ (J : Subgroup G) (hJ : J ∈ S) (x : G) (hx : x ∈ J),
      φ ⟨x, hK.le hJ hx⟩ = ψ ⟨x, hK.le hJ hx⟩) : φ = ψ := by
  ext ⟨k, hk⟩
  let E : Subgroup G := (MonoidHom.eqLocus φ.toMonoidHom ψ.toMonoidHom).map K.subtype
  have hKE : K ≤ E := by
    rw [← hK.sSup_eq]
    exact sSup_le fun J hJ x hx => ⟨⟨x, hK.le hJ hx⟩, h J hJ x hx, rfl⟩
  obtain ⟨⟨k', hk'⟩, hk'E, hkk'⟩ := hKE hk
  have : k' = k := hkk'
  subst this
  exact congrArg Subtype.val hk'E

theorem coord_conj_of_normalizes [Finite G] (hK : IsDirectProduct S K) {a : G}
    (ha : ∀ J ∈ S, a ∈ Subgroup.normalizer (J : Set G)) {J : Subgroup G} (hJ : J ∈ S) {y : G}
    (hy : y ∈ K) :
    ∃ hy' : a * y * a⁻¹ ∈ K, ((hK.coord hJ ⟨a * y * a⁻¹, hy'⟩ : J) : G) =
      a * ((hK.coord hJ ⟨y, hy⟩ : J) : G) * a⁻¹ := by
  have hJn' : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom = J := fun J hJ =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (ha J hJ)
  have hmap : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S := fun J hJ =>
    (hJn' J hJ).symm ▸ hJ
  have hJn : J.map (MulAut.conj a).toMonoidHom = J := hJn' J hJ
  refine ⟨hK.conj_mem hmap hy, ?_⟩
  have h1 := hK.coord_conj hmap hJ hy
  have h2 := hK.coord_val_congr (hmap J hJ) hJ hJn ⟨a * y * a⁻¹, hK.conj_mem hmap hy⟩
  exact h2.symm.trans h1

end IsDirectProduct

end CFSG.SignalizerFunctorTheorem.McBride
