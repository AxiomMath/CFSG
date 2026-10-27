module

public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

theorem isMulCommutative_subgroup_iff {E : Subgroup G} :
    IsMulCommutative E ↔ ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
  constructor
  · intro h x hx y hy
    exact congrArg Subtype.val (h.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · intro h
    exact ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

theorem isElemAbelian_map_mulEquiv {p : ℕ} (φ : G ≃* G) {E : Subgroup G} :
    IsElemAbelian p (E.map φ.toMonoidHom) ↔ IsElemAbelian p E := by
  unfold IsElemAbelian
  rw [isMulCommutative_subgroup_iff, isMulCommutative_subgroup_iff]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun x hx y hy => φ.injective ?_, fun x hx => φ.injective ?_⟩
    · simpa using hc (φ x) (Subgroup.mem_map_of_mem _ hx) (φ y) (Subgroup.mem_map_of_mem _ hy)
    · simpa using hp (φ x) (Subgroup.mem_map_of_mem _ hx)
  · rintro ⟨hc, hp⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp [← map_mul, hc x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      simp [← map_pow, hp x hx]

theorem card_map_mulEquiv (φ : G ≃* G) (E : Subgroup G) :
    Nat.card (E.map φ.toMonoidHom) = Nat.card E :=
  Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv.symm

theorem map_le_map_mulEquiv_iff (φ : G ≃* G) {A B : Subgroup G} :
    A.map φ.toMonoidHom ≤ B.map φ.toMonoidHom ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective φ.injective

theorem map_map_symm_mulEquiv (φ : G ≃* G) (A : Subgroup G) :
    (A.map φ.toMonoidHom).map φ.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x
  simp

theorem map_symm_map_mulEquiv (φ : G ≃* G) (A : Subgroup G) :
    (A.map φ.symm.toMonoidHom).map φ.toMonoidHom = A := by
  simpa using map_map_symm_mulEquiv φ.symm A

theorem omegaOneOf_map_mulEquiv (φ : G ≃* G) (X : Subgroup G) :
    (omegaOneOf X).map φ.toMonoidHom = omegaOneOf (X.map φ.toMonoidHom) := by
  unfold omegaOneOf
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem _ hx, by simp [← map_pow, hx2]⟩
  · rintro ⟨⟨x, hx, rfl⟩, h2⟩
    refine ⟨x, ⟨hx, φ.injective ?_⟩, rfl⟩
    simpa using h2

theorem centralizer_map_mulEquiv (φ : G ≃* G) (X : Subgroup G) :
    (Subgroup.centralizer (X : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((X.map φ.toMonoidHom : Subgroup G) : Set G) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc x hx
    simp [← map_mul, this]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    have := Subgroup.mem_centralizer_iff.mp hy (φ x) (Subgroup.mem_map_of_mem _ hx)
    apply φ.injective
    simpa using this

theorem centerOf_map_mulEquiv (φ : G ≃* G) (X : Subgroup G) :
    (centerOf X).map φ.toMonoidHom = centerOf (X.map φ.toMonoidHom) := by
  unfold centerOf
  rw [Subgroup.map_inf _ _ _ φ.injective, centralizer_map_mulEquiv]

theorem omegaOneCenterOf_map_mulEquiv (φ : G ≃* G) (X : Subgroup G) :
    (omegaOneCenterOf X).map φ.toMonoidHom = omegaOneCenterOf (X.map φ.toMonoidHom) := by
  unfold omegaOneCenterOf
  rw [omegaOneOf_map_mulEquiv, centerOf_map_mulEquiv]

theorem isMaxElemAbelian_map_mulEquiv (φ : G ≃* G) {H A : Subgroup G} :
    IsMaxElemAbelian (H.map φ.toMonoidHom) (A.map φ.toMonoidHom) ↔ IsMaxElemAbelian H A := by
  unfold IsMaxElemAbelian
  rw [map_le_map_mulEquiv_iff, isElemAbelian_map_mulEquiv, card_map_mulEquiv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun B hB hBe => ?_⟩
    have := h3 (B.map φ.toMonoidHom) ((map_le_map_mulEquiv_iff φ).mpr hB)
      ((isElemAbelian_map_mulEquiv φ).mpr hBe)
    rwa [card_map_mulEquiv] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun B hB hBe => ?_⟩
    have hB' : B.map φ.symm.toMonoidHom ≤ H := by
      rw [← map_map_symm_mulEquiv φ H]
      exact Subgroup.map_mono hB
    have hBe' : IsElemAbelian 2 (B.map φ.symm.toMonoidHom) := by
      rw [← isElemAbelian_map_mulEquiv φ, map_symm_map_mulEquiv]
      exact hBe
    have := h3 _ hB' hBe'
    rwa [card_map_mulEquiv] at this

theorem thompsonJ_map_mulEquiv (φ : G ≃* G) (H : Subgroup G) :
    (thompsonJ H).map φ.toMonoidHom = thompsonJ (H.map φ.toMonoidHom) := by
  unfold thompsonJ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian (H.map φ.toMonoidHom) B) => B)
      (A.map φ.toMonoidHom) ((isMaxElemAbelian_map_mulEquiv φ).mpr hA) le_rfl
  · refine iSup₂_le fun B hB => ?_
    have hB' : IsMaxElemAbelian H (B.map φ.symm.toMonoidHom) := by
      rw [← isMaxElemAbelian_map_mulEquiv φ, map_symm_map_mulEquiv]
      exact hB
    rw [← map_symm_map_mulEquiv φ B]
    exact Subgroup.map_mono (le_iSup₂_of_le
      (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian H A) => A) _ hB' le_rfl)

theorem baum_map_mulEquiv (φ : G ≃* G) (H : Subgroup G) :
    (baum H).map φ.toMonoidHom = baum (H.map φ.toMonoidHom) := by
  unfold baum
  rw [Subgroup.map_inf _ _ _ φ.injective, centralizer_map_mulEquiv,
    omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]

theorem map_conj_eq_of_mem_normalizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    R.map (MulAut.conj g).toMonoidHom = R := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x)
  simp only [inv_inv] at this
  exact this.symm

theorem normalizer_le_normalizer_of_map_mulEquiv {F : Subgroup G → Subgroup G}
    (hF : ∀ (φ : G ≃* G) (X : Subgroup G), (F X).map φ.toMonoidHom = F (X.map φ.toMonoidHom))
    (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (F R : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have h := hF (MulAut.conj g) R
  rw [map_conj_eq_of_mem_normalizer hg] at h
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h, Subgroup.mem_map_equiv] at hx
    simpa [mul_assoc] using hx

theorem normalizer_le_normalizer_thompsonJ (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (thompsonJ R : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv thompsonJ_map_mulEquiv R

theorem normalizer_le_normalizer_baum (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (baum R : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv baum_map_mulEquiv R

end CFSG.Quasithin
