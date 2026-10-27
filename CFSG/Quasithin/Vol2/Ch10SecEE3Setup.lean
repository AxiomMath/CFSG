module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Relabel
public import CFSG.Quasithin.Vol2.Ch10SecECase2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A5.Delta5 (pact)

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def A5Equivariant {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}
    (θ : ↥K ≃* Equiv.Perm (Fin 5)) (β : ↥(commV K) ≃* Multiplicative (evenWeight 5)) : Prop :=
  ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
    ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
      ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i)

structure Case2Data (hyp : Hyp10 G T L I) (t : G) where
  K₁ : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))
  K₂ : Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))
  θ₁ : ↥K₁ ≃* Equiv.Perm (Fin 5)
  θ₂ : ↥K₂ ≃* Equiv.Perm (Fin 5)
  β₁ : ↥(commV K₁) ≃* Multiplicative (evenWeight 5)
  β₂ : ↥(commV K₂) ≃* Multiplicative (evenWeight 5)
  equiv₁ : A5Equivariant θ₁ β₁
  equiv₂ : A5Equivariant θ₂ β₂
  oTwo₁ : oTwoUpper K₁ = autI (SecA.isElemAbelian_fsuVM hyp) L
  oTwo₂ : oTwoUpper K₂ = autI (SecA.isElemAbelian_fsuVM hyp) (CFSG.conjugate L t)
  comm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a
  inf : K₁ ⊓ K₂ = ⊥
  thompsonJ_L0T : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ (fsuL0 T L ⊔ T)) = K₁ ⊔ K₂
  memP₁ : ∀ g (hg : g ∈ K₁),
    g ∈ K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) ↔ θ₁ ⟨g, hg⟩ ∈ eFour
  memP₂ : ∀ g (hg : g ∈ K₂),
    g ∈ K₂ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) ↔ θ₂ ⟨g, hg⟩ ∈ eFour
  thompsonJ_eq : autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) =
    (K₁ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)) ⊔
      (K₂ ⊓ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T))
  baum_eq : autI (SecA.isElemAbelian_fsuVM hyp) (baum T) =
    autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)
  span : fixV (autI (SecA.isElemAbelian_fsuVM hyp) (fsuL0 T L)) ⊔ (commV K₁ ⊔ commV K₂) = ⊤

theorem iSup_pair_eq {α β : Type*} [CompleteLattice β] {I' : Finset α} {K₁ K₂ : α}
    (hK₁ : K₁ ∈ I') (hK₂ : K₂ ∈ I') (hmem : ∀ K ∈ I', K = K₁ ∨ K = K₂) (f : α → β) :
    (⨆ K ∈ I', f K) = f K₁ ⊔ f K₂ := by
  refine le_antisymm (iSup₂_le fun K hK => ?_) (sup_le (le_iSup₂ (f := fun K _ => f K) K₁ hK₁)
    (le_iSup₂ (f := fun K _ => f K) K₂ hK₂))
  rcases hmem K hK with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem exists_case2Data
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Nonempty (Case2Data hyp t) := by
  obtain ⟨hKJ, I', hcard, hJeq, hcomm, hind, htrans, htype, hspan, -, -, h3⟩ :=
    SecA.e23Concl_L0T he23 h37 h38 hshape h3228 hyp (Or.inr h2) hJ
  obtain ⟨hA5, K₁, hK₁, K₂, hK₂, hmem, -, hJL, hO₁, hO₂, hc, hinf⟩ :=
    ident_case2 h37 h38 h322 hyp h2 ht htn hKJ hcard hJeq hcomm hind htrans htype
  obtain ⟨hS, hJsup, hP⟩ := h3 hA5
  obtain ⟨θ₁, β₁, hβ₁⟩ := hA5 K₁ hK₁
  obtain ⟨θ₂, β₂, hβ₂⟩ := hA5 K₂ hK₂
  obtain ⟨hP4₁, θ₀₁, hPeq₁⟩ := hP K₁ hK₁
  obtain ⟨hP4₂, θ₀₂, hPeq₂⟩ := hP K₂ hK₂
  obtain ⟨θ₁', β₁', hβ₁', hm₁⟩ := exists_normalized hβ₁ θ₀₁ hP4₁ hPeq₁
  obtain ⟨θ₂', β₂', hβ₂', hm₂⟩ := exists_normalized hβ₂ θ₀₂ hP4₂ hPeq₂
  rw [twoResidual_fsuL0_sup h37 h38 hyp] at hspan
  rw [iSup_pair_eq hK₁ hK₂ hmem] at hJsup hspan
  exact ⟨⟨K₁, K₂, θ₁', θ₂', β₁', β₂', hβ₁', hβ₂', hO₁, hO₂, hc, hinf, hJL, hm₁, hm₂, hJsup, hS,
    hspan⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecE
