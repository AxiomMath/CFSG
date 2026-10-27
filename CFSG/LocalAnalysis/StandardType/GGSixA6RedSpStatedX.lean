module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpCoreAbs
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

section Bridge

private theorem ggA6sp_bilinIsometryGroup_map_generalLinearEquiv
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (B : BilinForm F V) :
    (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom =
      TauCeti.BilinForm.isometryGroup B := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    intro x y
    change B (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V) u : V →ₗ[F] V) x)
        (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V) u : V →ₗ[F] V) y) = B x y
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
    exact (CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mp hu) x y
  · intro h
    have hsymm : (((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm g :
        V →ₗ[F] V)) = (g : V →ₗ[F] V) := by
      rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
      rw [MulEquiv.apply_symm_apply]
    refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv F V).symm g, ?_, ?_⟩
    · exact CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr (fun x y => by
        rw [hsymm]
        exact (TauCeti.BilinForm.mem_isometryGroup_iff.mp h) x y)
    · exact MulEquiv.apply_symm_apply (LinearMap.GeneralLinearGroup.generalLinearEquiv F V) g

private noncomputable def gspIsometryGroupEquiv
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (B : BilinForm F V) :
    CFSG.ClassicalGroups.Alternating.Gsp B ≃* TauCeti.BilinForm.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).subgroupMap
      (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (ggA6sp_bilinIsometryGroup_map_generalLinearEquiv B))

end Bridge

private theorem ggA6sp_map_centralizer_eq_inf {G H : Type} [Group G] [Group H]
    (ι : G →* H) (hι : Function.Injective ι) (H₀ : Subgroup H) (hran : ι.range = H₀)
    (S : Set G) :
    (Subgroup.centralizer S).map ι = H₀ ⊓ Subgroup.centralizer (ι '' S) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer S := hc
    refine ⟨by rw [← hran]; exact ⟨c, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro s ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc' x hx]
  · rintro ⟨hg, hgc⟩
    rw [← hran] at hg
    rcases hg with ⟨c, rfl⟩
    have hgc' : ι c ∈ Subgroup.centralizer (ι '' S) := hgc
    exact Subgroup.mem_map.mpr ⟨c, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      apply hι
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_iff.mp hgc' (ι x) ⟨x, hx, rfl⟩, rfl⟩

theorem ggA6_sp_core_stated
    {F : Type} [Field F] [Finite F] [CharP F 2] (n : ℕ)
    (P : Subgroup (StatedSp n F)) (hodd : Odd (Nat.card P)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (x : StatedSp n F) (hxP : x ∈ P) (J L : Subgroup (StatedSp n F))
    (hJ : IsComponentOf J (Subgroup.centralizer (P : Set (StatedSp n F))))
    (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set (StatedSp n F))))
    (hJL : J ≤ L) (hPL : ¬ P ≤ Subgroup.centralizer (L : Set (StatedSp n F)))
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    Nat.card F = 2 ∧ ∃ m : ℕ, 3 ≤ m ∧ m ≤ n ∧ LieModel ↥L .PSp m 2 1 := by
  let V := Fin n ⊕ Fin n → F
  let B : BilinForm F V := CFSG.ClassicalGroups.Symplectic.spForm n F
  let H₀ : Subgroup (V ≃ₗ[F] V) := TauCeti.BilinForm.isometryGroup B
  let φ : StatedSp n F ≃* H₀ :=
    (CFSG.ClassicalGroups.Symplectic.spEquiv (m := n) (K := F)).trans
      (gspIsometryGroupEquiv B)
  let ι : StatedSp n F →* (V ≃ₗ[F] V) := H₀.subtype.comp φ.toMonoidHom
  have hι_inj : Function.Injective ι := H₀.subtype_injective.comp φ.injective
  have hran : ι.range = H₀ := by
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact (φ c).2
    · intro hg
      refine ⟨φ.symm ⟨g, hg⟩, ?_⟩
      simp [ι]
  let P' : Subgroup (V ≃ₗ[F] V) := P.map ι
  let x' : V ≃ₗ[F] V := ι x
  let J' : Subgroup (V ≃ₗ[F] V) := J.map ι
  let L' : Subgroup (V ≃ₗ[F] V) := L.map ι
  have hPB : P' ≤ TauCeti.BilinForm.isometryGroup B := by
    intro p hp
    rcases hp with ⟨q, -, rfl⟩
    exact (φ q).2
  have hodd' : Odd (Nat.card P') := by
    show Odd (Nat.card (P.map ι))
    rw [Subgroup.card_map_of_injective hι_inj]
    exact hodd
  have hab' : ∀ a ∈ P', ∀ b ∈ P', a * b = b * a := by
    intro a ha b hb
    rcases Subgroup.mem_map.mp ha with ⟨a₀, ha₀, rfl⟩
    rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
    rw [← map_mul, ← map_mul, hab a₀ ha₀ b₀ hb₀]
  have hxP' : x' ∈ P' := Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  have hJ' : IsComponentOf J' (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (P' : Set (V ≃ₗ[F] V))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hι_inj
      (Q := J) (K := Subgroup.centralizer (P : Set (StatedSp n F)))).mpr hJ
    rw [ggA6sp_map_centralizer_eq_inf ι hι_inj H₀ hran (P : Set (StatedSp n F))] at h
    exact h
  have hL' : IsComponentOf L' (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer ({x'} : Set (V ≃ₗ[F] V))) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff hι_inj
      (Q := L) (K := Subgroup.centralizer ({x} : Set (StatedSp n F)))).mpr hL
    rw [ggA6sp_map_centralizer_eq_inf ι hι_inj H₀ hran ({x} : Set (StatedSp n F)),
      Set.image_singleton] at h
    exact h
  have hJL' : J' ≤ L' := Subgroup.map_mono hJL
  have hPL' : ¬ P' ≤ Subgroup.centralizer (L' : Set (V ≃ₗ[F] V)) := by
    intro h
    apply hPL
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    apply hι_inj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)))
      (ι l) ⟨l, hl, rfl⟩
  have hA6' : Nonempty (↥J' ≃* alternatingGroup (Fin 6)) :=
    hA6.elim fun eA => ⟨(J.equivMapOfInjective ι hι_inj).symm.trans eA⟩
  obtain ⟨hF2, m, hm3, hmle, hLie'⟩ :=
    ggA6_sp_core_abs (B := B) (CFSG.ClassicalGroups.Symplectic.spForm_isAlt)
      (CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate) P' hPB hodd' hab' x' hxP'
      J' L' hJ' hL' hJL' hPL' hA6'
  have hfr : Module.finrank F V = 2 * n := by
    change Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n
    rw [CFSG.ClassicalGroups.Symplectic.finrank_spSpace]
  have hmn : m ≤ n := by omega
  have hLie : LieModel ↥L .PSp m 2 1 :=
    LieModel.of_mulEquiv (L.equivMapOfInjective ι hι_inj).symm hLie'
  exact ⟨hF2, m, hm3, hmn, hLie⟩

end CFSG.StandardType.A6Red
