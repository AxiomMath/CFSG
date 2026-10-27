module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportCore
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

@[expose] def LieZRow (R : Type*) [Group R] : Prop :=
  ∀ x : R, orderOf x = 7 → ∀ J : Subgroup R, IsComponentOf J (Subgroup.centralizer {x}) →
    Odd (Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set R)))

private theorem l937z_df_isComponentOf_map_equiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') {K C : Subgroup G} (h : IsComponentOf K C) :
    IsComponentOf (K.map φ.toMonoidHom) (C.map φ.toMonoidHom) := by
  have h' := CFSG.Assembly.isComponentOf_iff_open.mp h
  exact CFSG.Assembly.isComponentOf_iff_open.mpr
    (CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv φ h')

private theorem l937z_df_map_centralizer_equiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (S : Subgroup G) :
    (Subgroup.centralizer (S : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((S.map φ.toMonoidHom : Subgroup G') : Set G') := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hg s hs
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    show φ.symm y ∈ Subgroup.centralizer (S : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    apply φ.injective
    have := Subgroup.mem_centralizer_iff.mp hy (φ s) ⟨s, hs, rfl⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this

theorem lieZRow_of_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R') (h : LieZRow R) :
    LieZRow R' := by
  intro x' hx' J' hJ'
  have hx : orderOf (e.symm x') = 7 := by rw [MulEquiv.orderOf_eq]; exact hx'
  have hJ : IsComponentOf (J'.map e.symm.toMonoidHom)
      (Subgroup.centralizer {e.symm x'}) := by
    have h1 := l937z_df_isComponentOf_map_equiv e.symm hJ'
    rwa [CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e.symm x'] at h1
  have h2 := h (e.symm x') hx (J'.map e.symm.toMonoidHom) hJ
  have hcard : (J'.map e.symm.toMonoidHom) ⊓
      Subgroup.centralizer (((J'.map e.symm.toMonoidHom) : Subgroup R) : Set R) =
      (J' ⊓ Subgroup.centralizer (J' : Set R')).map e.symm.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ e.symm.injective, l937z_df_map_centralizer_equiv e.symm J']
  rw [hcard, Nat.card_congr
    ((J' ⊓ Subgroup.centralizer (J' : Set R')).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm.toEquiv] at h2
  exact h2

@[expose] def LieSevenOddCentre7sq (K : Type) [Group K] [Finite K] : Prop :=
  ∀ L : Subgroup K, IsSimpleGroup L →
    StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True) → 7 ^ 2 ∣ Nat.card L →
    ∀ x ∈ L, orderOf x = 7 → ∀ J : Subgroup K, IsComponentOf J (L ⊓ Subgroup.centralizer {x}) →
      Odd (Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set K)))

private theorem l937z_df_centralizer_singleton_subgroupOf {G : Type*} [Group G] {L : Subgroup G}
    {x : G} (hx : x ∈ L) :
    Subgroup.centralizer ({(⟨x, hx⟩ : ↥L)} : Set ↥L) =
      (Subgroup.centralizer ({x} : Set G)).subgroupOf L := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact congrArg Subtype.val (hy ⟨x, hx⟩ (Set.mem_singleton _))
  · intro hy z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subtype.ext (hy x (Set.mem_singleton x))

private theorem l937z_df_centralizer_subgroupOf {G : Type*} [Group G] (J L : Subgroup G)
    (hJL : J ≤ L) :
    Subgroup.centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) =
      (Subgroup.centralizer (J : Set G)).subgroupOf L := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hy z hz
    exact congrArg Subtype.val (hy ⟨z, hJL hz⟩ (Subgroup.mem_subgroupOf.mpr hz))
  · intro hy z hz
    exact Subtype.ext (hy z (Subgroup.mem_subgroupOf.mp hz))

private theorem l937z_df_subnormal_subgroupOf {G : Type*} [Group G] {L : Subgroup G}
    {J D : Subgroup G} (hDL : D ≤ L) (h : CFSG.Assembly.IsSubnormal J D) :
    CFSG.Assembly.IsSubnormal (J.subgroupOf L) (D.subgroupOf L) := by
  have hJ'le : J.subgroupOf L ≤ D.subgroupOf L := Subgroup.subgroupOf_mono L h.le
  refine (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJ'le).mpr ?_
  have hcomap : ((J.subgroupOf D).comap (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom) =
      (J.subgroupOf L).subgroupOf (D.subgroupOf L) := by
    ext y
    rfl
  rw [← hcomap]
  exact Subgroup.IsSubnormal.comap (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom h.subgroupOf

private theorem l937z_df_card {G : Type*} [Group G] (J L : Subgroup G) (hJL : J ≤ L) :
    Nat.card ↥(J.subgroupOf L ⊓
      Subgroup.centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L)) =
    Nat.card ↥(J ⊓ Subgroup.centralizer (J : Set G)) := by
  have h1 : J.subgroupOf L ⊓ Subgroup.centralizer ((J.subgroupOf L : Subgroup ↥L) : Set ↥L) =
      (J ⊓ Subgroup.centralizer (J : Set G)).subgroupOf L := by
    rw [l937z_df_centralizer_subgroupOf J L hJL]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hJL)).toEquiv

theorem lieSevenOddCentre7sq_of_rows {K : Type} [Group K] [Finite K]
    (h : ∀ L : Subgroup K, IsSimpleGroup L →
      StandardType.LargeEvenMarking L (fun _ _ _ _ _ _ => True) → 7 ^ 2 ∣ Nat.card L →
      LieZRow ↥L) : LieSevenOddCentre7sq K := by
  intro L hL hmark h7 x hxL hx J hJ
  have hx' : orderOf (⟨x, hxL⟩ : ↥L) = 7 := by rw [Subgroup.orderOf_mk]; exact hx
  have hJL : J ≤ L := fun g hg => (hJ.1 hg).1
  have hJ' : IsComponentOf (J.subgroupOf L)
      (Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) := by
    have hle : J.subgroupOf L ≤ Subgroup.centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := by
      have h1 : J.subgroupOf L ≤ (Subgroup.centralizer ({x} : Set K)).subgroupOf L := by
        intro y hy
        exact (hJ.1 (Subgroup.mem_subgroupOf.mp hy)).2
      rwa [← l937z_df_centralizer_singleton_subgroupOf hxL] at h1
    refine ⟨hle, ?_, ?_⟩
    · have h1 := l937z_df_subnormal_subgroupOf (L := L) (J := J)
          (D := L ⊓ Subgroup.centralizer {x}) inf_le_left hJ.2.1
      rwa [Subgroup.inf_subgroupOf_left, ← l937z_df_centralizer_singleton_subgroupOf hxL] at h1
    · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hJL) hJ.2.2
  have h2 := h L hL hmark h7 ⟨x, hxL⟩ hx' (J.subgroupOf L) hJ'
  have hcard := l937z_df_card J L hJL
  rw [hcard] at h2
  exact h2

private theorem l937z_df_simple_pullback {K K' : Type} [Group K] [Group K'] (e : K ≃* K')
    {L' : Subgroup K'} (hL' : IsSimpleGroup ↥L') :
    IsSimpleGroup ↥(L'.map e.symm.toMonoidHom) :=
  (L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.isSimpleGroup

theorem lieSevenOddCentre7sq_of_mulEquiv {K K' : Type} [Group K] [Finite K] [Group K']
    [Finite K'] (e : K ≃* K') (h : LieSevenOddCentre7sq K) : LieSevenOddCentre7sq K' := by
  intro L' hL' hmark' h7' x' hx'L' hx' J' hJ'
  have eL : ↥L' ≃* ↥(L'.map e.symm.toMonoidHom) :=
    L'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hLs := l937z_df_simple_pullback e hL'
  have hLm := largeEvenMarking_true_of_mulEquiv eL hmark'
  have hxL : e.symm x' ∈ L'.map e.symm.toMonoidHom := ⟨x', hx'L', rfl⟩
  have hord : orderOf (e.symm x') = 7 := by rw [MulEquiv.orderOf_eq]; exact hx'
  have h7 : 7 ^ 2 ∣ Nat.card ↥(L'.map e.symm.toMonoidHom) := by
    rwa [← Nat.card_congr eL.toEquiv]
  have hJ : IsComponentOf (J'.map e.symm.toMonoidHom)
      (L'.map e.symm.toMonoidHom ⊓ Subgroup.centralizer {e.symm x'}) := by
    have h1 := l937z_df_isComponentOf_map_equiv e.symm hJ'
    rwa [Subgroup.map_inf _ _ _ e.symm.injective,
      CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e.symm x'] at h1
  have h2 := h (L'.map e.symm.toMonoidHom) hLs hLm h7 (e.symm x') hxL hord
    (J'.map e.symm.toMonoidHom) hJ
  have hcard : (J'.map e.symm.toMonoidHom) ⊓
      Subgroup.centralizer (((J'.map e.symm.toMonoidHom) : Subgroup K) : Set K) =
      (J' ⊓ Subgroup.centralizer (J' : Set K')).map e.symm.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ e.symm.injective, l937z_df_map_centralizer_equiv e.symm J']
  rw [hcard, Nat.card_congr
    ((J' ⊓ Subgroup.centralizer (J' : Set K')).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm.toEquiv] at h2
  exact h2

end CFSG.StandardType.SporadicShape
