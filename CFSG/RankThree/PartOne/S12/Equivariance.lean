module

public import CFSG.RankThree.PartOne.S12.Hyp
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

variable {G : Type} [Group G] [Finite G]

@[expose] def conjBy (w : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj w).toMonoidHom

@[expose] noncomputable def conjAut (E : Subgroup G) (w : G)
    (hw : w ∈ Subgroup.normalizer (E : Set G)) : MulAut E :=
  E.normalizerMonoidHom ⟨w, hw⟩


namespace Equivariance

omit [Finite G] in
theorem mem_conjBy {w x : G} {H : Subgroup G} : x ∈ conjBy w H ↔ w⁻¹ * x * w ∈ H := by
  unfold conjBy
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite G] in
theorem conjBy_conjBy_inv (w : G) (H : Subgroup G) : conjBy w (conjBy w⁻¹ H) = H := by
  ext x
  rw [mem_conjBy, mem_conjBy]
  simp [mul_assoc]

omit [Finite G] in
theorem conjBy_inv_conjBy (w : G) (H : Subgroup G) : conjBy w⁻¹ (conjBy w H) = H := by
  simpa using conjBy_conjBy_inv w⁻¹ H

omit [Finite G] in
theorem conjBy_eq_of_mem_normalizer {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) : conjBy w E = E := by
  ext x
  rw [mem_conjBy]
  have := Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (E : Set G)).inv_mem hw) x
  simpa using this.symm

omit [Finite G] in
theorem map_inSubgroup_of_equivariant {G' : Type} [Group G']
    (F : ∀ (K : Type) [Group K], Subgroup K) (φ : G ≃* G') (X : Subgroup G)
    (hF : (F ↥X).map (X.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom =
      F ↥(X.map φ.toMonoidHom)) :
    (inSubgroup F X).map φ.toMonoidHom = inSubgroup F (X.map φ.toMonoidHom) := by
  rw [inSubgroup, inSubgroup, ← hF, Subgroup.map_map, Subgroup.map_map]
  rfl


@[expose] def centralizerEquiv {G' : Type} [Group G'] (e : G ≃* G') (a : G) :
    Subgroup.centralizer ({a} : Set G) ≃* Subgroup.centralizer ({e a} : Set G') where
  toFun y := ⟨e y, by
    have h := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    rw [← map_mul, ← map_mul, h]⟩
  invFun y := ⟨e.symm y, by
    have h := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h⟩
  left_inv y := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)

omit [Finite G] in
theorem coe_centralizerEquiv {G' : Type} [Group G'] (e : G ≃* G') (a : G)
    (y : Subgroup.centralizer ({a} : Set G)) : ((centralizerEquiv e a y : _) : G') = e y := rfl

theorem map_mem_thetaComponentsAt {G' : Type} [Group G'] {p : ℕ} (hp : p.Prime) (e : G ≃* G')
    (a : G) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt p a) :
    Y.map e.toMonoidHom ∈ thetaComponentsAt p (e a) := by
  obtain ⟨L, hL, rfl⟩ := hY
  refine ⟨L.map (centralizerEquiv e a).toMonoidHom,
    map_mulEquiv_mem_thetaComponents hp (centralizerEquiv e a) hL, ?_⟩
  beta_reduce
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isElementaryAbelian_map {p : ℕ} {R S : Type*} [Group R] [Group S] {A : Subgroup R}
    (hA : IsElementaryAbelian p A) (f : R →* S) : IsElementaryAbelian p (A.map f) :=
  CFSG.IsElementaryAbelian.subgroup_map hA _

omit [Finite G] in
theorem conjBy_ne_bot {w : G} {S : Subgroup G} (hS : S ≠ ⊥) : conjBy w S ≠ ⊥ := fun h =>
  hS ((Subgroup.map_eq_bot_iff_of_injective S (MulAut.conj w).injective).1 h)

omit [Finite G] in
theorem conjBy_le_normalizer {w : G} {B S : Subgroup G}
    (h : B ≤ Subgroup.normalizer (S : Set G)) :
    conjBy w B ≤ Subgroup.normalizer (conjBy w S : Set G) := by
  intro x hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
  have := Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom (h hb)
  rwa [Subgroup.map_equiv_normalizer_eq] at this

omit [Finite G] in
theorem coe_conjAut {E : Subgroup G} {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (e : E) : ((conjAut E w hw e : E) : G) = w * e * w⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe E ⟨w, hw⟩ e

omit [Finite G] in
theorem conj_conjAut_normalizerMonoidHom {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (y : ↥(Subgroup.normalizer (E : Set G))) :
    (MulAut.conj (conjAut E w hw)) (E.normalizerMonoidHom y) =
      E.normalizerMonoidHom (⟨w, hw⟩ * y * ⟨w, hw⟩⁻¹) := by
  unfold conjAut
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

omit [Finite G] in
theorem autMoved_conj {E : Subgroup G} (ψ t : MulAut E) :
    autMoved E (ψ * t * ψ⁻¹) = (autMoved E t).map ψ.toMonoidHom := by
  unfold autMoved
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨t (ψ⁻¹ e) * (ψ⁻¹ e)⁻¹, ⟨ψ⁻¹ e, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]
  · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
    refine ⟨ψ e, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]

omit [Finite G] in
theorem autFixed_conj {E : Subgroup G} (ψ t : MulAut E) :
    autFixed E (ψ * t * ψ⁻¹) = (autFixed E t).map ψ.toMonoidHom := by
  ext e
  rw [Subgroup.mem_map_equiv]
  show ψ (t (ψ⁻¹ e)) = e ↔ t (ψ.symm e) = ψ.symm e
  constructor
  · intro h
    have h1 := congrArg ψ.symm h
    rwa [MulEquiv.symm_apply_apply] at h1
  · intro h
    have h1 : t (ψ⁻¹ e) = ψ⁻¹ e := h
    rw [h1]
    exact MulEquiv.apply_symm_apply ψ e

omit [Finite G] in
theorem autFixedInG_conj {E : Subgroup G} (t : MulAut E) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    autFixedInG E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = conjBy w (autFixedInG E t) := by
  unfold autFixedInG conjBy
  rw [autFixed_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem autMovedInG_conj {E : Subgroup G} (t : MulAut E) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    autMovedInG E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = conjBy w (autMovedInG E t) := by
  unfold autMovedInG conjBy
  rw [autMoved_conj, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem centralizer_conjBy (w : G) (S : Subgroup G) :
    Subgroup.centralizer (conjBy w S : Set G) = conjBy w (Subgroup.centralizer (S : Set G)) := by
  ext x
  rw [mem_conjBy, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have h1 := h (w * s * w⁻¹) (Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hs)
    calc s * (w⁻¹ * x * w) = w⁻¹ * ((w * s * w⁻¹) * x) * w := by group
      _ = w⁻¹ * (x * (w * s * w⁻¹)) * w := by rw [h1]
      _ = (w⁻¹ * x * w) * s := by group
  · intro h y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 := h s hs
    calc (MulAut.conj w).toMonoidHom s * x = w * (s * (w⁻¹ * x * w)) * w⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
      _ = w * ((w⁻¹ * x * w) * s) * w⁻¹ := by rw [h1]
      _ = x * (MulAut.conj w).toMonoidHom s := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group

omit [Finite G] in
theorem pElementSubgroup_conjBy (p : ℕ) (w : G) (X : Subgroup G) :
    pElementSubgroup p (conjBy w X) = conjBy w (pElementSubgroup p X) := by
  unfold pElementSubgroup conjBy
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, k, hk⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨x, ⟨hx, k, ?_⟩, rfl⟩
    rw [← hk]
    exact (MulEquiv.orderOf_eq (MulAut.conj w) x).symm
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hx, k, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
    exact hk

theorem layer_map_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (layer A).map e.toMonoidHom = layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

omit [Finite G] in
theorem inSubgroup_layer_conjBy (w : G) (H : Subgroup G) :
    inSubgroup (fun K _ => layer K) (conjBy w H) =
      conjBy w (inSubgroup (fun K _ => layer K) H) :=
  (map_inSubgroup_of_equivariant (fun K _ => layer K) (MulAut.conj w) H
    (layer_map_mulEquiv _)).symm

theorem statedClassicalModel_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : StatedLieTag} {n q f : ℕ} (h : StatedClassicalModel A t n q f) :
    StatedClassicalModel B t n q f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

omit [Finite G] in
theorem statedClassicalModel_conjBy_iff (w : G) (K : Subgroup G) {t : StatedLieTag}
    {n q f : ℕ} : StatedClassicalModel (conjBy w K) t n q f ↔ StatedClassicalModel K t n q f := by
  let e : K ≃* conjBy w K :=
    K.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  exact ⟨statedClassicalModel_of_mulEquiv e.symm, statedClassicalModel_of_mulEquiv e⟩

omit [Finite G] in
theorem kExceptional_conjBy_iff (p f : ℕ) (w : G) (K0 : Subgroup G) :
    kExceptional p (conjBy w K0) f ↔ kExceptional p K0 f := by
  let e : K0 ≃* conjBy w K0 :=
    K0.equivMapOfInjective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective
  have hc : (Subgroup.center K0).map (e : K0 →* conjBy w K0) = Subgroup.center (conjBy w K0) :=
    Subgroup.map_center_eq e
  let e' : K0 ⧸ Subgroup.center K0 ≃* (conjBy w K0) ⧸ Subgroup.center (conjBy w K0) :=
    QuotientGroup.congr _ _ e hc
  unfold kExceptional
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨statedClassicalModel_of_mulEquiv e'.symm, statedClassicalModel_of_mulEquiv e'⟩

end Equivariance

theorem aschbacherSolvableCore_map_mulEquiv {X X' : Type} [Group X] [Group X'] [Finite X]
    {p : ℕ} (hp : p.Prime) (e : X ≃* X') :
    (aschbacherSolvableCore p X).map e.toMonoidHom = aschbacherSolvableCore p X' :=
  CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv hp e

theorem inSubgroup_theta_conjBy {p : ℕ} (hp : p.Prime) (w : G) (L : Subgroup G) :
    inSubgroup (aschbacherSolvableCore p) (conjBy w L) =
      conjBy w (inSubgroup (aschbacherSolvableCore p) L) := by
  have h := Equivariance.map_inSubgroup_of_equivariant (aschbacherSolvableCore p) (MulAut.conj w) L
    (aschbacherSolvableCore_map_mulEquiv hp (L.equivMapOfInjective (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective))
  exact h.symm

theorem conjBy_mem_thetaComponentsAt {p : ℕ} (hp : p.Prime) (w a : G) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt p a) : conjBy w Y ∈ thetaComponentsAt p (w * a * w⁻¹) :=
  Equivariance.map_mem_thetaComponentsAt hp (MulAut.conj w) a hY

theorem conjBy_mem_thetaComponentFamily {p : ℕ} (hp : p.Prime) (w : G) {A Y : Subgroup G}
    (hY : Y ∈ thetaComponentFamily p A) : conjBy w Y ∈ thetaComponentFamily p (conjBy w A) := by
  simp only [thetaComponentFamily, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop] at hY ⊢
  obtain ⟨a, ⟨haA, ha1⟩, hYa⟩ := hY
  refine ⟨w * a * w⁻¹, ⟨Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom haA, ?_⟩,
    conjBy_mem_thetaComponentsAt hp w a hYa⟩
  intro h
  exact ha1 (conj_eq_one_iff.1 h)

theorem sectionTenRel_conjBy {p : ℕ} (hp : p.Prime) (w : G) {L K : Subgroup G} :
    sectionTenRel p (conjBy w L) (conjBy w K) ↔ sectionTenRel p L K := by
  unfold sectionTenRel
  rw [inSubgroup_theta_conjBy hp w L]
  have h1 : conjBy w L ⊓ conjBy w K ⊔ conjBy w (inSubgroup (aschbacherSolvableCore p) L) =
      conjBy w (L ⊓ K ⊔ inSubgroup (aschbacherSolvableCore p) L) := by
    unfold conjBy
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj w).injective]
  rw [h1]
  exact (Subgroup.map_injective (MulAut.conj w).injective).eq_iff

omit [Finite G] in
theorem conjBy_mem_admissibleTriples {p : ℕ} {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) : conjBy w B ∈ admissibleTriples p E := by
  obtain ⟨hBE, hBel, hBcard, S, hS0, hS2, hBS⟩ := hB
  refine ⟨?_, ?_, ?_, conjBy w S, Equivariance.conjBy_ne_bot hS0, hS2.map _,
    Equivariance.conjBy_le_normalizer hBS⟩
  · calc conjBy w B ≤ conjBy w E := Subgroup.map_mono hBE
      _ = E := Equivariance.conjBy_eq_of_mem_normalizer hw
  · exact Equivariance.isElementaryAbelian_map hBel _
  · rw [conjBy, Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hBcard

theorem conjBy_mem_thetaCompE {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {X : Subgroup G} (hX : X ∈ thetaCompE p E) :
    conjBy w X ∈ thetaCompE p E := by
  obtain ⟨B, hB, hXB⟩ := hX
  exact ⟨conjBy w B, conjBy_mem_admissibleTriples hw hB,
    conjBy_mem_thetaComponentFamily hp w hXB⟩

theorem conjBy_mem_sectionTenZero {p : ℕ} (hp : p.Prime) (w : G) {B X : Subgroup G}
    (hX : X ∈ sectionTenZero p B) : conjBy w X ∈ sectionTenZero p (conjBy w B) := by
  obtain ⟨hXF, S, hSX, hS0, hS2, hBS, hSB⟩ := hX
  refine ⟨conjBy_mem_thetaComponentFamily hp w hXF, conjBy w S, Subgroup.map_mono hSX,
    Equivariance.conjBy_ne_bot hS0, hS2.map _, Equivariance.conjBy_le_normalizer hBS, ?_⟩
  unfold conjBy
  rw [← Subgroup.map_commutator, ← hSB]

theorem conjBy_mem_thetaCompE_iff {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {X : Subgroup G} :
    conjBy w X ∈ thetaCompE p E ↔ X ∈ thetaCompE p E := by
  refine ⟨fun h => ?_, conjBy_mem_thetaCompE hp hw⟩
  have := conjBy_mem_thetaCompE hp ((Subgroup.normalizer (E : Set G)).inv_mem hw) h
  rwa [Equivariance.conjBy_inv_conjBy] at this

theorem conjBy_mem_thetaCompStarE {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaCompStarE p E) : conjBy w X ∈ thetaCompStarE p E := by
  refine ⟨conjBy_mem_thetaCompE hp hw hX.1, fun J hJ hrel => ?_⟩
  have hJ' : conjBy w⁻¹ J ∈ thetaCompE p E :=
    conjBy_mem_thetaCompE hp ((Subgroup.normalizer (E : Set G)).inv_mem hw) hJ
  have hrel' : sectionTenRel p X (conjBy w⁻¹ J) := by
    rw [← sectionTenRel_conjBy hp w, Equivariance.conjBy_conjBy_inv]
    exact hrel
  have h2 := hX.2 _ hJ' hrel'
  have h3 := (sectionTenRel_conjBy hp w).2 h2
  rwa [Equivariance.conjBy_conjBy_inv] at h3

theorem conjBy_mem_thetaCompZeroStarE {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) {X : Subgroup G}
    (hX : X ∈ thetaCompZeroStarE p E) : conjBy w X ∈ thetaCompZeroStarE p E := by
  obtain ⟨⟨B, hB, hXB⟩, hXstar⟩ := hX
  exact ⟨⟨conjBy w B, conjBy_mem_admissibleTriples hw hB, conjBy_mem_sectionTenZero hp w hXB⟩,
    conjBy_mem_thetaCompStarE hp hw hXstar⟩

omit [Finite G] in
theorem torusImage_conjBy (E Y : Subgroup G) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    torusImage E (conjBy w Y) =
      (torusImage E Y).map (MulAut.conj (conjAut E w hw)).toMonoidHom := by
  have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := inv_mem hw
  ext φ
  constructor
  · intro hφ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hφ
    have hx' : w⁻¹ * (x : G) * w ∈ Y := Equivariance.mem_conjBy.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxN : w⁻¹ * (x : G) * w ∈ Subgroup.normalizer (E : Set G) :=
      mul_mem (mul_mem hw' x.2) hw
    refine Subgroup.mem_map.2 ⟨E.normalizerMonoidHom ⟨w⁻¹ * (x : G) * w, hxN⟩,
      Subgroup.mem_map.2 ⟨⟨w⁻¹ * (x : G) * w, hxN⟩, Subgroup.mem_subgroupOf.2 hx', rfl⟩, ?_⟩
    have h1 : (⟨w, hw⟩ : Subgroup.normalizer (E : Set G)) * ⟨w⁻¹ * (x : G) * w, hxN⟩ *
        (⟨w, hw⟩ : Subgroup.normalizer (E : Set G))⁻¹ = x := Subtype.ext (by simp [mul_assoc])
    show (MulAut.conj (conjAut E w hw)) (E.normalizerMonoidHom ⟨w⁻¹ * (x : G) * w, hxN⟩) = _
    rw [Equivariance.conj_conjAut_normalizerMonoidHom, h1]
  · intro hφ
    obtain ⟨φ0, hφ0, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hφ0
    refine Subgroup.mem_map.2 ⟨⟨w, hw⟩ * y * ⟨w, hw⟩⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
    · exact ⟨y, Subgroup.mem_subgroupOf.1 hy, rfl⟩
    · exact (Equivariance.conj_conjAut_normalizerMonoidHom hw y).symm

omit [Finite G] in
theorem isAutReflection_conj {p : ℕ} {E : Subgroup G} (ψ t : MulAut E)
    (ht : IsAutReflection p E t) : IsAutReflection p E (ψ * t * ψ⁻¹) := by
  obtain ⟨hord, hcard⟩ := ht
  refine ⟨?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hord
  · rw [Equivariance.autMoved_conj, Subgroup.card_map_of_injective ψ.injective]
    exact hcard

theorem conj_mem_reflectionSet {p : ℕ} (hp : p.Prime) {E : Subgroup G} {t : MulAut E}
    (ht : t ∈ reflectionSet p E) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    conjAut E w hw * t * (conjAut E w hw)⁻¹ ∈ reflectionSet p E := by
  obtain ⟨hrefl, X, hX, htX⟩ := ht
  refine ⟨isAutReflection_conj _ _ hrefl, conjBy w X, conjBy_mem_thetaCompZeroStarE hp hw hX, ?_⟩
  rw [torusImage_conjBy E X hw]
  exact Subgroup.mem_map_of_mem (MulAut.conj (conjAut E w hw)).toMonoidHom htX

omit [Finite G] in
theorem kZero_conj (p : ℕ) {E : Subgroup G} (t : MulAut E) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    kZero p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) = conjBy w (kZero p E t) := by
  unfold kZero
  rw [Equivariance.autFixedInG_conj t hw, Equivariance.centralizer_conjBy,
    Equivariance.inSubgroup_layer_conjBy, Equivariance.pElementSubgroup_conjBy]

omit [Finite G] in
theorem isKt_conj {p : ℕ} {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (hK : IsKt p E t K) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    IsKt p E (conjAut E w hw * t * (conjAut E w hw)⁻¹) (conjBy w K) := by
  have hk := kZero_conj p t hw
  unfold IsKt at hK ⊢
  rw [hk]
  obtain ⟨h1, h2⟩ := hK
  refine ⟨fun f hf => ?_, fun hne => ?_⟩
  · obtain ⟨hle, hmod, hmov⟩ := h1 f ((Equivariance.kExceptional_conjBy_iff p f w _).1 hf)
    refine ⟨Subgroup.map_mono hle, (Equivariance.statedClassicalModel_conjBy_iff w K).2 hmod, ?_⟩
    rw [Equivariance.autMovedInG_conj t hw]
    exact Subgroup.map_mono hmov
  · have hne' : ¬ ∃ f, kExceptional p (kZero p E t) f := fun ⟨f, hf⟩ =>
      hne ⟨f, (Equivariance.kExceptional_conjBy_iff p f w _).2 hf⟩
    rw [h2 hne']

theorem lieGenerated_conjBy {p : ℕ} (hp : p.Prime) {E : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    conjBy w (lieGenerated p E) = lieGenerated p E := by
  have key : ∀ v ∈ Subgroup.normalizer (E : Set G), ∀ K : Subgroup G,
      K ∈ {K | ∃ t ∈ reflectionSet p E, IsKt p E t K} →
        conjBy v K ∈ {K | ∃ t ∈ reflectionSet p E, IsKt p E t K} := by
    rintro v hv K ⟨t, ht, hKt⟩
    exact ⟨conjAut E v hv * t * (conjAut E v hv)⁻¹, conj_mem_reflectionSet hp ht hv,
      isKt_conj hKt hv⟩
  unfold lieGenerated
  change MulEquiv.mapSubgroup (MulAut.conj w) (sSup _) = sSup _
  rw [OrderIso.map_sSup, ← sSup_image]
  congr 1
  ext K
  constructor
  · rintro ⟨K', hK', rfl⟩
    exact key w hw K' hK'
  · intro hK
    exact ⟨conjBy w⁻¹ K, key w⁻¹ ((Subgroup.normalizer (E : Set G)).inv_mem hw) K hK,
      Equivariance.conjBy_conjBy_inv w K⟩

theorem torusNormalizer_le_lieNormalizer {p : ℕ} (hp : p.Prime) (E : Subgroup G) :
    torusNormalizer E ≤ lieNormalizer p E := by
  intro w hw
  have h : conjBy w (lieGenerated p E) = lieGenerated p E := lieGenerated_conjBy hp hw
  show w ∈ Subgroup.normalizer (lieGenerated p E : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hx
  · intro hx
    rw [← h] at hx
    have h1 := Equivariance.mem_conjBy.1 hx
    simpa [mul_assoc] using h1

end CFSG.RankThree.PartOne
