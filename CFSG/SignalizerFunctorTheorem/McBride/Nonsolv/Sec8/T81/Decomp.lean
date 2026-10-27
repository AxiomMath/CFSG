module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Cover
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

omit [Finite G] in
theorem zOf_comm {z w : G} (hz : z ∈ zOf S) (hw : w ∈ zOf S) : w * z = z * w :=
  (mem_zOf_iff.mp hz).2 w (zOf_le S hw)

theorem commute_mL
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {K K' : Subgroup G} (hK : K ∈ lcal (thetaOf θ B))
    (hK' : K' ∈ lcal (thetaOf θ B)) (hne : K ≠ K') :
    ∀ x ∈ mL θ (zOf S) B K, ∀ y ∈ mL θ (zOf S) B K', y * x = x * y := by
  have hdp := (h.isRegFam_plane_of_typeA hA hB).isDirectProduct
  have h1 : K ≤ Subgroup.centralizer (mL θ (zOf S) B K' : Set G) := by
    change K ≤ Subgroup.centralizer ((K' ⊔ zL θ (zOf S) B K' : Subgroup G) : Set G)
    rw [centralizer_sup]
    refine le_inf (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hdp.commute K hK K' hK' hne x hx y hy).eq.symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((mem_zL_iff.mp hy).2 K hK hne x hx).symm
  have h2 : zL θ (zOf S) B K ≤ Subgroup.centralizer (mL θ (zOf S) B K' : Set G) := by
    change _ ≤ Subgroup.centralizer ((K' ⊔ zL θ (zOf S) B K' : Subgroup G) : Set G)
    rw [centralizer_sup]
    refine le_inf (fun z hz => ?_) (fun z hz => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (mem_zL_iff.mp hz).2 K' hK' hne.symm y hy
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact zOf_comm (zL_le θ (zOf S) B K hz) (zL_le θ (zOf S) B K' hy)
  intro x hx y hy
  exact Subgroup.mem_centralizer_iff.mp (sup_le h1 h2 hx) y hy

theorem mL_ne_of_ne
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {K K' : Subgroup G} (hK : K ∈ lcal (thetaOf θ B))
    (hK' : K' ∈ lcal (thetaOf θ B)) (hne : K ≠ K') :
    mL θ (zOf S) B K ≠ mL θ (zOf S) B K' := by
  intro heq
  obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hK
  refine hnc (isMulCommutative_iff.mpr fun x y => Subtype.ext ?_)
  have hxm : (x : G) ∈ mL θ (zOf S) B K := le_mL θ _ B K x.2
  have hym : (y : G) ∈ mL θ (zOf S) B K' := heq ▸ le_mL θ _ B K y.2
  exact (commute_mL h hA hB hK hK' hne _ hxm _ hym).symm

theorem isDirectProduct_mFam
    (h : Counterexample p A θ) (hA : TypeA p A θ)
    (hr : InPiTheta A θ r) (hS : IsSr p A θ r S) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) :
    IsDirectProduct (mFam θ (zOf S) B) (sSup (Msig p A θ)) := by
  have hcomm : ∀ J ∈ mFam θ (zOf S) B, ∀ L ∈ mFam θ (zOf S) B, J ≠ L →
      ∀ x ∈ J, ∀ y ∈ L, Commute x y := by
    rintro _ ⟨K, hK, rfl⟩ _ ⟨K', hK', rfl⟩ hne x hx y hy
    have hKK' : K ≠ K' := fun hKK' => hne (hKK' ▸ rfl)
    exact (commute_mL h hA hB hK hK' hKK' x hx y hy).symm
  have hsup : sSup (mFam θ (zOf S) B) = sSup (Msig p A θ) := by
    rw [← mAll_eq_sSup_msig h hA hr hS hB]
    refine le_antisymm (sSup_le ?_) (iSup₂_le fun L hL => le_sSup ⟨L, hL, rfl⟩)
    rintro _ ⟨L, hL, rfl⟩
    exact mL_le_mAll hL
  refine ⟨hcomm, ?_, hsup⟩
  intro J hJ
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hxJ, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxM : x ∈ sSup (Msig p A θ) := hsup ▸ le_sSup hJ hxJ
  have hP : ∀ y ∈ J, y * x = x * y := by
    intro y hy
    have : sSup (mFam θ (zOf S) B \ {J}) ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sSup_le fun Y hY z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm Y hY.1 J hJ hY.2 z hz y hy).eq
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hxP)).symm
  have hQ : ∀ y ∈ sSup (mFam θ (zOf S) B \ {J}), y * x = x * y := by
    intro y hy
    have : sSup (mFam θ (zOf S) B \ {J}) ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sSup_le fun Y hY z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm Y hY.1 J hJ hY.2 z hz x hxJ).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hy)
  have hxZ : x ∈ zOf (sSup (Msig p A θ)) := by
    refine mem_zOf_iff.mpr ⟨hxM, fun w hw => ?_⟩
    have hle : J ⊔ sSup (mFam θ (zOf S) B \ {J}) ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun y hy => by rw [Subgroup.mem_centralizer_singleton_iff]; exact hP y hy)
        (fun y hy => by rw [Subgroup.mem_centralizer_singleton_iff]; exact hQ y hy)
    have hMle : sSup (Msig p A θ) ≤ J ⊔ sSup (mFam θ (zOf S) B \ {J}) := by
      rw [← hsup]
      refine sSup_le fun Y hY => ?_
      by_cases hYJ : Y = J
      · exact hYJ ▸ le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hY, hYJ⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hMle hw))
  rw [h.lemma_6_4] at hxZ
  exact hxZ

theorem inf_mL_eq
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) {L : Subgroup G}
    (hL : L ∈ lcal (thetaOf θ B)) : thetaOf θ B ⊓ mL θ (zOf S) B L = L := by
  have hΩ := h.isRegFam_plane_of_typeA hA hB
  have hdp := isDirectProduct_mFam h hA hr hS hB
  refine le_antisymm ?_ (le_inf (lcal_le hL) (le_mL θ _ B L))
  intro x hx
  obtain ⟨hxH, hxM⟩ := Subgroup.mem_inf.mp hx
  have hpair := hΩ.isDirectProduct.isDirectPair hL
  obtain ⟨l, hl, u, hu, rfl⟩ := (mem_sup_iff_of_commute hpair.commute).mp (hpair.sup_eq ▸ hxH)
  have hmL : mL θ (zOf S) B L ∈ mFam θ (zOf S) B := ⟨L, hL, rfl⟩
  have hu1 : u ∈ sSup (mFam θ (zOf S) B \ {mL θ (zOf S) B L}) := by
    have : sSup (lcal (thetaOf θ B) \ {L}) ≤
        sSup (mFam θ (zOf S) B \ {mL θ (zOf S) B L}) := by
      refine sSup_le fun K hK => ?_
      refine le_trans (le_mL θ (zOf S) B K) (le_sSup ⟨⟨K, hK.1, rfl⟩, fun hmem => ?_⟩)
      exact mL_ne_of_ne h hA hB hK.1 hL (fun hKL => hK.2 (Set.mem_singleton_iff.mpr hKL))
        (Set.mem_singleton_iff.mp hmem)
    exact this hu
  have hu2 : u ∈ mL θ (zOf S) B L := by
    have : u = l⁻¹ * (l * u) := by group
    rw [this]
    exact mul_mem (inv_mem (le_mL θ _ B L hl)) hxM
  have hu3 : u = 1 := (Subgroup.disjoint_def.mp (hdp.indep hmL)) hu2 hu1
  rw [hu3, mul_one]
  exact hl

theorem normalizes_zOf (hS : IsSr p A θ r S) : A ≤ Subgroup.normalizer (zOf S : Set G) :=
  fun _ ha => mem_normalizer_zOf (Counterexample.normalizes_of_isSr hS ha)

theorem map_conj_zL_le
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {Z : Subgroup G}
    (hZ : A ≤ Subgroup.normalizer (Z : Set G)) {a : G} (ha : a ∈ A) {L : Subgroup G} :
    (zL θ Z B L).map (MulAut.conj a).toMonoidHom ≤
      zL θ Z B (L.map (MulAut.conj a).toMonoidHom) := by
  have hΩ := h.isRegFam_plane_of_typeA hA hB
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwZ, hwc⟩ := mem_zL_iff.mp hw
  refine mem_zL_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hZ ha) w).mp hwZ, ?_⟩
  intro K' hK' hne y hy
  have hK : K'.map (MulAut.conj a⁻¹).toMonoidHom ∈ lcal (thetaOf θ B) :=
    hΩ.map_conj_mem a⁻¹ (inv_mem ha) K' hK'
  have hKL : K'.map (MulAut.conj a⁻¹).toMonoidHom ≠ L := by
    intro heq
    apply hne
    rw [← heq, Near.Thm210.map_conj_map_conj, mul_inv_cancel, Near.Thm210.map_conj_one]
  have hy' : a⁻¹ * y * a ∈ K'.map (MulAut.conj a⁻¹).toMonoidHom := ⟨y, hy, by simp⟩
  have h1 := hwc _ hK hKL _ hy'
  show y * (a * w * a⁻¹) = a * w * a⁻¹ * y
  calc y * (a * w * a⁻¹) = a * ((a⁻¹ * y * a) * w) * a⁻¹ := by group
    _ = a * (w * (a⁻¹ * y * a)) * a⁻¹ := by rw [h1]
    _ = a * w * a⁻¹ * y := by group

theorem map_conj_zL
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {Z : Subgroup G}
    (hZ : A ≤ Subgroup.normalizer (Z : Set G)) {a : G} (ha : a ∈ A) {L : Subgroup G} :
    (zL θ Z B L).map (MulAut.conj a).toMonoidHom =
      zL θ Z B (L.map (MulAut.conj a).toMonoidHom) := by
  refine le_antisymm (map_conj_zL_le h hA hB hZ ha) ?_
  intro z hz
  have h1 := map_conj_zL_le h hA hB hZ (inv_mem ha) (L := L.map (MulAut.conj a).toMonoidHom)
    ⟨z, hz, rfl⟩
  rw [Near.Thm210.map_conj_map_conj, inv_mul_cancel, Near.Thm210.map_conj_one] at h1
  exact ⟨_, h1, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩

theorem map_conj_mL
    (h : Counterexample p A θ) (hA : TypeA p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) {Z : Subgroup G}
    (hZ : A ≤ Subgroup.normalizer (Z : Set G)) {a : G} (ha : a ∈ A) {L : Subgroup G} :
    (mL θ Z B L).map (MulAut.conj a).toMonoidHom =
      mL θ Z B (L.map (MulAut.conj a).toMonoidHom) := by
  unfold mL
  rw [Subgroup.map_sup, map_conj_zL h hA hB hZ ha]

theorem isRegFam_mFam
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) :
    IsRegFam A (sSup (Msig p A θ)) (mFam θ (zOf S) B) B := by
  have hΩ := h.isRegFam_plane_of_typeA hA hB
  have hZ := normalizes_zOf hS
  refine ⟨isDirectProduct_mFam h hA hr hS hB, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hΩ.nonempty
    exact ⟨mL θ (zOf S) B L, L, hL, rfl⟩
  · rintro _ ⟨L, hL, rfl⟩ hbot
    exact hΩ.ne_bot L hL (le_bot_iff.mp ((le_mL θ _ B L).trans hbot.le))
  · rintro a ha _ ⟨L, hL, rfl⟩
    exact ⟨L.map (MulAut.conj a).toMonoidHom, hΩ.map_conj_mem a ha L hL,
      map_conj_mL h hA hB hZ ha⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive L hL L' hL'
    exact ⟨a, ha, (map_conj_mL h hA hB hZ ha).symm⟩
  · rintro _ ⟨L, hL, rfl⟩
    ext a
    constructor
    · intro ha
      obtain ⟨haA, haN⟩ := Subgroup.mem_inf.mp ha
      have h1 : (mL θ (zOf S) B L).map (MulAut.conj a).toMonoidHom = mL θ (zOf S) B L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
      rw [map_conj_mL h hA hB hZ haA] at h1
      have hL' := hΩ.map_conj_mem a haA L hL
      have h2 : L.map (MulAut.conj a).toMonoidHom = L := by
        by_contra hne
        exact mL_ne_of_ne h hA hB hL' hL hne h1
      rw [← hΩ.stabilizer L hL]
      exact Subgroup.mem_inf.mpr ⟨haA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2⟩
    · intro hb
      rw [← hΩ.stabilizer L hL] at hb
      obtain ⟨hbA, hbN⟩ := Subgroup.mem_inf.mp hb
      have h2 : L.map (MulAut.conj a).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hbN
      have h3 : (mL θ (zOf S) B L).map (MulAut.conj a).toMonoidHom = mL θ (zOf S) B L := by
        rw [map_conj_mL h hA hB hZ hbA, h2]
      exact Subgroup.mem_inf.mpr ⟨hbA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3⟩

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
