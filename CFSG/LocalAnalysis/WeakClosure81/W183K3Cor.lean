module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Lift
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3)

private theorem w183K3Cor_conj_eq_id {W : Type*} [Group W] {Z : Subgroup W} {n : W} (hn : n ∈ Z)
    (hZc : ∀ z ∈ Z, ∀ g : W, z * g = g * z) :
    (MulAut.conj n).toMonoidHom = MonoidHom.id W := by
  ext x
  change n * x * n⁻¹ = x
  rw [hZc n hn x]
  group

private theorem w183K3Cor_eq_of_map_mk_eq {W : Type*} [Group W] [Finite W] {Z : Subgroup W}
    [Z.Normal] (hZc : ∀ z ∈ Z, ∀ g : W, z * g = g * z) (hZ : Odd (Nat.card ↥Z))
    {A B : Subgroup W} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (h : A.map (QuotientGroup.mk' Z) = B.map (QuotientGroup.mk' Z)) : A = B := by
  obtain ⟨n, hn, hBn⟩ := W183K3.exists_conj_of_map_mk_eq hZ hA hB h
  rw [hBn, w183K3Cor_conj_eq_id hn hZc, Subgroup.map_id]

private theorem w183K3Cor_map_inf_comap {W : Type*} [Group W] {Z : Subgroup W} [Z.Normal]
    {P : Subgroup (W ⧸ Z)} {Pt : Subgroup W} (hPt : Pt.map (QuotientGroup.mk' Z) = P)
    {R : Subgroup (W ⧸ Z)} (hR : R ≤ P) :
    (Pt ⊓ R.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = R := by
  refine le_antisymm ?_ ?_
  · calc (Pt ⊓ R.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z)
        ≤ (R.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) :=
          Subgroup.map_mono inf_le_right
      _ ≤ R := Subgroup.map_comap_le _ _
  · intro r hr
    have hrP : r ∈ Pt.map (QuotientGroup.mk' Z) := hPt ▸ hR hr
    obtain ⟨p, hpPt, hp⟩ := Subgroup.mem_map.mp hrP
    exact Subgroup.mem_map.mpr ⟨p, Subgroup.mem_inf.mpr
      ⟨hpPt, Subgroup.mem_comap.mpr (by rw [hp]; exact hr)⟩, hp⟩

private theorem w183K3Cor_map_conj_map_mk {W : Type*} [Group W] {Z : Subgroup W} [Z.Normal]
    {g : W} {gA : W ⧸ Z} (hg : QuotientGroup.mk' Z g = gA) (A : Subgroup W) :
    (A.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' Z) =
      (A.map (QuotientGroup.mk' Z)).map (MulAut.conj gA).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  have hg' : (g : W ⧸ Z) = gA := hg
  simp [MulAut.conj_apply, hg']

theorem w183k3_corConfig_lift {W : Type*} [Group W] [Finite W] {Z : Subgroup W} [Z.Normal]
    (hZc : ∀ z ∈ Z, ∀ g : W, z * g = g * z) (hZ : Odd (Nat.card ↥Z)) {A : Subgroup W}
    (hA : IsPGroup 2 ↥A) {P : Subgroup (W ⧸ Z)} (hP : IsPGroup 2 ↥P)
    (hAP : A.map (QuotientGroup.mk' Z) ≤ P)
    (h : CorConfigIn (W ⧸ Z) (A.map (QuotientGroup.mk' Z)) P) : CorConfig W A := by
  obtain ⟨A', S, y, ⟨gA, hA'eq⟩, hS, hy, hs, hn, hSA', hA'P, hSP, hyP⟩ := h
  obtain ⟨Pt, hPt, hPtmap⟩ := W183K3.exists_isPGroup_map_mk_eq hZ hP
  have hAt2 : IsPGroup 2 ↥(Pt ⊓ (A.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z)) :=
    hPt.to_le inf_le_left
  have hAtmap : (Pt ⊓ (A.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z)).map
      (QuotientGroup.mk' Z) = A.map (QuotientGroup.mk' Z) :=
    w183K3Cor_map_inf_comap hPtmap hAP
  have hAeq : A = Pt ⊓ (A.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) :=
    w183K3Cor_eq_of_map_mk_eq hZc hZ hA hAt2 (by rw [hAtmap])
  have hAPt : A ≤ Pt := by rw [hAeq]; exact inf_le_left
  obtain ⟨yt, hytPt, hyt⟩ := Subgroup.mem_map.mp (hPtmap ▸ hyP)
  let St : Set (Subgroup W) := (fun X => Pt ⊓ X.comap (QuotientGroup.mk' Z)) '' S
  let A't : Subgroup W := Pt ⊓ A'.comap (QuotientGroup.mk' Z)
  have hA't2 : IsPGroup 2 ↥A't := hPt.to_le inf_le_left
  have hA'tmap : A't.map (QuotientGroup.mk' Z) = A' := w183K3Cor_map_inf_comap hPtmap hA'P
  have hStle : Subgroup.closure (⋃ Xt ∈ St, (Xt : Set W)) ≤ Pt := by
    rw [Subgroup.closure_le]
    rintro x hx
    obtain ⟨Xt, hXt, hxXt⟩ := Set.mem_iUnion₂.mp hx
    rw [Set.mem_image] at hXt
    obtain ⟨X, -, rfl⟩ := hXt
    exact hxXt.1
  have hlift : ∀ zbar ∈ Subgroup.closure (⋃ X ∈ S, (X : Set (W ⧸ Z))),
      ∃ zt ∈ Subgroup.closure (⋃ Xt ∈ St, (Xt : Set W)),
        QuotientGroup.mk' Z zt = zbar := by
    intro zbar hzbar
    refine Subgroup.closure_induction (p := fun z _ =>
      ∃ zt ∈ Subgroup.closure (⋃ Xt ∈ St, (Xt : Set W)),
        QuotientGroup.mk' Z zt = z) ?_ ?_ ?_ ?_ hzbar
    · intro x hx
      obtain ⟨X, hX, hxX⟩ := Set.mem_iUnion₂.mp hx
      have hXmap : (Pt ⊓ X.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = X :=
        w183K3Cor_map_inf_comap hPtmap (hSP X hX)
      obtain ⟨xt, hxt, hxteq⟩ := Subgroup.mem_map.mp (hXmap ▸ hxX)
      exact ⟨xt, Subgroup.subset_closure (Set.mem_iUnion₂.mpr
        ⟨Pt ⊓ X.comap (QuotientGroup.mk' Z), Set.mem_image_of_mem _ hX, hxt⟩), hxteq⟩
    · exact ⟨1, Subgroup.one_mem _, map_one _⟩
    · intro x y _ _ ihx ihy
      obtain ⟨xt, hxt, hxteq⟩ := ihx
      obtain ⟨yt', hyt', hyteq⟩ := ihy
      exact ⟨xt * yt', Subgroup.mul_mem _ hxt hyt', by rw [map_mul, hxteq, hyteq]⟩
    · intro x _ ihx
      obtain ⟨xt, hxt, hxteq⟩ := ihx
      exact ⟨xt⁻¹, Subgroup.inv_mem _ hxt, by rw [map_inv, hxteq]⟩
  refine ⟨A't, St, yt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N := Z) gA
    refine ⟨g, ?_⟩
    have hAgmap : (A.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' Z) = A' := by
      rw [w183K3Cor_map_conj_map_mk hg, ← hA'eq]
    exact (w183K3Cor_eq_of_map_mk_eq hZc hZ (hA.map _) hA't2
      (hAgmap.trans hA'tmap.symm)).symm
  · intro Xt hXt
    rw [Set.mem_image] at hXt
    obtain ⟨X, hX, rfl⟩ := hXt
    obtain ⟨gX, hgX⟩ := hS X hX
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N := Z) gX
    refine ⟨g, ?_⟩
    have hXmap : (Pt ⊓ X.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = X :=
      w183K3Cor_map_inf_comap hPtmap (hSP X hX)
    have hAgmap : (A.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' Z) = X := by
      rw [w183K3Cor_map_conj_map_mk hg, ← hgX]
    exact (w183K3Cor_eq_of_map_mk_eq hZc hZ (hA.map _) (hPt.to_le inf_le_left)
      (hAgmap.trans hXmap.symm)).symm
  · intro heq
    apply hy
    have h := w183K3Cor_map_conj_map_mk hyt A
    rw [heq] at h
    exact h.symm
  · intro s hsA
    obtain ⟨zbar, hzbar, hzbareq⟩ := hs (QuotientGroup.mk' Z s)
      (Subgroup.mem_map_of_mem _ hsA)
    obtain ⟨zt, hzt, hzteq⟩ := hlift zbar hzbar
    have hztPt : zt ∈ Pt := hStle hzt
    have hsPt : s ∈ Pt := hAPt hsA
    exact ⟨zt, hzt, CFSG.ComponentClassification.AschbacherToolkit.quotient_injective_on_of_isPGroup
      Z hZ hPt (Pt.mul_mem (Pt.mul_mem hytPt hsPt) (Pt.inv_mem hytPt)) (Pt.mul_mem hsPt hztPt)
      (by simp only [map_mul, map_inv, hyt, hzteq, hzbareq])⟩
  · intro hle
    apply hn
    calc A.map (QuotientGroup.mk' Z)
        ≤ (Subgroup.normalizer (A't : Set W)).map (QuotientGroup.mk' Z) :=
          Subgroup.map_mono hle
      _ ≤ Subgroup.normalizer ((A't.map (QuotientGroup.mk' Z) : Subgroup (W ⧸ Z)) :
            Set (W ⧸ Z)) := Subgroup.le_normalizer_map (QuotientGroup.mk' Z)
      _ = Subgroup.normalizer (A' : Set (W ⧸ Z)) := by rw [hA'tmap]
  · intro Xt hXt
    rw [Set.mem_image] at hXt
    obtain ⟨X, hX, rfl⟩ := hXt
    rcases hSA' X hX with hXA' | hcomm
    · left
      rw [hXA']
    · right
      intro a ha x hx
      have hamap : QuotientGroup.mk' Z a ∈ A' :=
        hA'tmap ▸ Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hXmap : (Pt ⊓ X.comap (QuotientGroup.mk' Z)).map (QuotientGroup.mk' Z) = X :=
        w183K3Cor_map_inf_comap hPtmap (hSP X hX)
      have hxmap : QuotientGroup.mk' Z x ∈ X :=
        hXmap ▸ Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact CFSG.ComponentClassification.AschbacherToolkit.quotient_injective_on_of_isPGroup
        Z hZ hPt (Pt.mul_mem ha.1 hx.1) (Pt.mul_mem hx.1 ha.1)
        (by simp only [map_mul, hcomm (QuotientGroup.mk' Z a) hamap (QuotientGroup.mk' Z x) hxmap])

theorem w183k3_ticorConfigHolds_central (hsyl : FinG1Syl) {G₀ : Type} [Group G₀] [Finite G₀]
    (hodd : Odd (Nat.card ↥(Subgroup.center G₀)))
    (hshape : IsL3 (G₀ ⧸ Subgroup.center G₀) 2) : TICorConfigHolds G₀ := by
  intro A₀ hcard hel hTI
  have hA0 : IsPGroup 2 A₀ := hel.isPGroup
  have hZc : ∀ z ∈ Subgroup.center G₀, ∀ g : G₀, z * g = g * z :=
    fun z hz g => (Subgroup.mem_center_iff.mp hz g).symm
  have hcardBar : Nat.card ↥(A₀.map (QuotientGroup.mk' (Subgroup.center G₀))) = 4 := by
    rw [W183K3.card_map_mk_of_isPGroup hodd hA0, hcard]
  have helBar : IsElemAbelian 2 (A₀.map (QuotientGroup.mk' (Subgroup.center G₀))) := hel.map _
  have hTIbar : IsTISub (G₀ ⧸ Subgroup.center G₀)
      (A₀.map (QuotientGroup.mk' (Subgroup.center G₀))) :=
    W183K3.isTISub_map_mk hodd hA0 hTI
  obtain ⟨P, hP, hAP, hconf⟩ := hsyl (G₀ ⧸ Subgroup.center G₀) hshape
    (A₀.map (QuotientGroup.mk' (Subgroup.center G₀))) hcardBar helBar hTIbar
  exact w183k3_corConfig_lift hZc hodd hA0 hP hAP hconf

end CFSG.LocalAnalysis.WeakClosure81

end
