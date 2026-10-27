module

public import CFSG.Timmesfeld.Transvection.ResidueBender
import CFSG.GroupTheory.QuasiDihedralFusion.Transport
public import CFSG.Timmesfeld.Transvection.PlaneGroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r}

private theorem residueMemberImage_conjSub_eq {X : Subgroup H}
    (hP : P k ∈ frameResidue Δ P Q k)
    {T T₀ : Sylow 2 (residueQuotient Δ P Q k)}
    (hTX : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
      CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup (residueQuotient Δ P Q k)))
    (hT₀P : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k) =
      CFSG.GH74.Uniqueness.Bender.rootCenter (T₀ : Subgroup (residueQuotient Δ P Q k)))
    {g : ↥(residueGroup Δ P Q k)}
    (hT : (T : Subgroup (residueQuotient Δ P Q k)) =
      (T₀ : Subgroup (residueQuotient Δ P Q k)).map
        (MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥(residueGroup Δ P Q k)) g)).toMonoidHom) :
    residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (conjSub (P k) (g : H)) =
      residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X := by
  let L := residueGroup Δ P Q k
  let π := QuotientGroup.mk' (Subgroup.center L)
  let A : Subgroup ↥L := (P k).subgroupOf L
  have hX'eq : (conjSub A g).map L.subtype = conjSub (P k) (g : H) := by
    rw [← ModelRank.conjSub_map L.subtype A g,
      Subgroup.map_subgroupOf_eq_of_le (frameResidue_le_residueGroup hP)]
    rfl
  have hX'sub : (conjSub (P k) (g : H)).subgroupOf L = conjSub A g := by
    change (conjSub (P k) (g : H)).comap L.subtype = conjSub A g
    rw [← hX'eq, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have hX'img : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k)
        (conjSub (P k) (g : H)) =
      conjSub (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k)) (π g) := by
    change ((conjSub (P k) (g : H)).subgroupOf L).map π =
      conjSub (((P k).subgroupOf L).map π) (π g)
    rw [hX'sub, ← ModelRank.conjSub_map π A g]
  have hroot_conj : CFSG.GH74.Uniqueness.Bender.rootCenter
        (T : Subgroup (residueQuotient Δ P Q k)) =
      (CFSG.GH74.Uniqueness.Bender.rootCenter
        (T₀ : Subgroup (residueQuotient Δ P Q k))).map
          (MulAut.conj (π g)).toMonoidHom := by
    rw [hT]
    exact CFSG.QuasiDihedralFusion.centerOf_map (MulAut.conj (π g))
      (T₀ : Subgroup (residueQuotient Δ P Q k))
  calc residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (conjSub (P k) (g : H))
      = conjSub (residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k)) (π g) :=
        hX'img
    _ = (CFSG.GH74.Uniqueness.Bender.rootCenter
          (T₀ : Subgroup (residueQuotient Δ P Q k))).map
            (MulAut.conj (π g)).toMonoidHom := by rw [hT₀P]
    _ = CFSG.GH74.Uniqueness.Bender.rootCenter
          (T : Subgroup (residueQuotient Δ P Q k)) := hroot_conj.symm
    _ = residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X := hTX.symm

theorem IsMaxFrame.exists_conjSub_eq_of_mem_frameResidue (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) (k : Fin r)
    {X : Subgroup H} (hX : X ∈ frameResidue Δ P Q k) :
    ∃ g ∈ residueGroup Δ P Q k, conjSub (P k) g = X := by
  classical
  haveI : Finite H := h.finite
  by_cases hsmall : IsSmallFrame Δ P Q k
  · have hle : X ≤ P k ⊔ Q k :=
      (isSmallFrame_iff hF.toIsFrame).1 hsmall X hX
    obtain ⟨x, hx, hxX⟩ :=
      exists_conjSub_eq_of_le h.cls.root hX.1 (hF.memP k) (hF.opposite k) hle
    refine ⟨x, ?_, hxX.symm⟩
    exact sup_le (frameResidue_le_residueGroup (hF.toIsFrame.memP_frameResidue k))
      (frameResidue_le_residueGroup (hF.toIsFrame.memQ_frameResidue k)) hx
  · let L := residueGroup Δ P Q k
    have hP : P k ∈ frameResidue Δ P Q k := hF.toIsFrame.memP_frameResidue k
    obtain ⟨T, hTX⟩ :=
      IsMaxFrame.map_mem_frameResidue_eq_center h hML hq hF hsmall hX
    obtain ⟨T₀, hT₀⟩ :=
      IsMaxFrame.map_mem_frameResidue_eq_center h hML hq hF hsmall hP
    have hXroot : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) X =
        CFSG.GH74.Uniqueness.Bender.rootCenter (T : Subgroup (residueQuotient Δ P Q k)) :=
      hTX.trans (CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center _).symm
    have hProot : residueMemberImage (Δ := Δ) (P := P) (Q := Q) (k := k) (P k) =
        CFSG.GH74.Uniqueness.Bender.rootCenter (T₀ : Subgroup (residueQuotient Δ P Q k)) :=
      hT₀.trans (CFSG.GH74.Uniqueness.Bender.rootCenter_eq_map_center _).symm
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (residueQuotient Δ P Q k) T₀ T
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) g
    have hTcoe : (T : Subgroup (residueQuotient Δ P Q k)) =
        (T₀ : Subgroup (residueQuotient Δ P Q k)).map
          (MulAut.conj (QuotientGroup.mk' (Subgroup.center L) g')).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul]
      rfl
    have himg := residueMemberImage_conjSub_eq hP hXroot hProot hTcoe
    have hX'mem : conjSub (P k) (g' : H) ∈ frameResidue Δ P Q k :=
      conjSub_mem_frameResidue h.cls hP g'.2
    exact ⟨(g' : H), g'.2,
      IsMaxFrame.eq_of_residueMemberImage_eq h.cls hML hF hX'mem hX himg⟩

variable {g : H} {π : Equiv.Perm (Fin r)}

theorem conjSub_mem_frameResidue_perm_iff
    (hP : ∀ i, conjSub (P i) g = P (π i)) (hQ : ∀ i, conjSub (Q i) g = Q (π i))
    (hΔ : IsRootClass Δ) {X : Subgroup H} :
    conjSub X g ∈ frameResidue Δ P Q (π k) ↔ X ∈ frameResidue Δ P Q k := by
  constructor
  · rintro ⟨hXΔ, hXc⟩
    refine ⟨?_, fun i hi => ?_⟩
    · have := hΔ.conjSub_mem hXΔ g⁻¹
      rwa [Aux.conjSub_conjSub_inv] at this
    · have hne : π i ≠ π k := fun h' => hi (π.injective h')
      have hc := hXc (π i) hne
      rw [← hP i, ← hQ i] at hc
      exact ⟨(Aux.commuting_conjSub_iff g).1 hc.1, (Aux.commuting_conjSub_iff g).1 hc.2⟩
  · rintro ⟨hXΔ, hXc⟩
    refine ⟨hΔ.conjSub_mem hXΔ g, fun i hi => ?_⟩
    have hjk : π.symm i ≠ k := fun h' => hi (by rw [← Equiv.apply_symm_apply π i, h'])
    have hc := hXc (π.symm i) hjk
    have hPi : P i = conjSub (P (π.symm i)) g := by
      rw [hP (π.symm i), Equiv.apply_symm_apply]
    have hQi : Q i = conjSub (Q (π.symm i)) g := by
      rw [hQ (π.symm i), Equiv.apply_symm_apply]
    rw [hPi, hQi]
    exact ⟨(Aux.commuting_conjSub_iff g).2 hc.1, (Aux.commuting_conjSub_iff g).2 hc.2⟩

theorem conjSub_residueGroup_of_perm
    (hP : ∀ i, conjSub (P i) g = P (π i)) (hQ : ∀ i, conjSub (Q i) g = Q (π i))
    (hΔ : IsRootClass Δ) :
    conjSub (residueGroup Δ P Q k) g = residueGroup Δ P Q (π k) := by
  have hset : (fun D => conjSub D g) '' frameResidue Δ P Q k = frameResidue Δ P Q (π k) := by
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).2 hX
    · intro hY
      refine ⟨conjSub Y g⁻¹, (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).1 ?_, ?_⟩
      · have hconj : conjSub (conjSub Y g⁻¹) g = Y := by
          rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
        rwa [hconj]
      · change conjSub (conjSub Y g⁻¹) g = Y
        rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  rw [residueGroup, conjSub_iSup_mem, hset]
  rfl

theorem isSmallFrame_perm_iff
    (hP : ∀ i, conjSub (P i) g = P (π i)) (hQ : ∀ i, conjSub (Q i) g = Q (π i))
    (hΔ : IsRootClass Δ) (hF : IsFrame Δ P Q) :
    IsSmallFrame Δ P Q (π k) ↔ IsSmallFrame Δ P Q k := by
  rw [isSmallFrame_iff hF, isSmallFrame_iff hF]
  constructor
  · intro h X hX
    have hX' : conjSub X g ∈ frameResidue Δ P Q (π k) :=
      (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).2 hX
    have hle : conjSub X g ≤ P (π k) ⊔ Q (π k) := h _ hX'
    have hPk : conjSub (P (π k)) g⁻¹ = P k := by
      rw [← hP k, Aux.conjSub_conjSub_inv]
    have hQk : conjSub (Q (π k)) g⁻¹ = Q k := by
      rw [← hQ k, Aux.conjSub_conjSub_inv]
    have hsup : conjSub (P (π k) ⊔ Q (π k)) g⁻¹ =
        conjSub (P (π k)) g⁻¹ ⊔ conjSub (Q (π k)) g⁻¹ :=
      Subgroup.map_sup _ _ _
    have hle' : conjSub (conjSub X g) g⁻¹ ≤
        conjSub (P (π k) ⊔ Q (π k)) g⁻¹ := Subgroup.map_mono hle
    rw [Aux.conjSub_conjSub_inv, hsup, hPk, hQk] at hle'
    exact hle'
  · intro h Y hY
    have hY' : conjSub Y g⁻¹ ∈ frameResidue Δ P Q k := by
      refine (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).1 ?_
      have hconj : conjSub (conjSub Y g⁻¹) g = Y := by
        rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
      rwa [hconj]
    have hle : conjSub Y g⁻¹ ≤ P k ⊔ Q k := h _ hY'
    have hconj : conjSub (conjSub Y g⁻¹) g = Y := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    have hsup : conjSub (P k ⊔ Q k) g = conjSub (P k) g ⊔ conjSub (Q k) g :=
      Subgroup.map_sup _ _ _
    have hle' : conjSub (conjSub Y g⁻¹) g ≤ conjSub (P k ⊔ Q k) g :=
      Subgroup.map_mono hle
    rw [hconj, hsup, hP k, hQ k] at hle'
    exact hle'

theorem conj_comp_of_perm
    (hP : ∀ i, conjSub (P i) g = P (π i)) (hQ : ∀ i, conjSub (Q i) g = Q (π i))
    (hΔ : IsRootClass Δ) {G₀ : Type*} [Group G₀] {S : Subgroup G₀}
    {θ : G₀ →* H} (hθ : θ.range = residueGroup Δ P Q k)
    (hmem : ∀ X, X ∈ frameResidue Δ P Q k ↔ ∃ x, X = (conjSub S x).map θ) :
    ((MulAut.conj g).toMonoidHom.comp θ).range = residueGroup Δ P Q (π k) ∧
      ∀ X, X ∈ frameResidue Δ P Q (π k) ↔
        ∃ x, X = (conjSub S x).map ((MulAut.conj g).toMonoidHom.comp θ) := by
  constructor
  · rw [MonoidHom.range_comp, hθ]
    exact conjSub_residueGroup_of_perm hP hQ hΔ
  · intro X
    have hmap : ∀ x : G₀, (conjSub S x).map ((MulAut.conj g).toMonoidHom.comp θ) =
        conjSub ((conjSub S x).map θ) g := by
      intro x
      exact (Subgroup.map_map (conjSub S x) (MulAut.conj g).toMonoidHom θ).symm
    constructor
    · intro hX
      have hconj : conjSub (conjSub X g⁻¹) g = X := by
        rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
      have hX' : conjSub X g⁻¹ ∈ frameResidue Δ P Q k := by
        refine (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).1 ?_
        rwa [hconj]
      obtain ⟨x, hx⟩ := (hmem _).1 hX'
      exact ⟨x, by rw [← hconj, hx, hmap]⟩
    · rintro ⟨x, rfl⟩
      have hx : (conjSub S x).map θ ∈ frameResidue Δ P Q k := (hmem _).2 ⟨x, rfl⟩
      rw [hmap]
      exact (conjSub_mem_frameResidue_perm_iff hP hQ hΔ).2 hx

end CFSG.Timmesfeld.Transvection
