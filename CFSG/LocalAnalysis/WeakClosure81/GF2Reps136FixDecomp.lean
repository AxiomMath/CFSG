module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136S
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136FixCount
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_stableUnder_biSup_irrSet (L : Subgroup (MulAut W)) :
    StableUnder L (⨆ I ∈ irrSet L, I) := by
  intro l hl u hu
  refine Subgroup.iSup_induction (C := fun u => l u ∈ ⨆ I ∈ irrSet L, I)
    (fun I : Subgroup W => ⨆ (_ : I ∈ irrSet L), I) hu ?_ ?_ ?_
  · intro I x hx
    refine Subgroup.iSup_induction (C := fun x => l x ∈ ⨆ I ∈ irrSet L, I)
      (fun (_ : I ∈ irrSet L) => I) hx ?_ ?_ ?_
    · intro hI y hy
      exact Subgroup.mem_iSup_of_mem I (Subgroup.mem_iSup_of_mem hI (hI.2.2.1 l hl y hy))
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b ha hb; rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b ha hb; rw [map_mul]; exact Subgroup.mul_mem _ ha hb

private theorem w1369_commSub_eq_iSup_map (U : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub U X = ⨆ x ∈ X, U.map (commHom x) := by
  refine le_antisymm ?_ ?_
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    exact Subgroup.mem_iSup_of_mem x (Subgroup.mem_iSup_of_mem hx
      (Subgroup.mem_map_of_mem (commHom x) hu))
  · refine iSup₂_le fun x hx => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    exact Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩

private theorem w1369_commSub_iSup_left {ι : Type*} (U : ι → Subgroup W)
    (X : Subgroup (MulAut W)) :
    commSub (⨆ i, U i) X = ⨆ i, commSub (U i) X := by
  refine le_antisymm ?_ (iSup_le fun i => commSub_mono (le_iSup U i) le_rfl)
  rw [w1369_commSub_eq_iSup_map (⨆ i, U i) X]
  refine iSup₂_le fun x hx => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun i => le_trans ?_ (le_iSup (fun j => commSub (U j) X) i)
  rw [w1369_commSub_eq_iSup_map (U i) X]
  exact le_iSup₂_of_le x hx le_rfl

private theorem w1369_commSub_sup_left (A B : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X := by
  have h := w1369_commSub_iSup_left (W := W) (fun b : Bool => cond b A B) X
  rw [iSup_bool_eq, iSup_bool_eq] at h
  exact h

private theorem w1369_commSub_fixV_self (L : Subgroup (MulAut W)) :
    commSub (fixV L) L = ⊥ :=
  commSub_eq_bot_iff.mpr le_rfl

private theorem w1369_stableUnder_fixV (L : Subgroup (MulAut W)) : StableUnder L (fixV L) :=
  fun l hl v hv => by rw [mem_fixV.mp hv l hl]; exact hv

private theorem w1369_stableUnder_sup {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊔ B) := by
  intro x hx u hu
  rw [Subgroup.sup_eq_closure] at hu ⊢
  refine Subgroup.closure_induction (p := fun u _ => x u ∈ Subgroup.closure (A ∪ B : Set W))
    ?_ ?_ ?_ ?_ hu
  · rintro u (huA | huB)
    · exact Subgroup.subset_closure (Or.inl (hA x hx u huA))
    · exact Subgroup.subset_closure (Or.inr (hB x hx u huB))
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb; rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha; rw [map_inv]; exact Subgroup.inv_mem _ ha

private theorem w1369_stableUnder_inf {X : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder X A) (hB : StableUnder X B) : StableUnder X (A ⊓ B) :=
  fun x hx u hu => Subgroup.mem_inf.mpr ⟨hA x hx u hu.1, hB x hx u hu.2⟩

private theorem w1369_stableUnder_Wd (L : Subgroup (MulAut W)) : StableUnder L (Wd L) := by
  intro l hl c hc
  change c ∈ commSub (⊤ : Subgroup W) L at hc
  change l c ∈ commSub (⊤ : Subgroup W) L
  refine Subgroup.closure_induction (p := fun c _ => l c ∈ commSub ⊤ L) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, u, -, rfl⟩
    refine Subgroup.subset_closure
      ⟨l * y * l⁻¹, L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl), l u, trivial, ?_⟩
    show (l * y * l⁻¹) (l u) * (l u)⁻¹ = l (y u * u⁻¹)
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb; rw [map_mul]; exact (commSub ⊤ L).mul_mem ha hb
  · intro a _ ha; rw [map_inv]; exact (commSub ⊤ L).inv_mem ha

private theorem w1369_stableUnder_Cd (L : Subgroup (MulAut W)) : StableUnder L (Cd L) :=
  w1369_stableUnder_inf (w1369_stableUnder_Wd L) (w1369_stableUnder_fixV L)

private theorem w1369_Wd_map_of_normalizer {L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (Wd L).map t.toMonoidHom = Wd L := by
  have h := w1369_commSub_top_map_conj L t
  have h2 : L.map (MulAut.conj t).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  have h3 : commSub (⊤ : Subgroup W) L = (commSub ⊤ L).map t.toMonoidHom := by
    simpa only [h2] using h
  exact h3.symm

private theorem w1369_map_fixV_of_normalizer {L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (fixV L).map t.toMonoidHom = fixV L := by
  apply le_antisymm
  · rintro v ⟨w, hw, rfl⟩
    simp only [mem_fixV] at hw ⊢
    intro l hl
    have hmem : t⁻¹ * l * t ∈ L := (Subgroup.mem_normalizer_iff''.mp ht l).mp hl
    have h1 : (t⁻¹ * l * t) w = w := hw _ hmem
    calc l (t w) = t ((t⁻¹ * l * t) w) := by
          simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      _ = t w := by rw [h1]
  · intro v hv
    refine Subgroup.mem_map.mpr ⟨t⁻¹ v, ?_, by simp⟩
    simp only [mem_fixV] at hv ⊢
    intro l hl
    have hmem : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht l).mp hl
    have h1 : (t * l * t⁻¹) v = v := hv _ hmem
    calc l (t⁻¹ v) = t⁻¹ ((t * l * t⁻¹) v) := by
          simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      _ = t⁻¹ v := by rw [h1]

private theorem w1369_Cd_map_of_normalizer {L : Subgroup (MulAut W)} {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    (Cd L).map t.toMonoidHom = Cd L := by
  rw [show Cd L = Wd L ⊓ fixV L from rfl,
    Subgroup.map_inf (Wd L) (fixV L) t.toMonoidHom t.injective,
    w1369_Wd_map_of_normalizer ht, w1369_map_fixV_of_normalizer ht]

private theorem w1369_Wd_eq_iSup_irrSet (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L) :
    Wd L = ⨆ I ∈ irrSet L, I := by
  classical
  let H : Subgroup (MulAut W) := ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom
  have hLY : L ≤ Y := c.comp.1
  have hHY : H ≤ Y := by
    refine iSup₂_le fun φ hφ => ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    show (MulAut.conj φ) l ∈ Y
    rw [MulAut.conj_apply]
    exact Y.mul_mem (Y.mul_mem hφ (hLY hl)) (Y.inv_mem hφ)
  have hHn : (H.subgroupOf Y).Normal := by
    let Hsub : Subgroup (MulAut W) :=
      ⨆ φ : Y, L.map (MulAut.conj (φ : MulAut W)).toMonoidHom
    have hHsub : H = Hsub :=
      (iSup_subtype'' (Y : Set (MulAut W)) fun φ => L.map (MulAut.conj φ).toMonoidHom).symm
    rw [Subgroup.normal_subgroupOf_iff hHY]
    intro h k hh hk
    rw [hHsub] at hh ⊢
    refine Subgroup.iSup_induction (C := fun x => k * x * k⁻¹ ∈ Hsub)
      (fun φ : Y => L.map (MulAut.conj (φ : MulAut W)).toMonoidHom) hh ?_ ?_ ?_
    · intro φ z hz
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_iSup_of_mem (⟨k * (φ : MulAut W), Y.mul_mem hk φ.2⟩ : Y) ?_
      refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
      show (MulAut.conj (k * (φ : MulAut W))).toMonoidHom l =
        k * (MulAut.conj (φ : MulAut W)).toMonoidHom l * k⁻¹
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro x z hx hz
      have heq : k * (x * z) * k⁻¹ = (k * x * k⁻¹) * (k * z * k⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ hx hz
  have hLne : L ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    haveI := c.comp.2.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (congrArg QuotientGroup.mk h)⟩
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hLne
    have hLH : L ≤ H := by
      have h1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
        ext x
        simp [MulAut.conj]
      rw [← h1]
      exact le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl
    rw [hbot] at hLH
    exact le_bot_iff.mp hLH
  have hspan : (⨆ I ∈ irrSet L, I) ⊔ fixV L = ⊤ :=
    ((w4Lem12_5_holds W hw2 Y c.std.o2 c.std.basic H hHne hHY hHn).2 L c.comp rfl).2
  calc Wd L = commSub (⊤ : Subgroup W) L := rfl
    _ = commSub ((⨆ I ∈ irrSet L, I) ⊔ fixV L) L := by rw [hspan]
    _ = commSub (⨆ I ∈ irrSet L, I) L ⊔ commSub (fixV L) L :=
          w1369_commSub_sup_left _ _ _
    _ = commSub (⨆ I ∈ irrSet L, I) L := by rw [w1369_commSub_fixV_self, sup_bot_eq]
    _ = ⨆ I ∈ irrSet L, I := by
      refine le_antisymm (commSub_le_of_invariant (w1369_stableUnder_biSup_irrSet L)) ?_
      refine iSup₂_le fun I hI => ?_
      rw [← hI.1]
      exact commSub_mono (le_iSup₂_of_le I hI le_rfl) le_rfl

private theorem w1369_irr_to_sect (L : Subgroup (MulAut W)) {I : Subgroup W}
    (hI : I ∈ irrSet L) :
    I ≤ Wd L ∧ Cd L ≤ I ⊔ Cd L ∧ I ⊔ Cd L ≤ Wd L ∧ IsIrrOn L (I ⊔ Cd L) (Cd L) ∧
      commSub (I ⊔ Cd L) L = I := by
  have hIW : I ≤ Wd L := by
    calc I = commSub I L := hI.1.symm
      _ ≤ commSub (⊤ : Subgroup W) L := commSub_mono le_top le_rfl
  have hstableI : StableUnder L I := hI.2.2.1
  have hstableC : StableUnder L (Cd L) := w1369_stableUnder_Cd L
  have hstableIC : StableUnder L (I ⊔ Cd L) := w1369_stableUnder_sup hstableI hstableC
  have hinf : I ⊓ Cd L = I ⊓ fixV L := by
    rw [show Cd L = Wd L ⊓ fixV L from rfl, ← inf_assoc, inf_eq_left.mpr hIW]
  refine ⟨hIW, le_sup_right, sup_le hIW inf_le_left, ?_, ?_⟩
  · refine ⟨?_, hstableIC, hstableC, ?_⟩
    · refine lt_of_le_of_ne le_sup_right (Ne.symm ?_)
      intro h
      have hIC : I ≤ Cd L := by rw [← h]; exact le_sup_left
      exact not_le_fixV_of_mem_irrSet hI (hIC.trans inf_le_right)
    · intro J hJ hCJ hJI
      have hJW : J ≤ Wd L := hJI.trans (sup_le hIW inf_le_left)
      have hNJ : I ⊓ fixV L ≤ J ⊓ I := by
        rw [← hinf]
        exact le_inf (inf_le_right.trans hCJ) inf_le_left
      rcases hI.2.2.2.2 (J ⊓ I) (w1369_stableUnder_inf hJ hstableI) hNJ inf_le_right with h | h
      · left
        have hJIC : J ⊓ I ≤ Cd L := by rw [h, ← hinf]; exact inf_le_right
        exact (eq_of_le_of_inf_le_of_le_sup hCJ hJIC (by rwa [sup_comm] at hJI)).symm
      · right
        exact le_antisymm hJI (sup_le ((le_of_eq h.symm).trans inf_le_left) hCJ)
  · rw [w1369_commSub_sup_left I (Cd L) L, hI.1,
      commSub_eq_bot_iff.mpr (inf_le_right : Cd L ≤ fixV L), sup_bot_eq]

private theorem w1369_sect_to_irr {L : Subgroup (MulAut W)} (hLp : ⁅L, L⁆ = L)
    {M : Subgroup W} (hCM : Cd L ≤ M) (hMW : M ≤ Wd L) (hM : IsIrrOn L M (Cd L)) :
    commSub M L ∈ irrSet L ∧ commSub M L ⊔ Cd L = M := by
  have hstableM : StableUnder L M := hM.2.1
  have hstableC : StableUnder L (Cd L) := hM.2.2.1
  have hIle : commSub M L ≤ M := commSub_le_of_invariant hstableM
  have hIstable : StableUnder L (commSub M L) := by
    intro l hl c hc
    refine Subgroup.closure_induction (p := fun c _ => l c ∈ commSub M L) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨y, hy, u, hu, rfl⟩
      refine Subgroup.subset_closure
        ⟨l * y * l⁻¹, L.mul_mem (L.mul_mem hl hy) (L.inv_mem hl), l u,
          hstableM l hl u hu, ?_⟩
      show (l * y * l⁻¹) (l u) * (l u)⁻¹ = l (y u * u⁻¹)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ ha hb; rw [map_mul]; exact (commSub M L).mul_mem ha hb
    · intro a _ ha; rw [map_inv]; exact (commSub M L).inv_mem ha
  have hsup : commSub M L ⊔ Cd L = M := by
    have hstable : StableUnder L (commSub M L ⊔ Cd L) := w1369_stableUnder_sup hIstable hstableC
    have hle : commSub M L ⊔ Cd L ≤ M := sup_le hIle hCM
    rcases hM.2.2.2 (commSub M L ⊔ Cd L) hstable le_sup_right hle with h | h
    · exfalso
      have hIleC : commSub M L ≤ Cd L := sup_eq_right.mp h
      have hIfix : commSub M L ≤ fixV L := hIleC.trans inf_le_right
      have h1 : commSub (commSub M L) L ≤ (⊥ : Subgroup W) := by
        have hx : commSub (commSub M L) L ≤ commSub (fixV L) L := commSub_mono hIfix le_rfl
        rwa [commSub_eq_bot_iff.mpr le_rfl] at hx
      have hfin := s13_perfect_chain L hLp (⊥ : Subgroup W) (commSub M L) M h1 le_rfl
      have hbot : commSub M L = ⊥ := le_bot_iff.mp hfin
      exact absurd (le_inf hMW (commSub_eq_bot_iff.mp hbot)) (not_le_of_gt hM.1)
    · exact h
  refine ⟨⟨le_antisymm (commSub_le_of_invariant hIstable) ?_, ?_⟩, hsup⟩
  · exact s13_perfect_chain L hLp (commSub (commSub M L) L) (commSub M L) M le_rfl le_rfl
  · have hinf : commSub M L ⊓ Cd L = commSub M L ⊓ fixV L := by
      rw [show Cd L = Wd L ⊓ fixV L from rfl, ← inf_assoc, inf_eq_left.mpr (hIle.trans hMW)]
    have hne : commSub M L ⊓ fixV L ≠ commSub M L := by
      intro hEq
      have hIfix : commSub M L ≤ fixV L := by rw [← hEq]; exact inf_le_right
      have hIC : commSub M L ≤ Cd L := le_inf (hIle.trans hMW) hIfix
      exact not_le_of_gt hM.1 (by rw [← hsup]; exact sup_le hIC le_rfl)
    refine ⟨lt_of_le_of_ne inf_le_left hne, hIstable,
      w1369_stableUnder_inf hIstable (w1369_stableUnder_fixV L), ?_⟩
    intro J hJ hNJ hJI
    have hstab2 : StableUnder L (J ⊔ Cd L) := w1369_stableUnder_sup hJ hstableC
    have hle2 : J ⊔ Cd L ≤ M := sup_le (hJI.trans hIle) hCM
    rcases hM.2.2.2 (J ⊔ Cd L) hstab2 le_sup_right hle2 with h2 | h2
    · left
      have hJC : J ≤ Cd L := sup_eq_right.mp h2
      exact le_antisymm (le_inf hJI (hJC.trans inf_le_right)) hNJ
    · right
      have hmod : (J ⊔ Cd L) ⊓ commSub M L = J ⊔ (Cd L ⊓ commSub M L) :=
        sup_inf_assoc_of_le (y := Cd L) hJI
      have hI' : commSub M L = J ⊔ (Cd L ⊓ commSub M L) := by
        rw [← hmod, h2, inf_eq_right.mpr hIle]
      have hCdJ : Cd L ⊓ commSub M L ≤ J := by rw [inf_comm, hinf]; exact hNJ
      rw [hI', sup_eq_left.mpr hCdJ]

theorem irr_section_stable (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) {M : Subgroup W} (hCM : Cd L ≤ M)
    (hMW : M ≤ Wd L) (hM : IsIrrOn L M (Cd L)) :
    StableUnder (Subgroup.zpowers t) M ∧ ¬ commSub M (Subgroup.zpowers t) ≤ Cd L := by
  have hLp : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr c.comp.2.2.1)
  obtain ⟨hI'irr, hI'sup⟩ := w1369_sect_to_irr hLp hCM hMW hM
  have hstableM : StableUnder L M := hM.2.1
  have hstableC : StableUnder L (Cd L) := hM.2.2.1
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (c.hfix L c.comp)
  have hCdmap : (Cd L).map t.toMonoidHom = Cd L := w1369_Cd_map_of_normalizer htN
  have hI'fix : (commSub M L).map t.toMonoidHom = commSub M L := hfix _ hI'irr
  have hMmap : M.map t.toMonoidHom = M := by
    rw [← hI'sup, Subgroup.map_sup, hI'fix, hCdmap]
  have htM : ∀ u ∈ M, t u ∈ M := fun u hu => by
    rw [← hMmap]; exact Subgroup.mem_map_of_mem t.toMonoidHom hu
  have htMinv : ∀ u ∈ M, t⁻¹ u ∈ M := by
    intro u hu
    have hle : M.map t.toMonoidHom ≤ M := fun x hx => hMmap ▸ hx
    have heq : M.map t.toMonoidHom = M :=
      Subgroup.eq_of_le_of_card_ge hle
        (le_of_eq (Subgroup.card_map_of_injective t.injective).symm)
    have hmem : u ∈ M.map t.toMonoidHom := by rw [heq]; exact hu
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hmem
    have hwu : t⁻¹ u = w := by
      rw [← hwv]
      simp
    rw [hwu]
    exact hw
  have htstab : t ∈ stabSub M := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun hu => by simpa using htMinv (t u) hu, htM u⟩
  refine ⟨fun x hx u hu => (mem_stabSub.mp (Subgroup.zpowers_le.mpr htstab hx) u).2 hu, ?_⟩
  intro hle
  have htK : t ∈ centSec M (Cd L) := by
    rw [mem_centSec]
    exact ⟨htstab, fun u hu =>
      hle (Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, u, hu, rfl⟩)⟩
  have hlM_of : ∀ l ∈ L, l ∈ stabSub M := by
    intro l hl
    rw [mem_stabSub]
    intro u
    refine ⟨fun hu => ?_, fun hu => hstableM l hl u hu⟩
    have h := hstableM l⁻¹ (L.inv_mem hl) (l u) hu
    simpa using h
  have hnorm : ∀ l ∈ L, ∀ x ∈ centSec M (Cd L), l * x * l⁻¹ ∈ centSec M (Cd L) := by
    intro l hl x hx
    rw [mem_centSec] at hx ⊢
    refine ⟨(stabSub M).mul_mem ((stabSub M).mul_mem (hlM_of l hl) hx.1)
      ((stabSub M).inv_mem (hlM_of l hl)), ?_⟩
    intro u hu
    have hw : l⁻¹ u ∈ M := (mem_stabSub.mp ((stabSub M).inv_mem (hlM_of l hl)) u).2 hu
    have hc : x (l⁻¹ u) * (l⁻¹ u)⁻¹ ∈ Cd L := hx.2 (l⁻¹ u) hw
    have hkey : (l * x * l⁻¹) u * u⁻¹ = l (x (l⁻¹ u) * (l⁻¹ u)⁻¹) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.apply_inv_self, map_mul, map_inv]
    rw [hkey]
    exact hstableC l hl _ hc
  have hLnormK : L ≤ Subgroup.normalizer (centSec M (Cd L) : Set (MulAut W)) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact hnorm l hl y hy
    · refine Subgroup.mem_map.mpr ⟨l⁻¹ * x * l, hnorm l⁻¹ (L.inv_mem hl) x hx, ?_⟩
      show l * (l⁻¹ * x * l) * l⁻¹ = x
      group
  have hcommK : ⁅L, Subgroup.zpowers t⁆ ≤ centSec M (Cd L) := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    have hxK : x ∈ centSec M (Cd L) := Subgroup.zpowers_le.mpr htK hx
    exact (centSec M (Cd L)).mul_mem (hnorm l hl x hxK) ((centSec M (Cd L)).inv_mem hxK)
  have hLleK : L ≤ centSec M (Cd L) := by
    have h := hcommK
    rwa [c.Lt] at h
  have hI'leC : commSub M L ≤ Cd L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    exact (mem_centSec.mp (hLleK hl)).2 u hu
  exact not_le_of_gt hM.1 (by rw [← hI'sup]; exact sup_le hI'leC le_rfl)

@[expose] def FixDec (t : MulAut W) (L : Subgroup (MulAut W)) (r : ℕ) (J : Fin r → Subgroup W) :
    Prop :=
  1 ≤ r ∧ r ≤ 3 ∧
    (∀ i, Cd L ≤ J i ∧ J i ≤ Wd L ∧ IsIrrOn L (J i) (Cd L) ∧ commSub (J i) L ⊔ Cd L = J i ∧
      StableUnder (Subgroup.zpowers t) (J i) ∧ 1 ≤ tcost t L (J i)) ∧
    (∀ i, J i ⊓ (Cd L ⊔ ⨆ (j : Fin r) (_ : j ≠ i), J j) ≤ Cd L) ∧
    (Cd L ⊔ ⨆ i, J i) = Wd L ∧ (∑ i, tcost t L (J i)) ≤ 3

private theorem w1369_component_ne_bot {Y : Subgroup (MulAut W)} {L : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) : L ≠ ⊥ := by
  rw [← Subgroup.nontrivial_iff_ne_bot]
  haveI := hL.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (congrArg QuotientGroup.mk h)⟩

theorem fix_decomp (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) :
    ∃ (r : ℕ) (J : Fin r → Subgroup W), FixDec t L r J := by
  classical
  have hLp : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr c.comp.2.2.1)
  have hWd : Wd L = ⨆ I ∈ irrSet L, I := w1369_Wd_eq_iSup_irrSet hw2 c
  let 𝒮 : Set (Subgroup W) := (fun I : Subgroup W => I ⊔ Cd L) '' irrSet L
  have hC𝒮 : ∀ M ∈ 𝒮, Cd L ≤ M ∧ IsIrrOn L M (Cd L) := by
    rintro M ⟨I, hI, rfl⟩
    obtain ⟨-, -, -, hirr, -⟩ := w1369_irr_to_sect L hI
    exact ⟨le_sup_right, hirr⟩
  obtain ⟨r, J, hJmem, hind, hspan⟩ := w1369_exists_indep_family 𝒮 (Set.toFinite 𝒮) hC𝒮
  have h𝒮le : (⨆ M ∈ 𝒮, M) ≤ Wd L := by
    refine iSup₂_le fun M hM => ?_
    obtain ⟨I, hI, rfl⟩ := hM
    obtain ⟨hIW, -, hJW, -, -⟩ := w1369_irr_to_sect L hI
    exact sup_le hIW inf_le_left
  have hWd_le : Wd L ≤ Cd L ⊔ ⨆ M ∈ 𝒮, M := by
    rw [hWd]
    refine iSup₂_le fun I hI => le_sup_of_le_right ?_
    exact le_iSup₂_of_le (I ⊔ Cd L) ⟨I, hI, rfl⟩ le_sup_left
  have hspanC : Cd L ⊔ ⨆ M ∈ 𝒮, M = Wd L := le_antisymm (sup_le inf_le_left h𝒮le) hWd_le
  have hJprops : ∀ i, Cd L ≤ J i ∧ J i ≤ Wd L ∧ IsIrrOn L (J i) (Cd L) ∧
      commSub (J i) L ⊔ Cd L = J i := by
    intro i
    obtain ⟨I, hI, hIeq⟩ := hJmem i
    obtain ⟨-, -, hJW, hirr, hcomm⟩ := w1369_irr_to_sect L hI
    exact ⟨hIeq ▸ le_sup_right, hIeq ▸ hJW, hIeq ▸ hirr, by rw [← hIeq, hcomm]⟩
  have hstab : ∀ i, StableUnder (Subgroup.zpowers t) (J i) ∧
      ¬ commSub (J i) (Subgroup.zpowers t) ≤ Cd L := fun i =>
    irr_section_stable hw2 c hfix (hJprops i).1 (hJprops i).2.1 (hJprops i).2.2.1
  have hcost_ge : ∀ i, 1 ≤ tcost t L (J i) := by
    intro i
    have hnt := (hstab i).2
    have hA2 : IsPGroup 2 ↥(commSub (J i) (Subgroup.zpowers t) ⊔ Cd L) :=
      isPGroup_two_of_sq_eq_one fun x => Subtype.ext (by
        have := hw2 (x : W)
        simpa [pow_two] using this)
    have hne : E3.mQuot (commSub (J i) (Subgroup.zpowers t) ⊔ Cd L) (Cd L) ≠ 0 := by
      intro h0
      have h0' : Cd L = commSub (J i) (Subgroup.zpowers t) ⊔ Cd L :=
        (E3.mQuot_eq_zero_iff hA2 le_sup_right).mp h0
      exact hnt (h0'.symm ▸ le_sup_left)
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hsum3 : (∑ i, tcost t L (J i)) ≤ 3 :=
    w1369_tcost_sum_le hw2 (fun i => (hJprops i).1) (fun i => (hJprops i).2.1)
      (fun i => (hstab i).1) hind c.std.cost
  have hr_le : r ≤ 3 := by
    have h1 : r ≤ ∑ i, tcost t L (J i) := by
      have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcost_ge i)
      simpa using h2
    omega
  have hCd_lt_Wd : Cd L < Wd L := by
    obtain ⟨I₀, hI₀⟩ := exists_mem_irrSet_of_ne_bot
      (quadTrivial_of_commutator_eq_top c.comp.2.2.1) (w1369_component_ne_bot c.comp)
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    have hle : (⨆ I ∈ irrSet L, I) ≤ fixV L := by
      rw [← hWd, ← hEq]
      exact inf_le_right
    exact not_le_fixV_of_mem_irrSet hI₀ ((le_iSup₂_of_le I₀ hI₀ le_rfl).trans hle)
  have hspanJ : Cd L ⊔ ⨆ i, J i = Wd L := by rw [hspan, hspanC]
  have hr_pos : 1 ≤ r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    have hbot : (⨆ i : Fin r, J i) = (⊥ : Subgroup W) := by
      refine le_antisymm (iSup_le fun i => ?_) bot_le
      exact absurd (by omega : i.val < 0) (Nat.not_lt_zero i.val)
    have hCW : Cd L = Wd L := by rw [← hspanJ, hbot, sup_bot_eq]
    exact absurd hCW (ne_of_lt hCd_lt_Wd)
  refine ⟨r, J, hr_pos, hr_le, ?_, hind, hspanJ, hsum3⟩
  intro i
  exact ⟨(hJprops i).1, (hJprops i).2.1, (hJprops i).2.2.1, (hJprops i).2.2.2,
    (hstab i).1, hcost_ge i⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
