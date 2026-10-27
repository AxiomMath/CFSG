module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.GroupTheory.PCore.SelfCentralizing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G}

namespace CaseTwoTransitive

variable (t : CaseTwoTransitive c)

private noncomputable def diagProd :
    ↥(t.Lhat 0) →* (↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2) where
  toFun u :=
    ((u, ⟨(MulAut.conj t.ybar) (u : t.Mb), conj_ybar_mem_Lhat_one t u.2⟩),
      ⟨(MulAut.conj (t.ybar ^ 2)) (u : t.Mb), conj_ybar_sq_mem_Lhat_two t u.2⟩)
  map_one' := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp
    · apply Subtype.ext
      simp
  map_mul' u v := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [map_mul]
    · apply Subtype.ext
      simp [map_mul]

private theorem muL_diagProd (u : ↥(t.Lhat 0)) :
    t.muL (diagProd t u) = t.delta u := by
  rw [delta_apply, muL_apply]
  rfl

private noncomputable def proj0 :
    ((↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2)) →* ↥(t.Lhat 0) :=
  (MonoidHom.fst (↥(t.Lhat 0)) (↥(t.Lhat 1))).comp
    (MonoidHom.fst (↥(t.Lhat 0) × ↥(t.Lhat 1)) (↥(t.Lhat 2)))

private noncomputable def proj1 :
    ((↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2)) →* ↥(t.Lhat 1) :=
  (MonoidHom.snd (↥(t.Lhat 0)) (↥(t.Lhat 1))).comp
    (MonoidHom.fst (↥(t.Lhat 0) × ↥(t.Lhat 1)) (↥(t.Lhat 2)))

private noncomputable def proj2 :
    ((↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2)) →* ↥(t.Lhat 2) :=
  MonoidHom.snd (↥(t.Lhat 0) × ↥(t.Lhat 1)) (↥(t.Lhat 2))

private theorem proj0_diagProd (u : ↥(t.Lhat 0)) : proj0 t (diagProd t u) = u := rfl

private theorem proj1_diagProd (u : ↥(t.Lhat 0)) :
    proj1 t (diagProd t u) =
      ⟨(MulAut.conj t.ybar) (u : t.Mb), conj_ybar_mem_Lhat_one t u.2⟩ := rfl

private theorem proj2_diagProd (u : ↥(t.Lhat 0)) :
    proj2 t (diagProd t u) =
      ⟨(MulAut.conj (t.ybar ^ 2)) (u : t.Mb), conj_ybar_sq_mem_Lhat_two t u.2⟩ := rfl

private theorem Lhat_two_eq_map :
    (t.Lhat 0).map (MulAut.conj (t.ybar ^ 2)).toMonoidHom = t.Lhat 2 := by
  have hcomp : (MulAut.conj (t.ybar ^ 2)).toMonoidHom =
      (MulAut.conj t.ybar).toMonoidHom.comp (MulAut.conj t.ybar).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, pow_two]
  have hcard10 : Nat.card ↥(t.Lhat 1) = Nat.card ↥(t.Lhat 0) := by
    change Nat.card ↥(t.Lhat (0 + 1)) = Nat.card ↥(t.Lhat 0)
    rw [← t.Lhat_conj 0]
    exact Subgroup.card_map_of_injective (MulAut.conj t.ybar).injective
  have hcard20 : Nat.card ↥(t.Lhat 2) = Nat.card ↥(t.Lhat 0) := by
    change Nat.card ↥(t.Lhat (1 + 1)) = Nat.card ↥(t.Lhat 0)
    rw [← t.Lhat_conj 1]
    exact (Subgroup.card_map_of_injective (MulAut.conj t.ybar).injective).trans hcard10
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    exact conj_ybar_sq_mem_Lhat_two t hu
  · rw [Subgroup.card_map_of_injective (MulAut.conj (t.ybar ^ 2)).injective]
    exact hcard20.le

theorem le_inf_N_of_le_L (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {W : Subgroup G}
    (hWL : W ≤ c.L) (hW : t.Ky ≤ Subgroup.normalizer (W : Set G)) (h3 : ¬ 3 ∣ Nat.card W) :
    W ≤ c.L ⊓ t.d.N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWM : W ≤ t.M := hWL.trans c.hyp81.1
  let Wq : Subgroup ↥(t.M) := W.subgroupOf t.M
  let Wbar : Subgroup t.Mb := Wq.map t.qmk
  have hWqL : Wq ≤ c.L.subgroupOf t.M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hWL (Subgroup.mem_subgroupOf.mp hx))
  have hWbar_le : Wbar ≤ (t.muL).range := by
    rw [← (t.muL_range).symm]
    change Wq.map t.qmk ≤ (c.L.subgroupOf t.M).map t.qmk
    exact Subgroup.map_mono hWqL
  let W' : Subgroup ((↥(t.Lhat 0) × ↥(t.Lhat 1)) × ↥(t.Lhat 2)) :=
    Wbar.comap t.muL
  have hW'image : W'.map t.muL = Wbar := Subgroup.map_comap_eq_self hWbar_le
  have hcardW' : Nat.card ↥W' = Nat.card ↥Wbar := by
    rw [← hW'image, Subgroup.card_map_of_injective (t.muL_injective hK32 hGA hSp)]
  have hcardWbar_dvd : Nat.card ↥Wbar ∣ Nat.card W := by
    have h1 : Nat.card ↥Wbar ∣ Nat.card ↥Wq := Subgroup.card_map_dvd Wq t.qmk
    have h2 : Nat.card ↥Wq = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
    rwa [h2] at h1
  have h3' : ¬ 3 ∣ Nat.card ↥W' := by
    intro h
    have hbar : 3 ∣ Nat.card ↥Wbar := hcardW' ▸ h
    exact h3 (hbar.trans hcardWbar_dvd)
  have hKy_norm : (t.delta).range ≤ Subgroup.normalizer (Wbar : Set t.Mb) := by
    rw [← t.phiKy_range_eq_delta_range hK32 hGA hSp]
    have hWq_norm : t.Ky.subgroupOf t.M ≤
        Subgroup.normalizer (Wq : Set ↥(t.M)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hWM]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hW (Subgroup.mem_subgroupOf.mp hx))
    have hmap := Subgroup.le_normalizer_map (H := Wq) (f := t.qmk)
    have hKybar : t.phiKy.range ≤
        (Subgroup.normalizer (Wq : Set ↥(t.M))).map t.qmk := by
      rw [t.phiKy_range]
      exact Subgroup.map_mono hWq_norm
    exact hKybar.trans hmap
  have hdiag_norm : ∀ u : ↥(t.Lhat 0),
      diagProd t u ∈ Subgroup.normalizer (W' : Set _) := by
    intro u
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    simp only [map_mul, map_inv, muL_diagProd]
    exact (Subgroup.mem_normalizer_iff.mp (hKy_norm ⟨u, rfl⟩) (t.muL x))
  let P0 : Subgroup ↥(t.Lhat 0) := W'.map (proj0 t)
  let P1 : Subgroup ↥(t.Lhat 1) := W'.map (proj1 t)
  let P2 : Subgroup ↥(t.Lhat 2) := W'.map (proj2 t)
  have hP0normal : P0.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨diagProd t g * x * (diagProd t g)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hdiag_norm g) x).mp hx, ?_⟩
    change proj0 t (diagProd t g * x * (diagProd t g)⁻¹) = g * proj0 t x * g⁻¹
    simp only [map_mul, map_inv, proj0_diagProd]
  have hP1normal : P1.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : t.Mb) ∈ (t.Lhat 0).map (MulAut.conj t.ybar).toMonoidHom := by
      rw [t.Lhat_conj 0]
      exact g.2
    obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp hg
    let u' : ↥(t.Lhat 0) := ⟨u, hu⟩
    have hdiag1 : proj1 t (diagProd t u') = g := by
      rw [proj1_diagProd]
      exact Subtype.ext hgu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨diagProd t u' * x * (diagProd t u')⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hdiag_norm u') x).mp hx, ?_⟩
    change proj1 t (diagProd t u' * x * (diagProd t u')⁻¹) = g * proj1 t x * g⁻¹
    simp only [map_mul, map_inv, hdiag1]
  have hP2normal : P2.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : (g : t.Mb) ∈ (t.Lhat 0).map (MulAut.conj (t.ybar ^ 2)).toMonoidHom := by
      rw [Lhat_two_eq_map t]
      exact g.2
    obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp hg
    let u' : ↥(t.Lhat 0) := ⟨u, hu⟩
    have hdiag2 : proj2 t (diagProd t u') = g := by
      rw [proj2_diagProd]
      exact Subtype.ext hgu
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨diagProd t u' * x * (diagProd t u')⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hdiag_norm u') x).mp hx, ?_⟩
    change proj2 t (diagProd t u' * x * (diagProd t u')⁻¹) = g * proj2 t x * g⁻¹
    simp only [map_mul, map_inv, hdiag2]
  have key : ∀ {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y] {K : Subgroup Y},
      K.Normal → ¬ 3 ∣ Nat.card K → 3 ∣ Nat.card Y → K = ⊥ := by
    intro Y _ _ _ K hKn hK3 hY3
    have hcore : CFSG.Open.GLAPPrimeCore 3 Y = ⊥ :=
      CFSG.gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_three
        inferInstance hY3
    have hpc : CFSG.pPrimeCore 3 Y = ⊥ := by
      simpa [CFSG.Open.GLAPPrimeCore] using hcore
    exact (CFSG.pPrimeCore_eq_bot_iff.mp hpc) K hKn
      (Nat.prime_three.coprime_iff_not_dvd.mpr hK3)
  have h3Lhat0 : 3 ∣ Nat.card ↥(t.Lhat 0) := by
    have hLfL : t.d.Lf 0 ≤ c.L := t.hdL ▸ t.d.Lf_le_L 0
    have hL : 3 ∣ Nat.card c.L :=
      (SylowThreeData.three_dvd_card_Lf t.d 0).trans (Subgroup.card_dvd_of_le hLfL)
    exact t.dvd_card_Lhat0 (p := 3) (by norm_num) hL
  have h3Lhat1 : 3 ∣ Nat.card ↥(t.Lhat 1) := by
    have hcard10 : Nat.card ↥(t.Lhat 1) = Nat.card ↥(t.Lhat 0) := by
      change Nat.card ↥(t.Lhat (0 + 1)) = Nat.card ↥(t.Lhat 0)
      rw [← t.Lhat_conj 0]
      exact Subgroup.card_map_of_injective (MulAut.conj t.ybar).injective
    rwa [hcard10]
  have h3Lhat2 : 3 ∣ Nat.card ↥(t.Lhat 2) := by
    rw [← Lhat_two_eq_map t]
    rw [Subgroup.card_map_of_injective (MulAut.conj (t.ybar ^ 2)).injective]
    exact h3Lhat0
  have hsimple0 : IsSimpleGroup ↥(t.Lhat 0) :=
    t.isSimpleGroup_Lhat_zero hK32 hGA hSp
  have hsimple1 : IsSimpleGroup ↥(t.Lhat 1) :=
    (t.eLhatLb 1).isSimpleGroup_congr.mpr (t.isSimpleGroup_Lb hK32 hGA hSp 1)
  have hsimple2 : IsSimpleGroup ↥(t.Lhat 2) :=
    (t.eLhatLb 2).isSimpleGroup_congr.mpr (t.isSimpleGroup_Lb hK32 hGA hSp 2)
  have hP0bot : P0 = ⊥ := by
    refine key (Y := ↥(t.Lhat 0)) hP0normal ?_ h3Lhat0
    intro h
    exact h3' (h.trans (Subgroup.card_map_dvd W' (proj0 t)))
  have hP1bot : P1 = ⊥ := by
    refine key (Y := ↥(t.Lhat 1)) hP1normal ?_ h3Lhat1
    intro h
    exact h3' (h.trans (Subgroup.card_map_dvd W' (proj1 t)))
  have hP2bot : P2 = ⊥ := by
    refine key (Y := ↥(t.Lhat 2)) hP2normal ?_ h3Lhat2
    intro h
    exact h3' (h.trans (Subgroup.card_map_dvd W' (proj2 t)))
  have hW'bot : W' = ⊥ := by
    have hprod : (P0.prod P1).prod P2 = ⊥ := by
      rw [Subgroup.prod_eq_bot_iff, Subgroup.prod_eq_bot_iff]
      exact ⟨⟨hP0bot, hP1bot⟩, hP2bot⟩
    refine le_bot_iff.mp (fun x hx => ?_)
    rw [← hprod]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_prod.mpr
      ⟨Subgroup.mem_map.mpr ⟨x, hx, rfl⟩, Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩,
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hWbar_bot : Wbar = ⊥ := by
    rw [← hW'image, hW'bot, Subgroup.map_bot]
  have hWq_le : Wq ≤ t.Kq := by
    have h : Wq.map t.qmk = ⊥ := hWbar_bot
    rw [Subgroup.map_eq_bot_iff] at h
    have hker : t.qmk.ker = t.Kq := QuotientGroup.ker_mk' (t.Kq)
    rwa [hker] at h
  intro x hx
  have hxWq : (⟨x, hWM hx⟩ : ↥(t.M)) ∈ Wq := Subgroup.mem_subgroupOf.mpr hx
  have hxK : (⟨x, hWM hx⟩ : ↥(t.M)) ∈ t.Kq := hWq_le hxWq
  exact Subgroup.mem_inf.mpr ⟨hWL hx, (Subgroup.mem_subgroupOf.mp hxK).2⟩

theorem commutator_Ky_le_inf_N (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {F : Subgroup G}
    (hFM : F ≤ c.S.M) (hF : t.Ky ≤ Subgroup.normalizer (F : Set G))
    (h3 : ¬ 3 ∣ Nat.card F) :
    ⁅F, t.Ky⁆ ≤ F ⊓ (c.L ⊓ t.d.N) := by
  have hJleF : ⁅F, t.Ky⁆ ≤ F :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hF
  have hJleL : ⁅F, t.Ky⁆ ≤ c.L := by
    have h1 : ⁅F, t.Ky⁆ ≤ ⁅c.S.M, c.L⁆ :=
      Subgroup.commutator_mono hFM (t.Ky_le.trans inf_le_left)
    have h2 : ⁅c.S.M, c.L⁆ ≤ c.L := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp c.le_normalizer_L
    exact h1.trans h2
  let W : Subgroup G := F ⊓ c.L
  have hWL : W ≤ c.L := inf_le_right
  have hWKy : t.Ky ≤ Subgroup.normalizer (W : Set G) := by
    have hKL : t.Ky ≤ c.L := t.Ky_le.trans inf_le_left
    exact (le_inf hF (hKL.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hW3 : ¬ 3 ∣ Nat.card W := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hWle : W ≤ c.L ⊓ t.d.N :=
    le_inf_N_of_le_L t hK32 hGA hSp hWL hWKy hW3
  intro x hx
  have hxF : x ∈ F := hJleF hx
  have hxL : x ∈ c.L := hJleL hx
  exact Subgroup.mem_inf.mpr ⟨hxF, hWle (Subgroup.mem_inf.mpr ⟨hxF, hxL⟩)⟩

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
