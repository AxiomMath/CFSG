module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinG4L34Map
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Model
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisFrobenius

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.GH74.KGroups
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b

private noncomputable def w183finSp44dyn_Inn : S4 →* MulAut S4 := MulAut.conj

private theorem w183finSp44dyn_Inn_injective : Function.Injective w183finSp44dyn_Inn :=
  conj_injective

private theorem w183finSp44dyn_Inn_range : w183finSp44dyn_Inn.range = innAutOf S4 := rfl

private noncomputable def w183finSp44dyn_U : Subgroup (MulAut S4) :=
  (antiUnipotent GF4).map w183finSp44dyn_Inn

private noncomputable def w183finSp44dyn_Q1 : Subgroup (MulAut S4) :=
  (radA1 GF4).map w183finSp44dyn_Inn

private noncomputable def w183finSp44dyn_Q2 : Subgroup (MulAut S4) :=
  (radA2 GF4).map w183finSp44dyn_Inn

private noncomputable def w183finSp44dyn_P1 : Subgroup (MulAut S4) :=
  Subgroup.normalizer (w183finSp44dyn_Q1 : Set (MulAut S4)) ⊓ innAutOf S4

private noncomputable def w183finSp44dyn_P2 : Subgroup (MulAut S4) :=
  Subgroup.normalizer (w183finSp44dyn_Q2 : Set (MulAut S4)) ⊓ innAutOf S4

private noncomputable def w183finSp44dyn_B : Subgroup (MulAut S4) :=
  Subgroup.normalizer (w183finSp44dyn_U : Set (MulAut S4)) ⊓ innAutOf S4

private theorem w183finSp44dyn_borelData :
    CFSG.QuasithinUnique.Borel252.BorelData S4 (antiUnipotent GF4) (radA1 GF4) (radA2 GF4) :=
  CFSG.QuasithinUnique.Borel252.Sp4.borelData_Sp (K := GF4) (n := 2) (by norm_num)
    (by rw [Nat.card_eq_fintype_card]; decide)

private theorem w183finSp44dyn_map_normalizer (A : Subgroup S4) :
    (Subgroup.normalizer (A : Set S4)).map w183finSp44dyn_Inn =
      Subgroup.normalizer (A.map w183finSp44dyn_Inn : Set (MulAut S4)) ⊓ innAutOf S4 := by
  refine le_antisymm (le_inf (Subgroup.le_normalizer_map w183finSp44dyn_Inn)
    (Subgroup.map_le_range w183finSp44dyn_Inn (Subgroup.normalizer A))) ?_
  rintro y ⟨hyN, hyR⟩
  obtain ⟨x, rfl⟩ := hyR
  refine ⟨x, ?_, rfl⟩
  have h1 : x ∈ Subgroup.normalizer ((A.map w183finSp44dyn_Inn).comap w183finSp44dyn_Inn :
      Set S4) :=
    Subgroup.le_normalizer_comap w183finSp44dyn_Inn (H := A.map w183finSp44dyn_Inn)
      (Subgroup.mem_comap.mpr hyN)
  rwa [Subgroup.comap_map_eq_self_of_injective w183finSp44dyn_Inn_injective] at h1

private theorem w183finSp44dyn_U_sylow : IsSylowIn 2 w183finSp44dyn_U (innAutOf S4) := by
  have hU : IsSylowIn 2 (antiUnipotent GF4) (⊤ : Subgroup S4) := w183finSp44dyn_borelData.sylow
  have h := W183L34.isSylowIn_map w183finSp44dyn_Inn w183finSp44dyn_Inn_injective hU
  rw [← MonoidHom.range_eq_map] at h
  simpa [w183finSp44dyn_U, w183finSp44dyn_Inn_range] using h

private theorem w183finSp44dyn_B_lt_P1 : w183finSp44dyn_B < w183finSp44dyn_P1 := by
  have h := w183finSp44dyn_borelData.lt₁
  have hB : w183finSp44dyn_B =
      (Subgroup.normalizer (antiUnipotent GF4 : Set S4)).map w183finSp44dyn_Inn := by
    rw [w183finSp44dyn_B, w183finSp44dyn_U, ← w183finSp44dyn_map_normalizer]
  have hP : w183finSp44dyn_P1 =
      (Subgroup.normalizer (radA1 GF4 : Set S4)).map w183finSp44dyn_Inn := by
    rw [w183finSp44dyn_P1, w183finSp44dyn_Q1, ← w183finSp44dyn_map_normalizer]
  rw [hB, hP]
  refine lt_of_le_of_ne (Subgroup.map_mono h.le) ?_
  intro heq
  exact h.ne (Subgroup.map_injective w183finSp44dyn_Inn_injective heq)

private theorem w183finSp44dyn_P1_lt_L : w183finSp44dyn_P1 < innAutOf S4 := by
  have h := w183finSp44dyn_borelData.lt_top₁
  have hP : w183finSp44dyn_P1 =
      (Subgroup.normalizer (radA1 GF4 : Set S4)).map w183finSp44dyn_Inn := by
    rw [w183finSp44dyn_P1, w183finSp44dyn_Q1, ← w183finSp44dyn_map_normalizer]
  have htop : (⊤ : Subgroup S4).map w183finSp44dyn_Inn = innAutOf S4 := by
    rw [← MonoidHom.range_eq_map, w183finSp44dyn_Inn_range]
  rw [hP]
  refine lt_of_le_of_ne ?_ ?_
  · rw [← htop]
    exact Subgroup.map_mono h.le
  · intro heq
    rw [← htop] at heq
    exact h.ne (Subgroup.map_injective w183finSp44dyn_Inn_injective heq)

private theorem w183finSp44dyn_only {Y : Subgroup (MulAut S4)} (hYL : Y ≤ innAutOf S4)
    (h1 : w183finSp44dyn_B < Y) (h2 : Y < innAutOf S4) :
    Y = w183finSp44dyn_P1 ∨ Y = w183finSp44dyn_P2 := by
  set X : Subgroup S4 := Y.comap w183finSp44dyn_Inn with hX
  have hXY : X.map w183finSp44dyn_Inn = Y := by
    rw [hX]
    exact Subgroup.map_comap_eq_self (f := w183finSp44dyn_Inn)
      (by rwa [w183finSp44dyn_Inn_range])
  have hNmap : (Subgroup.normalizer (antiUnipotent GF4 : Set S4)).map w183finSp44dyn_Inn =
      w183finSp44dyn_B := by
    simpa [w183finSp44dyn_B, w183finSp44dyn_U] using
      w183finSp44dyn_map_normalizer (antiUnipotent GF4)
  have hle : Subgroup.normalizer (antiUnipotent GF4 : Set S4) ≤ X := by
    rw [hX, ← Subgroup.map_le_iff_le_comap, hNmap]
    exact h1.le
  have hlt : Subgroup.normalizer (antiUnipotent GF4 : Set S4) < X := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply h1.ne
    rw [← hNmap, ← hXY, heq]
  have hXt : X < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro heq
    apply h2.ne
    rw [← hXY, heq, ← MonoidHom.range_eq_map, w183finSp44dyn_Inn_range]
  rcases w183finSp44dyn_borelData.only X hlt hXt with h | h
  · left
    have hmap := congrArg (fun Z : Subgroup S4 => Z.map w183finSp44dyn_Inn) h
    rw [hXY, w183finSp44dyn_map_normalizer] at hmap
    simpa [w183finSp44dyn_P1, w183finSp44dyn_Q1] using hmap
  · right
    have hmap := congrArg (fun Z : Subgroup S4 => Z.map w183finSp44dyn_Inn) h
    rw [hXY, w183finSp44dyn_map_normalizer] at hmap
    simpa [w183finSp44dyn_P2, w183finSp44dyn_Q2] using hmap

private theorem w183finSp44dyn_parabolic_conj {P : Subgroup (MulAut S4)}
    (hP : IsMaxParabolicMod ⊥ (innAutOf S4) P) :
    ∃ l ∈ innAutOf S4,
      P = conjSubgroup w183finSp44dyn_P1 l ∨ P = conjSubgroup w183finSp44dyn_P2 l := by
  have hP' := hP
  obtain ⟨-, hPL, -, S, -, hSL, hSpow, hSidx, hNSleP⟩ := hP
  have hSpgroup : IsPGroup 2 S := by
    intro s
    obtain ⟨n, hn⟩ := hSpow s s.2
    exact ⟨n, Subtype.ext (Subgroup.mem_bot.mp hn)⟩
  have hSsyl : IsSylowIn 2 S (innAutOf S4) := ⟨hSL, hSpgroup, hSidx⟩
  obtain ⟨k, hkL, hkS⟩ := W183L34.exists_conj_isSylowIn w183finSp44dyn_U_sylow hSsyl
  have hSc : S = conjSubgroup w183finSp44dyn_U k⁻¹ := by
    rw [conjSubgroup]
    simpa using hkS
  refine ⟨k⁻¹, (innAutOf S4).inv_mem hkL, ?_⟩
  have hYmax : IsMaxParabolicMod ⊥ (innAutOf S4) (conjSubgroup P k) :=
    W183L34.isMaxParabolicMod_conj (L := innAutOf S4) (P := P) (τ := k⁻¹)
      (Subgroup.le_normalizer ((innAutOf S4).inv_mem hkL)) hP'
  have hYL : conjSubgroup P k ≤ innAutOf S4 := by
    have h1 : conjSubgroup P k ≤ conjSubgroup (innAutOf S4) k := Subgroup.map_mono hPL.le
    rwa [show conjSubgroup (innAutOf S4) k = innAutOf S4 from
      (conjSubgroup_eq_iff_mem_normalizer (A := innAutOf S4) (g := k)).mpr
        (Subgroup.le_normalizer hkL)] at h1
  have hNc : (innAutOf S4 ⊓ Subgroup.normalizer (S : Set (MulAut S4))).map
      (MulAut.conj k⁻¹).toMonoidHom = w183finSp44dyn_B := by
    have hSk : conjSubgroup S k = w183finSp44dyn_U := by
      rw [hSc, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hnorm : (Subgroup.normalizer (S : Set (MulAut S4))).map
        (MulAut.conj k⁻¹).toMonoidHom =
        Subgroup.normalizer (w183finSp44dyn_U : Set (MulAut S4)) := by
      rw [Subgroup.map_normalizer_eq_of_bijective S
        (f := (MulAut.conj k⁻¹).toMonoidHom) (MulAut.conj k⁻¹).bijective]
      rw [show S.map (MulAut.conj k⁻¹).toMonoidHom = w183finSp44dyn_U from by
        simpa [conjSubgroup] using hSk]
    have hLk : (innAutOf S4).map (MulAut.conj k⁻¹).toMonoidHom = innAutOf S4 :=
      (conjSubgroup_eq_iff_mem_normalizer (A := innAutOf S4) (g := k)).mpr
        (Subgroup.le_normalizer hkL)
    rw [w183finSp44dyn_B, Subgroup.map_inf _ _ _ (MulAut.conj k⁻¹).injective,
      show (innAutOf S4).map (MulAut.conj k⁻¹).toMonoidHom = innAutOf S4 from hLk, hnorm]
    exact inf_comm _ _
  have hBle : w183finSp44dyn_B ≤ conjSubgroup P k := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hNSleP
    rw [hNc] at hmap
    simpa [conjSubgroup] using hmap
  have hBlt : w183finSp44dyn_B < conjSubgroup P k := by
    refine lt_of_le_of_ne hBle ?_
    intro heq
    exact w183finSp44dyn_P1_lt_L.ne
      (hYmax.2.2.1 w183finSp44dyn_P1 (heq ▸ w183finSp44dyn_B_lt_P1)
        w183finSp44dyn_P1_lt_L.le)
  rcases w183finSp44dyn_only hYL hBlt hYmax.2.1 with h | h
  · left
    rw [← h, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  · right
    rw [← h, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]

private noncomputable def w183finSp44dyn_phi : MulAut (S4) :=
  CFSG.RankThree.PartOne.KCRootAxis.frobAut GF4

private theorem w183finSp44dyn_phi_normalizes_L :
    (innAutOf S4).map (MulAut.conj w183finSp44dyn_phi).toMonoidHom = innAutOf S4 := by
  have hNorm : (innAutOf S4).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal S4
  have hmem : w183finSp44dyn_phi⁻¹ ∈ Subgroup.normalizer (innAutOf S4 : Set (MulAut S4)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hNorm]
    exact Subgroup.mem_top _
  simpa [conjSubgroup] using
    (conjSubgroup_eq_iff_mem_normalizer (A := innAutOf S4) (g := w183finSp44dyn_phi⁻¹)).mpr hmem

private theorem w183finSp44dyn_phi_map_Q1 :
    w183finSp44dyn_Q1.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom = w183finSp44dyn_Q1 := by
  have hrad : (radA1 GF4).map w183finSp44dyn_phi.toMonoidHom = radA1 GF4 := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (CFSG.RankThree.PartOne.KCRootAxis.frobAut_mem_radA1_iff (K := GF4) x).mpr hx
    · intro hy
      exact ⟨w183finSp44dyn_phi⁻¹ y,
        (CFSG.RankThree.PartOne.KCRootAxis.frobAut_mem_radA1_iff (K := GF4)
          (w183finSp44dyn_phi⁻¹ y)).mp (by simpa [w183finSp44dyn_phi] using hy),
        by simp⟩
  change ((radA1 GF4).map (MulAut.conj : S4 →* MulAut S4)).map
      (MulAut.conj w183finSp44dyn_phi).toMonoidHom =
    (radA1 GF4).map (MulAut.conj : S4 →* MulAut S4)
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj w183finSp44dyn_phi).toMonoidHom.comp (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp w183finSp44dyn_phi.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  rw [hcomp, ← Subgroup.map_map, hrad]

private theorem w183finSp44dyn_phi_map_Q2 :
    w183finSp44dyn_Q2.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom = w183finSp44dyn_Q2 := by
  have hrad : (radA2 GF4).map w183finSp44dyn_phi.toMonoidHom = radA2 GF4 := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (CFSG.RankThree.PartOne.KCRootAxis.frobAut_mem_radA2_iff (K := GF4) x).mpr hx
    · intro hy
      exact ⟨w183finSp44dyn_phi⁻¹ y,
        (CFSG.RankThree.PartOne.KCRootAxis.frobAut_mem_radA2_iff (K := GF4)
          (w183finSp44dyn_phi⁻¹ y)).mp (by simpa [w183finSp44dyn_phi] using hy),
        by simp⟩
  change ((radA2 GF4).map (MulAut.conj : S4 →* MulAut S4)).map
      (MulAut.conj w183finSp44dyn_phi).toMonoidHom =
    (radA2 GF4).map (MulAut.conj : S4 →* MulAut S4)
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj w183finSp44dyn_phi).toMonoidHom.comp (MulAut.conj : S4 →* MulAut S4) =
      (MulAut.conj : S4 →* MulAut S4).comp w183finSp44dyn_phi.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  rw [hcomp, ← Subgroup.map_map, hrad]

private theorem w183finSp44dyn_phi_map_P1 :
    w183finSp44dyn_P1.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom = w183finSp44dyn_P1 := by
  rw [w183finSp44dyn_P1, Subgroup.map_inf _ _ _ (MulAut.conj w183finSp44dyn_phi).injective,
    Subgroup.map_normalizer_eq_of_bijective w183finSp44dyn_Q1
      (f := (MulAut.conj w183finSp44dyn_phi).toMonoidHom)
      (MulAut.conj w183finSp44dyn_phi).bijective,
    w183finSp44dyn_phi_map_Q1, w183finSp44dyn_phi_normalizes_L]

private theorem w183finSp44dyn_phi_map_P2 :
    w183finSp44dyn_P2.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom = w183finSp44dyn_P2 := by
  rw [w183finSp44dyn_P2, Subgroup.map_inf _ _ _ (MulAut.conj w183finSp44dyn_phi).injective,
    Subgroup.map_normalizer_eq_of_bijective w183finSp44dyn_Q2
      (f := (MulAut.conj w183finSp44dyn_phi).toMonoidHom)
      (MulAut.conj w183finSp44dyn_phi).bijective,
    w183finSp44dyn_phi_map_Q2, w183finSp44dyn_phi_normalizes_L]

private theorem w183finSp44dyn_map_conjSubgroup (Φ : MulAut (MulAut S4)) (A : Subgroup (MulAut S4))
    (g : MulAut S4) :
    (conjSubgroup A g).map Φ.toMonoidHom =
      conjSubgroup (A.map Φ.toMonoidHom) (Φ g) := by
  rw [conjSubgroup, conjSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp [map_mul, map_inv]

private theorem w183finSp44dyn_not_actsOnDynkinMod_phi_aux :
    ¬ ActsOnDynkinMod ⊥ (innAutOf S4) w183finSp44dyn_phi := by
  rintro ⟨-, P, hPmax, hPne⟩
  obtain ⟨l, hlL, hlP⟩ := w183finSp44dyn_parabolic_conj hPmax
  have hphil : MulAut.conj w183finSp44dyn_phi l ∈ innAutOf S4 := by
    rw [← w183finSp44dyn_phi_normalizes_L]
    exact Subgroup.mem_map.mpr ⟨l, hlL, rfl⟩
  rcases hlP with hlP | hlP
  · refine hPne ((MulAut.conj w183finSp44dyn_phi l)⁻¹ * l)
      ((innAutOf S4).mul_mem ((innAutOf S4).inv_mem hphil) hlL) ?_
    have hΦP : conjSubgroup P w183finSp44dyn_phi⁻¹ =
        conjSubgroup w183finSp44dyn_P1 (MulAut.conj w183finSp44dyn_phi l) := by
      rw [show conjSubgroup P w183finSp44dyn_phi⁻¹ =
          P.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom from by simp [conjSubgroup]]
      rw [hlP, w183finSp44dyn_map_conjSubgroup, w183finSp44dyn_phi_map_P1]
    rw [← conjSubgroup_conjSubgroup, hΦP, conjSubgroup_conjSubgroup]
    rw [show MulAut.conj w183finSp44dyn_phi l *
        ((MulAut.conj w183finSp44dyn_phi l)⁻¹ * l) = l from by group]
    exact hlP.symm
  · refine hPne ((MulAut.conj w183finSp44dyn_phi l)⁻¹ * l)
      ((innAutOf S4).mul_mem ((innAutOf S4).inv_mem hphil) hlL) ?_
    have hΦP : conjSubgroup P w183finSp44dyn_phi⁻¹ =
        conjSubgroup w183finSp44dyn_P2 (MulAut.conj w183finSp44dyn_phi l) := by
      rw [show conjSubgroup P w183finSp44dyn_phi⁻¹ =
          P.map (MulAut.conj w183finSp44dyn_phi).toMonoidHom from by simp [conjSubgroup]]
      rw [hlP, w183finSp44dyn_map_conjSubgroup, w183finSp44dyn_phi_map_P2]
    rw [← conjSubgroup_conjSubgroup, hΦP, conjSubgroup_conjSubgroup]
    rw [show MulAut.conj w183finSp44dyn_phi l *
        ((MulAut.conj w183finSp44dyn_phi l)⁻¹ * l) = l from by group]
    exact hlP.symm

theorem w183finSp44dyn_not_actsOnDynkinMod_minorAut_sq :
    ¬ ActsOnDynkinMod ⊥ (innAutOf S4) (minorAut GF4 ^ 2) := by
  rw [show minorAut GF4 ^ 2 = CFSG.RankThree.PartOne.KCRootAxis.frobAut GF4 from
    (CFSG.RankThree.PartOne.KCRootAxis.frobAut_eq_minorAut_sq (K := GF4)).symm]
  exact w183finSp44dyn_not_actsOnDynkinMod_phi_aux

theorem w183finSp44dyn_actsOnDynkinMod_mul_inner {k t : MulAut S4} (hk : k ∈ innAutOf S4) :
    ActsOnDynkinMod ⊥ (innAutOf S4) (k * t) ↔ ActsOnDynkinMod ⊥ (innAutOf S4) t := by
  constructor
  · intro h
    obtain ⟨hN, P, hPmax, hPne⟩ := h
    have hkL : k ∈ Subgroup.normalizer (innAutOf S4 : Set (MulAut S4)) :=
      Subgroup.le_normalizer hk
    have hk' : k⁻¹ ∈ Subgroup.normalizer (innAutOf S4 : Set (MulAut S4)) :=
      Subgroup.inv_mem _ hkL
    refine ⟨?_, P, hPmax, ?_⟩
    · have := mul_mem hk' hN
      rwa [inv_mul_cancel_left] at this
    · intro l hl
      have h1 := hPne (k * l) ((innAutOf S4).mul_mem hk hl)
      rwa [show (k * t)⁻¹ * (k * l) = t⁻¹ * l from by group] at h1
  · intro h
    obtain ⟨hN, P, hPmax, hPne⟩ := h
    have hkL : k ∈ Subgroup.normalizer (innAutOf S4 : Set (MulAut S4)) :=
      Subgroup.le_normalizer hk
    refine ⟨mul_mem hkL hN, P, hPmax, ?_⟩
    intro l hl
    have h1 := hPne (k⁻¹ * l) ((innAutOf S4).mul_mem ((innAutOf S4).inv_mem hk) hl)
    rwa [show t⁻¹ * (k⁻¹ * l) = (k * t)⁻¹ * l from by group] at h1

theorem w183finSp44dyn_not_actsOnDynkinMod_inner {t : MulAut S4} (ht : t ∈ innAutOf S4) :
    ¬ ActsOnDynkinMod ⊥ (innAutOf S4) t := by
  rintro ⟨-, P, -, hP⟩
  exact hP t ht (by rw [inv_mul_cancel, conjSubgroup_one])

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
