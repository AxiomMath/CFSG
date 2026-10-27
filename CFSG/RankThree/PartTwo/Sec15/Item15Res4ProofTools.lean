module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L Y : Subgroup G} {c : G}

theorem Conf1515HJ.sec13Data (h : Conf1515HJ A c L Y) : Sec13Data G A c L :=
  h.sec15R.toSec13Data

theorem Conf1515HJ.A_le_normalizer (h : Conf1515HJ A c L Y) :
    A ≤ Subgroup.normalizer (Y : Set G) :=
  h.mem_scriptY0Star.prop.1.1.2

theorem Conf1515HJ.le_normalizer_pCoreOf (_h : Conf1515HJ A c L Y) :
    Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y

theorem Conf1515HJ.A_le_normalizer_pCoreOf (h : Conf1515HJ A c L Y) :
    A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
  h.A_le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)

namespace Proof15Res4

omit [Finite G] in
theorem exists_mul_of_mem_sup {M O : Subgroup G} (hMO : M ≤ Subgroup.normalizer (O : Set G))
    {y : G} (hy : y ∈ M ⊔ O) : ∃ m ∈ M, ∃ o ∈ O, y = m * o := by
  have hy' : y ∈ ((M ⊔ O : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right M O hMO] at hy'
  obtain ⟨m, hm, o, ho, rfl⟩ := hy'
  exact ⟨m, hm, o, ho, rfl⟩

omit [Finite G] in
theorem conj_mul_eq {a m o : G} (ham : a * m = m * a) :
    a * (m * o) * a⁻¹ * (m * o)⁻¹ = m * (a * o * a⁻¹ * o⁻¹) * m⁻¹ := by
  have : a * m * a⁻¹ = m := by rw [ham, mul_inv_cancel_right]
  calc a * (m * o) * a⁻¹ * (m * o)⁻¹ = (a * m * a⁻¹) * (a * o * a⁻¹ * o⁻¹) * m⁻¹ := by group
    _ = m * (a * o * a⁻¹ * o⁻¹) * m⁻¹ := by rw [this]

omit [Finite G] in
theorem conj_mul_eq' (a m o : G) :
    a * (m * o) * a⁻¹ * (m * o)⁻¹ =
      (a * m * a⁻¹ * m⁻¹) * (m * (a * o * a⁻¹ * o⁻¹) * m⁻¹) := by
  group

theorem inf_le_pCoreOf_of_eq (hL : L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L) :
    CFSG.Open.pCoreOf 2 Y ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := CFSG.Open.pCoreOf 2 Y ⊓ L with hT
  set O := CFSG.Open.pCoreOf 2 L with hO
  have hOL : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLO : L ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hTO : T ≤ Subgroup.normalizer (O : Set G) := inf_le_right.trans hLO
  have hT2 : IsPGroup 2 T :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).to_le inf_le_left
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hTO2 : IsPGroup 2 (T ⊔ O : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hT2 hO2 hTO
  have hLYn : L ⊓ Y ≤ Subgroup.normalizer ((T ⊔ O : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgT : g ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · rintro ⟨ht1, ht2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hg.2) t).mp ht1,
          L.mul_mem (L.mul_mem hg.1 ht2) (L.inv_mem hg.1)⟩
      · rintro ⟨ht1, ht2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y hg.2) t).mpr ht1, ?_⟩
        have := L.mul_mem (L.mul_mem (L.inv_mem hg.1) ht2) hg.1
        simpa [mul_assoc] using this
    have hgO : g ∈ Subgroup.normalizer (O : Set G) := hLO hg.1
    have key : ∀ g' ∈ Subgroup.normalizer (T : Set G) ⊓ Subgroup.normalizer (O : Set G),
        ∀ x ∈ T ⊔ O, g' * x * g'⁻¹ ∈ T ⊔ O := by
      intro g' hg' x hx
      have hle : T ⊔ O ≤ (T ⊔ O).comap (MulAut.conj g').toMonoidHom := by
        refine sup_le (fun t ht => ?_) (fun o ho => ?_)
        · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hg'.1 t).mp ht)
        · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hg'.2 o).mp ho)
      have := hle hx
      rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    refine ⟨key g (Subgroup.mem_inf.mpr ⟨hgT, hgO⟩) x, fun hx => ?_⟩
    have h1 := key g⁻¹ (Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ hgT, Subgroup.inv_mem _ hgO⟩) _ hx
    simpa [mul_assoc] using h1
  have hOn : O ≤ Subgroup.normalizer ((T ⊔ O : Subgroup G) : Set G) := by
    intro g hg
    have : g ∈ T ⊔ O := Subgroup.mem_sup_right hg
    exact Subgroup.le_normalizer this
  have hLn : L ≤ Subgroup.normalizer ((T ⊔ O : Subgroup G) : Set G) := by
    rw [hL]
    exact sup_le hLYn hOn
  have hTOL : T ⊔ O ≤ L := sup_le inf_le_right hOL
  exact le_sup_left.trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTOL hLn hTO2)

end Proof15Res4

open Proof15Res4

theorem Conf1515HJ.c_mem_sectionCentralizer (h : Conf1515HJ A c L Y) :
    c ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) := by
  have hD := h.sec13Data
  refine ⟨hD.mem_A, fun y hy => ?_⟩
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hYLO : Y ⊓ L ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_left.trans h.le_normalizer_pCoreOf
  have hy' : y ∈ (Y ⊓ L) ⊔ O := by rw [← h.eq_Y]; exact hy
  obtain ⟨m, hm, o, ho, rfl⟩ := exists_mul_of_mem_sup hYLO hy'
  have hcm : c * m = m * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hm.2)).symm
  rw [conj_mul_eq hcm]
  have hco : c * o * c⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (h.A_le_normalizer_pCoreOf hD.mem_A) o).mp ho
  have h1 : c * o * c⁻¹ * o⁻¹ ∈ O := O.mul_mem hco (O.inv_mem ho)
  exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_pCoreOf hm.1) _).mp h1

theorem Conf1515HJ.mem_zpowers_of_mem_sectionCentralizer (h : Conf1515HJ A c L Y) {a : G}
    (ha : a ∈ Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y)) :
    a ∈ Subgroup.zpowers c := by
  have hD := h.sec13Data
  obtain ⟨haA, haY⟩ := ha
  set O := CFSG.Open.pCoreOf 2 L with hO
  have hOθ : O ≤ (aschbacherSolvableCore 3 L).map L.subtype := by
    obtain ⟨-, -, -, -, -, -, hr⟩ :=
      solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
    rw [hO, CFSG.Open.pCoreOf]
    exact Subgroup.map_mono (hr 2 Nat.prime_two (by norm_num))
  have haL : a ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer haA
  have haO : a ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L haL
  have hmem : a ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨haA, fun l hl => hOθ ?_⟩
    have hLYO : L ⊓ Y ≤ Subgroup.normalizer (O : Set G) :=
      inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
    have hl' : l ∈ (L ⊓ Y) ⊔ O := by rw [← h.eq_L]; exact hl
    obtain ⟨m, hm, o, ho, rfl⟩ := exists_mul_of_mem_sup hLYO hl'
    rw [conj_mul_eq']
    refine O.mul_mem ?_ ?_
    ·
      refine inf_le_pCoreOf_of_eq h.eq_L ⟨haY m hm.2, ?_⟩
      have h1 : a * m * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haL m).mp hm.1
      exact L.mul_mem h1 (L.inv_mem hm.1)
    · have h1 : a * o * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp haO o).mp ho
      have h2 : a * o * a⁻¹ * o⁻¹ ∈ O := O.mul_mem h1 (O.inv_mem ho)
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hm.1) _).mp h2
  rw [hD.sectionCentralizer_eq] at hmem
  exact hmem

theorem Conf1515HJ.conj_mem_zpowers (h : Conf1515HJ A c L Y) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwY : w ∈ Subgroup.normalizer (Y : Set G)) :
    w * c * w⁻¹ ∈ Subgroup.zpowers c := by
  have hD := h.sec13Data
  set O := CFSG.Open.pCoreOf 2 Y with hO
  have hwO : w ∈ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hwY
  obtain ⟨-, hcY⟩ := h.c_mem_sectionCentralizer
  refine h.mem_zpowers_of_mem_sectionCentralizer
    ⟨(Subgroup.mem_normalizer_iff.mp hwA c).mp hD.mem_A, fun y hy => ?_⟩
  have hy' : w⁻¹ * y * w ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwY) y).mp hy
    simpa using this
  have h1 := hcY _ hy'
  have h2 := (Subgroup.mem_normalizer_iff.mp hwO _).mp h1
  have e : w * (c * (w⁻¹ * y * w) * c⁻¹ * (w⁻¹ * y * w)⁻¹) * w⁻¹ =
      w * c * w⁻¹ * y * (w * c * w⁻¹)⁻¹ * y⁻¹ := by group
  rwa [e] at h2

end CFSG.RankThree.PartTwo.Sec15
