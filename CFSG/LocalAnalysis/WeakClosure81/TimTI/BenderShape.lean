module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenBasic
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderRoot
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderTransv
public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.CGT.Timmesfeld75.BenderInputs3
public import CFSG.GH74.Bender.Suzuki
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Quot

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

private theorem timti_commute_of_mk_commute {T : Subgroup X} (hT : IsPGroup 2 T)
    (hodd : Odd (Nat.card (Subgroup.center X))) {x y : X} (hx : x ∈ T) (hy : y ∈ T)
    (h : Commute (QuotientGroup.mk' (Subgroup.center X) x)
      (QuotientGroup.mk' (Subgroup.center X) y)) : Commute x y := by
  have hmk : QuotientGroup.mk' (Subgroup.center X) (x * y) =
      QuotientGroup.mk' (Subgroup.center X) (y * x) := by
    rw [map_mul, map_mul, h.eq]
  have hz : x * y * (y * x)⁻¹ ∈ Subgroup.center X := by
    have h1 : x * y * (y * x)⁻¹ ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, mul_inv_cancel]
    rwa [QuotientGroup.ker_mk'] at h1
  have hzT : x * y * (y * x)⁻¹ ∈ T :=
    T.mul_mem (T.mul_mem hx hy) (T.inv_mem (T.mul_mem hy hx))
  have hbot : x * y * (y * x)⁻¹ ∈ T ⊓ Subgroup.center X := ⟨hzT, hz⟩
  rw [CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hT hodd, Subgroup.mem_bot] at hbot
  rw [commute_iff_eq]
  exact mul_inv_eq_one.mp hbot

private theorem timti_map_sylowCenter_mk (hodd : Odd (Nat.card (Subgroup.center X)))
    {T : Subgroup X} (hT : IsPGroup 2 T) :
    (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter T).map
        (QuotientGroup.mk' (Subgroup.center X)) =
      CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
        (T.map (QuotientGroup.mk' (Subgroup.center X))) := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter]
    refine ⟨Subgroup.mem_map_of_mem _
      (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter_le T hz), ?_⟩
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hw
    have hcz := (CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter.mp hz).2 t ht
    rw [← map_mul, ← map_mul, hcz]
  · intro y hy
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter] at hy
    obtain ⟨hyT, hyc⟩ := hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hyT
    refine Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter]
    refine ⟨ht, ?_⟩
    intro u hu
    have hcu : Commute (QuotientGroup.mk' (Subgroup.center X) t)
        (QuotientGroup.mk' (Subgroup.center X) u) :=
      (hyc (QuotientGroup.mk' (Subgroup.center X) u) (Subgroup.mem_map_of_mem _ hu)).symm
    exact (timti_commute_of_mk_commute hT hodd ht hu hcu).eq.symm

private theorem timti_mk_ne_one_of_mem_rootGroup (h : Hyp X S) {d : X} (hd : d ∈ dSet S)
    {w : X} (hw : w ∈ CFSG.Timmesfeld.rootGroup (dSet S) d) (hw1 : w ≠ 1) :
    QuotientGroup.mk' (Subgroup.center X) w ≠ 1 := by
  intro hcon
  have hwZ : w ∈ Subgroup.center X := by
    have h1 : w ∈ (QuotientGroup.mk' (Subgroup.center X)).ker := by
      rw [MonoidHom.mem_ker]; exact hcon
    rwa [QuotientGroup.ker_mk'] at h1
  have hbot : w ∈ CFSG.Timmesfeld.rootGroup (dSet S) d ⊓ Subgroup.center X := ⟨hw, hwZ⟩
  rw [CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd
    (CFSG.Timmesfeld.isPGroup_rootGroup h.root hd) h.odd_card_center, Subgroup.mem_bot] at hbot
  exact hw1 hbot

theorem bender_shape
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4)
    (hdisc : CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S))
    {s : X} (hs : s ∈ S) (hs1 : s ≠ 1) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ n ∧
      IsRootGroupShape X n (CFSG.Timmesfeld.rootGroup (dSet S) s) ∧
      ∀ w ∈ CFSG.Timmesfeld.rootGroup (dSet S) s, w ≠ 1 → w ∈ dSet S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  have hodd : Odd (Nat.card (Subgroup.center X)) := h.odd_card_center
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  have hW2 : IsPGroup 2 (CFSG.Timmesfeld.rootGroup (dSet S) s) :=
    CFSG.Timmesfeld.isPGroup_rootGroup h.root hsD
  have hS : CFSG.Timmesfeld.Bridge.Asc72.Setup (X ⧸ Subgroup.center X) (π '' dSet S) :=
    h.setup_quot hdeg
  have hK : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ Subgroup.center X) :=
    CFSG.Timmesfeld.Bridge.OddTransp.oddTranspBender (X ⧸ Subgroup.center X) (π '' dSet S)
      hS h.eq_bot_of_normal_isSolvable_quot h.meetsSq_quot hdisc
  have hπs : π s ∈ π '' dSet S := ⟨s, hsD, rfl⟩
  obtain ⟨Tb, -, hroot⟩ := rootGroup_eq_sylowCenter_of_isBenderGroup hS hK hπs
  have hWmap : (CFSG.Timmesfeld.rootGroup (dSet S) s).map π =
      CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (Tb : Subgroup _) := by
    rw [h.map_rootGroup hsD]
    exact hroot
  have hDsub : ∀ w ∈ CFSG.Timmesfeld.rootGroup (dSet S) s, w ≠ 1 → w ∈ dSet S := by
    intro w hw hw1
    have hw2 : w * w = 1 :=
      CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hsD hw
    refine h.mem_dSet_of_mk_mem hw2 ?_
    have hz : π w ∈ CFSG.Timmesfeld.rootGroup (π '' dSet S) (π s) := by
      rw [← h.map_rootGroup hsD]
      exact Subgroup.mem_map_of_mem π hw
    exact mem_of_mem_rootGroup_of_isBenderGroup hS hK hπs hz
      (timti_mk_ne_one_of_mem_rootGroup h hsD hw hw1)
  cases hK with
  | isPSL2 m hm e =>
    let e₁ : (X ⧸ Subgroup.center X) ≃* StatedSp 1 (GaloisField 2 m) :=
      (e.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 m))).trans
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne (GaloisField 2 m))
    have hcardW : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ m := by
      rw [← card_map_rootGroup h hsD, hWmap]
      exact CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psl2 hm e Tb
    refine ⟨m, hm, hcardW, ?_, hDsub⟩
    unfold IsRootGroupShape
    left
    refine ⟨2, ?_, ?_⟩
    · unfold IsSpGp
      exact ⟨1, rfl, GaloisField 2 m, inferInstance, inferInstance,
        GaloisField.card 2 m (by omega), ⟨e₁⟩⟩
    · unfold IsSymplecticRootGroup
      refine ⟨hcardW, 1, rfl, GaloisField 2 m, inferInstance, inferInstance,
        GaloisField.card 2 m (by omega), e₁, ?_⟩
      intro w hw hw1
      have hw2 : w * w = 1 :=
        CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hsD hw
      have hw1' : π w ≠ 1 := timti_mk_ne_one_of_mem_rootGroup h hsD hw hw1
      refine isSymplecticTransvectionIn_one_of_mul_self ?_ ?_
      · change e₁ (π w) * e₁ (π w) = 1
        rw [← map_mul, show π w * π w = 1 from by rw [← map_mul, hw2, map_one], map_one]
      · intro hcon
        exact hw1' (e₁.injective (by rw [map_one]; exact hcon))
  | isSuzuki a ha e =>
    have hcardW : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ (2 * a + 1) := by
      rw [← card_map_rootGroup h hsD, hWmap]
      exact CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_sz ha e Tb
    refine ⟨2 * a + 1, by omega, hcardW, ?_, hDsub⟩
    unfold IsRootGroupShape
    right; right
    refine ⟨?_, ?_⟩
    · exact CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha
        (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz a)))
    · obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective (f := π) hπ 2 Tb
      have hTcoe : (T : Subgroup X).map π = (Tb : Subgroup _) := by
        rw [← Sylow.coe_mapSurjective (f := π) hπ T, hT]
      have hmapsyl : (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
            (T : Subgroup X)).map π =
          CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (Tb : Subgroup _) := by
        rw [timti_map_sylowCenter_mk hodd T.isPGroup', hTcoe]
      have hZT2 : IsPGroup 2
          (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T : Subgroup X)) :=
        T.isPGroup'.to_le
          (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter_le (T : Subgroup X))
      have hWeq : CFSG.Timmesfeld.rootGroup (dSet S) s =
          CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T : Subgroup X) :=
        CFSG.GroupTheory.eq_of_map_eq_map_of_isPGroup_of_odd_ker π
          (by rw [hker]) (by rw [hker]; exact hodd) hW2 hZT2 (by rw [hWmap, hmapsyl])
      refine ⟨T, fun x => ?_⟩
      rw [hWeq, CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter]
      constructor
      · rintro ⟨hxT, hxc⟩
        exact ⟨hxT, fun y hy => (hxc y hy).symm⟩
      · rintro ⟨hxT, hxc⟩
        exact ⟨hxT, fun y hy => (hxc y hy).symm⟩
  | isPSU3 m hm e =>
    have hPSU : IsPSUGp (X ⧸ Subgroup.center X) 3 m := by
      unfold IsPSUGp CFSG.Blueprint.LieModel
      exact Or.inl ⟨by decide,
        CFSG.CGT.Timmesfeld75.statedClassicalModel_psu3_of_mulEquiv hm e⟩
    obtain ⟨-, F, hFld, hFin, hFcard, ⟨e₂⟩⟩ :=
      CFSG.CGT.Timmesfeld75.statedClassicalModel_psu3_of_mulEquiv hm e
    letI : Field F := hFld
    letI : Finite F := hFin
    have hcardW : Nat.card (CFSG.Timmesfeld.rootGroup (dSet S) s) = 2 ^ m := by
      rw [← card_map_rootGroup h hsD, hWmap]
      exact CFSG.StronglyEmbedded.BenderCentre.card_sylowCenter_psu3 hm e Tb
    refine ⟨m, hm, hcardW, ?_, hDsub⟩
    unfold IsRootGroupShape
    right; left
    refine ⟨3, ?_, ?_⟩
    · exact hPSU
    · unfold IsUnitaryRootGroup
      refine ⟨hcardW, F, hFld, hFin, hFcard, e₂, ?_⟩
      intro w hw hw1
      have hw2 : w * w = 1 :=
        CFSG.Timmesfeld.mul_self_eq_one_of_mem_rootGroup h.root hsD hw
      have hw1' : π w ≠ 1 := timti_mk_ne_one_of_mem_rootGroup h hsD hw hw1
      refine isUnitaryTransvectionIn_three_of_mul_self (n := m) (by omega) hFcard ?_ ?_
      · change e₂ (π w) * e₂ (π w) = 1
        rw [← map_mul, show π w * π w = 1 from by rw [← map_mul, hw2, map_one], map_one]
      · intro hcon
        exact hw1' (e₂.injective (by rw [map_one]; exact hcon))

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
