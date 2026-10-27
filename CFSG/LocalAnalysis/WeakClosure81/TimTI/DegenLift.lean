module

public import CFSG.Timmesfeld.Bridge.OddLocalRootCore
import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsGrp
import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

theorem map_conjSubgroup_mk (W : Subgroup X) (g : X) :
    (conjSubgroup W g).map (QuotientGroup.mk' (Subgroup.center X)) =
      conjSubgroup (W.map (QuotientGroup.mk' (Subgroup.center X)))
        (QuotientGroup.mk' (Subgroup.center X) g) := by
  have h : (QuotientGroup.mk' (Subgroup.center X)).comp (MulAut.conj g⁻¹).toMonoidHom =
      (MulAut.conj ((QuotientGroup.mk' (Subgroup.center X)) g)⁻¹).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center X)) := by
    ext x
    simp only [MonoidHom.comp_apply]
    change (QuotientGroup.mk' (Subgroup.center X)) ((MulAut.conj g⁻¹) x) =
      (MulAut.conj ((QuotientGroup.mk' (Subgroup.center X)) g)⁻¹)
        ((QuotientGroup.mk' (Subgroup.center X)) x)
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    group
  rw [conjSubgroup, conjSubgroup, Subgroup.map_map, Subgroup.map_map, h]

private theorem timti_one_lt_of_isL2OrSz {Y : Type} [Group Y] {n : ℕ}
    (h : SevenK.IsL2OrSz Y n) : 1 < n := by
  rcases h with h | h
  · unfold CFSG.Quasithin.IsPSL CFSG.Open.StatedClassicalModel
      CFSG.Open.StatedLieAdmissible at h
    have h1 : 1 ≤ n := h.1.2.1
    have hne : (2, 2 ^ n) ≠ (2, 2) := h.1.2.2.2.1
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hne (by norm_num)
    omega
  · unfold CFSG.Quasithin.IsSz CFSG.Blueprint.SuzukiModel at h
    obtain ⟨-, a, ha, K, hK, hfin, hf, hcard, ⟨e⟩⟩ := h
    omega

private theorem timti_center_eq_bot_of_isL2OrSz {Y : Type} [Group Y] {n : ℕ}
    (hn : 1 < n) (hY : SevenK.IsL2OrSz Y n) : Subgroup.center Y = ⊥ := by
  haveI : IsSimpleGroup Y := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz hY
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Y) with hbot | htop
  · exact hbot
  · exfalso
    obtain ⟨a, b, hab⟩ := CFSG.Quasithin.E2.nonabelian_of_psl_or_sz hn hY
    exact hab (Subgroup.mem_center_iff.mp (htop.symm ▸ Subgroup.mem_top a) b).symm

namespace Hyp

theorem isL2OrSz_of_map
    (h : Hyp X S) {A B : Subgroup X} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) {n : ℕ}
    (hL : SevenK.IsL2OrSz ↥((A ⊔ B).map (QuotientGroup.mk' (Subgroup.center X))) n) :
    SevenK.IsL2OrSz ↥(A ⊔ B) n := by
  classical
  set K : Subgroup X := A ⊔ B with hK
  set π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X) with hπ
  set Kb : Subgroup (X ⧸ Subgroup.center X) := K.map π with hKb
  set φ : ↥K →* ↥Kb := π.subgroupMap K with hφ
  haveI : Finite ↥K := inferInstance
  have hφsurj : Function.Surjective φ := π.subgroupMap_surjective K
  have hφker : φ.ker = (Subgroup.center X).subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h' : ((φ x : ↥Kb) : X ⧸ Subgroup.center X) = 1 := congrArg Subtype.val hx
      rw [show ((φ x : ↥Kb) : X ⧸ Subgroup.center X) = π x from rfl,
        QuotientGroup.mk'_apply] at h'
      exact (QuotientGroup.eq_one_iff (x : X)).mp h'
    · intro hx
      apply Subtype.ext
      show ((φ x : ↥Kb) : X ⧸ Subgroup.center X) = 1
      rw [show ((φ x : ↥Kb) : X ⧸ Subgroup.center X) = π x from rfl,
        QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (x : X)).mpr hx
  have h1n : 1 < n := timti_one_lt_of_isL2OrSz hL
  have hcentb : Subgroup.center ↥Kb = ⊥ := timti_center_eq_bot_of_isL2OrSz h1n hL
  have hKbperf : commutator ↥Kb = ⊤ :=
    CFSG.Quasithin.E2.commutator_eq_top_of_psl_or_sz h1n hL
  have hmapC : (commutator ↥K).map φ = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective φ hφsurj]
    rw [← _root_.commutator_def]
    exact hKbperf
  have hCsup : commutator ↥K ⊔ φ.ker = ⊤ := by
    have h := Subgroup.comap_map_eq φ (commutator ↥K)
    rw [hmapC, Subgroup.comap_top] at h
    exact h.symm
  have h2quot : IsPGroup 2 (↥K ⧸ commutator ↥K) := by
    let q : ↥K →* (↥K ⧸ commutator ↥K) := QuotientGroup.mk' (commutator ↥K)
    have hA' : IsPGroup 2 (A.subgroupOf K) := hA.comap_subtype (K := K)
    have hB' : IsPGroup 2 (B.subgroupOf K) := hB.comap_subtype (K := K)
    have hAq : IsPGroup 2 ((A.subgroupOf K).map q) := IsPGroup.map hA' q
    have hBq : IsPGroup 2 ((B.subgroupOf K).map q) := IsPGroup.map hB' q
    have hsup' : (A.subgroupOf K) ⊔ (B.subgroupOf K) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (show A ≤ K from by rw [hK]; exact le_sup_left)
        (show B ≤ K from by rw [hK]; exact le_sup_right), ← hK,
        Subgroup.subgroupOf_self]
    have hsup : (A.subgroupOf K).map q ⊔ (B.subgroupOf K).map q = ⊤ := by
      rw [← Subgroup.map_sup, hsup',
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact ((hsup ▸ IsPGroup.to_sup_of_normal_right hAq hBq)).of_equiv Subgroup.topEquiv
  have hdivD : Nat.card ((Subgroup.center X).subgroupOf K) ∣ Nat.card (Subgroup.center X) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.card_comap_dvd_of_injective (Subgroup.center X) K.subtype K.subtype_injective
  have hoddD : Odd (Nat.card φ.ker) := by
    rw [hφker]
    exact h.odd_card_center.of_dvd_nat hdivD
  have hoddquot : Odd (Nat.card (↥K ⧸ commutator ↥K)) := by
    let q : ↥K →* (↥K ⧸ commutator ↥K) := QuotientGroup.mk' (commutator ↥K)
    let g : φ.ker →* (↥K ⧸ commutator ↥K) := q.comp φ.ker.subtype
    have hgsurj : Function.Surjective g := by
      have hker_map : (commutator ↥K).map q = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨c, hc, rfl⟩
        rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      have hrange : (φ.ker).map q = ⊤ := by
        have h1 : (commutator ↥K ⊔ φ.ker).map q = ⊤ := by
          rw [hCsup, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
        rwa [Subgroup.map_sup, hker_map, bot_sup_eq] at h1
      intro y
      have hy : y ∈ (φ.ker).map q := by rw [hrange]; trivial
      obtain ⟨d, hd, hdeq⟩ := (Subgroup.mem_map).mp hy
      exact ⟨⟨d, hd⟩, hdeq⟩
    exact hoddD.of_dvd_nat (Subgroup.card_dvd_of_surjective hgsurj)
  have hKperf : commutator ↥K = ⊤ := by
    have hcard1 : Nat.card (↥K ⧸ commutator ↥K) = 1 := by
      rcases h2quot.card_eq_or_dvd with h1 | h2
      · exact h1
      · exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hoddquot)
    exact QuotientGroup.subsingleton_iff.mp (Nat.card_eq_one_iff_unique.mp hcard1).1
  haveI : Group.IsPerfect ↥K := ⟨hKperf⟩
  have hDcenter : φ.ker ≤ Subgroup.center ↥K := by
    rw [hφker, ← Subgroup.comap_subtype]
    exact Subgroup.comap_center_le_center K.subtype_injective
  have hcenter_le : Subgroup.center ↥K ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : φ z ∈ Subgroup.center ↥Kb := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hφsurj w
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subgroup.mem_center_iff.mp hz y)
    rw [hcentb, Subgroup.mem_bot] at hzc
    exact hzc
  have hcenter_eq : Subgroup.center ↥K = φ.ker := le_antisymm hcenter_le hDcenter
  have hKcenterIso : (↥K ⧸ Subgroup.center ↥K) ≃* ↥Kb :=
    (QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have hKcenterOrSz : SevenK.IsL2OrSz (↥K ⧸ Subgroup.center ↥K) n :=
    isL2OrSz_of_mulEquiv hL hKcenterIso.symm
  have hZodd : Odd (Nat.card (Subgroup.center ↥K)) := by
    rw [hcenter_eq, hφker]
    exact h.odd_card_center.of_dvd_nat hdivD
  have hZ2 : IsPGroup 2 (Subgroup.center ↥K) := by
    rcases hKcenterOrSz with hP | hSz
    · obtain ⟨-, F, hFld, hFfin, hFcard, ⟨eF⟩⟩ := hP
      letI : Field F := hFld
      letI : Finite F := hFfin
      exact CFSG.Quasithin.isPGroup_two_of_mulEquiv_stated_psl_two_even
        (Subgroup.center ↥K) le_rfl h1n hFcard eF
    · exact CFSG.Quasithin.isPGroup_two_of_isSz (Subgroup.center ↥K) le_rfl hSz
  have hZbot : Subgroup.center ↥K = ⊥ := by
    have hcard1 : Nat.card (Subgroup.center ↥K) = 1 := by
      rcases hZ2.card_eq_or_dvd with h1 | h2
      · exact h1
      · exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hZodd)
    exact Subgroup.card_eq_one.mp hcard1
  have hKiso : ↥Kb ≃* ↥K :=
    hKcenterIso.symm.trans (CFSG.Timmesfeld.Bridge.OddLocal.mulEquivOfCenterEqBot hZbot).symm
  exact isL2OrSz_of_mulEquiv hL hKiso

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
