module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65SylowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open scoped Pointwise

private theorem exists_isSylowOf_ge_chain {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {K E : Subgroup G} (hEK : E ≤ K) (hE : IsPGroup p ↥E) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ E ≤ P := by
  obtain ⟨T, hT⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hEK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem isWeaklyClosedIn_normalizer_of_uniqueSet {G : Type} [Group G] [Finite G]
    {D : Data G} {Z : Subgroup G} (hZU : Z ∈ uniqueSet D.M)
    (hW : ∀ m ∈ D.M, CFSG.conjugate Z m ≤ Subgroup.normalizer (Z : Set G) →
      CFSG.conjugate Z m = Z) :
    CFSG.ASVolI.ChIJK.IsWeaklyClosedIn Z (Subgroup.normalizer (Z : Set G)) := by
  intro g hg
  have hgM : g ∈ D.M := by
    have hNM : Subgroup.normalizer (Z : Set G) ≤ D.M :=
      CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hZU
    have hZgM : CFSG.conjugate Z g ≤ D.M := hg.trans hNM
    have hginv : g⁻¹ ∈ D.M :=
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.mem_of_map_conj_le_of_mem_uniqueSet
        D.maxLocal hZU (h := g⁻¹) (by simpa [CFSG.conjugate] using hZgM)
    simpa using D.M.inv_mem hginv
  exact hW g hgM hg

theorem eq_of_le_sup_of_le_normalizer {G : Type} [Group G] [Finite G] {Z Y O : Subgroup G}
    (hZ : Nat.card Z = 3) (hY : Nat.card Y = 3) (hO : Nat.Coprime 3 (Nat.card O))
    (hZO : Z ≤ Subgroup.normalizer (O : Set G)) (hYZO : Y ≤ Z ⊔ O)
    (hYN : Y ≤ Subgroup.normalizer (Z : Set G)) : Y = Z := by
  have hdisj : Z ⊓ O = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxZ : x ∈ Z := hx.1
    have hxO : x ∈ O := hx.2
    have h1 : orderOf x ∣ 3 := by rw [← hZ]; exact Z.orderOf_dvd_natCard hxZ
    have h2 : orderOf x ∣ Nat.card O := O.orderOf_dvd_natCard hxO
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hO h1 h2)
  have hsup : (↑(Z ⊔ O) : Set G) = (Z : Set G) * (O : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Z O hZO
  have hle : Y ≤ Z := by
    intro y hy
    have hyZO : y ∈ (Z ⊔ O : Subgroup G) := hYZO hy
    have hyZO' : y ∈ (Z : Set G) * (O : Set G) := by
      rw [← hsup]
      exact hyZO
    obtain ⟨z, hz, o, ho, rfl⟩ := hyZO'
    have hyN : z * o ∈ Subgroup.normalizer (Z : Set G) := hYN hy
    have hcomm : Commute z o := by
      have hoN : o ∈ Subgroup.normalizer (Z : Set G) := by
        have hzN : z ∈ Subgroup.normalizer (Z : Set G) := Subgroup.le_normalizer hz
        have h := (Subgroup.normalizer (Z : Set G)).mul_mem
          ((Subgroup.normalizer (Z : Set G)).inv_mem hzN) hyN
        simpa using h
      have hcommZ : o * z * o⁻¹ = z := by
        have hmemZ : o * z * o⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hoN z).mp hz
        have hmemO : o * z * o⁻¹ * z⁻¹ ∈ O := by
          have hzO : z * o⁻¹ * z⁻¹ ∈ O :=
            (Subgroup.mem_normalizer_iff.mp (hZO hz) o⁻¹).mp (O.inv_mem ho)
          have hrew : o * z * o⁻¹ * z⁻¹ = o * (z * o⁻¹ * z⁻¹) := by group
          rw [hrew]
          exact O.mul_mem ho hzO
        have hmemZO : o * z * o⁻¹ * z⁻¹ ∈ Z ⊓ O :=
          ⟨Z.mul_mem hmemZ (Z.inv_mem hz), hmemO⟩
        have hc1 : o * z * o⁻¹ * z⁻¹ = 1 := by simpa [hdisj] using hmemZO
        exact mul_inv_eq_one.mp hc1
      have hzo : o * z = z * o := by
        have h := congrArg (fun x => x * o) hcommZ
        simpa [mul_assoc] using h
      exact hzo.symm
    have hz3 : z ^ 3 = 1 := by
      have h : orderOf z ∣ 3 := by rw [← hZ]; exact Z.orderOf_dvd_natCard hz
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have hy3 : (z * o) ^ 3 = 1 := by
      have h : orderOf (z * o) ∣ 3 := by rw [← hY]; exact Y.orderOf_dvd_natCard hy
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have ho3 : o ^ 3 = 1 := by
      rw [hcomm.mul_pow 3, hz3, one_mul] at hy3
      exact hy3
    have ho1 : o = 1 := by
      have h1 : orderOf o ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ho3
      have h2 : orderOf o ∣ Nat.card O := O.orderOf_dvd_natCard ho
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hO h1 h2)
    rw [ho1]
    simpa using hz
  have hcard : Nat.card Z ≤ Nat.card Y := by omega
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem conjugate_eq_of_le_normalizer_of_sylow {Y : Type} [Group Y] [Finite Y]
    (Q : Sylow 3 Y) {Z : Subgroup Y} (hZQ : Z ≤ (Q : Subgroup Y))
    (hZc : Z ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y))
    (hwc : ∀ g : Y, CFSG.conjugate Z g ≤ (Q : Subgroup Y) → CFSG.conjugate Z g = Z)
    {g : Y} (hg : CFSG.conjugate Z g ≤ Subgroup.normalizer (Z : Set Y)) :
    CFSG.conjugate Z g = Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQN : (Q : Subgroup Y) ≤ Subgroup.normalizer (Z : Set Y) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq z hz
    have hcomm : q * z = z * q := Subgroup.mem_centralizer_iff.mp (hZc hz) q hq
    rw [hcomm]
    simpa using hz
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  have hQNsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup Y)
      (Subgroup.normalizer (Z : Set Y)) :=
    hQtop.of_le hQN le_top
  have hA : IsPGroup 3 ↥(CFSG.conjugate Z g) := by
    have hZ3 : IsPGroup 3 Z := Q.isPGroup'.to_le hZQ
    exact hZ3.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨S, hSN, hAS⟩ := exists_isSylowOf_ge_chain hg hA
  obtain ⟨k, hkN, hk⟩ := hQNsyl.exists_mem_conj hSN
  have hZgkQ : CFSG.conjugate Z (g * k) ≤ (Q : Subgroup Y) := by
    rw [← CFSG.GroupTheory.conjugate_conjugate]
    intro x hx
    rw [CFSG.conjugate] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have haS : a ∈ S := hAS ha
    have hmem := (hk a).mp haS
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmem
  have hZgk : CFSG.conjugate Z (g * k) = Z := hwc (g * k) hZgkQ
  have hZk : CFSG.conjugate Z k = Z := by
    have hk' : k⁻¹ ∈ Subgroup.normalizer (Z : Set Y) :=
      (Subgroup.normalizer (Z : Set Y)).inv_mem hkN
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hk'
    simpa [CFSG.conjugate] using h
  have hZg : CFSG.conjugate Z g = Z := by
    have h1 : CFSG.conjugate Z g = CFSG.conjugate (CFSG.conjugate Z (g * k)) k⁻¹ := by
      rw [CFSG.GroupTheory.conjugate_conjugate]
      simp
    rw [h1, hZgk]
    have h2 : CFSG.conjugate Z k⁻¹ = Z := by
      have h := CFSG.GroupTheory.conjugate_conjugate Z k k⁻¹
      rw [hZk, mul_inv_cancel] at h
      have h1 : CFSG.conjugate Z 1 = Z := CFSG.conjugate_one Z
      rw [h1] at h
      exact h
    exact h2
  exact hZg

theorem exists_conjugate_eq_map_of_sylow_center {Y : Type} [Group Y] [Finite Y]
    (Q : Sylow 3 Y) {Z : Subgroup Y} (hZQ : Z ≤ (Q : Subgroup Y))
    (hZc : Z ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y)) (hZ3 : Nat.card Z = 3)
    (hQZ : Nat.card ((Subgroup.center ↥(Q : Subgroup Y)).map (Q : Subgroup Y).subtype) = 3)
    (φ : MulAut Y) : ∃ h : Y, Z.map φ.toMonoidHom = CFSG.conjugate Z h := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZZQ : Z ≤ (Subgroup.center ↥(Q : Subgroup Y)).map (Q : Subgroup Y).subtype := by
    intro z hz
    refine Subgroup.mem_map.2 ⟨⟨z, hZQ hz⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hZc hz)) q q.2)
  have hZeqZQ : Z = (Subgroup.center ↥(Q : Subgroup Y)).map (Q : Subgroup Y).subtype := by
    refine Subgroup.eq_of_le_of_card_ge hZZQ ?_
    rw [hQZ, hZ3]
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 3 (Q : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  have hφQtop : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup Y).map φ.toMonoidHom) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Subgroup.card_map_of_injective φ.injective]
    exact CFSG.ABGLocalTools.IsSylowOf.card_eq hQtop
  obtain ⟨k, -, hkconj⟩ := hQtop.exists_mem_conj hφQtop
  refine ⟨k⁻¹, ?_⟩
  have hle : Z.map φ.toMonoidHom ≤ CFSG.conjugate Z k⁻¹ := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hwQ : k⁻¹ * φ z * k ∈ (Q : Subgroup Y) := by
      have hφz : φ z ∈ (Q : Subgroup Y).map φ.toMonoidHom := by
        rw [Subgroup.mem_map]
        exact ⟨z, hZQ hz, rfl⟩
      exact (hkconj (φ z)).mp hφz
    have hwZ : k⁻¹ * φ z * k ∈ Z := by
      rw [hZeqZQ]
      refine Subgroup.mem_map.2 ⟨⟨k⁻¹ * φ z * k, hwQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hkqk_mem : k * (q : Y) * k⁻¹ ∈ (Q : Subgroup Y).map φ.toMonoidHom :=
        (hkconj (k * (q : Y) * k⁻¹)).mpr (by simp [mul_assoc])
      obtain ⟨q', hq'Q, hφq'⟩ := Subgroup.mem_map.1 hkqk_mem
      have hzq' : q' * z = z * q' :=
        (Subgroup.mem_centralizer_iff.mp (hZc hz)) q' hq'Q
      have hφ_comm : φ q' * φ z = φ z * φ q' := by
        rw [← map_mul, ← map_mul, hzq']
      have hconj : q * (k⁻¹ * φ z * k) = (k⁻¹ * φ z * k) * q := by
        have hφq'' : φ q' = k * (q : Y) * k⁻¹ := by
          simpa only [MulEquiv.coe_toMonoidHom] using hφq'
        have h := congrArg (fun x => k⁻¹ * x * k) hφ_comm
        rw [hφq''] at h
        simpa [mul_assoc] using h
      simpa using hconj
    rw [CFSG.conjugate]
    refine Subgroup.mem_map.2 ⟨k⁻¹ * φ z * k, hwZ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hcard : Nat.card (CFSG.conjugate Z k⁻¹) ≤ Nat.card (Z.map φ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective φ.injective, CFSG.conjugate,
        Subgroup.card_map_of_injective (MulAut.conj (k⁻¹)⁻¹).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem map_eq_of_le_normalizer_of_sylowCenterWeaklyClosed {Y : Type} [Group Y] [Finite Y]
    (hY : SylowCenterWeaklyClosed Y) (Q : Sylow 3 Y) {Z : Subgroup Y}
    (hZQ : Z ≤ (Q : Subgroup Y))
    (hZc : Z ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y)) (hZ3 : Nat.card Z = 3)
    (hQZ : Nat.card ((Subgroup.center ↥(Q : Subgroup Y)).map (Q : Subgroup Y).subtype) = 3)
    (φ : MulAut Y) (hφ : Z.map φ.toMonoidHom ≤ Subgroup.normalizer (Z : Set Y)) :
    Z.map φ.toMonoidHom = Z := by
  obtain ⟨h, hh⟩ := exists_conjugate_eq_map_of_sylow_center Q hZQ hZc hZ3 hQZ φ
  rw [hh] at hφ ⊢
  exact conjugate_eq_of_le_normalizer_of_sylow Q hZQ hZc (hY Q Z hZQ hZc hZ3) hφ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
