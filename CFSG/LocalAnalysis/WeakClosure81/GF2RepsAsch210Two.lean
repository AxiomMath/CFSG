module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Pi
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type} [∀ i, Group (B i)]
  [∀ i, Finite (B i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210two_prodSub_normal (F : Finset ι) : (prodSub B F).Normal where
  conj_mem := fun x hx g j hj => by simp [Pi.mul_apply, Pi.inv_apply, hx j hj]

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210two_inf_eq_bot (i : ι) (F : Finset ι) :
    prodSub B {i} ⊓ prodSub B (F.erase i) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rw [Subgroup.mem_bot]
  funext j
  by_cases hj : j = i
  · rw [hj]
    exact hx.2 i (Finset.notMem_erase i F)
  · exact hx.1 j (by simpa [Finset.mem_singleton] using hj)

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210two_component_aux (hB : SimpleFactors B) {Y : Type} [Group Y] [Finite Y]
    (θ : Y →* ∀ i, B i) {F : Finset ι} (hrange : θ.range = prodSub B F)
    (hC : ¬ Subgroup.centralizer (θ.ker : Set Y) ≤ θ.ker) :
    ∃ i ∈ F, ∃ J : Subgroup Y, J.Normal ∧ Group.IsPerfect ↥J ∧ J.map θ = prodSub B {i} ∧
      ∀ p : Y, θ p ∈ prodSub B (F.erase i) → ∀ j ∈ J, j * p = p * j := by
  classical
  let C : Subgroup Y := Subgroup.centralizer (θ.ker : Set Y)
  have hCnorm : C.Normal := Subgroup.normal_centralizer
  let N : Subgroup (∀ i, B i) := C.map θ
  have hNne : N ≠ ⊥ := by
    have hC' : ¬ (C : Set Y) ⊆ (θ.ker : Set Y) := hC
    obtain ⟨x, hxC, hxQ⟩ := Set.not_subset.mp hC'
    intro hbot
    have hxN : θ x ∈ N := Subgroup.mem_map_of_mem θ hxC
    rw [hbot] at hxN
    exact hxQ (MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hxN))
  have hNle : N ≤ prodSub B F := by
    rw [← hrange]
    exact Subgroup.map_le_range θ C
  have hNnorm : ∀ s ∈ prodSub B F, ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro s hs n hn
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hs)
    obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨y * c * y⁻¹, hCnorm.conj_mem c hcC y, ?_⟩
    rw [map_mul, map_mul, map_inv]
  obtain ⟨i, hiF, hile⟩ := SimpleFactors.exists_single_le_of_normal hB hNle hNnorm hNne
  have hsingle : (prodSub B {i}).Normal := a210two_prodSub_normal {i}
  let C₁ : Subgroup Y := C ⊓ (prodSub B {i}).comap θ
  have hC₁norm : C₁.Normal := by
    have : C.Normal := hCnorm
    have : ((prodSub B {i}).comap θ).Normal := hsingle.comap θ
    exact inferInstance
  have hC₁map : C₁.map θ = prodSub B {i} := by
    apply le_antisymm
    · calc C₁.map θ ≤ ((prodSub B {i}).comap θ).map θ := Subgroup.map_mono inf_le_right
        _ ≤ prodSub B {i} := Subgroup.map_comap_le θ (prodSub B {i})
    · intro s hs
      obtain ⟨c, hcC, hcs⟩ := Subgroup.mem_map.mp (hile hs)
      exact Subgroup.mem_map.mpr
        ⟨c, ⟨hcC, Subgroup.mem_comap.mpr (by rw [hcs]; exact hs)⟩, hcs⟩
  let Sset : Set (Subgroup Y) := {J | J.Normal ∧ J ≤ C₁ ∧ J.map θ = prodSub B {i}}
  have hC₁mem : C₁ ∈ Sset := ⟨hC₁norm, le_rfl, hC₁map⟩
  obtain ⟨J, hJmem, hJmin⟩ := wellFounded_lt.has_min Sset ⟨C₁, hC₁mem⟩
  have hJnorm : J.Normal := hJmem.1
  have hJle : J ≤ C₁ := hJmem.2.1
  have hJmap : J.map θ = prodSub B {i} := hJmem.2.2
  have : J.Normal := hJnorm
  have hJperfeq : ⁅J, J⁆ = J := by
    have hmem : ⁅J, J⁆ ∈ Sset := by
      refine ⟨Subgroup.commutator_normal J J, (Subgroup.commutator_le_left J J).trans hJle, ?_⟩
      rw [Subgroup.map_commutator, hJmap]
      exact Subgroup.isPerfect_iff.mp (hB.perfect_prodSub {i})
    have hle : ⁅J, J⁆ ≤ J := Subgroup.commutator_le_left J J
    have hge : J ≤ ⁅J, J⁆ := by
      by_contra hnot
      exact hJmin ⁅J, J⁆ hmem (lt_of_le_of_ne hle fun heq => hnot (le_of_eq heq.symm))
    exact le_antisymm hle hge
  have hJperf : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperfeq
  let P : Subgroup Y := (prodSub B (F.erase i)).comap θ
  have hPnorm : P.Normal := (a210two_prodSub_normal (F.erase i)).comap θ
  have hJPleker : J ⊓ P ≤ θ.ker := by
    intro x hx
    have hxJ : θ x ∈ prodSub B {i} := by
      have h := Subgroup.mem_map_of_mem θ hx.1
      rwa [hJmap] at h
    have hxP : θ x ∈ prodSub B (F.erase i) := Subgroup.mem_comap.mp hx.2
    have hxinf : θ x ∈ prodSub B {i} ⊓ prodSub B (F.erase i) := ⟨hxJ, hxP⟩
    rw [a210two_inf_eq_bot] at hxinf
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hxinf)
  have hJleC : J ≤ C := hJle.trans inf_le_left
  have hJcentKer : ⁅J, θ.ker⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJleC
  have hdouble : ⁅⁅J, P⁆, J⁆ = ⊥ := by
    apply le_bot_iff.mp
    have : P.Normal := hPnorm
    calc ⁅⁅J, P⁆, J⁆ ≤ ⁅J ⊓ P, J⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_le_inf J P) le_rfl
      _ = ⁅J, J ⊓ P⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅J, θ.ker⁆ := Subgroup.commutator_mono le_rfl hJPleker
      _ = ⊥ := hJcentKer
  have hJPcomm : ⁅J, P⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hJperf hdouble
  refine ⟨i, hiF, J, hJnorm, hJperf, hJmap, ?_⟩
  intro p hp j hj
  have hJcent : J ≤ Subgroup.centralizer (P : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJPcomm
  exact ((Subgroup.mem_centralizer_iff.mp (hJcent hj)) p (Subgroup.mem_comap.mpr hp)).symm

omit [Fintype ι] [∀ i, Finite (B i)] in
theorem SimpleFactors.exists_perfect_component (hB : SimpleFactors B) {Y : Type} [Group Y]
    [Finite Y] (θ : Y →* ∀ i, B i) {F : Finset ι} {R : Subgroup Y}
    (hRF : R.map θ = prodSub B F)
    (hC : ¬ ∀ r ∈ R, (∀ q ∈ R ⊓ θ.ker, r * q = q * r) → r ∈ θ.ker) :
    ∃ i ∈ F, ∃ J : Subgroup Y, J ≤ R ∧ Group.IsPerfect ↥J ∧ J.map θ = prodSub B {i} ∧
      ∀ p ∈ R, θ p ∈ prodSub B (F.erase i) → ∀ j ∈ J, j * p = p * j := by
  let θR : ↥R →* ∀ i, B i := θ.domRestrict R
  have hθR : θR = θ.domRestrict R := rfl
  have hrange : θR.range = prodSub B F := by
    rw [MonoidHom.domRestrict_range, hRF]
  have hC' : ¬ Subgroup.centralizer (θR.ker : Set ↥R) ≤ θR.ker := by
    intro hle
    apply hC
    intro r hr hcomm
    have hmem : (⟨r, hr⟩ : ↥R) ∈ Subgroup.centralizer (θR.ker : Set ↥R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      refine Subtype.ext ?_
      have hz' : ((z : ↥R) : Y) ∈ R ⊓ θ.ker :=
        ⟨z.2, MonoidHom.mem_ker.mpr (by
          simpa only [hθR, MonoidHom.domRestrict_apply] using MonoidHom.mem_ker.mp hz)⟩
      exact (hcomm ((z : ↥R) : Y) hz').symm
    have hker : (⟨r, hr⟩ : ↥R) ∈ θR.ker := hle hmem
    exact MonoidHom.mem_ker.mpr (by
      simpa only [hθR, MonoidHom.domRestrict_apply] using MonoidHom.mem_ker.mp hker)
  obtain ⟨i, hiF, J', hJ'norm, hJ'perf, hJ'map, hJ'comm⟩ :=
    a210two_component_aux hB θR hrange hC'
  have hperf : Group.IsPerfect ↥(J'.map R.subtype) := by
    rw [Subgroup.isPerfect_iff]
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hJ'perf]
  have hmap : (J'.map R.subtype).map θ = prodSub B {i} := by
    have hcomp : θ.comp R.subtype = θR := MonoidHom.ext fun x => rfl
    rw [Subgroup.map_map, hcomp, hJ'map]
  refine ⟨i, hiF, J'.map R.subtype, Subgroup.map_subtype_le J', hperf, hmap, ?_⟩
  intro p hpR hp j hj
  obtain ⟨j', hj', rfl⟩ := Subgroup.mem_map.mp hj
  have hp' : θR ⟨p, hpR⟩ ∈ prodSub B (F.erase i) := hp
  exact congrArg Subtype.val (hJ'comm ⟨p, hpR⟩ hp' j' hj')

end CFSG.LocalAnalysis.WeakClosure81.Asch210
