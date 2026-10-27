module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45OuterSpan
import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44G45OuterPVAux1
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44ModelAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

private theorem w183finSp44pv_mOfG_eq {G : Type} [Group G] (A B : Subgroup G)
    [Finite ↥A] [Finite ↥B] (hBA : B ≤ A) {k : Nat}
    (hcard : Nat.card ↥A = Nat.card ↥B * 2 ^ k) : mOfG A B = k := by
  haveI : Nonempty ↥B := ⟨⟨1, B.one_mem⟩⟩
  haveI : Finite ↥(B.subgroupOf A) := inferInstance
  rw [mOfG, Subgroup.index_eq_card_div, w183finSp44pv_card_subgroupOf hBA, hcard]
  rw [Nat.mul_div_cancel_left _ Nat.card_pos]
  exact Nat.log_pow (by norm_num) k

theorem pairViolation_of_checkPV {c : Nat} (hc : checkPV c = true) :
    ∃ y : MulAut S4, PairViolation (outerRep c) y := by
  simp only [checkPV] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcomm, hnodupR⟩, hlenR⟩, hwit1⟩, hwit2⟩, hidx1⟩, hidx2⟩, htree⟩, h5⟩,
    h7⟩ := hc
  have hRall : outerRepGens.all (fun row => row.all validB) = true := by decide +kernel
  have hYall : outerY.all validB = true := by decide +kernel
  have hgRvalid : ∀ x ∈ outerRepGens.getD c [], validB x = true := by
    intro x hx
    rcases Nat.lt_or_ge c outerRepGens.length with hc' | hc'
    · rw [List.getD_eq_getElem outerRepGens [] hc'] at hx
      exact (List.all_eq_true.mp ((List.all_eq_true.mp hRall) _ (List.getElem_mem hc'))) x hx
    · rw [List.getD_eq_default outerRepGens [] hc'] at hx
      simp at hx
  have hyEvalid : validB (outerY.getD c oneE) = true := by
    rcases Nat.lt_or_ge c outerY.length with hc' | hc'
    · rw [List.getD_eq_getElem outerY oneE hc']
      exact (List.all_eq_true.mp hYall) _ (List.getElem_mem hc')
    · rw [List.getD_eq_default outerY oneE hc']; exact validB_oneE
  have hc4 : c < 4 := by
    by_contra h
    have hge : outerRepGens.length ≤ c := by
      have : 4 ≤ c := by omega
      simpa [outerRepGens] using this
    have hgeY : outerY.length ≤ c := by
      have : 4 ≤ c := by omega
      simpa [outerY] using this
    have hg0 : outerRepGens.getD c [] = [] := List.getD_eq_default outerRepGens [] hge
    have hy0 : outerY.getD c oneE = oneE := List.getD_eq_default outerY oneE hgeY
    have hRy0 : (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)) = [oneE] := by
      rw [hg0, show span2 ([] : List El) = [oneE] from rfl, List.map_singleton,
        w183finSp44pv_conjE_oneE (by rw [hy0]; exact validB_oneE)]
    rw [hRy0, hg0] at hwit1
    simp only [show span2 ([] : List El) = [oneE] from rfl, List.any_cons, List.any_nil,
      Bool.or_false] at hwit1
    rw [w183finSp44pv_conjE_oneE validB_oneE] at hwit1
    simp [memK] at hwit1
  have hRvalid : ∀ x ∈ span2 (outerRepGens.getD c []), validB x = true :=
    w183finSp44pv_span2_valid hgRvalid
  have hRnodup : (span2 (outerRepGens.getD c [])).Nodup :=
    w183finSp44pv_nodupE_sound hnodupR
  have hRvalRy : ∀ s ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)),
      validB s = true := by
    intro s hs
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hs
    rw [← hxe]
    exact w183finSp44pv_valid_conjE hyEvalid (hRvalid x hx)
  have hRylNodup : ((span2 (outerRepGens.getD c [])).map
      (conjE (outerY.getD c oneE))).Nodup :=
    List.Nodup.map_on
      (fun a ha b hb hab => w183finSp44pv_conjE_inj hyEvalid (hRvalid a ha) (hRvalid b hb) hab)
      hRnodup
  have hK1 : (outerK.getD c (0, 0)).1 ≤ 2 := by
    have hc' : c < 4 := by simpa [outerK] using hc4
    interval_cases c <;> decide +kernel
  have hK2 : (outerK.getD c (0, 0)).2 ≤ 2 := by
    have hc' : c < 4 := by simpa [outerK] using hc4
    interval_cases c <;> decide +kernel
  have hKne : outerK.getD c (0, 0) ≠ (1, 1) := by
    have hc' : c < 4 := by simpa [outerK] using hc4
    interval_cases c <;> decide +kernel
  have hAcard : Nat.card (outerRep c) = (span2 (outerRepGens.getD c [])).length :=
    w183finSp44pv_card_of_iff hRnodup hRvalid (mem_outerRep_iff hc4)
  have hAiff : ∀ α, α ∈ outerRep c ↔
      ∃ r ∈ span2 (outerRepGens.getD c []), autOf r = α :=
    mem_outerRep_iff hc4
  have hAeq : outerRep c = Subgroup.closure (autOf '' {x | x ∈ outerRepGens.getD c []}) := by
    apply Subgroup.ext
    intro α
    rw [hAiff α]
    exact (mem_closure_autOf_iff hcomm hgRvalid α).symm
  have hAset : ((outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom :
      Set (MulAut S4)) =
      autOf '' {x | x ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))} := by
    ext α
    constructor
    · intro hα
      obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hα
      obtain ⟨r, hr, hre⟩ := (hAiff a).mp ha
      refine ⟨conjE (outerY.getD c oneE) r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
      rw [← hae, ← hre]
      exact (autOf_conjE hyEvalid (hRvalid r hr)).trans (MulAut.conj_apply _ _).symm
    · rintro ⟨z, hz, hze⟩
      obtain ⟨r, hr, hre⟩ := List.mem_map.mp hz
      refine ⟨autOf r, (hAiff _).mpr ⟨r, hr, rfl⟩, ?_⟩
      rw [← hze, ← hre]
      exact (MulAut.conj_apply _ _).trans (autOf_conjE hyEvalid (hRvalid r hr)).symm
  have hAyEq : (outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom =
      Subgroup.closure (autOf '' {x | x ∈
        (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))}) := by
    rw [show (Subgroup.closure (autOf '' {x | x ∈
        (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))})) =
        Subgroup.closure ((outerRep c).map
          (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4)) from by
      rw [hAset]]
    exact (Subgroup.closure_eq _).symm
  have hRyI : ∀ z, validB z = true →
      (autOf z ∈ Subgroup.closure (autOf '' {x | x ∈
        (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))}) ↔
        z ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))) := by
    intro z hz
    rw [← hAyEq]
    change autOf z ∈ ((outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4)) ↔
      z ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))
    rw [hAset]
    constructor
    · rintro ⟨x, hx, hxz⟩
      have hxz' : x = z := autOf_inj (hRvalRy x hx) hz hxz
      rwa [hxz'] at hx
    · intro hz'; exact ⟨z, hz', rfl⟩
  have hRzI : ∀ z, validB z = true →
      (autOf z ∈ outerRep c ↔ z ∈ span2 (outerRepGens.getD c [])) := by
    intro z hz
    rw [hAiff (autOf z)]
    constructor
    · rintro ⟨r, hr, hrz⟩
      have hrz' : r = z := autOf_inj (hRvalid r hr) hz hrz
      rwa [hrz'] at hr
    · intro hz'; exact ⟨z, hz', rfl⟩
  have hRext : Subgroup.closure (autOf '' {x | x ∈ span2 (outerRepGens.getD c [])}) =
      outerRep c := by
    rw [show autOf '' {x | x ∈ span2 (outerRepGens.getD c [])} =
        (outerRep c : Set (MulAut S4)) from ?_]
    exact Subgroup.closure_eq _
    ext α
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hAiff _).mpr ⟨r, hr, rfl⟩
    · intro hα
      obtain ⟨r, hr, hre⟩ := (hAiff α).mp hα
      exact ⟨r, hr, hre⟩
  have hRextI : ∀ z, validB z = true →
      (autOf z ∈ Subgroup.closure (autOf '' {x | x ∈ span2 (outerRepGens.getD c [])}) ↔
        z ∈ span2 (outerRepGens.getD c [])) := by
    intro z hz
    rw [hRext]
    exact hRzI z hz
  have hXgen : outerRep c ⊔ (outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom =
      Subgroup.closure (autOf '' {x | x ∈ outerRepGens.getD c [] ++
        (outerRepGens.getD c []).map (conjE (outerY.getD c oneE))}) := by
    rw [hAeq]
    rw [w183finSp44pv_map_closure_conj hyEvalid hgRvalid, ← Subgroup.closure_union]
    congr 1
    ext x
    constructor
    · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
      · exact ⟨r, List.mem_append.mpr (Or.inl hr), rfl⟩
      · exact ⟨r, List.mem_append.mpr (Or.inr hr), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
  have hgensXvalid : ∀ x ∈ outerRepGens.getD c [] ++
      (outerRepGens.getD c []).map (conjE (outerY.getD c oneE)), validB x = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hgRvalid x hx
    · obtain ⟨g, hg, hge⟩ := List.mem_map.mp hx
      rw [← hge]
      exact w183finSp44pv_valid_conjE hyEvalid (hgRvalid g hg)
  have hgensXinv : ∀ x ∈ outerRepGens.getD c [] ++
      (outerRepGens.getD c []).map (conjE (outerY.getD c oneE)), gmulE x x = oneE := by
    intro x hx
    have hcomm' := hcomm
    rw [commInv, Bool.and_eq_true] at hcomm'
    rcases List.mem_append.mp hx with hx | hx
    · have hxx : (x != oneE && gmulE x x == oneE) = true :=
        (List.all_eq_true.mp hcomm'.1) x hx
      rw [Bool.and_eq_true] at hxx
      exact beq_iff_eq.mp hxx.2
    · obtain ⟨g, hg, hge⟩ := List.mem_map.mp hx
      rw [← hge]
      have hgg : (g != oneE && gmulE g g == oneE) = true :=
        (List.all_eq_true.mp hcomm'.1) g hg
      rw [Bool.and_eq_true] at hgg
      rw [w183finSp44pv_conjE_gmulE hyEvalid (hgRvalid g hg) (hgRvalid g hg),
        beq_iff_eq.mp hgg.2, w183finSp44pv_conjE_oneE hyEvalid]
  have hXcard : Nat.card ↥(outerRep c ⊔ (outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom) =
      (outerX.getD c ([], [])).1.length := by
    rw [hXgen]
    exact w183finSp44pv_checkTree_card htree hgensXvalid hgensXinv
  have hnot1 : ¬ (outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom ≤
      Subgroup.normalizer (outerRep c : Set (MulAut S4)) := by
    obtain ⟨s, hs, hwit⟩ := List.any_eq_true.mp hwit1
    obtain ⟨r, hr, hwr⟩ := List.any_eq_true.mp hwit
    have hwR : conjE s r ∉ span2 (outerRepGens.getD c []) := by
      intro hmem
      have hmem' : memK (span2 (outerRepGens.getD c [])) (conjE s r) = true := by
        rw [memK]; exact List.any_eq_true.mpr ⟨conjE s r, hmem, by simp⟩
      rw [hmem'] at hwr
      exact Bool.noConfusion hwr
    have hsval : validB s = true := hRvalRy s hs
    have hrval : validB r = true := hRvalid r hr
    have hsAy : autOf s ∈ (outerRep c).map
        (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom := by
      change autOf s ∈ ((outerRep c).map
        (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4))
      rw [hAset]
      exact ⟨s, hs, rfl⟩
    have hnotN : autOf s ∉ Subgroup.normalizer (outerRep c : Set (MulAut S4)) := by
      intro hN
      have hmap : (outerRep c).map (MulAut.conj (autOf s)).toMonoidHom = outerRep c :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp hN
      have hmem : (MulAut.conj (autOf s)) (autOf r) ∈ outerRep c := by
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨autOf r, (hAiff _).mpr ⟨r, hr, rfl⟩, rfl⟩
      have hconj : autOf (conjE s r) = (MulAut.conj (autOf s)) (autOf r) :=
        (autOf_conjE hsval hrval).trans (MulAut.conj_apply _ _).symm
      apply hwR
      apply (hRzI (conjE s r) (w183finSp44pv_valid_conjE hsval hrval)).mp
      rwa [← hconj] at hmem
    intro hle
    exact hnotN (hle hsAy)
  have hnot2 : ¬ outerRep c ≤ Subgroup.normalizer
      ((outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom :
        Set (MulAut S4)) := by
    obtain ⟨r, hr, hwit⟩ := List.any_eq_true.mp hwit2
    obtain ⟨s, hs, hwr⟩ := List.any_eq_true.mp hwit
    have hwRy : conjE r s ∉ (span2 (outerRepGens.getD c [])).map
        (conjE (outerY.getD c oneE)) := by
      intro hmem
      have hmem' : memK ((span2 (outerRepGens.getD c [])).map
          (conjE (outerY.getD c oneE))) (conjE r s) = true := by
        rw [memK]; exact List.any_eq_true.mpr ⟨conjE r s, hmem, by simp⟩
      rw [hmem'] at hwr
      exact Bool.noConfusion hwr
    have hrval : validB r = true := hRvalid r hr
    have hsval : validB s = true := hRvalRy s hs
    have hnotN : autOf r ∉ Subgroup.normalizer
        ((outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom :
          Set (MulAut S4)) := by
      intro hN
      have hmap : ((outerRep c).map
          (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom).map
          (MulAut.conj (autOf r)).toMonoidHom =
          (outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp hN
      have hAy_s : autOf s ∈ (outerRep c).map
          (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom := by
        change autOf s ∈ ((outerRep c).map
          (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4))
        rw [hAset]
        exact ⟨s, hs, rfl⟩
      have hmem : (MulAut.conj (autOf r)) (autOf s) ∈
          (outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom := by
        rw [← hmap]
        exact Subgroup.mem_map.mpr ⟨autOf s, hAy_s, rfl⟩
      have hconj : autOf (conjE r s) = (MulAut.conj (autOf r)) (autOf s) :=
        (autOf_conjE hrval hsval).trans (MulAut.conj_apply _ _).symm
      have hmem' : autOf (conjE r s) ∈ Subgroup.closure (autOf '' {x | x ∈
          (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))}) := by
        rw [hconj]
        rw [← hAyEq]
        exact hmem
      apply hwRy
      exact (hRyI (conjE r s) (w183finSp44pv_valid_conjE hrval hsval)).mp hmem'
    intro hle
    exact hnotN (hle ((hAiff _).mpr ⟨r, hr, rfl⟩))
  have hAiff' : ∀ α, α ∈ Subgroup.closure (autOf '' {x | x ∈ outerRepGens.getD c []}) ↔
      ∃ r ∈ span2 (outerRepGens.getD c []), autOf r = α := by
    intro α
    rw [← hAeq]
    exact hAiff α
  have hcard1 : Nat.card ↥(outerRep c ⊓
      Subgroup.normalizer ((outerRep c).map
        (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4))) =
      ((span2 (outerRepGens.getD c [])).filter (fun r =>
        ((span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))).all
          fun s => memK ((span2 (outerRepGens.getD c [])).map
            (conjE (outerY.getD c oneE))) (conjE r s))).length := by
    rw [hAyEq, hAeq]
    exact w183finSp44pv_card_inf_normalizer (gens := outerRepGens.getD c [])
      (R := span2 (outerRepGens.getD c []))
      (Ry := (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)))
      hRnodup hRvalid hAiff' hRyI hRvalRy
  have hAyIff : ∀ α, α ∈ Subgroup.closure (autOf '' {x | x ∈
      (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))}) ↔
      ∃ r ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)),
        autOf r = α := by
    intro α
    rw [← hAyEq]
    change α ∈ ((outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4)) ↔
      ∃ r ∈ (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)),
        autOf r = α
    rw [hAset]
    exact Iff.rfl
  have hcard2 : Nat.card ↥((outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom ⊓
      Subgroup.normalizer (outerRep c : Set (MulAut S4))) =
      (((span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))).filter
        (fun s => (span2 (outerRepGens.getD c [])).all
          fun r => memK (span2 (outerRepGens.getD c [])) (conjE s r))).length := by
    rw [hAyEq, ← hRext]
    exact w183finSp44pv_card_inf_normalizer
      (gens := (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)))
      (R := (span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE)))
      (Ry := span2 (outerRepGens.getD c []))
      hRylNodup hRvalRy hAyIff hRextI hRvalid
  have hidx1' : mOfG (outerRep c) (outerRep c ⊓
      Subgroup.normalizer ((outerRep c).map
        (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom : Set (MulAut S4))) =
      (outerK.getD c (0, 0)).1 := by
    apply w183finSp44pv_mOfG_eq _ _ inf_le_left
    rw [hAcard, hcard1, beq_iff_eq.mp hidx1]
  have hAycard : Nat.card ↥((outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom) =
      ((span2 (outerRepGens.getD c [])).map (conjE (outerY.getD c oneE))).length := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (autOf (outerY.getD c oneE))).injective,
      hAcard, List.length_map]
  have hidx2' : mOfG ((outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom)
      ((outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom ⊓
        Subgroup.normalizer (outerRep c : Set (MulAut S4))) =
      (outerK.getD c (0, 0)).2 := by
    apply w183finSp44pv_mOfG_eq _ _ inf_le_left
    rw [hAycard, hcard2, beq_iff_eq.mp hidx2]
  have hdiv : Nat.card (Bar2 (outerRep c ⊔ (outerRep c).map
      (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom)) ∣
      (outerX.getD c ([], [])).1.length := by
    have h := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(outerRep c ⊔
      (outerRep c).map (MulAut.conj (autOf (outerY.getD c oneE))).toMonoidHom))
    rw [hXcard] at h
    exact h
  refine ⟨autOf (outerY.getD c oneE), hnot1, hnot2, ?_, ?_, ?_⟩
  · rw [hidx1']; exact hK1
  · rw [hidx2']; exact hK2
  · rw [hidx1', hidx2']
    have h5' : ¬ 5 ∣ (outerX.getD c ([], [])).1.length := by
      intro h
      have hne : (outerX.getD c ([], [])).1.length % 5 ≠ 0 := by simpa using h5
      exact hne (Nat.dvd_iff_mod_eq_zero.mp h)
    have h7' : ¬ 7 ∣ (outerX.getD c ([], [])).1.length := by
      intro h
      have hne : (outerX.getD c ([], [])).1.length % 7 ≠ 0 := by simpa using h7
      exact hne (Nat.dvd_iff_mod_eq_zero.mp h)
    rintro (⟨h1, h2, -⟩ | ⟨hsum, hcard⟩ | ⟨h1, h2, hcard⟩)
    · exact hKne (Prod.ext h1 h2)
    · exact h5' (dvd_trans (by norm_num : 5 ∣ 60) (hcard ▸ hdiv))
    · rcases hcard with h60 | h504
      · exact h5' (dvd_trans (by norm_num : 5 ∣ 60) (h60 ▸ hdiv))
      · exact h7' (dvd_trans (by norm_num : 7 ∣ 504) (h504 ▸ hdiv))

theorem pairViolation_outerRep {c : Nat} (hc : c < 4) :
    ∃ y : MulAut S4, PairViolation (outerRep c) y := by
  match c, hc with
  | 0, _ => exact pairViolation_of_checkPV outer_pv_check_0
  | 1, _ => exact pairViolation_of_checkPV outer_pv_check_1
  | 2, _ => exact pairViolation_of_checkPV outer_pv_check_2
  | 3, _ => exact pairViolation_of_checkPV outer_pv_check_3
  | c + 4, h => exact absurd h (by omega)

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
