module

public import CFSG.Monster.B.Geometry.InitialIsometryF4
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

local notation "cs4" => coxeterSystem Tag.F4

variable {C : Type*} {δ : C → C → WeylGroup .F4} {C' : Type*} {δ' : C' → C' → WeylGroup .F4}

theorem unitTypes_inter_orthTypes : unitTypes ∩ orthTypes = ({1, 2} : Set (Fin Tag.F4.rank)) := by
  ext j
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide

theorem subset_orthTypes_cases {J : Set (Fin Tag.F4.rank)} (hJ : J ⊆ orthTypes)
    (hJ2 : J.encard ≤ 2) : J ⊆ {0, 1} ∨ J ⊆ {1, 2} ∨ J = insert 2 {0} := by
  by_cases h0 : (0 : Fin Tag.F4.rank) ∈ J
  · by_cases h2 : (2 : Fin Tag.F4.rank) ∈ J
    · right; right
      have h1 : (1 : Fin Tag.F4.rank) ∉ J := by
        intro h1
        have hsub : ({0, 1, 2} : Set (Fin Tag.F4.rank)) ⊆ J := by
          intro j hj
          rcases hj with rfl | rfl | hj
          · exact h0
          · exact h1
          · rw [Set.mem_singleton_iff.mp hj]; exact h2
        have := (Set.encard_le_encard hsub).trans hJ2
        rw [Set.encard_insert_of_notMem (by decide), Set.encard_pair (by decide)] at this
        norm_num at this
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hj
        have := hJ hj
        rcases fin_f4_cases j with rfl | rfl | rfl | rfl
        · exact Or.inr rfl
        · exact absurd hj h1
        · exact Or.inl rfl
        · exact absurd this (by decide)
      · rintro (rfl | rfl)
        · exact h2
        · exact h0
    · left
      intro j hj
      have := hJ hj
      rcases fin_f4_cases j with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hj h2
      · exact absurd this (by decide)
  · right; left
    intro j hj
    have := hJ hj
    rcases fin_f4_cases j with rfl | rfl | rfl | rfl
    · exact absurd hj h0
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd this (by decide)

theorem subset_types_cases {J : Set (Fin Tag.F4.rank)} (hJ2 : J.encard ≤ 2) :
    J ⊆ unitTypes ∨ J ⊆ orthTypes ∨ J = insert 3 {0} := by
  by_cases h0 : (0 : Fin Tag.F4.rank) ∈ J
  · by_cases h3 : (3 : Fin Tag.F4.rank) ∈ J
    · right; right
      have hother : ∀ j ∈ J, j = 0 ∨ j = 3 := by
        intro j hj
        by_contra hne
        push Not at hne
        have hsub : ({0, 3, j} : Set (Fin Tag.F4.rank)) ⊆ J := by
          intro k hk
          rcases hk with rfl | rfl | hk
          · exact h0
          · exact h3
          · rw [Set.mem_singleton_iff.mp hk]; exact hj
        have := (Set.encard_le_encard hsub).trans hJ2
        rw [Set.encard_insert_of_notMem (by simp [Ne.symm hne.1]),
          Set.encard_pair (Ne.symm hne.2)] at this
        norm_num at this
      ext j
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hj
        rcases hother j hj with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (rfl | rfl)
        · exact h3
        · exact h0
    · right; left
      intro j hj (e : j = 3)
      exact h3 (e ▸ hj)
  · left
    intro j hj (e : j = 0)
    exact h0 (e ▸ hj)

theorem not_mem_residue_of_opposite (hδ : IsWeylDistanceBuilding cs4 δ) {c d : C}
    (hcd : δ c d = longest cs4 Set.univ) {K : Set (Fin Tag.F4.rank)} {k : Fin Tag.F4.rank}
    (hk : k ∉ K) : d ∉ residue cs4 δ K c := fun h => by
  have hmem := (mem_residue_iff_mem_parabolic hδ).mp h
  rw [hcd] at hmem
  exact hk (subset_of_longest_mem_parabolic isLongest_univ hmem (Set.mem_univ k))

theorem resProj_not_mem_residue (hδ : IsWeylDistanceBuilding cs4 δ) {c d : C}
    (hcd : δ c d = longest cs4 Set.univ) {J K : Set (Fin Tag.F4.rank)} {k : Fin Tag.F4.rank}
    (hkJ : k ∈ J) (hk : k ∉ K) : resProj cs4 δ J c d ∉ residue cs4 δ K c := fun h => by
  have hmem := (mem_residue_iff_mem_parabolic hδ).mp h
  rw [(dist_resProj_of_opposite hδ hcd J).1] at hmem
  exact hk (subset_of_longest_mem_parabolic (isLongest_of_finite J) hmem hkJ)

theorem exists_correction (hδ : IsWeylDistanceBuilding cs4 δ)
    (hδ' : IsWeylDistanceBuilding cs4 δ') (hM' : HasClassicalEnds δ')
    (hP' : ∀ x : C', (panel cs4 δ' 1 x).encard ≤ 3) {c d : C} {c' d' : C'}
    (hcd' : δ' c' d' = longest cs4 Set.univ) {a b : C → C'}
    (ha : IsTypeIso cs4 δ δ' (residue cs4 δ unitTypes c) (residue cs4 δ' unitTypes c') a)
    (hac : a c = c') (hap : a (resProj cs4 δ unitTypes c d) = resProj cs4 δ' unitTypes c' d')
    (hb : IsTypeIso cs4 δ δ' (residue cs4 δ orthTypes c) (residue cs4 δ' orthTypes c') b)
    (hbc : b c = c') (hbp : b (resProj cs4 δ orthTypes c d) = resProj cs4 δ' orthTypes c' d') :
    ∃ b' : C → C',
      IsTypeIso cs4 δ δ' (residue cs4 δ orthTypes c) (residue cs4 δ' orthTypes c') b' ∧
      b' c = c' ∧ b' (resProj cs4 δ orthTypes c d) = resProj cs4 δ' orthTypes c' d' ∧
      ∀ x ∈ residue cs4 δ {1, 2} c, b' x = a x := by
  classical
  have hCU : ({1, 2} : Set (Fin Tag.F4.rank)) ⊆ unitTypes := by
    rintro j (rfl | rfl | _) <;> decide
  have hCO : ({1, 2} : Set (Fin Tag.F4.rank)) ⊆ orthTypes := by
    rintro j (rfl | rfl | _) <;> decide
  set RC := residue cs4 δ {1, 2} c
  set RC' := residue cs4 δ' {1, 2} c'
  obtain ⟨haC, haCd⟩ := isometry_residue_of_subset hδ hδ' hCU ha hac
  obtain ⟨hbC, hbCd⟩ := isometry_residue_of_subset hδ hδ' hCO hb hbc
  set pC := resProj cs4 δ {1, 2} c d
  set pC' := resProj cs4 δ' {1, 2} c' d'
  have hapC : a pC = pC' := map_resProj_of_subset hδ hδ' hCU ha hac hap
  have hbpC : b pC = pC' := map_resProj_of_subset hδ hδ' hCO hb hbc hbp
  have : Nonempty C := ⟨c⟩
  set binv := Function.invFunOn b RC
  have hinv : Set.InvOn binv b RC RC' := hbC.invOn_invFunOn
  have hbinv : Set.BijOn binv RC' RC := hbC.symm hinv.symm
  set τ : C' → C' := fun y => a (binv y) with hτdef
  have hτb : ∀ x ∈ RC, τ (b x) = a x := fun x hx => by
    simp only [hτdef]
    rw [hinv.1 hx]
  have hτC : Set.BijOn τ RC' RC' := haC.comp hbinv
  have hτd : ∀ y ∈ RC', ∀ y' ∈ RC', δ' (τ y) (τ y') = δ' y y' := by
    intro y hy y' hy'
    obtain ⟨x, hx, rfl⟩ := hbC.surjOn hy
    obtain ⟨x', hx', rfl⟩ := hbC.surjOn hy'
    rw [hτb x hx, hτb x' hx', haCd x hx x' hx', hbCd x hx x' hx']
  have hτiso : IsWeylIsometry δ' δ' RC' RC' τ := ⟨hτC, hτd⟩
  have hτc : τ c' = c' :=
    calc τ c' = τ (b c) := by rw [hbc]
      _ = a c := hτb c (self_mem_residue _ c)
      _ = c' := hac
  have hτp : τ pC' = pC' :=
    calc τ pC' = τ (b pC) := by rw [hbpC]
      _ = a pC := hτb pC (resProj_mem hδ _ c d)
      _ = pC' := hapC
  have hτsub : ∀ {K : Set (Fin Tag.F4.rank)}, K ⊆ {1, 2} →
      Set.BijOn τ (residue cs4 δ' K c') (residue cs4 δ' K c') := fun hK =>
    hτiso.bijOn_residue hδ' hδ' (self_mem_residue _ c') hτc (residue_mono hK c')
      (residue_mono hK c')
  have hτfix : ∀ {K : Set (Fin Tag.F4.rank)}, K ⊆ {1, 2} →
      τ (resProj cs4 δ' K c' d') = resProj cs4 δ' K c' d' := by
    intro K hK
    have e : resProj cs4 δ' K c' pC' = resProj cs4 δ' K c' d' := resProj_resProj hδ' hK c' d'
    have h := resProj_map hδ' hδ' (y := pC') (hτsub hK) fun q hq =>
      hτd pC' (resProj_mem hδ' _ c' d') q (residue_mono hK c' hq)
    rw [hτp, e] at h
    exact h.symm
  have hτP : ∀ y ∈ panel cs4 δ' 1 c', τ y = y := by
    intro y hy
    set q := resProj cs4 δ' {1} c' d'
    have hq : q ∈ panel cs4 δ' 1 c' := resProj_mem hδ' _ c' d'
    have hcq : δ' c' q = (coxeterSystem .F4).simple 1 := by
      rw [(dist_resProj_of_opposite hδ' hcd' {1}).1, longest_singleton]
    have hne : c' ≠ q := hδ'.ne_of_eq_simple hcq
    have h1 : ({1} : Set (Fin Tag.F4.rank)) ⊆ {1, 2} := by simp
    have hτq : τ q = q := hτfix h1
    have hP := hτsub h1
    by_contra hy'
    have hyc : y ≠ c' := fun e => hy' (by rw [e, hτc])
    have hyq : y ≠ q := fun e => hy' (by rw [e, hτq])
    have hτyc : τ y ≠ c' := fun e => hyc (hP.injOn hy (self_mem_residue _ c') (e.trans hτc.symm))
    have hτyq : τ y ≠ q := fun e => hyq (hP.injOn hy hq (e.trans hτq.symm))
    have hsub : ({c', q, y, τ y} : Set C') ⊆ panel cs4 δ' 1 c' := by
      intro w hw
      rcases hw with rfl | rfl | rfl | hw
      · exact self_mem_residue _ _
      · exact hq
      · exact hy
      · rw [Set.mem_singleton_iff.mp hw]; exact hP.mapsTo hy
    have h4 := (Set.encard_le_encard hsub).trans (hP' c')
    rw [Set.encard_insert_of_notMem (by simp [hne, Ne.symm hyc, Ne.symm hτyc]),
      Set.encard_insert_of_notMem (by simp [Ne.symm hyq, Ne.symm hτyq]),
      Set.encard_pair (Ne.symm hy')] at h4
    norm_num at h4
  have hz : (2 : Fin Tag.F4.rank) ∉ ({0} : Set (Fin Tag.F4.rank)) := by decide
  have hcomm : ∀ i ∈ ({0} : Set (Fin Tag.F4.rank)),
      CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) i 2 = 2 := by
    intro i hi
    rw [Set.mem_singleton_iff.mp hi]
    exact f4_M02
  have hF₂ : Set.BijOn τ (panel cs4 δ' 2 c') (panel cs4 δ' 2 c') := hτsub (by simp)
  have hprod := isTypeIso_prodMap hδ' hδ' hz hcomm (Set.bijOn_id _) hF₂ fun _ _ _ _ => rfl
  set P := prodMap cs4 δ' δ' {0} 2 c' c' id τ
  set Ψ : C' → C' := fun y =>
    if y ∈ RC' then τ y else if y ∈ residue cs4 δ' {0, 1} c' then y
      else if y ∈ residue cs4 δ' (insert 2 {0}) c' then P y else y with hΨdef
  have hΨC : ∀ y ∈ RC', Ψ y = τ y := fun y hy => by simp only [hΨdef, ite_eq_left hy]
  have hΨA : ∀ y ∈ residue cs4 δ' {0, 1} c', Ψ y = y := by
    intro y hy
    by_cases hyC : y ∈ RC'
    · rw [hΨC y hyC]
      have hy1 : y ∈ panel cs4 δ' 1 c' := by
        have : y ∈ residue cs4 δ' ({0, 1} ∩ {1, 2}) c' := by
          rw [← residue_inter hδ']
          exact ⟨hy, hyC⟩
        have e : ({0, 1} ∩ {1, 2} : Set (Fin Tag.F4.rank)) = {1} := by
          ext j
          simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
        rwa [e] at this
      exact hτP y hy1
    · simp only [hΨdef, ite_eq_right hyC, ite_eq_left hy]
  have hΨB : ∀ y ∈ residue cs4 δ' (insert 2 {0}) c', Ψ y = P y := by
    intro y hy
    by_cases hyC : y ∈ RC'
    · rw [hΨC y hyC]
      have hy2 : y ∈ panel cs4 δ' 2 c' := by
        have : y ∈ residue cs4 δ' (insert 2 {0} ∩ {1, 2}) c' := by
          rw [← residue_inter hδ']
          exact ⟨hy, hyC⟩
        have e : (insert 2 {0} ∩ {1, 2} : Set (Fin Tag.F4.rank)) = {2} := by
          ext j
          simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
        rwa [e] at this
      exact (prodMap_eq_snd hδ' hδ' hz hcomm (Set.bijOn_id _) hF₂ rfl hy2).symm
    · by_cases hyA : y ∈ residue cs4 δ' {0, 1} c'
      · rw [hΨA y hyA]
        have hy0 : y ∈ residue cs4 δ' {0} c' := by
          have : y ∈ residue cs4 δ' (insert 2 {0} ∩ {0, 1}) c' := by
            rw [← residue_inter hδ']
            exact ⟨hy, hyA⟩
          have e : (insert 2 {0} ∩ {0, 1} : Set (Fin Tag.F4.rank)) = {0} := by
            ext j
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
          rwa [e] at this
        exact (prodMap_eq_fst hδ' hδ' hz hcomm (Set.bijOn_id _) hF₂ hτc hy0).symm
      · simp only [hΨdef, ite_eq_right hyC, ite_eq_right hyA, ite_eq_left hy]
  set pO' := resProj cs4 δ' orthTypes c' d'
  have hpO' : pO' ∈ residue cs4 δ' orthTypes c' := resProj_mem hδ' _ c' d'
  have hΨp : Ψ pO' = pO' := by
    have h1 : pO' ∉ RC' := resProj_not_mem_residue hδ' hcd' (k := 0) (by decide) (by decide)
    have h2 : pO' ∉ residue cs4 δ' {0, 1} c' :=
      resProj_not_mem_residue hδ' hcd' (k := 2) (by decide) (by decide)
    have h3 : pO' ∉ residue cs4 δ' (insert 2 {0}) c' :=
      resProj_not_mem_residue hδ' hcd' (k := 1) (by decide) (by decide)
    simp only [hΨdef, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  have hΨres : ∀ J : Set (Fin Tag.F4.rank), J ⊆ orthTypes → J.encard ≤ 2 →
      Set.BijOn Ψ (residue cs4 δ' J c') (residue cs4 δ' J c') ∧
        ∀ x ∈ residue cs4 δ' J c', ∀ y ∈ residue cs4 δ' J c', δ' (Ψ x) (Ψ y) = δ' x y := by
    intro J hJ hJ2
    rcases subset_orthTypes_cases hJ hJ2 with hA | hC | rfl
    · have hEq : Set.EqOn id Ψ (residue cs4 δ' J c') := fun y hy =>
        (hΨA y (residue_mono hA c' hy)).symm
      refine ⟨(Set.bijOn_id _).congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      rfl
    · have hEq : Set.EqOn τ Ψ (residue cs4 δ' J c') := fun y hy =>
        (hΨC y (residue_mono hC c' hy)).symm
      refine ⟨(hτsub hC).congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact hτd x (residue_mono hC c' hx) y (residue_mono hC c' hy)
    · have hEq : Set.EqOn P Ψ (residue cs4 δ' (insert 2 {0}) c') := fun y hy => (hΨB y hy).symm
      refine ⟨hprod.1.congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact hprod.dist_eq hδ' hδ' hx hy
  have hΨproj : ∀ J : Set (Fin Tag.F4.rank), J ⊆ orthTypes → J.encard ≤ 2 →
      Ψ (resProj cs4 δ' J c' pO') = resProj cs4 δ' J c' pO' := by
    intro J hJ hJ2
    rw [resProj_resProj hδ' hJ c' d']
    rcases subset_orthTypes_cases hJ hJ2 with hA | hC | rfl
    · exact hΨA _ (residue_mono hA c' (resProj_mem hδ' J c' d'))
    · rw [hΨC _ (residue_mono hC c' (resProj_mem hδ' J c' d'))]
      exact hτfix hC
    · rw [hΨB _ (resProj_mem hδ' _ c' d')]
      have h2 : resProj cs4 δ' {2} c' (resProj cs4 δ' (insert 2 {0}) c' d') =
          τ (resProj cs4 δ' {2} c' (resProj cs4 δ' (insert 2 {0}) c' d')) := by
        rw [resProj_resProj hδ' (by simp) c' d']
        exact (hτfix (by simp)).symm
      exact (eq_prodMap hδ' hδ' hz hcomm (Set.bijOn_id _) hF₂ (resProj_mem hδ' _ c' d') rfl
        h2).symm
  have hΨiso := isWeylIsometry_residueFoundation_glue hδ' hδ' orthTypes (c := c') (d := pO')
    (c' := c') (d' := pO') (f := Ψ) (fun J hJ hJ2 => (hΨres J hJ hJ2).1)
    (fun J hJ hJ2 => (hΨres J hJ hJ2).2) hΨp (fun J hJ hJ2 => by rw [hΨproj J hJ hJ2])
  have hΨc : Ψ c' = c' := (hΨC c' (self_mem_residue _ c')).trans hτc
  have hopp' := (dist_resProj_of_opposite hδ' hcd' orthTypes).1
  obtain ⟨⟨G, hG, -, hGΨ⟩, -⟩ := ext₃At_orthTypes hδ' hδ' hM' hM' c' pO' c' pO' hpO' hpO'
    hopp' hopp' Ψ hΨiso hΨc hΨp
  have hCF : RC' ⊆ residueFoundation cs4 δ' orthTypes c' :=
    residue_subset_residueFoundation hCO (encard_pair_le_two 1 2) c'
  refine ⟨G ∘ b, hb.trans hG, ?_, ?_, fun x hx => ?_⟩
  · change G (b c) = c'
    rw [hbc, hGΨ (Or.inl (self_mem_residueFoundation _ c')), hΨc]
  · change G (b (resProj cs4 δ orthTypes c d)) = pO'
    rw [hbp, hGΨ (Or.inr rfl), hΨp]
  · change G (b x) = a x
    rw [hGΨ (Or.inl (hCF (hbC.mapsTo hx))), hΨC _ (hbC.mapsTo hx), hτb x hx]

theorem exists_initial_isometry_of_hasClassicalEnds (hδ : IsWeylDistanceBuilding cs4 δ)
    (hδ' : IsWeylDistanceBuilding cs4 δ') (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ')
    (hP' : ∀ x : C', (panel cs4 δ' 1 x).encard ≤ 3) {c d : C} {c' d' : C'}
    (hcd : δ c d = longest cs4 Set.univ) (hcd' : δ' c' d' = longest cs4 Set.univ) :
    ∃ φ : C → C', IsWeylIsometry δ δ' (foundation cs4 δ 2 c ∪ {d})
      (foundation cs4 δ' 2 c' ∪ {d'}) φ ∧ φ c = c' ∧ φ d = d' := by
  classical
  obtain ⟨a, ha, hac, hap⟩ := exists_unit_iso hδ hδ' hM hM' hcd hcd'
  obtain ⟨b, hb, hbc, hbp⟩ := exists_orth_iso hδ hδ' hM hM' hcd hcd'
  obtain ⟨b', hb', hb'c, hb'p, hab'⟩ := exists_correction hδ hδ' hM' hP' hcd' ha hac hap hb hbc hbp
  have hz : (3 : Fin Tag.F4.rank) ∉ ({0} : Set (Fin Tag.F4.rank)) := by decide
  have hcomm : ∀ i ∈ ({0} : Set (Fin Tag.F4.rank)),
      CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) i 3 = 2 := by
    intro i hi
    rw [Set.mem_singleton_iff.mp hi, f4_M]
    rfl
  have h0O : ({0} : Set (Fin Tag.F4.rank)) ⊆ orthTypes := by simp
  have h3U : ({3} : Set (Fin Tag.F4.rank)) ⊆ unitTypes := by simp
  obtain ⟨hF₁, hd₁⟩ := isometry_residue_of_subset hδ hδ' h0O hb' hb'c
  obtain ⟨hF₂, -⟩ := isometry_residue_of_subset hδ hδ' h3U ha hac
  have hprod := isTypeIso_prodMap hδ hδ' hz hcomm hF₁ hF₂ hd₁
  set P := prodMap cs4 δ δ' {0} 3 c c' b' a
  set φ : C → C' := fun x =>
    if x ∈ residue cs4 δ unitTypes c then a x else if x ∈ residue cs4 δ orthTypes c then b' x
      else if x ∈ residue cs4 δ (insert 3 {0}) c then P x else d' with hφdef
  have hφU : ∀ x ∈ residue cs4 δ unitTypes c, φ x = a x := fun x hx => by
    simp only [hφdef, ite_eq_left hx]
  have hφO : ∀ x ∈ residue cs4 δ orthTypes c, φ x = b' x := by
    intro x hx
    by_cases hxU : x ∈ residue cs4 δ unitTypes c
    · rw [hφU x hxU]
      have : x ∈ residue cs4 δ (unitTypes ∩ orthTypes) c := by
        rw [← residue_inter hδ]
        exact ⟨hxU, hx⟩
      rw [unitTypes_inter_orthTypes] at this
      exact (hab' x this).symm
    · simp only [hφdef, ite_eq_right hxU, ite_eq_left hx]
  have hφZ : ∀ x ∈ residue cs4 δ (insert 3 {0}) c, φ x = P x := by
    intro x hx
    by_cases hxU : x ∈ residue cs4 δ unitTypes c
    · rw [hφU x hxU]
      have hx3 : x ∈ panel cs4 δ 3 c := by
        have : x ∈ residue cs4 δ (insert 3 {0} ∩ unitTypes) c := by
          rw [← residue_inter hδ]
          exact ⟨hx, hxU⟩
        have e : (insert 3 {0} ∩ unitTypes : Set (Fin Tag.F4.rank)) = {3} := by
          ext j
          simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
            Set.mem_ofPred_eq]
          rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
        rwa [e] at this
      exact (prodMap_eq_snd hδ hδ' hz hcomm hF₁ hF₂ hb'c hx3).symm
    · by_cases hxO : x ∈ residue cs4 δ orthTypes c
      · rw [hφO x hxO]
        have hx0 : x ∈ residue cs4 δ {0} c := by
          have : x ∈ residue cs4 δ (insert 3 {0} ∩ orthTypes) c := by
            rw [← residue_inter hδ]
            exact ⟨hx, hxO⟩
          have e : (insert 3 {0} ∩ orthTypes : Set (Fin Tag.F4.rank)) = {0} := by
            ext j
            simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
              Set.mem_ofPred_eq]
            rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
          rwa [e] at this
        exact (prodMap_eq_fst hδ hδ' hz hcomm hF₁ hF₂ hac hx0).symm
      · simp only [hφdef, ite_eq_right hxU, ite_eq_right hxO, ite_eq_left hx]
  have hres : ∀ J : Set (Fin Tag.F4.rank), J.encard ≤ 2 →
      Set.BijOn φ (residue cs4 δ J c) (residue cs4 δ' J c') ∧
        ∀ x ∈ residue cs4 δ J c, ∀ y ∈ residue cs4 δ J c, δ' (φ x) (φ y) = δ x y := by
    intro J hJ
    rcases subset_types_cases hJ with hU | hO | rfl
    · obtain ⟨h1, h2⟩ := isometry_residue_of_subset hδ hδ' hU ha hac
      have hEq : Set.EqOn a φ (residue cs4 δ J c) := fun x hx =>
        (hφU x (residue_mono hU c hx)).symm
      refine ⟨h1.congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact h2 x hx y hy
    · obtain ⟨h1, h2⟩ := isometry_residue_of_subset hδ hδ' hO hb' hb'c
      have hEq : Set.EqOn b' φ (residue cs4 δ J c) := fun x hx =>
        (hφO x (residue_mono hO c hx)).symm
      refine ⟨h1.congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact h2 x hx y hy
    · have hEq : Set.EqOn P φ (residue cs4 δ (insert 3 {0}) c) := fun x hx => (hφZ x hx).symm
      refine ⟨hprod.1.congr hEq, fun x hx y hy => ?_⟩
      rw [← hEq hx, ← hEq hy]
      exact hprod.dist_eq hδ hδ' hx hy
  have hproj : ∀ J : Set (Fin Tag.F4.rank), J.encard ≤ 2 →
      φ (resProj cs4 δ J c d) = resProj cs4 δ' J c' d' := by
    intro J hJ
    rcases subset_types_cases hJ with hU | hO | rfl
    · rw [hφU _ (residue_mono hU c (resProj_mem hδ J c d))]
      exact map_resProj_of_subset hδ hδ' hU ha hac hap
    · rw [hφO _ (residue_mono hO c (resProj_mem hδ J c d))]
      exact map_resProj_of_subset hδ hδ' hO hb' hb'c hb'p
    · rw [hφZ _ (resProj_mem hδ _ c d)]
      refine (eq_prodMap hδ hδ' hz hcomm hF₁ hF₂ (resProj_mem hδ' _ c' d') ?_ ?_).symm
      · rw [resProj_resProj hδ' (by simp) c' d', resProj_resProj hδ (by simp) c d]
        exact (map_resProj_of_subset hδ hδ' h0O hb' hb'c hb'p).symm
      · rw [resProj_resProj hδ' (by simp) c' d', resProj_resProj hδ (by simp) c d]
        exact (map_resProj_of_subset hδ hδ' h3U ha hac hap).symm
  have hφd : φ d = d' := by
    have h1 : d ∉ residue cs4 δ unitTypes c := not_mem_residue_of_opposite hδ hcd (k := 0)
      (by decide)
    have h2 : d ∉ residue cs4 δ orthTypes c := not_mem_residue_of_opposite hδ hcd (k := 3)
      (by decide)
    have h3 : d ∉ residue cs4 δ (insert 3 {0}) c := not_mem_residue_of_opposite hδ hcd (k := 1)
      (by decide)
    simp only [hφdef, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
  refine ⟨φ, isWeylIsometry_foundation_glue hδ hδ' (fun J hJ => (hres J hJ).1)
    (fun J hJ => (hres J hJ).2) hφd fun J hJ => ?_, (hφU c (self_mem_residue _ c)).trans hac,
    hφd⟩
  rw [hproj J hJ, (dist_resProj_of_opposite hδ hcd J).2, (dist_resProj_of_opposite hδ' hcd' J).2]

theorem building_iso_of_hasClassicalEnds (hδ : IsWeylDistanceBuilding cs4 δ)
    (hδ' : IsWeylDistanceBuilding cs4 δ') (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ')
    (hP' : ∀ x : C', (panel cs4 δ' 1 x).encard ≤ 3) :
    (∃ F : C → C', IsTypeIso cs4 δ δ' Set.univ Set.univ F ∧
      IsWeylIsometry δ δ' Set.univ Set.univ F) ∧
    ∀ (c d : C) (c' d' : C'), δ c d = longest cs4 Set.univ →
      δ' c' d' = longest cs4 Set.univ → ∀ φ : C → C',
        IsWeylIsometry δ δ' (foundation cs4 δ 2 c ∪ {d}) (foundation cs4 δ' 2 c' ∪ {d'}) φ →
          φ c = c' → φ d = d' →
            ∃! F : C → C', (IsTypeIso cs4 δ δ' Set.univ Set.univ F ∧
              IsWeylIsometry δ δ' Set.univ Set.univ F) ∧
              Set.EqOn F φ (foundation cs4 δ 2 c ∪ {d}) := by
  have hext := ext₃_of_hasClassicalEnds hδ hδ' hM hM'
  have hrig := rig₂_of_hasClassicalEnds hδ hM
  have hrig' := rig₂_of_hasClassicalEnds hδ' hM'
  have key : ∀ (c d : C) (c' d' : C'), δ c d = longest cs4 Set.univ →
      δ' c' d' = longest cs4 Set.univ → ∀ φ : C → C',
        IsWeylIsometry δ δ' (foundation cs4 δ 2 c ∪ {d}) (foundation cs4 δ' 2 c' ∪ {d'}) φ →
          φ c = c' → φ d = d' →
            ∃! F : C → C', (IsTypeIso cs4 δ δ' Set.univ Set.univ F ∧
              IsWeylIsometry δ δ' Set.univ Set.univ F) ∧
              Set.EqOn F φ (foundation cs4 δ 2 c ∪ {d}) := by
    intro c d c' d' hcd hcd' φ hφ hφc hφd
    obtain ⟨F, hF, hFφ, huniq⟩ := F4_global_extension_from_rank_three_opposition hδ hδ' hext
      hrig hrig' hcd hcd' hφ hφc hφd
    refine ⟨F, ⟨⟨hF, hF.1, fun x _ y _ => IsTypeIso.dist_eq_univ hδ hδ' hF x y⟩, hFφ⟩,
      fun F' hF' => huniq F' hF'.1.1 hF'.2⟩
  refine ⟨?_, key⟩
  obtain ⟨c⟩ := hδ.nonempty
  obtain ⟨c'⟩ := hδ'.nonempty
  obtain ⟨d, hcd⟩ := exists_dist hδ c (longest cs4 Set.univ)
  obtain ⟨d', hcd'⟩ := exists_dist hδ' c' (longest cs4 Set.univ)
  obtain ⟨φ, hφ, hφc, hφd⟩ := exists_initial_isometry_of_hasClassicalEnds hδ hδ' hM hM' hP'
    hcd hcd'
  obtain ⟨F, ⟨hF, -⟩, -⟩ := key c d c' d' hcd hcd' φ hφ hφc hφd
  exact ⟨F, hF⟩

end CFSG.Monster.B.Geometry
