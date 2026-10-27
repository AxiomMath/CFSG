module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitaryRoot

public section

namespace CFSG.StandardType

namespace IOneU52

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2 TableBUE
open IOneU

section Block

variable {K : Type} [Field K] [Finite K] {n d : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem blockSU_map_iso {S : Finset (Fin d)} (hS : S.card < d) :
    Nonempty (((blockSU (n := n) (K := K) S).map (LargeEvenProjMk (unitarySU 2 n K d))) ≃*
      ↥(unitarySU 2 n K S.card)) := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin d, i₀ ∉ S := by
    by_contra hcon
    push Not at hcon
    have : S = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ, Fintype.card_fin] at hS
    exact lt_irrefl _ hS
  set f : ↥(blockSU (n := n) (K := K) S) →* LargeEvenProj (unitarySU 2 n K d) :=
    π.comp (blockSU S).subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' : (z : ↥(unitarySU 2 n K d)) ∈ π.ker := hz
    rw [hπ, LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, largeEvenScalars_def,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz'
    obtain ⟨u, hu⟩ := hz'
    have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K)) hu) i₀) i₀
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h2
    have h3 := z.2 i₀ i₀ (Or.inl hi₀)
    have hu1 : (u : K) = 1 := by
      rw [h2]
      simpa using h3
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [← hu]
    have : u = 1 := Units.ext hu1
    rw [this]
    simp
  have hr : f.range = (blockSU S).map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hinj).symm).trans
    (blockSUEquiv S h).symm⟩

end Block

section Diag

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

include h in
theorem exists_rootEndNode_diag_five (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 5 ≤ d)
    {A : Subgroup ↥(unitarySU 2 n K d)} (hA : IsElemAbelian p A)
    (hdiag : ∀ x ∈ A, ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ)
    (hcard : p ^ (d - 2) ≤ Nat.card A) {s t : Fin d} (hst : s ≠ t)
    (hpair : ∀ σ ∈ diagVec A, σ s = σ t) :
    ∃ t₀, TableBOrth.IsEndNode (A.map (LargeEvenProjMk (unitarySU 2 n K d))) t₀ ∧
      Nonempty (↥(LargeEvenLayer
        (Subgroup.centralizer ({t₀} : Set (LargeEvenProj (unitarySU 2 n K d))))) ≃*
          ↥(unitarySU 2 n K (d - 1))) ∧
      ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t₀} : Set _)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        A.map (LargeEvenProjMk (unitarySU 2 n K d)) ≤ Subgroup.normalizer (U : Set _) := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hpK := dvd_card_sub_one hK hpq
  obtain ⟨c, hcs, hct⟩ : ∃ c : Fin d, c ≠ s ∧ c ≠ t := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin d)) ⊆ {s, t} := fun c _ => by
      by_cases hcs : c = s
      · simp [hcs]
      · simp [hcon c hcs]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ({s, t} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
    omega
  set W := diagVec A with hW
  have hWp : ∀ σ ∈ W, ∀ k, σ k ∈ rootsOfUnity p K := fun σ hσ k => by
    rw [mem_rootsOfUnity]
    exact (diagVec_props h hA hσ).1 k
  have hW1 : ∀ σ ∈ W, ∏ k, (σ k : K) = 1 := fun σ hσ => (diagVec_props h hA hσ).2
  have hWc : p ^ (d - 2) ≤ Nat.card W := by
    rw [hW, card_diagVec hdiag]
    exact hcard
  obtain ⟨σ, hσW, hσ1, hconst, hdist, hpow⟩ :=
    exists_node_of_pair hp hpK hpd hWp hW1 hst hcs.symm hct hpair hWc
  obtain ⟨x, hxA, hxσ⟩ := mem_diagVec.mp hσW
  set S : Finset (Fin d) := {c}ᶜ with hSdef
  have hmemS : ∀ i, i ∈ S ↔ i ≠ c := fun i => by simp [hSdef]
  have hSnode : IsNodeOn σ S := by
    refine ⟨fun i hi j hj => hconst i ((hmemS i).mp hi) j ((hmemS j).mp hj), fun i hi j hj => ?_⟩
    have hic : i = c := by
      by_contra hne
      exact hi ((hmemS i).mpr hne)
    rw [hic] at hj ⊢
    exact hdist j hj
  have hScard : S.card = d - 1 := by
    rw [hSdef, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  have hS3 : 3 ≤ S.card := by omega
  have hSq : (S.card, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : S.card = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    rcases hq with hq | hq <;> omega
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  have hker := ker_projMk_le_center (n := n) (d := d) (K := K)
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : diagHom d σ = 1 := by rw [← hxσ]; rfl
    exact diagHom_injective d (h1.trans (map_one _).symm)
  have hC := centralizer_map_eq_of_noTorsion π (QuotientGroup.mk'_surjective _) hker hnp
    (hA.2 x hxA)
  have hJq := isQuasisimple_blockSU S h hK hS3 hSq
  have hJC := blockSU_le_centralizer hSnode.1 hxσ
  have hcomm : ∀ g ∈ Subgroup.centralizer {x}, ∀ g' ∈ Subgroup.centralizer {x},
      g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := fun g hg g' hg' =>
    commutator_mem_blockSU hSnode hxσ hg hg'
  have hcent : ∀ y' ∈ A, (∀ j ∈ blockSU S, y' * j = j * y') ↔ y' ∈ Subgroup.zpowers x := by
    intro y' hy'
    obtain ⟨σ', hσ'⟩ := hdiag y' hy'
    rw [commute_blockSU_iff h hσ']
    constructor
    · intro hc
      have hmem := hpow σ' (mem_diagVec_of hy' hσ') fun i hi j hj =>
        hc i ((hmemS i).mpr hi) j ((hmemS j).mpr hj)
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
      rw [Subgroup.coe_zpow, hxσ, hσ', ← hm, map_zpow]
    · intro hmem i hi j hj
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hσm : σ' = σ ^ m := by
        apply diagHom_injective d
        rw [← hσ', map_zpow, ← hxσ, Subgroup.coe_zpow]
      rw [hσm, Pi.pow_apply, Pi.pow_apply, hSnode.1 i hi j hj]
  have hinj : ∀ y ∈ A, π y = 1 → y = 1 := fun y hy hy1 => hnp y hy1 (hA.2 y hy)
  have hend := isEndNode_map_of_cover π hker hinj hxA hx1 hJq hJC hcomm hC hcent
  have hJq' : CFSG.IsQuasisimple ((blockSU S).map π) := by
    have h1 := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_range hJq
      (π.comp (blockSU S).subtype) (by
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hz) y))
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  obtain ⟨hlayer, -⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem
    (H := Subgroup.centralizer {π x}) (D := (blockSU S).map π)
    (by rw [hC]; exact Subgroup.map_mono hJC)
    (by
      rw [hC]
      rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      refine ⟨g * g' * g⁻¹ * g'⁻¹, hcomm g hg g' hg', ?_⟩
      simp only [map_mul, map_inv])
    hJq'
  have hsS : s ∈ S := (hmemS s).mpr hcs.symm
  have htS : t ∈ S := (hmemS t).mpr hct.symm
  have hwS : swapSU h s t ∈ blockSU S := isBlockOn_permGL_swap hsS htS
  refine ⟨π x, hend, ?_, (Subgroup.zpowers (swapSU h s t)).map π, ?_, ?_,
    (isPGroup_two_zpowers (swapSU_sq h s t)).map π, ?_⟩
  · rw [hlayer, ← hScard]
    exact blockSU_map_iso h (by omega)
  · rw [hlayer]
    exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hwS)
  · intro hbot
    apply projMk_swapSU_ne_one h hst
    have h1 : π (swapSU h s t) ∈ (Subgroup.zpowers (swapSU h s t)).map π :=
      ⟨_, Subgroup.mem_zpowers _, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact h1
  · rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨y, hy, rfl⟩ _ ⟨u, hu, rfl⟩
    obtain ⟨σ', hσ'⟩ := hdiag y hy
    have hyw := commute_swapSU h hσ' (hpair σ' (mem_diagVec_of hy hσ'))
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine ⟨swapSU h s t ^ m, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    have hc : y * swapSU h s t ^ m * y⁻¹ = swapSU h s t ^ m := by
      rw [← (Commute.zpow_left hyw m).eq, mul_inv_cancel_right]
    rw [← map_inv, ← map_mul, ← map_mul, hc]

include h in
theorem exists_rootEndNode_unitary_five (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hd : 4 ≤ d) (hq : 2 < 2 ^ n ∨ 5 ≤ d)
    {Ab : Subgroup (LargeEvenProj (unitarySU 2 n K d))} (hAb : IsElemAbelian p Ab)
    (hr : p ^ (d - 2) ≤ Nat.card Ab)
    (hU : ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      Ab ≤ Subgroup.normalizer (U : Set _)) :
    ∃ t, TableBOrth.IsEndNode Ab t ∧
      Nonempty (↥(LargeEvenLayer
        (Subgroup.centralizer ({t} : Set (LargeEvenProj (unitarySU 2 n K d))))) ≃*
          ↥(unitarySU 2 n K (d - 1))) ∧
      ∃ U : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set _)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        Ab ≤ Subgroup.normalizer (U : Set _) := by
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_suScalars h hp hpd hz hzp
  obtain ⟨A, hmap, -, hA, hcardA⟩ :=
    exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective _) hp hnp hAb
  obtain ⟨P, hP, hdiag⟩ := exists_conj_diag h hp hpq hA
  set c := conjSU h P hP with hc
  set A' := A.map (c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)) with hA'
  have hA'ab : IsElemAbelian p A' := by
    have := isElemAbelian_range (H := A) (p := p)
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
      (fun a => Subtype.ext (by simpa using hA.2 a a.2))
      ((c : ↥(unitarySU 2 n K d) →* ↥(unitarySU 2 n K d)).comp A.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at this
  have hdiag' : ∀ x ∈ A', ∃ σ : Fin d → Kˣ, (x : GL (Fin d) K) = diagHom d σ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hdiag x hx
  have hcard' : Nat.card A' = Nat.card Ab := by
    rw [hA', ← hcardA]
    exact (Nat.card_congr (A.equivMapOfInjective _ c.injective).toEquiv).symm
  set cR := conjProj h P hP with hcR
  have hmap' : A'.map π = Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d)) := by
    rw [← hmap, hA', Subgroup.map_map, Subgroup.map_map]
    congr 1
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  set U' := U.map (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d))
    with hU'
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR u ∈ U' := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.injective (h1.trans (map_one cR).symm)
  have hBU' : A'.map π ≤ Subgroup.normalizer (U' : Set _) := by
    rw [hmap']
    exact (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map _)
  obtain ⟨s, t, hst, hpairF⟩ := SURepair.exists_framePair_of_twoSubgroup h
    (ker_projMk_le_center (n := n) (d := d) (K := K)) hU'1 (hU2.map _)
    (fun u _ => QuotientGroup.mk'_surjective _ u) hBU'
  have hpair : ∀ σ ∈ diagVec A', σ s = σ t := by
    intro σ hσ
    obtain ⟨x, hx, hxσ⟩ := mem_diagVec.mp hσ
    obtain ⟨hpow, -⟩ := diagVec_props h hA'ab hσ
    refine hpairF (π x) ⟨x, hx, rfl⟩ σ ⟨fun i => ?_, fun u u' hu' => ?_⟩
    · obtain ⟨k, hk⟩ := hpq
      rw [hk, pow_mul, ← Units.val_pow_eq_pow_val, hpow i, Units.val_one, one_pow]
    · have hu'' : u' = x * u * x⁻¹ := by
        apply Subtype.ext
        rw [hu', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxσ]
      rw [hu'', map_mul, map_mul, map_inv]
  obtain ⟨t₀, hend, hiso₀, U₀, hU₀J, hU₀1, hU₀2, hAU₀⟩ :=
    exists_rootEndNode_diag_five h hK hp hpq hpd hd hq
    hA'ab hdiag' (hcard' ▸ hr) hst hpair
  rw [hmap'] at hend hAU₀
  have hid : cR.symm.toMonoidHom.comp
      (cR : LargeEvenProj (unitarySU 2 n K d) →* LargeEvenProj (unitarySU 2 n K d)) =
        MonoidHom.id _ := by
    ext x
    simp
  have hAbeq : (Ab.map (cR : LargeEvenProj (unitarySU 2 n K d) →*
      LargeEvenProj (unitarySU 2 n K d))).map cR.symm.toMonoidHom = Ab := by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  have hend' := hend.map cR.symm
  rw [hAbeq] at hend'
  have hC : Subgroup.centralizer ({cR.symm t₀} : Set (LargeEvenProj (unitarySU 2 n K d))) =
      (Subgroup.centralizer ({t₀} : Set _)).map cR.symm.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton cR.symm t₀).symm
  have hL : LargeEvenLayer
      (Subgroup.centralizer ({cR.symm t₀} : Set (LargeEvenProj (unitarySU 2 n K d)))) =
      (LargeEvenLayer (Subgroup.centralizer ({t₀} : Set _))).map cR.symm.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective cR.symm.toMonoidHom cR.symm.injective]
  obtain ⟨e₀⟩ := hiso₀
  refine ⟨cR.symm t₀, hend', ?_, U₀.map cR.symm.toMonoidHom, ?_, ?_, hU₀2.map _, ?_⟩
  · exact ⟨(MulEquiv.subgroupCongr hL).trans
      (((LargeEvenLayer (Subgroup.centralizer ({t₀} : Set _))).equivMapOfInjective
        cR.symm.toMonoidHom cR.symm.injective).symm.trans e₀)⟩
  · rw [hL]
    exact Subgroup.map_mono hU₀J
  · intro hbot
    apply hU₀1
    rw [eq_bot_iff]
    intro u hu
    have h1 : cR.symm u ∈ U₀.map cR.symm.toMonoidHom := ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact cR.symm.injective (h1.trans (map_one cR.symm).symm)
  · rw [← hAbeq]
    exact (Subgroup.map_mono hAU₀).trans (Subgroup.le_normalizer_map _)

end Diag

theorem isU42_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : LargeEvenIsU42 Y) : LargeEvenIsU42 X := by
  obtain ⟨F, i1, i2, hF, ⟨e'⟩⟩ := hY
  exact ⟨F, i1, i2, hF, ⟨e.trans e'⟩⟩

theorem unitarySU_four_isU42 {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    LargeEvenIsU42 ↥(unitarySU 2 1 K 4) := by
  have h4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hcube : ∀ u : Kˣ, u ^ 3 = 1 := by
    intro u
    haveI : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact h4
    apply Units.ext
    have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rw [hc] at h
    simpa using h
  have hpd : ¬ 3 ∣ 4 := by norm_num
  have hz3 : ∀ z ∈ (LargeEvenProjMk (unitarySU 2 1 K 4)).ker, z ^ 3 = 1 := by
    intro z hz
    rw [LargeEvenProjMk, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf,
      largeEvenScalars_def] at hz
    obtain ⟨u, hu⟩ := hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu, ← map_pow, hcube u, map_one]
    rfl
  have hbij : Function.Bijective (LargeEvenProjMk (unitarySU 2 1 K 4)) := by
    refine ⟨?_, QuotientGroup.mk_surjective⟩
    rw [injective_iff_map_eq_one]
    intro z hz
    exact eq_one_of_mem_suScalars (TableBU.unitaryFieldData_of_card hK le_rfl) Nat.prime_three
      hpd hz (hz3 z hz)
  exact ⟨K, inferInstance, inferInstance, h4, ⟨MulEquiv.ofBijective _ hbij⟩⟩

theorem exists_rootEndNode_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    {Ab : Subgroup (UnitaryR K 1 5)} (hAb : IsElemAbelian 3 Ab)
    (hr : 3 ^ (5 - 2) ≤ Nat.card Ab)
    (hU : ∃ U : Subgroup (UnitaryR K 1 5), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      Ab ≤ Subgroup.normalizer (U : Set _)) :
    ∃ t, TableBOrth.IsEndNode Ab t ∧
      LargeEvenSmall (LargeEvenLayer
        (Subgroup.centralizer ({t} : Set (UnitaryR K 1 5)))) ∧
      ∃ U : Subgroup (UnitaryR K 1 5),
        U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set _)) ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
        Ab ≤ Subgroup.normalizer (U : Set _) := by
  obtain ⟨t, hend, ⟨e⟩, U, hUL, hU1, hU2, hAU⟩ := exists_rootEndNode_unitary_five
    (n := 1) (d := 5) (p := 3) (TableBU.unitaryFieldData_of_card hK le_rfl) hK Nat.prime_three
    (by norm_num)
    (by norm_num) (by norm_num) (Or.inr (by norm_num)) hAb hr hU
  exact ⟨t, hend, Or.inl (isU42_of_mulEquiv e (unitarySU_four_isU42 hK)), U, hUL, hU1, hU2, hAU⟩

end IOneU52

end CFSG.StandardType
