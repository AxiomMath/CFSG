module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaData
import CFSG.RankThree.GF2n.Tim81.Sec6.S61Tools
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {n f : ℕ}

theorem Hyp.sigmaAt_conj (h : Hyp M V) (a : G) :
    sigmaAt (conjSubgroup a V) = sigmaSet (conjSubgroup a M) (conjSubgroup a V) := by
  unfold sigmaAt
  rw [normalizer_conjSubgroup a V, h.normalizer_eq]

theorem sigmaSet_subset_omegaSet (M V : Subgroup G) : sigmaSet M V ⊆ omegaSet V := by
  rintro U ⟨g, rfl, -⟩
  exact ⟨g, Subgroup.mem_top g, rfl⟩

theorem sigmaAt_subset_omegaSet {X : Subgroup G} (hX : X ∈ omegaSet V) :
    sigmaAt X ⊆ omegaSet V := by
  rintro U ⟨g, rfl, -⟩
  obtain ⟨x, -, rfl⟩ := hX
  exact ⟨g * x, Subgroup.mem_top _, by rw [conjSubgroup_conjSubgroup]⟩

theorem Hyp.mem_sigmaAt_conj_iff (h : Hyp M V) {X : Subgroup G} (hX : X ∈ omegaSet V) (a : G)
    {U : Subgroup G} : U ∈ sigmaAt (conjSubgroup a X) ↔ conjSubgroup a⁻¹ U ∈ sigmaAt X := by
  obtain ⟨b, -, rfl⟩ := hX
  rw [conjSubgroup_conjSubgroup, Hyp.mem_sigmaAt_conjSubgroup_iff h (a * b),
    Hyp.mem_sigmaAt_conjSubgroup_iff h b]
  simp only [conjSubgroup_conjSubgroup, mul_inv_rev]

theorem Hyp.mem_gammaAt_conj_iff (h : Hyp M V) {X : Subgroup G} (hX : X ∈ omegaSet V) (a : G)
    {B : Subgroup G} : B ∈ gammaAt (conjSubgroup a X) ↔ conjSubgroup a⁻¹ B ∈ gammaAt X := by
  constructor
  · rintro ⟨C, hC, hBC⟩
    have hC' : conjSubgroup a⁻¹ C ∈ sigmaAt X :=
      (Hyp.mem_sigmaAt_conj_iff h hX a).mp hC
    have hCω : conjSubgroup a⁻¹ C ∈ omegaSet V := sigmaAt_subset_omegaSet hX hC'
    refine ⟨conjSubgroup a⁻¹ C, hC', ?_⟩
    have hBC' : B ∈ sigmaAt (conjSubgroup a (conjSubgroup a⁻¹ C)) := by
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    exact (Hyp.mem_sigmaAt_conj_iff h hCω a).mp hBC'
  · rintro ⟨C, hC, hBC⟩
    have hCω : C ∈ omegaSet V := sigmaAt_subset_omegaSet hX hC
    refine ⟨conjSubgroup a C, ?_, ?_⟩
    · refine (Hyp.mem_sigmaAt_conj_iff h hX a).mpr ?_
      rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    · exact (Hyp.mem_sigmaAt_conj_iff h hCω a).mpr hBC

theorem Sec5Hyp.mem_sigmaAt_symm (hS : Sec5Hyp M V) {X U : Subgroup G}
    (hX : X ∈ omegaSet V) (hU : U ∈ sigmaAt X) : X ∈ sigmaAt U := by
  obtain ⟨b, -, rfl⟩ := hX
  have hU' : U ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.toRootHyp.toHyp b) ▸ hU
  exact (hS.conj b).self_mem_sigmaAt hU'

theorem Sec5Hyp.conj_mem_sigmaAt (hS : Sec5Hyp M V) {X U : Subgroup G} (hX : X ∈ omegaSet V)
    {x : G} (hx : x ∈ Subgroup.normalizer (X : Set G)) (hU : U ∈ sigmaAt X) :
    conjSubgroup x U ∈ sigmaAt X := by
  obtain ⟨b, -, rfl⟩ := hX
  have hU' : U ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.toRootHyp.toHyp b) ▸ hU
  have hxM : x ∈ conjSubgroup b M := by
    have hN : Subgroup.normalizer (conjSubgroup b V : Set G) = conjSubgroup b M := by
      rw [normalizer_conjSubgroup b V, hS.toRootHyp.toHyp.normalizer_eq]
    rwa [hN] at hx
  have h := (hS.conj b).conj_mem_sigmaSet hxM hU'
  rwa [← Hyp.sigmaAt_conj hS.toRootHyp.toHyp b] at h

theorem Sec5Hyp.le_of_mem_sigmaAt (hS : Sec5Hyp M V) {X U : Subgroup G}
    (hX : X ∈ omegaSet V) (hU : U ∈ sigmaAt X) :
    U ≤ Subgroup.normalizer (X : Set G) ∧ U ≤ cenOf X := by
  obtain ⟨b, -, rfl⟩ := hX
  have hU' : U ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.toRootHyp.toHyp b) ▸ hU
  have h := (hS.conj b).le_M_of_mem_sigmaSet hU'
  refine ⟨?_, h.2⟩
  rw [normalizer_conjSubgroup b V, hS.toRootHyp.toHyp.normalizer_eq]
  exact h.1

theorem Sec6Hyp.mem_sigmaAt_of_commute (hS : Sec6Hyp M V) {A C : Subgroup G}
    (hA : A ∈ sigmaSet M V) (hC : C ∈ sigmaSet M V) (hAC : ⁅A, C⁆ = ⊥) (hne : A ≠ C) :
    C ∈ sigmaAt A := by
  obtain ⟨h, hAeq, hHh⟩ := hA
  obtain ⟨g, hCeq, hHg⟩ := hC
  rw [hAeq, hCeq] at hAC hne
  rw [hAeq, hCeq, sigmaAt, normalizer_conjSubgroup h V,
    hS.sec5.toRootHyp.toHyp.normalizer_eq]
  refine ⟨g * h⁻¹, ?_, ?_⟩
  · rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  · have hOf_eq : hOf (conjSubgroup h M) (conjSubgroup h V) (g * h⁻¹) =
        conjSubgroup h (Pc M V) ⊔ conjSubgroup g (Pc M V) := by
      unfold hOf
      rw [Pc_conjSubgroup, conjSubgroup_conjSubgroup]
      rw [show (g * h⁻¹) * h = g by group]
    rw [hOf_eq, sup_comm]
    exact hS.res.s512 M V hS.sec5 g h ⟨h, rfl, hHh⟩ ⟨g, rfl, hHg⟩
      (by rwa [Subgroup.commutator_comm]) (Ne.symm hne)

theorem Sec6Hyp.mem_sigmaAt_of_commute_at (hS : Sec6Hyp M V) {X A C : Subgroup G}
    (hX : X ∈ omegaSet V) (hA : A ∈ sigmaAt X) (hC : C ∈ sigmaAt X) (hAC : ⁅A, C⁆ = ⊥)
    (hne : A ≠ C) : C ∈ sigmaAt A := by
  obtain ⟨b, -, rfl⟩ := hX
  have hA' : A ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.sec5.toRootHyp.toHyp b) ▸ hA
  have hC' : C ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.sec5.toRootHyp.toHyp b) ▸ hC
  exact (hS.conj b).mem_sigmaAt_of_commute hA' hC' hAC hne

theorem Sec6Hyp.commute_or_isL2Gen_at (hS : Sec6Hyp M V) {X A B : Subgroup G}
    (hX : X ∈ omegaSet V) (hA : A ∈ sigmaAt X) (hB : B ∈ sigmaAt X) :
    ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B := by
  obtain ⟨b, -, rfl⟩ := hX
  have hA' : A ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.sec5.toRootHyp.toHyp b) ▸ hA
  have hB' : B ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.sec5.toRootHyp.toHyp b) ▸ hB
  rcases hS.res.s513 (conjSubgroup b M) (conjSubgroup b V) (hS.sec5.conj b) A hA' B hB' with
    ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem Sec6Hyp.mem_sigmaAt_conj_of_mem_Pc (hS : Sec6Hyp M V) {D : Subgroup G}
    (hD : D ∈ sigmaSet M V) {p : G} (hp : p ∈ Pc M V) (hne : conjSubgroup p D ≠ D) :
    D ∈ sigmaAt (conjSubgroup p D) := by
  obtain ⟨d, hDeq, hHd⟩ := hD
  subst hDeq
  have hD : conjSubgroup d V ∈ sigmaSet M V := ⟨d, rfl, hHd⟩
  have hDp_mem : conjSubgroup p (conjSubgroup d V) ∈ sigmaSet M V :=
    hS.sec5.conj_mem_sigmaSet (hS.sec5.toRootHyp.toHyp.Pc_le_M hp) hD
  have hD2 : IsPGroup 2 (conjSubgroup d V) :=
    hS.sec5.toRootHyp.toHyp.isPGroup_V.map (MulAut.conj d).toMonoidHom
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hleP : conjSubgroup d V ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (hS.sec5.le_M_of_mem_sigmaSet hD).1.trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
  have h2 : IsPGroup 2 ((conjSubgroup d V ⊔ Pc M V : Subgroup G)) :=
    hD2.to_sup_of_normal_right' hP2 hleP
  have hconj_le : conjSubgroup p (conjSubgroup d V) ≤ conjSubgroup d V ⊔ Pc M V := by
    rintro x hx
    rw [mem_conjSubgroup] at hx
    set y : G := p⁻¹ * x * p with hydef
    have hyD : y ∈ conjSubgroup d V := hx
    have hyM : y ∈ M := (hS.sec5.le_M_of_mem_sigmaSet hD).1 hyD
    have hxeq : x = y * (y⁻¹ * p * y * p⁻¹) := by
      rw [hydef]
      group
    have h1 : y⁻¹ * p * y ∈ Pc M V := by
      have := (Subgroup.mem_normalizer_iff.mp
        (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc (M.inv_mem hyM)) p).mp hp
      simpa using this
    have h2' : y⁻¹ * p * y * p⁻¹ ∈ Pc M V :=
      (Pc M V).mul_mem h1 ((Pc M V).inv_mem hp)
    rw [hxeq]
    exact (conjSubgroup d V ⊔ Pc M V).mul_mem (Subgroup.mem_sup_left hyD)
      (Subgroup.mem_sup_right h2')
  have hnotL2 : ¬ IsL2Gen (conjSubgroup p (conjSubgroup d V)) (conjSubgroup d V) := by
    intro hl2
    obtain ⟨a, ha, b, hb, hord⟩ := hl2.exists_orderOf_eq_three
    have ha' : a ∈ conjSubgroup d V ⊔ Pc M V := hconj_le ha
    have hb' : b ∈ conjSubgroup d V ⊔ Pc M V := Subgroup.mem_sup_left hb
    have hab : a * b ∈ conjSubgroup d V ⊔ Pc M V :=
      (conjSubgroup d V ⊔ Pc M V).mul_mem ha' hb'
    obtain ⟨k, hk⟩ := h2.exists_orderOf_dvd_pow
      (⟨a * b, hab⟩ : ↥(conjSubgroup d V ⊔ Pc M V))
    have hk' : orderOf (a * b) ∣ 2 ^ k := by
      simpa [Subgroup.orderOf_coe] using hk
    rw [hord] at hk'
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hk') (by norm_num)
  have hcomm : ⁅conjSubgroup p (conjSubgroup d V), conjSubgroup d V⁆ = ⊥ := by
    rcases hS.res.s513 M V hS.sec5 (conjSubgroup p (conjSubgroup d V)) hDp_mem
      (conjSubgroup d V) hD with ⟨h, -⟩ | ⟨hl2, -⟩
    · exact h
    · exact absurd hl2 hnotL2
  exact hS.mem_sigmaAt_of_commute hDp_mem hD hcomm hne

theorem Sec6Hyp.sigmaSet_subset_gammaAt (hS : Sec6Hyp M V) : sigmaSet M V ⊆ gammaAt V := by
  intro U hU
  by_cases hUV : U = V
  · subst hUV
    obtain ⟨C, hC⟩ := hS.ne
    refine ⟨C, ?_, ?_⟩
    · rw [hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
      exact hC
    · exact hS.sec5.self_mem_sigmaAt hC
  · have hex : ∃ p ∈ Pc M V, conjSubgroup p U ≠ U := by
      by_contra hcon
      push Not at hcon
      have hPN : Pc M V ≤ Subgroup.normalizer (U : Set G) := fun p hp =>
        mem_normalizer_iff_conjSubgroup_eq.mpr (hcon p hp)
      have hinf : Pc M V ⊓ Subgroup.normalizer (U : Set G) = Pc M V :=
        le_antisymm inf_le_left (le_inf le_rfl hPN)
      have hcent : Pc M V ⊓ Subgroup.centralizer (U : Set G) = Pc M V := by
        rw [← hS.sec5.Pc_inf_normalizer_eq_centralizer hU, hinf]
      have hcard := hS.sec5.card_Pc_inf_centralizer hU
      rw [hcent] at hcard
      have hq2 : Nat.card V ^ 2 = 1 := by
        have hpos : 0 < Nat.card ↥(Pc M V) := Nat.card_pos
        exact Nat.eq_of_mul_eq_mul_left hpos (by simpa [mul_one] using hcard)
      have h4 : 4 ≤ Nat.card V := hS.sec5.toRootHyp.four_le_card
      nlinarith
    obtain ⟨p, hp, hpne⟩ := hex
    refine ⟨conjSubgroup p U, ?_, hS.mem_sigmaAt_conj_of_mem_Pc hU hp hpne⟩
    rw [hS.sec5.toRootHyp.toHyp.sigmaAt_eq]
    exact hS.sec5.conj_mem_sigmaSet (hS.sec5.toRootHyp.toHyp.Pc_le_M hp) hU

theorem Sec6Hyp.sigmaAt_subset_gammaAt (hS : Sec6Hyp M V) {X : Subgroup G}
    (hX : X ∈ omegaSet V) : sigmaAt X ⊆ gammaAt X := by
  obtain ⟨b, -, rfl⟩ := hX
  intro U hU
  have hU' : U ∈ sigmaSet (conjSubgroup b M) (conjSubgroup b V) :=
    (Hyp.sigmaAt_conj hS.sec5.toRootHyp.toHyp b) ▸ hU
  exact (hS.conj b).sigmaSet_subset_gammaAt hU'

theorem le_y0Of (V X : Subgroup G) : V ≤ y0Of V X := by
  unfold y0Of
  simpa [conjSubgroup_one] using
    le_iSup₂_of_le (f := fun x (_ : x ∈ cenOf X) => conjSubgroup x V) 1
      ((cenOf X).one_mem) le_rfl

theorem y0Of_anti (V : Subgroup G) {X X' : Subgroup G} (h : X ≤ X') :
    y0Of V X' ≤ y0Of V X := by
  unfold y0Of
  refine iSup₂_le fun x hx => ?_
  exact le_iSup₂_of_le x (Subgroup.centralizer_le h hx) le_rfl

private theorem y0Of_eq_iSup_conjSet (V X : Subgroup G) :
    y0Of V X = ⨆ C ∈ {C : Subgroup G | ∃ x ∈ cenOf X, C = conjSubgroup x V}, C := by
  unfold y0Of
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    exact le_iSup₂_of_le (conjSubgroup x V) ⟨x, hx, rfl⟩ le_rfl
  · refine iSup₂_le fun C hC => ?_
    obtain ⟨x, hx, rfl⟩ := hC
    exact le_iSup₂_of_le x hx le_rfl

private theorem iSup_conj_eq {S S' : Set (Subgroup G)} (a : G)
    (h : ∀ U, U ∈ S' ↔ conjSubgroup a⁻¹ U ∈ S) :
    (⨆ C ∈ S', C) = conjSubgroup a (⨆ C ∈ S, C) := by
  have hmap : conjSubgroup a (⨆ C ∈ S, C) = ⨆ C ∈ S, conjSubgroup a C := by
    simp only [conjSubgroup, Subgroup.map_iSup]
  rw [hmap]
  apply le_antisymm
  · refine iSup₂_le fun C' hC' => ?_
    have hCS : conjSubgroup a⁻¹ C' ∈ S := (h C').mp hC'
    have hCeq : conjSubgroup a (conjSubgroup a⁻¹ C') = C' := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [← hCeq]
    exact le_iSup₂_of_le (conjSubgroup a⁻¹ C') hCS le_rfl
  · refine iSup₂_le fun C hC => ?_
    have hC' : conjSubgroup a C ∈ S' := (h (conjSubgroup a C)).mpr ?_
    · exact le_iSup₂_of_le (conjSubgroup a C) hC' le_rfl
    · rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem cenOf_le_normalizer_y0Of (V X : Subgroup G) :
    cenOf X ≤ Subgroup.normalizer (y0Of V X : Set G) := by
  intro c hc
  rw [mem_normalizer_iff_conjSubgroup_eq, y0Of_eq_iSup_conjSet]
  refine (iSup_conj_eq c ?_).symm
  intro U
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c⁻¹ * x, mul_mem ((cenOf X).inv_mem hc) hx, by rw [conjSubgroup_conjSubgroup]⟩
  · rintro ⟨x, hx, hxU⟩
    refine ⟨c * x, mul_mem hc hx, ?_⟩
    have hU : U = conjSubgroup c (conjSubgroup c⁻¹ U) := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [hU, hxU, conjSubgroup_conjSubgroup]

theorem y0Of_conjSubgroup (a : G) (V X : Subgroup G) :
    y0Of (conjSubgroup a V) (conjSubgroup a X) = conjSubgroup a (y0Of V X) := by
  rw [y0Of_eq_iSup_conjSet, y0Of_eq_iSup_conjSet]
  refine iSup_conj_eq a ?_
  intro U
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : a⁻¹ * y * a ∈ cenOf X := by
      change y ∈ Subgroup.centralizer (conjSubgroup a X : Set G) at hy
      rw [centralizer_conjSubgroup_eq] at hy
      exact mem_conjSubgroup.mp hy
    refine ⟨a⁻¹ * y * a, hy', ?_⟩
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  · rintro ⟨x, hx, hxU⟩
    refine ⟨a * x * a⁻¹, ?_, ?_⟩
    · change a * x * a⁻¹ ∈ Subgroup.centralizer (conjSubgroup a X : Set G)
      rw [centralizer_conjSubgroup_eq]
      refine mem_conjSubgroup.mpr ?_
      have hx' : x ∈ Subgroup.centralizer (X : Set G) := hx
      rwa [show a⁻¹ * (a * x * a⁻¹) * a = x by group]
    · have hC : U = conjSubgroup a (conjSubgroup a⁻¹ U) := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      rw [hC, hxU, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group

private theorem conj_conj_Pc_eq (a p g : G) (hpg : g = a * p * a⁻¹) :
    conjSubgroup g (Pc (conjSubgroup a M) (conjSubgroup a V)) =
      conjSubgroup a (conjSubgroup p (Pc M V)) := by
  rw [Pc_conjSubgroup, hpg, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
    show (a * p * a⁻¹) * a = a * p by group]

private theorem conj_conj_m0Of_eq (a p g : G) (hpg : g = a * p * a⁻¹) :
    conjSubgroup g (m0Of (conjSubgroup a M) (conjSubgroup a V)) =
      conjSubgroup a (conjSubgroup p (m0Of M V)) := by
  rw [m0Of_conjSubgroup a, hpg, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
    show (a * p * a⁻¹) * a = a * p by group]

private theorem iSup_sigmaAt_conj_eq (h : Hyp M V) (a : G) {A' B' : Subgroup G}
    (hA' : A' ∈ omegaSet V) (hB' : B' ∈ omegaSet V) :
    (⨆ C ∈ sigmaAt (conjSubgroup a A') ∩ sigmaAt (conjSubgroup a B'), C) =
      conjSubgroup a (⨆ C ∈ sigmaAt A' ∩ sigmaAt B', C) := by
  refine iSup_conj_eq a fun C => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(Hyp.mem_sigmaAt_conj_iff h hA' a).mp h1,
      (Hyp.mem_sigmaAt_conj_iff h hB' a).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(Hyp.mem_sigmaAt_conj_iff h hA' a).mpr h1,
      (Hyp.mem_sigmaAt_conj_iff h hB' a).mpr h2⟩

theorem Sec7.Stmt71.conj (h71 : Sec7.Stmt71 M V) (a : G) :
    Sec7.Stmt71 (conjSubgroup a M) (conjSubgroup a V) := by
  intro N hVN hNP hNm0
  have hV' : V ≤ conjSubgroup a⁻¹ N := by
    rw [← conjSubgroup_le_iff]
    exact hVN
  have hNP' : conjSubgroup a⁻¹ N ≤ Pc M V := by
    rw [conjSubgroup_le_iff, inv_inv, ← Pc_conjSubgroup]
    exact hNP
  have hm0 : m0Of M V ≤ Subgroup.normalizer (conjSubgroup a⁻¹ N : Set G) := by
    have hm0a : conjSubgroup a (m0Of M V) ≤ Subgroup.normalizer (N : Set G) := by
      rwa [m0Of_conjSubgroup a] at hNm0
    have h' : conjSubgroup a⁻¹ (conjSubgroup a (m0Of M V)) ≤
        conjSubgroup a⁻¹ (Subgroup.normalizer (N : Set G)) :=
      Subgroup.map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hm0a
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
      ← normalizer_conjSubgroup a⁻¹ N] at h'
    exact h'
  rcases h71 (conjSubgroup a⁻¹ N) hV' hNP' hm0 with hN | hN
  · left
    calc N = conjSubgroup a (conjSubgroup a⁻¹ N) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ = conjSubgroup a V := by rw [hN]
  · right
    calc N = conjSubgroup a (conjSubgroup a⁻¹ N) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ = conjSubgroup a (Pc M V) := by rw [hN]
      _ = Pc (conjSubgroup a M) (conjSubgroup a V) := (Pc_conjSubgroup M V a).symm

theorem Sec7.Stmt74.conj (hS : Sec5Hyp M V) (h74 : Sec7.Stmt74 M V) (a : G) :
    Sec7.Stmt74 (conjSubgroup a M) (conjSubgroup a V) := by
  intro A B g hAg hA hB hAB
  have hHyp : Hyp M V := hS.toRootHyp.toHyp
  have hA' : conjSubgroup a⁻¹ A ∈ sigmaSet M V :=
    (mem_sigmaSet_conjSubgroup_iff a).mp hA
  have hB' : conjSubgroup a⁻¹ B ∈ sigmaSet M V :=
    (mem_sigmaSet_conjSubgroup_iff a).mp hB
  have hA'ω : conjSubgroup a⁻¹ A ∈ omegaSet V := sigmaSet_subset_omegaSet M V hA'
  have hB'ω : conjSubgroup a⁻¹ B ∈ omegaSet V := sigmaSet_subset_omegaSet M V hB'
  have hAB' : IsL2Gen (conjSubgroup a⁻¹ A) (conjSubgroup a⁻¹ B) := hAB.conj a⁻¹
  have hAg' : conjSubgroup a⁻¹ A = conjSubgroup (a⁻¹ * g * a) V := by
    rw [hAg, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  obtain ⟨h1, h2, h3⟩ :=
    h74 (conjSubgroup a⁻¹ A) (conjSubgroup a⁻¹ B) (a⁻¹ * g * a) hAg' hA' hB' hAB'
  have hAeq : A = conjSubgroup a (conjSubgroup a⁻¹ A) := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hBeq : B = conjSubgroup a (conjSubgroup a⁻¹ B) := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hsup : conjSubgroup a (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B) = A ⊔ B := by
    rw [conjSubgroup_sup, ← hAeq, ← hBeq]
  have h1' : y0Of (conjSubgroup a V) (A ⊔ B) =
      conjSubgroup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B)) := by
    rw [← hsup, y0Of_conjSubgroup]
  have hpg : g = a * (a⁻¹ * g * a) * a⁻¹ := by group
  refine ⟨?_, ?_, ?_⟩
  · have hABconj : (⨆ C ∈ sigmaAt A ∩ sigmaAt B, C) =
        ⨆ C ∈ sigmaAt (conjSubgroup a (conjSubgroup a⁻¹ A)) ∩
          sigmaAt (conjSubgroup a (conjSubgroup a⁻¹ B)), C := by
      rw [← hAeq, ← hBeq]
    rw [h1', h1, hABconj]
    exact (iSup_sigmaAt_conj_eq hHyp a hA'ω hB'ω).symm
  · calc
      y0Of (conjSubgroup a V) (A ⊔ B) ⊓
          conjSubgroup g (Pc (conjSubgroup a M) (conjSubgroup a V))
          = conjSubgroup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B)) ⊓
              conjSubgroup a (conjSubgroup (a⁻¹ * g * a) (Pc M V)) := by
            rw [h1', conj_conj_Pc_eq a (a⁻¹ * g * a) g hpg]
      _ = conjSubgroup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B) ⊓
              conjSubgroup (a⁻¹ * g * a) (Pc M V)) :=
            (conjSubgroup_inf a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B))
              (conjSubgroup (a⁻¹ * g * a) (Pc M V))).symm
      _ = conjSubgroup a (⊥ : Subgroup G) := by rw [h2]
      _ = ⊥ := Subgroup.map_bot _
  · calc
      y0Of (conjSubgroup a V) (A ⊔ B) ⊔
          conjSubgroup g (Pc (conjSubgroup a M) (conjSubgroup a V))
          = conjSubgroup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B)) ⊔
              conjSubgroup a (conjSubgroup (a⁻¹ * g * a) (Pc M V)) := by
            rw [h1', conj_conj_Pc_eq a (a⁻¹ * g * a) g hpg]
      _ = conjSubgroup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B) ⊔
              conjSubgroup (a⁻¹ * g * a) (Pc M V)) :=
            (conjSubgroup_sup a (y0Of V (conjSubgroup a⁻¹ A ⊔ conjSubgroup a⁻¹ B))
              (conjSubgroup (a⁻¹ * g * a) (Pc M V))).symm
      _ = conjSubgroup a (conjSubgroup (a⁻¹ * g * a) (m0Of M V)) := by rw [h3]
      _ = conjSubgroup g (m0Of (conjSubgroup a M) (conjSubgroup a V)) :=
            (conj_conj_m0Of_eq a (a⁻¹ * g * a) g hpg).symm

end CFSG.RankThree.GF2n.Tim81
