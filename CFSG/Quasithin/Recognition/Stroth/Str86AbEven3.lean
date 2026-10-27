module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbEven2
public import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeAbDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.Stroth.Str86AbC8
import CFSG.Quasithin.Recognition.Stroth.Str86AbE4Base
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_conjClosure_le_V2 {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) :
    conjClosure (Z2 L1 L2 S) L1 ≤
      str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
  obtain ⟨-, -, -, -, hV1⟩ := str86_base_values hI
  rw [← hV1]
  exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ nbrs (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) =>
    Vv (Z2 L1 L2 S) γ) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) CosetGeom.adj_γ₀_γ₁ le_rfl

theorem str86_V2_not_le_pCoreOf_even_base {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hl0 : lam 0 = γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (hl1 : lam 1 = γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (hb : Even (str86CritB L1 L2 S)) (hb4 : 4 ≤ str86CritB L1 L2 S) :
    ¬ str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) := by
  intro hX
  have hF := hI.hF
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hI.hSB h1 hI.hB2 h2 hI.hZI
  obtain ⟨hGL1, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨h0, h1', -, -, -⟩ := str86_base_values hI
  obtain ⟨-, hD42, -⟩ := str86_vertex_basics hI
  obtain ⟨hE1a, hZ1b, -, -, hE1e, -, -, -⟩ := str86_critPath_e1 hE1 hI hP hb (by omega)
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  rw [hl0, h0] at hE1a
  obtain ⟨d, hdV, hdQ⟩ := SetLike.not_le_iff_exists.mp hE1a
  have hvb : vtype (lam (str86CritB L1 L2 S)) = false := hP.vtype_of_even hI le_rfl hb
  have hdQ1 : d ∈ Q1 L1 L2 S := by
    have h := hGL1 _ (lam 1) hvb (by
      rw [CosetGeom.dist_comm, hP.isGeo 1 _ (by omega) le_rfl]; omega) hdV
    rwa [hl1, h1'] at h
  have hdH : d ∈ u3H L1 L2 S := str86_s_le_u3H hF.toW hI.hSB hI.hm hI.hL2 (hQ1S hdQ1)
  have hZb1 : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))) = Z1 L1 L2 S := by
    rw [← hZ1b, hl1, h1']
  have hdX : ∀ x ∈ str86V2 L1 L2 S (lam 0), d * x * d⁻¹ * x⁻¹ ∈ Z2 L1 L2 S := by
    intro x hx
    have hc := Subgroup.commutator_mem_commutator hdV (hX hx)
    rw [hE1e, hZb1] at hc
    rw [← commutatorElement_def]
    exact hZ1Z2 hc
  have hXN : u3H L1 L2 S ≤ Subgroup.normalizer (str86V2 L1 L2 S (lam 0) : Set G) := by
    have h := hD42 (lam 0)
    rw [hl0, h0] at h
    rw [hl0]
    exact (u3H_le_p2 L1 L2 S).trans h
  have hC := str86_commutator_oTwoUpper_le_of_mem hI hXN hdH hdQ hdX
  rw [hl0] at hC
  exact str86_false_of_commutator_oTwoUpper_le hI (hZQ (by omega)) (str86_conjClosure_le_V2 hI) hC

theorem str86_V2_not_le_pCoreOf_even {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hb : Even (str86CritB L1 L2 S)) (hb4 : 4 ≤ str86CritB L1 L2 S) :
    ¬ str86V2 L1 L2 S (lam 0) ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))) := by
  obtain ⟨-, x, hx0, hx1⟩ := hP.smul hI
  have hP' := (hP.smul hI).1 x⁻¹
  have h0' : (fun i => x⁻¹ • lam i) 0 = γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
    show x⁻¹ • lam 0 = _
    rw [hx0, inv_smul_smul]
  have h1' : (fun i => x⁻¹ • lam i) 1 = γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
    show x⁻¹ • lam 1 = _
    rw [hx1, inv_smul_smul]
  have hbase := str86_V2_not_le_pCoreOf_even_base hE1 hI hP' h0' h1' hb hb4
  intro hle
  apply hbase
  show str86V2 L1 L2 S (x⁻¹ • lam 0) ≤
    pCoreOf 2 (stab (x⁻¹ • lam (str86CritB L1 L2 S - 1)))
  rw [(str86_vertex_smul hI x⁻¹ (lam 0) (lam 0)).2.2.2.2,
    (str86_vertex_smul hI x⁻¹ (lam (str86CritB L1 L2 S - 1)) (lam 0)).1,
    F112Crit.conjSub_le_conjSub_iff]
  exact hle

theorem str86_le_of_critB_even {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hI : Str86AbHyp L1 L2 S k m F)
    (hb : Even (str86CritB L1 L2 S)) (hb6 : 6 ≤ str86CritB L1 L2 S) : m ≤ k := by
  have hF := hI.hF
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hI.hSB h1 hI.hB2 h2 hI.hZI
  obtain ⟨hGL1, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨h0, h1', -, -, -⟩ := str86_base_values hI
  obtain ⟨hD41, hD42, -⟩ := str86_vertex_basics hI
  obtain ⟨-, -, -, hAB4, hAB5⟩ := str86_Vv_abelian hI
  obtain ⟨lam, hP, hl0, hl1⟩ := str86_exists_critPath hI
  obtain ⟨hE1a, hZ1b, -, -, hE1e, -, -, -⟩ := str86_critPath_e1 hE1 hI hP hb (by omega)
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hb1 : 1 ≤ str86CritB L1 L2 S := by omega
  set X : Subgroup G := str86V2 L1 L2 S (lam 0) with hXdef
  have hvb1 : vtype (lam (str86CritB L1 L2 S - 1)) = true := by
    obtain ⟨j, hj⟩ := hb
    exact hP.vtype_of_odd hI (by omega) ⟨j - 1, by omega⟩
  have hvb2 : vtype (lam (str86CritB L1 L2 S - 2)) = false := by
    obtain ⟨j, hj⟩ := hb
    exact hP.vtype_of_even hI (by omega) ⟨j - 1, by omega⟩
  have hn : lam (str86CritB L1 L2 S - 2) ∈ nbrs (lam (str86CritB L1 L2 S - 1)) := by
    have h := (hP.isGeo.adj (i := str86CritB L1 L2 S - 2) (by omega)).symm
    rwa [show str86CritB L1 L2 S - 2 + 1 = str86CritB L1 L2 S - 1 by omega] at h
  have hQ0 : pCoreOf 2 (stab (lam 0)) = Q2 L1 L2 S := by rw [hl0, h0]
  have hS0 : stab (lam 0) = P2 L1 L2 S := by rw [hl0, h0]
  have hXQ : X ≤ Q2 L1 L2 S := (hAB4 (by omega) (lam 0) hP.linear).trans hQ0.le
  have hXe : IsElemAbelian 2 X := hAB5 (by omega) (lam 0) hP.linear
  have hXS : X ≤ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)) ⊓
      stab (lam (str86CritB L1 L2 S - 2))) := by
    rw [inf_comm]
    exact (str86_V2_le_pCoreOf_even hE1 hI hP hb hb6).trans
      (str86_pCoreOf_le_pCoreOf_inf hI (show lam (str86CritB L1 L2 S - 1) ∈
        nbrs (lam (str86CritB L1 L2 S - 2)) from (show (graph _ _ _).Adj
          (lam (str86CritB L1 L2 S - 1)) (lam (str86CritB L1 L2 S - 2)) from hn).symm))
  have hidx := (str86_edge_facts hI hvb1 hn).2.2.2.2.2.2 X hXe hXS
  rw [hQ0] at hE1a
  obtain ⟨t, htV, htQ⟩ := SetLike.not_le_iff_exists.mp hE1a
  have hvb : vtype (lam (str86CritB L1 L2 S)) = false := hP.vtype_of_even hI le_rfl hb
  have htQ1 : t ∈ Q1 L1 L2 S := by
    have h := hGL1 _ (lam 1) hvb (by
      rw [CosetGeom.dist_comm, hP.isGeo 1 _ (by omega) le_rfl]; omega) htV
    rwa [hl1, h1'] at h
  have htH : t ∈ u3H L1 L2 S := str86_s_le_u3H hF.toW hI.hSB hI.hm hI.hL2 (hQ1S htQ1)
  have ht2 : t * t ∈ Q2 L1 L2 S := by
    have htZ : t ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
      rw [← hD41 _ hvb]
      exact htV
    rw [← pow_two, (SmithC27.isElemAbelian_omegaOneCenterOf _).2 t htZ]
    exact (Q2 L1 L2 S).one_mem
  have hZb1 : omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1)))) =
      Z1 L1 L2 S := by
    rw [← hZ1b, hl1, h1']
  have htY : ∀ y ∈ X ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S - 1))),
      t * y * t⁻¹ * y⁻¹ ∈ Z2 L1 L2 S := by
    intro y hy
    have hc := Subgroup.commutator_mem_commutator htV (Subgroup.mem_inf.mp hy).2
    rw [hE1e, hZb1] at hc
    rw [← commutatorElement_def]
    exact hZ1Z2 hc
  have hXN : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G) :=
    (le_of_eq hS0.symm).trans (hD42 (lam 0))
  have hVX : conjClosure (Z2 L1 L2 S) L1 ≤ X := by
    rw [hXdef, hl0]
    exact str86_conjClosure_le_V2 hI
  have h := str86_two_pow_le_of_commutator_mod_z2 hI (hZQ (by omega)) hVX hXQ hXN inf_le_left
    hidx htH htQ ht2 htY
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem str86_critB_not_even_ge_eight {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hE1 : Str86E1) (hW : Str86LemmaW)
    (hI : Str86AbHyp L1 L2 S k m F) (hb : Even (str86CritB L1 L2 S))
    (hb8 : 8 ≤ str86CritB L1 L2 S) : False := by
  obtain ⟨hGL1, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨h0, h1', -, -, hV1⟩ := str86_base_values hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  have hmk := str86_le_of_critB_even hE1 hI hb (by omega)
  obtain ⟨lam, hP, hl0, hl1⟩ := str86_exists_critPath hI
  have hPr := hP.reverse hE1 hI hb (by omega)
  have hE42 := str86_V2_le_pCoreOf_even hE1 hI hPr hb (by omega)
  have hE43 := str86_V2_not_le_pCoreOf_even hE1 hI hPr hb (by omega)
  simp only [Nat.sub_zero] at hE42 hE43
  rw [show str86CritB L1 L2 S - (str86CritB L1 L2 S - 2) = 2 by omega] at hE42
  rw [show str86CritB L1 L2 S - (str86CritB L1 L2 S - 1) = 1 by omega] at hE43
  have hvb : vtype (lam (str86CritB L1 L2 S)) = false := hP.vtype_of_even hI le_rfl hb
  obtain ⟨μ, hμ, hμQ⟩ : ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)),
      ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) := by
    by_contra hcon
    refine hE43 (iSup₂_le fun μ hμ => ?_)
    by_contra h
    exact hcon ⟨μ, hμ, h⟩
  have hvμ : vtype μ = true := F112Crit.vtype_eq_true_of_mem_nbrs hvb hμ
  obtain ⟨ν, hν, hνQ⟩ : ∃ ν ∈ nbrs μ, ¬ Vv (Z2 L1 L2 S) ν ≤ pCoreOf 2 (stab (lam 1)) := by
    by_contra hcon
    refine hμQ (F112Crit.Vv_le_of_forall_mem_nbrs hvμ fun ν hν => ?_)
    by_contra h
    exact hcon ⟨ν, hν, h⟩
  have hvν : vtype ν = false := str86_vtype_of_mem_nbrs hvμ hν
  obtain ⟨t, htV, htQ⟩ := SetLike.not_le_iff_exists.mp hνQ
  have ht2 : t * t = 1 := by
    have htZ : t ∈ omegaOneCenterOf (pCoreOf 2 (stab ν)) := by
      rw [← hD41 _ hvν]
      exact htV
    rw [← pow_two]
    exact (SmithC27.isElemAbelian_omegaOneCenterOf _).2 t htZ
  have htV2 : t ∈ str86V2 L1 L2 S (lam (str86CritB L1 L2 S)) :=
    le_iSup₂_of_le (f := fun γ (_ : γ ∈ nbrs (lam (str86CritB L1 L2 S))) => Vv (Z2 L1 L2 S) γ)
      μ hμ (F112Crit.Vv_le_Vv_of_mem_nbrs hvμ hν) htV
  have hn21 : lam 1 ∈ nbrs (lam 2) := (hP.isGeo.adj (i := 1) (by omega)).symm
  have htS : t ∈ pCoreOf 2 (stab (lam 2) ⊓ stab (lam 1)) :=
    str86_pCoreOf_le_pCoreOf_inf hI hn21 (hE42 htV2)
  have htP : t ∈ P1 L1 L2 S := by
    have h := (pCoreOf_le 2 _ htS).2
    rwa [hl1, h1'] at h
  have htQ1 : t ∉ Q1 L1 L2 S := by
    rw [hl1, h1'] at htQ
    exact htQ
  have hd := str86_displacement_far_even hI hP hb (by omega) hμ hν htV
  rw [hl1, hV1] at hd
  have hle : 2 ^ m * 2 ^ k * 2 ^ m ≤ (2 ^ k) ^ 3 := by
    rw [← pow_add, ← pow_add, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkm := hW G L1 L2 S k m F hI (hZQ (by omega)) t htP htQ1 ht2 (hd.trans hle)
  have := hI.hk
  omega

theorem str86CritNotEven_of (hE1 : Str86E1) (hW : Str86LemmaW) :
    Str86CritNotEven := by
  rintro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI _hZ ⟨h4, hev⟩
  obtain ⟨k, m, F, _, _, hI⟩ := str86AbHyp_exists hF hSB h1 hB2 h2 hZI
  by_cases hb4 : str86CritB L1 L2 S = 4
  · exact str86_critB_ne_four hE1 hI hb4
  by_cases hb6 : str86CritB L1 L2 S = 6
  · exact str86_critB_ne_six hE1 hI hb6
  refine str86_critB_not_even_ge_eight hE1 hW hI hev ?_
  obtain ⟨j, hj⟩ := hev
  omega

end CFSG.Quasithin.Stroth

end
