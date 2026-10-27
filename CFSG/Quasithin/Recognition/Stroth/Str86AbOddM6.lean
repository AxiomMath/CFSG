module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Background.D15Chief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem two_pow_lt_two_pow_sq {k : ℕ} (hk : 1 ≤ k) : 2 ^ k < (2 ^ k) ^ 2 := by
  rw [← pow_mul]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem two_mul_le_of_two_pow_sq_le {k m : ℕ} (h : (2 ^ k) ^ 2 ≤ 2 ^ m) : 2 * k ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  have h' := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
  rw [← pow_mul, mul_comm] at h
  exact absurd h (not_le.mpr h')

theorem str86_sq_le_relIndex_Vv {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6)
    (hI : Str86AbHyp L1 L2 S k m F) (hb : 2 ≤ str86CritB L1 L2 S) {γ : Str86Γ L1 L2 S}
    (hγ : vtype γ = true) {t : G} (htγ : t ∈ stab γ) (htQ : t ∉ pCoreOf 2 (stab γ))
    (ht2 : t * t = 1) :
    (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Vv (Z2 L1 L2 S) γ) := by
  obtain ⟨-, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨-, h1, -, -, hV1⟩ := str86_base_values hI
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hγ
  obtain ⟨hQ, -, -, hV, -⟩ := str86_vertex_smul hI g
    (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
  rw [CosetGeom.stab_smul, h1, mem_conjSub] at htγ
  rw [hQ, h1, mem_conjSub] at htQ
  have ht'2 : ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = 1 := by
    rw [show ((g : G)⁻¹ * t * g) * ((g : G)⁻¹ * t * g) = (g : G)⁻¹ * (t * t) * g by group, ht2]
    group
  have h := hM6 G L1 L2 S k m F hI (hZQ hb) _ htγ htQ ht'2
  have hz : Subgroup.zpowers t = conjSub (g : G) (Subgroup.zpowers ((g : G)⁻¹ * t * g)) := by
    rw [conjSub, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hV, hV1, hz, conjSub_centralizer, str86_conjSub_eq_smul, str86_conjSub_eq_smul,
    Subgroup.relIndex_pointwise_smul]
  exact h

theorem str86_critPath_odd_O2 {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6)
    (hI : Str86AbHyp L1 L2 S k m F) {lam : ℕ → Str86Γ L1 L2 S}
    (hP : Str86CritPath L1 L2 S lam) (hodd : Odd (str86CritB L1 L2 S))
    (hb3 : 3 ≤ str86CritB L1 L2 S) :
    Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓
        Subgroup.centralizer (Vv (Z2 L1 L2 S) (lam 1) : Set G) <
      Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ⊓ pCoreOf 2 (stab (lam 1)) ∧
    (¬ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1)) →
      Vv (Z2 L1 L2 S) (lam 1) ⊓
          Subgroup.centralizer (Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) : Set G) <
        Vv (Z2 L1 L2 S) (lam 1) ⊓ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
  have hc := hI.critHypN
  obtain ⟨-, hO12, hO13, hE1, hEb, -, hO17, hO18⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  obtain ⟨hF1, hF2, hF3, -⟩ := str86_critPath_odd_F4 hI hP hodd hb3
  obtain ⟨hv1, -, -, hvb, -, -, hn21, hnb', -⟩ := hP.odd_shape hI hodd hb3
  have hk : 2 ^ k < (2 ^ k) ^ 2 := two_pow_lt_two_pow_sq (by have := hI.hk; omega)
  have hQstab : ∀ δ ε : Str86Γ L1 L2 S, ε ∈ nbrs δ → pCoreOf 2 (stab δ) ≤ stab ε :=
    fun δ ε hε => (CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam δ).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (CosetGeom.dist_eq_one_iff_adj.mpr hε).le)
  have key : ∀ {γ : Str86Γ L1 L2 S} {U : Subgroup G}, vtype γ = true → IsElemAbelian 2 U →
      U ≤ stab γ → ¬ U ≤ pCoreOf 2 (stab γ) →
      (2 ^ k) ^ 2 ≤ (Vv (Z2 L1 L2 S) γ ⊓ Subgroup.centralizer (U : Set G)).relIndex
        (Vv (Z2 L1 L2 S) γ) := by
    intro γ U hγ hU hUs hUQ
    obtain ⟨t, htU, htQ⟩ := SetLike.not_le_iff_exists.mp hUQ
    have ht2 : t * t = 1 := by
      rw [← pow_two]
      exact hU.2 t htU
    refine (str86_sq_le_relIndex_Vv hM6 hI (by omega) hγ (hUs htU) htQ ht2).trans ?_
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htU))
      (D15Proof.relIndex_ne_zero _ _)
  constructor
  · refine lt_of_le_of_ne (le_inf inf_le_left hF3) fun heq => ?_
    have h := key hvb hE1 (hO12.trans (hQstab _ _ hnb')) hF1
    rw [heq] at h
    exact absurd (h.trans hO18) (not_le.mpr hk)
  · intro hVQ
    refine lt_of_le_of_ne (le_inf inf_le_left hF2) fun heq => ?_
    have h := key hv1 hEb (hO13.trans (hQstab _ _ hn21)) hVQ
    rw [heq] at h
    exact absurd (h.trans hO17) (not_le.mpr hk)

theorem str86_critPath_odd_O3 {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6)
    (hI : Str86AbHyp L1 L2 S k m F) {lam : ℕ → Str86Γ L1 L2 S}
    (hP : Str86CritPath L1 L2 S lam) (hodd : Odd (str86CritB L1 L2 S))
    (hb3 : 3 ≤ str86CritB L1 L2 S)
    (hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))) :
    2 * k ≤ m := by
  have hc := hI.critHypN
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨hv1, -, -, hvb, hn01, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  obtain ⟨t, ht0, htb⟩ := SetLike.not_le_iff_exists.mp hP.critical
  have ht0' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam 0))) := by
    rw [← hD41 _ hP.linear]
    exact ht0
  have htstab : t ∈ stab (lam (str86CritB L1 L2 S)) :=
    CritHypN.le_stab_of_dist_le_at hc (show 1 ≤ str86CritB L1 L2 S by omega) hP.linear
      (show CosetGeom.dist (lam 0) (lam (str86CritB L1 L2 S)) ≤ str86CritB L1 L2 S by
        rw [hP.isGeo 0 _ (Nat.zero_le _) le_rfl]; omega) ht0
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact (SmithC27.isElemAbelian_omegaOneCenterOf _).2 t ht0'
  have hM := str86_sq_le_relIndex_Vv hM6 hI (by omega) hvb htstab htb ht2
  have hCt : pCoreOf 2 (stab (lam 0)) ⊓ Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    inf_le_left.trans ((SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab (lam 0))).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr ht0')))
  have hVS : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤
      pCoreOf 2 (stab (lam 1) ⊓ stab (lam 0)) :=
    hVQ.trans (str86_pCoreOf_le_pCoreOf_inf hI hn01)
  have hr := (str86_edge_facts hI hv1 hn01).2.2.2.1
  have h1 := Subgroup.relIndex_le_of_le_left (L := Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)))
    hCt (D15Proof.relIndex_ne_zero _ _)
  rw [Subgroup.inf_relIndex_right] at h1
  have h2 := Subgroup.relIndex_le_of_le_right hVS (D15Proof.relIndex_ne_zero
    (pCoreOf 2 (stab (lam 0))) (pCoreOf 2 (stab (lam 1) ⊓ stab (lam 0))))
  rw [hr] at h2
  exact two_mul_le_of_two_pow_sq_le ((hM.trans h1).trans h2)

theorem str86_two_mul_le_of_critB_odd {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hM6 : Str86UnitaryM6) (hW : Str86LemmaW)
    (hI : Str86AbHyp L1 L2 S k m F) (hodd : Odd (str86CritB L1 L2 S))
    (hb3 : 3 ≤ str86CritB L1 L2 S) : 2 * k ≤ m := by
  obtain ⟨-, -, hZQ⟩ := str86_le_pCoreOf_of_dist_lt hI
  obtain ⟨hD41, -⟩ := str86_vertex_basics hI
  obtain ⟨-, h1, -, -, hV1⟩ := str86_base_values hI
  obtain ⟨lam, hP, -, hl1⟩ := str86_exists_critPath hI
  obtain ⟨-, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  by_cases hVQ : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤ pCoreOf 2 (stab (lam 1))
  · exact str86_critPath_odd_O3 hM6 hI hP hodd hb3 hVQ
  · obtain ⟨μ, hμ, hμQ, hμS, hdisp⟩ := str86_critPath_odd_O5 hI hP hodd hb3 hVQ
    obtain ⟨t, htμ, htQ⟩ := SetLike.not_le_iff_exists.mp hμQ
    have hvμ : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
    have htP : t ∈ P1 L1 L2 S := by
      have h' := (pCoreOf_le 2 _ (hμS htμ)).1
      rwa [hl1, h1] at h'
    have htQ' : t ∉ Q1 L1 L2 S := by
      rw [hl1, h1] at htQ
      exact htQ
    have ht2 : t * t = 1 := by
      rw [← pow_two]
      have htμ' : t ∈ omegaOneCenterOf (pCoreOf 2 (stab μ)) := by
        rw [← hD41 μ hvμ]
        exact htμ
      exact (SmithC27.isElemAbelian_omegaOneCenterOf _).2 t htμ'
    have hd := hdisp t htμ
    rw [hl1, hV1] at hd
    by_contra hlt
    rw [not_le] at hlt
    have hle : 2 ^ k * 2 ^ m ≤ (2 ^ k) ^ 3 := by
      rw [← pow_add, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (hW G L1 L2 S k m F hI (hZQ (by omega)) t htP htQ' ht2 (hd.trans hle))
      (not_le.mpr hlt)

theorem str86OddRGeQSq_of (hM6 : Str86UnitaryM6)
    (hW : Str86LemmaW) : Str86OddRGeQSq := by
  intro G _ _ L1 L2 S k m F _ _ hI hb3 hodd
  exact str86_two_mul_le_of_critB_odd hM6 hW hI hodd hb3

end CFSG.Quasithin.Stroth

end
