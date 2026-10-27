module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeAbDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbOddModule
import CFSG.Quasithin.Recognition.Stroth.Str86AbM6
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5Dsp
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5T13g
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5L311
import CFSG.Quasithin.Recognition.Stroth.Str86CritOdd5V2
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str86_critPath_odd_T313_exists_a
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S) :
    ∃ (a : G) (μ : Str86Γ L1 L2 S),
      a ∈ Vv (Z2 L1 L2 S) (lam 1) ∧
        a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) ∧
        μ ∈ nbrs (lam (str86CritB L1 L2 S)) ∧
        a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ) ∧
        a ∉ pCoreOf 2 (stab μ) ∧ a * a = 1 ∧
        ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆ =
          omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S)))) := by
  have hb3 : 3 ≤ str86CritB L1 L2 S := by omega
  obtain ⟨-, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  obtain ⟨-, -, -, hE1, -, -, -, -⟩ := str86_critPath_odd_O1 hI hP hodd hb3
  have hM6 : Str86UnitaryM6 := fun _ _ _ _ _ _ _ _ _ _ _ hI' hZQ' _ htP htQ ht2 =>
    str86_sq_le_relIndex_conjClosure_of_mem_p1 hI' hZQ' htP htQ ht2
  have hO41 := (str86_critPath_odd_O4 hM6 hI hO hkm hP hodd hb3).1
  have hkey : ∃ a ∈ Vv (Z2 L1 L2 S) (lam 1) ⊓
      pCoreOf 2 (stab (lam (str86CritB L1 L2 S))),
      ∃ μ ∈ nbrs (lam (str86CritB L1 L2 S)), a ∉ pCoreOf 2 (stab μ) := by
    by_contra hcon
    push Not at hcon
    refine hO41 ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcent : Vv (Z2 L1 L2 S) (lam (str86CritB L1 L2 S)) ≤
        Subgroup.centralizer ({a} : Set G) := by
      refine F112Crit.Vv_le_of_forall_mem_nbrs hvb fun μ hμ => ?_
      have hvμ : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
      rw [(str86_vertex_basics hI).1 μ hvμ]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact (Subgroup.mem_centralizer_iff.mp
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (stab μ)
          (hcon a ha μ hμ)) v hv).symm
    exact (Subgroup.mem_centralizer_iff.mp (hcent hy) a (Set.mem_singleton a)).symm
  obtain ⟨a, haA, μ, hμ, haQμ⟩ := hkey
  have haV : a ∈ Vv (Z2 L1 L2 S) (lam 1) := haA.1
  have haQ' : a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S))) := haA.2
  have haS : a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ) :=
    str86_pCoreOf_le_pCoreOf_inf hI hμ haQ'
  have ha2 : a * a = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hE1 haV
  exact ⟨a, μ, haV, haQ', hμ, haS, haQμ, ha2,
    (str86_oddModule_edge hI hO hvb hμ).2.1 a haS haQμ⟩

private theorem str86_critPath_odd_T313_Zmu_not_le
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    {a : G} {μ : Str86Γ L1 L2 S} (haV : a ∈ Vv (Z2 L1 L2 S) (lam 1))
    (hZμa : ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆ =
      omegaOneCenterOf (pCoreOf 2 (stab (lam (str86CritB L1 L2 S))))) :
    ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) := by
  have hb3 : 3 ≤ str86CritB L1 L2 S := by omega
  obtain ⟨hv1, -, -, -, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  have hVQα := str86_commutator_Vv_pCoreOf hI hO hb3 hv1
  refine fun hle => str86_critPath_odd_L311c hI hO hkm hP hodd hb3 ?_
  rw [← hZμa]
  calc ⁅Vv (Z2 L1 L2 S) μ, Subgroup.zpowers a⁆
      ≤ ⁅pCoreOf 2 (stab (lam 1)), Subgroup.zpowers a⁆ :=
        Subgroup.commutator_mono hle le_rfl
    _ ≤ ⁅pCoreOf 2 (stab (lam 1)), Vv (Z2 L1 L2 S) (lam 1)⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr haV)
    _ = ⁅Vv (Z2 L1 L2 S) (lam 1), pCoreOf 2 (stab (lam 1))⁆ :=
        Subgroup.commutator_comm _ _
    _ = omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := hVQα

private theorem str86_critPath_odd_T313_turn
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {lam : ℕ → Str86Γ L1 L2 S}
    (hP : Str86CritPath L1 L2 S lam)
    {μ : Str86Γ L1 L2 S} (hμ : μ ∈ nbrs (lam (str86CritB L1 L2 S)))
    (hlin : vtype μ = false)
    (hcrit : ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)))
    (hb5 : 5 ≤ str86CritB L1 L2 S) :
    ∃ lam' : ℕ → Str86Γ L1 L2 S, Str86CritPath L1 L2 S lam' ∧ lam' 0 = μ ∧
      lam' 1 = lam (str86CritB L1 L2 S) ∧
      lam' (str86CritB L1 L2 S) = lam 1 ∧
      lam' (str86CritB L1 L2 S - 1) = lam 2 := by
  classical
  let lam' : ℕ → Str86Γ L1 L2 S :=
    fun i => if i = 0 then μ else lam (str86CritB L1 L2 S + 1 - i)
  have hb0 : str86CritB L1 L2 S ≠ 0 := by omega
  have hbm1 : str86CritB L1 L2 S - 1 ≠ 0 := by omega
  have hlam'0 : lam' 0 = μ := by simp [lam']
  have hlam'1 : lam' 1 = lam (str86CritB L1 L2 S) := by
    dsimp only [lam']
    rw [if_neg (by decide : (1 : ℕ) ≠ 0), Nat.add_sub_cancel]
  have hlam'b : lam' (str86CritB L1 L2 S) = lam 1 := by
    dsimp only [lam']
    rw [if_neg hb0, Nat.add_sub_cancel_left]
  have hlam'bm1 : lam' (str86CritB L1 L2 S - 1) = lam 2 := by
    dsimp only [lam']
    rw [if_neg hbm1]
    have h : str86CritB L1 L2 S + 1 - (str86CritB L1 L2 S - 1) = 2 := by omega
    rw [h]
  have hadj : ∀ i, i < str86CritB L1 L2 S →
      (graph (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)).Adj (lam' i) (lam' (i + 1)) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [hlam'0, hlam'1]
      exact CosetGeom.mem_nbrs_symm hμ
    · have hi1 : i + 1 ≠ 0 := by omega
      rw [show lam' i = lam (str86CritB L1 L2 S + 1 - i) from by
            dsimp only [lam']; rw [if_neg (by omega)],
          show lam' (i + 1) = lam (str86CritB L1 L2 S + 1 - (i + 1)) from by
            dsimp only [lam']; rw [if_neg hi1]]
      have h := (hP.isGeo.adj (i := str86CritB L1 L2 S - i) (by omega)).symm
      have e1 : str86CritB L1 L2 S + 1 - i = str86CritB L1 L2 S - i + 1 := by omega
      have e2 : str86CritB L1 L2 S + 1 - (i + 1) = str86CritB L1 L2 S - i := by omega
      rw [e1, e2]
      exact h
  exact ⟨lam', str86_critPath_of_walk hI (by rw [hlam'0]; exact hlin) hadj
      (by rw [hlam'0, hlam'b]; exact hcrit), hlam'0, hlam'1, hlam'b, hlam'bm1⟩

private theorem str86_critPath_odd_T313_disp
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : 2 * k ≤ m)
    {lam : ℕ → Str86Γ L1 L2 S} (hP : Str86CritPath L1 L2 S lam)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S)
    {a : G} {μ : Str86Γ L1 L2 S} (hvμ : vtype μ = false)
    (haV : a ∈ Vv (Z2 L1 L2 S) (lam 1))
    (haS : a ∈ pCoreOf 2 (stab (lam (str86CritB L1 L2 S)) ⊓ stab μ))
    {lam' : ℕ → Str86Γ L1 L2 S} (hP' : Str86CritPath L1 L2 S lam')
    (h0 : lam' 0 = μ) (hbm1 : lam' (str86CritB L1 L2 S - 1) = lam 2) :
    (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex
      (str86V2 L1 L2 S μ) ≤ 2 ^ k * 2 ^ m := by
  have hb3 : 3 ≤ str86CritB L1 L2 S := by omega
  obtain ⟨-, -, -, hAB4, hAB5⟩ := str86_Vv_abelian hI
  obtain ⟨hv1, -, -, -, -, hn12, hn21, -, -⟩ := hP.odd_shape hI hodd hb3
  have hUe : IsElemAbelian 2 (str86V2 L1 L2 S μ) := hAB5 hb5 μ hvμ
  have hL12 := str86_critPath_odd_V2_le hI hO hkm hP' hodd hb5
  rw [h0, hbm1] at hL12
  have hUS : str86V2 L1 L2 S μ ≤ pCoreOf 2 (stab (lam 1) ⊓ stab (lam 2)) := by
    rw [inf_comm]
    exact hL12.trans (str86_pCoreOf_le_pCoreOf_inf hI hn21)
  have hU1 := (str86_edge_facts hI hv1 hn12).2.2.2.2.2.2 (str86V2 L1 L2 S μ) hUe hUS
  have hcardZ : Nat.card (omegaOneCenterOf (pCoreOf 2 (stab (lam 1)))) = 2 ^ m :=
    (str86_oddModule_edge hI hO hv1 hn12).1
  have haStabμ : a ∈ stab μ := ((pCoreOf_le 2 _).trans inf_le_right) haS
  have haN : a ∈ Subgroup.normalizer (str86V2 L1 L2 S μ : Set G) :=
    (str86_vertex_basics hI).2.1 μ haStabμ
  have hVQα := str86_commutator_Vv_pCoreOf hI hO hb3 hv1
  have hZmem : ∀ u ∈ str86V2 L1 L2 S μ ⊓ pCoreOf 2 (stab (lam 1)),
      u * a * u⁻¹ * a⁻¹ ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
    intro u hu
    obtain ⟨-, huQ⟩ := Subgroup.mem_inf.mp hu
    have hmem : ⁅u, a⁆ ∈ omegaOneCenterOf (pCoreOf 2 (stab (lam 1))) := by
      rw [← hVQα, ← Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator huQ haV
    simpa only [commutatorElement_def] using hmem
  have hDsp := relIndex_centralizer_le_mul_card (U := str86V2 L1 L2 S μ)
    (U₀ := str86V2 L1 L2 S μ ⊓ pCoreOf 2 (stab (lam 1)))
    (Z := omegaOneCenterOf (pCoreOf 2 (stab (lam 1))))
    (fun u hu v hv => F7.isElemAbelian_comm hUe hu hv) haN inf_le_left hZmem
  exact hDsp.trans (Nat.mul_le_mul hU1 hcardZ.le)

private theorem str86_critPath_odd_T313_base_XU
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {μ : Str86Γ L1 L2 S} {g' : ↥(L1 ⊔ L2 ⊔ S)}
    (hg'μ : μ = g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) :
    conjSub (g' : G)⁻¹ (str86V2 L1 L2 S μ) =
      str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
  have hV2 := (str86_vertex_smul hI g' (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.2.2.2
  rw [← hg'μ] at hV2
  rw [hV2, conjSub_conjSub_inv]

private theorem str86_critPath_odd_T313_base_group
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {μ α' : Str86Γ L1 L2 S} {g' : ↥(L1 ⊔ L2 ⊔ S)}
    (hg'μ : μ = g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (hg'α' : α' = g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (hVα'U : Vv (Z2 L1 L2 S) α' ≤ str86V2 L1 L2 S μ)
    (hUQμ : str86V2 L1 L2 S μ ≤ pCoreOf 2 (stab μ)) :
    conjClosure (Z2 L1 L2 S) L1 ≤ str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ∧
      str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ≤ Q2 L1 L2 S ∧
      P2 L1 L2 S ≤ Subgroup.normalizer
        (str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) : Set G) := by
  obtain ⟨h0, -, -, -, hV1⟩ := str86_base_values hI
  have hXU := str86_critPath_odd_T313_base_XU hI hg'μ
  have hVα'U' : conjSub (g' : G) (conjClosure (Z2 L1 L2 S) L1) ≤ str86V2 L1 L2 S μ := by
    have hVγ := (str86_vertex_smul hI g' (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.2.2.1
    rw [hg'α', hVγ, hV1] at hVα'U
    exact hVα'U
  have hVX : conjClosure (Z2 L1 L2 S) L1 ≤
      str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    rw [← hXU]
    exact (conjSub_le_iff (g := (g' : G))).mp hVα'U'
  have hUQ' : str86V2 L1 L2 S μ ≤ conjSub (g' : G) (Q2 L1 L2 S) := by
    have hQ := (str86_vertex_smul hI g' (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1
    rw [h0] at hQ
    rw [← hQ, ← hg'μ]
    exact hUQμ
  have hXQ : str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ≤
      Q2 L1 L2 S := by
    rw [← hXU]
    exact (conjSub_le_iff (g := (g' : G)⁻¹)).mpr (by simpa using hUQ')
  have hXN : P2 L1 L2 S ≤ Subgroup.normalizer
      (str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) : Set G) := by
    have h := (str86_vertex_basics hI).2.1
      (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    rwa [h0] at h
  exact ⟨hVX, hXQ, hXN⟩

private theorem str86_critPath_odd_T313_base_elem
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {μ α' : Str86Γ L1 L2 S} {a : G}
    {g' : ↥(L1 ⊔ L2 ⊔ S)}
    (hg'μ : μ = g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (hg'α' : α' = g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
    (haS : a ∈ pCoreOf 2 (stab α' ⊓ stab μ))
    (haQμ : a ∉ pCoreOf 2 (stab μ)) (ha2 : a * a = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex
      (str86V2 L1 L2 S μ) ≤ 2 ^ k * 2 ^ m) :
    (g' : G)⁻¹ * a * g' ∈ S ∧ (g' : G)⁻¹ * a * g' ∉ Q2 L1 L2 S ∧
      ((g' : G)⁻¹ * a * g') * ((g' : G)⁻¹ * a * g') = 1 ∧
      (Subgroup.centralizer
        (Subgroup.zpowers ((g' : G)⁻¹ * a * g'))).relIndex
        (str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) ≤
        2 ^ k * 2 ^ m := by
  obtain ⟨h0, -, hS0, -, -⟩ := str86_base_values hI
  have hXU := str86_critPath_odd_T313_base_XU hI hg'μ
  have hS1 : pCoreOf 2 (stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) ⊓
      stab (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) = S := by
    rw [inf_comm]
    exact hS0
  have hSconj : pCoreOf 2 (stab α' ⊓ stab μ) = conjSub (g' : G) S := by
    have hSγ := (str86_vertex_smul hI g' (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.2.1
    rw [hg'α', hg'μ, hSγ, hS1]
  have ha'S : (g' : G)⁻¹ * a * g' ∈ S := by
    rw [hSconj] at haS
    exact mem_conjSub.mp haS
  have hQμ : pCoreOf 2 (stab μ) = conjSub (g' : G) (Q2 L1 L2 S) := by
    have hQ := (str86_vertex_smul hI g' (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).1
    rw [h0, ← hg'μ] at hQ
    exact hQ
  have haQ'S : (g' : G)⁻¹ * a * g' ∉ Q2 L1 L2 S := by
    rw [hQμ] at haQμ
    exact fun hmem => haQμ (mem_conjSub.mpr hmem)
  have ha'2 : ((g' : G)⁻¹ * a * g') * ((g' : G)⁻¹ * a * g') = 1 := by
    rw [show ((g' : G)⁻¹ * a * g') * ((g' : G)⁻¹ * a * g') =
      (g' : G)⁻¹ * (a * a) * g' by group, ha2]
    group
  have hz : Subgroup.zpowers ((g' : G)⁻¹ * a * g') =
      conjSub (g' : G)⁻¹ (Subgroup.zpowers a) := by
    rw [conjSub, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hdisp' : (Subgroup.centralizer
        (Subgroup.zpowers ((g' : G)⁻¹ * a * g'))).relIndex
        (str86V2 L1 L2 S (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))) ≤
        2 ^ k * 2 ^ m := by
    rw [hz, conjSub_centralizer (g := (g' : G)⁻¹) (H := Subgroup.zpowers a), ← hXU,
      str86_conjSub_eq_smul, str86_conjSub_eq_smul, Subgroup.relIndex_pointwise_smul]
    exact hdisp
  exact ⟨ha'S, haQ'S, ha'2, hdisp'⟩

private theorem str86_critPath_odd_T313_base
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) (hkm : k < m)
    {μ α' : Str86Γ L1 L2 S} {a : G} (hvμ : vtype μ = false) (hμα' : μ ∈ nbrs α')
    (hVα'U : Vv (Z2 L1 L2 S) α' ≤ str86V2 L1 L2 S μ)
    (hUQμ : str86V2 L1 L2 S μ ≤ pCoreOf 2 (stab μ))
    (haS : a ∈ pCoreOf 2 (stab α' ⊓ stab μ))
    (haQμ : a ∉ pCoreOf 2 (stab μ)) (ha2 : a * a = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex
      (str86V2 L1 L2 S μ) ≤ 2 ^ k * 2 ^ m) :
    False := by
  classical
  obtain ⟨g, hgμ⟩ := CosetGeom.exists_smul_eq_γ₀ hvμ
  have hμ' : α' ∈ nbrs (g • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    rw [← hgμ]
    exact CosetGeom.mem_nbrs_symm hμα'
  obtain ⟨h, -, hε, hg0⟩ := str86_nbrs_smul_γ₀ hI g hμ'
  let g' : ↥(L1 ⊔ L2 ⊔ S) := g * h
  have hg'μ : μ = g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
    show μ = (g * h) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)
    rw [hgμ, hg0]
  have hg'α' : α' = g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := hε
  obtain ⟨hVX, hXQ, hXN⟩ :=
    str86_critPath_odd_T313_base_group hI hg'μ hg'α' hVα'U hUQμ
  obtain ⟨ha'S, haQ'S, ha'2, hdisp'⟩ :=
    str86_critPath_odd_T313_base_elem hI hg'μ hg'α' haS haQμ ha2 hdisp
  exact str86_false_of_V2_displacement hI hO hZQ hkm hVX hXQ hXN ha'S haQ'S ha'2 hdisp'

theorem str86_critB_not_odd_ge_five_of
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hT36 : Str86OddRGeQSq) (hmod : Str86OddModuleOf)
    (hodd : Odd (str86CritB L1 L2 S)) (hb5 : 5 ≤ str86CritB L1 L2 S) : False := by
  have hb3 : 3 ≤ str86CritB L1 L2 S := by omega
  have hk2 : 2 ≤ k := hI.hk
  have hkm : 2 * k ≤ m := hT36 G L1 L2 S k m F hI hb3 hodd
  have hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S :=
    (str86_le_pCoreOf_of_dist_lt hI).2.2 (by omega)
  have hab : ∀ x ∈ conjClosure (Z2 L1 L2 S) L1,
      ∀ y ∈ conjClosure (Z2 L1 L2 S) L1, x * y = y * x :=
    (str86_Vv_abelian hI).2.2.1 hb3
  have hO : Str86OddModule L1 L2 S m :=
    hmod G L1 L2 S k m F hI.hF hI.hSB hI.hk hI.hFc hI.hU3 hI.hB2 hI.hL2 hkm hI.hZI hZQ hab
  obtain ⟨lam, hP, -, -⟩ := str86_exists_critPath hI
  obtain ⟨-, -, -, hvb, -, -, -, -, -⟩ := hP.odd_shape hI hodd hb3
  obtain ⟨a, μ, haV, haQ', hμ, haS, haQμ, ha2, hZμa⟩ :=
    str86_critPath_odd_T313_exists_a hI hO hkm hP hodd hb5
  have hvμ : vtype μ = false := str86_vtype_of_mem_nbrs hvb hμ
  have hμNotLe : ¬ Vv (Z2 L1 L2 S) μ ≤ pCoreOf 2 (stab (lam 1)) :=
    str86_critPath_odd_T313_Zmu_not_le hI hO hkm hP hodd hb5 haV hZμa
  obtain ⟨lam', hP', h0', -, -, hbm1'⟩ :=
    str86_critPath_odd_T313_turn hI hP hμ hvμ hμNotLe hb5
  have hdisp := str86_critPath_odd_T313_disp hI hO hkm hP hodd hb5 hvμ haV haS
    hP' h0' hbm1'
  refine str86_critPath_odd_T313_base hI hO hZQ (by omega) hvμ hμ ?_ ?_ haS haQμ ha2 hdisp
  · exact le_iSup₂_of_le (lam (str86CritB L1 L2 S)) (CosetGeom.mem_nbrs_symm hμ) le_rfl
  · exact (str86_Vv_abelian hI).2.2.2.1 hb3 μ hvμ

theorem str86CritNotOdd5_of
    (hT36 : Str86OddRGeQSq)
    (hmod : Str86OddModuleOf) : Str86CritNotOdd5 := by
  rintro G _ _ L1 L2 S hF hSB h1 hB2 h2 hZI _hZ ⟨hb5, hodd⟩
  obtain ⟨k, m, F, _, _, hI⟩ := str86AbHyp_exists hF hSB h1 hB2 h2 hZI
  exact str86_critB_not_odd_ge_five_of hI hT36 hmod hodd hb5

end CFSG.Quasithin.Stroth

end
