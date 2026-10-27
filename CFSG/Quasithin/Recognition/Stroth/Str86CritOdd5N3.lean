module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbGraph
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphF1
import CFSG.Quasithin.Recognition.Stroth.Str86AbGraphEdge
import CFSG.GroupTheory.SubgroupCardMul
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoModule

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem n3_bigB_le_normalizer_L2 {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
  have h := bigB_le_normalizer_of_hyp111 hF.1.symm
  rwa [bigB_comm L1 L2 S] at h

private theorem n3_P2_le_normalizer_u3H {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) :
    P2 L1 L2 S ≤ Subgroup.normalizer (u3H L1 L2 S : Set G) :=
  D14.le_normalizer_sup (sup_le Subgroup.le_normalizer (n3_bigB_le_normalizer_L2 hF))
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S))

private theorem n3_conj_sup_mul {g t : G} {A W : Subgroup G}
    (hA : A ⊔ conjSub t A = W) : conjSub g A ⊔ conjSub (g * t) A = conjSub g W := by
  rw [conjSub_mul, ← conjSub_sup, hA]

private theorem n3_conj_inf_mul {g t : G} {W Z : Subgroup G}
    (hW : W ⊓ conjSub t W = Z) : conjSub g W ⊓ conjSub (g * t) W = conjSub g Z := by
  rw [conjSub_mul, ← conjSub_inf, hW]

theorem str86_z1_sup_conj_z1_eq {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hO : Str86OddModule L1 L2 S m) {h : G} (hh : h ∈ P2 L1 L2 S) (hhB : h ∉ bigB L1 L2 S) :
    Z1 L1 L2 S ⊔ MulAut.conj h • Z1 L1 L2 S = ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ := by
  classical
  set W : Subgroup G := ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ with hW
  obtain ⟨hstep, hE, hnat⟩ := hO.1
  have hZleW : Z1 L1 L2 S ≤ W := by rw [hW]; exact hO.2.1
  have hcardZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ m := hO.2.2.1
  have hWcard : Nat.card W = (2 ^ m) ^ 2 := by
    have h := natCard_quotient_of_isNaturalChiefStep hnat
    change Nat.card (W ⧸ (⊥ : Subgroup G).subgroupOf W) =
      (Nat.card (GaloisField 2 m)) ^ 2 at h
    have hq : Nat.card (W ⧸ (⊥ : Subgroup G).subgroupOf W) = Nat.card W := by
      rw [Subgroup.bot_subgroupOf]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    rw [hq, GaloisField.card 2 m (by have hm := hI.hm; omega)] at h
    exact h
  have hZ2n : h ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) := hI.critHypN.normalizes hh
  have hHn : h ∈ Subgroup.normalizer (u3H L1 L2 S : Set G) := n3_P2_le_normalizer_u3H hI.hF hh
  have hZ2 : conjSub h (Z2 L1 L2 S) = Z2 L1 L2 S := by
    rw [str86_conjSub_eq_smul, mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hZ2n
  have hH : conjSub h (u3H L1 L2 S) = u3H L1 L2 S := by
    rw [str86_conjSub_eq_smul, mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hHn
  have hWn : MulAut.conj h • W = W := by
    rw [hW, ← str86_conjSub_eq_smul, (conjSub_commutator h _ _).symm, hZ2, hH]
  have hconjWle : MulAut.conj h • Z1 L1 L2 S ≤ W := by
    calc MulAut.conj h • Z1 L1 L2 S ≤ MulAut.conj h • W :=
          (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj h)).mpr hZleW
      _ = W := hWn
  have hcardconj : Nat.card (MulAut.conj h • Z1 L1 L2 S : Subgroup G) = 2 ^ m := by
    have hsmul : Nat.card (MulAut.conj h • Z1 L1 L2 S : Subgroup G) =
        Nat.card (Z1 L1 L2 S) := by
      rw [← str86_conjSub_eq_smul]
      exact Subgroup.card_mapSubgroup (Z1 L1 L2 S) (MulAut.conj h)
    rw [hsmul, hcardZ1]
  have hinf : Z1 L1 L2 S ⊓ MulAut.conj h • Z1 L1 L2 S = ⊥ :=
    str86_z1_inf_conj_eq_bot hI hh hhB
  have hprodSup : 2 ^ m * 2 ^ m ≤
      Nat.card (Z1 L1 L2 S ⊔ MulAut.conj h • Z1 L1 L2 S : Subgroup G) := by
    have h := CFSG.card_mul_card_le_of_inf_eq_bot
      (le_sup_left : Z1 L1 L2 S ≤ Z1 L1 L2 S ⊔ MulAut.conj h • Z1 L1 L2 S)
      (le_sup_right : MulAut.conj h • Z1 L1 L2 S ≤
        Z1 L1 L2 S ⊔ MulAut.conj h • Z1 L1 L2 S) hinf
    rwa [hcardZ1, hcardconj] at h
  refine Subgroup.eq_of_le_of_card_ge (sup_le hZleW hconjWle) ?_
  rw [hWcard]
  simpa [pow_two] using hprodSup

theorem str86_oddModule_inf_sup {L1 L2 S : Subgroup G}
    {k m : ℕ} {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F)
    (hO : Str86OddModule L1 L2 S m) {γ δ δ' ε ε' : Str86Γ L1 L2 S} (hγ : vtype γ = true)
    (hδ : δ ∈ nbrs γ) (hδ' : δ' ∈ nbrs γ) (hne : δ ≠ δ') (hε : ε ∈ nbrs δ) (hεγ : ε ≠ γ)
    (hε' : ε' ∈ nbrs δ') (hε'γ : ε' ≠ γ) :
    (omegaOneCenterOf (pCoreOf 2 (stab γ)) ⊔ omegaOneCenterOf (pCoreOf 2 (stab ε))) ⊓
        (omegaOneCenterOf (pCoreOf 2 (stab γ)) ⊔ omegaOneCenterOf (pCoreOf 2 (stab ε'))) =
      omegaOneCenterOf (pCoreOf 2 (stab γ)) := by
  classical
  set W : Subgroup G := ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ with hW
  have hP3 : ∀ t : G, t ∈ P2 L1 L2 S → t ∉ bigB L1 L2 S →
      Z1 L1 L2 S ⊔ conjSub t (Z1 L1 L2 S) = W := by
    intro t ht htB
    rw [hW, str86_conjSub_eq_smul]
    exact str86_z1_sup_conj_z1_eq hI hO ht htB
  have hN3 : ∀ t : G, t ∈ P1 L1 L2 S → t ∉ bigB L1 L2 S →
      W ⊓ conjSub t W = Z1 L1 L2 S := by
    intro t ht htB
    rw [hW, str86_conjSub_eq_smul]
    exact hO.2.2.2.2 t ht htB
  obtain ⟨-, -, -, -, hB5, hB6⟩ := str86_vertex_basics hI
  have hbase1 : stab (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) = P1 L1 L2 S :=
    (str86_base_values hI).2.1
  have hZγ₁ : ∀ t : ↥(L1 ⊔ L2 ⊔ S),
      omegaOneCenterOf (pCoreOf 2 (stab (t • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)))) =
        conjSub (t : G) (Z1 L1 L2 S) := by
    intro t
    simpa [hbase1] using
      (str86_vertex_smul hI t (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
        (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).2.1
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hγ
  obtain ⟨y₀, hy₀P, hδeq, hγeq⟩ := str86_nbrs_smul_γ₁ hI g hδ
  set g' : ↥(L1 ⊔ L2 ⊔ S) := g * y₀ with hg'
  have hγeq' : g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
      g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := hγeq
  have hδeq' : δ = g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := hδeq
  subst hδeq'
  have hδ'' : δ' ∈ nbrs (g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
    rw [← hγeq']
    exact hδ'
  obtain ⟨y, hyP, hδ'eq, -⟩ := str86_nbrs_smul_γ₁ hI g' hδ''
  subst hδ'eq
  obtain ⟨h, hhP, hεeq, -⟩ := str86_nbrs_smul_γ₀ hI g' hε
  subst hεeq
  obtain ⟨h', hh'P, hε'eq, -⟩ := str86_nbrs_smul_γ₀ hI (g' * y) hε'
  subst hε'eq
  have hyfix₁ : y • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
      γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) :=
    CosetGeom.smul_eq_of_mem_stab (by rw [hbase1]; exact hyP)
  have hyB : (y : G) ∉ bigB L1 L2 S := by
    intro hy
    apply hne
    calc g' • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)
        = g' • (y • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) := by
          rw [(hB5 y hyP).mpr hy]
      _ = (g' * y) • γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) :=
          (mul_smul g' y (γ₀ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).symm
  have hhB : (h : G) ∉ bigB L1 L2 S := by
    intro hh
    apply hεγ
    calc (g' * h) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)
        = g' • (h • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) :=
          mul_smul g' h (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      _ = g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
          rw [(hB6 h hhP).mpr hh]
      _ = g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := hγeq'.symm
  have hh'B : (h' : G) ∉ bigB L1 L2 S := by
    intro hh'
    apply hε'γ
    calc ((g' * y) * h') • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)
        = (g' * y) • (h' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) :=
          mul_smul (g' * y) h' (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      _ = (g' * y) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by
          rw [(hB6 h' hh'P).mpr hh']
      _ = g' • (y • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)) :=
          mul_smul g' y (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))
      _ = g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := by rw [hyfix₁]
      _ = g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) := hγeq'.symm
  have hZg : omegaOneCenterOf (pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S)
      (P1 L1 L2 S)))) = conjSub (g : G) (Z1 L1 L2 S) := hZγ₁ g
  have hZg' : omegaOneCenterOf (pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S)
      (P1 L1 L2 S)))) = conjSub (g' : G) (Z1 L1 L2 S) := by
    rw [hγeq']
    exact hZγ₁ g'
  have hveq : (g' * y) • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) =
      g' • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S) :=
    (mul_smul g' y (γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S))).trans (by rw [hyfix₁])
  have hZgy : omegaOneCenterOf (pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S)
      (P1 L1 L2 S)))) = conjSub ((g' * y : G)) (Z1 L1 L2 S) := by
    rw [hγeq', ← hveq]
    exact hZγ₁ (g' * y)
  have hE1 : omegaOneCenterOf (pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S)
        (P1 L1 L2 S)))) ⊔ omegaOneCenterOf (pCoreOf 2 (stab ((g' * h) • γ₁ (L1 ⊔ L2 ⊔ S)
        (P2 L1 L2 S) (P1 L1 L2 S)))) = conjSub (g' : G) W := by
    rw [hZg', hZγ₁ (g' * h)]
    exact n3_conj_sup_mul (g := (g' : G)) (t := (h : G)) (A := Z1 L1 L2 S) (W := W)
      (hP3 h hhP hhB)
  have hE2 : omegaOneCenterOf (pCoreOf 2 (stab (g • γ₁ (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S)
        (P1 L1 L2 S)))) ⊔ omegaOneCenterOf (pCoreOf 2 (stab (((g' * y) * h') • γ₁
        (L1 ⊔ L2 ⊔ S) (P2 L1 L2 S) (P1 L1 L2 S)))) =
        conjSub ((g' * y : G)) W := by
    rw [hZgy, hZγ₁ ((g' * y) * h')]
    exact n3_conj_sup_mul (g := ((g' * y : G))) (t := (h' : G)) (A := Z1 L1 L2 S) (W := W)
      (hP3 h' hh'P hh'B)
  rw [hE1, hE2, hZg']
  exact n3_conj_inf_mul (g := (g' : G)) (t := (y : G)) (W := W) (Z := Z1 L1 L2 S)
    (hN3 y hyP hyB)

end CFSG.Quasithin.Stroth

end
