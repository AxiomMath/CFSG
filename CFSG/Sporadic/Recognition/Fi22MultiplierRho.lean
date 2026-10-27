module

public import CFSG.Sporadic.Recognition.Fi22MultiplierY332
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Certificate24051

public section

namespace CFSG.Sporadic.Recognition.Fi22Multiplier

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_cons evalWord_nil)
open CFSG.Sporadic.Th CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native
open CFSG.Sporadic.Fi22 (a b J orb rep_alpha rep_beta actionChecks_parts closure_ab fi22EquivJ)
open CFSG.YGroups (YGroup yGen yRels yModelHom yModelHom_yGen)
open CFSG.Sporadic.Recognition.YCover

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Rho


theorem wordProd_append_eq (x : ℕ → J) (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp [wordProd]

theorem rep_alpha_inv' : Rep 3510 orb.alpha a⁻¹ := by
  rw [CFSG.Sporadic.Fi22.a_inv]
  exact rep_alpha

theorem rho_rels_eval :
    ∀ v ∈ fi22RhoRels, wordProd (img2 a b) v = 1 :=
  wordProd_eq_one_of_relCheck (n := 3510) (by norm_num) rep_alpha rep_alpha_inv' rep_beta
    (Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1)
    Certificates.certificate24051

@[expose] noncomputable def gen332 (c : ℕ) : J := wordProd (img2 a b) (fi22Letter c)

theorem evalWord_gen332 (w : List ℕ) :
    evalWord gen332 w = wordProd (img2 a b) (expandWord w) := by
  induction w with
  | nil => simp [evalWord, expandWord, wordProd]
  | cons c w ih =>
    rw [evalWord_cons, ih]
    unfold expandWord
    rw [List.flatMap_cons, wordProd_append_eq]
    rfl

theorem gen332_rels : ∀ w ∈ yRels 3 3 2, evalWord gen332 w = 1 := by
  intro w hw
  rw [evalWord_gen332]
  refine rho_rels_eval _ ?_
  unfold fi22RhoRels
  exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨w, hw, rfl⟩))

@[expose] noncomputable def rhoY : YGroup 3 3 2 →* J :=
  yModelHom gen332 gen332_rels

theorem rhoY_yGen {c : ℕ} (hc : c < 9) :
    rhoY (yGen 3 3 2 c) = gen332 c :=
  yModelHom_yGen hc

theorem rhoY_evalWord (w : List ℕ) (hw : ∀ c ∈ w, c < 9) :
    rhoY (evalWord (yGen 3 3 2) w) = evalWord gen332 w := by
  rw [map_evalWord' rhoY]
  exact CFSG.YGroups.evalWord_congr fun c hc => rhoY_yGen (hw c hc)

theorem rhoY_F : rhoY F332 = 1 := by
  rw [F332_eq, rhoY_evalWord _ (by decide), evalWord_gen332]
  refine rho_rels_eval _ ?_
  unfold fi22RhoRels
  exact List.mem_append.2 (Or.inr List.mem_cons_self)

@[expose] noncomputable def rho332 : R332 →* J :=
  QuotientGroup.lift _ rhoY (Subgroup.normalClosure_le_normal (by
    simpa [MonoidHom.mem_ker] using rhoY_F))

theorem rho332_quotMk (x : YGroup 3 3 2) :
    rho332 (quotMk F332 x) = rhoY x := rfl

set_option maxRecDepth 100000 in
theorem rho332_surjective : Function.Surjective rho332 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · refine ⟨quotMk F332 (yGen 3 3 2 0), ?_⟩
    rw [rho332_quotMk, rhoY_yGen (by norm_num)]
    simp [gen332, fi22Letter, fi22Words, fi22Code, wordProd, img2]
  · refine ⟨quotMk F332 (evalWord (yGen 3 3 2) fi22BWord), ?_⟩
    rw [rho332_quotMk, rhoY_evalWord _ (by decide), evalWord_gen332]
    have h := rho_rels_eval (expandWord fi22BWord ++ [(1, false)]) (by
      unfold fi22RhoRels
      exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    have hb1 : wordProd (img2 a b) [(1, false)] = b⁻¹ := by simp [wordProd, img2]
    rw [wordProd_append_eq, hb1] at h
    exact mul_inv_eq_one.1 h

@[expose] noncomputable def rhoFi22 :
    R332 →* CFSG.Blueprint.NativeSporadic.Fi22 :=
  (fi22EquivJ.symm : J →* CFSG.Blueprint.NativeSporadic.Fi22).comp rho332

theorem rhoFi22_surjective : Function.Surjective rhoFi22 :=
  fi22EquivJ.symm.surjective.comp rho332_surjective

theorem nonempty_mulEquiv_R332_of_doubleCover
    {D : Type} [Group D] (φ : D →* CFSG.Blueprint.NativeSporadic.Fi22)
    (hφ : Function.Surjective φ) (hperf : Group.IsPerfect D) (hk : Nat.card φ.ker = 2) :
    Nonempty (D ≃* R332) := by
  obtain ⟨hY, h1⟩ := identities_of_Y flagData332 (F := F332) rfl rhoFi22 y332Conj y332_I2
    y332_I1
  have : Finite R332 := card_R332_le.1
  have hcard : Nat.card R332 ≤ 2 * Nat.card CFSG.Blueprint.NativeSporadic.Fi22 := by
    rw [CFSG.Sporadic.Fi22.card_Fi22]
    exact card_R332_le.2
  exact nonempty_mulEquiv_quot_of_doubleCover flagData332 (F := F332) rfl rhoFi22_surjective
    y332Conj_lt hY h1 hcard φ hφ hperf hk

end Rho

end CFSG.Sporadic.Recognition.Fi22Multiplier
