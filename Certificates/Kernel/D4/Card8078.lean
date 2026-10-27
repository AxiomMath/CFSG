module

public import CFSG.Quasithin.Recognition.CertTrialityFaithful
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import Certificates.Kernel.D4.LinkFacts

public section

namespace CertificateChecks.KernelD4

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.KC.D4Link CFSG.KS.Raw
open scoped LinearAlgebra.Projectivization Matrix

@[expose] def witWords8078 : List (List ℕ) :=
  [[], [1, 9], [16, 17, 1, 9], [1, 16, 9, 17, 1, 9], [16, 17, 1, 16, 9, 17, 1, 9],
    [1, 16, 9, 17, 1, 16, 9, 17, 1, 9], [16, 9, 17, 1, 9], [16, 14, 17, 1, 9], [9], [16, 17, 9],
    [1, 9, 17, 9], [16, 17, 1, 9, 17, 9], [17, 1, 9, 17, 9, 17, 9], [9, 17, 9], [14, 17, 1, 9]]

@[expose] def pk8078 (l : List ℕ) : ℕ := l.foldr (fun d a => d + 8 * a) 0

@[expose] noncomputable def evalK8078 : List ℕ → Option ℕ
  | [] => some 1
  | l :: w =>
    match evalK8078 w with
    | some V => if decide (l < 18) && validK (actK LG l V) then some (actK LG l V) else none
    | none => none

theorem witChk8078 :
    ∀ t : Fin 15, evalK8078 (witWords8078.getD t []) = some (pk8078 (faithDigits.getD t [])) := by
  decide +kernel

theorem witChk8078_neg : evalK8078 [18] = none ∧
    evalK8078 [9, 1] ≠ some (pk8078 (faithDigits.getD 1 [])) := by
  decide +kernel

theorem vget_pk8078 : ∀ t : Fin 15, ∀ j : Fin 8,
    GF8.ofNat' (vget (pk8078 (faithDigits.getD t [])) j) = wv t j := by
  decide +kernel

theorem rootV_eq8078 : rootV = unpack 8 3 1 := by
  rw [root_eq, Nat.eq_of_beq_eq_true root]

theorem evalK8078_spec {w : List ℕ} {V : ℕ} (h : evalK8078 w = some V) :
    validV (unpack 8 3 V) = true ∧ (∀ l ∈ w, l < 18) ∧
      decL (unpack 8 3 V) = wordGL w • decL rootV := by
  induction w generalizing V with
  | nil =>
    simp only [evalK8078, Option.some.injEq] at h
    subst h
    refine ⟨?_, by simp, ?_⟩
    · rw [validV_eq]
      decide +kernel
    · rw [← rootV_eq8078]
      simp [wordGL]
  | cons l w ih =>
    cases hw : evalK8078 w with
    | none => simp [evalK8078, hw] at h
    | some U =>
      simp only [evalK8078, hw] at h
      obtain ⟨hu, hl, hdu⟩ := ih hw
      split_ifs at h with hc
      · rw [Option.some.injEq] at h
        subst h
        rw [Bool.and_eq_true, decide_eq_true_eq] at hc
        have hpa := projAct_eq (gmK l hc.1) U
        refine ⟨by rw [validV_eq]; exact hc.2, ?_, ?_⟩
        · intro m hm
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hc.1
          · exact hl m hm
        · rw [← hpa, decL_projAct hc.1 hu, hdu, ← mul_smul]
          simp [wordGL]

theorem d4Rho_eq_rho8078 :
    (d4Rho : lineGroup →* Equiv.Perm (Fin 2457)) = rho d4_link_check.1 d4_link_check.2.1 := by
  have hS : Subgroup.closure (((↑) : lineGroup → GL (Fin 8) GF8) ⁻¹' (letterGL '' {k | k < 18})) =
      ⊤ := Subgroup.closure_closure_coe_preimage
  refine MonoidHom.eq_of_eqOn_dense hS ?_
  rintro s ⟨k, hk, hks⟩
  have hk' : k < 18 := hk
  have hs : s = letterX k := Subtype.ext (by simp [letterX, hk', hks])
  subst hs
  exact (rep_d4Rho_letter hk').unique (rep_piArr d4_link_check.1 d4_link_check.2.1 hk')

theorem eq_one_of_d4Rho_eq_one (g : lineGroup) (hg : d4Rho g = 1) : g = 1 := by
  have hc := d4_link_check.1
  have hsize := d4_link_check.2.1
  have hfix : ∀ i : Fin 2457, (g : GL (Fin 8) GF8) • ptL lineCert i = ptL lineCert i := by
    intro i
    have h := ptL_rho hc hsize g i
    have h1 : rho hc hsize g = 1 := by rw [← d4Rho_eq_rho8078]; exact hg
    rw [h1] at h
    exact h.symm
  have horb : ∀ x ∈ MulAction.orbit lineGroup (decL rootV), (g : GL (Fin 8) GF8) • x = x := by
    rw [orbit_ptL hc]
    rintro _ ⟨i, hi, rfl⟩
    exact hfix ⟨i, hsize ▸ hi⟩
  have key : ∀ t : Fin 15, ∃ c : GF8,
      ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) *ᵥ wv t = c • wv t := by
    intro t
    obtain ⟨hv, hw, hdec⟩ := evalK8078_spec (witChk8078 t)
    have hmem : decL (unpack 8 3 (pk8078 (faithDigits.getD t []))) ∈
        MulAction.orbit lineGroup (decL rootV) := by
      refine ⟨wordX (witWords8078.getD t []), ?_⟩
      change (wordX (witWords8078.getD t []) : lineGroup) • decL rootV = _
      rw [Subgroup.smul_def, coe_wordX hw, hdec]
    have hfx := horb _ hmem
    obtain ⟨-, -, hne, -⟩ := validV_spec hv
    unfold decL at hfx
    rw [dif_pos hne] at hfx
    obtain ⟨c, hc⟩ := exists_eigen_of_fixed_line _ _ hne hfx
    have hvec : vecOf (unpack 8 3 (pk8078 (faithDigits.getD t []))) = wv t := by
      funext j
      simp only [vecOf]
      rw [unpack_get8 _ j.2]
      exact vget_pk8078 t j
    exact ⟨c, by rw [← hvec]; exact hc⟩
  have hmem : (g : GL (Fin 8) GF8) ∈ trialityGroup8 := lineGroup_eq ▸ g.2
  exact Subtype.ext (eq_one_of_fixes_wv hmem key)

theorem card8078 : Nat.card trialityGroup8 = 211341312 := by
  have hinj : Function.Injective (d4Rho : lineGroup →* Equiv.Perm (Fin 2457)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    exact (Subgroup.mem_bot).2 (eq_one_of_d4Rho_eq_one g hg)
  have h1 : Nat.card lineGroup = Nat.card d4Rho.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← lineGroup_eq, h1, d4Rho_range, card_d4P]

end CertificateChecks.KernelD4
