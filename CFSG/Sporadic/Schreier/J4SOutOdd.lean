module

public import CFSG.Sporadic.Schreier.J4SSylow11
public import CFSG.Sporadic.Schreier.J4SOutGen
public import CFSG.Sporadic.Schreier.J4SOddInner
public import CFSG.Sporadic.SmallOddCore.Assembly

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.SectionRank CFSG.SectionRank.Native
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

theorem qu_pow_eight :
    qu ^ 8 = 1 := pow_eq_one_of_rep_check rep_qu sixteen_check.1

theorem qw_sq : qw ^ 2 = 1 := by
  rw [sq]
  exact eq_of_rep_check (rep_mulP rep_qw rep_qw) rep_oneP sixteen_check.2.1

theorem qw_qu :
    qw * qu * qw⁻¹ = qu ^ 3 :=
  conj_of_rep_check rep_qw rep_qu (rep_powP rep_qu 3) sixteen_check.2.2.1

theorem sixteen_inj :
    Function.Injective fun t : Fin 8 × Fin 2 =>
    qu ^ (t.1 : ℕ) * qw ^ (t.2 : ℕ) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij
  dsimp only at hij
  have hm := congrArg φ hij
  rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_pow] at hm
  have hnf := sixteen_check.2.2.2
  unfold sixteenOK at hnf
  have hsz : (Array.ofFn (n := 16) fun t => O.appBase 8 [U8n.1, W2n.1] t.val (O.unit 0)).size =
      16 := by
    simp
  have hvs : ∀ n < 16, Sp.toVec (Array.ofFn (n := 16) fun t =>
      O.appBase 8 [U8n.1, W2n.1] t.val (O.unit 0))[n]! = Sp.toVec (O.unit 0) ᵥ*
        (Sp.toMat U8n.1 ^ (n % 8) * Sp.toMat W2n.1 ^ (n / 8 % 8)) := by
    intro n hn
    rw [getElem!_pos _ n (by rw [hsz]; exact hn), Array.getElem_ofFn]
    exact Sp.appBase_two rep_qu.1 rep_qw.1 8 n (Sp.unit_wf 0)
  have hcode : ∀ (i : Fin 8) (j : Fin 2), (i + 8 * j : ℕ) < 16 ∧ (i + 8 * j : ℕ) % 8 = i ∧
      (i + 8 * j : ℕ) / 8 % 8 = j := by
    intro i j
    have := i.isLt
    have := j.isLt
    omega
  obtain ⟨c1, c2, c3⟩ := hcode i j
  obtain ⟨c1', c2', c3'⟩ := hcode i' j'
  by_contra hne
  have hcne : (i + 8 * j : ℕ) ≠ i' + 8 * j' := by
    intro hc
    apply hne
    have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
    have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
  rw [hvs _ c1, hvs _ c1', c2, c3, c2', c3', rep_qu.2.2.1, rep_qw.2.2.1]
  exact congrArg (fun M => Sp.toVec (O.unit 0) ᵥ* M) hm

theorem card_R16 :
    Nat.card (Subgroup.closure ({qu, qw} : Set J)) = 16 :=
  @card_closure_metacyclic J (Subgroup.toGroup J) qu qw 8 3 (by norm_num) qu_pow_eight qw_sq qw_qu
    sixteen_inj

theorem R16_le_normalizer :
    Subgroup.closure ({qu, qw} : Set J) ≤ Subgroup.normalizer (Q11 : Set J) := by
  have hQN : Q11 ≤ Subgroup.normalizer (Q11 : Set J) := Subgroup.le_normalizer
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact Subgroup.pow_mem _ nrm₂_mem_normalizer 5
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (hQN qx_mem) 3) (Subgroup.pow_mem _ (hQN qy_mem) 9)) (hQN qz_mem)) ?_
    exact signedWord_mem _ nrm₁_mem_normalizer nrm₂_mem_normalizer _

theorem sixteen_dvd_card_normalizer :
    16 ∣ Nat.card (Subgroup.normalizer (Q11 : Set J)) := by
  rw [← card_R16]
  exact Subgroup.card_dvd_of_le R16_le_normalizer

theorem center_J :
    Subgroup.center J = ⊥ := by
  have := isSimpleGroup_J j4Facts
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    have hx : qx ∈ Subgroup.center J := by rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_center_iff] at hx
    apply qz_ne_one
    rw [qz, commutatorElement_def, ← hx qy, mul_inv_cancel_right, mul_inv_cancel]

theorem factorization_two_normalizer :
    (Nat.card (MulAut Q11)).factorization 2 ≤
      (Nat.card (Subgroup.normalizer (Q11 : Set J))).factorization 2 := by
  refine (factorization_two_card_mulAut isExtraspecial_Q11 card_Q11).trans ?_
  have h := (Nat.factorization_le_iff_dvd (by norm_num) Nat.card_pos.ne').2
    sixteen_dvd_card_normalizer 2
  rwa [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same] at h

theorem CTU_J4_outer_automorphism_group_odd_order :
    Odd (Nat.card (Outer J)) := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact @odd_card_outer_of_sylow J (Subgroup.toGroup J) _ center_J 11 _ Q11Sylow
    odd_card_pointwiseFixingAut_Q11 factorization_two_normalizer

theorem CTU_J4_full_group_involution_odd_core
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (ψ : CFSG.generalizedFitting X ≃* J) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hC := SmallOddCore.centralizer_generalizedFitting_eq_bot hF hnab
  have hsq : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hmem : t ∈ CFSG.generalizedFitting X :=
    @mem_of_sq_eq_one_of_odd_outer X _ _ _ J (Subgroup.toGroup J) ψ hC
      CTU_J4_outer_automorphism_group_odd_order t hsq
  exact CTU_J4_full_group_inner_involution_odd_core hF hnab ψ ⟨t, hmem⟩ ht

end CFSG.Sporadic.J4Schreier
