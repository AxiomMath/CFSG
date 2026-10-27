module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNbr
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUInnerDiag
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSULeaves
public import CFSG.LocalAnalysis.StandardType.GGSixTCMarkDict
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUBlockDeg

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem false_of_splitModel_PSU
    {X : Type} [Group X] {p g r : ℕ} {L : Subgroup X}
    (hsplit : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab))
    (hp : ¬ p ∣ 2 ^ (g + 1) + 1) (hr : 5 ≤ r)
    (hmodel : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU r 2 (g + 1)) : False := by
  obtain ⟨lab, hlab, hQ, hM⟩ := exists_label_of_marking_tc hsplit
  have hrk : 2 ≤ (ggU .PSU r (g + 1)).D.rank := by
    rw [ggU_PSU_rank r (g + 1) (by omega)]
    omega
  obtain ⟨ht, hk, hc, hg⟩ := markData_of_lieModel hlab hM (Or.inr (Or.inl rfl))
    hmodel.admissible hrk hmodel
  rcases split_of_markTag_PSU ht hk hc hg hr hQ with h | ⟨h1, h2⟩
  · exact hp h
  · apply hp
    rw [h1, h2]
    decide

theorem false_of_halfSplitModel_PSU
    {X : Type} [Group X] {p g r : ℕ} {K : Subgroup X}
    (hhs : LargeEvenMarking ↥K (fun lab _ _ _ _ _ =>
      LargeEvenHalfSplit p lab (Subgroup.center ↥K = ⊥)))
    (hp : ¬ p ∣ 2 ^ (g + 1) + 1) (hp1 : ¬ p ∣ 2 ^ (g + 1) - 1) (hr : 5 ≤ r)
    (hmodel : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSU r 2 (g + 1)) : False := by
  obtain ⟨lab, hlab, hQ, hM⟩ := exists_label_of_marking_tc hhs
  have hrk : 2 ≤ (ggU .PSU r (g + 1)).D.rank := by
    rw [ggU_PSU_rank r (g + 1) (by omega)]
    omega
  obtain ⟨ht, hk, hc, hg⟩ := markData_of_lieModel hlab hM (Or.inr (Or.inl rfl))
    hmodel.admissible hrk hmodel
  rcases halfSplit_of_markTag_PSU ht hk hc hg hr hQ with h | ⟨h1, h2⟩ | ⟨-, h⟩
  · exact hp h
  · apply hp
    rw [h1, h2]
    decide
  · exact hp1 h

theorem false_of_not_dvd_PSU_of_models
    {X : Type} [Group X] [Finite X] {n p : ℕ} {G₀ B D J L : Subgroup X} {x : X} {g : ℕ}
    {ψ : (ggU .PSU n (g + 1)).K →* X} (h : GGTCHyp .PSU n (g + 1) ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSU (g + 1)) (hp : ¬ p ∣ 2 ^ (g + 1) + 1)
    (hM1 : ∀ {S : Set (GL (Fin n) (PSUF g))} {ε e : Matrix (Fin n) (Fin n) (PSUF g)}
      {J' : Subgroup ↥(Unitary.SU (PSUσ g) n)}, PSUBlock ψ B S ε e → e ≠ ε →
      IsComponentOf J'
        ⁅glBlockCentralizer (PSUj n g) S ε, glBlockCentralizer (PSUj n g) S ε⁆ →
      J'.map ψ = J → 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e)
    (hM2 : p ∣ Nat.card J) : False := by
  classical
  have hH := PSULiftHyp.of_ggTCHyp h
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h.range]
    exact h.j_comp
  obtain ⟨S, ε, e, J', hS, hb, -, hJ'g, hJ'm⟩ := hH.exists_block h.d_le hJ
  have hd : 2 ≤ blockDegree (Algebra.adjoin (PSUF g) (Units.val '' S)) e := by
    by_cases hself : e = ε
    · exact hb.two_le_blockDegree_of_selfDual hH hself h.d_card h.j_cent hJ'g hJ'm hF
    · exact hM1 hb hself hJ'g hJ'm
  have hpF : ¬ p ∣ Nat.card (PSUF g)ˣ := hb.not_dvd_units_card_of_two_le hH hp hd
  have hp1 : ¬ p ∣ 2 ^ (g + 1) - 1 := by
    intro h1
    apply hpF
    rw [Nat.card_units, card_PSUF]
    have : 2 ^ (g + 1) - 1 ∣ (2 ^ (g + 1)) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ (g + 1)) 1 2
    exact h1.trans this
  have hSD : ∀ d ∈ D, ∀ s ∈ psuE ψ B, IsGLLift (PSUj n g) ψ s d → s ∈ S :=
    fun d hd' s hs hsl => (hS s).mpr ⟨hs.1, d, hd', hsl⟩
  have hperf : ⁅J, J⁆ = J := tcCommutator_self_of_isQuasisimple hJ.2.2
  have hne : J ≠ ⊥ := tcNe_bot_of_isQuasisimple hJ.2.2
  have hxB : x ∈ B := h.d_le h.x_mem
  have hspecx := hH.lam_spec hp hxB
  by_cases hxe : ((hH.lam hp ⟨x, hxB⟩ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      e = e
  ·
    obtain ⟨T, -, -, -, hrank, -, hYm, hJY, -, hmodel⟩ := hH.exists_avgY hp hpF hb h.d_le
      h.d_card h.j_cent hSD hJ'g hJ'm hd h.x_mem hxe
    have hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer ({x} : Set X)) := by
      rw [h.range]
      exact h.l_comp
    have hLeq : L = (PSUYsd n g T).map ψ :=
      isComponentOf_eq_of_perfect_le hYm hL hJY h.j_le_l hperf hne
    have hmodel' : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU (Matrix.rank T) 2
        (g + 1) := by
      rw [hLeq]
      exact hmodel
    exact false_of_splitModel_PSU h.l_split hp (by omega) hmodel'
  ·
    obtain ⟨g₀, hg₀D, -, hg₀x, hg₀e⟩ := hb.exists_mem_ker hH hp h.d_le h.d_card hSD h.x_mem hxe
    obtain ⟨T, hTid, hTa, hTc, hrank, -, hYm, hJY, -, hmodel⟩ := hH.exists_avgY hp hpF hb
      h.d_le h.d_card h.j_cent hSD hJ'g hJ'm hd hg₀D hg₀e
    have hK : IsComponentOf ((PSUYsd n g T).map ψ)
        (G₀ ⊓ Subgroup.centralizer ({g₀} : Set X)) := by
      rw [← h.range]
      exact hYm
    have hKJ : (PSUYsd n g T).map ψ ≠ J := by
      intro heq
      apply false_of_fieldExt_of_model_PSU (J := J) (r := Matrix.rank T) (by omega) _ hF
      rw [← heq]
      exact hmodel
    have hcomm : (hH.lam hp ⟨x, hxB⟩ : GL (Fin n) (PSUF g)) *
        (hH.lam hp ⟨g₀, h.d_le hg₀D⟩ : GL (Fin n) (PSUF g)) =
        (hH.lam hp ⟨g₀, h.d_le hg₀D⟩ : GL (Fin n) (PSUF g)) *
        (hH.lam hp ⟨x, hxB⟩ : GL (Fin n) (PSUF g)) :=
      (hH.commute_lifts hxB (h.d_le hg₀D) (hH.lam_spec hp hxB).2.1
        (hH.lam_spec hp (h.d_le hg₀D)).2.1).eq
    have hinn := innerDiagOn_map_PSUYsd hH.ker hH.adm hTid hTa (by omega) hspecx.1.1
      hspecx.2.1 (hTc _ hcomm)
    have hnbr := h.nbr g₀ hg₀D hg₀x _ hK (hJY) hKJ hM2 hinn
    exact false_of_halfSplitModel_PSU hnbr hp hp1 (by omega) hmodel

end CFSG.StandardType.TableCRes
