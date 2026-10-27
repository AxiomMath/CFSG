module

public import CFSG.Quasithin.Background.C124AsmEntry
public import CFSG.Quasithin.Background.C124AsmNormal
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C1GNNotation

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem concl1_of_baum_eq {X T V L R : Subgroup G} (hT : IsSylowTwoOf T X)
    (hred : IsTwoReducedIn X V) (hQR : pCoreOf 2 X ≤ R) (hRT : R ≤ T) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hb : baum R = baum (pCoreOf 2 X)) :
    ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
      X ≤ Subgroup.normalizer (C : Set G) := by
  have hR2 : IsPGroup 2 R := hT.2.1.to_le hRT
  have hR0 : R ≠ ⊥ := by
    intro hR
    apply hVL
    have hV0 : V = ⊥ := le_bot_iff.1 (hR ▸ (le_pCoreOf_of_reduced hred).trans hQR)
    rw [hV0, Subgroup.commutator_bot_left]
  refine ⟨baum R, C1GN.baum_ne_bot hR2 hR0, le_rfl, ?_, ?_⟩
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [hb]
    exact (le_normalizer_pCoreOf 2 X).trans (normalizer_le_normalizer_baum _)

theorem pCoreOf_eq_pCoreOf_inf {X V : Subgroup G} (hred : IsTwoReducedIn X V) :
    pCoreOf 2 X = pCoreOf 2 (X ⊓ Subgroup.centralizer (V : Set G)) := by
  have hQC : pCoreOf 2 X ≤ X ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (pCoreOf_le 2 X) (pCoreOf_le_centralizer hred)
  have hXC : X ≤
      Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun x hx => by
      rw [Subgroup.mem_normalizer_iff]
      intro c
      refine ⟨fun hc => ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
        conj_mem_centralizer_of_le hred.2.1 hx hc.2⟩, fun hc => ?_⟩
      have h1 := conj_mem_centralizer_of_le hred.2.1 (X.inv_mem hx) hc.2
      exact ⟨by simpa [mul_assoc] using X.mul_mem (X.mul_mem (X.inv_mem hx) hc.1) hx,
        by simpa [mul_assoc] using h1⟩
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 hQC (inf_le_left.trans (le_normalizer_pCoreOf 2 X))
      (pCoreOf_isPGroup 2 X)
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans inf_le_left)
      (hXC.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem entryPlus_or_concl1 (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) {X T V L R : Subgroup G} {m : ℕ} (hC : CharTwo X)
    (hSQ : SQTKGroup ↥X) (hred : IsTwoReducedIn X V) (hT : IsSylowTwoOf T X)
    (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hcomp : L ∈ cComp X) (hCL : CharTwo L)
    (hVL : ⁅V, L⁆ ≠ ⊥) (halt : IsAltQuotient L (oTwoZIn L) m) (hQR : pCoreOf 2 X ≤ R)
    (hRT : R ≤ T)
    (hm : m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ L ⊔ (X ⊓ Subgroup.centralizer (V : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R V) = 2)) :
    (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R ∧ (C.subgroupOf (baum R)).Characteristic ∧
        X ≤ Subgroup.normalizer (C : Set G)) ∨ EntryPlus X T V L R m hred.2.2.1 := by
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hm' : m = 5 ∨ m = 6 ∨ m = 7 := by omega
  have hLX : L ≤ X := le_of_mem_cComp hcomp
  have hn : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_prod hT hprod hcomp
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_altQuotient hcomp halt hm'
  obtain ⟨⟨hCsyl, hQC⟩, hqc, hF, hbranch⟩ :=
    B2_10_2 hV hred hQR hRT hT hLX hn hprod hVL (Or.inl hLq)
  have hVR : V ≤ R := (le_pCoreOf_of_reduced hred).trans hQR
  rcases hbranch with hb | ⟨hstab, hffle, hfstar⟩
  · exact Or.inl (concl1_of_baum_eq hT hred hQR hRT hVL hb)
  by_cases hJ : thompsonJ R ≤ Subgroup.centralizer (V : Set G)
  · refine Or.inl (concl1_of_baum_eq hT hred hQR hRT hVL ?_)
    have hJR : thompsonJ R ≤ R ⊓ Subgroup.centralizer (V : Set G) :=
      le_inf (thompsonJ_le_self R) hJ
    rw [← hQC] at hJR
    rw [baum_eq_baum_centralizer hV hVR (hQC ▸ hJR), hQC]
  right
  have hperf : Group.IsPerfect ↥(autI hV L) := by
    have : Group.IsPerfect ↥L := isPerfect_of_comm_eq (perfect_of_mem_cComp hcomp)
    exact Group.IsPerfect.ofSurjective (f := starHom hV L (hLX.trans hred.2.1))
      (starHom_surjective hV _)
  have hquasi : CFSG.IsQuasisimple ↥(autI hV L) := by
    rcases hqc with h | h3
    · exact h
    · exfalso
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic ↥(autI hV L) := isCyclic_of_prime_card h3
      have hnil : Group.IsNilpotent ↥(autI hV L) := inferInstance
      have : Nontrivial ↥(autI hV L) :=
        Finite.one_lt_card_iff_nontrivial.1 (by rw [h3]; norm_num)
      exact Group.IsPerfect.not_isNilpotent _ hnil
  have ho2 : pCoreOf 2 (autI hV L) = ⊥ := pCoreOf_autI_L_eq_bot hV hred hLX hn
  have hψ := exists_surj_alt_aux (hV := hV) hred hLX hn halt hquasi (by omega)
  obtain ⟨z, hzo, hzc⟩ := card_of_surj_alt hquasi ho2 (by omega) hψ
  have hcase1i := b51Case1i_ffJP hV hI hA21 hA36 hSQ hred.2.1 hLX hstab hfstar hquasi ho2 hm'
    hzo hzc
  have hCsyl' : IsSylowTwoOf (pCoreOf 2 X) (X ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [pCoreOf_eq_pCoreOf_inf hred]
    exact hCsyl
  exact
    { charTwo := hC, sqtk := hSQ, red := hred, sylow := hT, prod := hprod, comp := hcomp
      charTwoL := hCL, VL := hVL, alt := halt, QR := hQR, RT := hRT, mcase := hm, normal := hn
      QC := hQC, hJ := hJ, fstarX := hF, stab := hstab, ffJP_le := hffle, fstar := hfstar
      quasi := hquasi, o2 := ho2, card := ⟨z, hzo, hzc⟩, case1i := hcase1i, Lq := hLq
      Csyl := hCsyl' }

end CFSG.Quasithin.C124
