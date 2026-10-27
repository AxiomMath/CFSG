module

public import CFSG.Quasithin.Vol2.Ch11SecC37Set
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem eq_commutator_thompsonJ (hC58 : TheoremC58) (h317 : AS317Sylow)
    (hFC : SecB.FactCentralizerTwo) (h1102 : Stmt11_0_2) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h331 : Stmt3_3_1) : L = ⁅L, thompsonJ T⁆ := by
  have hJ : ¬ thompsonJ T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L I s.hyp.fsu
    rw [SecA.fsuL0_eq s.hyp] at hVLT hVred hcent
    have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L (fsuV T I) :=
      { inM := ⟨SecA.isMaxTwoLocal_M h331 s.hyp, s.hyp.normal⟩
        nonempty := ⟨H, s.h31.hstar⟩
        perfect := (C2Nine.oTwoUpper_eq_of_perfect s.hyp.fsu.faithful.1.2.1.2.1).symm
        le_M := Subgroup.le_normalizer
        normal := le_rfl
        unique := SecA.isUniqueM_LT h331 s.hyp
        reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
        centralizer := hcent }
    rcases theorem318_three hC58 h317 s.hyp.fsu.simple s.hyp.fsu.nonabelian s.hyp.fsu.qtke
        s.hyp.fsu.sylow h318 with h | ⟨-, hZ, -⟩
    · exact h.1
    · exfalso
      apply s.h31.moves
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact fun z hz => (hZ H s.h31.hstar hz).2
  exact SecB.eq_commutator_thompsonJ hFC h1102 s.hyp hJ

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
