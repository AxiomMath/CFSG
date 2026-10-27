module

public import CFSG.Quasithin.H13.NQS13412G
public import CFSG.Quasithin.H13.U3S1349G
public import CFSG.Quasithin.H13.NQS134108G
public import CFSG.Quasithin.H13.NQS13412D
public import CFSG.Quasithin.H13.NQS13412F

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

theorem wt6_e45 : (Finset.univ.filter fun i : Fin 6 =>
    Multiplicative.toAdd (e45 : G6.PermMod 6) i = 1).card = 2 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem side (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2) (h1345 : Stmt13_4_5)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) :
    ∃ H₂ : Subgroup G, (SideI S z H₂ ∨ SideII S z H₂) ∧
      ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X →
        X ≤ centralizer ({z} : Set G) → X = H₂ := by
  obtain ⟨-, hHKT, hHGz, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  have hGzKT : centralizer ({z} : Set G) = K ⊔ T := hHGz.symm.trans hHKT
  obtain ⟨H₂, hstar, hH₂KT, huniq, -⟩ := D.exists_h2 hC137 h1332 h1228 hC58 h317 h56 he hnhat
  have hH₂H : H₂ ≤ H := hHKT ▸ hH₂KT
  obtain ⟨hq, hcls, hinc1, hinc2, hcZ, -⟩ :=
    D.eight_setup hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H
  have hside : Side S z H₂ :=
    { zV1 := D.zV1
      zL := D.zL
      L1T := D.L1TH.trans D.Hz
      star := hstar
      le_Gz := hH₂H.trans D.Hz
      quot := hq
      cls := hcls
      inc1 := hinc1
      inc2 := hinc2
      cZ := hcZ }
  refine ⟨H₂, ?_, fun X hX hXz => huniq X hX (hGzKT ▸ hXz)⟩
  obtain ⟨-, hcases⟩ :=
    D.eight hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 h1345 he hnhat hstar hH₂H
  obtain ⟨hVKW, -, -, -, -, -⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  rcases hcases with ⟨hi, hwt, hZV, -⟩ | ⟨-, hnj, hinM, huniq0⟩
  · refine Or.inl ⟨hside, hi, fun hz => ?_,
      D.chief_h2 hC137 h1332 h1228 hC58 h317 h56 he hnhat hstar hH₂H, ?_⟩
    · rcases D.psi_z_cases with h | h
      · exact h
      · exfalso
        change (Finset.univ.filter fun i : Fin 6 =>
          Multiplicative.toAdd (S.frame.ψ ⟨z, D.zV1.1⟩ : G6.PermMod 6) i = 1).card = 4 at hwt
        rw [h, wt6_e45] at hwt
        exact absurd hwt (by decide)
    · intro X hX hzX zb hzb hzbL hzbz Y hTY hYX hYzb hYM
      exact D.false_of_le hC137 h1332 h1228 hC58 h317 h56 he hnhat (hVKW ▸ hZV) hX
        (D.Kz.trans hzX) hzb hzbL hzbz hTY hYX hYzb hYM
  · have h0 : h0Of S H₂ = H₂ ⊔ (U3.l2Of S ⊔ T) := sup_comm _ _
    rw [h0] at hnj hinM huniq0
    exact Or.inr ⟨hside, hnj, hinM, huniq0⟩

end Data13410

theorem sideII_of_solvable (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h56 : AsB56) (h1347 : U3.Stmt13_4_7L2) (h1348 : U3.Stmt13_4_8)
    (h1345 : Stmt13_4_5) (S : A6.Setting134 G T L V) {z : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G))
    (hCz : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable ↥(centralizer ({z} : Set G))) :
    ∃ H₁ : Subgroup G, SideII S z H₁ := by
  obtain ⟨H₁, hstar, hH₁z, -, hq, hcls, hinc1, hinc2, hcZ, hInH0, hH0M, hii, hmax⟩ :=
    U3.s134_solvable_Gz_data h1222 h1332 hC58 h317 h56 h1347 h1348 S hz hzL hCz hsol
  have hTM : T ≤ normalizer (L : Set G) := S.T_le_NL
  have hL2TM : U3.l2Of S ⊔ T ≤ normalizer (L : Set G) :=
    sup_le ((U3.s134_L2_le_L S).trans le_normalizer) hTM
  obtain ⟨-, h2T, -, -⟩ := U3.s134_parabolics S
  have hZcard := U3.s134_card_Z h1332 hC58 h317 h56 S ⟨_, hInH0, hH0M⟩
  have hL2H₁ : ¬ U3.l2Of S ⊔ T ≤ H₁ := by
    intro h
    apply hzL
    have hzc : z ∈ U3.cZ T (U3.l2Of S ⊔ T) :=
      mem_inf.2 ⟨hz.2, U3.mem_centralizer_of_le_centralizer (h.trans hH₁z)⟩
    rw [U3.s134_cZ_L2T S hZcard] at hzc
    exact (mem_inf.1 hzc).2
  obtain ⟨hnj, hinM, huniq0⟩ := eight_ii S h1345 hstar hL2TM h2T hL2H₁ hInH0 hH0M hii hmax
  exact ⟨H₁, ⟨⟨hz, hzL, U3.s134_L1T_le_Gz S hz, hstar, hH₁z, hq, hcls, hinc1, hinc2, hcZ⟩,
    hnj, hinM, huniq0⟩⟩

theorem NZ134.side (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2) (h1345 : Stmt13_4_5)
    (h1346 : Stmt13_4_6) {z : G} (N : NZ134 G T L V z) :
    quasithinOmegaOneCenter T = fsuV1 T V ∧ Nat.card ↥(quasithinOmegaOneCenter T) = 4 ∧
      ∃ H₂ : Subgroup G, (SideI N.S z H₂ ∨ SideII N.S z H₂) ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X →
          X ≤ centralizer ({z} : Set G) → X = H₂ := by
  have hHz := N.inHz h1332 hC58 h317 h56
  obtain ⟨K, hK⟩ := exists_mem_cComp N.nsolv
  obtain ⟨W, _, D⟩ := exists_data13410 h1345 h1346 N.S N.zV1 N.zL hHz N.nsolv hK
  have hnhat := D.not_hat hC137 h1332 h1228 hC58 h317 h56
  have he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨h5, -, -, -⟩ := h1332 G T L N.S.h13 L N.S.h13.faithful
    exact (U3.a6_or_hatA6_of_isA6On N.S.frame.L_le (U3.s134_pCoreOf_L_le N.S) h5
      (U3.s134_isA6On N.S)).resolve_right hnhat
  obtain ⟨-, -, -, -, -, hZ4, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  exact ⟨hZV1, hZ4, D.side hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 h1345 he hnhat⟩

theorem stmt13_4_12_of (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347One : U3.Stmt13_4_7One)
    (h1347 : U3.Stmt13_4_7L2) (h1348 : U3.Stmt13_4_8) (h1345 : Stmt13_4_5)
    (h1346 : Stmt13_4_6) : Stmt13_4_12 := by
  intro G _ _ T L V z N
  obtain ⟨hZV1, hZ4, H₂, hside, huniq⟩ :=
    N.side hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 h1345 h1346
  have hA : Side N.S z H₂ := by
    rcases hside with A | A
    · exact A.side
    · exact A.side
  refine ⟨⟨hZV1, hZ4, fun z' hz' hz'1 hz'M => ?_⟩, H₂, hA.star, hA.le_Gz, huniq⟩
  by_contra hne
  have hzz' : z ≠ z' := fun h => hne h.symm
  have hz'V1 : z' ∈ fsuV1 T V := hZV1 ▸ hz'
  have hz'L : z' ∉ centralizer (L : Set G) := by
    intro h
    rcases N.S.mem_ZV_iff.1 (mem_inf.2 ⟨hz'V1.1, h⟩) with h1 | h1
    · exact hz'1 h1
    · apply hz'M
      rw [h1]
      exact (N.S.centralizer_zV h1222).le
  by_cases hsol : Group.IsSolvable ↥(centralizer ({z'} : Set G))
  · obtain ⟨H', B⟩ :=
      sideII_of_solvable h1222 h1332 hC58 h317 h56 h1347 h1348 h1345 N.S hz'V1 hz'L hz'M hsol
    rcases hside with A | A
    · exact false_of_i_ii h1347One hZ4 A B hzz'
    · exact false_of_ii_ii A B hzz'
  · obtain ⟨-, -, H', hside', -⟩ := NZ134.side hC137 h1332 h1228 hC58 h317 h56 h1222 h1347
      h1345 h1346 (⟨N.S, hz'V1, hz'L, hz'M, hsol⟩ : NZ134 G T L V z')
    rcases hside with A | A <;> rcases hside' with B | B
    · exact false_of_i_i A B hzz'
    · exact false_of_i_ii h1347One hZ4 A B hzz'
    · exact false_of_i_ii h1347One hZ4 B A hne
    · exact false_of_ii_ii A B hzz'

end CFSG.Quasithin.H13.NQS134
