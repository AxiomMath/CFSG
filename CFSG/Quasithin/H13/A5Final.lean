module

public import CFSG.Quasithin.H13.A5Global
public import CFSG.Quasithin.H13.A5S1515c
public import CFSG.Quasithin.H13.VolIC113
public import CFSG.Quasithin.H13.VolIF956

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint
open scoped commutatorElement

@[expose] def Stmt13_2_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)

theorem isQuasisimple_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ∃ a b : Q, a * b ≠ b * a) : CFSG.IsQuasisimple Q := by
  obtain ⟨a, b, hab⟩ := hQ
  have hc : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exact absurd ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a) hab
  let e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hne : e.symm a * e.symm b ≠ e.symm b * e.symm a := by
    rw [← map_mul, ← map_mul]
    exact fun h => hab (e.symm.injective h)
  have : Nontrivial (Q ⧸ Subgroup.center Q) :=
    ⟨⟨e.symm a, e.symm b, fun h => hne (by rw [h])⟩⟩
  refine ⟨⟨?_⟩, IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective,
    e.symm a, e.symm b, hne⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isQuasisimple_L : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨φ, hφ, hker⟩ := S.a5
  have hk : φ.ker = CFSG.pCore 2 ↥L := hker.trans (openPCore_eq_pCore' 2 ↥L)
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  refine (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 ?_
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  refine isQuasisimple_of_simple ⟨⟨finRotate 5, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 0 2, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · rw [Equiv.Perm.mem_alternatingGroup]
    decide
  · intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_mul] at this
    revert this
    decide

theorem conjClosure_L_T : conjClosure L T = L := by
  apply le_antisymm
  · exact conjClosure_le fun t ht x hx => (Subgroup.mem_normalizer_iff.mp (S.T_le_NL ht) x).mp hx
  · exact le_conjClosure L T

theorem z_mem_omegaOneCenter : S.z ∈ quasithinOmegaOneCenter T := by
  refine Subgroup.subset_closure ⟨⟨S.V_le_T S.z_mem_V, ?_⟩, S.z_sq⟩
  show S.z ∈ Subgroup.centralizer (T : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have := S.conj_z_of_mem_T ht
  calc t * S.z = t * S.z * t⁻¹ * t := by group
    _ = S.z * t := by rw [this]

end Setting

theorem input1336_of (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) : Input1336 := by
  intro G _ _ T L V S hle
  obtain ⟨-, -, ⟨H, hH⟩, -, -⟩ := (h331 G T S.h13.simple S.h13.nonabelian S.h13.qtke
    S.h13.sylow).2 L S.maximal S.isQuasisimple_L
  rw [S.conjClosure_L_T] at hH
  have hHZ := h1327 G T L V S H hH
  apply hH.2.1
  refine le_trans ?_ hle
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp (hHZ hx) S.z S.z_mem_omegaOneCenter
  show x ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact this.symm

theorem stmt13_6_1_of_ext
    (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) (hG248 : StmtG248)
    (h13518 : Input13518) (h136 : Input136) (hF112 : F112Statement) (hF431 : StmtF431U42) :
    Stmt13_6_1 := by
  have h1323 := input1323Two_of h311 h1222
  have h1326 := input1326Two_of h1222 h517
  have h1336 := input1336_of h331 h1327
  exact stmt13_6_1_of_inputs h132two h132fsu h132A5 h1323 h1336
    (input13515_of h1323 h1326 h1336 VolI.stmtF956i hG248 VolI.stmtC113c) h13518 h136 hF112
    hF431

end CFSG.Quasithin.H13.A5
