module

public import CFSG.Quasithin.Vol2.Ch11SecB24Basic
public import CFSG.Quasithin.Vol2.Ch11SecBFacts24
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

structure In24 : Prop where
  facts : Facts24
  nat : NatFacts
  s331 : Stmt3_3_1
  s3228 : Ch10.TmpL6_3_2_2_eight
  s1102 : Stmt11_0_2
  s1103 : Stmt11_0_3
  s1113 : Stmt11_1_3
  s1122 : Stmt11_2_2

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

structure Hyp24 (T L I : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G) : Prop where
  hyp : Hyp11 G T L I n
  v₁ : IsVi T L I n 1 V₁
  v₂ : IsVi T L I n 2 V₂
  abelian : IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))
  wclos : ⁅fsuV T I, E3.wClos (fsuV T I) 0 T⁆ ≠ ⊥
  sl3 : KindSL3 L (fsuV T I) n →
    Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)

namespace Hyp24

variable {V₁ V₂ : Subgroup G}

theorem notG2 (hI : In24) (h : Hyp24 T L I n V₁ V₂) : ¬ KindG2 L (fsuV T I) n :=
  (setup24 hI.s1122 h.hyp h.v₁ h.v₂ h.wclos h.sl3).1

theorem sParam (hI : In24) (h : Hyp24 T L I n V₁ V₂) (hV : IsElemAbelian 2 (fsuV T I)) :
    E3.sParam hV = n :=
  (setup24 hI.s1122 h.hyp h.v₁ h.v₂ h.wclos h.sl3).2.1 hV

theorem lt_rParam (hI : In24) (h : Hyp24 T L I n V₁ V₂) :
    (n : ℕ∞) < E3.rParam (fsuV T I) :=
  (setup24 hI.s1122 h.hyp h.v₁ h.v₂ h.wclos h.sl3).2.2

theorem kind (hI : In24) (h : Hyp24 T L I n V₁ V₂) :
    KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n := by
  rcases kind_cases hI.s1102 h.hyp with hk | hk | hk
  · exact Or.inl hk
  · exact Or.inr hk
  · exact absurd hk (h.notG2 hI)

theorem flag (hI : In24) (h : Hyp24 T L I n V₁ V₂) : Flag24 L (fsuV T I) ⊤ T V₁ V₂ n := by
  obtain ⟨U₁, U₂, -, hU₁, hU₂, -, h12, -, hu1, hu2, -⟩ := exists_isVi hI.nat hI.s1102 h.hyp
  have e1 : V₁ = U₁ := hu1 V₁ h.v₁
  have e2 : V₂ = U₂ := hu2 V₂ h.v₂
  rw [← e1, ← e2] at h12
  exact
    { elem := isElemAbelian_fsuV h.hyp
      two_le := h.hyp.one_lt
      le_normalizer := L_le_normalizer_fsuV h.hyp
      commutator_eq := commutator_fsuV_eq_self h.hyp
      nat := natModuleOf_fsuV hI.s1102 h.hyp
      kind := h.kind hI
      cL_two := isPGroup_cL_fsuV hI.s1102 h.hyp
      le_X := le_top
      normalizer_le := inf_le_right.trans (normalizer_fsuV_le hI.s331 h.hyp)
      sylow := isSylowTwoOf_of_quasithinIsSylowTwo h.hyp.fsu.sylow le_sup_right
      T_le_V := T_le_normalizer_fsuV T I
      T_le_L := h.hyp.normal
      cV_le := IsVi.cV_le h.v₁
      le₁₂ := h12
      le₂ := IsVi.le_fsuV h.v₂
      stable₁ := IsVi.isEndStable h.v₁
      stable₂ := IsVi.isEndStable h.v₂
      index₁ := by rw [IsVi.relIndex_eq h.v₁, mul_one]
      index₂ := IsVi.relIndex_eq h.v₂
      T_le_V₁ := IsVi.le_normalizer h.v₁
      T_le_V₂ := IsVi.le_normalizer h.v₂ }

end Hyp24

theorem relIndex_fsuV_of_Sp4 (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) (hG2 : ¬ KindG2 L (fsuV T I) n) :
    (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex (fsuV T I) = 2 ^ (4 * n) := by
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n hyp
  rcases hc with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact (kind_not_SL3_Sp4 (by have := hyp.one_lt; omega)
      ⟨K, inferInstance, inferInstance, hK, he⟩ hk).elim
  · rw [Subgroup.relIndex, inf_centralizer_subgroupOf, index_eq_of_realizesVia hπ]
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))).subgroupOf ⊤) = _
    rw [Subgroup.bot_subgroupOf, ← Subgroup.index_eq_card, Subgroup.index_bot,
      Subgroup.card_top]
    change Nat.card (Fin 2 ⊕ Fin 2 → K) = _
    rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, hK, ← pow_mul]
    ring_nf
  · exact (hG2 ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem Hyp24.mQuot_V₂ (hI : In24) {V₁ V₂ : Subgroup G} (h : Hyp24 T L I n V₁ V₂)
    (hk : KindSp4 L (fsuV T I) n) : E3.mQuot (fsuV T I) V₂ = 2 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := relIndex_fsuV_of_Sp4 hI.s1102 h.hyp hk (h.notG2 hI)
  have h3 := Subgroup.relIndex_mul_relIndex _ _ _ (IsVi.cV_le h.v₂) (IsVi.le_fsuV h.v₂)
  rw [h1, IsVi.relIndex_eq h.v₂] at h3
  have h4 : V₂.relIndex (fsuV T I) = 2 ^ (2 * n) := by
    have e : 2 ^ (4 * n) = 2 ^ (n * 2) * 2 ^ (2 * n) := by rw [← pow_add]; ring_nf
    rw [e] at h3
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
  unfold E3.mQuot
  rw [h4, padicValNat.prime_pow]

end CFSG.Quasithin.Vol2.Ch11.SecB
