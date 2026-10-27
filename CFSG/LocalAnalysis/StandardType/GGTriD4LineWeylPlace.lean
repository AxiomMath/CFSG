module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped Pointwise

theorem triD4Line_placement
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (D : TriD4LineKGXData n K k)
    (E : Subgroup (GGTriD4R n K)) (hE : IsPGroup 3 E) :
    ∃ g : GGTriD4R n K, ∀ e ∈ E, g * e * g⁻¹ ∈ Subgroup.centralizer {D.z₀} := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 3 (pow_ne_zero n (by norm_num)))
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [pow_zero, one_pow] at hK
      omega
    · exact h
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 3)
    (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := CFSG.StandardType.TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  haveI : Finite (GGTriD4R n K) :=
    Finite.of_equiv (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) e.symm.toEquiv
  obtain ⟨P, _, hcommP⟩ := D.sylow_z₀
  have hPc : (P : Subgroup (GGTriD4R n K)) ≤ Subgroup.centralizer {D.z₀} := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact (hcommP y hy).symm
  obtain ⟨Q, hEQ⟩ := hE.exists_le_sylow
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 (GGTriD4R n K)) := Sylow.finite_of_finiteIndex P
  haveI : MulAction.IsPretransitive (GGTriD4R n K) (Sylow 3 (GGTriD4R n K)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GGTriD4R n K) Q P
  refine ⟨g, fun e he => ?_⟩
  have heQ : e ∈ (Q : Subgroup (GGTriD4R n K)) := hEQ he
  have hQP : MulAut.conj g • (Q : Subgroup (GGTriD4R n K)) =
      (P : Subgroup (GGTriD4R n K)) := by
    have := congrArg (fun S : Sylow 3 (GGTriD4R n K) => (S : Subgroup (GGTriD4R n K))) hg
    simpa [Sylow.coe_subgroup_smul] using this
  have hmem : (MulAut.conj g) e ∈ (P : Subgroup (GGTriD4R n K)) := by
    rw [← hQP]
    exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g)
      (Q : Subgroup (GGTriD4R n K)) heQ
  simpa [MulAut.conj_apply] using hPc hmem

theorem triD4Line_mem_of_order_nine
    {n : ℕ} (hn : 1 ≤ n) (hev : Even n) (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (k : Type) [Field k] [Algebra k K] (D : TriD4LineKGXData n K k)
    (E : Subgroup (GGTriD4R n K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hle : E ≤ Subgroup.centralizer {D.z₀}) : D.z₀ ∈ E := by
  by_contra hzE
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 3 (pow_ne_zero n (by norm_num)))
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 3)
    (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := CFSG.StandardType.TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  haveI : Finite (GGTriD4R n K) :=
    Finite.of_equiv (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) e.symm.toEquiv
  have hdvd : 3 ∣ 2 ^ n - 1 := by
    obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp hev
    have hmod : 1 ≡ 2 ^ n [MOD 3] := by
      rw [ht]
      have hbase : 1 ≡ 2 ^ 2 [MOD 3] := by decide
      have hpow := Nat.ModEq.pow t hbase
      simpa [pow_mul] using hpow
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod
  have hzp : D.z₀ ^ 3 = 1 := by
    rw [← D.orderOf_z₀]
    exact pow_orderOf_eq_one _
  have hk2 : Nat.card E = 3 ^ 2 := by rw [hEc]; norm_num
  have hz : ∀ x ∈ E, x * D.z₀ = D.z₀ * x := by
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) D.z₀ (Set.mem_singleton _)).symm
  obtain ⟨hH_elem, hH_card⟩ :=
    CFSG.StandardType.isElemAbelian_sup_zpowers_of_card (p := 3) Nat.prime_three hE hk2 hzp hzE hz
  have hH'_elem : CFSG.Open.IsElemAbelian 3
      ((E ⊔ Subgroup.zpowers D.z₀).map e.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hH_elem e.toMonoidHom
  have hbound := CFSG.StandardType.TableBExcSmallRanks.ggTriD4ThreeRankInput_holds
    n hn (Or.inl hdvd) K hK σ hσ ((E ⊔ Subgroup.zpowers D.z₀).map e.toMonoidHom) hH'_elem
  rw [Subgroup.card_map_of_injective e.injective, hH_card] at hbound
  norm_num at hbound

end CFSG.StandardType
