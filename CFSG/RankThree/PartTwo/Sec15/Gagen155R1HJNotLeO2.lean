module

public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_commutator_le {K R : Subgroup G} (hRK : R ≤ K)
    (hc : ⁅R, K⁆ ≤ CFSG.Open.pCoreOf 2 K)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    R ≤ CFSG.Open.pCoreOf 2 K := by
  intro r hr
  let x : ↥K := ⟨r, hRK hr⟩
  have hcomm : ∀ k : ↥K, QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⁅x, k⁆ = 1 := by
    intro k
    have hmemP : ⁅x, k⁆ ∈ CFSG.pCore 2 ↥K := by
      rw [← Subgroup.mem_map_iff_mem (f := K.subtype) (K := CFSG.pCore 2 ↥K)
        K.subtype_injective]
      have hcoe : K.subtype ⁅x, k⁆ = ⁅r, (k : G)⁆ := by
        rw [map_commutatorElement]
        rfl
      rw [hcoe]
      exact hc (Subgroup.commutator_mem_commutator hr k.2)
    exact (QuotientGroup.eq_one_iff (⁅x, k⁆)).2 hmemP
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y
    have h1 : ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥K) x,
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) k⁆ = 1 := by
      rw [← map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥K))]
      exact hcomm k
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x *
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) k =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) k *
          QuotientGroup.mk' (CFSG.pCore 2 ↥K) x :=
      commutatorElement_eq_one_iff_mul_comm.mp h1
    simpa [map_mul] using h2.symm
  have hqx : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x = 1 := by
    have h := hmem
    rw [hZ] at h
    simpa using h
  have hxP : x ∈ CFSG.pCore 2 ↥K := by
    apply (QuotientGroup.eq_one_iff x).1
    simpa [QuotientGroup.mk'_apply] using hqx
  exact Subgroup.mem_map_of_mem K.subtype hxP

theorem hj_pCoreOf_le_of_item154 (h154 : Item154R) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {X K : Subgroup G}
    (hK : K ∈ scriptY0 A (lB A)) (hX : X ∈ scriptY4 A (lB A)) (hXK : X ≤ K)
    (hKJ : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hA5 : IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5))) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.Open.pCoreOf 2 X with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) :=
    hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hXR : X ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hRmem : R ∈ invariantPiSubgroups (Subgroup.normalizer (K : Set G)) (A ⊔ X) (piOf 2) :=
    ⟨(hRX.trans hXK).trans Subgroup.le_normalizer,
      (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2, sup_le hAR hXR⟩
  rcases h154 G A c L hR K hK X hX hXK R hRmem with h1 | h2 | h3
  · exact le_pCoreOf_of_commutator_le (hRX.trans hXK) h1
      (KFacts.KS14.center_eq_bot_of_j2 h415 hKJ)
  ·
    obtain ⟨n, m, hn, hm, ⟨e⟩, -, -⟩ := h2
    exfalso
    obtain ⟨φ⟩ := hKJ
    have hmod : 2 ^ (2 * n * m) % 3 = 1 := by
      rw [show 2 * n * m = 2 * (n * m) by ring, pow_mul, Nat.pow_mod]
      norm_num
    have hL3 : Sec4.IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) 2 (2 * n * m) :=
      Or.inl ⟨hmod, ⟨e⟩⟩
    exact (Proof1514.not_isoLThreePi_of_j2 φ hL3).elim
  ·
    obtain ⟨-, hXA5, -⟩ := h3
    exact (hA5.false hXA5.some).elim

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
