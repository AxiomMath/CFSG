module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInOne
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

section General

variable {G : Type*} [Group G]

theorem iSub_le_pCoreOf_kSub {V H E : Subgroup G} (hK : kSub V H E ≤ H) :
    iSub V H E ≤ pCoreOf 2 (kSub V H E) :=
  iSup₂_le fun _ hU =>
    (inf_le_inf_right _ (le_kSub hU)).trans (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hK)

theorem pCoreOf_subgroupOf_normal {K H : Subgroup G} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).Normal) : ((pCoreOf 2 K).subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)]
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hK).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)

theorem fusionOddCoreOf_eq_bot_of_charTwo {X : Type*} [Group X] [Finite X]
    (hX : CharTwo (⊤ : Subgroup X)) (K : Subgroup X) [K.Normal] : fusionOddCoreOf K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup X := pCoreOf 2 (⊤ : Subgroup X) with hQ
  set N : Subgroup X := fusionOddCoreOf K with hN
  have hNodd : Odd (Nat.card N) := by
    have h : fusionOddCore ↥K = CFSG.pPrimeCore 2 ↥K := by
      unfold fusionOddCore CFSG.pPrimeCore
      congr 1
      ext L
      simp [Nat.coprime_two_left]
    have h2 : Odd (Nat.card (fusionOddCore ↥K)) := by
      rw [h]
      exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K))
    rw [hN, fusionOddCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
    exact h2
  have hNnorm : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨n₀, hn₀, rfl⟩ := hn
    have h1 : MulAut.conjNormal (H := K) x n₀ ∈ fusionOddCore ↥K := by
      rw [← CFSG.CGT.Timmesfeld75.fusionOddCore_map_mulEquiv (MulAut.conjNormal (H := K) x)]
      exact Subgroup.mem_map_of_mem _ hn₀
    exact ⟨_, h1, MulAut.conjNormal_apply x n₀⟩
  have hQnorm : Q.Normal :=
    ⟨fun n hn x => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup X) (Subgroup.mem_top x)) n).mp
        hn⟩
  have hbot : N ⊓ Q = ⊥ := by
    have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hQp.to_le (inf_le_right : N ⊓ Q ≤ Q))
    have hdvd : Nat.card ↥(N ⊓ Q) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hk0 : k = 0 := by
      by_contra hk0
      have h2 : 2 ∣ Nat.card N := (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  have hcomm : ∀ n ∈ N, n ∈ Subgroup.centralizer (Q : Set X) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : n * q * n⁻¹ * q⁻¹ ∈ N ⊓ Q := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h3 := N.mul_mem hn (hNnorm.conj_mem _ (N.inv_mem hn) q)
        simpa [mul_assoc] using h3
      · exact Q.mul_mem (hQnorm.conj_mem q hq n) (Q.inv_mem hq)
    rw [hbot, Subgroup.mem_bot] at h1
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm
  have hle : N ≤ Q := fun n hn =>
    hX (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top n, hcomm n hn⟩)
  rw [← le_bot_iff, ← hbot]
  exact le_inf le_rfl hle

end General

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

namespace Hyp83

theorem le_normalizer_kGenIn (h : Hyp83 V H T) :
    T ≤ Subgroup.normalizer (kGenIn V H : Set G) :=
  h.sylow.le.trans (inf_normalizer_le_normalizer_kGenIn V H)

theorem le_normalizer_kGenIn_of_eq_sup (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    H ≤ Subgroup.normalizer (kGenIn V H : Set G) :=
  hKT.le.trans (sup_le Subgroup.le_normalizer h.le_normalizer_kGenIn)

theorem conjClosure_eq_kGenIn (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    conjClosure V H = kGenIn V H := by
  refine le_antisymm (conjClosure_le fun x hx z hz => ?_) (kGenIn_le_conjClosure V H)
  exact (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_kGenIn_of_eq_sup hKT hx) z).mp
    (le_kGenIn_self V H hz)

end Hyp83

namespace AmbientH

theorem kSub_eq_kGenIn (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) =
      (kGenIn V H).subgroupOf H := by
  rw [kSub_eq h, h.conjClosure_eq_kGenIn hKT]

theorem exists_mem_kSub_eq_conjSubgroup (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    ∀ U ∈ omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)),
      ∃ k ∈ kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
          (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)),
        U = conjSubgroup (V.subgroupOf H) k := by
  intro U hU
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  have hgTK : (g : G) ∈ ((T ⊔ kGenIn V H : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, sup_comm]
    exact hKT.le g.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T (kGenIn V H) h.le_normalizer_kGenIn] at hgTK
  obtain ⟨t, ht, k, hk, hgtk⟩ := hgTK
  have htH : t ∈ H := h.T_le_H ht
  have hkH : k ∈ H := kGenIn_le_H h.le_H hk
  have hg : g = (⟨t, htH⟩ : ↥H) * ⟨k, hkH⟩ := Subtype.ext hgtk.symm
  have hcT : conjSubgroup (V.subgroupOf H) (⟨t, htH⟩ : ↥H) = V.subgroupOf H := by
    ext x
    rw [mem_conjSubgroup_iff]
    exact (Subgroup.mem_normalizer_iff.mp
      ((hyp83 h).T_le_normalizer (Subgroup.mem_subgroupOf.mpr ht)) x).symm
  refine ⟨⟨k, hkH⟩, ?_, ?_⟩
  · rw [kSub_eq_kGenIn h hKT]
    exact Subgroup.mem_subgroupOf.mpr hk
  · rw [hg, ← conjSubgroup_conjSubgroup, hcT]

theorem hyp711 (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) :
    SevenK.Hyp711 (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) where
  elemAbelian := (hyp83 h).elemAbelian
  ti := (hyp83 h).isTI
  noncyclic := (hyp83 h).two_lt_card
  abelian := (hyp83 h).isMulCommutative_eSub
  le := le_top
  normal := (hyp83 h).eSub_subgroupOf_normal
  mem := (hyp83 h).mem_omegaSet_self
  omega_le := fun _ _ => le_top
  iSub_le := iSub_le_pCoreOf_kSub le_top
  pcore_le := (hyp83 h).pCoreOf_kSub_le fun _ _ => le_top
  jnormal := pCoreOf_subgroupOf_normal le_top ((hyp83 h).kSub_normal fun _ _ => le_top)
  oddCore := by
    have hKnorm : (kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H))).Normal :=
      ⟨fun n hn x => (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp
          ((hyp83 h).kSub_normal fun _ _ => le_top) (Subgroup.mem_top x)) n).mp hn⟩
    exact fusionOddCoreOf_eq_bot_of_charTwo (hyp83 h).isCalH.2.1 _
  transitive := exists_mem_kSub_eq_conjSubgroup h hKT

end AmbientH

end CFSG.LocalAnalysis.WeakClosure81
