module

public import CFSG.RankThree.PartTwo.Sec21.Commute33Tools
public import CFSG.RankThree.PartTwo.Sec21.Star22
public import CFSG.LocalAnalysis.ComponentInitial.OddCoreFreeInvolutionLayer
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.RankThree.PartTwo.Sec21.Commute33Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] noncomputable def oddTwoCore (N : Subgroup G) : Subgroup G :=
  ((pCore 2 (N ⧸ pPrimeCore 2 N)).comap (QuotientGroup.mk' (pPrimeCore 2 N))).map N.subtype

theorem oddTwoCore_le (N : Subgroup G) : oddTwoCore N ≤ N := map_subtype_le _

theorem normalizer_le_normalizer_oddCore (N : Subgroup G) :
    normalizer (N : Set G) ≤ normalizer (inSubgroup (pPrimeCore 2) N : Set G) :=
  SignalizerFunctor.Helpers.normalizer_le_normalizer_characteristic N (pPrimeCore 2 N)

theorem normalizer_le_normalizer_oddTwoCore (N : Subgroup G) :
    normalizer (N : Set G) ≤ normalizer (oddTwoCore N : Set G) := by
  refine le_normalizer_of_forall_mul_mem fun g hg y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  set α : MulAut N := N.normalizerMonoidHom ⟨g, hg⟩ with hα
  have hαO : (pPrimeCore 2 N).map α.toMonoidHom = pPrimeCore 2 N :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  set ᾱ := QuotientGroup.congr (pPrimeCore 2 N) (pPrimeCore 2 N) α hαO
  have hP : (pCore 2 (N ⧸ pPrimeCore 2 N)).map ᾱ.toMonoidHom = pCore 2 (N ⧸ pPrimeCore 2 N) :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance ᾱ
  refine ⟨α x, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap] at hx ⊢
  have h1 : QuotientGroup.mk' (pPrimeCore 2 N) (α x) = ᾱ (QuotientGroup.mk' (pPrimeCore 2 N) x) :=
    (QuotientGroup.congr_mk' _ _ _ _ x).symm
  rw [h1, ← hP]
  exact ⟨_, hx, rfl⟩

theorem mem_oddTwoCore_of_commutator_mem [Finite G] {N : Subgroup G} (hNs : Group.IsSolvable N)
    {x : G} (hx : x ∈ N) (h : ∀ y ∈ oddTwoCore N, ⁅x, y⁆ ∈ inSubgroup (pPrimeCore 2) N) :
    x ∈ oddTwoCore N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 N with hO
  set π := QuotientGroup.mk' O with hπ
  set Q := N ⧸ O
  have hQs : Group.IsSolvable Q := inferInstance
  have hQO : pPrimeCore 2 Q = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hFP : fittingSubgroup Q = pCore 2 Q :=
    le_antisymm (LocalAnalysis.ComponentInitial.fittingSubgroup_le_pCore_of_pPrimeCore_eq_bot hQO)
      (pCore_le_fitting Q 2)
  have hCP : centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
    rw [← hFP]
    exact RankThree.PGroups.solvable_fitting_self_centralizing Q
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  apply hCP
  rw [mem_centralizer_iff]
  intro q hq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O q
  have hyP : (y : G) ∈ oddTwoCore N := ⟨y, hq, rfl⟩
  have hc : ⁅(⟨x, hx⟩ : N), y⁆ ∈ O := by
    obtain ⟨z, hz, hzeq⟩ := h _ hyP
    have : z = ⁅(⟨x, hx⟩ : N), y⁆ := Subtype.ext (by
      simpa [commutatorElement_def] using hzeq)
    rw [← this]
    exact hz
  have h1 : π ⁅(⟨x, hx⟩ : N), y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem oddTwoCore_le_sup [Finite G] {N : Subgroup G} (S : Sylow 2 N) :
    oddTwoCore N ≤ inSubgroup (pPrimeCore 2) N ⊔ (S : Subgroup N).map N.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 N
  set π := QuotientGroup.mk' O
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap] at hx
  have hxS := IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2))
    (Sylow.mapSurjective (QuotientGroup.mk'_surjective O) S) hx
  obtain ⟨s, hs, hsx⟩ := hxS
  have hxs : x * s⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change π x * (π s)⁻¹ = 1
    rw [← hsx]
    exact mul_inv_cancel _
  have hx' : N.subtype x = ((x * s⁻¹ : N) : G) * (s : G) := by simp
  rw [hx']
  exact Subgroup.mul_mem_sup ⟨_, hxs, rfl⟩ ⟨s, hs, rfl⟩

theorem odd_card_inSubgroup_pPrimeCore [Finite G] (N : Subgroup G) :
    Odd (Nat.card (inSubgroup (pPrimeCore 2) N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [inSubgroup, Subgroup.card_map_of_injective N.subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem le_normalizer_commutator {A K J : Subgroup G} (hK : A ≤ normalizer (K : Set G))
    (hJ : A ≤ normalizer (J : Set G)) : A ≤ normalizer ((⁅K, J⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_mul_mem fun a ha y hy => ?_
  have hmap : ⁅K, J⁆.map (MulAut.conj a).toMonoidHom = ⁅K, J⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hK ha),
      map_conj_eq_of_mem_normalizer (hJ ha)]
  rw [← hmap]
  exact ⟨y, hy, rfl⟩

theorem odd_card_commutator [Finite G] {K J A : Subgroup G} [IsSimpleGroup K]
    (hK : ⁅K, K⁆ = K) (hNs : Group.IsSolvable (⁅K, J⁆ : Subgroup G)) (hA3 : IsPGroup 3 A)
    (hcop : Nat.Coprime 3 (Nat.card (⁅K, J⁆ : Subgroup G)))
    (hAK : A ≤ normalizer (K : Set G)) (hAJ : A ≤ normalizer (J : Set G))
    (hS : ∀ S : Subgroup G, S ≤ ⁅K, J⁆ → IsPGroup 2 S → A ≤ normalizer (S : Set G) →
      A ≤ centralizer (S : Set G))
    {z : G} (hzA : z ∈ A) (hzK : z ∈ K) (hz1 : z ≠ 1) :
    Odd (Nat.card (⁅K, J⁆ : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := ⁅K, J⁆ with hNdef
  set O := inSubgroup (pPrimeCore 2) N with hOdef
  set P := oddTwoCore N with hPdef
  have hKN : K ≤ normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_left K J
  have hAN : A ≤ normalizer (N : Set G) := le_normalizer_commutator hAK hAJ
  have hNO : N ≤ normalizer (O : Set G) := fun n hn =>
    normalizer_le_normalizer_oddCore N (Subgroup.le_normalizer hn)
  have hKO : K ≤ normalizer (O : Set G) := hKN.trans (normalizer_le_normalizer_oddCore N)
  have hKP : K ≤ normalizer (P : Set G) := hKN.trans (normalizer_le_normalizer_oddTwoCore N)
  have hNP : N ≤ normalizer (P : Set G) := fun n hn =>
    normalizer_le_normalizer_oddTwoCore N (Subgroup.le_normalizer hn)
  have hPO : P ≤ normalizer (O : Set G) := (oddTwoCore_le N).trans hNO
  have hzO : z ∈ normalizer (O : Set G) := normalizer_le_normalizer_oddCore N (hAN hzA)
  obtain ⟨S, hSA⟩ := SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow 3 2
    Nat.prime_three Nat.prime_two A N hA3 hAN hcop
  set S' : Subgroup G := (S : Subgroup N).map N.subtype with hS'
  have hS'N : S' ≤ N := map_subtype_le _
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map N.subtype
  have hAS : A ≤ centralizer (S' : Set G) := hS S' hS'N hS'2 hSA
  have hset : ((O ⊔ S' : Subgroup G) : Set G) = (O : Set G) * (S' : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O S' (hS'N.trans hNO)
  have hzP : ∀ p ∈ P, ⁅p, z⁆ ∈ O := by
    intro p hp
    have hpOS : p ∈ ((O ⊔ S' : Subgroup G) : Set G) := oddTwoCore_le_sup S hp
    rw [hset] at hpOS
    obtain ⟨o, ho, s, hs, rfl⟩ := hpOS
    have hsz : s * z = z * s := mem_centralizer_iff.mp (hAS hzA) s hs
    have e : ⁅o * s, z⁆ = o * (z * o⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      calc o * s * z * (o * s)⁻¹ * z⁻¹ = o * (s * z) * s⁻¹ * o⁻¹ * z⁻¹ := by group
        _ = o * (z * s) * s⁻¹ * o⁻¹ * z⁻¹ := by rw [hsz]
        _ = o * (z * o⁻¹ * z⁻¹) := by group
    rw [e]
    exact O.mul_mem ho ((mem_normalizer_iff.mp hzO _).mp (O.inv_mem ho))
  have hPK : ⁅P, K⁆ ≤ O := commutator_le_of_simple hKP hKO hzK hz1 hzP
  have hNKP : ⁅⁅N, K⁆, P⁆ ≤ O := by
    refine PartOne.FTL.commutator_commutator_le_of_rotate hNO hKO hPO ?_ ?_
    · rw [Subgroup.commutator_comm K P]
      exact (Subgroup.commutator_mono hPK le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hNO |>.trans le_rfl)
    · exact (Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hNP)
        le_rfl).trans hPK
  have hNK : ⁅N, K⁆ ≤ P := fun x hx => mem_oddTwoCore_of_commutator_mem hNs
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hKN hx) fun y hy =>
      hNKP (Subgroup.commutator_mem_commutator hx hy)
  have hNKK : ⁅⁅N, K⁆, K⁆ ≤ O := (Subgroup.commutator_mono hNK le_rfl).trans hPK
  have hKNO : ⁅K, N⁆ ≤ O :=
    commutator_le_of_perfect hK hKO hNO (by rw [Subgroup.commutator_comm K N]; exact hNKK)
  have hJO : J ≤ normalizer (O : Set G) := by
    have hJN : J ≤ normalizer (N : Set G) := Subgroup.normalizer_commutator_ge_right K J
    exact hJN.trans (normalizer_le_normalizer_oddCore N)
  have hNle : N ≤ O := commutator_le_of_perfect hK hKO hJO (by
    rw [← hNdef, Subgroup.commutator_comm N K]
    exact hKNO)
  have heq : O = N := le_antisymm (map_subtype_le _) hNle
  rw [← heq]
  exact odd_card_inSubgroup_pPrimeCore N

end CFSG.RankThree.PartTwo.Sec21.Commute33Steps
