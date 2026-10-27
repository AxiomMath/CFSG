module

public import CFSG.LocalAnalysis.WeakClosure81.InCalEOneMembers
public import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import CFSG.Quasithin.EmptyFaithful.E22PS4
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {Q : Type} [Group Q] [Finite Q]

theorem bar2_perm_three_of_relIndex_le_two {X K : Subgroup Q} (hXK : X ≤ K)
    (hXn : K ≤ normalizer (X : Set Q)) (hidx : X.relIndex K ≤ 2)
    (hX : Nonempty (Bar2 X ≃* Equiv.Perm (Fin 3))) : Nonempty (Bar2 K ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨eX⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOle : CFSG.Open.pCoreOf 2 X ≤ K :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXK
  let O : Subgroup ↥K := (CFSG.Open.pCoreOf 2 X).subgroupOf K
  have hOn : O.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mpr ?_
    exact hXn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have : O.Normal := hOn
  let π : ↥K →* (↥K ⧸ O) := QuotientGroup.mk' O
  have hXn' : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hXn
  let N : Subgroup (↥K ⧸ O) := (X.subgroupOf K).map π
  have hNn : N.Normal := Subgroup.Normal.map hXn' π (QuotientGroup.mk'_surjective O)
  have : N.Normal := hNn
  let f : ↥X →* (↥K ⧸ O) := π.comp (Subgroup.inclusion hXK)
  have hkerf : f.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
    change (X.subtype x) ∈ (CFSG.pCore 2 ↥X).map X.subtype ↔
      x ∈ CFSG.pCore 2 ↥X
    exact Subgroup.mem_map_iff_mem X.subtype_injective
  have hrange : f.range = N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXK x,
        Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨(k : Q), Subgroup.mem_subgroupOf.mp hk⟩, ?_⟩
      change π (Subgroup.inclusion hXK ⟨(k : Q), Subgroup.mem_subgroupOf.mp hk⟩) = π k
      rw [show Subgroup.inclusion hXK ⟨(k : Q), Subgroup.mem_subgroupOf.mp hk⟩ = k
        from Subtype.ext rfl]
  let eXN : Bar2 X ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  let eN : N ≃* Equiv.Perm (Fin 3) := eXN.symm.trans eX
  obtain ⟨ψbar, hψbar⟩ := CFSG.Quasithin.SBd.exists_hom_extending_perm_three N eN
  let ψ : ↥K →* Equiv.Perm (Fin 3) := ψbar.comp π
  have hsurj : Function.Surjective ψ := by
    intro s
    obtain ⟨n, hn⟩ := eN.surjective s
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective O (n : ↥K ⧸ O)
    refine ⟨k, ?_⟩
    change ψbar (π k) = s
    rw [hk, hψbar n, hn]
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hker_card : Nat.card ψ.ker * 6 = Nat.card ↥K := by
    have h := Subgroup.card_ker_mul_card_of_surjective hsurj
    rwa [hperm] at h
  have hKcard : X.relIndex K * Nat.card ↥X = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card (H := X) (K := K)
    rwa [inf_eq_left.mpr hXK] at h
  have hXcard : Nat.card (CFSG.pCore 2 ↥X) * Nat.card (Bar2 X) = Nat.card ↥X := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
    rwa [QuotientGroup.ker_mk'] at h
  have hBar6 : Nat.card (Bar2 X) = 6 := by
    rw [Nat.card_congr eX.toEquiv]
    exact hperm
  have hker_eq : Nat.card ψ.ker =
      X.relIndex K * Nat.card (CFSG.pCore 2 ↥X) := by
    have h : Nat.card ψ.ker * 6 =
        X.relIndex K * (6 * Nat.card (CFSG.pCore 2 ↥X)) := by
      rw [hker_card, ← hKcard, ← hXcard, hBar6]
      ring
    have h' : Nat.card ψ.ker * 6 =
        (X.relIndex K * Nat.card (CFSG.pCore 2 ↥X)) * 6 := by
      rw [h, mul_comm 6 (Nat.card (CFSG.pCore 2 ↥X)), mul_assoc]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hker2 : IsPGroup 2 ψ.ker := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)
      (G := ↥(CFSG.pCore 2 ↥X))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X))
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    have hrelpos : 0 < X.relIndex K := by
      rcases Nat.eq_zero_or_pos (X.relIndex K) with h0 | h
      · rw [h0, zero_mul] at hKcard
        omega
      · exact h
    have hcases : X.relIndex K = 1 ∨ X.relIndex K = 2 := by omega
    have hdvd : Nat.card ψ.ker ∣ 2 ^ (a + 1) := by
      rcases hcases with h1 | h2
      · rw [hker_eq, h1, one_mul, ha]
        exact pow_dvd_pow 2 (Nat.le_succ a)
      · rw [hker_eq, h2, ha, pow_succ']
    exact IsPGroup.of_card_dvd_pow hdvd
  have hpcore : CFSG.Open.pCore 2 ↥K = ψ.ker :=
    CFSG.Quasithin.E22L2.e22ps4_pCore_eq_ker ψ hsurj hker2
  have : ψ.ker.Normal := ψ.normal_ker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

theorem PermThreeMember.inCalEi {L T A X : Subgroup Q} {z : Q} {i : ℕ} (hi : 1 ≤ i)
    [L.Normal] (hidx : L.index ≤ 2) (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hX : PermThreeMember L T A z X) :
    UniquenessCase.PartTwo.InCalEi i T A (X ⊔ UniquenessCase.PartTwo.tA T A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : Subgroup Q := UniquenessCase.PartTwo.tA T A with hτdef
  set K : Subgroup Q := X ⊔ τ with hKdef
  have hτT : τ ≤ T := E1.tauOf_le ⊤ T A
  have hXK : X ≤ K := le_sup_left
  have hτK : τ ≤ K := le_sup_right
  have hτ_norm : τ ≤ normalizer (X : Set Q) := hX.tA_le_normalizer
  have hτ_inf_le : τ ⊓ L ≤ X := hX.tA_inf_le
  have hXn : K ≤ normalizer (X : Set Q) :=
    sup_le Subgroup.le_normalizer hτ_norm
  have hXn' : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hXn
  have hτ : τ ≤ T ⊓ K := le_inf hτT hτK
  have hKL : K ⊓ L = X := by
    refine le_antisymm ?_ (le_inf hXK hX.le)
    intro y hy
    have hyK : y ∈ K := hy.1
    have hyL : y ∈ L := hy.2
    rw [hKdef] at hyK
    change y ∈ (↑(X ⊔ τ) : Set Q) at hyK
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X τ hτ_norm,
      Set.mem_mul] at hyK
    obtain ⟨x, hxX, t, htτ, hxy⟩ := hyK
    have htL : t ∈ L := by
      have hxt : t = x⁻¹ * y := by rw [← hxy]; group
      rw [hxt]
      exact L.mul_mem (L.inv_mem (hX.le hxX)) hyL
    have htX : t ∈ X := hτ_inf_le ⟨htτ, htL⟩
    rw [← hxy]
    exact X.mul_mem hxX htX
  have hidxK : X.relIndex K ≤ 2 := by
    have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := τ) (K := X) hτ_norm).2
    have hinf : τ ⊓ X = τ ⊓ L := by
      refine le_antisymm (le_inf inf_le_left (inf_le_right.trans hX.le)) ?_
      exact le_inf inf_le_left hτ_inf_le
    have hτTL : τ ⊓ L = τ ⊓ (T ⊓ L) := by
      refine le_antisymm ?_ ?_
      · intro y hy
        exact ⟨hy.1, ⟨hτT hy.1, hy.2⟩⟩
      · intro y hy
        exact ⟨hy.1, hy.2.2⟩
    have hrelNZ : (T ⊓ L).relIndex T ≠ 0 := by
      intro h0
      have hmul := Subgroup.relIndex_mul_card (H := T ⊓ L) (K := T)
      rw [h0, zero_mul] at hmul
      have := Nat.card_pos (α := ↥T)
      omega
    rw [hKdef, sup_comm, hrel, hinf, hτTL, Subgroup.inf_relIndex_left]
    calc (T ⊓ L).relIndex τ ≤ (T ⊓ L).relIndex T :=
          Subgroup.relIndex_le_of_le_right hτT hrelNZ
      _ = L.relIndex T := Subgroup.inf_relIndex_left (H := T) (K := L)
      _ ≤ L.index := by
          refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_)
            (Subgroup.relIndex_dvd_index_of_normal (H := L) (K := T))
          exact Subgroup.FiniteIndex.index_ne_zero
      _ ≤ 2 := hidx
  have hKbar : Nonempty (Bar2 K ≃* Equiv.Perm (Fin 3)) :=
    bar2_perm_three_of_relIndex_le_two hXK hXn hidxK hX.bar2
  have hSyl : IsSylowIn 2 (T ⊓ K) K := by
    have hHnorm : T ⊓ K ≤ normalizer (X : Set Q) := inf_le_right.trans hXn
    have hsupX : (T ⊓ K) ⊔ X = K := by
      refine le_antisymm (sup_le inf_le_right hXK) ?_
      rw [hKdef]
      refine sup_le le_sup_right ?_
      exact (le_inf hτT hτK).trans le_sup_left
    have hinfX : (T ⊓ K) ⊓ X = T ⊓ X := by
      rw [inf_assoc, inf_eq_right.mpr hXK]
    have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := T ⊓ K) (K := X) hHnorm).1
    rw [hsupX, hinfX] at hrel
    refine ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, ?_⟩
    rw [hrel]
    exact hX.sylow.not_dvd_relIndex
  have hO_le : pCoreOf 2 K ⊓ L ≤ pCoreOf 2 X := by
    have h1 : pCoreOf 2 K ⊓ L ≤ pCoreOf 2 K ⊓ X := by
      refine le_inf inf_le_left ?_
      rw [← hKL]
      intro x hx
      exact ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 K) hx.1, hx.2⟩
    refine h1.trans ?_
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
    · refine (le_inf ?_ (Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
      exact hXK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_inf_left
  have hAO : ¬ A ≤ pCoreOf 2 K := by
    intro hAle
    apply hX.not_inf_le_pCore
    intro a ha
    exact hO_le ⟨hAle ha.1, ha.2⟩
  exact CFSG.LocalAnalysis.WeakClosure81.inCalEi_of_bar2_mulEquiv_perm_three
    hAT hA hi hτ hSyl hKbar hAO

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
