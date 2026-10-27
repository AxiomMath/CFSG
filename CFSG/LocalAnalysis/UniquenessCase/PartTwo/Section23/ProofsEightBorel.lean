module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.Quasithin.Background.HTriPermute
public import CFSG.Quasithin.SteinbergCFCentralSylowInnerOuterBound
public import CFSG.Fischer.Aut.TwoPower

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma sup_le_normalizer_inf_range {X : Type} [Group X]
    (B T₁ : Subgroup (MulAut X)) :
    B ⊔ T₁ ≤ Subgroup.normalizer
      ((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
        Subgroup (MulAut X)) : Set (MulAut X)) := by
  have hR : ((MulAut.conj : X →* MulAut X).range).Normal :=
    CFSG.Fischer.innerAut_normal
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact ⟨(B ⊔ T₁).mul_mem ((B ⊔ T₁).mul_mem hj hn.1) ((B ⊔ T₁).inv_mem hj),
      hR.conj_mem n hn.2 j⟩
  · intro hn
    have hj' : j⁻¹ ∈ B ⊔ T₁ := (B ⊔ T₁).inv_mem hj
    have h : j⁻¹ * (j * n * j⁻¹) * (j⁻¹)⁻¹ ∈
        (B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range :=
      ⟨(B ⊔ T₁).mul_mem ((B ⊔ T₁).mul_mem hj' hn.1) ((B ⊔ T₁).inv_mem hj'),
        hR.conj_mem (j * n * j⁻¹) hn.2 j⁻¹⟩
    simpa [mul_assoc] using h

private lemma relIndex_inf_eq_relIndex_sup {H : Type} [Group H] [Finite H]
    (N B : Subgroup H) (hBN : B ≤ Subgroup.normalizer (N : Set H)) :
    (N ⊓ B).relIndex N = B.relIndex (N ⊔ B) := by
  have hcardNB : Nat.card ↥(N ⊔ B : Subgroup H) * Nat.card ↥(N ⊓ B) =
      Nat.card ↥N * Nat.card ↥B := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B) (K := N) hBN
    simpa [sup_comm, inf_comm, mul_comm] using h
  have h1 : (N ⊓ B).relIndex N * Nat.card ↥(N ⊓ B) = Nat.card ↥N := by
    have := Subgroup.relIndex_mul_card (N ⊓ B) N
    rwa [inf_eq_left.mpr inf_le_left] at this
  have h2 : B.relIndex (N ⊔ B) * Nat.card ↥B = Nat.card ↥(N ⊔ B) := by
    have := Subgroup.relIndex_mul_card B (N ⊔ B)
    rwa [inf_eq_left.mpr le_sup_right] at this
  have h3 : B.relIndex (N ⊔ B) * Nat.card ↥B * Nat.card ↥(N ⊓ B) =
      (N ⊓ B).relIndex N * Nat.card ↥B * Nat.card ↥(N ⊓ B) := by
    calc B.relIndex (N ⊔ B) * Nat.card B * Nat.card ↥(N ⊓ B)
        = Nat.card ↥(N ⊔ B) * Nat.card ↥(N ⊓ B) := by rw [h2]
      _ = Nat.card N * Nat.card B := hcardNB
      _ = ((N ⊓ B).relIndex N * Nat.card ↥(N ⊓ B)) * Nat.card B := by rw [h1]
      _ = (N ⊓ B).relIndex N * Nat.card B * Nat.card ↥(N ⊓ B) := by ring
  have h4 := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(N ⊓ B))) h3
  exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥B)) h4).symm

private lemma relIndex_inf_dvd_relIndex {H : Type} [Group H] [Finite H]
    (N B J : Subgroup H) (hNJ : N ≤ J) (hBJ : B ≤ J)
    (hBN : B ≤ Subgroup.normalizer (N : Set H)) :
    (N ⊓ B).relIndex N ∣ B.relIndex J := by
  rw [relIndex_inf_eq_relIndex_sup N B hBN]
  exact ⟨(N ⊔ B).relIndex J,
    (Subgroup.relIndex_mul_relIndex B (N ⊔ B) J le_sup_right (sup_le hNJ hBJ)).symm⟩

private lemma relIndex_sup_eq_card_of_permutes {H : Type} [Group H] [Finite H]
    {B T : Subgroup H}
    (hperm : (B : Set H) * (T : Set H) = (T : Set H) * (B : Set H))
    (hBT : B ⊓ T = ⊥) : B.relIndex (B ⊔ T) = Nat.card ↥T := by
  have hcard : Nat.card ↥(B ⊔ T) = Nat.card ↥B * Nat.card ↥T :=
    CFSG.Quasithin.H.Tri.card_sup_eq_mul hperm hBT
  have h1 : B.relIndex (B ⊔ T) * Nat.card ↥B = Nat.card ↥(B ⊔ T) := by
    have := Subgroup.relIndex_mul_card B (B ⊔ T)
    rwa [inf_eq_left.mpr le_sup_left] at this
  rw [hcard] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := B)) (by rw [h1, mul_comm])

private lemma relIndex_inf_dvd_card_of_permutes {H : Type} [Group H] [Finite H]
    (B T N : Subgroup H) (hNJ : N ≤ B ⊔ T)
    (hBN : B ≤ Subgroup.normalizer (N : Set H))
    (hperm : (B : Set H) * (T : Set H) = (T : Set H) * (B : Set H))
    (hBT : B ⊓ T = ⊥) :
    (N ⊓ B).relIndex N ∣ Nat.card ↥T := by
  rw [← relIndex_sup_eq_card_of_permutes hperm hBT]
  exact relIndex_inf_dvd_relIndex N B (B ⊔ T) hNJ le_sup_left hBN

private lemma card_dvd_card_of_le_range_conj {X : Type} [Group X] [Finite X]
    {N : Subgroup (MulAut X)}
    (hNleR : N ≤ (MulAut.conj : X →* MulAut X).range)
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) :
    Nat.card ↥N ∣ Nat.card X := by
  let P : Subgroup X := N.comap (MulAut.conj : X →* MulAut X)
  have hPmap : P.map (MulAut.conj : X →* MulAut X) = N :=
    Subgroup.map_comap_eq_self hNleR
  have hcard : Nat.card ↥P = Nat.card ↥N := by
    rw [← hPmap, Subgroup.card_map_of_injective hinj]
  have htop : Nat.card ↥(⊤ : Subgroup X) = Nat.card X :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [← hcard, ← htop]
  exact Subgroup.card_dvd_of_le (le_top : P ≤ ⊤)

private lemma dvd_of_dvd_mul_odd {q s m : ℕ} (hq : ∃ j, q = 2 ^ j)
    (hm : Odd m) (h : q ∣ s * m) : q ∣ s := by
  obtain ⟨j, rfl⟩ := hq
  exact (Nat.coprime_two_left.mpr hm).pow_left j |>.dvd_of_dvd_mul_right h

private lemma p3a_card_dvd_sylow {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ N : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hN : N = (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range)
    (hBN : B ≤ Subgroup.normalizer (N : Set (MulAut X))) :
    (N ⊓ B).relIndex N ∣ Nat.card ↥(S : Subgroup X) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T₁) := by
    rw [hk]
    exact (Odd.coprime_two_left hBodd).symm.pow_right k
  have hq_dvd_t : (N ⊓ B).relIndex N ∣ Nat.card ↥T₁ :=
    relIndex_inf_dvd_card_of_permutes B T₁ N (by rw [hN]; exact inf_le_left) hBN hperm
      (disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop))
  rw [hk] at hq_dvd_t
  obtain ⟨j, -, hqj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hq_dvd_t
  have hq_dvd_X : (N ⊓ B).relIndex N ∣ Nat.card X :=
    (Subgroup.relIndex_dvd_card _ _).trans
      (card_dvd_card_of_le_range_conj (by rw [hN]; exact inf_le_right) hinj)
  have hXcard : Nat.card X = Nat.card ↥(S : Subgroup X) * (S : Subgroup X).index :=
    (Subgroup.card_mul_index (S : Subgroup X)).symm
  have hidxodd : Odd ((S : Subgroup X).index) := by
    by_contra h
    exact S.not_dvd_index (Nat.not_odd_iff_even.mp h).two_dvd
  exact dvd_of_dvd_mul_odd ⟨j, hqj⟩ hidxodd (by rwa [← hXcard])

private lemma p3a_card_eq_sylow {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ N : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hN : N = (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range)
    (hBN : B ≤ Subgroup.normalizer (N : Set (MulAut X)))
    (hCleN : (S : Subgroup X).map (MulAut.conj : X →* MulAut X) ≤ N)
    (hqS : (N ⊓ B).relIndex N ∣ Nat.card ↥(S : Subgroup X)) :
    (N ⊓ B).relIndex N = Nat.card ↥(S : Subgroup X) := by
  classical
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hS_dvd_N : Nat.card ↥(S : Subgroup X) ∣ Nat.card ↥N := by
    have hSdvdC : Nat.card ↥(S : Subgroup X) ∣
        Nat.card ↥((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) := by
      rw [Subgroup.card_map_of_injective hinj]
    exact hSdvdC.trans (Subgroup.card_dvd_of_le hCleN)
  have hS_dvd_q : Nat.card ↥(S : Subgroup X) ∣ (N ⊓ B).relIndex N := by
    have h1 : (N ⊓ B).relIndex N * Nat.card ↥(N ⊓ B) = Nat.card ↥N := by
      have := Subgroup.relIndex_mul_card (N ⊓ B) N
      rwa [inf_eq_left.mpr inf_le_left] at this
    have hodd : Odd (Nat.card ↥(N ⊓ B)) :=
      Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_right)
    have hcop2 : Nat.Coprime (Nat.card ↥(S : Subgroup X)) (Nat.card ↥(N ⊓ B)) := by
      obtain ⟨ks, hks⟩ := (S.isPGroup').exists_card_eq
      rw [hks]
      exact Nat.Coprime.pow_left ks (Nat.coprime_two_left.mpr hodd)
    have hdvd : Nat.card ↥(S : Subgroup X) ∣
        (N ⊓ B).relIndex N * Nat.card ↥(N ⊓ B) := by
      rw [h1]
      exact hS_dvd_N
    exact hcop2.dvd_of_dvd_mul_right hdvd
  exact Nat.dvd_antisymm hqS hS_dvd_q

private theorem p3a_card {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁) :
    Nat.card ↥(((B ⊔ T₁ : Subgroup (MulAut X)) ⊓
        (MulAut.conj : X →* MulAut X).range) ⊓ B) *
      Nat.card ↥(S : Subgroup X) =
    Nat.card ↥((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) := by
  classical
  let J : Subgroup (MulAut X) := B ⊔ T₁
  let C : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X)
  let N : Subgroup (MulAut X) := J ⊓ (MulAut.conj : X →* MulAut X).range
  change Nat.card ↥(N ⊓ B) * Nat.card ↥(S : Subgroup X) = Nat.card ↥N
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCrange : C ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro x ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  have hCleN : C ≤ N := by
    change C ≤ J ⊓ (MulAut.conj : X →* MulAut X).range
    exact le_inf hconjS hCrange
  have hJnorm : B ⊔ T₁ ≤ Subgroup.normalizer (N : Set (MulAut X)) := by
    simpa [J, N] using sup_le_normalizer_inf_range (X := X) B T₁
  have hBN : B ≤ Subgroup.normalizer (N : Set (MulAut X)) :=
    fun b hb => hJnorm (Subgroup.mem_sup_left hb)
  have hqS := p3a_card_dvd_sylow S B T₁ N hZ hBodd hT2 hperm rfl hBN
  have hq := p3a_card_eq_sylow S B T₁ N hZ hBodd hT2 hperm rfl hBN hCleN hqS
  change Nat.card ↥(N ⊓ B) * Nat.card ↥(S : Subgroup X) = Nat.card N
  have h1 : (N ⊓ B).relIndex N * Nat.card ↥(N ⊓ B) = Nat.card N := by
    have := Subgroup.relIndex_mul_card (N ⊓ B) N
    rwa [inf_eq_left.mpr inf_le_left] at this
  rw [← hq, mul_comm]
  exact h1

private lemma eq_setMul_of_card_eq_of_subset {H : Type} [Group H] [Finite H]
    (C D N : Subgroup H) (hCD : C ⊓ D = ⊥)
    (hsub : (C : Set H) * (D : Set H) ⊆ N)
    (hcard : Nat.card ↥N = Nat.card ↥C * Nat.card ↥D) :
    (N : Set H) = (C : Set H) * (D : Set H) := by
  have hcardmul := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf C D
  rw [hCD, Subgroup.card_bot] at hcardmul
  have hcard' : Nat.card ↥((C : Set H) * (D : Set H)) = Nat.card ↥N := by
    rw [hcard]
    simpa using hcardmul
  refine (Set.Finite.eq_of_subset_of_card_le
    (s := (C : Set H) * (D : Set H)) (t := (N : Set H)) (Set.toFinite _) hsub ?_).symm
  rw [hcard']
  simpa using (le_rfl : Nat.card ↥N ≤ Nat.card ↥N)

private lemma p3a_kbor_card {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ N C : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    (hN : N = (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range)
    (hC : C = (S : Subgroup X).map (MulAut.conj : X →* MulAut X)) :
    Nat.card ↥N = Nat.card ↥C * Nat.card ↥(N ⊓ B) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup X) := by
    rw [hC, Subgroup.card_map_of_injective hinj]
  have h := p3a_card S B T₁ hZ hBodd hT2 hperm hconjS
  rw [mul_comm, ← hCcard, ← hN] at h
  exact h.symm

private lemma p3a_kbor_set {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    (hCleN : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤
      (B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
    ((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
        Subgroup (MulAut X)) : Set (MulAut X)) =
      ((((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) : Subgroup (MulAut X)) :
        Set (MulAut X)) *
      (((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
        Subgroup (MulAut X)) ⊓ B : Subgroup (MulAut X)) : Set (MulAut X)) := by
  classical
  let N : Subgroup (MulAut X) := (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range
  let C : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X)
  change (N : Set (MulAut X)) = (C : Set (MulAut X)) * ((N ⊓ B : Subgroup (MulAut X)) : Set (MulAut X))
  have hNcard : Nat.card ↥N = Nat.card ↥C * Nat.card ↥(N ⊓ B) :=
    p3a_kbor_card S B T₁ N C hZ hBodd hT2 hperm hconjS rfl rfl
  have hC2 : IsPGroup 2 C := S.isPGroup'.map (MulAut.conj : X →* MulAut X)
  have hdisj : C ⊓ (N ⊓ B) = ⊥ := by
    have hodd : Odd (Nat.card ↥(N ⊓ B)) :=
      Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_right)
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    have hcop : Nat.Coprime (Nat.card ↥(N ⊓ B)) (Nat.card ↥C) := by
      rw [hk]
      exact (Odd.coprime_two_left hodd).symm.pow_right k
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop.symm)
  have hsub : (C : Set (MulAut X)) * ((N ⊓ B : Subgroup (MulAut X)) : Set (MulAut X)) ⊆
      (N : Set (MulAut X)) := by
    rintro z ⟨c, hc, d, hd, rfl⟩
    exact N.mul_mem (hCleN hc) hd.1
  exact eq_setMul_of_card_eq_of_subset C (N ⊓ B) N hdisj hsub hNcard

private lemma comap_le_sup_of_map_eq_setMul {X : Type} [Group X]
    {S A : Subgroup X} {N C D : Subgroup (MulAut X)}
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    (hC : C = S.map (MulAut.conj : X →* MulAut X))
    (hD : D = A.map (MulAut.conj : X →* MulAut X))
    (hNset : (N : Set (MulAut X)) = (C : Set (MulAut X)) * (D : Set (MulAut X))) :
    N.comap (MulAut.conj : X →* MulAut X) ≤ S ⊔ A := by
  intro p hp
  have hpN : (MulAut.conj : X →* MulAut X) p ∈ (N : Set (MulAut X)) := hp
  rw [hNset] at hpN
  obtain ⟨c, hc, d, hd, hcd⟩ := Set.mem_mul.mp hpN
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp (hC ▸ hc)
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp (hD ▸ hd)
  have hpa : p = s * a := by
    apply hinj
    rw [← hcd, map_mul]
  rw [hpa]
  exact Subgroup.mul_mem_sup hs ha

private lemma p3a_kbor_sup {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥)
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    (hNset : ((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓
        (MulAut.conj : X →* MulAut X).range) : Subgroup (MulAut X)) : Set (MulAut X)) =
      ((((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) : Subgroup (MulAut X)) :
        Set (MulAut X)) *
      (((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
        Subgroup (MulAut X)) ⊓ B : Subgroup (MulAut X)) : Set (MulAut X))) :
    (S : Subgroup X) ⊔
        ((((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
          Subgroup (MulAut X)) ⊓ B).comap (MulAut.conj : X →* MulAut X) =
      (((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range) :
        Subgroup (MulAut X)).comap (MulAut.conj : X →* MulAut X) := by
  classical
  let N : Subgroup (MulAut X) := (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range
  let C : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X)
  let A : Subgroup X := (N ⊓ B).comap (MulAut.conj : X →* MulAut X)
  let P : Subgroup X := N.comap (MulAut.conj : X →* MulAut X)
  change (S : Subgroup X) ⊔ A = P
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hCleN : C ≤ N := by
    change C ≤ (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range
    exact le_inf hconjS (by rintro x ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  have hAmap : A.map (MulAut.conj : X →* MulAut X) = N ⊓ B := by
    rw [show A = (N ⊓ B).comap (MulAut.conj : X →* MulAut X) from rfl]
    exact Subgroup.map_comap_eq_self (inf_le_left.trans inf_le_right)
  have hSP : S.map (MulAut.conj : X →* MulAut X) ≤ N := by simpa [C] using hCleN
  have hAP : A.map (MulAut.conj : X →* MulAut X) ≤ N := by rw [hAmap]; exact inf_le_left
  have hP : P = N.comap (MulAut.conj : X →* MulAut X) := rfl
  refine le_antisymm (sup_le ?_ ?_) (comap_le_sup_of_map_eq_setMul hinj rfl hAmap.symm (by simpa [C, N] using hNset))
  · rw [hP, ← Subgroup.map_le_iff_le_comap]; exact hSP
  · rw [hP, ← Subgroup.map_le_iff_le_comap]; exact hAP

private lemma p3a_kbor_A {X : Type} [Group X] [Finite X]
    (B N : Subgroup (MulAut X)) (A : Subgroup X) (hZ : Subgroup.center X = ⊥)
    (hBcomm : IsMulCommutative B)
    (hBodd : Odd (Nat.card B)) (hNleR : N ≤ (MulAut.conj : X →* MulAut X).range)
    (hA : A = (N ⊓ B).comap (MulAut.conj : X →* MulAut X)) :
    A.map (MulAut.conj : X →* MulAut X) = N ⊓ B ∧
      Nat.card ↥A = Nat.card ↥(N ⊓ B) ∧ Odd (Nat.card ↥A) ∧ IsMulCommutative ↥A := by
  haveI : IsMulCommutative ↥B := hBcomm
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hAmap : A.map (MulAut.conj : X →* MulAut X) = N ⊓ B := by
    rw [hA]
    exact Subgroup.map_comap_eq_self (inf_le_left.trans hNleR)
  have hcard : Nat.card ↥A = Nat.card ↥(N ⊓ B) := by
    rw [← hAmap, Subgroup.card_map_of_injective hinj]
  have hodd : Odd (Nat.card ↥A) := by
    rw [hcard]
    exact Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_right)
  refine ⟨hAmap, hcard, hodd, ?_⟩
  rw [hA]
  exact Subgroup.comap_injective_isMulCommutative (H := N ⊓ B) hinj

private lemma p3a_kbor_cardSA {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ N C : Subgroup (MulAut X)) (A P : Subgroup X)
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    (hN : N = (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range)
    (hC : C = (S : Subgroup X).map (MulAut.conj : X →* MulAut X))
    (hP : P = N.comap (MulAut.conj : X →* MulAut X))
    (hNleR : N ≤ (MulAut.conj : X →* MulAut X).range)
    (hCleN : C ≤ N) (hcardA : Nat.card ↥A = Nat.card ↥(N ⊓ B))
    (hSA : (S : Subgroup X) ⊔ A = P) :
    Nat.card ↥((S : Subgroup X) ⊔ A) =
      Nat.card ↥(S : Subgroup X) * Nat.card ↥A := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup X) := by
    rw [hC, Subgroup.card_map_of_injective hinj]
  have hNcard : Nat.card ↥N = Nat.card ↥C * Nat.card ↥(N ⊓ B) := by
    have h := p3a_card S B T₁ hZ hBodd hT2 hperm hconjS
    rw [mul_comm] at h
    rw [← hN] at h
    rw [hCcard]
    exact h.symm
  have hPcard : Nat.card ↥P = Nat.card ↥N := by
    have h := Subgroup.map_comap_eq_self hNleR (f := (MulAut.conj : X →* MulAut X))
    have h' : Nat.card ↥N = Nat.card ↥((N.comap (MulAut.conj : X →* MulAut X)).map
        (MulAut.conj : X →* MulAut X)) := by rw [h]
    rw [hP, h']
    exact (Subgroup.card_map_of_injective hinj).symm
  rw [hSA, hPcard, hNcard, hCcard, hcardA]

private lemma p3a_kbor_apply {X : Type} [Group X] [Finite X]
    (hKBor : KBor) (hshape : ∃ a : ℕ, IsL2 X a ∨ IsSz X a ∨ IsSp4 X a ∨ IsU3 X a)
    (S : Sylow 2 X) (B T₁ N C : Subgroup (MulAut X)) (A : Subgroup X)
    (hC : C = (S : Subgroup X).map (MulAut.conj : X →* MulAut X))
    (hNset : (N : Set (MulAut X)) = (C : Set (MulAut X)) *
      ((N ⊓ B : Subgroup (MulAut X)) : Set (MulAut X)))
    (hSA : (S : Subgroup X) ⊔ A = N.comap (MulAut.conj : X →* MulAut X))
    (hAmap : A.map (MulAut.conj : X →* MulAut X) = N ⊓ B)
    (hAab : IsMulCommutative ↥A) (hAodd : Odd (Nat.card ↥A))
    (hcardSA : Nat.card ↥((S : Subgroup X) ⊔ A) =
      Nat.card ↥(S : Subgroup X) * Nat.card ↥A) :
    N ≤ Subgroup.normalizer (C : Set (MulAut X)) := by
  obtain ⟨a, hshape'⟩ := hshape
  have hKB := hKBor X a hshape' S A hAab hAodd hcardSA
  have hmap := Subgroup.map_mono (f := (MulAut.conj : X →* MulAut X)) hKB
  have hnormMap : (Subgroup.normalizer (S : Set X)).map (MulAut.conj : X →* MulAut X) ≤
      Subgroup.normalizer (C : Set (MulAut X)) := by
    simpa [hC] using (Subgroup.le_normalizer_map (H := (S : Subgroup X))
      (f := (MulAut.conj : X →* MulAut X)))
  rw [hAmap] at hmap
  have hNBnorm : N ⊓ B ≤ Subgroup.normalizer (C : Set (MulAut X)) :=
    hmap.trans hnormMap
  intro n hn
  change n ∈ (N : Set (MulAut X)) at hn
  rw [hNset] at hn
  obtain ⟨c, hc, d, hd, hcd⟩ := Set.mem_mul.mp hn
  rw [← hcd]
  exact (Subgroup.normalizer (C : Set (MulAut X))).mul_mem
    (Subgroup.le_normalizer hc) (hNBnorm hd)

private theorem p3a_kbor {X : Type} [Group X] [Finite X]
    (hKBor : KBor) (hshape : ∃ a : ℕ, IsL2 X a ∨ IsSz X a ∨ IsSp4 X a ∨ IsU3 X a)
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBcomm : IsMulCommutative B) (hBodd : Odd (Nat.card B))
    (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁) :
    (((B ⊔ T₁ : Subgroup (MulAut X)) ⊓ (MulAut.conj : X →* MulAut X).range)) ≤
      Subgroup.normalizer
        (((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) : Set (MulAut X)) := by
  classical
  let J : Subgroup (MulAut X) := B ⊔ T₁
  let C : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X)
  let N : Subgroup (MulAut X) := J ⊓ (MulAut.conj : X →* MulAut X).range
  let A : Subgroup X := (N ⊓ B).comap (MulAut.conj : X →* MulAut X)
  let P : Subgroup X := N.comap (MulAut.conj : X →* MulAut X)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hNleR : N ≤ (MulAut.conj : X →* MulAut X).range := inf_le_right
  have hCleN : C ≤ N := by
    change C ≤ J ⊓ (MulAut.conj : X →* MulAut X).range
    exact le_inf hconjS (by rintro x ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  obtain ⟨hAmap, hcardA, hAodd, hAab⟩ :=
    p3a_kbor_A B N A hZ hBcomm hBodd hNleR rfl
  have hNset : (N : Set (MulAut X)) = (C : Set (MulAut X)) *
      ((N ⊓ B : Subgroup (MulAut X)) : Set (MulAut X)) := by
    simpa [C, N] using p3a_kbor_set S B T₁ hZ hBodd hT2 hperm hconjS
      (by simpa [C, N] using hCleN)
  have hSA : (S : Subgroup X) ⊔ A = P := by
    simpa [A, P, N, C] using p3a_kbor_sup S B T₁ hZ hconjS hNset
  have hcardSA := p3a_kbor_cardSA S B T₁ N C A P hZ hBodd hT2 hperm hconjS
    rfl rfl rfl hNleR hCleN hcardA hSA
  exact p3a_kbor_apply hKBor hshape S B T₁ N C A rfl hNset hSA hAmap hAab hAodd hcardSA

private lemma p3a_norm_index {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B T₁ N C : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    (hN : N = (B ⊔ T₁) ⊓ (MulAut.conj : X →* MulAut X).range)
    (hC : C = (S : Subgroup X).map (MulAut.conj : X →* MulAut X))
    (hCleN : C ≤ N) : Odd ((C.subgroupOf N).index) := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hCcard : Nat.card ↥C = Nat.card ↥(S : Subgroup X) := by
    rw [hC, Subgroup.card_map_of_injective hinj]
  have hcardN : Nat.card ↥N = Nat.card ↥C * Nat.card ↥(N ⊓ B) := by
    have h := p3a_card S B T₁ hZ hBodd hT2 hperm hconjS
    rw [mul_comm] at h
    rw [← hN] at h
    rw [hCcard]
    exact h.symm
  have hCsubcard : Nat.card ↥(C.subgroupOf N) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleN).toEquiv
  have hoddNB : Odd (Nat.card ↥(N ⊓ B)) :=
    Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_right)
  have h1 := Subgroup.index_mul_card (C.subgroupOf N)
  rw [hCsubcard, hcardN] at h1
  have hidx : (C.subgroupOf N).index = Nat.card ↥(N ⊓ B) :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C)) (by rw [h1, mul_comm])
  rw [hidx]
  exact hoddNB

private lemma p3a_norm_step {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (B N C : Subgroup (MulAut X))
    (hC : C = (S : Subgroup X).map (MulAut.conj : X →* MulAut X))
    (hNnorm : N ≤ Subgroup.normalizer (C : Set (MulAut X)))
    (hCleN : C ≤ N) (hBC : B ≤ Subgroup.normalizer (N : Set (MulAut X)))
    (hCindexodd : Odd ((C.subgroupOf N).index)) :
    ∀ y ∈ B, ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Csub : Subgroup ↥N := C.subgroupOf N
  have hC2 : IsPGroup 2 C := by
    rw [hC]
    exact S.isPGroup'.map (MulAut.conj : X →* MulAut X)
  have hCsub2 : IsPGroup 2 Csub := hC2.comap_subtype (K := N)
  let P_N : Sylow 2 ↥N := hCsub2.toSylow hCindexodd.not_two_dvd_nat
  have hPNcoe : (P_N : Subgroup ↥N) = Csub := IsPGroup.toSylow_coe _ _
  have hPNnormal : (P_N : Subgroup ↥N).Normal := by
    rw [hPNcoe]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCleN).mpr hNnorm
  haveI : Unique (Sylow 2 ↥N) := Sylow.unique_of_normal P_N hPNnormal
  intro y hy c hc
  let φ : MulAut ↥N := N.normalizerMonoidHom ⟨y, hBC hy⟩
  have hφfix : Sylow.mapSurjective (f := (φ : ↥N →* ↥N)) φ.surjective P_N = P_N :=
    Subsingleton.elim _ _
  have hcoe : (P_N : Subgroup ↥N).map (φ : ↥N →* ↥N) = (P_N : Subgroup ↥N) := by
    have h := congrArg (fun Q : Sylow 2 ↥N => (Q : Subgroup ↥N)) hφfix
    simpa only [MulEquiv.coe_toMonoidHom,
      Sylow.coe_mapSurjective (f := (φ : ↥N →* ↥N)) φ.surjective] using h
  let x : ↥N := ⟨c, hCleN hc⟩
  have hxP : x ∈ (P_N : Subgroup ↥N) := by
    rw [hPNcoe]
    exact hc
  have himg : φ x ∈ (P_N : Subgroup ↥N) := by
    rw [← hcoe]
    exact Subgroup.mem_map_of_mem _ hxP
  rw [hPNcoe, Subgroup.mem_subgroupOf,
    Subgroup.normalizerMonoidHom_apply_apply_coe] at himg
  simpa using himg

private theorem p3a_norm {X : Type} [Group X] [Finite X]
    (hKBor : KBor) (hshape : ∃ a : ℕ, IsL2 X a ∨ IsSz X a ∨ IsSp4 X a ∨ IsU3 X a)
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hZ : Subgroup.center X = ⊥) (hBcomm : IsMulCommutative B) (hBodd : Odd (Nat.card B))
    (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁) :
    B ≤ Subgroup.normalizer
      ((((S : Subgroup X).map (MulAut.conj : X →* MulAut X))) : Set (MulAut X)) := by
  classical
  let J : Subgroup (MulAut X) := B ⊔ T₁
  let C : Subgroup (MulAut X) := (S : Subgroup X).map (MulAut.conj : X →* MulAut X)
  let N : Subgroup (MulAut X) := J ⊓ (MulAut.conj : X →* MulAut X).range
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNnorm : N ≤ Subgroup.normalizer (C : Set (MulAut X)) :=
    p3a_kbor hKBor hshape S B T₁ hZ hBcomm hBodd hT2 hperm hconjS
  have hCleN : C ≤ N := by
    change C ≤ J ⊓ (MulAut.conj : X →* MulAut X).range
    exact le_inf hconjS (by rintro x ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)
  have hJnorm : B ⊔ T₁ ≤ Subgroup.normalizer (N : Set (MulAut X)) := by
    simpa [J, N] using sup_le_normalizer_inf_range (X := X) B T₁
  have hBN : B ≤ Subgroup.normalizer (N : Set (MulAut X)) :=
    fun b hb => hJnorm (Subgroup.mem_sup_left hb)
  have hCindexodd := p3a_norm_index S B T₁ N C hZ hBodd hT2 hperm hconjS rfl rfl hCleN
  have hstep := p3a_norm_step S B N C rfl hNnorm hCleN hBN hCindexodd
  rw [Subgroup.le_normalizer_iff]
  exact hstep

theorem mulAut_apply_mem_sylow_of_abelian_odd {X : Type} [Group X] [Finite X]
    (hKBor : KBor) (hshape : ∃ a : ℕ, IsL2 X a ∨ IsSz X a ∨ IsSp4 X a ∨ IsU3 X a)
    (hZ : Subgroup.center X = ⊥)
    (S : Sylow 2 X) (B T₁ : Subgroup (MulAut X))
    (hBcomm : IsMulCommutative B) (hBodd : Odd (Nat.card B)) (hT2 : IsPGroup 2 T₁)
    (hperm : (B : Set (MulAut X)) * (T₁ : Set (MulAut X)) =
      (T₁ : Set (MulAut X)) * (B : Set (MulAut X)))
    (hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T₁)
    {β : MulAut X} (hβ : β ∈ B) {x : X} (hx : x ∈ S) :
    β x ∈ S := by
  have hinj := CFSG.Quasithin.SteinbergCF.conj_injective_of_center_eq_bot hZ
  have hnorm := p3a_norm hKBor hshape S B T₁ hZ hBcomm hBodd hT2 hperm hconjS hβ
  have hcx : (MulAut.conj : X →* MulAut X) x ∈
      ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) :=
    Subgroup.mem_map_of_mem _ hx
  have hb : β * (MulAut.conj : X →* MulAut X) x * β⁻¹ ∈
      ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) :=
    (Subgroup.mem_normalizer_iff.mp hnorm ((MulAut.conj : X →* MulAut X) x)).mp hcx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hb
  have h1 : (MulAut.conj : X →* MulAut X) y =
      (MulAut.conj : X →* MulAut X) (β x) := by
    rw [hxy, CFSG.InnerNormalizedAutomorphisms.mul_conj_mul_inv_eq]
  rw [← hinj h1]
  exact hy

private theorem inducedQuotInfAutHom_eq_conj_piBarInf {K : Subgroup G} {t : G}
    (htK : t ∈ K) (htN : t ∈ Subgroup.normalizer (K : Set G)) :
    inducedQuotInfAutHom K ⟨t, htN⟩ =
      MulAut.conj (piBarInf K ⟨t, htK⟩) := by
  ext y
  obtain ⟨l, rfl⟩ := piBarInf_surjective K y
  change inducedQuotInfAut K t htN (piBarInf K l) =
    MulAut.conj (piBarInf K ⟨t, htK⟩) (piBarInf K l)
  rw [inducedQuotInfAut_piBarInf, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 2

private lemma inducedQuotInfAut_sylow_le_T {D : Data G} {K T0 : Subgroup G}
    (hK : K ∈ calC D.M) (hT0 : T0 = D.T ⊓ Subgroup.normalizer (K : Set G)) :
    ((((D.T ⊓ K).subgroupOf K).map (piBarInf K)).map
        (MulAut.conj : (BarInf K ⧸ Subgroup.center (BarInf K)) →*
          MulAut (BarInf K ⧸ Subgroup.center (BarInf K)))) ≤
      ((T0.subgroupOf (Subgroup.normalizer (K : Set G))).map (inducedQuotInfAutHom K)) := by
  intro y hy
  obtain ⟨x, hxSK, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hxSK
  have hlD : (l : G) ∈ D.T := hl.1
  have hlK : (l : G) ∈ K := l.2
  have hlN : (l : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hlK
  have hφeq := inducedQuotInfAutHom_eq_conj_piBarInf (K := K) hlK hlN
  have hmemT1 : (⟨(l : G), hlN⟩ : Subgroup.normalizer (K : Set G)) ∈
      T0.subgroupOf (Subgroup.normalizer (K : Set G)) := by
    rw [hT0]
    exact ⟨hlD, hlN⟩
  have hmemT : inducedQuotInfAutHom K ⟨(l : G), hlN⟩ ∈
      (T0.subgroupOf (Subgroup.normalizer (K : Set G))).map (inducedQuotInfAutHom K) :=
    Subgroup.mem_map_of_mem _ hmemT1
  rw [← hφeq]
  exact hmemT

private lemma inducedQuotInfAut_odd_comm {D : Data G} {Ch : Choice2011 G}
    (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) :
    Odd (Nat.card ↥((c.B0.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (inducedQuotInfAutHom K))) ∧
    IsMulCommutative ↥((c.B0.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (inducedQuotInfAutHom K)) := by
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let B1 : Subgroup N := c.B0.subgroupOf N
  have hB0N : c.B0 ≤ N := c.B0_le_normalizer_of_mem_calC h215 h1930 hK
  have hB0odd : Odd (Nat.card c.B0) := uc22p22f_odd_card_B c.withB0.toCtx21
  have hB1odd : Odd (Nat.card ↥B1) := by
    rw [show Nat.card ↥B1 = Nat.card ↥c.B0 from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB0N).toEquiv]
    exact hB0odd
  obtain ⟨-, hB0comm, -, -, -, -, -, -, -, -, -⟩ := c.hB0
  haveI : IsMulCommutative ↥c.B0 := hB0comm
  haveI : IsMulCommutative ↥B1 := inferInstance
  exact ⟨Odd.of_dvd_nat hB1odd (Subgroup.card_map_dvd B1 (inducedQuotInfAutHom K)),
    Subgroup.map_isMulCommutative B1 (inducedQuotInfAutHom K)⟩

private lemma inducedQuotInfAut_pgroup_permutes {D : Data G} {Ch : Choice2011 G}
    (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) :
    let X : Type := BarInf K ⧸ Subgroup.center (BarInf K)
    let N : Subgroup G := Subgroup.normalizer (K : Set G)
    let B : Subgroup (MulAut X) := (c.B0.subgroupOf N).map (inducedQuotInfAutHom K)
    let T : Subgroup (MulAut X) := ((D.T ⊓ N).subgroupOf N).map (inducedQuotInfAutHom K)
    IsPGroup 2 T ∧ (B : Set (MulAut X)) * (T : Set (MulAut X)) =
      (T : Set (MulAut X)) * (B : Set (MulAut X)) := by
  dsimp only
  let X : Type := BarInf K ⧸ Subgroup.center (BarInf K)
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let B1 : Subgroup N := c.B0.subgroupOf N
  let T0 : Subgroup G := D.T ⊓ N
  let T1 : Subgroup N := T0.subgroupOf N
  let φ : N →* MulAut X := inducedQuotInfAutHom K
  let B : Subgroup (MulAut X) := B1.map φ
  let T : Subgroup (MulAut X) := T1.map φ
  have hT2D : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hT0p : IsPGroup 2 ↥T0 := hT2D.to_le inf_le_left
  have hT1p : IsPGroup 2 ↥T1 := hT0p.comap_subtype (K := N)
  have hT2T : IsPGroup 2 T := hT1p.map φ
  obtain ⟨-, -, -, -, -, -, -, -, -, hperm0, -⟩ := c.hB0
  have hB0N : c.B0 ≤ N := c.B0_le_normalizer_of_mem_calC h215 h1930 hK
  have hpermB0T0 : (c.B0 : Set G) * (T0 : Set G) = (T0 : Set G) * (c.B0 : Set G) := by
    simpa [T0] using CFSG.GroupTheory.permutes_inf_of_le hB0N
      (show (c.B0 : Set G) * (D.T : Set G) = (D.T : Set G) * (c.B0 : Set G) from hperm0)
  have hpermB1T1 : (B1 : Set N) * (T1 : Set N) = (T1 : Set N) * (B1 : Set N) :=
    CFSG.Quasithin.H.Tri.subgroupOf_mul_comm hB0N inf_le_right hpermB0T0
  have hpermBT : (B : Set (MulAut X)) * (T : Set (MulAut X)) =
      (T : Set (MulAut X)) * (B : Set (MulAut X)) := by
    simpa [B, T] using CFSG.GroupTheory.map_permutes_map φ hpermB1T1
  exact ⟨hT2T, hpermBT⟩

private lemma inducedQuotInfAutHom_maps_sk {D : Data G} {Ch : Choice2011 G}
    (hBor : KBor) (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hZ : Subgroup.center (BarInf K ⧸ Subgroup.center (BarInf K)) = ⊥)
    (hshape : ∃ a : ℕ, IsL2 (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsSz (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsSp4 (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsU3 (BarInf K ⧸ Subgroup.center (BarInf K)) a)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ ((D.T ⊓ K).subgroupOf K).map (piBarInf K),
      inducedQuotInfAutHom K ⟨b, hbN⟩ x ∈
        ((D.T ⊓ K).subgroupOf K).map (piBarInf K) := by
  classical
  let X : Type := BarInf K ⧸ Subgroup.center (BarInf K)
  let φ : Subgroup.normalizer (K : Set G) →* MulAut X := inducedQuotInfAutHom K
  let B : Subgroup (MulAut X) := (c.B0.subgroupOf (Subgroup.normalizer (K : Set G))).map φ
  let T : Subgroup (MulAut X) := ((D.T ⊓ Subgroup.normalizer (K : Set G)).subgroupOf (Subgroup.normalizer (K : Set G))).map φ
  let SK : Subgroup X := ((D.T ⊓ K).subgroupOf K).map (piBarInf K)
  obtain ⟨hBoddB, hBcommB⟩ := inducedQuotInfAut_odd_comm h215 h1930 c hK
  obtain ⟨hT2T, hpermBT⟩ := inducedQuotInfAut_pgroup_permutes h215 h1930 c hK
  obtain ⟨-, hSKp, hSKidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp
    (isSylowOf_map_piBarInf (D := D) (K := K) hK)
  let S : Sylow 2 X := hSKp.toSylow (by simpa using hSKidx)
  have hScoe : (S : Subgroup X) = SK := IsPGroup.toSylow_coe hSKp _
  have hconjS : ((S : Subgroup X).map (MulAut.conj : X →* MulAut X)) ≤ B ⊔ T := by
    rw [hScoe]
    exact (inducedQuotInfAut_sylow_le_T (D := D) (K := K) (T0 := D.T ⊓ Subgroup.normalizer (K : Set G)) hK rfl).trans le_sup_right
  have hmain := mulAut_apply_mem_sylow_of_abelian_odd (β := φ ⟨b, hbN⟩) hBor hshape hZ
    S B T hBcommB hBoddB hT2T hpermBT hconjS
  intro x hx
  have hbB1 : (⟨b, hbN⟩ : Subgroup.normalizer (K : Set G)) ∈
      c.B0.subgroupOf (Subgroup.normalizer (K : Set G)) := hb
  have hβ : φ ⟨b, hbN⟩ ∈ B := Subgroup.mem_map_of_mem _ hbB1
  have hxS : x ∈ (S : Subgroup X) := by rwa [hScoe]
  change φ ⟨b, hbN⟩ x ∈ SK
  rw [← hScoe]
  exact hmain hβ hxS

theorem Ctx23L.inducedQuotInfAut_mem_sylow {D : Data G} {Ch : Choice2011 G}
    (hBor : KBor) (h215 : S21_5 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hZ : Subgroup.center (BarInf K ⧸ Subgroup.center (BarInf K)) = ⊥)
    (hshape : ∃ a : ℕ, IsL2 (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsSz (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsSp4 (BarInf K ⧸ Subgroup.center (BarInf K)) a ∨
      IsU3 (BarInf K ⧸ Subgroup.center (BarInf K)) a)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ ((D.T ⊓ K).subgroupOf K).map (piBarInf K),
      inducedQuotInfAut K b hbN x ∈ ((D.T ⊓ K).subgroupOf K).map (piBarInf K) := by
  classical
  intro x hx
  have h := inducedQuotInfAutHom_maps_sk hBor h215 h1930 c hK hZ hshape hb hbN x hx
  change (inducedQuotInfAutHom K ⟨b, hbN⟩) x ∈
    ((D.T ⊓ K).subgroupOf K).map (piBarInf K)
  exact h

