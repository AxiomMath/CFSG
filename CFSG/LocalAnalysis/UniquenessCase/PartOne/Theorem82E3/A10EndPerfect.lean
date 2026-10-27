module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDichotomy
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct
import CFSG.Quasithin.Vol2.Ch4Sec4Frattini
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompHatA6
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinSyl
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Gen

private theorem derivedSeries_map_subtype_le_sup {H X N : Subgroup G}
    (hXH : X ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (hH : H ≤ X ⊔ N) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype ≤ (derivedSeries ↥X n).map X.subtype ⊔ N := by
  induction n with
  | zero =>
    rw [derivedSeries_zero, derivedSeries_zero, ← MonoidHom.range_eq_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.range_subtype]
    exact hH
  | succ n ih =>
    rw [derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator,
      Subgroup.map_commutator]
    have hXn : (derivedSeries ↥X n).map X.subtype ≤
        Subgroup.normalizer (N : Set G) :=
      (Subgroup.map_subtype_le _).trans (hXH.trans hHN)
    calc ⁅(derivedSeries ↥H n).map H.subtype, (derivedSeries ↥H n).map H.subtype⁆
        ≤ ⁅(derivedSeries ↥X n).map X.subtype ⊔ N,
            (derivedSeries ↥X n).map X.subtype ⊔ N⁆ :=
          Subgroup.commutator_mono ih ih
      _ ≤ ⁅(derivedSeries ↥X n).map X.subtype,
            (derivedSeries ↥X n).map X.subtype⁆ ⊔ N :=
          CFSG.Quasithin.H13.commutator_sup_sup_le hXn

private theorem derivedSeries_le_ker_of_derivedSeries_range_eq_bot {T : Type} [Group T]
    {X : Subgroup G} (f : ↥X →* T) {k : ℕ} (hk : derivedSeries ↥f.range k = ⊥) :
    derivedSeries ↥X k ≤ f.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have h1 : f.rangeRestrict x ∈ derivedSeries ↥f.range k :=
    map_derivedSeries_le_derivedSeries f.rangeRestrict k
      (Subgroup.mem_map_of_mem f.rangeRestrict hx)
  rw [hk, Subgroup.mem_bot] at h1
  exact congrArg Subtype.val h1

private theorem coprime_card_sup_of_coprime {q : ℕ} {N Y : Subgroup G}
    (hNcop : Nat.Coprime q (Nat.card N)) (hYcop : Nat.Coprime q (Nat.card Y))
    (hYnorm : Y ≤ Subgroup.normalizer (N : Set G)) :
    Nat.Coprime q (Nat.card ↥(Y ⊔ N)) := by
  rw [show Y ⊔ N = N ⊔ Y from sup_comm _ _]
  have hdvd :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      N Y hYnorm
  exact (hNcop.mul_right hYcop).coprime_dvd_right hdvd

private theorem derivedSeries_map_subtype_le_relPPrimeCore {q : ℕ} (hq : q.Prime)
    {T : Type} [Group T] {H X : Subgroup G} (f : ↥X →* T)
    (hker : Nat.Coprime (Nat.card f.ker) q) (hXH : X ≤ H)
    (hH : H ≤ X ⊔ CFSG.Open.relPPrimeCore q H) {k : ℕ}
    (hk : derivedSeries ↥f.range k = ⊥) :
    (derivedSeries ↥H k).map H.subtype ≤ CFSG.Open.relPPrimeCore q H := by
  classical
  have hNnormal : ((CFSG.Open.relPPrimeCore q H).subgroupOf H).Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
      hq H
  have hHN : H ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore q H : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf
      (H := CFSG.Open.relPPrimeCore q H) (K := H) (hK := hNnormal)
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le H)
  have hXkY : (derivedSeries ↥X k).map X.subtype ≤ f.ker.map X.subtype :=
    Subgroup.map_mono (derivedSeries_le_ker_of_derivedSeries_range_eq_bot f hk)
  have hW : (derivedSeries ↥H k).map H.subtype ≤
      f.ker.map X.subtype ⊔ CFSG.Open.relPPrimeCore q H :=
    (derivedSeries_map_subtype_le_sup hXH hHN hH k).trans (sup_le_sup hXkY le_rfl)
  have hYnorm : f.ker.map X.subtype ≤
      Subgroup.normalizer (CFSG.Open.relPPrimeCore q H : Set G) :=
    (Subgroup.map_subtype_le _).trans (hXH.trans hHN)
  have hYcop : Nat.Coprime q (Nat.card (f.ker.map X.subtype)) := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hker.symm
  have hNcop : Nat.Coprime q (Nat.card (CFSG.Open.relPPrimeCore q H)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      hq H
  have hsupcop : Nat.Coprime q
      (Nat.card ↥(f.ker.map X.subtype ⊔ CFSG.Open.relPPrimeCore q H)) :=
    coprime_card_sup_of_coprime hNcop hYcop hYnorm
  have hWcop : Nat.Coprime q (Nat.card ↥((derivedSeries ↥H k).map H.subtype)) :=
    hsupcop.coprime_dvd_right (Subgroup.card_dvd_of_le hW)
  have hWeq : ((derivedSeries ↥H k).map H.subtype).subgroupOf H = derivedSeries ↥H k :=
    CFSG.subgroupOf_map_subtype_eq (K := H) (derivedSeries ↥H k)
  have hWnormal : (((derivedSeries ↥H k).map H.subtype).subgroupOf H).Normal := by
    rw [hWeq]
    exact derivedSeries_normal (↥H) k
  exact le_sSup ⟨Subgroup.map_subtype_le _, hWnormal, hWcop⟩

theorem le_relPPrimeCore_of_perfect {q : ℕ} (hq : q.Prime) {T : Type} [Group T]
    {H X K : Subgroup G} (f : ↥X →* T) (hf : IsSolvable f.range)
    (hker : Nat.Coprime (Nat.card f.ker) q) (hXH : X ≤ H)
    (hH : H ≤ X ⊔ CFSG.Open.relPPrimeCore q H) (hKH : K ≤ H) (hK : ⁅K, K⁆ = K) :
    K ≤ CFSG.Open.relPPrimeCore q H := by
  obtain ⟨k, hk⟩ := hf.solvable
  have hWN := derivedSeries_map_subtype_le_relPPrimeCore hq f hker hXH hH hk
  have hKW : K ≤ (derivedSeries ↥H k).map H.subtype := by
    have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
    refine (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
      K H hperf hKH).trans ?_
    rw [CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf]
    exact Subgroup.map_mono (iInf_le (fun n => derivedSeries ↥H n) k)
  exact hKW.trans hWN

end A10Gen

namespace Ctx82E3.A10Frame

open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {c : Ctx82E3 D}

private theorem cycleType_of_pow_three_support {x : Equiv.Perm (Fin 10)} (h3 : x ^ 3 = 1)
    (hsupp : x.support.card = 6 ∨ x.support.card = 9) :
    x.cycleType = {3, 3} ∨ x.cycleType = {3, 3, 3} := by
  have hct := CFSG.Quasithin.H13.S126C.cycleType_eq_replicate_of_cube h3
  have hsum := congrArg Multiset.sum hct
  rw [Equiv.Perm.sum_cycleType, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk : Multiset.card x.cycleType = 2 ∨ Multiset.card x.cycleType = 3 := by
    rcases hsupp with h | h <;> rw [h] at hsum <;> omega
  rcases hk with hk | hk
  · left; rw [hct, hk]; decide +kernel
  · right; rw [hct, hk]; decide +kernel

private theorem card_centralizer_of_pow_three_support {x : Equiv.Perm (Fin 10)}
    (h3 : x ^ 3 = 1) (hsupp : x.support.card = 6 ∨ x.support.card = 9) :
    Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 10)))) = 432 ∨
      Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 10)))) = 162 := by
  rcases cycleType_of_pow_three_support h3 hsupp with h | h
  · left
    rw [Equiv.Perm.nat_card_centralizer, h]
    norm_num [Nat.factorial]
  · right
    rw [Equiv.Perm.nat_card_centralizer, h]
    norm_num [Nat.factorial]

private theorem range_phiA_inclusion_le_centralizer (F : A10Frame c) {B : Subgroup G}
    {b : G} (hbB : b ∈ B) (hbM : b ∈ D.M) :
    (F.phiA.comp (Subgroup.inclusion
      (inf_le_right : Subgroup.centralizer (B : Set G) ⊓ D.M ≤ D.M))).range ≤
      Subgroup.centralizer ({F.phiA ⟨b, hbM⟩} : Set (Equiv.Perm (Fin 10))) := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hxb : (x : G) * b = b * (x : G) :=
    ((Subgroup.mem_centralizer_iff.mp x.2.1) b hbB).symm
  let xM : ↥D.M := Subgroup.inclusion inf_le_right x
  have h1 : xM * ⟨b, hbM⟩ = ⟨b, hbM⟩ * xM := by
    apply Subtype.ext
    change (x : G) * b = b * (x : G)
    exact hxb
  have h2 : (F.phiA.comp (Subgroup.inclusion inf_le_right)) x = F.phiA xM := rfl
  rw [h2]
  change F.phiA ⟨b, hbM⟩ * F.phiA xM = F.phiA xM * F.phiA ⟨b, hbM⟩
  calc F.phiA ⟨b, hbM⟩ * F.phiA xM = F.phiA (⟨b, hbM⟩ * xM) := (map_mul _ _ _).symm
    _ = F.phiA (xM * ⟨b, hbM⟩) := by rw [← h1]
    _ = F.phiA xM * F.phiA ⟨b, hbM⟩ := map_mul _ _ _

private theorem isSolvable_range_of_le_centralizer {p : Equiv.Perm (Fin 10)} (hp3 : p ^ 3 = 1)
    (hsupp : p.support.card = 6 ∨ p.support.card = 9) {X : Subgroup G}
    (f : ↥X →* Equiv.Perm (Fin 10))
    (hle : f.range ≤ Subgroup.centralizer ({p} : Set (Equiv.Perm (Fin 10)))) :
    Group.IsSolvable ↥f.range := by
  classical
  haveI : Finite ↥f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard := card_centralizer_of_pow_three_support hp3 hsupp
  have hdvd : Nat.card ↥f.range ∣
      Nat.card (Subgroup.centralizer ({p} : Set (Equiv.Perm (Fin 10)))) :=
    Subgroup.card_dvd_of_le hle
  have hdvd' : Nat.card ↥f.range ∣ 2 ^ 4 * 3 ^ 4 := by
    rcases hcard with hc | hc
    · rw [hc] at hdvd
      exact hdvd.trans (by norm_num)
    · rw [hc] at hdvd
      exact hdvd.trans (by norm_num)
  exact TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 4) (b := 4) Nat.prime_two Nat.prime_three hdvd'

private theorem coprime_card_ker_phiA_inclusion (F : A10Frame c) {B : Subgroup G} :
    Nat.Coprime (Nat.card (F.phiA.comp (Subgroup.inclusion
      (inf_le_right : Subgroup.centralizer (B : Set G) ⊓ D.M ≤ D.M))).ker) 3 := by
  have hkermap : (F.phiA.comp (Subgroup.inclusion
      (inf_le_right : Subgroup.centralizer (B : Set G) ⊓ D.M ≤ D.M))).ker.map
      (Subgroup.inclusion inf_le_right) ≤ F.phiA.ker := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hdvd : Nat.card (F.phiA.comp (Subgroup.inclusion
      (inf_le_right : Subgroup.centralizer (B : Set G) ⊓ D.M ≤ D.M))).ker ∣
      Nat.card F.phiA.ker := by
    rw [← Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective
        (inf_le_right : Subgroup.centralizer (B : Set G) ⊓ D.M ≤ D.M))]
    exact Subgroup.card_dvd_of_le hkermap
  exact F.coprime_card_ker_phiA.coprime_dvd_left hdvd

theorem le_relPPrimeCore_of_perfect_of_deg_ne_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB : F.deg B ≠ 3)
    (hCB : Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {K : Subgroup G} (hKB : K ≤ Subgroup.centralizer (B : Set G)) (hK : ⁅K, K⁆ = K) :
    K ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  classical
  obtain ⟨b, hbord, hBz⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K421SylProof.exists_zpowers_of_card_three hB3
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbord
    omega
  have hbB : b ∈ B := by rw [hBz]; exact Subgroup.mem_zpowers b
  have hbA : b ∈ F.A := hBA hbB
  have hbL : b ∈ c.L := F.P_le_L (F.A_le hbA)
  have hbM : b ∈ D.M := F.A_le_M hbA
  rw [hBz] at hB
  have hdeg : F.deg (Subgroup.zpowers b) = 6 ∨ F.deg (Subgroup.zpowers b) = 9 := by
    rcases F.deg_zpowers_mem hbA hb1 with h | h | h
    · exact absurd h hB
    · exact Or.inl h
    · exact Or.inr h
  let p : Equiv.Perm (Fin 10) := F.phiA ⟨b, hbM⟩
  have hpA : p ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hbA)
  have hp3 : p ^ 3 = 1 := A10Perm.isElemAbelian_atilde.2 p hpA
  have hsupp : p.support.card = 6 ∨ p.support.card = 9 := by
    have h := F.deg_zpowers_eq hbL
    change F.deg (Subgroup.zpowers b) = p.support.card at h
    rw [← h]
    exact hdeg
  let f : ↥(Subgroup.centralizer (B : Set G) ⊓ D.M) →* Equiv.Perm (Fin 10) :=
    F.phiA.comp (Subgroup.inclusion inf_le_right)
  have hle : f.range ≤ Subgroup.centralizer ({p} : Set (Equiv.Perm (Fin 10))) := by
    simpa [f, p] using range_phiA_inclusion_le_centralizer F hbB hbM
  have hf : Group.IsSolvable ↥f.range :=
    isSolvable_range_of_le_centralizer hp3 hsupp f hle
  have hker : Nat.Coprime (Nat.card f.ker) 3 :=
    coprime_card_ker_phiA_inclusion F
  exact A10Gen.le_relPPrimeCore_of_perfect Nat.prime_three f hf hker inf_le_left hCB hKB hK

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
