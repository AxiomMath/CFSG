module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd low-torus subgroups centralized by an involution in `PSL₂`

The Huppert II.8.5(a) partition forces an odd cyclic subgroup from the
odd low-torus half to vanish when an involution centralizes it.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A cyclic odd subgroup of `PSL₂(K)` whose order divides the odd one of
the two torus half-orders is trivial if it is centralized by an involution. -/
public theorem psl2_low_odd_cyclic_centralizer_eq_bot
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PSL2 K)) (t : PSL2 K) (n : ℕ)
    (hAcyclic : IsCyclic A) (hAodd : Odd (Nat.card A))
    (hnodd : Odd n) (hAcard : Nat.card A ∣ n)
    (hn : n = (Nat.card K - 1) / 2 ∨
      n = (Nat.card K + 1) / 2)
    (ht : IsInvolution t)
    (hcentral : A ≤ Subgroup.centralizer ({t} : Set (PSL2 K))) :
    A = ⊥ := by
  classical
  by_contra hA
  let Z : Subgroup (PSL2 K) := Subgroup.zpowers t
  have htOrder : orderOf t = 2 :=
    orderOf_eq_prime ht.2 ht.1
  have hZcard : Nat.card Z = 2 := by
    simpa [Z] using (Nat.card_zpowers t).trans htOrder
  have htcentA : t ∈ Subgroup.centralizer (A : Set (PSL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcentral ha)
  have hZcentA : Z ≤ Subgroup.centralizer (A : Set (PSL2 K)) := by
    simpa [Z] using (Subgroup.zpowers_le.mpr htcentA)
  have hZnormA : Z ≤ Subgroup.normalizer (A : Set (PSL2 K)) :=
    hZcentA.trans (Subgroup.centralizer_le_normalizer (A : Set (PSL2 K)))
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    rw [hZcard]
    exact hAodd.coprime_two_right
  have hdisjoint : Disjoint A Z :=
    Subgroup.disjoint_of_coprime_natCard hcop
  let B : Subgroup (PSL2 K) := A ⊔ Z
  let toB : A × Z →* B :=
    { toFun := fun x =>
        ⟨(x.1 : PSL2 K) * (x.2 : PSL2 K),
          Subgroup.mul_mem_sup x.1.2 x.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hcomm : (x.2 : PSL2 K) * (y.1 : PSL2 K) =
            (y.1 : PSL2 K) * (x.2 : PSL2 K) :=
          (Subgroup.mem_centralizer_iff.mp (hZcentA x.2.2)
            (y.1 : PSL2 K) y.1.2).symm
        dsimp
        calc
          (x.1 : PSL2 K) * (y.1 : PSL2 K) *
              ((x.2 : PSL2 K) * (y.2 : PSL2 K)) =
              (x.1 : PSL2 K) * ((y.1 : PSL2 K) * (x.2 : PSL2 K)) *
                (y.2 : PSL2 K) := by group
          _ = (x.1 : PSL2 K) * ((x.2 : PSL2 K) * (y.1 : PSL2 K)) *
                (y.2 : PSL2 K) := by rw [hcomm]
          _ = ((x.1 : PSL2 K) * (x.2 : PSL2 K)) *
                ((y.1 : PSL2 K) * (y.2 : PSL2 K)) := by group }
  have htoBinj : Function.Injective toB := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have htoBsurj : Function.Surjective toB := by
    intro b
    have hb : (b : PSL2 K) ∈ (A : Set (PSL2 K)) * (Z : Set (PSL2 K)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A Z hZnormA]
      exact b.2
    rcases hb with ⟨a, ha, z, hz, haz⟩
    exact ⟨(⟨a, ha⟩, ⟨z, hz⟩), Subtype.ext haz⟩
  let eB : A × Z ≃* B :=
    MulEquiv.ofBijective toB ⟨htoBinj, htoBsurj⟩
  have hBcyclic : IsCyclic B := by
    rw [← eB.isCyclic, Group.isCyclic_prod_iff]
    exact ⟨hAcyclic, inferInstance, hcop⟩
  have hBcard : Nat.card B = 2 * Nat.card A := by
    calc
      Nat.card B = Nat.card (A × Z) := Nat.card_congr eB.toEquiv.symm
      _ = Nat.card A * Nat.card Z := Nat.card_prod A Z
      _ = Nat.card A * 2 := by rw [hZcard]
      _ = 2 * Nat.card A := Nat.mul_comm _ _
  rcases hK with ⟨p, f, hp, hpodd, hf, hKcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hqOdd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hpodd.pow
  let P : Sylow p (PSL2 K) := default
  obtain ⟨U, S, hUcyclic, hUcard, hScyclic, hScard, hpartition⟩ :=
    Glauberman.Dickson.huppert_II_8_5_a_psl2_partition hKcard P
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
    have htwo : 2 ∣ Nat.card K - 1 := by
      rcases hqOdd with ⟨a, ha⟩
      use a
      omega
    exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
      (Nat.dvd_gcd htwo (dvd_refl 2))
  have hhalves : (Nat.card K - 1) / 2 + 1 =
      (Nat.card K + 1) / 2 := by
    rcases hqOdd with ⟨a, ha⟩
    omega
  rw [hgcd] at hUcard hScard
  let Family : Subgroup (PSL2 K) → Prop := fun T =>
    (∃ g, T = (P : Subgroup (PSL2 K)).map
      (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : PSL2 K, x ≠ 1 →
      ∃! T : Subgroup (PSL2 K), x ∈ T ∧ Family T := by
    simpa [Family] using hpartition
  have htB : t ∈ B := by
    exact (le_sup_right : Z ≤ B) (Subgroup.mem_zpowers t)
  obtain ⟨T, htT, hTfamily⟩ :=
    (hpartition' t ht.1).exists
  have hBleT : B ≤ T := by
    let : IsCyclic B := hBcyclic
    rcases IsCyclic.exists_zpow_surjective (G := B) with ⟨b, hb⟩
    have hb_ne : (b : PSL2 K) ≠ 1 := by
      intro hb_one
      obtain ⟨k, hk⟩ := hb ⟨t, htB⟩
      have hkval : ((b : PSL2 K) ^ k) = t := congrArg Subtype.val hk
      simp [hb_one] at hkval
      exact ht.1 hkval.symm
    obtain ⟨Tb, hbTb, _hTb_unique⟩ := hpartition' (b : PSL2 K) hb_ne
    have htTb : t ∈ Tb := by
      obtain ⟨k, hk⟩ := hb ⟨t, htB⟩
      have hkval : (b : PSL2 K) ^ k = t := congrArg Subtype.val hk
      have hbpow : (b : PSL2 K) ^ k ∈ Tb := Tb.zpow_mem hbTb.1 k
      rwa [hkval] at hbpow
    have hTbT : Tb = T :=
      (hpartition' t ht.1).unique ⟨htTb, hbTb.2⟩ ⟨htT, hTfamily⟩
    intro y hyB
    obtain ⟨k, hk⟩ := hb ⟨y, hyB⟩
    have hkval : (b : PSL2 K) ^ k = y := congrArg Subtype.val hk
    have hypow : (b : PSL2 K) ^ k ∈ Tb := Tb.zpow_mem hbTb.1 k
    rw [hTbT, hkval] at hypow
    exact hypow
  have hBdT : Nat.card B ∣ Nat.card T :=
    Subgroup.card_dvd_of_le hBleT
  rcases hTfamily with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hBdT
    obtain ⟨eP⟩ :=
      Glauberman.Dickson.huppert_II_8_2_a_sylow_equiv_additive hKcard P
    have hPcard : Nat.card (P : Subgroup (PSL2 K)) = Nat.card K := by
      exact (Nat.card_congr eP.toEquiv).symm
    rw [hBcard, hPcard] at hBdT
    apply hqOdd.not_two_dvd_nat
    exact dvd_trans (dvd_mul_right 2 (Nat.card A)) hBdT
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hBcard, hUcard] at hBdT
    rcases hn with hn | hn
    · apply hnodd.not_two_dvd_nat
      rw [← hn] at hBdT
      exact (dvd_mul_right 2 (Nat.card A)).trans hBdT
    · have hAleft : Nat.card A ∣ (Nat.card K - 1) / 2 :=
        (dvd_mul_left (Nat.card A) 2).trans hBdT
      have hAright : Nat.card A ∣ (Nat.card K + 1) / 2 := by
        rwa [← hn]
      have hAone : Nat.card A ∣ 1 := by
        apply (Nat.dvd_add_iff_left hAleft).mpr
        rw [add_comm, hhalves]
        exact hAright
      have hAcardOne : Nat.card A = 1 := Nat.eq_one_of_dvd_one hAone
      have hAcardGt : 1 < Nat.card A :=
        (Subgroup.one_lt_card_iff_ne_bot A).mpr hA
      omega
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hBcard, hScard] at hBdT
    rcases hn with hn | hn
    · have hAleft : Nat.card A ∣ (Nat.card K - 1) / 2 := by
        rwa [← hn]
      have hAright : Nat.card A ∣ (Nat.card K + 1) / 2 :=
        (dvd_mul_left (Nat.card A) 2).trans hBdT
      have hAone : Nat.card A ∣ 1 := by
        apply (Nat.dvd_add_iff_left hAleft).mpr
        rw [add_comm, hhalves]
        exact hAright
      have hAcardOne : Nat.card A = 1 := Nat.eq_one_of_dvd_one hAone
      have hAcardGt : 1 < Nat.card A :=
        (Subgroup.one_lt_card_iff_ne_bot A).mpr hA
      omega
    · apply hnodd.not_two_dvd_nat
      rw [← hn] at hBdT
      exact (dvd_mul_right 2 (Nat.card A)).trans hBdT

public theorem no_kleinFour_centralizes_low_torus_cyclic
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A V : Subgroup (PSL2 K)) (n : ℕ)
    (hAcyclic : IsCyclic A) (hAodd : Odd (Nat.card A))
    (hAne : A ≠ ⊥) (hnodd : Odd n)
    (hAcard : Nat.card A ∣ n)
    (hn : n = (Nat.card K - 1) / 2 ∨
      n = (Nat.card K + 1) / 2)
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer (A : Set (PSL2 K))) :
    False := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hVK.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let t : PSL2 K := (w : V)
  have htmem : t ∈ V := w.property
  have htne : t ≠ 1 := by
    intro h
    apply hwne
    ext
    exact h
  have htsq : t * t = 1 := congrArg Subtype.val (IsKleinFour.mul_self w)
  have ht : IsInvolution t := ⟨htne, by simpa [pow_two] using htsq⟩
  have htcentA : t ∈ Subgroup.centralizer (A : Set (PSL2 K)) :=
    (Subgroup.mem_centralizer_iff.mp (hVleC htmem))
  have hcentral : A ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htcentA a ha)
  have hbot := psl2_low_odd_cyclic_centralizer_eq_bot K hK A t n
    hAcyclic hAodd hnodd hAcard hn ht hcentral
  exact hAne hbot

end CFSG.GorensteinWalter
