module

import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTrans
import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofDL
public import CFSG.RankThree.PartTwo.Sec16.Item1613ResProofOut
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1613Res
  CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS
open scoped commutatorElement

section Pair

variable {G : Type} [Group G] [Finite G]

theorem exists_transv_data (h131 : Item131) {A L : Subgroup G} {c : G} (hc : Ctx169 G A c L)
    (hPc : Sec8.IsZ3PGLThreePi ↥(lBarA c L A)) :
    ∃ u ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, u ^ 3 ^ k = 1) ∧
      ∃ d ∈ A, d ≠ 1 ∧ (∀ a ∈ A, u * a * u⁻¹ * a⁻¹ ∈ Subgroup.zpowers d) ∧
        (∃ a ∈ A, u * a * u⁻¹ ≠ a) ∧ A ⊓ L = Subgroup.zpowers d ∧
        A ⊓ Subgroup.centralizer ({u} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have hA := hc.isElemAbelian
  have hA27 : Nat.card A = 27 := hc.card_eq
  have hcA : c ∈ A := hc.mem_A
  have hcL : c ∉ L := hc.toSec15R.hypS.2.2 c hc.zpowers_mem_omegaA L hc.mem_lA
  obtain ⟨u, huLW, ⟨k, huk⟩, d, hdA, hd1, huA, hu1⟩ := ks1614Trans_of h131 G A c L hc hPc
  obtain ⟨huL, -⟩ := Subgroup.mem_inf.mp huLW
  have hdL : d ∈ L := center_mem hA hc.le_normalizer huL hdA huA hu1
  have hdz3 : Nat.card (Subgroup.zpowers d) = 3 := card_zpowers_eq_three (hA.2 d hdA) hd1
  have hAL : A ⊓ L = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩)) ?_).symm
    rw [Proof1614Trans.card_inf_eq_three_of_pgl hc.toSec13Data hPc, hdz3]
  have huc : u * c * u⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer huL), mul_inv_cancel_right]
  have hud : u * d * u⁻¹ = d := conj_center_eq hA huk hdA huA
  have hdc : d ∉ Subgroup.zpowers c := by
    intro hdc'
    apply hcL
    have hzd := zpowers_eq_of_mem_of_ne_one hc.card_zpowers hdc' hd1
    exact (Subgroup.zpowers_le.mpr hdL) (hzd ▸ Subgroup.mem_zpowers c)
  refine ⟨u, huLW, ⟨k, huk⟩, d, hdA, hd1, huA, hu1, hAL, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge
    (le_inf (sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA))
      (sup_le (Subgroup.zpowers_le.mpr (mem_centralizer_of_conj_eq huc))
        (Subgroup.zpowers_le.mpr (mem_centralizer_of_conj_eq hud)))) ?_).symm
  have h1 := card_inf_centralizer_le_nine hA27 hu1
  have h2 : 9 ≤ Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) :=
    nine_le_card_of_lt (sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA))
      hA27 hc.card_zpowers (lt_of_le_of_ne le_sup_left fun heq =>
        hdc (heq ▸ (le_sup_right : Subgroup.zpowers d ≤ _) (Subgroup.mem_zpowers d)))
  omega

theorem inf_le_of_pgl_pair (h131 : Item131) {A L K : Subgroup G} {c b : G}
    (hc : Ctx169 G A c L) (hb : Ctx169 G A b K) (hPc : Sec8.IsZ3PGLThreePi ↥(lBarA c L A))
    (hPb : Sec8.IsZ3PGLThreePi ↥(lBarA b K A)) (hbB : b ∈ Subgroup.zpowers c ⊔ (A ⊓ L)) :
    A ⊓ K ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hA := hc.isElemAbelian
  obtain ⟨u, huLW, ⟨k, huk⟩, d, -, -, -, -, hAL, hCu⟩ := exists_transv_data h131 hc hPc
  obtain ⟨-, huW⟩ := Subgroup.mem_inf.mp huLW
  have hbA : b ∈ A := hb.mem_A
  have hub : u * b * u⁻¹ = b := by
    have h1 : b ∈ A ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hCu, ← hAL]
      exact hbB
    rw [← Subgroup.mem_centralizer_singleton_iff.mp h1.2, mul_inv_cancel_right]
  have huC : u ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * b = u * b * u⁻¹ * u := by group
      _ = b * u := by rw [hub]
  have huK : u ∈ Subgroup.normalizer (K : Set G) := centralizer_le_normalizer_L hb.toSec14Std huC
  obtain ⟨y, hyAK, hy1, hAKy⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
    (Proof1614Trans.card_inf_eq_three_of_pgl hb.toSec13Data hPb)
  have hyA : y ∈ A := (Subgroup.mem_inf.mp hyAK).1
  have hyK : y ∈ K := (Subgroup.mem_inf.mp hyAK).2
  have huy : u * y * u⁻¹ = y := by
    refine conj_eq_of_mem_zpowers huk (hA.2 y hyA) ?_
    rw [← hAKy]
    exact ⟨(Subgroup.mem_normalizer_iff.mp huW y).mp hyA,
      (Subgroup.mem_normalizer_iff.mp huK y).mp hyK⟩
  have hyB : y ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have h1 : y ∈ A ⊓ Subgroup.centralizer ({u} : Set G) := ⟨hyA, mem_centralizer_of_conj_eq huy⟩
    rw [hCu, ← hAL] at h1
    exact h1
  rw [hAKy]
  exact Subgroup.zpowers_le.mpr hyB

end Pair

section Point

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_point (h131 : Item131) (h1611 : Step1611) {A L K : Subgroup G} {c b : G}
    (hc : Ctx169 G A c L) (hb : Ctx169 G A b K) (hPc : Sec8.IsZ3PGLThreePi ↥(lBarA c L A))
    (hbB : b ∈ Subgroup.zpowers c ⊔ (A ⊓ L)) : c ∈ Subgroup.zpowers b ⊔ (A ⊓ K) := by
  have hA := hc.isElemAbelian
  have hA27 : Nat.card A = 27 := hc.card_eq
  have hcA : c ∈ A := hc.mem_A
  have hbA : b ∈ A := hb.mem_A
  have hbK : b ∉ K := hb.toSec15R.hypS.2.2 b hb.zpowers_mem_omegaA K hb.mem_lA
  have hb1 : b ≠ 1 := hb.toSec13Data.ne_one
  rcases h1611 G A b K hb with hPb | ⟨n, -, -, ⟨ψ⟩⟩
  ·
    obtain ⟨d', hd'AK, hd'1, hAK⟩ := Sec5.exists_eq_zpowers_of_card_eq_prime Nat.prime_three
      (Proof1614Trans.card_inf_eq_three_of_pgl hb.toSec13Data hPb)
    have hd'K : d' ∈ K := (Subgroup.mem_inf.mp hd'AK).2
    have hd'B := inf_le_of_pgl_pair h131 hc hb hPc hPb hbB hd'AK
    have hBA : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
    have hB9 : Nat.card (Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) ≤ 9 := by
      obtain ⟨-, -, -, d, hdA, hd1, -, -, hAL, -⟩ := exists_transv_data h131 hc hPc
      rw [hAL]
      exact card_sup_zpowers_le (hc.commute hcA hdA) hc.card_zpowers
        (card_zpowers_eq_three (hA.2 d hdA) hd1)
    have hd'b : d' ∉ Subgroup.zpowers b := by
      intro h'
      apply hbK
      have hz := zpowers_eq_of_mem_of_ne_one hb.card_zpowers h' hd'1
      exact (Subgroup.zpowers_le.mpr hd'K) (hz ▸ Subgroup.mem_zpowers b)
    have hBeq : Subgroup.zpowers b ⊔ Subgroup.zpowers d' = Subgroup.zpowers c ⊔ (A ⊓ L) :=
      sup_eq_of_mem hA hA27 hBA hB9 hbB hd'B hb1 hd'b
    rw [hAK, hBeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  ·
    have h9 : Nat.card (A ⊓ K : Subgroup G) = 9 :=
      card_inf_eq_nine hb.toSec13Data (isPerfect_lBar hb.toSec13Data) ψ
    have hBh : IsHyperplane A (A ⊓ K) := ⟨inf_le_left, by rw [hA27, h9]⟩
    exact le_zpowers_sup_of_not_mem hBh hbA (fun h' => hbK h'.2) hcA

theorem false_of_point (h131 : Item131) (h138 : Item138N) (h1611 : Step1611)
    {A K : Subgroup G} {b c : G} (hb : Ctx169 G A b K) (hcA : c ∈ A)
    (hcbK : c ∈ Subgroup.zpowers b ⊔ (A ⊓ K)) (hodd : Odd (Nat.card (thetaCen ({b} : Set G))))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2))
    (hT : ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≠ ⊥) : False := by
  have hA := hb.isElemAbelian
  have hbA : b ∈ A := hb.mem_A
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  obtain ⟨⟨hTb, hT2', hAT⟩, hTc, -⟩ :=
    commutator_inf_centralizer_mem hA (Subgroup.zpowers_le.mpr hcA) hS2 hAS hbA
  set T := ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ with hTdef
  have hT2 : IsPGroup 2 T := (isPiSubgroup_piOf_iff Nat.prime_two T).mp hT2'
  have hTK : T ≤ K := by
    rw [hTdef, Subgroup.commutator_le]
    intro s hs y hy
    have hsb : s ∈ Subgroup.centralizer ({b} : Set G) := (Subgroup.mem_inf.mp hs).2
    have hsK : s ∈ Subgroup.normalizer (K : Set G) :=
      centralizer_le_normalizer_L hb.toSec14Std hsb
    have hyB : y ∈ Subgroup.zpowers b ⊔ (A ⊓ K) := (Subgroup.zpowers_le.mpr hcbK) hy
    obtain ⟨i, z, hz, rfl⟩ := exists_zpow_mul_of_mem_sup' (H := A ⊓ K) (c := b)
      (fun x hx => hb.commute (Subgroup.mem_inf.mp hx).1 hbA) hyB
    have hzK : z ∈ K := (Subgroup.mem_inf.mp hz).2
    have hsz : s * z * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hsK z).mp hzK
    have hbi : b ^ i ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.zpow_mem _ (hb.le_normalizer hbA) i
    have hcomm : s * b ^ i = b ^ i * s :=
      (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hsb : Commute s b) i).eq
    have heq : s * (b ^ i * z) * s⁻¹ * (b ^ i * z)⁻¹ =
        b ^ i * ((s * z * s⁻¹) * z⁻¹) * (b ^ i)⁻¹ := by
      calc s * (b ^ i * z) * s⁻¹ * (b ^ i * z)⁻¹ = (s * b ^ i) * z * s⁻¹ * z⁻¹ * (b ^ i)⁻¹ := by
            group
        _ = (b ^ i * s) * z * s⁻¹ * z⁻¹ * (b ^ i)⁻¹ := by rw [hcomm]
        _ = b ^ i * ((s * z * s⁻¹) * z⁻¹) * (b ^ i)⁻¹ := by group
    rw [commutatorElement_def, heq]
    exact (Subgroup.mem_normalizer_iff.mp hbi _).mp (K.mul_mem hsz (K.inv_mem hzK))
  have hFix := ks1613Fix_of h131 h138
  have hTx : A ⊓ K ≤ Subgroup.centralizer (T : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    have hx3 : Nat.card (Subgroup.zpowers x) = 3 :=
      card_zpowers_eq_three (hA.2 x (Subgroup.mem_inf.mp hx).1) hx1
    have hθ := hFix G A b K hb (h1611 G A b K hb) (Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr hx) hx3 T ⟨hTK, hT2', hAT⟩
    have hle : ⁅T, Subgroup.zpowers x⁆ ≤ thetaCen ({b} : Set G) :=
      hθ.trans (Sec21.theta_le_theta_centralizer hb.mem_thetaComponentsAt)
    have hleT : ⁅T, Subgroup.zpowers x⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro t ht y hy
      have hyN : y ∈ Subgroup.normalizer (T : Set G) :=
        hAT ((Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hx).1) hy)
      have h1 : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
      rw [commutatorElement_def, h1]
      exact T.mul_mem ht ((Subgroup.mem_normalizer_iff.mp hyN _).mp (T.inv_mem ht))
    have hbot : ⁅T, Subgroup.zpowers x⁆ = ⊥ := by
      by_contra hne
      exact not_odd_of_le hle (hT2.to_le hleT) hne hodd
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      (Subgroup.mem_zpowers x)
  have hbT : Subgroup.zpowers b ≤ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTb ht)
  have hcT : Subgroup.zpowers c ≤ Subgroup.centralizer (T : Set G) :=
    Subgroup.zpowers_le.mpr ((sup_le hbT hTx) hcbK)
  have hbot : ⁅T, Subgroup.zpowers c⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hcT)
  exact hT (hTc.trans hbot)

end Point

end CFSG.RankThree.PartTwo.Sec16.Res12

