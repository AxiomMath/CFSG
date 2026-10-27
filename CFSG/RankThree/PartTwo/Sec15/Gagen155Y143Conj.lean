module

import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.GroupTheory.PerfectSylowInversion
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Gagen155Y143

private theorem exists_mul_zpow_of_mem_sup_of_centralizes {B : Subgroup G} {u x : G}
    (hu : ∀ b ∈ B, u * b = b * u) (hx : x ∈ B ⊔ Subgroup.zpowers u) :
    ∃ b ∈ B, ∃ k : ℤ, b * u ^ k = x := by
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hc : Commute (u ^ j) y := Commute.zpow_left (hu y hy) j
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hy
  have hx' : x ∈ ((B ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers u) hnorm] at hx'
  obtain ⟨b, hb, t, ht, hbt⟩ := Set.mem_mul.mp hx'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
  exact ⟨b, hb, k, by rw [hk]; exact hbt⟩

theorem eq_one_of_conj_eq_mul {A L : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {B : Subgroup G} (hBA : IsHyperplane A B) (hcB : c ∉ B)
    {Yc : Subgroup (↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))}
    {a : ↥(Subgroup.centralizer (B : Set G))} (haA : (a : G) ∈ A) (haB : (a : G) ∉ B) {x : ↥Yc}
    (hx : (x : ↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) a)
    {z : ↥Yc}
    (hz : (z : ↥(Subgroup.centralizer (B : Set G)) ⧸
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G))) ∈
      (B.subgroupOf (Subgroup.centralizer (B : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)))))
    {g : ↥Yc} (hg : g * x * g⁻¹ = x * z) : z = 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  let N : Subgroup C := CFSG.pPrimeCore 3 C
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hR.mem_partTwoF.1
  have hcA : c ∈ A := (mem_omegaA_iff.mp hR.zpowers_mem_omegaA).1 (Subgroup.mem_zpowers c)
  have hccard : Nat.card (Subgroup.zpowers c) = 3 :=
    (mem_omegaA_iff.mp hR.zpowers_mem_omegaA).2.1
  have hco : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hccard
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hco
    omega
  have hAC : A ≤ C := by
    intro y hy
    exact Subgroup.mem_centralizer_iff.mpr (fun b hb =>
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA.1 hb⟩ ⟨y, hy⟩))
  have hBC : B ≤ C := hBA.1.trans hAC
  have hsup : B ⊔ Subgroup.zpowers (a : G) = A :=
    Item148HJ.sup_zpowers_eq_of_isHyperplane hBA haA haB
  have hcinf : Subgroup.zpowers c ⊓ B = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ B : Subgroup G) ∣ 3 := by
      rw [← hco, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ B = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hco])
      exact hcB ((le_of_eq heq.symm).trans inf_le_right (Subgroup.mem_zpowers c))
  have hA_C_p : IsPGroup 3 (A.subgroupOf C) := (hAab.subgroupOf C).isPGroup
  have hNcop : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (G := C) (p := 3))
  have hzp : (Subgroup.zpowers (a : G)).subgroupOf C = Subgroup.zpowers a := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hAsub : A.subgroupOf C = B.subgroupOf C ⊔ Subgroup.zpowers a := by
    rw [← hsup, Subgroup.subgroupOf_sup hBC (Subgroup.zpowers_le.mpr (hAC haA)), hzp]
  have hAeq : (A.subgroupOf C).map (QuotientGroup.mk' N) =
      (B.subgroupOf C).map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers (x : C ⧸ N) := by
    rw [hAsub, Subgroup.map_sup, MonoidHom.map_zpowers, ← hx]
  have hg' : (g : C ⧸ N) * (x : C ⧸ N) * (g : C ⧸ N)⁻¹ =
      (x : C ⧸ N) * (z : C ⧸ N) := by
    have h := congrArg (fun t : ↥Yc => (t : C ⧸ N)) hg
    simpa using h
  have hBtilde_central : ∀ y ∈ (B.subgroupOf C).map (QuotientGroup.mk' N),
      ∀ w : C ⧸ N, w * y = y * w := by
    intro y hy w
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨s0, hs0⟩ := QuotientGroup.mk'_surjective N w
    rw [← hs0, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp s0.2 (b : G)
      (Subgroup.mem_subgroupOf.mp hb)).symm
  have hgnorm : (g : C ⧸ N) ∈ Subgroup.normalizer
      (((A.subgroupOf C).map (QuotientGroup.mk' N) : Subgroup (C ⧸ N)) :
        Set (C ⧸ N)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : ((A.subgroupOf C).map (QuotientGroup.mk' N)).map
        (MulAut.conj (g : C ⧸ N)).toMonoidHom ≤
        (A.subgroupOf C).map (QuotientGroup.mk' N) := by
      rw [hAeq]
      intro y hy
      obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨b, hb, k, hbk⟩ := exists_mul_zpow_of_mem_sup_of_centralizes
        (B := (B.subgroupOf C).map (QuotientGroup.mk' N)) (u := (x : C ⧸ N))
        (fun y hy => hBtilde_central y hy (x : C ⧸ N)) hy0
      rw [← hbk]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [MulAut.conj_apply]
      have hconj : (g : C ⧸ N) * (b * (x : C ⧸ N) ^ k) * (g : C ⧸ N)⁻¹ =
          b * (((x : C ⧸ N) * (z : C ⧸ N)) ^ k) := by
        have h1 : (g : C ⧸ N) * (b * (x : C ⧸ N) ^ k) * (g : C ⧸ N)⁻¹ =
            ((g : C ⧸ N) * b * (g : C ⧸ N)⁻¹) *
              ((g : C ⧸ N) * (x : C ⧸ N) ^ k * (g : C ⧸ N)⁻¹) := by group
        rw [h1]
        have hgb : (g : C ⧸ N) * b * (g : C ⧸ N)⁻¹ = b := by
          rw [hBtilde_central b hb, mul_assoc, mul_inv_cancel, mul_one]
        have hgx : (g : C ⧸ N) * (x : C ⧸ N) ^ k * (g : C ⧸ N)⁻¹ =
            ((g : C ⧸ N) * (x : C ⧸ N) * (g : C ⧸ N)⁻¹) ^ k := by
          rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
        rw [hgb, hgx, hg']
      rw [hconj]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.zpow_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : C ⧸ N)))
          (Subgroup.mem_sup_left hz)) k)
    have hcard : Nat.card (((A.subgroupOf C).map (QuotientGroup.mk' N)).map
        (MulAut.conj (g : C ⧸ N)).toMonoidHom) =
        Nat.card ((A.subgroupOf C).map (QuotientGroup.mk' N)) :=
      Subgroup.card_map_of_injective (MulAut.conj (g : C ⧸ N)).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  obtain ⟨s, hsN, hsg⟩ :=
    CFSG.GroupTheory.exists_mem_normalizer_mk'_eq N hNcop hA_C_p hgnorm
  have hsA : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
    have h : s ∈ (Subgroup.normalizer (A : Set G)).subgroupOf C := by
      rw [Subgroup.subgroupOf_normalizer_eq hAC]
      exact hsN
    exact Subgroup.mem_subgroupOf.mp h
  have hsaA : (s : G) * (a : G) * (s : G)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hsA (a : G)).mp haA
  have hsaC : (s : G) * (a : G) * (s : G)⁻¹ ∈ C := hAC hsaA
  let saC : C := ⟨(s : G) * (a : G) * (s : G)⁻¹, hsaC⟩
  let saA : A.subgroupOf C := ⟨saC, Subgroup.mem_subgroupOf.mpr hsaA⟩
  obtain ⟨b0, hb0sub, hb0z⟩ := Subgroup.mem_map.mp hz
  have hb0B : (b0 : G) ∈ B := Subgroup.mem_subgroupOf.mp hb0sub
  have hb0A : (b0 : G) ∈ A := hBA.1 hb0B
  have hab0A : ((a * b0 : C) : G) ∈ A := by
    rw [Subgroup.coe_mul]
    exact A.mul_mem haA hb0A
  let ab0A : A.subgroupOf C := ⟨a * b0, Subgroup.mem_subgroupOf.mpr hab0A⟩
  have hkey : QuotientGroup.mk' N saA = QuotientGroup.mk' N ab0A := by
    calc QuotientGroup.mk' N saA
        = QuotientGroup.mk' N s * QuotientGroup.mk' N a *
            (QuotientGroup.mk' N s)⁻¹ := by
          rw [show (saA : C) = s * a * s⁻¹ from Subtype.ext rfl]
          rw [map_mul, map_mul, map_inv]
      _ = (g : C ⧸ N) * (x : C ⧸ N) * (g : C ⧸ N)⁻¹ := by rw [hsg, ← hx]
      _ = (x : C ⧸ N) * (z : C ⧸ N) := hg'
      _ = QuotientGroup.mk' N a * QuotientGroup.mk' N b0 := by rw [← hx, ← hb0z]
      _ = QuotientGroup.mk' N ab0A := by
          rw [show (ab0A : C) = a * b0 from Subtype.ext rfl]
          exact (map_mul (QuotientGroup.mk' N) a b0).symm
  have heq : saA = ab0A :=
    Sylow155T51.injective_mk_comp_subtype N hNcop hA_C_p hkey
  have hsaG : (s : G) * (a : G) * (s : G)⁻¹ = (a : G) * (b0 : G) := by
    have hCeq : (saA : C) = (ab0A : C) :=
      congrArg (fun t : A.subgroupOf C => (t : C)) heq
    have hG : ((saA : C) : G) = ((ab0A : C) : G) := congrArg (fun t : C => (t : G)) hCeq
    exact hG
  have hcA' : c ∈ B ⊔ Subgroup.zpowers (a : G) := by
    rw [hsup]
    exact hcA
  have huA : ∀ b ∈ B, (a : G) * b = b * (a : G) := fun b hb =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨(a : G), haA⟩ ⟨b, hBA.1 hb⟩)
  obtain ⟨β, hβB, k, hc_eq⟩ :=
    exists_mul_zpow_of_mem_sup_of_centralizes huA hcA'
  have hk3 : k % 3 ≠ 0 := by
    intro h0
    apply hcB
    have hak : (a : G) ^ k = 1 := by
      obtain ⟨q, rfl⟩ := Int.dvd_of_emod_eq_zero h0
      rw [zpow_mul, zpow_ofNat, hAab.2 (a : G) haA, one_zpow]
    rw [← hc_eq, hak, mul_one]
    exact hβB
  have hcommG : Commute (a : G) (b0 : G) := by
    have h := hAab.1.is_comm.comm (⟨(a : G), haA⟩ : A) (⟨(b0 : G), hb0A⟩ : A)
    exact congrArg Subtype.val h
  have hsβ : (s : G) * β * (s : G)⁻¹ = β := by
    have h := Subgroup.mem_centralizer_iff.mp s.2 β hβB
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_a : (s : G) * (a : G) ^ k * (s : G)⁻¹ = ((a : G) * (b0 : G)) ^ k := by
    calc (s : G) * (a : G) ^ k * (s : G)⁻¹
        = (MulAut.conj (s : G)) ((a : G) ^ k) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj (s : G)) (a : G)) ^ k := map_zpow _ _ k
      _ = ((a : G) * (b0 : G)) ^ k := by rw [MulAut.conj_apply, hsaG]
  have hsc : (s : G) * c * (s : G)⁻¹ = c * (b0 : G) ^ k := by
    rw [← hc_eq]
    calc (s : G) * (β * (a : G) ^ k) * (s : G)⁻¹
        = β * ((s : G) * (a : G) ^ k * (s : G)⁻¹) := by
          have h1 : (s : G) * (β * (a : G) ^ k) * (s : G)⁻¹ =
              ((s : G) * β * (s : G)⁻¹) *
                ((s : G) * (a : G) ^ k * (s : G)⁻¹) := by group
          rw [h1, hsβ]
      _ = β * ((a : G) * (b0 : G)) ^ k := by rw [hconj_a]
      _ = β * ((a : G) ^ k * (b0 : G) ^ k) := by rw [hcommG.mul_zpow]
      _ = (β * (a : G) ^ k) * (b0 : G) ^ k := by group
  have hsc_norm : (s : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hW hsA
  have hsc_mem : (s : G) * c * (s : G)⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hsc_norm c).mp (Subgroup.mem_zpowers c)
  have hb0k_z : (b0 : G) ^ k ∈ Subgroup.zpowers c := by
    have h : c * (b0 : G) ^ k ∈ Subgroup.zpowers c := hsc ▸ hsc_mem
    have h2 := Subgroup.mul_mem (Subgroup.zpowers c)
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c)) h
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
  have hb0k_B : (b0 : G) ^ k ∈ B := B.zpow_mem hb0B k
  have hb0k1 : (b0 : G) ^ k = 1 := by
    have h : (b0 : G) ^ k ∈ Subgroup.zpowers c ⊓ B := ⟨hb0k_z, hb0k_B⟩
    rw [hcinf] at h
    exact Subgroup.mem_bot.mp h
  have hb0pow : (b0 : G) ^ 3 = 1 := hAab.2 (b0 : G) hb0A
  have hkmod : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2 := by
    have h0 : (0 : ℤ) ≤ k % ((3 : ℕ) : ℤ) :=
      Int.emod_nonneg k (by norm_num)
    have hlt : k % ((3 : ℕ) : ℤ) < 3 :=
      Int.emod_lt_of_pos k (by norm_num)
    omega
  have hb01 : (b0 : G) = 1 := by
    have hmod : (b0 : G) ^ (k % ((3 : ℕ) : ℤ)) = 1 := by
      rw [← zpow_eq_zpow_emod' k hb0pow]
      exact hb0k1
    rcases hkmod with h0 | h1 | h2
    · exact absurd h0 hk3
    · rw [h1] at hmod
      simpa using hmod
    · have hb02 : (b0 : G) ^ 2 = 1 := by
        rw [h2] at hmod
        simpa [zpow_natCast] using hmod
      calc (b0 : G) = (b0 : G) * 1 := (mul_one _).symm
        _ = (b0 : G) * (b0 : G) ^ 2 := by rw [hb02]
        _ = (b0 : G) ^ 3 := by group
        _ = 1 := hb0pow
  have hz1 : (z : C ⧸ N) = 1 := by
    rw [← hb0z, show b0 = (1 : C) from Subtype.ext hb01]
    simp
  exact Subtype.ext hz1

end Gagen155Y143

end CFSG.RankThree.PartTwo.Sec15
