module

public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Lemmas
public import CFSG.RankThree.PartTwo.Sec15.ThmDLemma10
public import CFSG.RankThree.PartTwo.Sec15.ThmDL3Core
public import CFSG.RankThree.PartTwo.Sec15.ThmDL3Card

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_ker148 {A Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    ¬ 3 ∣ Nat.card (ker148 A Y) := by
  have h1 : Nat.card (ker148 A Y) = Nat.card (pPrimeCoreOf 3 Y) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((pPrimeCoreOf_le 3 Y).trans le_sup_left)).toEquiv
  rw [h1]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)

section Certs


theorem step153D4_of_inputs (hL3 : L3FieldFusionK) (h142 : Concl142S14) : Step153D4 := by
  intro G _ _ A c L hR Y hY hYΔ hV h5 P hPY hP2 hAP
  have hS := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.1.1.2
  letI := ker148_normal hAY
  obtain ⟨c₀, hc₀A, L', n, m, hc₀Ω, hL', hn, hm, hiso, hQ, hxK, hfield, -⟩ := h5
  rw [← hYΔ] at hiso hQ hxK hfield
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM : Y ≤ Y ⊔ A := le_sup_left
  have hAM : A ≤ Y ⊔ A := le_sup_right
  haveI hYn : (Y.subgroupOf (Y ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr (sup_le Subgroup.le_normalizer hAY)
  haveI hKn : (img148 A Y Y).Normal :=
    Subgroup.Normal.map hYn (QuotientGroup.mk' (ker148 A Y)) (QuotientGroup.mk'_surjective _)
  have hc₀3 : c₀ ^ 3 = 1 := hA.1.2 c₀ hc₀A
  have hx : alpha148 A Y c₀ hc₀A =
      QuotientGroup.mk' (ker148 A Y) (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) := rfl
  have hx3 : alpha148 A Y c₀ hc₀A ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hc₀3)
    rw [this, map_one]
  have hxne : alpha148 A Y c₀ hc₀A ≠ 1 := fun h => hxK (h ▸ (img148 A Y Y).one_mem)
  have hxord : orderOf (alpha148 A Y c₀ hc₀A) = 3 := orderOf_eq_prime hx3 hxne
  have hxN : alpha148 A Y c₀ hc₀A ∈ Subgroup.normalizer ((img148 A Y Y : Subgroup _) : Set _) :=
    (Subgroup.normalizer_eq_top_iff.mpr hKn) ▸ Subgroup.mem_top _
  have hQtop : img148 A Y Y ⊔ Subgroup.zpowers (alpha148 A Y c₀ hc₀A) = ⊤ := by
    rw [← hQ]
    simp only [img148, Subgroup.subgroupOf_self]
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hAabG : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun x hx y hy =>
    congrArg Subtype.val (hR.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA3G : ∀ a ∈ A, a ^ 3 = 1 := fun a ha => hR.isElemAbelian.2 a ha
  have hNn : ¬ 3 ∣ Nat.card (ker148 A Y) := not_three_dvd_card_ker148 hAY
  have hNY : ker148 A Y ≤ Y.subgroupOf (Y ⊔ A) := fun x hx => pPrimeCoreOf_le 3 Y hx
  have hAab : ∀ a ∈ A.subgroupOf (Y ⊔ A), ∀ b ∈ A.subgroupOf (Y ⊔ A), a * b = b * a :=
    fun a ha b hb => Subtype.ext (hAabG _ ha _ hb)
  have hA27 : Nat.card (A.subgroupOf (Y ⊔ A)) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hA.2
  have hA3 : IsPGroup 3 (A.subgroupOf (Y ⊔ A)) :=
    IsPGroup.of_card (n := 3) (by rw [hA27]; norm_num)
  have hinj : ∀ a ∈ A.subgroupOf (Y ⊔ A), QuotientGroup.mk' (ker148 A Y) a = 1 → a = 1 := by
    intro a ha h
    have hAN := inf_eq_bot_of_isPGroup_of_not_dvd hNn hA3
    have : a ∈ A.subgroupOf (Y ⊔ A) ⊓ ker148 A Y := ⟨ha, (QuotientGroup.eq_one_iff a).mp h⟩
    rw [hAN] at this
    exact this
  have hcM : (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ∈ A.subgroupOf (Y ⊔ A) := hc₀A
  have hcMY : (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ∉ Y.subgroupOf (Y ⊔ A) := by
    intro h
    apply hxK
    rw [hx]
    exact Subgroup.mem_map_of_mem _ h
  have hcM3 : (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ 3 = 1 := Subtype.ext (by simpa using hc₀3)
  have hAdec : ∀ a ∈ A.subgroupOf (Y ⊔ A), ∃ a₁ ∈ A.subgroupOf (Y ⊔ A) ⊓ Y.subgroupOf (Y ⊔ A),
      ∃ i : ℕ, a = a₁ * (⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i := by
    intro a ha
    have hmem : QuotientGroup.mk' (ker148 A Y) a ∈
        img148 A Y Y ⊔ Subgroup.zpowers (alpha148 A Y c₀ hc₀A) := hQtop ▸ Subgroup.mem_top _
    have hmem' : QuotientGroup.mk' (ker148 A Y) a ∈
        (↑(img148 A Y Y) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) *
          ↑(Subgroup.zpowers (alpha148 A Y c₀ hc₀A)) := by
      rw [← Subgroup.normal_mul]
      exact hmem
    obtain ⟨k, hk, z, hz, hkz⟩ := hmem'
    obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).mpr hz
    obtain ⟨y₁, hy₁, hy₁k⟩ := hk
    have hz' : z = QuotientGroup.mk' (ker148 A Y)
        ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i) := by
      rw [map_pow, ← hx]
      exact hi.symm
    refine ⟨a * ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i)⁻¹,
      ⟨(A.subgroupOf (Y ⊔ A)).mul_mem ha
        ((A.subgroupOf (Y ⊔ A)).inv_mem ((A.subgroupOf (Y ⊔ A)).pow_mem hcM i)), ?_⟩, i, by group⟩
    have hmk : QuotientGroup.mk' (ker148 A Y)
        (a * ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i)⁻¹) = QuotientGroup.mk' (ker148 A Y) y₁ := by
      rw [map_mul, map_inv, ← hz', hy₁k, ← hkz]
      group
    have hyn : y₁⁻¹ * (a * ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i)⁻¹) ∈ ker148 A Y :=
      QuotientGroup.eq.mp hmk.symm
    have hdec : a * ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i)⁻¹ =
        y₁ * (y₁⁻¹ * (a * ((⟨c₀, hAM hc₀A⟩ : ↥(Y ⊔ A)) ^ i)⁻¹)) := by group
    rw [hdec]
    exact (Y.subgroupOf (Y ⊔ A)).mul_mem hy₁ (hNY hyn)
  have hA₀ab : ∀ x ∈ (A.subgroupOf (Y ⊔ A) ⊓ Y.subgroupOf (Y ⊔ A)).map
      (QuotientGroup.mk' (ker148 A Y)), ∀ y ∈ (A.subgroupOf (Y ⊔ A) ⊓ Y.subgroupOf (Y ⊔ A)).map
      (QuotientGroup.mk' (ker148 A Y)), x * y = y * x := by
    rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨b₁, hb₁, rfl⟩
    rw [← map_mul, ← map_mul, hAab a₁ ha₁.1 b₁ hb₁.1]
  have hfus := hL3 (↥(Y ⊔ A) ⧸ ker148 A Y) (img148 A Y Y) (alpha148 A Y c₀ hc₀A) n hn hiso hxN
    hxord hxK hQtop hfield
    ((A.subgroupOf (Y ⊔ A) ⊓ Y.subgroupOf (Y ⊔ A)).map (QuotientGroup.mk' (ker148 A Y)))
    (Subgroup.map_mono inf_le_right)
    (by
      rintro _ ⟨a₁, ha₁, rfl⟩
      rw [hx, ← map_mul, ← map_mul, hAab a₁ ha₁.1 _ hcM])
    ((card_map_of_injOn _ inf_le_left hinj).trans
      (card_inf_eq_nine _ _ hA27 _ hcM hcMY hcM3 hAdec))
    ⟨⟨⟨fun a b => Subtype.ext (hA₀ab a a.2 b b.2)⟩⟩, by
      rintro _ ⟨a₁, ha₁, rfl⟩
      have h3 : a₁ ^ 3 = 1 := Subtype.ext (hA3G a₁ ha₁.1)
      rw [← map_pow, h3, map_one]⟩
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  refine mem_scriptQ_of_hyperplanes hA (h142 G A c L hS) hV hP3 hAP ?_
  intro B hB hBΩ p hp
  have hpP : p ∈ P := hp.1
  have hpB : p ∈ Subgroup.centralizer (B : Set G) := hp.2
  have hpY : p ∈ Y := hPY hpP
  have hBle : B ≤ A := hB.1
  have hB9 : Nat.card (B.subgroupOf (Y ⊔ A)) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBle.trans hAM)).toEquiv]
    have := hB.2
    rw [hA.2] at this
    omega
  have hpN := l3_fusion_core (ker148 A Y) (Y.subgroupOf (Y ⊔ A)) (A.subgroupOf (Y ⊔ A)) hNn hNY
    hA3 hAab ⟨c₀, hAM hc₀A⟩ hcM hAdec
    {F' | ∃ F ∈ omegaA A, F' = F.subgroupOf (Y ⊔ A)}
    ⟨Subgroup.zpowers c₀, hc₀Ω, zpowers_subgroupOf (hAM hc₀A)⟩
    (fun m hm F' hF' => by
      obtain ⟨F, hF, rfl⟩ := hF'
      obtain ⟨F₂, hF₂, heq⟩ := exists_omega_conj_subgroupOf hAM hF hm
      exact ⟨F₂, hF₂, heq⟩) hfus
    (B.subgroupOf (Y ⊔ A)) (fun x hx => hBle hx) hB9
    (by
      rintro F' ⟨F, hF, rfl⟩ hle
      refine hBΩ F hF fun x hx => ?_
      have hxY : x ∈ Y ⊔ A := hAM (hF.1 hx)
      exact hle (show (⟨x, hxY⟩ : ↥(Y ⊔ A)) ∈ F.subgroupOf (Y ⊔ A) from hx))
    ⟨p, hYM hpY⟩ hpY
    (fun b hb => Subtype.ext ((Subgroup.mem_centralizer_iff.mp hpB b hb).symm))
    (by
      obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩)
  obtain ⟨k, hk⟩ := hP2 ⟨p, hpP⟩
  exact mem_pCoreOf_of_mem_pPrimeCoreOf hY hpY hpN ⟨k, by simpa using congrArg Subtype.val hk⟩

end Certs

end CFSG.RankThree.PartTwo.Sec15.ThmD
