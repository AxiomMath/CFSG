module

public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofT
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProofS
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Claim1721SComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      omegaA A = {Subgroup.zpowers c} →
        ∀ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) → A ≤ T →
          ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L

@[expose] def Claim1721SA10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      ¬ Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      Nonempty (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 10)) →
      omegaA A ≠ {Subgroup.zpowers c} →
        ∃ s ∈ Subgroup.normalizer (A : Set G), s * c * s⁻¹ = c⁻¹

namespace Proof1721

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_card_nine {P K : Subgroup G} (hPK : P ≤ K) (h9 : Nat.card P = 9)
    (h27 : ¬ 27 ∣ Nat.card K) : IsSylowOf 3 P K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPK, hP3, fun h3 => h27 ?_⟩
  have h := Subgroup.relIndex_mul_card P K
  rw [inf_eq_left.mpr hPK, h9] at h
  rw [← h]
  obtain ⟨k, hk⟩ := h3
  rw [hk, show (27 : ℕ) = 3 * 9 by norm_num, mul_assoc, mul_comm k 9, ← mul_assoc]
  exact Dvd.intro k rfl

variable {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}

theorem exists_inverts_c_of_omega (h : Sec17Y1 G A c L Y₀ Y₁ S p P)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (h175 : Item175 A c)
    (hcomm : ∀ T : Subgroup G, IsSylowOf 3 T (Subgroup.centralizer ({c} : Set G)) → A ≤ T →
      ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (h27 : ¬ 27 ∣ Nat.card L) :
    ∃ s ∈ Subgroup.normalizer (A : Set G), s * c * s⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs := h.toSec17Std
  have hcL : c ∉ L := hs.toSec15R.hypS.2.2 c hs.zpowers_mem_omegaA L hs.mem_lA
  have hc3 : c ^ 3 = 1 := hs.c_pow_three
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ one_mem L)
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcA : c ∈ A := hs.c_mem
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hs.commute_of_mem ha hcA)
  obtain ⟨T, hT, hAT⟩ := Item134SylowBarProof.exists_isSylowOf_le hAc hs.isE27.isPGroup
  obtain ⟨h₀, hh₀⟩ := exists_conj_eq_inv_of_weaklyClosed hs.isSimpleGroup hs.nonabelian hc hT
    (hAT hcA) (h175 hΩ) (hcomm T hT hAT) hcL
  have hh₀H : h₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (h₀ * c * h₀⁻¹) = _
    rw [hh₀, Subgroup.zpowers_inv]
  have hh₀L : h₀ ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L hs.toSec15R (three_dvd_card_L h9) hh₀H
  set E := A ⊓ L with hE
  have hEL : E ≤ L := inf_le_right
  have hE' : E.map (MulAut.conj h₀).toMonoidHom ≤ L := by
    rw [← Late.map_conj_eq_of_mem_normalizer hh₀L]
    exact Subgroup.map_mono hEL
  have hE'9 : Nat.card (E.map (MulAut.conj h₀).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h₀).injective, h9]
  obtain ⟨g, hgL, hg⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf
    (isSylowOf_of_card_nine hEL h9 h27) (isSylowOf_of_card_nine hE' hE'9 h27)
  have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp (hs.le_centralizer_c hgL)
  have hgH : g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    inv_mem (Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
      (hs.le_centralizer_c hgL))
  have hsE : g⁻¹ * h₀ ∈ Subgroup.normalizer (E : Set G) :=
    inv_mul_mem_normalizer_of_map_conj_eq hg.symm
  have hsA : g⁻¹ * h₀ ∈ Subgroup.normalizer (A : Set G) := by
    rw [eq_zpowers_sup_inf hs h9]
    exact mem_normalizer_sup (mul_mem hgH hh₀H) hsE
  refine ⟨g⁻¹ * h₀, hsA, ?_⟩
  have hgc' : g⁻¹ * c⁻¹ * g⁻¹⁻¹ = c⁻¹ := conj_inv_eq_of_commute hgc
  calc g⁻¹ * h₀ * c * (g⁻¹ * h₀)⁻¹ = g⁻¹ * (h₀ * c * h₀⁻¹) * g⁻¹⁻¹ := by group
    _ = c⁻¹ := by rw [hh₀, hgc']

end Proof1721

end CFSG.RankThree.PartTwo.Sec17
