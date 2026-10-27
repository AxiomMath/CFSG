module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c167_frame_odd_inf_le_centerF {A : Type*} [Group A] {X F O : Subgroup A}
    (hFX : F ≤ X) (hOn : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O) (hodd : Odd (Nat.card O))
    (hoddF : ∀ N : Subgroup ↥F, N.Normal → Odd (Nat.card N) → N ≤ Subgroup.center ↥F) :
    O ⊓ F ≤ (Subgroup.center ↥F).map F.subtype := by
  intro y hy
  rw [Subgroup.mem_map]
  have hN : ((O ⊓ F).subgroupOf F).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnO, hnF⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := hOn (g : A) (hFX g.2) (n : A) hnO
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
    · exact F.mul_mem (F.mul_mem g.2 hnF) (F.inv_mem g.2)
  have hcard : Nat.card ↥((O ⊓ F).subgroupOf F) = Nat.card ↥(O ⊓ F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ F ≤ F)).toEquiv
  have hdvd : Nat.card ↥((O ⊓ F).subgroupOf F) ∣ Nat.card O := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le (inf_le_left : O ⊓ F ≤ O)
  have hoddN : Odd (Nat.card ↥((O ⊓ F).subgroupOf F)) := Odd.of_dvd_nat hodd hdvd
  have hmem : (⟨y, hy.2⟩ : ↥F) ∈ (O ⊓ F).subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact hy
  exact ⟨⟨y, hy.2⟩, hoddF ((O ⊓ F).subgroupOf F) hN hoddN hmem, rfl⟩

theorem s16c167_frame_centralizer_le_centerF {A : Type*} [Group A] {X F O : Subgroup A}
    (hFX : F ≤ X) (hOX : O ≤ X) (hFn : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hOn : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O)
    (hself : ∀ y ∈ X, (∀ f ∈ F, y * f = f * y) → y ∈ F)
    (hOF : O ⊓ F ≤ (Subgroup.center ↥F).map F.subtype)
    (hsup : Subgroup.center ↥F ⊔ commutator ↥F = ⊤)
    (hinf : Subgroup.center ↥F ⊓ commutator ↥F = ⊥) :
    ∀ y ∈ O, (∀ z ∈ (Subgroup.center ↥F).map F.subtype, y * z = z * y) →
      y ∈ (Subgroup.center ↥F).map F.subtype := by
  intro y hyO hycent
  have hyX : y ∈ X := hOX hyO
  let κ : ↥F →* ↥F :=
    { toFun := fun f => ⟨y * (f : A) * y⁻¹, hFn y hyX f f.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        ext
        simp only [Subgroup.coe_mul]
        group }
  have hκ : Subgroup.map κ (commutator ↥F) ≤ commutator ↥F := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top]
    exact commutator_mono le_top le_top
  have step1 : ∀ p ∈ (commutator ↥F).map F.subtype, y * p = p * y := by
    intro p hp
    rw [Subgroup.mem_map] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have hcP : (c : A) ∈ (commutator ↥F).map F.subtype :=
      Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    have hconjP : y * (c : A) * y⁻¹ ∈ (commutator ↥F).map F.subtype :=
      Subgroup.mem_map.mpr ⟨κ c, hκ (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩), rfl⟩
    have hdP : y * (c : A) * y⁻¹ * (c : A)⁻¹ ∈ (commutator ↥F).map F.subtype :=
      ((commutator ↥F).map F.subtype).mul_mem hconjP
        (((commutator ↥F).map F.subtype).inv_mem hcP)
    have hconjF : y * (c : A) * y⁻¹ ∈ F := (κ c).2
    have hdF : y * (c : A) * y⁻¹ * (c : A)⁻¹ ∈ F :=
      F.mul_mem hconjF (F.inv_mem c.2)
    have hpy : (c : A) * y⁻¹ * (c : A)⁻¹ ∈ O :=
      hOn (c : A) (hFX c.2) y⁻¹ (O.inv_mem hyO)
    have hdO : y * (c : A) * y⁻¹ * (c : A)⁻¹ ∈ O := by
      have h := O.mul_mem hyO hpy
      simpa only [mul_assoc] using h
    have hdZ : y * (c : A) * y⁻¹ * (c : A)⁻¹ ∈ (Subgroup.center ↥F).map F.subtype :=
      hOF (Subgroup.mem_inf.mpr ⟨hdO, hdF⟩)
    have hZcP : (Subgroup.center ↥F).map F.subtype ⊓
        (commutator ↥F).map F.subtype = ⊥ := by
      rw [← Subgroup.map_inf_eq _ _ F.subtype F.subtype_injective, hinf, Subgroup.map_bot]
    have hd1 : y * (c : A) * y⁻¹ * (c : A)⁻¹ = 1 := by
      have hmem : y * (c : A) * y⁻¹ * (c : A)⁻¹ ∈ (⊥ : Subgroup A) := by
        rw [← hZcP]
        exact ⟨hdZ, hdP⟩
      exact Subgroup.mem_bot.mp hmem
    have hconj_eq : y * (c : A) * y⁻¹ = (c : A) := mul_inv_eq_one.mp hd1
    calc y * (c : A) = y * (c : A) * y⁻¹ * y := by group
      _ = (c : A) * y := by rw [hconj_eq]
  let K : Subgroup A := Subgroup.centralizer ({(y : A)} : Set A)
  have hZc_le : (Subgroup.center ↥F).map F.subtype ≤ K := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hycent z hz
  have hP_le : (commutator ↥F).map F.subtype ≤ K := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact step1 p hp
  have hF : (Subgroup.center ↥F).map F.subtype ⊔ (commutator ↥F).map F.subtype = F := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, Subgroup.range_subtype]
  have hF_le : F ≤ K := by
    rw [← hF]
    exact sup_le hZc_le hP_le
  have hyF : y ∈ F :=
    hself y hyX (fun f hf =>
      (Subgroup.mem_centralizer_iff.mp (hF_le hf)) y (Set.mem_singleton y))
  exact hOF (Subgroup.mem_inf.mpr ⟨hyO, hyF⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
