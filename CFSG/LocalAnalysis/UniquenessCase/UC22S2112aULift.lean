module

public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.BNPair.Lemma3013

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

theorem uc22s2112u_mem_normalizer_of_inv {Γ : Type*} [Group Γ] {B : Subgroup Γ} {t : Γ}
    (ht : ∀ b ∈ B, t * b * t⁻¹ = b⁻¹) : t ∈ normalizer (B : Set Γ) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [ht g hg]
    exact B.inv_mem hg
  · intro hg
    have h1 : t * (t * g * t⁻¹)⁻¹ * t⁻¹ = t * g * t⁻¹ := by
      rw [ht _ (B.inv_mem hg), inv_inv]
    have h2 : (t * g * t⁻¹)⁻¹ = g := mul_left_cancel (mul_right_cancel h1)
    rw [← h2]
    exact B.inv_mem hg

theorem uc22s2112u_lift_inv {Γ H : Type*} [Group Γ] [Finite Γ] [Group H] (φ : Γ →* H)
    {B S : Subgroup Γ} (hS : IsPGroup 2 S) (hBo : Odd (Nat.card B))
    (hBS : (B : Set Γ) * S = S * B) (hfaith : ∀ b ∈ B, φ b = 1 → b = 1) {s : Γ} (hs : s ∈ S)
    (hinv : ∀ b ∈ B, φ s * φ b * (φ s)⁻¹ = (φ b)⁻¹) :
    ∃ t ∈ S, ∀ b ∈ B, t * b * t⁻¹ = b⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ x ∈ S, ∀ b ∈ B, φ (x * b) = 1 → b = 1 := by
    intro x hx b hb h
    apply hfaith b hb
    rw [map_mul] at h
    have h1 : φ b = (φ x)⁻¹ := eq_inv_of_mul_eq_one_right h
    obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf (φ b) ∣ 2 ^ k := by
      rw [h1, orderOf_inv]
      exact (orderOf_map_dvd φ x).trans (orderOf_dvd_of_pow_eq_one hxk)
    have h3 : orderOf (φ b) ∣ Nat.card B :=
      (orderOf_map_dvd φ b).trans (Subgroup.orderOf_dvd_natCard B hb)
    have hcop : Nat.Coprime (2 ^ k) (Nat.card B) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hBo)
    exact orderOf_eq_one_iff.1
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3)
  have hBS' : ∀ b ∈ B, ∀ x ∈ S, ∃ y ∈ S, ∃ c ∈ B, b * x = y * c := by
    intro b hb x hx
    have h : b * x ∈ (B : Set Γ) * S := Set.mul_mem_mul hb hx
    rw [hBS] at h
    obtain ⟨y, hy, c, hc, hyc⟩ := h
    exact ⟨y, hy, c, hc, hyc.symm⟩
  set K : Subgroup Γ := S ⊓ φ.ker with hKdef
  have hKS : K ≤ S := inf_le_left
  have hmemK : ∀ {x : Γ}, x ∈ K ↔ x ∈ S ∧ φ x = 1 := by
    intro x
    rw [hKdef, mem_inf, MonoidHom.mem_ker]
  have hBK : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := by
    intro b hb k hk
    obtain ⟨hkS, hk1⟩ := hmemK.1 hk
    obtain ⟨y, hy, c, hc, hbk⟩ := hBS' b hb k hkS
    have hφ : φ (b * k * b⁻¹) = 1 := by simp [map_mul, hk1]
    have hc1 : c * b⁻¹ = 1 := by
      refine key y hy (c * b⁻¹) (B.mul_mem hc (B.inv_mem hb)) ?_
      rw [← mul_assoc, ← hbk]
      exact hφ
    have heq : b * k * b⁻¹ = y := by rw [hbk, mul_assoc, hc1, mul_one]
    refine hmemK.2 ⟨?_, hφ⟩
    rw [heq]
    exact hy
  have hBnorm : B ≤ normalizer (K : Set Γ) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro g
    refine ⟨hBK b hb g, fun hg => ?_⟩
    have h := hBK b⁻¹ (B.inv_mem hb) _ hg
    simpa [mul_assoc] using h
  have hsK : ∀ b ∈ B, s * b * s⁻¹ * b ∈ K := by
    intro b hb
    have hφ : φ (s * b * s⁻¹ * b) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hinv b hb, inv_mul_cancel]
    obtain ⟨y, hy, c, hc, hbs⟩ := hBS' b hb s⁻¹ (S.inv_mem hs)
    have hsb : s * b * s⁻¹ * b = s * y * (c * b) := by
      rw [mul_assoc s b s⁻¹, hbs]
      simp only [mul_assoc]
    have hcb : c * b = 1 := by
      refine key (s * y) (S.mul_mem hs hy) (c * b) (B.mul_mem hc hb) ?_
      rw [← hsb]
      exact hφ
    refine hmemK.2 ⟨?_, hφ⟩
    rw [hsb, hcb, mul_one]
    exact S.mul_mem hs hy
  set Bs : Subgroup Γ := B.map (MulAut.conj s).toMonoidHom with hBsdef
  have hmemBs : ∀ b ∈ B, s * b * s⁻¹ ∈ Bs := fun b hb =>
    ⟨b, hb, by simp [MulAut.conj_apply]⟩
  have hsup : B ⊔ K = Bs ⊔ K := by
    apply le_antisymm
    · refine sup_le (fun b hb => ?_) le_sup_right
      have h1 := hsK b⁻¹ (B.inv_mem hb)
      have hb' : b = (s * b⁻¹ * s⁻¹ * b⁻¹)⁻¹ * (s * b⁻¹ * s⁻¹) := by group
      rw [hb']
      exact mul_mem (mem_sup_right (inv_mem h1)) (mem_sup_left (hmemBs _ (B.inv_mem hb)))
    · refine sup_le ?_ le_sup_right
      rintro _ ⟨b, hb, rfl⟩
      have h1 := hsK b hb
      have hb' : (MulAut.conj s).toMonoidHom b = s * b * s⁻¹ * b * b⁻¹ := by
        simp [MulAut.conj_apply]
      rw [hb']
      exact mul_mem (mem_sup_right h1) (mem_sup_left (B.inv_mem hb))
  set X : Subgroup Γ := B ⊔ K with hXdef
  haveI : (K.subgroupOf X).Normal := normal_subgroupOf_sup_of_le_normalizer hBnorm
  have hBX : B ≤ X := le_sup_left
  have hKX : K ≤ X := le_sup_right
  have hBsX : Bs ≤ X := by
    rw [hsup]
    exact le_sup_left
  have hE : IsPGroup 2 (K.subgroupOf X) :=
    (hS.to_le hKS).of_equiv (subgroupOfEquivOfLe hKX).symm
  have hZp : ¬ 2 ∣ Nat.card (B.subgroupOf X) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv]
    exact hBo.not_two_dvd_nat
  have hdisj : ∀ {W : Subgroup Γ}, (∀ w ∈ W, w ∈ K → w = 1) →
      Disjoint (K.subgroupOf X) (W.subgroupOf X) := by
    intro W hW
    rw [disjoint_def]
    intro x hx1 hx2
    exact Subtype.ext (hW _ (mem_subgroupOf.1 hx2) (mem_subgroupOf.1 hx1))
  have hKB : ∀ w ∈ B, w ∈ K → w = 1 := fun w hw hwK => hfaith w hw (hmemK.1 hwK).2
  have hKBs : ∀ w ∈ Bs, w ∈ K → w = 1 := by
    rintro _ ⟨b, hb, rfl⟩ hK
    have h := (hmemK.1 hK).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv] at h
    rw [hinv b hb] at h
    rw [hfaith b hb (inv_eq_one.1 h)]
    simp
  have htop : ∀ {W : Subgroup Γ}, W ≤ X → W ⊔ K = X → K.subgroupOf X ⊔ W.subgroupOf X = ⊤ := by
    intro W hW hWK
    rw [← subgroupOf_sup hKX hW, sup_comm, hWK, subgroupOf_self]
  obtain ⟨n, hn, hnY⟩ := CFSG.GH74.BNPair.exists_conj_of_complements_top (p := 2) hE hZp
    (hdisj hKB) (hdisj hKBs) (htop hBX rfl) (htop hBsX hsup.symm)
  have hnK : (n : Γ) ∈ K := mem_subgroupOf.1 hn
  refine ⟨(n : Γ) * s, S.mul_mem (hKS hnK) hs, fun b hb => ?_⟩
  have hbX : s * b * s⁻¹ ∈ X := hBsX (hmemBs b hb)
  have h1 : (⟨s * b * s⁻¹, hbX⟩ : X) ∈ Bs.subgroupOf X := mem_subgroupOf.2 (hmemBs b hb)
  have h2 : n * ⟨s * b * s⁻¹, hbX⟩ * n⁻¹ ∈ B.subgroupOf X := by
    rw [← hnY]
    exact mem_map.2 ⟨_, h1, by simp [MulAut.conj_apply]⟩
  have h3 : (n : Γ) * s * b * ((n : Γ) * s)⁻¹ ∈ B := by
    have h := mem_subgroupOf.1 h2
    simpa [mul_assoc] using h
  have hφn : φ (n : Γ) = 1 := (hmemK.1 hnK).2
  have h4 : φ ((n : Γ) * s * b * ((n : Γ) * s)⁻¹ * b) = 1 := by
    simp only [map_mul, map_inv, hφn, one_mul]
    rw [hinv b hb, inv_mul_cancel]
  exact eq_inv_of_mul_eq_one_left (hfaith _ (B.mul_mem h3 hb) h4)

end CFSG.LocalAnalysis.UniquenessCase.UC22
