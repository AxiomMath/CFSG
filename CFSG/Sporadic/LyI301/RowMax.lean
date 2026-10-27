module

public import CFSG.Sporadic.LyI301.RowLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max
public import CFSG.Sporadic.LyI301.RowBasic

public noncomputable section

namespace CFSG.Sporadic.LyI301

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.LyonsSims CFSG.Certificates
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301

variable {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

private theorem exists_mem_normalizer_of_not_le {R' : Subgroup G} (hR : IsPGroup 2 R')
    (hRR : lyR ρ ≤ R') (hne : ¬ R' ≤ lyR ρ) :
    ∃ y ∈ R', y ∈ Subgroup.normalizer (lyR ρ : Set G) ∧ y ∉ lyR ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hR.isNilpotent
  set Q' : Subgroup R' := (lyR ρ).subgroupOf R'
  have hlt : Q' < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne fun r hr => ?_
    have h1 : (⟨r, hr⟩ : R') ∈ Q' := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h1
  obtain ⟨y, hyN, hyQ⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q' hlt)
  have hconj : ∀ u : R', u ∈ Subgroup.normalizer (Q' : Set R') → ∀ q ∈ lyR ρ,
      (u : G) * q * (u : G)⁻¹ ∈ lyR ρ := by
    intro u hu q hq
    have h1 := (Subgroup.mem_normalizer_iff.1 hu ⟨q, hRR hq⟩).1 (Subgroup.mem_subgroupOf.2 hq)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have hN : (y : G) ∈ Subgroup.normalizer (lyR ρ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hconj y hyN q, fun hq => ?_⟩
    have h := hconj y⁻¹ ((Subgroup.normalizer (Q' : Set R')).inv_mem hyN) _ hq
    rw [Subgroup.coe_inv, inv_inv] at h
    have e : (y : G)⁻¹ * ((y : G) * q * (y : G)⁻¹) * (y : G) = q := by group
    rwa [e] at h
  exact ⟨y, y.2, hN, fun h => hyQ (Subgroup.mem_subgroupOf.2 h)⟩

private theorem rho_normalizes (D : LyData G t ρ) {h : ↥(centralizer ({t} : Set G))}
    (hh : (h : G) ∈ Subgroup.normalizer (lyR ρ : Set G)) :
    (∀ σ ∈ lyVS, ρ h * σ * (ρ h)⁻¹ ∈ lyVS) ∧ ∀ σ ∈ lyVS, (ρ h)⁻¹ * σ * ρ h ∈ lyVS := by
  refine ⟨fun σ hσ => rho_conj_mem_lyVS D hh hσ, fun σ hσ => ?_⟩
  have hi : ((h⁻¹ : ↥(centralizer ({t} : Set G))) : G) ∈ Subgroup.normalizer (lyR ρ : Set G) := by
    rw [Subgroup.coe_inv]
    exact Subgroup.inv_mem _ hh
  have := rho_conj_mem_lyVS D hi hσ
  rwa [map_inv, inv_inv] at this


theorem eq_lyR_of_invariant (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (R' : Subgroup G)
    (hR : IsPGroup 2 R') (hB : lyB1 x₁ x₂ x₃ ≤ Subgroup.normalizer (R' : Set G))
    (hRR : lyR ρ ≤ R') : R' = lyR ρ := by
  refine le_antisymm ?_ hRR
  by_contra hne
  obtain ⟨y, hyR, hyN, hyQ⟩ := exists_mem_normalizer_of_not_le hR hRR hne
  let N : Subgroup G := R' ⊓ Subgroup.normalizer (lyR ρ : Set G)
  let YE : Subgroup ↥(centralizer ({t} : Set G)) := N.comap (centralizer ({t} : Set G)).subtype
  let Y : Subgroup (Perm (Fin 11)) := YE.map ρ
  have hY2 : IsPGroup 2 Y :=
    ((hR.to_le inf_le_left).comap_of_injective _ (centralizer ({t} : Set G)).subtype_injective).map ρ
  have hNt : N ≤ centralizer ({t} : Set G) := inf_le_right.trans (normalizer_lyR_le D)
  have hVY : lyVS ≤ Y := by
    intro σ hσ
    obtain ⟨r, hr⟩ := D.cover.exists_lift (lyVS_le_alternatingGroup hσ)
    have hrR : (r : G) ∈ lyR ρ := mem_lyR.2 ⟨r, hr ▸ hσ, rfl⟩
    exact ⟨r, ⟨hRR hrR, Subgroup.le_normalizer hrR⟩, hr⟩
  have hYn : ∀ g ∈ Y, ∀ σ ∈ lyVS, g * σ * g⁻¹ ∈ lyVS := by
    rintro _ ⟨h, hh, rfl⟩ σ hσ
    exact (rho_normalizes D (Subgroup.mem_inf.1 hh).2).1 σ hσ
  have hYne : ¬ Y ≤ lyVS := by
    intro hle
    have hyt : y ∈ centralizer ({t} : Set G) := hNt ⟨hyR, hyN⟩
    have hmem : ρ ⟨y, hyt⟩ ∈ Y := ⟨⟨y, hyt⟩, ⟨hyR, hyN⟩, rfl⟩
    exact hyQ (mem_lyR.2 ⟨⟨y, hyt⟩, hle hmem, rfl⟩)
  obtain ⟨g, hgY, hgV, hg2, hgc⟩ := exists_central_mod hY2 hVY hYn hYne
  obtain ⟨h, hh, rfl⟩ := hgY
  obtain ⟨hn, hn'⟩ := rho_normalizes D (Subgroup.mem_inf.1 hh).2
  obtain ⟨σ₃, σ₈, hsplit⟩ := exists_eq_lySplit (lt_three_iff_of_normalizes hn hn')
  have hconjY : ∀ β : ↥(centralizer ({t} : Set G)), (β : G) ∈ lyB1 x₁ x₂ x₃ →
      ρ β * ρ h * (ρ β)⁻¹ ∈ Y := by
    intro β hβ
    have hβR' := hB hβ
    have hβN := ly_hBN D S hβ
    refine ⟨β * h * β⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_inv]⟩
    · show ((β * h * β⁻¹ : ↥(centralizer ({t} : Set G))) : G) ∈ R'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 hβR' _).1 (Subgroup.mem_inf.1 hh).1
    · show ((β * h * β⁻¹ : ↥(centralizer ({t} : Set G))) : G) ∈
        Subgroup.normalizer (lyR ρ : Set G)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hβN (Subgroup.mem_inf.1 hh).2)
        (Subgroup.inv_mem _ hβN)
  have hx3 : ((x₃ : ↥(centralizer ({t} : Set G))) : G) ∈ lyB1 x₁ x₂ x₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hx12 : ((x₁ * x₂ : ↥(centralizer ({t} : Set G))) : G) ∈ lyB1 x₁ x₂ x₃ := by
    rw [Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hρx3 : ρ x₃ = lyX3 := S.rho₃
  have hρx12 : ρ (x₁ * x₂) = lyX1 * lyX2 := by rw [map_mul, S.rho₁, S.rho₂]; rfl
  obtain ⟨b, hb, hbad⟩ := lySplit_inv_facts σ₃ σ₈
    (fun i => by rw [← hsplit]; exact mem_lyVS_iff.1 (hn _ (lyU_mem i)))
    (fun h' => hgV (mem_lyVS_iff.2 (hsplit ▸ h')))
    (by rw [← hsplit]; exact mem_lyVS_iff.1 hg2)
  rw [← hsplit] at hbad
  simp only [lyConj, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl
  · exact hbad (mem_lyVS_iff.1 (hgc _ (hρx3 ▸ hconjY x₃ hx3)))
  · exact hbad (mem_lyVS_iff.1 (hgc _ (hρx12 ▸ hconjY (x₁ * x₂) hx12)))

theorem ly_hMax (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (hOut : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) :
    ∀ (A : Type) [Group A] [Finite A] (ι : G →* A), Function.Injective ι →
      ι.range.Normal → Subgroup.centralizer (ι.range : Set A) = ⊥ →
      ∀ R' : Subgroup A, IsPGroup 2 R' →
        (rowKOf Row.ly.prime (x₁ : G) (lyR ρ) ⊔ lyB1 x₁ x₂ x₃).map ι ≤
          Subgroup.normalizer (R' : Set A) →
        (lyR ρ).map ι ≤ R' → R' = (lyR ρ).map ι := by
  intro A _ _ ι hι hN hC R' hR' hKB hQR'
  have htop := range_eq_top_of_forall_inner hOut ι hι hN hC
  have hR'eq : R' = (R'.comap ι).map ι := by
    rw [Subgroup.map_comap_eq, htop, top_inf_eq]
  rw [ly_K D S, bot_sup_eq] at hKB
  rw [hR'eq, eq_lyR_of_invariant D S (R'.comap ι) (hR'.comap_of_injective ι hι)
    ((Subgroup.map_le_iff_le_comap.1 hKB).trans (Subgroup.le_normalizer_comap ι))
    (Subgroup.map_le_iff_le_comap.1 hQR')]

end CFSG.Sporadic.LyI301
