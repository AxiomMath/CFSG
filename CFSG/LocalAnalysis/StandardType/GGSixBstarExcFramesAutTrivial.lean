module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCentralize
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFixedField
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.Open
open scoped Pointwise

section FiniteSup

variable {Γ : Type*} [Group Γ]

theorem finite_sup_of_le_normalizer (C Dg : Subgroup Γ)
    (hDg : Dg ≤ Subgroup.normalizer (C : Set Γ)) [Finite C] [Finite Dg] :
    Finite ↥(C ⊔ Dg) := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right Dg C hDg
  have hfin : (((Dg ⊔ C : Subgroup Γ)) : Set Γ).Finite := by
    rw [h]
    exact Set.Finite.mul (Set.toFinite _) (Set.toFinite _)
  rw [sup_comm]
  exact hfin.to_subtype

end FiniteSup

section Trivial

variable {τ : Tag} {K : Type} [Field K] [Finite K] {p m k : ℕ} [Fact p.Prime]

theorem trivial_on_stable_of_normalForm (Dg : Subgroup (ModGL τ K)) [Finite Dg]
    (hDg : Dg ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K))) (hk : ¬ p ∣ k)
    (hkDg : ∀ d ∈ Dg, d ^ k ∈ adjointGroup τ K)
    (hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) →
        SylowTorus (adjointGroup τ K₀) p m)
    {α : MulAut (adjointGroup τ K)} (hαp : α ^ p = 1) {x : ModGL τ K}
    (hx : x ∈ adjointGroup τ K ⊔ Dg) {σ : K ≃+* K} (hσ : σ ^ p = 1)
    (hα : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      x * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * x⁻¹)
    {Bs : Subgroup (adjointGroup τ K)} (hBs : IsElemAbelian p Bs) (hBsc : p ^ m ≤ Nat.card Bs)
    (hstable : ∀ b ∈ Bs, α b ∈ Bs) : ∀ b ∈ Bs, α b = b := by
  classical
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  haveI : Finite ↥(adjointGroup τ K ⊔ Dg) := finite_sup_of_le_normalizer _ _ hDg
  set s : ModGL τ K →* ModGL τ K := Units.map (entrywiseHom σ.toRingHom) with hs
  have hSyl : SylowTorus (adjointGroup τ K) p m := hdata K rfl
  have hxN : x ∈ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)) :=
    (sup_le Subgroup.le_normalizer hDg : adjointGroup τ K ⊔ Dg ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K))) hx
  have hsC : ∀ h ∈ adjointGroup τ K, s h ∈ adjointGroup τ K := by
    intro h hh
    have h1 := hα ⟨h, hh⟩
    have h2 : s h = x⁻¹ * ((α ⟨h, hh⟩ : adjointGroup τ K) : ModGL τ K) * x := by
      rw [h1]
      group
    rw [h2]
    have hαC : ((α ⟨h, hh⟩ : adjointGroup τ K) : ModGL τ K) ∈ adjointGroup τ K := (α ⟨h, hh⟩).2
    have h3 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) _).1 hαC
    rwa [inv_inv] at h3
  obtain ⟨E, hE, hEc, hEs⟩ := exists_fixedElemAbelian σ hσ hdata
  have hEmap : IsElemAbelian p (E.map (adjointGroup τ K).subtype) := isElemAbelian_map_frame (adjointGroup τ K).subtype hE
  have hEcard : p ^ m ≤ Nat.card (E.map (adjointGroup τ K).subtype) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hEc]
  have hEfix : ∀ e ∈ E.map (adjointGroup τ K).subtype, s e = e := by
    rintro _ ⟨e, he, rfl⟩
    exact hEs e he
  have hBmap : IsElemAbelian p (Bs.map (adjointGroup τ K).subtype) := isElemAbelian_map_frame (adjointGroup τ K).subtype hBs
  have hBcard : p ^ m ≤ Nat.card (Bs.map (adjointGroup τ K).subtype) := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective]
    exact hBsc
  have hnorm : ∀ b ∈ Bs.map (adjointGroup τ K).subtype, x * s b * x⁻¹ ∈ Bs.map (adjointGroup τ K).subtype := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨α b, hstable b hb, hα b⟩
  have hit : ∀ j : ℕ, ∀ b : adjointGroup τ K, (fun h => x * s h * x⁻¹)^[j] (b : ModGL τ K) =
      (((α ^ j) b : adjointGroup τ K) : ModGL τ K) := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [Function.iterate_succ_apply', ih b]
      show x * s (((α ^ j) b : adjointGroup τ K) : ModGL τ K) * x⁻¹ = _
      rw [← hα, pow_succ', MulAut.mul_apply]
  have hord : ∀ b ∈ Bs.map (adjointGroup τ K).subtype, (fun h => x * s h * x⁻¹)^[p] b = b := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 := hit p b
    rw [hαp] at h1
    exact h1
  have key := fixes_of_sylowTorus_of_fixedSubgroup (C := adjointGroup τ K) (Dg := Dg) hDg hk hkDg hSyl s hsC
    (Subgroup.map_subtype_le E) hEmap hEcard hEfix (Subgroup.map_subtype_le Bs) hBmap hBcard hx
    hnorm hord
  intro b hb
  have h1 := key b ⟨b, hb, rfl⟩
  refine Subtype.ext ?_
  rw [hα b]
  exact h1

theorem centralizes_of_induced_exists {G : Type} [Group G] (hk : ¬ p ∣ k)
    (hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) →
        SylowTorus (adjointGroup τ K₀) p m)
    (hNF : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      ∃ (Dg : Subgroup (ModGL τ K)) (x : ModGL τ K) (σ : K ≃+* K),
        Dg ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K)) ∧
        (∀ d ∈ Dg, d ^ k ∈ adjointGroup τ K) ∧ x ∈ adjointGroup τ K ⊔ Dg ∧ σ ^ p = 1 ∧
        ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
          x * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * x⁻¹)
    (ψ : adjointGroup τ K →* G) (hψ : Function.Injective ψ) {Bs : Subgroup G}
    (hBsR : Bs ≤ ψ.range) (hBs : IsElemAbelian p Bs) (hBsc : p ^ m ≤ Nat.card Bs) {g : G}
    (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) (hgp : g ^ p = 1) :
    g ∈ Subgroup.centralizer (Bs : Set G) := by
  classical
  haveI : Finite (adjointGroup τ K) := generated_group_finite τ K
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨α, hα⟩ := exists_inducedAut ψ hψ hgN
  have hαp : α ^ p = 1 := inducedAut_pow_eq_one ψ hψ hα hgp
  obtain ⟨Dg, x, σ, hDg, hkDg, hx, hσ, hαx⟩ := hNF α hαp
  have hBs' : IsElemAbelian p (Bs.comap ψ) := isElemAbelian_comap_frame ψ hψ hBs
  have hcard : p ^ m ≤ Nat.card (Bs.comap ψ) := by
    rw [card_comap_of_le_range ψ hψ hBsR]
    exact hBsc
  have hstable : ∀ b ∈ Bs.comap ψ, α b ∈ Bs.comap ψ := by
    intro b hb
    have hb' : ψ b ∈ Bs := hb
    show ψ (α b) ∈ Bs
    rw [hα b]
    exact (Subgroup.mem_normalizer_iff.1 hgB (ψ b)).1 hb'
  have hfix := trivial_on_stable_of_normalForm Dg hDg hk hkDg hdata hαp hx hσ hαx hBs' hcard hstable
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨b, rfl⟩ := hBsR hy
  have h1 := hα b
  rw [hfix b hy] at h1
  exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm

theorem centralizes_of_induced {G : Type} [Group G] (Dg : Subgroup (ModGL τ K)) [Finite Dg]
    (hDg : Dg ≤ Subgroup.normalizer (adjointGroup τ K : Set (ModGL τ K))) (hk : ¬ p ∣ k)
    (hkDg : ∀ d ∈ Dg, d ^ k ∈ adjointGroup τ K)
    (hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) →
        SylowTorus (adjointGroup τ K₀) p m)
    (hNF : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      ∃ (x : ModGL τ K) (σ : K ≃+* K), x ∈ adjointGroup τ K ⊔ Dg ∧ σ ^ p = 1 ∧
        ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
          x * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * x⁻¹)
    (ψ : adjointGroup τ K →* G) (hψ : Function.Injective ψ) {Bs : Subgroup G}
    (hBsR : Bs ≤ ψ.range) (hBs : IsElemAbelian p Bs) (hBsc : p ^ m ≤ Nat.card Bs) {g : G}
    (hgN : g ∈ Subgroup.normalizer (ψ.range : Set G))
    (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) (hgp : g ^ p = 1) :
    g ∈ Subgroup.centralizer (Bs : Set G) :=
  centralizes_of_induced_exists hk hdata (fun α hα => by
    obtain ⟨x, σ, hx, hσ, h⟩ := hNF α hα
    exact ⟨Dg, x, σ, hDg, hkDg, hx, hσ, h⟩) ψ hψ hBsR hBs hBsc hgN hgB hgp

end Trivial

end ExcFrames

end CFSG.StandardType
