module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.StandardType.SpJoin
open Multiplicative

namespace TypeBDatum

theorem mem_normalizer_of_frame_action {G : Type} [Group G] {p m : ℕ} {Bs X : Subgroup G}
    (Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G)
    (Θ : ((Fin m → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c)
    {n : G} (hn : n ∈ X) (τ : MulAut (Fin m → Multiplicative (ZMod p)))
    (hτ : ∀ v, n * Θ₁ v * n⁻¹ = Θ₁ (τ v)) :
    n ∈ Subgroup.normalizer (Bs : Set G) := by
  have hτinv : ∀ v, n⁻¹ * Θ₁ v * (n⁻¹)⁻¹ = Θ₁ (τ⁻¹ v) := by
    intro v
    have h := hτ (τ⁻¹ v)
    rw [MulAut.apply_inv_self] at h
    rw [← h]
    group
  have key : ∀ (y : G), y ∈ X → ∀ (ρ : MulAut (Fin m → Multiplicative (ZMod p))),
      (∀ v, y * Θ₁ v * y⁻¹ = Θ₁ (ρ v)) → ∀ b ∈ Bs, y * b * y⁻¹ ∈ Bs := by
    intro y hy ρ hρ b hb
    obtain ⟨⟨w, c⟩, hwc⟩ := Θ.surjective ⟨b, hb⟩
    have hbval : ((Θ (w, c) : ↥Bs) : G) = b := by
      simpa using congrArg Subtype.val hwc
    rw [← hbval, hΘ]
    have hxc : y * (c : G) * y⁻¹ = c := by
      have h := Subgroup.mem_centralizer_iff.mp c.2.2 y hy
      rw [h]
      group
    have hconj : y * (Θ₁ w * (c : G)) * y⁻¹ = ((Θ (ρ w, c) : ↥Bs) : G) := by
      rw [hΘ (ρ w) c]
      calc y * (Θ₁ w * (c : G)) * y⁻¹
          = (y * Θ₁ w * y⁻¹) * (y * (c : G) * y⁻¹) := by group
        _ = Θ₁ (ρ w) * (c : G) := by rw [hρ, hxc]
    rw [hconj]
    exact (Θ (ρ w, c)).2
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact key n hn τ hτ b
  · intro hb
    have hb' : b = n⁻¹ * (n * b * n⁻¹) * n := by group
    rw [hb']
    simpa using key n⁻¹ (X.inv_mem hn) τ⁻¹ hτinv (n * b * n⁻¹) hb

theorem conj_frame_eq_liftBs {G : Type} [Group G] {p m : ℕ} {Bs X : Subgroup G}
    (Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G)
    (Θ : ((Fin m → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c)
    {x : G} (hx : x ∈ X) {σ : MulAut (Fin m → Multiplicative (ZMod p))}
    (hσ : ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v)) (b : ↥Bs) :
    ((liftBs Θ σ b : ↥Bs) : G) = x * b * x⁻¹ := by
  obtain ⟨⟨w, c⟩, hwc⟩ := Θ.surjective b
  rw [← hwc, liftBs_apply, hΘ, hΘ]
  have hxc : x * (c : G) * x⁻¹ = c := by
    have h := Subgroup.mem_centralizer_iff.mp c.2.2 x hx
    rw [h]
    group
  calc Θ₁ (σ w) * (c : G) = (x * Θ₁ w * x⁻¹) * (x * (c : G) * x⁻¹) := by rw [hσ, hxc]
    _ = x * (Θ₁ w * (c : G)) * x⁻¹ := by group

theorem sectionFrameAut_le_signedAut {G : Type} [Group G] {p m : ℕ} {Bs X J : Subgroup G}
    (Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G)
    (Θ : ((Fin m → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c)
    (hle : ∀ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ σ ∈ spSignedGroup m p, ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v))
    (hJX : J ≤ X) :
    FrameBs.sectionFrameAut Θ₁ J ≤ signedAut m p := by
  have hΘ₁ : Function.Injective Θ₁ := by
    intro w w' hww'
    have h1 : ((Θ (w, 1) : ↥Bs) : G) = ((Θ (w', 1) : ↥Bs) : G) := by
      rw [hΘ w 1, hΘ w' 1, hww']
    have h2 : Θ (w, 1) = Θ (w', 1) := Subtype.ext h1
    exact congrArg Prod.fst (Θ.injective h2)
  rintro τ ⟨n, hn, hτ⟩
  have hnN := mem_normalizer_of_frame_action Θ₁ Θ hΘ (hJX hn) τ hτ
  obtain ⟨σ, hσ, hσn⟩ := hle n (hJX hn) hnN
  obtain ⟨σ', hσ', hσ'eq⟩ := exists_mem_signedAut_of_mem_spSignedGroup m p hσ
  have hτeq : τ = σ' := by
    refine MulEquiv.ext fun v => hΘ₁ ?_
    calc Θ₁ (τ v) = n * Θ₁ v * n⁻¹ := (hτ v).symm
      _ = Θ₁ (σ v) := hσn v
      _ = Θ₁ (σ' v) := by rw [show σ' v = σ v from congrArg (fun e => e v) hσ'eq]
  rw [hτeq]
  exact hσ'

theorem ggAutomizer_eq_map_sectionFrameAut {G : Type} [Group G] {p m : ℕ} {Bs X J : Subgroup G}
    (Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G)
    (Θ : ((Fin m → Multiplicative (ZMod p)) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G))) ≃* ↥Bs)
    (hΘ : ∀ w c, ((Θ (w, c) : ↥Bs) : G) = Θ₁ w * c)
    (hle : ∀ x ∈ X, x ∈ Subgroup.normalizer (Bs : Set G) →
      ∃ σ ∈ spSignedGroup m p, ∀ v, x * Θ₁ v * x⁻¹ = Θ₁ (σ v))
    (hJX : J ≤ X) :
    ggAutomizer J Bs = (FrameBs.sectionFrameAut Θ₁ J).map (liftBs Θ) := by
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨g, hg, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨σ, hσ, hσg⟩ := hle g (hJX hg) hgN
    obtain ⟨σ', hσ', hσ'eq⟩ := exists_mem_signedAut_of_mem_spSignedGroup m p hσ
    have hσ'g : ∀ v, g * Θ₁ v * g⁻¹ = Θ₁ (σ' v) := by
      intro v
      calc g * Θ₁ v * g⁻¹ = Θ₁ (σ v) := hσg v
        _ = Θ₁ (σ' v) := by rw [show σ' v = σ v from congrArg (fun e => e v) hσ'eq]
    refine Subgroup.mem_map.mpr ⟨σ', ⟨g, hg, hσ'g⟩, ?_⟩
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hφg b]
    exact conj_frame_eq_liftBs Θ₁ Θ hΘ (hJX hg) hσ'g b
  · rintro _ ⟨τ, ⟨n, hn, hτ⟩, rfl⟩
    refine mem_ggAutomizer_iff.mpr ⟨n, hn, ?_, ?_⟩
    · exact mem_normalizer_of_frame_action Θ₁ Θ hΘ (hJX hn) τ hτ
    · intro b
      exact conj_frame_eq_liftBs Θ₁ Θ hΘ (hJX hn) hτ b

theorem sectionFrameAut_eq_signedSupportedAut {G : Type} [Group G] {p m : ℕ} (hp : p.Prime)
    {Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G} (hΘ₁ : Function.Injective Θ₁)
    {J : Subgroup G} (S : Finset (Fin m))
    (hsigned : FrameBs.sectionFrameAut Θ₁ J ≤ signedAut m p)
    (hfix : ∀ x ∈ J, ∀ i ∉ S,
      x * Θ₁ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * x⁻¹ = Θ₁ (Pi.mulSingle i (ofAdd 1)))
    (hswap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      permAut (p := p) (Equiv.swap a b) ∈ FrameBs.sectionFrameAut Θ₁ J)
    (hsgn : ∀ i ∈ S, sgnAut (p := p) i ∈ FrameBs.sectionFrameAut Θ₁ J) :
    FrameBs.sectionFrameAut Θ₁ J = signedSupportedAut m p S := by
  refine le_antisymm ?_ (signedSupportedAut_le S hsgn hswap)
  rintro τ ⟨n, hn, hτ⟩
  refine mem_signedSupportedAut_of_fix hp (hsigned ⟨n, hn, hτ⟩) S fun i hi => hΘ₁ ?_
  rw [← hτ (Pi.mulSingle i (ofAdd 1)), hfix n hn i hi]

theorem sectionFrameAut_eq_twistedPermAut {G : Type} [Group G] {p m : ℕ} (hp : p.Prime)
    {Θ₁ : (Fin m → Multiplicative (ZMod p)) →* G} (hΘ₁ : Function.Injective Θ₁)
    {J : Subgroup G} (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    (hsgn : ∀ i, s i = 1 ∨ s i = -1)
    (hsigned : FrameBs.sectionFrameAut Θ₁ J ≤ signedAut m p)
    (hfix : ∀ x ∈ J, ∀ i ∉ S,
      x * Θ₁ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * x⁻¹ = Θ₁ (Pi.mulSingle i (ofAdd 1)))
    (hvec : ∀ x ∈ J, x * Θ₁ (fun j => if j ∈ S then ofAdd (s j) else 1) * x⁻¹ =
      Θ₁ (fun j => if j ∈ S then ofAdd (s j) else 1))
    (hgen : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ ∈
        FrameBs.sectionFrameAut Θ₁ J) :
    FrameBs.sectionFrameAut Θ₁ J = twistedPermAut m p S s hs := by
  refine le_antisymm ?_ (twistedPermAut_le S s hs hgen)
  rintro τ ⟨n, hn, hτ⟩
  refine mem_twistedPermAut_of_fix hp (hsigned ⟨n, hn, hτ⟩) S s hs hsgn ?_ ?_
  · intro i hi
    exact hΘ₁ (by rw [← hτ (Pi.mulSingle i (ofAdd 1)), hfix n hn i hi])
  · exact hΘ₁ (by rw [← hτ (fun j => if j ∈ S then ofAdd (s j) else 1), hvec n hn])

end TypeBDatum

end CFSG.StandardType

end
