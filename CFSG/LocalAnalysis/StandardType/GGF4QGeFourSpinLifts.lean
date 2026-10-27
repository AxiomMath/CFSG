module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeOmegaFourMinusPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourLocalMaps
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

public noncomputable section

namespace CFSG.StandardType.F4KGPosition

open CFSG.LieType.Universal CFSG.StandardType.ClassicalPosition CFSG.Assembly CFSG.Open

theorem exists_spinMinus_lift_kernel_rank
    (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {G : Type} [Group G] [Finite G]
    (ψ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) (Bs : Subgroup G) [IsMulCommutative ↥Bs]
    (hBs : ∀ b ∈ Bs, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ b)
    {p r : ℕ} (hpow : ∀ b ∈ Bs, b ^ p = 1)
    (hrank : p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card Bs) :
    ∃ ℓ : ↥Bs →* ↥(spinGroup (Spin.quadMinus n F bq cq)),
      (∀ (b : ↥Bs) (u : ↥(spinGroup (Spin.quadMinus n F bq cq))),
        (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
      ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (ψ.range : Set G) ∧
      (∀ b : ↥Bs, ℓ b ^ p = 1) ∧ p ^ r ≤ Nat.card ℓ.range := by
  obtain ⟨ℓ, hℓ⟩ := RCKRP.exists_liftHom_POmegaMinus n hirr hn ψ hψ Bs hBs
  have hker (b : ↥Bs) : ℓ b = 1 ↔ (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    constructor
    · intro hb
      rw [Subgroup.mem_centralizer_iff]
      rintro z ⟨u, rfl⟩
      have h := hℓ b u
      rw [hb, inv_one, one_mul, mul_one] at h
      have h' := congrArg (fun z : G => (b : G) * z) h
      simpa only [mul_assoc, mul_inv_cancel_left] using h'
    · intro hb
      apply conj_eq_unique_POmegaMinus n hirr hn ψ hψ (s' := 1)
      intro u
      rw [inv_one, one_mul, mul_one, ← hℓ b u]
      have hc := Subgroup.mem_centralizer_iff.mp hb (ψ u) ⟨u, rfl⟩
      calc (b : G)⁻¹ * ψ u * (b : G) = (b : G)⁻¹ * (ψ u * (b : G)) := by group
        _ = (b : G)⁻¹ * ((b : G) * ψ u) := by rw [hc]
        _ = ψ u := by group
  have hmap : ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (ψ.range : Set G) := by
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.property, (hker b).mp (MonoidHom.mem_ker.mp hb)⟩
    · rintro ⟨hgBs, hgC⟩
      exact ⟨⟨g, hgBs⟩, MonoidHom.mem_ker.mpr ((hker ⟨g, hgBs⟩).mpr hgC), rfl⟩
  have hcard : Nat.card ℓ.ker = Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective Bs.subtype_injective]
  have hmul := Subgroup.card_ker_mul_card_range ℓ
  rw [hcard] at hmul
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := Nat.card_pos
  refine ⟨ℓ, hℓ, hmap, ?_, ?_⟩
  · intro b
    rw [← map_pow]
    have hb : b ^ p = 1 := Subtype.ext (by simpa using hpow b b.property)
    rw [hb, map_one]
  · nlinarith

theorem exists_spinMinus_lifts_of_f4_member
    (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hmark : GGCentralImage .POmegaMinus 4 f X) :
    ∃ ψ : (ggU .POmegaMinus 4 f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K ∧ ψ.range = X ∧
      ∃ ℓ : ↥Bs →* (ggU .POmegaMinus 4 f).K,
        (∀ (b : ↥Bs) (u : (ggU .POmegaMinus 4 f).K),
          (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
        ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
        (∀ b : ↥Bs, ℓ b ^ p = 1) ∧ p ^ 3 ≤ Nat.card ℓ.range := by
  have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  let : IsMulCommutative ↥Bs := hBs.1
  obtain ⟨ψ, hadm, hker, hrange⟩ := hmark
  have hrk : 2 ≤ (ggU .POmegaMinus 4 f).D.rank :=
    two_le_lieUniversal_rank .POmegaMinus 4 2 f Nat.prime_two hadm (by decide)
  obtain ⟨_, hdiag, hcard⟩ := ggF4QGeFour_localMap_of_mp hMp hcfg hX ψ hadm hrk hker hrange
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 f
  let ψn : ↥(spinGroup (Spin.quadMinus 4 F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) →* G := ψ
  have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag
      (Spin.Twisted.minusDatum 4 (minusCoeffs_irr 2 f)) ψn b := hdiag
  have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤ Nat.card Bs := by
    rw [show ψn.range = X from hrange]
    exact hcard
  obtain ⟨ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ⟩ := exists_spinMinus_lift_kernel_rank
    4 (minusCoeffs_irr 2 f) (by decide) ψn hker Bs hdiag' hBs.2 hcard'
  refine ⟨ψ, hker, hrange, ℓ, hℓ, ?_, hpowℓ, hrankℓ⟩
  rw [show ψn.range = X from hrange] at hkerℓ
  exact hkerℓ

end CFSG.StandardType.F4KGPosition
