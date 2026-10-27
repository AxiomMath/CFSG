module

public import CFSG.Sporadic.Co2Smith.GlRefineFacts
public import CFSG.Sporadic.Co2Smith.GlDataInputs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Rank3 MulAction

@[expose] def glBasePt (s : ℕ) : Fin 2300 :=
  ⟨Native.glBase[s]! % 2300, Nat.mod_lt _ (by norm_num)⟩

theorem glBasePt_val {s : ℕ} (hs : s < 3) : (glBasePt s : ℕ) = Native.glBase[s]! := by
  interval_cases s <;> rfl

theorem ncard_setOf_mem {pts : List ℕ} (hnd : pts.Nodup) (hlt : ∀ x ∈ pts, x < 2300) :
    {y : Fin 2300 | (y : ℕ) ∈ pts}.ncard = pts.length := by
  have himg : Fin.val '' {y : Fin 2300 | (y : ℕ) ∈ pts} = (pts.toFinset : Set ℕ) := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hlt x hx⟩, hx, rfl⟩
  rw [← Set.ncard_image_of_injective _ Fin.val_injective, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

theorem stabChain_fix {G : Subgroup (Equiv.Perm (Fin 2300))} {s : ℕ} {τ : G}
    (hτ : τ ∈ stabChain (G := G) glBasePt s) :
    ∀ j < s, (τ : Equiv.Perm (Fin 2300)) (glBasePt j) = glBasePt j :=
  fun j hj => mem_stabChain.1 hτ j hj

theorem card_eq_of_stabChain {G : Subgroup (Equiv.Perm (Fin 2300))} {n₀ n₁ n₂ : ℕ}
    (h₀ : (orbit (stabChain (G := G) glBasePt 0) (glBasePt 0)).ncard = n₀)
    (h₁ : (orbit (stabChain (G := G) glBasePt 1) (glBasePt 1)).ncard = n₁)
    (h₂ : (orbit (stabChain (G := G) glBasePt 2) (glBasePt 2)).ncard = n₂)
    (h₃ : stabChain (G := G) glBasePt 3 = ⊥) :
    Nat.card G = n₀ * n₁ * n₂ := by
  have e0 := card_stabChain_succ (G := G) glBasePt 0
  have e1 := card_stabChain_succ (G := G) glBasePt 1
  have e2 := card_stabChain_succ (G := G) glBasePt 2
  rw [h₃, Subgroup.card_bot] at e2
  have htop : Nat.card (stabChain (G := G) glBasePt 0) = Nat.card G := by
    rw [stabChain, Subgroup.card_top]
  rw [← htop, e0, e1, e2, h₀, h₁, h₂]
  ring

structure GlGroup (G : Subgroup (Equiv.Perm (Fin 2300)))
    (arcs : List (Array ℕ)) : Prop where
  mem_co2P : ∀ σ ∈ G, σ ∈ co2P
  arc : ∀ σ ∈ G, ∀ p ∈ arcs, ArcComm σ p

variable
  {G : Subgroup (Equiv.Perm (Fin 2300))} {arcs : List (Array ℕ)}

variable {p₀ p₁ p₂ : List ℕ} {extra : List (ℕ × List ℕ)}

theorem GlGroup.facts_mem (hG : GlGroup G arcs) (hF : GlOrbitFacts arcs p₀ p₁ p₂ extra) {s : ℕ}
    (hs : s < 3) {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ G)
    (hfix : ∀ j < s, σ (glBasePt j) = glBasePt j) :
    ((σ (glBasePt s) : Fin 2300) : ℕ) ∈ [p₀, p₁, p₂][s]! := by
  have hm := hG.mem_co2P σ hσ
  have ha := hG.arc σ hσ
  interval_cases s
  · exact hF.orb0 σ hm ha
  · exact hF.orb1 σ hm ha (hfix 0 (by norm_num))
  · exact hF.orb2 σ hm ha (hfix 0 (by norm_num)) (hfix 1 (by norm_num))

theorem GlGroup.orbit_eq_facts (hG : GlGroup G arcs) (hF : GlOrbitFacts arcs p₀ p₁ p₂ extra)
    {s : ℕ} (hs : s < 3) {pts : List ℕ} (hpts : [p₀, p₁, p₂][s]! = pts)
    (hwit : ∀ x ∈ pts, ∃ hx : x < 2300, ∃ σ ∈ G, (∀ j < s, σ (glBasePt j) = glBasePt j) ∧
      σ (glBasePt s) = ⟨x, hx⟩) :
    orbit (stabChain (G := G) glBasePt s) (glBasePt s) = {y : Fin 2300 | (y : ℕ) ∈ pts} := by
  ext y
  constructor
  · rintro ⟨⟨τ, hτ⟩, rfl⟩
    have h := hG.facts_mem hF hs τ.2 (stabChain_fix hτ)
    rw [hpts] at h
    exact h
  · intro hy
    obtain ⟨hx, σ, hσG, hfix, hσ⟩ := hwit y hy
    refine ⟨⟨⟨σ, hσG⟩, mem_stabChain.2 fun j hj => hfix j hj⟩, ?_⟩
    change σ (glBasePt s) = y
    rw [hσ]

theorem GlGroup.stabChain_three_facts (hG : GlGroup G arcs)
    (hF : GlOrbitFacts arcs p₀ p₁ p₂ extra) : stabChain (G := G) glBasePt 3 = ⊥ := by
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  have hfix := stabChain_fix hτ
  exact Subtype.ext (hF.triv _ (hG.mem_co2P _ τ.2) (hG.arc _ τ.2) (hfix 0 (by norm_num))
    (hfix 1 (by norm_num)) (hfix 2 (by norm_num)))

end CFSG.Sporadic.Co2Smith
