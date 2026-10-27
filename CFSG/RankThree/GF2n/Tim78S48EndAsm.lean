module

public import CFSG.RankThree.GF2n.Tim78S48EndSplit
public import CFSG.RankThree.GF2n.Tim78S48EndAlg
public import CFSG.RankThree.GF2n.Tim78S42

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

namespace EndgameData

variable [Finite G] {M B Q P T : Subgroup G} {g : G}
  {C L : Subgroup G} (E : EndgameData M B Q P T g C L) (H : Hyp4 M B Q P T)
include E H

theorem false_of_frame {b' : G} (hb' : b' ∈ conjSubgroup g B) (hb'1 : b' ≠ 1)
    {L₀ N₀ L₁ X : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (S : CSplit B C L₀)
    (hXB : ∀ x ∈ X, ∀ β ∈ B, x * β = β * x) (hXb' : ∀ x ∈ X, x * b' = b' * x)
    (hXL₀ : X ≤ Subgroup.normalizer (L₀ : Set G))
    (hN₀ : N₀ ≤ L₀) (hL₁ : L₁ ≤ L₀) (hsplit : L₀ ≤ N₀ ⊔ L₁)
    (hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set G))
    (hXL₁ : ∀ x ∈ X, ∀ l ∈ L₁, x * l = l * x)
    (hnat : InducesNaturalSL2 n X N₀) : False := by
  classical
  obtain ⟨Θ, kp, hΘ, hkp⟩ := E.exists_dec H hb' S
  have hsurj := E.Theta_surjective H hb' hb'1 S hΘ
  obtain ⟨φ, ψ, hφs, -, hφψ⟩ := hnat
  let σ : ↥L₀ → ↥P := Function.surjInv hsurj
  have hσ : ∀ a, Θ (σ a) = a := Function.surjInv_eq hsurj
  have hLL : ∀ l ∈ L₀, l ∈ L := fun l hl => E.C_le_L (S.le_C hl)
  letI : MulDistribMulAction ↥X ↥L₀ := Subgroup.conjMulDistribMulActionOfLeNormalizer X L₀ hXL₀
  have hXM : X ≤ M := by rw [← H.normalizer_B]; exact le_normalizer_of_comm hXB
  let cj : ↥X → ↥P → ↥P := fun x y => ⟨x * y * (x : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P (hXM x.2)) y).mp y.2⟩
  have hΘcj : ∀ (x : ↥X) (y : ↥P), Θ (cj x y) = x • Θ y ∧ kp (cj x y) = kp y := by
    intro x y
    have := E.Theta_conj H hb' S hΘ (hXb' x x.2) (hXB x x.2) (hXL₀ x.2) (y := y) (y₁ := cj x y) rfl
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  have hD : ∀ y y' : ↥P, ⁅(y : G), ⁅b', (y' : G)⁆⁆ ∈ B := fun y y' =>
    E.D_mem H hb' (H.P_le_Q y.2) (H.P_le_Q y'.2)
  let Dm : ↥L₀ → ↥L₀ → ↥B := fun a b => ⟨⁅(σ a : G), ⁅b', (σ b : G)⁆⁆, hD _ _⟩
  have hDm : ∀ y y' : ↥P, Dm (Θ y) (Θ y') = ⟨⁅(y : G), ⁅b', (y' : G)⁆⁆, hD _ _⟩ := fun y y' =>
    Subtype.ext (E.D_eq_of_Theta H hb' hb'1 S hΘ (hσ (Θ y)).symm (hσ (Θ y')).symm)
  let κ : ↥L₀ → ↥B := fun a => kp (σ a)
  have hκm : ∀ y : ↥P, κ (Θ y) = kp y := fun y =>
    E.kp_eq_of_Theta H hb' hb'1 S hΘ (hσ (Θ y))
  have hD₁ : ∀ a a' b, Dm (a * a') b = Dm a b * Dm a' b := by
    intro a a' b
    obtain ⟨y, rfl⟩ := hsurj a
    obtain ⟨y₂, rfl⟩ := hsurj a'
    obtain ⟨y', rfl⟩ := hsurj b
    rw [← map_mul, hDm, hDm, hDm]
    exact Subtype.ext (E.D_mul_left H hb' (H.P_le_Q y.2) (H.P_le_Q y₂.2) (H.P_le_Q y'.2))
  have hD₂ : ∀ a b b', Dm a (b * b') = Dm a b * Dm a b' := by
    intro a b b'
    obtain ⟨y, rfl⟩ := hsurj a
    obtain ⟨y', rfl⟩ := hsurj b
    obtain ⟨y₂', rfl⟩ := hsurj b'
    rw [← map_mul, hDm, hDm, hDm]
    exact Subtype.ext (E.D_mul_right H hb' (H.P_le_Q y.2) (H.P_le_Q y'.2) (H.P_le_Q y₂'.2))
  have hDalt : ∀ a, Dm a a = 1 := by
    intro a
    obtain ⟨y, rfl⟩ := hsurj a
    rw [hDm]
    exact Subtype.ext (E.D_self H hb' (H.P_le_Q y.2))
  have hDinv : ∀ (x : ↥X) a b, Dm (x • a) (x • b) = Dm a b := by
    intro x a b
    obtain ⟨y, rfl⟩ := hsurj a
    obtain ⟨y', rfl⟩ := hsurj b
    rw [← (hΘcj x y).1, ← (hΘcj x y').1, hDm, hDm]
    refine Subtype.ext ?_
    show ⁅(x : G) * y * (x : G)⁻¹, ⁅b', (x : G) * y' * (x : G)⁻¹⁆⁆ = ⁅(y : G), ⁅b', (y' : G)⁆⁆
    rw [u_conj (hXb' x x.2) y']
    have e : ⁅(x : G) * y * (x : G)⁻¹, (x : G) * ⁅b', (y' : G)⁆ * (x : G)⁻¹⁆ =
        (x : G) * ⁅(y : G), ⁅b', (y' : G)⁆⁆ * (x : G)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hXB x x.2 _ (hD y y')]
    group
  have hDnd : ∀ b : ↥L₀, b ≠ 1 → ∃ a, Dm a b ≠ 1 := by
    intro b hb
    obtain ⟨y', rfl⟩ := hsurj b
    have hy'C : (y' : G) ∉ C := fun h => hb ((E.Theta_eq_one_iff H hb' hb'1 S hΘ y').mpr h)
    have hu : ⁅b', (y' : G)⁆ ∉ B := fun h => hy'C (E.mem_C_of_comm_mem_B H hb' hb'1 y'.2 h)
    have huP : ⁅b', (y' : G)⁆ ∈ P := E.C_le_P (E.u_mem hb' (H.P_le_Q y'.2))
    have : ∃ y ∈ P, ⁅y, ⁅b', (y' : G)⁆⁆ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hu
      rw [← H.inf_centralizer_P]
      refine ⟨huP, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact commutatorElement_eq_one_iff_mul_comm.mp (hcon y hy)
    obtain ⟨y, hy, hne⟩ := this
    refine ⟨Θ ⟨y, hy⟩, ?_⟩
    rw [hDm]
    intro h
    exact hne (congrArg Subtype.val h)
  have hκ : ∀ a b, κ (a * b) = κ a * κ b * Dm a b := by
    intro a b
    obtain ⟨y, rfl⟩ := hsurj a
    obtain ⟨y', rfl⟩ := hsurj b
    rw [← map_mul, hκm, hκm, hκm, hDm]
    exact Subtype.ext (hkp y y')
  have hκinv : ∀ (x : ↥X) a, κ (x • a) = κ a := by
    intro x a
    obtain ⟨y, rfl⟩ := hsurj a
    rw [← (hΘcj x y).1, hκm, hκm]
    exact (hΘcj x y).2
  let ν : Multiplicative (Fin 2 → GaloisField 2 n) →* ↥L₀ :=
    (Subgroup.inclusion hN₀).comp ψ.symm.toMonoidHom
  have hν : Function.Injective ν := fun v w h =>
    ψ.symm.injective (Subgroup.inclusion_injective hN₀ h)
  have hνx : ∀ (x : ↥X) (v : Fin 2 → GaloisField 2 n),
      ν (Multiplicative.ofAdd ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v)) =
        x • ν (Multiplicative.ofAdd v) := by
    intro x v
    set w : ↥N₀ := ψ.symm (Multiplicative.ofAdd v) with hw
    have hmem : (x : G) * (w : G) * (x : G)⁻¹ ∈ N₀ :=
      (Subgroup.mem_normalizer_iff.mp (hXN₀ x.2) w).mp w.2
    have h1 := hφψ x w ⟨_, hmem⟩ rfl
    have hψw : ψ w = Multiplicative.ofAdd v := by simp [hw]
    rw [hψw, toAdd_ofAdd] at h1
    have h2 : ψ ⟨_, hmem⟩ = Multiplicative.ofAdd
        ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v) := by
      rw [← h1]; rfl
    have h3 : ψ.symm (Multiplicative.ofAdd
        ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v)) = ⟨_, hmem⟩ := by
      rw [← h2]; simp
    show Subgroup.inclusion hN₀ (ψ.symm (Multiplicative.ofAdd
        ((φ x : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) *ᵥ v))) =
      x • Subgroup.inclusion hN₀ w
    rw [h3]
    rfl
  have hsplit' : ∀ l : ↥L₀, ∃ (v : Fin 2 → GaloisField 2 n) (l₁ : ↥L₀),
      (∀ x : ↥X, x • l₁ = l₁) ∧ l = ν (Multiplicative.ofAdd v) * l₁ := by
    intro l
    have hnorm : L₁ ≤ Subgroup.normalizer (N₀ : Set G) := le_normalizer_of_comm fun x hx y hy =>
      E.comm_L (hLL _ (hL₁ hx)) (hLL _ (hN₀ hy))
    obtain ⟨m, hm, l₁, hl₁, hml⟩ := exists_mul_of_mem_sup hnorm (hsplit l.2)
    refine ⟨Multiplicative.toAdd (ψ ⟨m, hm⟩), ⟨l₁, hL₁ hl₁⟩, fun x => Subtype.ext ?_,
      Subtype.ext ?_⟩
    · show (x : G) * l₁ * (x : G)⁻¹ = l₁
      rw [hXL₁ x x.2 l₁ hl₁]; group
    · show (l : G) = ((Subgroup.inclusion hN₀ (ψ.symm (Multiplicative.ofAdd
        (Multiplicative.toAdd (ψ ⟨m, hm⟩)))) : ↥L₀) : G) * l₁
      simpa using hml
  exact no_invariant_form_mul n hn (fun a b => Subtype.ext (H.B_comm a.2 b.2))
    (fun a => Subtype.ext (by simpa [pow_two] using H.sq_eq_one _ a.2)) φ hφs
    (fun a b => Subtype.ext (E.comm_L (hLL _ a.2) (hLL _ b.2))) ν hν hνx hsplit' Dm hD₁ hD₂
    hDalt hDinv hDnd κ hκ hκinv

end EndgameData

end CFSG.RankThree.GF2n.Tim78
