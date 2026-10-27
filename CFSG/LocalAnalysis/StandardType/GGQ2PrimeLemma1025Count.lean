module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeLemma1025Coords

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.StandardType

theorem lem1025_count {G : Type} [Group G] [Finite G] {Bs L X T : Subgroup G}
    {A : Subgroup (MulAut Bs)} {x zn zk t : G}
    {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {m n k : Fin 7}
    (hW : WeylCoords Bs A x κ m) (hAL : ggAutomizer L Bs ≤ A)
    (hmn : m ≠ n) (hmk : m ≠ k) (hnk : n ≠ k) (hXL : X ≤ L) (hTBs : T ≤ Bs)
    (hdec : ∀ b ∈ Bs, ∃ s ∈ T, ∃ c ∈ Bs ⊓ centralizer (X : Set G), b = s * c)
    (hxC : x ∈ centralizer (X : Set G)) (hznC : zn ∈ centralizer (X : Set G))
    (hzn : zn ∈ Bs) (hcn : ∀ j, κ j ⟨zn, hzn⟩ = if j = n then 1 else ω3)
    (hzk : zk ∈ Bs) (hck : ∀ j, κ j ⟨zk, hzk⟩ = if j = k then 1 else ω3)
    (hzkt : ∀ y ∈ X, y * zk = zk * y → y * t = t * y)
    (h120 : 120 ≤ ((fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
      ((X ⊓ normalizer (T : Set G) : Subgroup G) : Set G)).ncard) :
    24 ≤ ((fun y : G => fun b : T => y * (b : G) * y⁻¹) ''
      ((X ⊓ normalizer (T : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)).ncard := by
  classical
  set F : G → (↥T → G) := fun y b => y * (b : G) * y⁻¹ with hF
  set N : Subgroup G := X ⊓ normalizer (T : Set G) with hN
  have hconj : ∀ y ∈ X, ∀ c ∈ centralizer (X : Set G), y * c * y⁻¹ = c := fun y hy c hc => by
    rw [mul_inv_eq_iff_eq_mul]; exact mem_centralizer_iff.1 hc y hy
  have hconjsc : ∀ y ∈ X, ∀ (s c : G), c ∈ centralizer (X : Set G) →
      y * (s * c) * y⁻¹ = (y * s * y⁻¹) * c := fun y hy s c hc => by
    calc y * (s * c) * y⁻¹ = (y * s * y⁻¹) * (y * c * y⁻¹) := by group
      _ = (y * s * y⁻¹) * c := by rw [hconj y hy c hc]
  have hnormBs : ∀ y ∈ N, ∀ b ∈ Bs, y * b * y⁻¹ ∈ Bs := by
    intro y hy b hb
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec b hb
    rw [hconjsc y hy.1 s c hc.2]
    exact Bs.mul_mem (hTBs ((mem_normalizer_iff.1 hy.2 s).1 hs)) hc.1
  have hnormB : ∀ y ∈ N, y ∈ normalizer (Bs : Set G) := fun y hy =>
    mem_normalizer_iff.2 fun b => ⟨hnormBs y hy b, fun h => by
      have := hnormBs y⁻¹ (N.inv_mem hy) _ h
      have e : y⁻¹ * (y * b * y⁻¹) * y⁻¹⁻¹ = b := by group
      rwa [e] at this⟩
  have hlift : ∀ y ∈ N, ∃ σ, IsCoordLift Bs κ y σ := by
    intro y hy
    have hyN := hnormB y hy
    obtain ⟨σ, hσ⟩ := hW.perm (ggConjAut Bs hyN)
      (hAL (ggConjAut_mem_ggAutomizer (hXL hy.1) hyN))
    exact ⟨σ, fun j b _ => hσ j b⟩
  have hA : ∀ y ∈ N, ∀ y' ∈ N, ∀ σ, IsCoordLift Bs κ y σ → IsCoordLift Bs κ y' σ →
      F y = F y' := by
    intro y hy y' hy' σ hl hl'
    funext s
    have h1 : y * s * y⁻¹ ∈ Bs := hnormBs y hy s (hTBs s.2)
    have h2 : y' * s * y'⁻¹ ∈ Bs := hnormBs y' hy' s (hTBs s.2)
    have := weylCoords_ext hW (b := ⟨y * s * y⁻¹, h1⟩) (b' := ⟨y' * s * y'⁻¹, h2⟩) fun j =>
      (hl j ⟨s, hTBs s.2⟩ h1).trans (hl' j ⟨s, hTBs s.2⟩ h2).symm
    exact congrArg Subtype.val this
  have hB : ∀ y ∈ N, ∀ y' ∈ N, F y = F y' → ∀ σ σ', IsCoordLift Bs κ y σ →
      IsCoordLift Bs κ y' σ' → σ = σ' := by
    intro y hy y' hy' hFy σ σ' hl hl'
    refine lem1025_perm_unique hW fun b j => ?_
    have h1 : y * b * y⁻¹ ∈ Bs := hnormBs y hy b b.2
    have h2 : y' * b * y'⁻¹ ∈ Bs := hnormBs y' hy' b b.2
    obtain ⟨s, hs, c, hc, hbsc⟩ := hdec b b.2
    have hss : y * s * y⁻¹ = y' * s * y'⁻¹ := congrFun hFy ⟨s, hs⟩
    have hyy : (⟨y * b * y⁻¹, h1⟩ : Bs) = ⟨y' * b * y'⁻¹, h2⟩ := Subtype.ext (by
      show y * (b : G) * y⁻¹ = y' * (b : G) * y'⁻¹
      rw [hbsc, hconjsc y hy.1 s c hc.2, hconjsc y' hy'.1 s c hc.2, hss])
    calc κ (σ.symm j) b = κ j ⟨y * b * y⁻¹, h1⟩ := (hl j b h1).symm
      _ = κ j ⟨y' * b * y'⁻¹, h2⟩ := by rw [hyy]
      _ = κ (σ'.symm j) b := hl' j b h2
  let Ξ : (↥T → G) → Equiv.Perm (Fin 7) := fun f =>
    Classical.epsilon fun σ => ∃ y ∈ N, F y = f ∧ IsCoordLift Bs κ y σ
  have hΞ : ∀ y ∈ N, IsCoordLift Bs κ y (Ξ (F y)) := by
    intro y hy
    obtain ⟨σ, hσ⟩ := hlift y hy
    obtain ⟨y', hy', hFy, hl'⟩ := Classical.epsilon_spec
      (p := fun σ => ∃ y' ∈ N, F y' = F y ∧ IsCoordLift Bs κ y' σ) ⟨σ, y, hy, rfl, hσ⟩
    have hσe := hB y hy y' hy' hFy.symm σ _ hσ hl'
    show IsCoordLift Bs κ y (Classical.epsilon fun σ => ∃ y' ∈ N, F y' = F y ∧
      IsCoordLift Bs κ y' σ)
    rw [← hσe]
    exact hσ
  have hP : ∀ y ∈ N, Ξ (F y) m = m ∧ Ξ (F y) n = n := fun y hy =>
    ⟨lem1025_lift_fix (hΞ y hy) hW.x_mem (hconj y hy.1 x hxC) hW.x_coord,
      lem1025_lift_fix (hΞ y hy) hzn (hconj y hy.1 zn hznC) hcn⟩
  have hinj : Set.InjOn Ξ (F '' (N : Set G)) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    exact hA y hy y' hy' (Ξ (F y)) (hΞ y hy) (by rw [h]; exact hΞ y' hy')
  set P : Set (Equiv.Perm (Fin 7)) := {σ | σ m = m ∧ σ n = n} with hPdef
  set P' : Set (Equiv.Perm (Fin 7)) := {σ | σ m = m ∧ σ n = n ∧ σ k = k} with hP'def
  have hPcard : P.ncard = 120 := by
    have : P = {σ | ∀ a ∈ ({m, n} : Finset (Fin 7)), σ a = a} := by ext σ; simp [hPdef]
    rw [this, lem1025_ncard_perm_fixing, Finset.card_pair hmn]
    rfl
  have hP'card : P'.ncard = 24 := by
    have : P' = {σ | ∀ a ∈ ({m, n, k} : Finset (Fin 7)), σ a = a} := by ext σ; simp [hP'def]
    rw [this, lem1025_ncard_perm_fixing, Finset.card_eq_three.2 ⟨m, n, k, hmn, hmk, hnk, rfl⟩]
    rfl
  have hEP : Ξ '' (F '' (N : Set G)) ⊆ P := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hP y hy
  have hΞE : Ξ '' (F '' (N : Set G)) = P :=
    Set.eq_of_subset_of_ncard_le hEP (by rw [hinj.ncard_image, hPcard]; exact h120)
  have hreal : ∀ σ ∈ P', ∃ y ∈ N ⊓ centralizer ({t} : Set G), Ξ (F y) = σ := by
    intro σ hσ
    have hσP : σ ∈ Ξ '' (F '' (N : Set G)) := by rw [hΞE]; exact ⟨hσ.1, hσ.2.1⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hσP
    refine ⟨y, ⟨hy, mem_centralizer_singleton_iff.2 (hzkt y hy.1 ?_)⟩, rfl⟩
    have := lem1025_lift_cent hW (hΞ y hy) (hnormB y hy) hzk hck hσ.2.2
    rwa [mul_inv_eq_iff_eq_mul] at this
  have hsub : P' ⊆ Ξ '' (F '' ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)) :=
    fun σ hσ => by
      obtain ⟨y, hy, hyσ⟩ := hreal σ hσ
      exact ⟨F y, ⟨y, hy, rfl⟩, hyσ⟩
  have hinj' : Set.InjOn Ξ (F '' ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)) :=
    hinj.mono (Set.image_mono fun y hy => hy.1)
  calc 24 = P'.ncard := hP'card.symm
    _ ≤ (Ξ '' (F '' ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G))).ncard :=
        Set.ncard_le_ncard hsub
    _ = (F '' ((N ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G)).ncard := hinj'.ncard_image

end CFSG.GGQ2Prime
