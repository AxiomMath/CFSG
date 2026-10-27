module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev DV (n : ℕ) : Type := Fin (n + 1) → ZMod 3

abbrev DGL (n : ℕ) : Type := DV n ≃ₗ[ZMod 3] DV n

noncomputable abbrev dStd (n : ℕ) : Module.Basis (Fin (n + 1)) (ZMod 3) (DV n) :=
  Pi.basisFun (ZMod 3) (Fin (n + 1))

@[expose] def dE (n : ℕ) (i : Fin (n + 1)) : DV n := Pi.single i 1

@[expose] def dB {n : ℕ} (ρ : ZMod 3) (u v : DV n) : ZMod 3 :=
  ρ * u 0 * v 0 + ∑ i : Fin n, u i.succ * v i.succ

@[expose] def dRef {n : ℕ} (ρ : ZMod 3) (h g : DV n) : DV n :=
  g - (2 * dB ρ h h * dB ρ h g) • h

@[expose] def DRefl {n : ℕ} (ρ : ZMod 3) (r : DGL n) (h : DV n) : Prop :=
  dB ρ h h ≠ 0 ∧ ∀ v, r v = dRef ρ h v

@[expose] def dRoots {n : ℕ} (ρ : ZMod 3) (H : Subgroup (DGL n)) : Set (DV n) :=
  {h | ∃ r ∈ H, DRefl ρ r h}

@[expose] noncomputable def dGroup {n : ℕ} (ρ : ZMod 3) (Φ : Set (DV n)) : Subgroup (DGL n) :=
  Subgroup.closure {r | ∃ h ∈ Φ, DRefl ρ r h}

@[expose] def DSPData {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3) : Prop :=
  σ 0 = 0 ∧ c 0 = 1 ∧ (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1

@[expose] def dAct {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3) (h : DV n) : DV n :=
  fun j => c (σ.symm j) * h (σ.symm j)

@[expose] noncomputable def dActL {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3)
    (hc : ∀ i, c i = 1 ∨ c i = -1) : DGL n where
  toFun := dAct σ c
  invFun w := fun i => c i * w (σ i)
  map_add' x y := by ext j; simp [dAct, mul_add]
  map_smul' a x := by ext j; simp only [dAct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv x := by
    ext i
    simp only [dAct, Equiv.symm_apply_apply]
    rcases hc i with h | h <;> rw [h] <;> ring
  right_inv w := by
    ext j
    simp only [dAct, Equiv.apply_symm_apply]
    rcases hc (σ.symm j) with h | h <;> rw [h] <;> ring

@[simp] theorem dActL_apply {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → ZMod 3)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (v : DV n) : dActL σ c hc v = dAct σ c v := rfl

@[expose] def dSupp {n : ℕ} (h : DV n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => h i.succ ≠ 0).card

@[expose] def dSgn {n : ℕ} (h : DV n) : ZMod 3 :=
  ∏ i : Fin n, (h 0 * h i.succ)

@[expose] def dIsD {n : ℕ} (h : DV n) : Prop :=
  ∃ i j : Fin (n + 1), i ≠ j ∧ h i ≠ 0 ∧ h j ≠ 0 ∧ ∀ k, k ≠ i → k ≠ j → h k = 0

@[expose] def dIsO {n : ℕ} (h : DV n) : Prop :=
  ∃ i : Fin (n + 1), h i ≠ 0 ∧ ∀ k, k ≠ i → h k = 0

@[expose] def dIsS {n : ℕ} (ε : ZMod 3) (h : DV n) : Prop :=
  h 0 ≠ 0 ∧ (∀ i : Fin n, h i.succ ≠ 0) ∧ dSgn h = ε

instance {n : ℕ} (h : DV n) : Decidable (dIsD h) := by unfold dIsD; infer_instance

instance {n : ℕ} (h : DV n) : Decidable (dIsO h) := by unfold dIsO; infer_instance

instance {n : ℕ} (ε : ZMod 3) (h : DV n) : Decidable (dIsS ε h) := by unfold dIsS; infer_instance

@[expose] def dPhiD (n : ℕ) : Set (DV n) := {h | dIsD h}

@[expose] def dPhiB (n : ℕ) : Set (DV n) := {h | dIsD h ∨ dIsO h}

@[expose] def dPhiE7 (ε : ZMod 3) : Set (DV 6) :=
  {h | (h 0 = 0 ∧ dIsD h) ∨ (h 0 ≠ 0 ∧ dIsO h) ∨ dIsS ε h}

@[expose] def dPhiE8 (ε : ZMod 3) : Set (DV 7) :=
  {h | dIsD h ∨ dIsS ε h}

@[expose] def DRCl {n : ℕ} (ρ : ZMod 3) (Φ : Set (DV n)) : Prop :=
  (∀ h ∈ Φ, dB ρ h h ≠ 0) ∧
  (∀ h ∈ Φ, -h ∈ Φ) ∧
  (∀ h ∈ Φ, ∀ g ∈ Φ, dRef ρ h g ∈ Φ) ∧
  (∀ h ∈ Φ, ∀ σ c, DSPData σ c → dAct σ c h ∈ Φ) ∧
  (∀ h : DV n, h 0 = 0 → dIsD h → h ∈ Φ) ∧
  (∀ h ∈ Φ, h 0 = 0 → dIsD h ∨ dIsO h) ∧
  (∃ h ∈ Φ, h 0 ≠ 0 ∧ dSupp h ≠ 0)

@[expose] def DReflFixLeaf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
    DLinData p n V b H A → ∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ LinearMap.ker (b.coord 0) →
    r (b 0) = b 0

@[expose] def DSmNormLeaf : Prop :=
  DNormalizerLeaf → DReflFixLeaf → ∀ (n : ℕ) (H A : Subgroup (DGL n)),
    DLinData 3 n (DV n) (dStd n) H A → ∀ r ∈ H, GGLinRefl r →
      (∃ h : DV n, h 0 = 0 ∧ (dIsD h ∨ dIsO h) ∧ ∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r h) ∨
      (∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r (dE n 0)) ∨
      ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h : DV n, h 0 = 1 ∧ dSupp h ≠ 0 ∧ DRefl ρ r h

@[expose] def DSmCommonLeaf : Prop :=
  ∀ (n : ℕ) (H A : Subgroup (DGL n)), DLinData 3 n (DV n) (dStd n) H A →
    ∀ (ρ ρ' : ZMod 3) (r r' : DGL n) (h h' : DV n), r ∈ H → r' ∈ H → ρ ≠ 0 → ρ' ≠ 0 →
      h 0 ≠ 0 → h' 0 ≠ 0 → dSupp h ≠ 0 → dSupp h' ≠ 0 → DRefl ρ r h → DRefl ρ' r' h' → ρ = ρ'

@[expose] def DSmExistLeaf : Prop :=
  DSmNormLeaf → DNormalizerLeaf → DReflFixLeaf → ∀ (n : ℕ) (H A : Subgroup (DGL n)),
    DLinData 3 n (DV n) (dStd n) H A →
    (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0)) →
    ∃ r ∈ H, ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h : DV n, h 0 = 1 ∧ dSupp h ≠ 0 ∧ DRefl ρ r h

@[expose] def DSmTransLeaf : Prop :=
  (∀ (n : ℕ) (h g : DV n), h 0 ≠ 0 → g 0 ≠ 0 → dSupp h = dSupp g → (dSupp h = n → dSgn h = dSgn g) →
    ∃ σ c, DSPData σ c ∧ (dAct σ c h = g ∨ dAct σ c h = -g)) ∧
  (∀ (n : ℕ) (h g : DV n), h 0 = 0 → g 0 = 0 → dSupp h = 1 → dSupp g = 1 →
    ∃ σ c, DSPData σ c ∧ (dAct σ c h = g ∨ dAct σ c h = -g))

@[expose] def DSmClassLeaf : Prop :=
  DSmTransLeaf →
    (∀ Φ : Set (DV 6), DRCl 1 Φ → Φ = dPhiD 6 ∨ Φ = dPhiB 6) ∧
    (∀ Φ : Set (DV 6), DRCl 2 Φ → Φ = dPhiE7 1 ∨ Φ = dPhiE7 (-1)) ∧
    (∀ Φ : Set (DV 7), DRCl 1 Φ → Φ = dPhiD 7 ∨ Φ = dPhiB 7 ∨ Φ = dPhiE8 1 ∨ Φ = dPhiE8 (-1)) ∧
    (∀ Φ : Set (DV 7), ¬ DRCl 2 Φ)

@[expose] def DSmGenLeaf : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : Subgroup (DGL n),
    (∀ i j : Fin n, j.val = i.val + 1 → ∃ r ∈ G, DRefl 1 r (dE n i.succ - dE n j.succ)) →
    (∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n → ∃ r ∈ G, DRefl 1 r (dE n i.succ + dE n j.succ)) →
    ∀ a, DSP 3 (dStd n) a → a ∈ G

@[expose] def DSmModelsBDLeaf : Prop :=
  ZS.LinWeyl 3 (dGroup 1 (dPhiD 6)) ∧ ZS.LinWeyl 3 (dGroup 1 (dPhiB 6)) ∧
    ZS.LinWeyl 3 (dGroup 1 (dPhiD 7)) ∧ ZS.LinWeyl 3 (dGroup 1 (dPhiB 7))

@[expose] def DSmModelsE7Leaf : Prop :=
  DSmGenLeaf → DSmTransLeaf →
    ZS.LinWeyl 3 (dGroup 2 (dPhiE7 1)) ∧ ZS.LinWeyl 3 (dGroup 2 (dPhiE7 (-1)))

@[expose] def DSmModelsE8Leaf : Prop :=
  DSmGenLeaf → DSmTransLeaf →
    ZS.LinWeyl 3 (dGroup 1 (dPhiE8 1)) ∧ ZS.LinWeyl 3 (dGroup 1 (dPhiE8 (-1)))

end CFSG.StandardType.HdRo7D.Small
