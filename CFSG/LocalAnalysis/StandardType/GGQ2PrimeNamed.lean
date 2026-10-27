module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

structure WeylCoords {G : Type} [Group G] (Bs : Subgroup G) (A : Subgroup (MulAut Bs)) (x : G)
    (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m : Fin 7) : Prop where
  inj : ∀ b : Bs, (∀ j, κ j b = 1) → b = 1
  sum_one : ∀ b : Bs, ∏ j, κ j b = 1
  perm : ∀ φ ∈ A, ∃ σ : Equiv.Perm (Fin 7), ∀ j b, κ j (φ b) = κ (σ.symm j) b
  onto : ∀ σ : Equiv.Perm (Fin 7), ∃ φ ∈ A, ∀ j b, κ j (φ b) = κ (σ.symm j) b
  x_mem : x ∈ Bs
  x_coord : ∀ j, κ j ⟨x, x_mem⟩ = if j = m then 1 else ω3

structure CoordCtx {G : Type} [Group G] [Finite G]
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (A : Subgroup (MulAut Bs))
    (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m : Fin 7) : Prop where
  setting : Q2pSetting B Bs x L
  even : ¬ Odd (Nat.card (center L))
  eq : Bs = B
  A_le : A ≤ ggAutomizer ⊤ Bs
  AL_le : ggAutomizer L Bs ≤ A
  weyl6 : GGWeylOfType 3 (CoxeterMatrix.A 6) A
  weyl5 : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)
  coords : WeylCoords Bs A x κ m

@[expose] def IsCoordLift {G : Type} [Group G]
    (Bs : Subgroup G) (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (g : G)
    (σ : Equiv.Perm (Fin 7)) : Prop :=
  ∀ j (b : Bs) (hgb : g * b * g⁻¹ ∈ Bs), κ j ⟨_, hgb⟩ = κ (σ.symm j) b

@[expose] def WeylCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (y : G) (K : Subgroup G),
    GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 → Nat.card Bs = 3 ^ 6 → GGNbr 3 B x D J y K →
    GGWeylOfType 3 (CoxeterMatrix.A 6) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
    GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs) →
    ∃ (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m : Fin 7),
      WeylCoords Bs (ggAutomizer L Bs ⊔ ggAutomizer K Bs) x κ m

@[expose] def Lemma81Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L : Subgroup G)
    (A : Subgroup (MulAut Bs)) (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m : Fin 7),
    CoordCtx B Bs x L A κ m →
      Nat.card (O2Z L) = 4 ∧
        ∀ b (hb : b ∈ Bs), b ∈ centralizer (O2Z L : Set G) ↔ κ m ⟨b, hb⟩ = 1

@[expose] def Lemma101cInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L : Subgroup G)
    (A : Subgroup (MulAut Bs)) (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m n : Fin 7) (g : G),
    CoordCtx B Bs x L A κ m → n ≠ m → g ∈ normalizer (Bs : Set G) →
    IsCoordLift Bs κ g (Equiv.swap m n) →
      ∃ X : Subgroup G, LieModel X .PSU 5 2 1 ∧
        X ≤ L ⊓ centralizer ({g * x * g⁻¹} : Set G) ∧
        (∀ h ∈ L ⊓ centralizer ({g * x * g⁻¹} : Set G),
          ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ X, h = c * y) ∧
        X ≤ L.map (MulAut.conj g).toMonoidHom ∧
        Bs ⊓ centralizer (X : Set G) = closure {x, x * (g * x * g⁻¹)⁻¹}

@[expose] def Lemma1025Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L : Subgroup G)
    (A : Subgroup (MulAut Bs)) (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m n k : Fin 7)
    (g g' : G) (X : Subgroup G),
    CoordCtx B Bs x L A κ m → n ≠ m → k ≠ m → k ≠ n →
    g ∈ normalizer (Bs : Set G) → IsCoordLift Bs κ g (Equiv.swap m n) →
    g' ∈ normalizer (Bs : Set G) → IsCoordLift Bs κ g' (Equiv.swap m k) →
    LieModel X .PSU 5 2 1 → X ≤ L ⊓ centralizer ({g * x * g⁻¹} : Set G) →
    X ≤ L.map (MulAut.conj g).toMonoidHom →
    Bs ⊓ centralizer (X : Set G) = closure {x, x * (g * x * g⁻¹)⁻¹} →
      ∃ Xk : Subgroup G, LieModel Xk .PSU 4 2 1 ∧
        Xk ≤ X ⊓ centralizer ({g' * x * g'⁻¹} : Set G) ∧ Xk ≤ L.map (MulAut.conj g').toMonoidHom

@[expose] def F14Input : Prop :=
  ∀ (G : Type) [Group G] (X Xk : Subgroup G), LieModel X .PSU 5 2 1 → LieModel Xk .PSU 4 2 1 →
    Xk ≤ X → ∀ α : MulAut X, (∀ y : X, (y : G) ∈ Xk → α y = y) → α ^ 3 = 1

theorem coordLift_inv {G : Type} [Group G]
    {Bs : Subgroup G} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))} {g : G}
    {a b : Fin 7} (hg : g ∈ normalizer (Bs : Set G)) (h : IsCoordLift Bs κ g (Equiv.swap a b))
    (j : Fin 7) (c : Bs) (hc : g⁻¹ * c * g ∈ Bs) :
    κ j ⟨_, hc⟩ = κ (Equiv.swap a b j) c := by
  have hgb : g * (g⁻¹ * c * g) * g⁻¹ ∈ Bs := by
    have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
    rw [e]; exact c.2
  have := h (Equiv.swap a b j) ⟨_, hc⟩ hgb
  rw [Equiv.symm_swap, Equiv.swap_apply_self] at this
  rw [← this]
  congr 1
  exact Subtype.ext (by simp only; group)

theorem q2p_of_named {G : Type} [Group G] [Finite G]
    (hL : GGLBalanceInput) (hI : PumpUpLieInputs) (hW : WeylCoordInput)
    (h81 : Lemma81Input) (hc : Lemma101cInput) (hk : Lemma1025Input) (hF : F14Input)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hcard : Nat.card Bs = 3 ^ 6)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1)
    (hWA : GGSecFiveWeylAt 3 B Bs x L D J (CoxeterMatrix.A 6))
    (hAL : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs)) :
    Odd (Nat.card (center L)) := by
  have hS := q2pSetting_of_routeCfg hcfg hcard hm
  by_contra hev
  obtain ⟨hEq, -⟩ := cor_9_5 hS hev
  obtain ⟨y, K, hnbr, hWK⟩ := hWA
  obtain ⟨κ, m, hκ⟩ := hW G B Bs x L D J 𝒦 y K hcfg hcard hnbr hWK hAL
  set A := ggAutomizer L Bs ⊔ ggAutomizer K Bs with hA
  have hctx : CoordCtx B Bs x L A κ m :=
    ⟨hS, hev, hEq, sup_le (ggAutomizer_le_top L Bs) (ggAutomizer_le_top K Bs), le_sup_left,
      hWK, hAL, hκ⟩
  have hlift : ∀ n : Fin 7, ∃ g ∈ normalizer (Bs : Set G), IsCoordLift Bs κ g (Equiv.swap m n) := by
    intro n
    obtain ⟨φ, hφA, hφ⟩ := hκ.onto (Equiv.swap m n)
    obtain ⟨g, -, hgN, hgφ⟩ := mem_ggAutomizer_iff.1 (hctx.A_le hφA)
    refine ⟨g, hgN, fun j b hgb => ?_⟩
    have e : (⟨g * b * g⁻¹, hgb⟩ : Bs) = φ b := Subtype.ext (hgφ b).symm
    rw [e, hφ]
  set n : Fin 7 := m + 1 with hn
  set k : Fin 7 := m + 2 with hk'
  have hnm : n ≠ m := by fin_cases m <;> decide
  have hkm : k ≠ m := by fin_cases m <;> decide
  have hkn : k ≠ n := by fin_cases m <;> decide
  obtain ⟨gn, hgnN, hgn⟩ := hlift n
  obtain ⟨gk, hgkN, hgk⟩ := hlift k
  obtain ⟨X, hXm, hXle, hXs, hXL, hXB⟩ := hc G B Bs x L A κ m n gn hctx hnm hgnN hgn
  obtain ⟨Xk, hXkm, hXkle, hXkL⟩ :=
    hk G B Bs x L A κ m n k gn gk X hctx hnm hkm hkn hgnN hgn hgkN hgk hXm hXle hXL hXB
  obtain ⟨hT4, h81'⟩ := h81 G B Bs x L A κ m hctx
  subst hEq
  set g : Fin 3 → G := ![1, gn, gk] with hg
  set σ : Fin 3 → Equiv.Perm (Fin 7) := ![1, Equiv.swap m n, Equiv.swap m k] with hσ
  have hgN : ∀ i, g i ∈ normalizer (Bs : Set G) := by
    intro i; fin_cases i
    · exact one_mem _
    · exact hgnN
    · exact hgkN
  have hfwd : ∀ i j (b : Bs) (hgb : g i * b * (g i)⁻¹ ∈ Bs),
      κ j ⟨_, hgb⟩ = κ (σ i j) b := by
    intro i j b hgb
    fin_cases i
    · congr 1; exact Subtype.ext (by simp [hg])
    · simpa [hg, hσ, Equiv.symm_swap] using hgn j b hgb
    · simpa [hg, hσ, Equiv.symm_swap] using hgk j b hgb
  have hbwd : ∀ i j (c : Bs) (hc : (g i)⁻¹ * c * g i ∈ Bs),
      κ j ⟨_, hc⟩ = κ (σ i j) c := by
    intro i j c hc
    fin_cases i
    · congr 1; exact Subtype.ext (by simp [hg])
    · simpa [hg, hσ] using coordLift_inv hgnN hgn j c hc
    · simpa [hg, hσ] using coordLift_inv hgkN hgk j c hc
  have hcoord : ∀ i j (hb : (g j)⁻¹ * zT g x i * g j ∈ Bs),
      κ m ⟨_, hb⟩ = if i = j then 1 else ω3 := by
    intro i j hb
    have hzi : zT g x i ∈ Bs := (mem_normalizer_iff.1 (hgN i) x).1 hκ.x_mem
    rw [hbwd j m ⟨_, hzi⟩ hb]
    have hz : (⟨zT g x i, hzi⟩ : Bs) = ⟨g i * x * (g i)⁻¹, hzi⟩ := rfl
    rw [hz, hfwd i (σ j m) ⟨x, hκ.x_mem⟩ hzi, hκ.x_coord]
    have hmn : m ≠ n := Ne.symm hnm
    have hmk : m ≠ k := Ne.symm hkm
    have hnk : n ≠ k := Ne.symm hkn
    fin_cases i <;> fin_cases j <;>
      simp [hσ, Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne,
        hmn, hmk, hnk, hnm, hkm, hkn]
  have hrest : O1pRest Bs x L g (κ m) X Xk :=
    { T_card := hT4
      lemma81 := h81'
      g0 := rfl
      g_norm := hgN
      coord := hcoord
      X_model := hXm
      X_le := hXle
      X_split := hXs
      X_le_L1 := hXL
      B_cent_X := hXB
      Xk_model := hXkm
      Xk_le := hXkle
      Xk_le_L2 := hXkL
      F14 := hF G X Xk hXm hXkm (fun _ hy => (hXkle hy).1) }
  exact hev (q2p_of_rest hL hI hS (fun _ => ⟨g, κ m, X, Xk, hrest⟩))

end CFSG.GGQ2Prime
