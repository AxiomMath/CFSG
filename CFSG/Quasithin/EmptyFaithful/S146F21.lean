module

public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.EmptyFaithful.S146F10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def g2_14615 (K₂ : Subgroup G) : Subgroup G := Subgroup.normalizer (K₂ : Set G)

@[expose] def g12_14615 (T K₂ : Subgroup G) : Subgroup G := mcOf T ⊓ g2_14615 K₂

structure Setup14615 (T M H H₁ H₂ K₁ K₂ : Subgroup G) (s : G) : Prop where
  kz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ K₂
  s_mem : s ∈ T
  s_not : s ∉ Subgroup.normalizer (K₁ : Set G)
  conj : K₂ = conjSub s K₁
  oTwo₁ : oTwoUpper H₁ ≤ K₁
  oTwo₂ : oTwoUpper H₂ ≤ K₂
  cent : ⁅uHi T M H H₁, K₂⁆ ≤ quasithinOmegaOneCenter T
  perf₂ : oTwoUpper K₂ = K₂
  shape : (K₁ ∈ cComp (mcOf T) ∧ K₂ ∈ cComp (mcOf T) ∧
      mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
      Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4))) ∨
    (K₁ = oTwoUpper H₁ ∧ K₂ = oTwoUpper H₂)

end Defs

section Steps

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₁ H₂ K₁ K₂ : Subgroup G} {s : G}

theorem Setup14615.le_mcOf (S : Setting146 G T M) {PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (h : Setup14615 T M H H₁ H₂ K₁ K₂ s) : K₂ ≤ mcOf T := by
  have hH : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hKz : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T :=
    conjClosure_le fun g hg v hv =>
      (mcOf T).mul_mem ((mcOf T).mul_mem hg (hH (oTwoUpper_le H hv))) ((mcOf T).inv_mem hg)
  rw [h.kz] at hKz
  exact le_sup_right.trans hKz

theorem charTwo_oTwoFIn_of_charTwo {H : Subgroup G} (h : CharTwo H) : CharTwo (oTwoFIn H) := by
  have hYH : oTwoFIn H ≤ H := C2Six.oTwoFIn_le
  have hHY : H ≤ Subgroup.normalizer (oTwoFIn H : Set G) := C2Six.le_normalizer_oTwoFIn
  have hQY : pCoreOf 2 H ≤ oTwoFIn H := C2Six.pCoreOf_le_oTwoFIn
  have h1 : pCoreOf 2 H ≤ pCoreOf 2 (oTwoFIn H) :=
    le_pCoreOf_of_le_normalizer 2 hQY (hYH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have h2 : pCoreOf 2 (oTwoFIn H) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (oTwoFIn H)).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 (oTwoFIn H))) (pCoreOf_isPGroup 2 (oTwoFIn H))
  have h3 : pCoreOf 2 (oTwoFIn H) = pCoreOf 2 H := le_antisymm h2 h1
  intro x hx
  rw [h3] at hx ⊢
  exact h ⟨hYH hx.1, hx.2⟩

theorem Setup14615.centralizes (S : Setting146 G T M) {PQ : Subgroup G} {p : ℕ}
    (hred : IsRedCE T M H PQ p) (h : Setup14615 T M H H₁ H₂ K₁ K₂ s) {A : Subgroup G}
    (hA : A ≤ uHi T M H H₁) : K₂ ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hK₂ : oTwoUpper K₂ ≤ Subgroup.centralizer ({a} : Set G) :=
    oTwoUpper_le_centralizer_of_comm_mem_Z (h.le_mcOf S hred) fun y hy =>
      h.cent (Subgroup.commutator_mem_commutator (hA ha) hy)
  have hx' : x ∈ oTwoUpper K₂ := by
    rw [h.perf₂]
    exact hx
  exact Subgroup.mem_centralizer_iff.mp (hK₂ hx') a (Set.mem_singleton a)

end Steps

end CFSG.Quasithin
