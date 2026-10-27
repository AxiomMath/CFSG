module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofChainFin

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aut

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G}

theorem ggFar_aut_commute (hp2 : p ≠ 2) [Fact p.Prime] (hBs : IsElemAbelian p Bs)
    {A : Subgroup (MulAut ↥Bs)} {n : ℕ} (hn : 3 ≤ n)
    (hW : GGWeylOfType p (CoxeterMatrix.A (n + 1)) A)
    (Φ₁ Φ₂ : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs) (hΦ₁ : ∀ π, Φ₁ π ∈ A)
    (hΦ₂ : ∀ π, Φ₂ π ∈ A) (hinj₁ : Function.Injective Φ₁) (hinj₂ : Function.Injective Φ₂)
    (hr₁ : ∀ a b, a ≠ b → GGIsReflection p (Φ₁ (Equiv.swap a b)))
    (hr₂ : ∀ a b, a ≠ b → GGIsReflection p (Φ₂ (Equiv.swap a b)))
    (hJ : ∀ i j : Fin n,
      Φ₁ (Equiv.swap i.succ j.succ) = Φ₂ (Equiv.swap i.castSucc j.castSucc))
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hout : ∀ σ, Φ₁ σ ≠ Φ₂ (Equiv.swap j.castSucc j.succ)) :
    Φ₁ (Equiv.swap i.castSucc i.succ) * Φ₂ (Equiv.swap j.castSucc j.succ) =
      Φ₂ (Equiv.swap j.castSucc j.succ) * Φ₁ (Equiv.swap i.castSucc i.succ) := by
  obtain ⟨Ê, hÊ⟩ := exists_permEquiv_of_ggWeylOfType_A hW
  let E : Equiv.Perm (Fin (n + 1 + 1)) →* MulAut ↥Bs := A.subtype.comp Ê.toMonoidHom
  have hEinj : Function.Injective E := by
    intro a b hab
    exact Ê.injective (Subtype.ext hab)
  let ρ₁ : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n + 1 + 1)) :=
    Ê.symm.toMonoidHom.comp (MonoidHom.codRestrict Φ₁ A hΦ₁)
  let ρ₂ : Equiv.Perm (Fin (n + 1)) →* Equiv.Perm (Fin (n + 1 + 1)) :=
    Ê.symm.toMonoidHom.comp (MonoidHom.codRestrict Φ₂ A hΦ₂)
  have hρE₁ : ∀ π, E (ρ₁ π) = Φ₁ π := by
    intro π
    show ((Ê (Ê.symm ⟨Φ₁ π, hΦ₁ π⟩) : ↥A) : MulAut ↥Bs) = Φ₁ π
    rw [MulEquiv.apply_symm_apply]
  have hρE₂ : ∀ π, E (ρ₂ π) = Φ₂ π := by
    intro π
    show ((Ê (Ê.symm ⟨Φ₂ π, hΦ₂ π⟩) : ↥A) : MulAut ↥Bs) = Φ₂ π
    rw [MulEquiv.apply_symm_apply]
  have hρ₁inj : Function.Injective ρ₁ := by
    intro a b hab
    have h : (⟨Φ₁ a, hΦ₁ a⟩ : ↥A) = ⟨Φ₁ b, hΦ₁ b⟩ := Ê.symm.injective hab
    exact hinj₁ (congrArg Subtype.val h)
  have hρ₂inj : Function.Injective ρ₂ := by
    intro a b hab
    have h : (⟨Φ₂ a, hΦ₂ a⟩ : ↥A) = ⟨Φ₂ b, hΦ₂ b⟩ := Ê.symm.injective hab
    exact hinj₂ (congrArg Subtype.val h)
  have hzero : (0 : Fin (n + 1)).castSucc ≠ (0 : Fin (n + 1)).succ := by
    simp [Fin.ext_iff]
  have hsw : ∀ x y : Fin (n + 1 + 1), x ≠ y → GGIsReflection p (E (Equiv.swap x y)) :=
    fun x y hxy =>
      ggIsReflection_swap_of_swap (E := E) (a := (0 : Fin (n + 1)).castSucc)
        (b := (0 : Fin (n + 1)).succ) hzero (hÊ 0) hxy
  have hs₁ : ∀ c d : Fin (n + 1), c ≠ d → (ρ₁ (Equiv.swap c d)).IsSwap := by
    intro c d hcd
    exact isSwap_of_ggIsReflection hp2 hBs E hEinj hsw (by rw [hρE₁]; exact hr₁ c d hcd)
  have hs₂ : ∀ c d : Fin (n + 1), c ≠ d → (ρ₂ (Equiv.swap c d)).IsSwap := by
    intro c d hcd
    exact isSwap_of_ggIsReflection hp2 hBs E hEinj hsw (by rw [hρE₂]; exact hr₂ c d hcd)
  have hJ' : ∀ i j : Fin n,
      ρ₁ (Equiv.swap i.succ j.succ) = ρ₂ (Equiv.swap i.castSucc j.castSucc) := by
    intro i j
    show Ê.symm ⟨Φ₁ (Equiv.swap i.succ j.succ), hΦ₁ _⟩ =
      Ê.symm ⟨Φ₂ (Equiv.swap i.castSucc j.castSucc), hΦ₂ _⟩
    exact congrArg Ê.symm (Subtype.ext (hJ i j))
  have hout' : ∀ σ, ρ₁ σ ≠ ρ₂ (Equiv.swap j.castSucc j.succ) := by
    intro σ hσ
    refine hout σ ?_
    have h := congrArg E hσ
    simpa only [hρE₁, hρE₂] using h
  have hcomm := ggFar_chain_commute hn ρ₁ ρ₂ hρ₁inj hρ₂inj hs₁ hs₂ hJ' hi hj hout'
  have h2 := congrArg E hcomm
  simp only [map_mul, hρE₁, hρE₂] at h2
  exact h2

end Aut

end CFSG.StandardType
