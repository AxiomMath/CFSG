module

public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.S146C2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {K Z U₁ D : Subgroup G} {s : G}

theorem Sec8.false_of_decomp (h : Sec8 K Z U₁) (hsimple : IsSimpleGroup (KBar K))
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ Z)
    (h168 : (pCoreOf 2 K).relIndex K = 168) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hsZ : s ∈ Subgroup.normalizer (Z : Set G)) (hout : KbarInducesOuter K s)
    (hDN : D ≤ Subgroup.normalizer (Z : Set G)) (hKD : K ≤ Subgroup.normalizer (D : Set G))
    (hZU₂ : Z ≤ conjSub s U₁) (hE₁ : U₁ ⊓ D ≤ Z) (hE₂ : conjSub s U₁ ⊓ D ≤ Z)
    (hle : conjSub s U₁ ≤ U₁ ⊔ D)
    (hab : ∀ x ∈ U₁ ⊔ D, ∀ y ∈ U₁ ⊔ D, x * y * x⁻¹ * y⁻¹ ∈ Z) (hsq : ∀ x ∈ U₁ ⊔ D, x ^ 2 ∈ Z) :
    False := by
  classical
  set A := Subgroup.normalizer (Z : Set G) with hA
  set c : SecQuot A Z := secMk A Z ⟨s, hsZ⟩ with hc
  have hWE : tildeOf Z U₁ ⊓ tildeOf Z D = ⊥ := by
    rw [← tildeOf_inf h.le]
    exact eq_bot_iff.mpr ((secImg_mono hE₁).trans (tildeOf_eq_bot_of_le le_rfl).le)
  have hconj : conjSub c (tildeOf Z U₁) = tildeOf Z (conjSub s U₁) := (tildeOf_conjSub hsZ).symm
  have hW2E : conjSub c (tildeOf Z U₁) ⊓ tildeOf Z D = ⊥ := by
    rw [hconj, ← tildeOf_inf hZU₂]
    exact eq_bot_iff.mpr ((secImg_mono hE₂).trans (tildeOf_eq_bot_of_le le_rfl).le)
  have hsup : tildeOf Z (U₁ ⊔ D) = tildeOf Z U₁ ⊔ tildeOf Z D := tildeOf_sup h.norm hDN
  have hle' : conjSub c (tildeOf Z U₁) ≤ tildeOf Z U₁ ⊔ tildeOf Z D := by
    rw [hconj, ← hsup]
    exact secImg_mono hle
  have hel : IsElemAbelian 2 (tildeOf Z U₁ ⊔ tildeOf Z D) := by
    rw [← hsup]
    exact isElemAbelian_secImg_normalizer hab hsq
  have hcomm : ∀ x ∈ tildeOf Z U₁ ⊔ tildeOf Z D, ∀ y ∈ tildeOf Z U₁ ⊔ tildeOf Z D, x * y = y * x :=
    fun x hx y hy => isElemAbelian_comm hel hx hy
  obtain ⟨ψ, hψ⟩ := exists_twisted_mulAut hWE hW2E hle' hcomm
  have hψ' : ∀ k : ↥K, ψ * h.rho k * ψ⁻¹ = h.rho (conjAct K ⟨s, hsK⟩ k) := by
    intro k
    set g : SecQuot A Z := secMk A Z (Subgroup.inclusion h.KZ k) with hg
    have hgW : g ∈ Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot A Z)) :=
      secMk_mem_normalizer_secImg (a := Subgroup.inclusion h.KZ k) (h.KU k.2)
    have hσ : (Subgroup.inclusion h.KZ (conjAct K ⟨s, hsK⟩ k) : ↥A) =
        ⟨s, hsZ⟩ * Subgroup.inclusion h.KZ k * ⟨s, hsZ⟩⁻¹ := by
      apply Subtype.ext
      exact conjAct_apply_coe' K ⟨s, hsK⟩ k
    have hg' : secMk A Z (Subgroup.inclusion h.KZ (conjAct K ⟨s, hsK⟩ k)) = c * g * c⁻¹ := by
      rw [hσ, map_mul, map_mul, map_inv]
    have hg'W : c * g * c⁻¹ ∈ Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot A Z)) := by
      rw [← hg']
      exact secMk_mem_normalizer_secImg (a := Subgroup.inclusion h.KZ (conjAct K ⟨s, hsK⟩ k))
        (h.KU (conjAct K ⟨s, hsK⟩ k).2)
    have hg'E : c * g * c⁻¹ ∈ Subgroup.normalizer (tildeOf Z D : Set (SecQuot A Z)) := by
      rw [← hg']
      exact secMk_mem_normalizer_secImg (a := Subgroup.inclusion h.KZ (conjAct K ⟨s, hsK⟩ k))
        (hKD (conjAct K ⟨s, hsK⟩ k).2)
    have key := twisted_conj hWE ψ hψ hgW hg'W hg'E
    have e1 : h.rho k = conjAct (tildeOf Z U₁) ⟨g, hgW⟩ := rfl
    have e2 : h.rho (conjAct K ⟨s, hsK⟩ k) = conjAct (tildeOf Z U₁) ⟨c * g * c⁻¹, hg'W⟩ := by
      show conjAct (tildeOf Z U₁) _ = _
      congr 1
    rw [e1, e2]
    exact key
  exact h.false_of_twisted hsimple hQ h168 hsK hout ψ hψ'

end CFSG.Quasithin
