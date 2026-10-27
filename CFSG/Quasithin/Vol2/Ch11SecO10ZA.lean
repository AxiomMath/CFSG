module

public import CFSG.Quasithin.H13.A7Offender
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.H13.A7

variable {G : Type} [Group G]

theorem isElemAbelian_map_hom {H : Type*} [Group H] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) (f : G →* H) : IsElemAbelian p (E.map f) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem exists_conj_offender [Finite G] {T V N : Subgroup G} (hT : quasithinIsSylowTwo T)
    {ψ : V ≃* Multiplicative (evenWeight 7)} (hNV : N ≤ normalizer (V : Set G))
    (hN : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ) (hTN : T ≤ N)
    (hTP : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ t σ) {B : Subgroup G}
    (hBmax : IsMaxElemAbelian T B) (hBT3 : ∀ b ∈ B, ∀ σ, IsCoordAct ψ b σ → InT3 σ) {b₀ : G}
    (hb₀ : b₀ ∈ B) {τ κ : Perm (Fin 7)} (hτ : IsCoordAct ψ b₀ τ) {g : G} (hgN : g ∈ N)
    (hg : IsCoordAct ψ g κ)
    (hκT3 : ∀ u, InT3 (sevenWord u) →
      InT3 (κ * sevenWord u * κ⁻¹) ∧ sevenCond (κ * sevenWord u * κ⁻¹)) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ∃ a ∈ A, ∃ σ ∈ sevenP, IsCoordAct ψ a (σ * (κ * τ * κ⁻¹) * σ⁻¹) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set TG : Sylow 2 G := hT.1.toSylow hT.2 with hTG
  have hTGcoe : (TG : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  set lamN : N →* Perm (Fin 7) := coordRep ψ hNV hN with hlamN
  have hspec : ∀ m : N, IsCoordAct ψ m (lamN m) := coordRep_spec ψ hNV hN
  have heq : ∀ (m : N) {σ : Perm (Fin 7)}, IsCoordAct ψ m σ → lamN m = σ := fun m σ hσ =>
    IsCoordAct.unique ψ (hNV m.2) (hspec m) hσ
  have hBT : B ≤ T := hBmax.1
  have hBN : B ≤ N := hBT.trans hTN
  set X : Subgroup G := (sevenP.comap lamN).map N.subtype with hXdef
  have hmemX : ∀ n (hn : n ∈ N), lamN ⟨n, hn⟩ ∈ sevenP → n ∈ X := fun n hn h =>
    ⟨⟨n, hn⟩, h, rfl⟩
  have hTX : T ≤ X := fun t ht => by
    obtain ⟨σ, hσP, hσ⟩ := hTP t ht
    exact hmemX t (hTN ht) (by rw [heq ⟨t, hTN ht⟩ hσ]; exact hσP)
  have hlamP : ∀ b (hb : b ∈ B), lamN ⟨b, hBN hb⟩ ∈ sevenP := fun b hb => by
    obtain ⟨σ, hσP, hσ⟩ := hTP b (hBT hb)
    rw [heq ⟨b, hBN hb⟩ hσ]
    exact hσP
  set B' : Subgroup G := B.map (MulAut.conj g).toMonoidHom with hB'def
  have hconjN : ∀ b ∈ B, g * b * g⁻¹ ∈ N := fun b hb =>
    mul_mem (mul_mem hgN (hBN hb)) (inv_mem hgN)
  have hlamconj : ∀ b (hb : b ∈ B), lamN ⟨g * b * g⁻¹, hconjN b hb⟩ =
      κ * lamN ⟨b, hBN hb⟩ * κ⁻¹ := by
    intro b hb
    rw [show (⟨g * b * g⁻¹, hconjN b hb⟩ : N) = ⟨g, hgN⟩ * ⟨b, hBN hb⟩ * ⟨g, hgN⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv, heq ⟨g, hgN⟩ hg]
  have hB'X : B' ≤ X := by
    rintro _ ⟨b, hb, rfl⟩
    have hcj : (MulAut.conj g).toMonoidHom b = g * b * g⁻¹ := rfl
    rw [hcj]
    refine hmemX _ (hconjN b hb) ?_
    obtain ⟨u, hu⟩ := exists_word_of_mem_sevenP (hlamP b hb)
    have hT3b := hBT3 b hb _ (hspec ⟨b, hBN hb⟩)
    rw [hu] at hT3b
    have h1 := (hκT3 u hT3b).2
    rw [← hu, ← hlamconj b hb] at h1
    exact mem_sevenP_of_sevenCond h1
  have hB2 : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow]; exact hBmax.2.1.2 b b.2)⟩
  have hB'2 : IsPGroup 2 B' := hB2.map _
  obtain ⟨x, hxX, hxT⟩ := exists_conj_le_of_le TG (hTGcoe ▸ hTX) hB'X hB'2
  rw [hTGcoe] at hxT
  set A : Subgroup G := B'.map (MulAut.conj x).toMonoidHom with hAdef
  have hAT : A ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    exact hxT b hb
  have hcard : Nat.card A = Nat.card B := by
    rw [hAdef, card_map_of_injective (MulAut.conj x).injective, hB'def,
      card_map_of_injective (MulAut.conj g).injective]
  have hAel : IsElemAbelian 2 A :=
    isElemAbelian_map_hom (isElemAbelian_map_hom hBmax.2.1 _) _
  refine ⟨A, ⟨hAT, hAel, fun C hC hCel => hcard ▸ hBmax.2.2 C hC hCel⟩,
    x * (g * b₀ * g⁻¹) * x⁻¹, ⟨g * b₀ * g⁻¹, ⟨b₀, hb₀, rfl⟩, rfl⟩, ?_⟩
  obtain ⟨⟨x', hx'N⟩, hx'P, rfl⟩ := hxX
  have hjN : x' * (g * b₀ * g⁻¹) * x'⁻¹ ∈ N :=
    mul_mem (mul_mem hx'N (hconjN b₀ hb₀)) (inv_mem hx'N)
  refine ⟨lamN ⟨x', hx'N⟩, hx'P, ?_⟩
  have hlamj : lamN ⟨x' * (g * b₀ * g⁻¹) * x'⁻¹, hjN⟩ =
      lamN ⟨x', hx'N⟩ * (κ * τ * κ⁻¹) * (lamN ⟨x', hx'N⟩)⁻¹ := by
    rw [show (⟨x' * (g * b₀ * g⁻¹) * x'⁻¹, hjN⟩ : N) =
        ⟨x', hx'N⟩ * ⟨g * b₀ * g⁻¹, hconjN b₀ hb₀⟩ * ⟨x', hx'N⟩⁻¹ from rfl,
      map_mul, map_mul, map_inv, hlamconj b₀ hb₀, heq ⟨b₀, hBN hb₀⟩ hτ]
  have h1 := hspec ⟨x' * (g * b₀ * g⁻¹) * x'⁻¹, hjN⟩
  rw [hlamj] at h1
  exact h1

end CFSG.Quasithin.Vol2.Ch11.O10
