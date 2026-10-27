module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CX
public import CFSG.Quasithin.Vol2.Ch10SecQ3CY
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixBaum

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem map_eq_closure_swaps {L J X : Subgroup (MulAut V)} (θ : ↥L ≃* Equiv.Perm (Fin 5))
    (hgen : L ⊓ J = Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ X ∧ (θ ⟨x, hx⟩).IsSwap}) :
    ((L ⊓ J).subgroupOf L).map θ.toMonoidHom = Subgroup.closure
      (θ.toMonoidHom '' {y : ↥L | (y : MulAut V) ∈ X ∧ (θ y).IsSwap}) := by
  set S' : Set ↥L := {y | (y : MulAut V) ∈ X ∧ (θ y).IsSwap} with hS'
  have h1 : (Subgroup.closure S').map L.subtype = L ⊓ J := by
    rw [MonoidHom.map_closure, hgen]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨y.2, h1, h2⟩
    · rintro ⟨hx, h1, h2⟩
      exact ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩
  have h2 : (L ⊓ J).subgroupOf L = Subgroup.closure S' := by
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  rw [h2, MonoidHom.map_closure]

theorem eq_one_of_A5_component {L J X : Subgroup (MulAut V)} (θ : ↥L ≃* Equiv.Perm (Fin 5))
    (hcard : Nat.card ↥(L ⊓ J) = 4)
    (hgen : L ⊓ J = Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ X ∧ (θ ⟨x, hx⟩).IsSwap})
    {ψ : MulAut V} (hψ : ψ ∈ L) (hψo : Odd (orderOf ψ))
    (hψN : ∀ x ∈ L ⊓ J, ψ * x * ψ⁻¹ ∈ L ⊓ J) : ψ = 1 := by
  have hQc : Nat.card ↥(((L ⊓ J).subgroupOf L).map θ.toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective θ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hcard]
  have hσo : Odd (orderOf (θ ⟨ψ, hψ⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hψo
  have hσN : ∀ x ∈ ((L ⊓ J).subgroupOf L).map θ.toMonoidHom,
      θ ⟨ψ, hψ⟩ * x * (θ ⟨ψ, hψ⟩)⁻¹ ∈ ((L ⊓ J).subgroupOf L).map θ.toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨ψ, hψ⟩ * y * (⟨ψ, hψ⟩ : ↥L)⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
    exact hψN _ hy
  have h := eq_one_of_normalizes_swaps (by rintro _ ⟨y, ⟨-, hy⟩, rfl⟩; exact hy)
    (map_eq_closure_swaps θ hgen) hQc hσN hσo
  have h' : (⟨ψ, hψ⟩ : ↥L) = 1 := θ.injective (by rw [h, map_one])
  exact congrArg Subtype.val h'

theorem exists_mul_of_mem_sup_comm {Y : Type*} [Group Y] {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : Y} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hN : B ≤ Subgroup.normalizer (A : Set Y) := by
    refine le_trans (fun b hb => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hc a ha b hb
  have hx' : x ∈ ((A ⊔ B : Subgroup Y) : Set Y) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hN] at hx'
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, rfl⟩

theorem eq_one_of_A5_components {I : Finset (Subgroup (MulAut V))} {J X : Subgroup (MulAut V)}
    (hcard : I.card = 1 ∨ I.card = 2)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hindep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (h3 : ∀ L ∈ I, Nat.card ↥(L ⊓ J) = 4 ∧ ∃ θ : ↥L ≃* Equiv.Perm (Fin 5), L ⊓ J =
      Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ X ∧ (θ ⟨x, hx⟩).IsSwap})
    {φ : MulAut V} (hφ : φ ∈ ⨆ L ∈ I, L) (hφo : Odd (orderOf φ))
    (hφN : ∀ x ∈ J, φ * x * φ⁻¹ ∈ J) : φ = 1 := by
  classical
  have hcomp : ∀ L ∈ I, ∀ ψ ∈ L, Odd (orderOf ψ) →
      (∀ x ∈ L ⊓ J, ψ * x * ψ⁻¹ ∈ L ⊓ J) → ψ = 1 := by
    intro L hL ψ hψ ho hN
    obtain ⟨hc, θ, hg⟩ := h3 L hL
    exact eq_one_of_A5_component θ hc hg hψ ho hN
  rcases hcard with h1 | h2
  · obtain ⟨L, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.iSup_singleton] at hφ
    exact hcomp L (Finset.mem_singleton_self L) φ hφ hφo fun x hx =>
      ⟨L.mul_mem (L.mul_mem hφ hx.1) (L.inv_mem hφ), hφN x hx.2⟩
  · obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.mp h2
    have hA : A ∈ ({A, B} : Finset _) := by simp
    have hB : B ∈ ({A, B} : Finset _) := by simp
    rw [Finset.iSup_insert, Finset.iSup_singleton] at hφ
    have hcAB := hcomm A hA B hB hAB
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_comm hcAB hφ
    have hAB1 : ∀ x ∈ A, x ∈ B → x = 1 := by
      intro x hxA hxB
      have hle : B ≤ ⨆ L' ∈ ({A, B} : Finset _), ⨆ (_ : L' ≠ A), L' :=
        le_iSup₂_of_le (f := fun L' _ => ⨆ (_ : L' ≠ A), L') B hB
          (le_iSup_of_le (Ne.symm hAB) le_rfl)
      have hx : x ∈ A ⊓ ⨆ L' ∈ ({A, B} : Finset _), ⨆ (_ : L' ≠ A), L' := ⟨hxA, hle hxB⟩
      rw [hindep A hA] at hx
      exact hx
    have hab : a * b = b * a := hcAB a ha b hb
    have hk : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
    rw [Commute.mul_pow hab] at hk
    have han : a ^ orderOf (a * b) = 1 := by
      refine hAB1 _ (A.pow_mem ha _) ?_
      rw [eq_inv_of_mul_eq_one_left hk]
      exact B.inv_mem (B.pow_mem hb _)
    have hbn : b ^ orderOf (a * b) = 1 := by
      rw [han, one_mul] at hk
      exact hk
    have ha1 : a = 1 := by
      refine hcomp A hA a ha (hφo.of_dvd_nat (orderOf_dvd_of_pow_eq_one han)) fun x hx =>
        ⟨A.mul_mem (A.mul_mem ha hx.1) (A.inv_mem ha), ?_⟩
      have h := hφN x hx.2
      have hbx : b * x = x * b := (hcAB x hx.1 b hb).symm
      have e : a * b * x * (a * b)⁻¹ = a * x * a⁻¹ := by
        rw [mul_inv_rev, mul_assoc a b x, hbx]
        group
      rwa [e] at h
    have hb1 : b = 1 := by
      refine hcomp B hB b hb (hφo.of_dvd_nat (orderOf_dvd_of_pow_eq_one hbn)) fun x hx =>
        ⟨B.mul_mem (B.mul_mem hb hx.1) (B.inv_mem hb), ?_⟩
      have h := hφN x hx.2
      have hax : a * x = x * a := hcAB a ha x hx.1
      have e : a * b * x * (a * b)⁻¹ = b * x * b⁻¹ := by
        rw [hab, mul_inv_rev, mul_assoc b a x, hax]
        group
      rwa [e] at h
    rw [ha1, hb1, one_mul]

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem isA5Module_of_isA5Module {H T W : Subgroup Γ} {hW : IsElemAbelian 2 W}
    {I : Finset (Subgroup (MulAut (IntMod W hW)))} (hD : E23Data H T W hW I)
    {K₀ : Subgroup (MulAut (IntMod W hW))} (hK₀ : K₀ ∈ I) (h5 : E2.IsA5Module K₀) :
    ∀ L ∈ I, E2.IsA5Module L := by
  intro L hL
  rcases hD.types L hL with ⟨m, hm⟩ | h
  · obtain ⟨s, -, hs⟩ := hD.trans K₀ hK₀ L hL
    have hc := SecA.card_of_isL2Natural hm
    rw [← hs, SecA.card_conjAut, SecA.card_of_isA5Module h5] at hc
    exact absurd hc.symm (SecA.two_pow_mul_ne_120 m)
  · exact h

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
