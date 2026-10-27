module

public import CFSG.Quasithin.Background.SmithB45Alt7Class

public section

namespace CFSG.Quasithin.B45Alt7

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3

section Class4

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

theorem card_eq_sixteen_of_equiv (Ψ : Vec 4 ≃ₗ[ZMod 2] Additive V) : Nat.card V = 2 ^ 4 := by
  have h1 : Nat.card (Vec 4) = Nat.card (Additive V) := Nat.card_congr Ψ.toEquiv
  have h2 : Nat.card (Additive V) = Nat.card V := rfl
  rw [← h2, ← h1, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 4),
    Fintype.card_fin]

theorem card_four_of_conj {i r : ℕ} (h : (i, r) ∈ [(5, 0), (8, 0), (6, 2), (10, 2)]) (c : Bool)
    (hrc : rB c = r)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hcard : Nat.card V ≤ 2 ^ 12) {ψ : Vec 4 →ₗ[ZMod 2] Additive V} (hψi : Function.Injective ψ)
    (hψ : ∀ b s, ψ (lin 4 (blkOf i b) s) = sigma6 ι (gen b) (ψ s)) :
    Nat.card V = 2 ^ 4 := by
  have hψ' : ∀ b s, (ψ.comp (lin 4 (indQ i))) (lin 4 (blkOf (rB c) b) s) =
      sigma6 ι (gen b) ((ψ.comp (lin 4 (indQ i))) s) := by
    intro b s
    simp only [LinearMap.comp_apply]
    rw [hrc, ← lin_conj h, hψ]
  have hinj : Function.Injective (ψ.comp (lin 4 (indQ i))) := by
    intro s s' hs
    have h1 := hψi hs
    have h2 := congrArg (lin 4 (indP i)) h1
    rwa [lin_PQ h, lin_PQ h] at h2
  obtain ⟨j, hj, Ψ, hΨ⟩ := exists_four_block ι hirr hcard c hinj hψ'
  exact card_eq_sixteen_of_equiv Ψ

theorem classifyFour (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hfix : fixV L = ⊥) (hcard : Nat.card V ≤ 2 ^ 12) :
    (∃ β : V ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : V),
      (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) = G6.permAct 7 (γ : Perm (Fin 7)) (β s)) ∨
    Nat.card V = 2 ^ 4 := by
  classical
  have hne : (⊤ : Submodule (ZMod 2) (Additive V)) ≠ ⊥ := by
    intro h
    have hall : ∀ v : V, v = 1 := fun v => by
      have : Additive.ofMul v ∈ (⊤ : Submodule (ZMod 2) (Additive V)) := trivial
      rw [h, Submodule.mem_bot] at this
      exact this
    have h1 : ((ι.symm (gen7 false) : ↥L) : MulAut V) = 1 :=
      MulEquiv.ext fun v => (hall _).trans (hall v).symm
    have h2 : ι.symm (gen7 false) = 1 := Subtype.ext h1
    have h3 : gen7 false = 1 := by
      have := congrArg ι h2
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    exact absurd h3 (by decide)
  obtain ⟨i, hi, ψ, hψi, hψ⟩ := exists_block_emb (sigma6 ι) hne
  have hone : ∀ (hi1 : i = 1 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 9),
      (∃ β : V ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : V),
        (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) =
          G6.permAct 7 (γ : Perm (Fin 7)) (β s)) := by
    intro hi1
    have hd : eNs.getD (i + 1) 0 - eNs.getD i 0 = 1 := by
      rcases hi1 with rfl | rfl | rfl | rfl | rfl <;> decide
    set e0 : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0) := Pi.single ⟨0, by omega⟩ 1 with he0
    have hv0 : ψ e0 ≠ 0 := by
      intro h
      have h1 : e0 = 0 := hψi (h.trans (map_zero ψ).symm)
      have h2 := congrFun h1 ⟨0, by omega⟩
      simp [he0] at h2
    refine exists_coreEquiv ι hirr hfix hv0 fun b => ?_
    have := hψ b e0
    rw [blkOf_one hi1, lin_one hd] at this
    exact this.symm
  interval_cases i
  · exact Or.inr (card_eq_sixteen_of_equiv
      (exists_four_block ι hirr hcard false hψi hψ).choose_spec.2.choose)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (card_eq_sixteen_of_equiv
      (exists_four_block ι hirr hcard true hψi hψ).choose_spec.2.choose)
  · exact Or.inl (hone (by omega))
  · exact Or.inl (hone (by omega))
  · exact Or.inr (card_four_of_conj (r := 0) ι (by simp) false (by decide) hirr hcard hψi hψ)
  · exact Or.inr (card_four_of_conj (r := 2) ι (by simp) true (by decide) hirr hcard hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (card_four_of_conj (r := 0) ι (by simp) false (by decide) hirr hcard hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (card_four_of_conj (r := 2) ι (by simp) true (by decide) hirr hcard hψi hψ)
  · exfalso
    have h1 : Nat.card (Vec (eNs.getD (11 + 1) 0 - eNs.getD 11 0)) ≤ Nat.card (Additive V) :=
      Nat.card_le_card_of_injective ψ hψi
    have h16 : eNs.getD (11 + 1) 0 - eNs.getD 11 0 = 16 := by decide
    rw [h16, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 16),
      Fintype.card_fin] at h1
    have h2 : Nat.card (Additive V) = Nat.card V := rfl
    rw [h2] at h1
    have := h1.trans hcard
    norm_num at this

end Class4

end CFSG.Quasithin.B45Alt7
