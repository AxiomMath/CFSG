module

public import CFSG.Quasithin.Background.SmithB45Alt7Class
public import CFSG.RankThree.FFModules.RepMulAut

public section

namespace CFSG.Quasithin.A7Q528

open Equiv Equiv.Perm CFSG.QuasithinUnique.Setup.X3E CFSG.QuasithinUnique.Setup.X3
open CFSG.Quasithin.B45Alt7

section Class

variable {V : Type} [CommGroup V] [Finite V] [Module (ZMod 2) (Additive V)]
  {L : Subgroup (MulAut V)} (ι : ↥L ≃* A7)

theorem fourBlock_of_conj {i r : ℕ} (h : (i, r) ∈ [(5, 0), (8, 0), (6, 2), (10, 2)]) (c : Bool)
    (hrc : rB c = r)
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hcard : Nat.card V ≤ 2 ^ 12) {ψ : Vec 4 →ₗ[ZMod 2] Additive V} (hψi : Function.Injective ψ)
    (hψ : ∀ b s, ψ (lin 4 (blkOf i b) s) = sigma6 ι (gen b) (ψ s)) :
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ₗ[ZMod 2] Additive V,
      ∀ b s, Ψ (lin 4 (indBlk true j b) s) = rho7 ι (gen7 b) (Ψ s) := by
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
  exact exists_four_block ι hirr hcard c hinj hψ'

theorem classify4 (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hfix : fixV L = ⊥) (hcard : Nat.card V ≤ 2 ^ 12) :
    (∃ β : V ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : V),
      (β ((ι.symm γ : MulAut V) s) : G6.PermMod 7) = G6.permAct 7 (γ : Perm (Fin 7)) (β s)) ∨
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ₗ[ZMod 2] Additive V,
      ∀ b s, Ψ (lin 4 (indBlk true j b) s) = rho7 ι (gen7 b) (Ψ s) := by
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
  · exact Or.inr (exists_four_block ι hirr hcard false hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (exists_four_block ι hirr hcard true hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inl (hone (by omega))
  · exact Or.inr (fourBlock_of_conj (r := 0) ι (by simp) false (by decide) hirr hcard hψi hψ)
  · exact Or.inr (fourBlock_of_conj (r := 2) ι (by simp) true (by decide) hirr hcard hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (fourBlock_of_conj (r := 0) ι (by simp) false (by decide) hirr hcard hψi hψ)
  · exact Or.inl (hone (by omega))
  · exact Or.inr (fourBlock_of_conj (r := 2) ι (by simp) true (by decide) hirr hcard hψi hψ)
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

end Class

theorem papply_fpf : ∀ j < 2, ∀ x < 16, papply 4 (indBlk true j false) x < 16 ∧
    (papply 4 (indBlk true j false) x = x → x = 0) := by
  decide +kernel

theorem lin_fpf {j : ℕ} (hj : j < 2) {s : Vec 4} (h : lin 4 (indBlk true j false) s = s) :
    s = 0 := by
  obtain ⟨x, hx, rfl⟩ := exists_toVec s
  have hx' : x < 16 := by simpa using hx
  obtain ⟨hlt, hfix⟩ := papply_fpf j hj x hx'
  rw [← toVec_papply] at h
  rw [hfix (toVec_injOn (by simpa using hlt) hx h), toVec_zero]

section Sect

variable {S : Type} [AddCommGroup S] [Module (ZMod 2) S]

theorem section_cases [Finite S] (ρ : Representation (ZMod 2) A7 S)
    (hirr : ∀ J : Submodule (ZMod 2) S, (∀ g, ∀ s ∈ J, ρ g s ∈ J) → J = ⊥ ∨ J = ⊤)
    (hnt : ∃ g s, ρ g s ≠ s) (hcard : Nat.card S ≤ 2 ^ 12) :
    (∃ β : Multiplicative S ≃* ↥(G6.coreMod 7), ∀ (γ : A7) (s : S),
      (β (Multiplicative.ofAdd (ρ γ s)) : G6.PermMod 7) =
        G6.permAct 7 (γ : Perm (Fin 7)) (β (Multiplicative.ofAdd s))) ∨
    ∃ j < 2, ∃ Ψ : Vec 4 ≃ₗ[ZMod 2] S,
      ∀ b s, Ψ (lin 4 (indBlk true j b) s) = ρ (gen7 b) (Ψ s) := by
  classical
  set τ := CFSG.RankThree.FFModules.repMulAut ρ with hτ
  have hker : τ.ker = ⊥ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 7) (by simp)
      (N := τ.ker) with h | h
    · exact h
    · exfalso
      obtain ⟨g, s, hgs⟩ := hnt
      have hg : τ g = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)
      have h1 := congrArg (fun φ : MulAut (Multiplicative S) =>
        Multiplicative.toAdd (φ (Multiplicative.ofAdd s))) hg
      exact hgs h1
  have hinj : Function.Injective τ := (MonoidHom.ker_eq_bot_iff τ).mp hker
  set L := τ.range with hL
  set ι : ↥L ≃* A7 := (MonoidHom.ofInjective hinj).symm with hι
  have hιs : ∀ γ : A7, ((ι.symm γ : ↥L) : MulAut (Multiplicative S)) = τ γ := fun γ => by
    rw [hι, MulEquiv.symm_symm, MonoidHom.ofInjective_apply]
  let _ : Module (ZMod 2) (Additive (Multiplicative S)) := inferInstanceAs (Module (ZMod 2) S)
  have hirr' : ∀ J : Subgroup (Multiplicative S), (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    let J' : Submodule (ZMod 2) S :=
      { carrier := {s | Multiplicative.ofAdd s ∈ J}
        add_mem' := fun {a b} ha hb => J.mul_mem ha hb
        zero_mem' := J.one_mem
        smul_mem' := fun c s hs => by
          have e : c • s = c.val • s := by
            rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
          show Multiplicative.ofAdd (c • s) ∈ J
          rw [e, ofAdd_nsmul]
          exact J.pow_mem hs _ }
    have hJ' : ∀ g, ∀ s ∈ J', ρ g s ∈ J' := fun g s hs => hJ (τ g) ⟨g, rfl⟩ _ hs
    rcases hirr J' hJ' with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h1 : Multiplicative.toAdd v ∈ J' := hv
      rw [h, Submodule.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact toAdd_eq_zero.mp h1
    · right
      rw [eq_top_iff]
      intro v _
      have h1 : Multiplicative.toAdd v ∈ J' := h ▸ Submodule.mem_top
      exact h1
  have hfix : fixV L = ⊥ := by
    have hinv : ∀ l ∈ L, ∀ v ∈ fixV L, l v ∈ fixV L := by
      intro l hl v hv
      rw [mem_fixV] at hv ⊢
      intro x hx
      rw [hv l hl]
      exact hv x hx
    rcases hirr' (fixV L) hinv with h | h
    · exact h
    · exfalso
      obtain ⟨g, s, hgs⟩ := hnt
      have h1 : Multiplicative.ofAdd s ∈ fixV L := h ▸ Subgroup.mem_top _
      exact hgs (congrArg Multiplicative.toAdd ((mem_fixV.mp h1) (τ g) ⟨g, rfl⟩))
  have hcard' : Nat.card (Multiplicative S) ≤ 2 ^ 12 := hcard
  rcases classify4 ι hirr' hfix hcard' with ⟨β, hβ⟩ | ⟨j, hj, Ψ, hΨ⟩
  · left
    refine ⟨β, fun γ s => ?_⟩
    have h1 := hβ γ (Multiplicative.ofAdd s)
    rw [hιs] at h1
    exact h1
  · right
    refine ⟨j, hj, Ψ, fun b s => ?_⟩
    have h1 := hΨ b s
    rw [rho7_apply, hιs] at h1
    exact h1

end Sect

end CFSG.Quasithin.A7Q528
