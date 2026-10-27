module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofChain

public section

namespace CFSG.GGQ2Prime

open CFSG.StandardType CFSG.Assembly CFSG.Open

theorem adjSwap6_ne : ∀ c d : Fin 5, c ≠ d →
    Equiv.swap c.castSucc c.succ ≠ Equiv.swap d.castSucc d.succ := by decide

theorem adjSwap6_braid : ∀ c : Fin 4,
    (Equiv.swap (c.castSucc.castSucc : Fin (5 + 1)) c.castSucc.succ *
      Equiv.swap c.succ.castSucc c.succ.succ) ^ 3 = 1 := by decide

theorem adjSwap6_comm : ∀ c d : Fin 5, c.val + 2 ≤ d.val →
    Equiv.swap (c.castSucc : Fin (5 + 1)) c.succ * Equiv.swap d.castSucc d.succ =
      Equiv.swap d.castSucc d.succ * Equiv.swap c.castSucc c.succ := by decide

theorem exists_chain_of_weylA5 {G : Type} [Group G] {Bs : Subgroup G} [Finite Bs]
    (hBs : IsElemAbelian 3 Bs) (E : Equiv.Perm (Fin (5 + 1 + 1)) →* MulAut Bs)
    (hEinj : Function.Injective E) (hsw : ∀ a b, a ≠ b → GGIsReflection 3 (E (Equiv.swap a b)))
    {AL : Subgroup (MulAut Bs)} (hAL : AL ≤ E.range)
    (hW5 : GGWeylOfType 3 (CoxeterMatrix.A 5) AL) :
    ∃ w : ℕ → Fin (5 + 1 + 1), (∀ c d, c ≤ 5 → d ≤ 5 → w c = w d → c = d) ∧
      ∀ c, c < 5 → E (Equiv.swap (w c) (w (c + 1))) ∈ AL := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E', hE'⟩ := exists_permEquiv_of_ggWeylOfType_A hW5
  let R : Equiv.Perm (Fin (5 + 1 + 1)) ≃* E.range := MonoidHom.ofInjective hEinj
  let F : Equiv.Perm (Fin (5 + 1)) →* Equiv.Perm (Fin (5 + 1 + 1)) :=
    R.symm.toMonoidHom.comp ((Subgroup.inclusion hAL).comp E'.toMonoidHom)
  have hEF : ∀ ρ, E (F ρ) = (E' ρ : MulAut Bs) := fun ρ => by
    have h : ((R (R.symm ((Subgroup.inclusion hAL) (E' ρ))) : E.range) : MulAut Bs) =
        E (R.symm ((Subgroup.inclusion hAL) (E' ρ))) := MonoidHom.ofInjective_apply hEinj
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hFinj : Function.Injective F := by
    intro ρ ρ' h
    apply E'.injective
    apply Subtype.ext
    rw [← hEF, ← hEF, h]
  let adj : Fin 5 → Equiv.Perm (Fin (5 + 1)) := fun c => Equiv.swap c.castSucc c.succ
  let s : ℕ → Equiv.Perm (Fin (5 + 1 + 1)) := fun c => if h : c < 5 then F (adj ⟨c, h⟩) else 1
  have hs : ∀ c (h : c < 5), s c = F (adj ⟨c, h⟩) := fun c h => dif_pos h
  obtain ⟨w, hwinj, hweq⟩ := chain_labels s 5 (by norm_num)
    (fun c hc => by
      rw [hs c hc]
      exact isSwap_of_ggIsReflection (p := 3) (by norm_num) hBs E hEinj hsw
        (by rw [hEF]; exact hE' ⟨c, hc⟩))
    (fun c d hcd hd => by
      rw [hs c (by omega), hs d hd]
      intro h
      exact adjSwap6_ne ⟨c, by omega⟩ ⟨d, hd⟩ (fun h' => by
        have := congrArg Fin.val h'
        simp at this
        omega) (hFinj h))
    (fun c hc => by
      rw [hs c (by omega), hs (c + 1) hc, ← map_mul, ← map_pow]
      have := adjSwap6_braid ⟨c, by omega⟩
      have e1 : adj ⟨c, by omega⟩ = Equiv.swap ((⟨c, by omega⟩ : Fin 4).castSucc.castSucc)
          (⟨c, by omega⟩ : Fin 4).castSucc.succ := rfl
      have e2 : adj ⟨c + 1, hc⟩ = Equiv.swap ((⟨c, by omega⟩ : Fin 4).succ.castSucc)
          (⟨c, by omega⟩ : Fin 4).succ.succ := rfl
      rw [e1, e2, this, map_one])
    (fun c d hcd hd => by
      rw [hs c (by omega), hs d hd, ← map_mul, ← map_mul,
        adjSwap6_comm ⟨c, by omega⟩ ⟨d, hd⟩ hcd])
  refine ⟨w, hwinj, fun c hc => ?_⟩
  rw [← hweq c hc, hs c hc, hEF]
  exact (E' (adj ⟨c, hc⟩)).2

theorem zmod3_three : (3 : ZMod 3) = 0 := by decide

@[expose] def adjSwap7 (i : Fin (5 + 1)) : Equiv.Perm (Fin (5 + 1 + 1)) :=
  Equiv.swap i.castSucc i.succ

theorem adjSwap7_ne : ∀ i j : Fin (5 + 1), i ≠ j → adjSwap7 i ≠ adjSwap7 j := by decide

theorem adjSwap7_comm : ∀ i j : Fin (5 + 1), i.val + 2 ≤ j.val →
    adjSwap7 i * adjSwap7 j = adjSwap7 j * adjSwap7 i := by
  decide

theorem adjSwap7_braid : ∀ i j : Fin (5 + 1), i.val + 1 = j.val →
    adjSwap7 i * adjSwap7 j * adjSwap7 i = adjSwap7 j * adjSwap7 i * adjSwap7 j := by decide

theorem conj_adjSwap7 (lab : Equiv.Perm (Fin (5 + 1 + 1))) (i : Fin (5 + 1)) :
    (MulAut.conj lab) (adjSwap7 i) = Equiv.swap (lab i.castSucc) (lab i.succ) := by
  rw [MulAut.conj_apply, adjSwap7, Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right]

end CFSG.GGQ2Prime
