module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameAux

public section

namespace CFSG.StandardType

open SpCoord

theorem bSignedFull_eq_signedPermSubgroup (n p : ℕ) :
    bSignedFull n p = SignedPermCount.signedPermSubgroup p n := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro r (⟨i, rfl⟩ | ⟨a, b, _, rfl⟩)
    · change IsSignedPerm ⇑(sgnAut i)
      exact isSignedPerm_sgnAut i
    · change IsSignedPerm ⇑(permAut (Equiv.swap a b))
      exact isSignedPerm_permAut (Equiv.swap a b)
  · intro u hu
    change IsSignedPerm ⇑u at hu
    exact mem_of_isSignedPerm
      (fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩))
      (fun a b hab => Subgroup.subset_closure (Or.inr ⟨a, b, hab, rfl⟩)) hu

private theorem spRefl_u_short {n p : ℕ}
    (u : Fin n → MulAut (Fin n → Multiplicative (ZMod p)))
    (hu : ∀ k f, u k f = SpJoin.spReflPerm n p k f)
    (k : Fin n) (hk : k.val + 1 < n) :
    u k = permAut (Equiv.swap k ⟨k.val + 1, hk⟩) := by
  refine MulEquiv.ext fun f => ?_
  rw [hu k f, SpJoin.spReflPerm_of_lt n p k hk]
  rfl

private theorem spRefl_u_long {n p : ℕ}
    (u : Fin n → MulAut (Fin n → Multiplicative (ZMod p)))
    (hu : ∀ k f, u k f = SpJoin.spReflPerm n p k f)
    (k : Fin n) (hk : ¬ k.val + 1 < n) :
    u k = sgnAut (p := p) k := by
  refine MulEquiv.ext fun f => ?_
  rw [hu k f, SpJoin.spReflPerm_of_not_lt n p k hk]
  rfl

private theorem permAut_swap_mem_closure_spRefl {n p : ℕ}
    (u : Fin n → MulAut (Fin n → Multiplicative (ZMod p)))
    (hu : ∀ k f, u k f = SpJoin.spReflPerm n p k f)
    {a b : Fin n} (hab : a ≠ b) :
    permAut (Equiv.swap a b) ∈ Subgroup.closure (Set.range u) := by
  rcases n with _ | m
  · exact a.elim0
  · have hK : (Subgroup.closure (Set.range u)).comap
        (ggSpSigned_permAutHom p (m + 1)) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rw [← Subgroup.closure_eq_top_of_mclosure_eq_top
        (Equiv.Perm.mclosure_swap_castSucc_succ m)]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      change (ggSpSigned_permAutHom p (m + 1)) (Equiv.swap i.castSucc i.succ) ∈
        Subgroup.closure (Set.range u)
      rw [show (ggSpSigned_permAutHom p (m + 1)) (Equiv.swap i.castSucc i.succ) =
        permAut (Equiv.swap i.castSucc i.succ) from rfl]
      have hlt : (i.castSucc : Fin (m + 1)).val + 1 < m + 1 :=
        Nat.succ_lt_succ i.isLt
      rw [show i.succ = (⟨(i.castSucc).val + 1, hlt⟩ : Fin (m + 1)) from
        Fin.ext rfl, ← spRefl_u_short u hu i.castSucc hlt]
      exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
    have hmem : (ggSpSigned_permAutHom p (m + 1)) (Equiv.swap a b) ∈
        Subgroup.closure (Set.range u) := by
      have h : Equiv.swap a b ∈ (Subgroup.closure (Set.range u)).comap
          (ggSpSigned_permAutHom p (m + 1)) := by
        rw [hK]
        exact Subgroup.mem_top _
      exact h
    rw [show (ggSpSigned_permAutHom p (m + 1)) (Equiv.swap a b) =
      permAut (Equiv.swap a b) from rfl] at hmem
    exact hmem

private theorem sgnAut_mem_closure_spRefl {n p : ℕ}
    (u : Fin n → MulAut (Fin n → Multiplicative (ZMod p)))
    (hu : ∀ k f, u k f = SpJoin.spReflPerm n p k f)
    (i : Fin n) : sgnAut i ∈ Subgroup.closure (Set.range u) := by
  have hn : 0 < n := Fin.pos i
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : ¬ last.val + 1 < n := by
    simp only [last]
    rw [Nat.sub_add_cancel hn]
    exact Nat.lt_irrefl n
  have hu_last : sgnAut (p := p) last ∈ Subgroup.closure (Set.range u) := by
    have h := Subgroup.subset_closure (show u last ∈ Set.range u from ⟨last, rfl⟩)
    rwa [spRefl_u_long u hu last hlast] at h
  by_cases hi : i = last
  · rw [hi]
    exact hu_last
  · have hσ : permAut (Equiv.swap i last) ∈ Subgroup.closure (Set.range u) :=
      permAut_swap_mem_closure_spRefl u hu hi
    have hconj := ggSpSigned_conj_permAut_sgnAut p n (Equiv.swap i last) last
    rw [Equiv.swap_apply_right] at hconj
    have h2 : (permAut (Equiv.swap i last) * sgnAut last *
        (permAut (Equiv.swap i last))⁻¹) ∈ Subgroup.closure (Set.range u) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hu_last) (Subgroup.inv_mem _ hσ)
    rwa [hconj] at h2

theorem closure_spReflPerm_eq_bSignedFull {n p : ℕ}
    (u : Fin n → MulAut (Fin n → Multiplicative (ZMod p)))
    (hu : ∀ k f, u k f = SpJoin.spReflPerm n p k f) :
    Subgroup.closure (Set.range u) = bSignedFull n p := by
  rcases n with _ | m
  · apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨k, _⟩
      exact k.elim0
    · refine (Subgroup.closure_le _).mpr ?_
      rintro r (⟨i, _⟩ | ⟨a, _, _, _⟩)
      · exact i.elim0
      · exact a.elim0
  · apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨k, rfl⟩
      by_cases hk : k.val + 1 < m + 1
      · rw [spRefl_u_short u hu k hk]
        refine Subgroup.subset_closure (Or.inr ⟨k, ⟨k.val + 1, hk⟩, ?_, rfl⟩)
        exact fun h =>
          Nat.ne_of_lt (Nat.lt_succ_self k.val) (by simpa using congrArg Fin.val h)
      · rw [spRefl_u_long u hu k hk]
        exact Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)
    · refine (Subgroup.closure_le _).mpr ?_
      rintro r (⟨i, rfl⟩ | ⟨a, b, hab, rfl⟩)
      · exact sgnAut_mem_closure_spRefl u hu i
      · exact permAut_swap_mem_closure_spRefl u hu hab

theorem eq_sgnAut_or_swap_of_isRefl {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} (hu : u ∈ bSignedFull n p) (hu2 : u ^ 2 = 1)
    (hfix : Nat.card {f // u f = f} * p = Nat.card (Fin n → Multiplicative (ZMod p))) :
    (∃ i, u = sgnAut i) ∨ ∃ a b, a ≠ b ∧
      (u = permAut (Equiv.swap a b) ∨ u = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) := by
  have hsp : IsSignedPerm ⇑u := by
    rw [bSignedFull_eq_signedPermSubgroup n p] at hu
    change IsSignedPerm ⇑u at hu
    exact hu
  have hu2' : u * u = 1 := by simpa [sq] using hu2
  rcases RealKGSignedRefl.signedRefl_cases hp hp2 hsp hu2' hfix with ⟨i, hi⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨i, hi⟩
  · rcases x with ⟨⟨⟨a, b⟩, hab⟩, s⟩
    cases s with
    | false =>
      exact Or.inr ⟨a, b, ne_of_lt hab,
        Or.inl (by rw [hx, omPlusRefl_false (p := p) hab])⟩
    | true =>
      exact Or.inr ⟨a, b, ne_of_lt hab, Or.inr (by
        rw [hx, omPlusRefl_true (p := p) hab,
          ← OrthExcEven.sgnTransp_eq (ne_of_lt hab)])⟩

end CFSG.StandardType

end
