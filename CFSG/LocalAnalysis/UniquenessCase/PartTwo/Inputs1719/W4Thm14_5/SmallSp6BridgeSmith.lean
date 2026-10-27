module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeFactors
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open CFSG.Open CFSG.Quasithin.SmithCurtis Module Representation

variable {K k V : Type} [Field K] [Finite K] [CharP K 2] [Field k] [CharP k 2]
  [AddCommGroup V] [Module k V] [Module.Finite k V]

theorem root_normalizes_Us (i : Fin 3) {m x : StatedSp 3 K}
    (hm : m ∈ (spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i)
    (hx : x ∈ (spCurtisDatum 3 K).Us i) :
    m * x * m⁻¹ ∈ (spCurtisDatum 3 K).Us i :=
  conj_mem_of_sup ((spCurtisDatum 3 K).X_normUs i)
    (fun _ hy _ hx => curtisDatum_Y_normUs (spCurtisDatum 3 K) i hy hx) hm hx

omit [CharP k 2] [Module.Finite k V] in
theorem apply_mem_fixSub_Us (ρ : Representation k (StatedSp 3 K) V) (i : Fin 3)
    {m : StatedSp 3 K} (hm : m ∈ (spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i)
    {v : V} (hv : v ∈ fixSub ρ ((spCurtisDatum 3 K).Us i)) :
    ρ m v ∈ fixSub ρ ((spCurtisDatum 3 K).Us i) := by
  rw [mem_fixSub] at hv ⊢
  intro x hx
  have hx' := root_normalizes_Us i (inv_mem hm) hx
  rw [inv_inv] at hx'
  calc
    ρ x (ρ m v) = ρ m (ρ (m⁻¹ * x * m) v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    _ = ρ m v := by rw [hv _ hx']

theorem finrank_fixSub_Us_le_of_factors
    (ρ : Representation k (StatedSp 3 K) V) (hsimp : IsSimpleRep ρ)
    (hsplit : SplitOver k (spCurtisDatum 3 K).H) (i : Fin 3)
    (hfac : FactorsFinrankLe (ρ.comp
      ((spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i).subtype) 2) :
    finrank k (fixSub ρ ((spCurtisDatum 3 K).Us i)) ≤ 2 := by
  classical
  let C := fixSub ρ ((spCurtisDatum 3 K).Us i)
  let R := (spCurtisDatum 3 K).X i ⊔ (spCurtisDatum 3 K).Y i
  let τ : Representation k R C :=
    restrictRep (ρ.comp R.subtype) C (fun m _ hv => apply_mem_fixSub_Us ρ i m.2 hv)
  by_cases hC : C = ⊥
  · change finrank k C ≤ 2
    rw [hC]
    simp
  have : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hC
  have hτ : τ.IsIrreducible := by
    apply (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff τ).mpr
    refine ⟨inferInstance, fun T hT => ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let T' := T.map C.subtype
    have hT'C : T' ≤ C := by
      rintro _ ⟨w, _, rfl⟩
      exact w.2
    have hT' : ∀ m ∈ R, ∀ v ∈ T', ρ m v ∈ T' := by
      rintro m hm v ⟨w, hw, rfl⟩
      exact ⟨τ ⟨m, hm⟩ w, hT ⟨m, hm⟩ w hw, rfl⟩
    rcases fixSub_Us_eq_bot_or_eq (spCurtisDatum 3 K) hsplit hsimp i hT'C hT' with h | h
    · left
      have hm : (T.map C.subtype).comap C.subtype = T :=
        Submodule.comap_map_eq_self (by rw [Submodule.ker_subtype]; exact bot_le)
      change T.map C.subtype = ⊥ at h
      rw [h, Submodule.comap_bot, Submodule.ker_subtype] at hm
      exact hm.symm
    · right
      have hm : (T.map C.subtype).comap C.subtype = T :=
        Submodule.comap_map_eq_self (by rw [Submodule.ker_subtype]; exact bot_le)
      change T.map C.subtype = C at h
      rw [h, Submodule.comap_subtype_self] at hm
      exact hm.symm
  let f : IntertwiningMap τ (ρ.comp R.subtype) := ⟨C.subtype, fun _ => rfl⟩
  have hτfac := factorsFinrankLe_of_injective f C.injective_subtype hfac
  exact finrank_le_of_factorsFinrankLe τ hτ hτfac

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
