module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4TensorFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81

theorem s16t_l4_fst_eq_one_of_simple {X : Type*} [Group X] {H : Type*} [Group H]
    {Mb Lb : Subgroup X} (hLM : Lb ≤ Mb) (φ : ↥Mb ≃* (Equiv.Perm (Fin 3) × H))
    (hLs : IsSimpleGroup ↥Lb) (hLc : 6 < Nat.card ↥Lb) {l : ↥Mb} (hl : (l : X) ∈ Lb) :
    (φ l).1 = 1 := by
  let f : ↥Lb →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst (Equiv.Perm (Fin 3)) H).comp (φ.toMonoidHom.comp (Subgroup.inclusion hLM))
  have hk : f.ker = ⊤ := by
    rcases hLs.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exfalso
      have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h
      have h6 : Nat.card ↥Lb ≤ Nat.card (Equiv.Perm (Fin 3)) :=
        Nat.card_le_card_of_injective f hinj
      have h6' : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        rfl
      omega
    · exact h
  have hmem : (⟨l, hl⟩ : ↥Lb) ∈ f.ker := by
    rw [hk]
    exact Subgroup.mem_top _
  exact hmem

theorem s16t_l4_tensor_dichotomy {W : Type} [CommGroup W] [Finite W]
    {Mb Kb Lb : Subgroup (MulAut W)} (hK : IsSym ↥Kb 3) (hL : IsLn ↥Lb 4 1)
    (hLs : IsSimpleGroup ↥Lb) (hLc : 6 < Nat.card ↥Lb) (hdir : IsInternalDirect Kb Lb Mb)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 4 1) Lb ⊤ ⊥ 2) {w : W} (hw : w ≠ 1) :
    (∃ E : Subgroup (MulAut W), E ≤ Mb ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
        ∀ e ∈ E, (e : MulAut W) w = w) ∨
      ∃ τ ∈ Mb, τ ≠ 1 ∧ (∀ l ∈ Lb, τ * l = l * τ) ∧ (τ : MulAut W) w = w := by
  have hT : IsTensorS3L2 W Mb 4 :=
    s16c1610_isTensorS3L2_of_sum_natural (by norm_num) hK hL hdir hsum
  have hLM : Lb ≤ Mb := le_sup_right.trans hdir.2.2.le
  obtain ⟨φ, hE | ⟨τ, hτ1, hτw, hτ2⟩⟩ := s16t_l4_tensor_fix_or_pure hT hw
  · exact Or.inl hE
  · refine Or.inr ⟨(τ : MulAut W), τ.2, fun h => hτ1 (Subtype.ext h), ?_, hτw⟩
    intro l hl
    have h1 : (φ ⟨l, hLM hl⟩).1 = 1 :=
      s16t_l4_fst_eq_one_of_simple hLM φ hLs hLc (l := ⟨l, hLM hl⟩) hl
    have h2 : τ * ⟨l, hLM hl⟩ = ⟨l, hLM hl⟩ * τ := by
      apply φ.injective
      refine Prod.ext ?_ ?_
      · simp [h1]
      · simp [hτ2]
    exact congrArg Subtype.val h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
