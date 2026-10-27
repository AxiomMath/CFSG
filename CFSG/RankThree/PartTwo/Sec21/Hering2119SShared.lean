module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SA
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SStep2
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SNA

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

theorem item2119EndStep2Pair_holds : Item2119EndStep2Pair := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX h28 hL e₀ he₀ he₀d e₁ he₁
    he₁d P₀ P₁ hP₀ hP₁ hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he₁d' : e₁ ∉ Subgroup.zpowers d := fun h => he₁d (Subgroup.mem_sup_right h)
  have hL₀ := hL e₀ he₀ he₀d P₀ hP₀
  have hL₁ := hL e₁ he₁ he₁d' P₁ hP₁
  have h₀ := Hering2119S.lineAbs_of_config hE hLf h26 hF h27 hQ hQX h28 he₀ he₀d hL₀
  have h₁' := Hering2119S.lineAbs_of_config hE hLf h26 hF h27 hQ hQX h28 he₁ he₁d' hL₁
  have h₁ : Hering2119S.LineAbs (CFSG.Open.thompsonSubgroup P₀) (F e₁ ⊓ Lf e₁)
      (y2128Of (Lf e₁) (F e₁) (q2127Of A d F)) e₁ := by
    rw [hJ]; exact h₁'
  obtain ⟨hDe, hD81, -, -⟩ := hL₀
  set Q := q2127Of A d F with hQdef
  have hDc : ∀ x ∈ CFSG.Open.thompsonSubgroup P₀, ∀ y ∈ CFSG.Open.thompsonSubgroup P₀,
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hD : Hering2119S.IsElem3 (CFSG.Open.thompsonSubgroup P₀) := ⟨hDc, fun x hx => hDe.2 x hx⟩
  have hD3 : IsPGroup 3 (CFSG.Open.thompsonSubgroup P₀) :=
    Item2119End8Proof.isPGroup_of_pow hDe.2
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hA27 : Nat.card A = 27 := by rw [hE.cfg.card]; norm_num
  have hAFQ : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ⊔ F b ≤ Q := fun b hb hbd =>
    le_iSup₂_of_le (f := fun e (_ : e ∈ {e : G | e ∈ A ∧ e ∉ Subgroup.zpowers d}) => A ⊔ F e)
      b ⟨hb, hbd⟩ le_rfl
  have hAY : ∀ b ∈ A, b ∉ Subgroup.zpowers d → A ≤ y2128Of (Lf b) (F b) Q := fun b hb hbd =>
    le_sup_left.trans ((hAFQ b hb hbd).trans le_sup_right)
  have hind : ∀ j : ℕ, e₁ * (e₀ ^ j)⁻¹ ∉
      Subgroup.centralizer (CFSG.Open.thompsonSubgroup P₀ : Set G) := by
    intro j hz
    have hzA : e₁ * (e₀ ^ j)⁻¹ ∈ A := A.mul_mem he₁ (A.inv_mem (A.pow_mem he₀ j))
    by_cases hzd : e₁ * (e₀ ^ j)⁻¹ ∈ Subgroup.zpowers d
    · apply he₁d
      have : e₁ = (e₁ * (e₀ ^ j)⁻¹) * e₀ ^ j := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzd)
        (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers e₀)) j)
    · have h27' := Item2119End8Proof.card_le_27_of_le_centralizer h27 hQ hA27 hzA hzd hD3 hDc
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hz x hx))
      rw [hD81] at h27'
      norm_num at h27'
  obtain ⟨T, a₁, b₁, c₁, t, hT⟩ := Hering2119S.step2_abs hD hD81 h₀ h₁
    (hAY e₀ he₀ he₀d he₁) (hAY e₁ he₁ he₁d' he₀) hind
  exact ⟨T, a₁, b₁, c₁, t, hT⟩

theorem item2119EndSharedA_holds : Item2119EndSharedA :=
  item2119EndSharedA_of_step2 item2119EndStep2Pair_holds

theorem item2119EndShared_holds : Item2119EndShared :=
  item2119EndShared_of_branches item2119EndSharedNA_holds item2119EndSharedA_holds

theorem item2119EndLoc_of_share_holds (h1 : Item2119EndShare) : Item2119EndLoc :=
  item2119EndLoc_of_share h1 item2119EndShared_holds

end CFSG.RankThree.PartTwo.Sec21
