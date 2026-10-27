module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic Matrix

namespace AutPSp

variable {n : ℕ} {K : Type} [Field K]

theorem formJ_alt (v : Fin n ⊕ Fin n → K) : v ⬝ᵥ (formJ n K *ᵥ v) = 0 := by
  simp only [formJ, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  simp [Matrix.neg_mulVec, mul_comm]

theorem formJ_det : (formJ n K).det ≠ 0 := by
  have h : formJ n K * (-formJ n K) = 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [formJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

theorem center_eq_bot [CharP K 2] [NeZero n] : Subgroup.center (StatedSp n K) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq n K]
  exact spScalars_eq_bot

theorem four_le_of_bstar [Finite K] [CharP K 2] {G : Type*} [Group G] (hn : 2 ≤ n)
    (ψ : StatedSp n K →* G) (hker : ψ.ker ≤ Subgroup.center (StatedSp n K))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBsE : CFSG.Assembly.IsElemAbelian p Bs) (hcard : p ^ 4 ≤ Nat.card Bs)
    (hBsI : ∀ b ∈ Bs, GGPsiInnerDiag (rootDatum n K) ψ b) : 4 ≤ n := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hle : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Symp.exists_mem_centralizer hn ψ hker (hBsI b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (le_of_eq center_eq_bot)
  set E := Bs.comap ψ
  have hcardE : Nat.card E = Nat.card Bs := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
  set F := E.map (StatedSp n K).subtype
  have hcardF : Nat.card F = Nat.card E :=
    Subgroup.card_map_of_injective (StatedSp n K).subtype_injective
  have hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := hBsE.1.is_comm.comm ⟨ψ a, ha⟩ ⟨ψ b, hb⟩
    have h' : ψ (a * b) = ψ (b * a) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h
    rw [← map_mul, ← map_mul, hinj h']
  have hexp : ∀ x ∈ F, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h : ψ (a ^ p) = ψ 1 := by
      rw [map_pow, map_one]
      exact hBsE.2 _ ha
    rw [← map_pow, hinj h, map_one]
  have hpK : (p : K) ≠ 0 := CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2
  have hb := CFSG.RankThree.PartOne.LIT.card_le_pow_half_of_form_gl hp hpK (formJ n K) formJ_det
    formJ_alt F hcomm hexp (by
      rintro _ ⟨a, -, rfl⟩
      exact SymplecticTorusWeyl.mem_statedSp_iff.mp a.2)
  rw [Fintype.card_sum, Fintype.card_fin, ← two_mul, Nat.mul_div_cancel_left _ two_pos, hcardF,
    hcardE] at hb
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hb)

end AutPSp

end CFSG.StandardType
