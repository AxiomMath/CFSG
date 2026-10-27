module

public import CFSG.LocalAnalysis.StandardType.GGLangData

public section

namespace CFSG.StandardType

section Dict

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem ggPsiBar_injective (t : StatedLieTag) (n f : ℕ)
    (h : Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) = ⊥) :
    Function.Injective (ggPsiBar t n f) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := DFunLike.congr_fun hg x
    simp only [ggPsiBar, MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  rw [h] at hmem
  exact Subgroup.mem_bot.1 hmem

variable {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
  {Bs : Subgroup (GGAutU t n f)}
  {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
  {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
  {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}

theorem latChar_eq_zero_iff_rootChar_eq_one (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime)
    (b : Bs) (v : Fin (ggU (absTag t) 6 f).D.rank → ℤ) :
    latChar p (Multiplicative.toAdd (coord b)) v = 0 ↔
      rootChar (B.a b) (ggLangReidx B.rank_eq v) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hsum : ∀ (s : Finset (Fin (ggU (absTag t) 6 f).D.rank))
      (e : Fin (ggU (absTag t) 6 f).D.rank → ℤ), ∏ k ∈ s, B.ζ ^ e k = B.ζ ^ ∑ k ∈ s, e k := by
    intro s e
    refine Finset.induction_on s (by simp) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have hroot : rootChar (B.a b) (ggLangReidx B.rank_eq v) =
      B.ζ ^ ∑ k, ((ZMod.val (Multiplicative.toAdd (coord b) k) : ℕ) : ℤ) * v k := by
    show ∏ j, B.a b j ^ ggLangReidx B.rank_eq v j = _
    simp_rw [B.a_coord, ← zpow_natCast, ← zpow_mul]
    rw [← hsum]
    exact Fintype.prod_equiv (finCongr B.rank_eq.symm) _ _ fun j => by simp [ggLangReidx]
  have hcast : ((∑ k, ((ZMod.val (Multiplicative.toAdd (coord b) k) : ℕ) : ℤ) * v k : ℤ) :
      ZMod p) = latChar p (Multiplicative.toAdd (coord b)) v := by
    simp only [latChar, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hroot, ← orderOf_dvd_iff_zpow_eq_one, B.ζ_order, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast]

end Dict

end CFSG.StandardType
