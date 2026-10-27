module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNormA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNormB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNormC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem s16t_a_exists_fixed_of_norm {T : Type} [CommGroup T] [Finite T]
    (hT : ∀ v : T, v ^ 2 = 1) {ι : Type} [Fintype ι] (hι : Fintype.card ι = 3)
    {Y : ι → Subgroup T} (hinj : Function.Injective Y) (hind : iSupIndep Y)
    (hY : ∀ i, Y i ≠ ⊥) {Λ B : Subgroup (MulAut T)} (hΛ : IsElemAbelianOfRank 3 2 ↥Λ)
    (hB : IsPGroup 2 ↥B) (hΛperm : ∀ f ∈ Λ, ∀ i, ∃ j, (Y i).map f.toMonoidHom = Y j)
    (hBperm : ∀ b ∈ B, ∀ i, ∃ j, (Y i).map b.toMonoidHom = Y j)
    (hBΛ : ∀ b ∈ B, ∀ f ∈ Λ, b * f * b⁻¹ ∈ Λ)
    (hmove : ∃ f ∈ Λ, ∃ i, (Y i).map f.toMonoidHom ≠ Y i) :
    ∃ a ∈ Λ, orderOf a = 3 ∧ ∃ n : T, n ≠ 1 ∧ a n = n ∧ ∀ b ∈ B, b n = n := by
  classical
  have hsmul : ∀ (x : MulAut T) (I : Subgroup T), x • I = I.map x.toMonoidHom := by
    intro x I
    have hf : MulDistribMulAction.toMonoidEnd _ _ x = x.toMonoidHom := by
      ext y
      rfl
    rw [Subgroup.pointwise_smul_def, hf]
  let Λ₀ : Subgroup (MulAut T) := Λ ⊓ ⨅ i, MulAction.stabilizer (MulAut T) (Y i)
  have hΛ₀ : ∀ f, f ∈ Λ₀ ↔ f ∈ Λ ∧ ∀ i, (Y i).map f.toMonoidHom = Y i := by
    intro f
    simp only [Λ₀, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hsmul]
  obtain ⟨hcard₀, hmove'⟩ := s16t_a_card_stab_all hι hinj hΛ hΛperm hmove hΛ₀
  have hBΛ₀ : ∀ b ∈ B, ∀ f ∈ Λ₀, b * f * b⁻¹ ∈ Λ₀ := by
    intro b hb f hf
    obtain ⟨hfΛ, hfY⟩ := (hΛ₀ f).1 hf
    refine (hΛ₀ _).2 ⟨hBΛ b hb f hfΛ, fun i => ?_⟩
    obtain ⟨j, hj⟩ := hBperm b⁻¹ (B.inv_mem hb) i
    have h1 : (Y i).map (b * f * b⁻¹).toMonoidHom = (((Y i).map b⁻¹.toMonoidHom).map
        f.toMonoidHom).map b.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have h2 : (Y j).map b.toMonoidHom = Y i := by
      rw [← hj, Subgroup.map_map]
      have h3 : b.toMonoidHom.comp b⁻¹.toMonoidHom = MonoidHom.id T := by
        ext x
        simp
      rw [h3, Subgroup.map_id]
    rw [h1, hj, hfY j, h2]
  obtain ⟨a, haΛ, haΛ₀, hao, hBa⟩ := s16t_a_exists_stable_line hΛ (fun f hf => ((hΛ₀ f).1 hf).1)
    hcard₀ hB hBΛ hBΛ₀
  obtain ⟨n, hn1, han, hBn⟩ := s16t_a_exists_fixed_vector hT hι hind hY
    (by rw [← hao]; exact pow_orderOf_eq_one a) (hΛperm a haΛ) (hmove' a haΛ haΛ₀) hB hBa
  exact ⟨a, haΛ, hao, n, hn1, han, hBn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
