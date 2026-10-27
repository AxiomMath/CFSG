module

public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.RankThree.PartOne.CTP.SpEdge
public import CFSG.RankThree.PartOne.CTP.SpSwap
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieAdmissible StatedSp StatedProj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (projSpEquiv)
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Linear

theorem exists_linearBlockStandardPair {G : Type} [Group G] {f p : ℕ} (hf : 2 ≤ f)
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hA : StatedClassicalModel A .PSL 2 2 f)
    (hB : StatedClassicalModel B .PSL 2 2 f) (hAB : CentrallyLThree f ↥(A ⊔ B)) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2 ^ f) : ∃ W, LinearBlockStandardPair F W A B := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  obtain ⟨L, _, _, hL, θ₀, hsurj, hker₀⟩ := exists_sl3_surj_of_centrallyL3 hAB
  obtain ⟨Li, _, _, _, hLi, ⟨ρi⟩⟩ := exists_sl2_equiv_of_model hA
  obtain ⟨Lj, _, _, _, hLj, ⟨ρj⟩⟩ := exists_sl2_equiv_of_model hB
  have : CharP L 2 := charP_two_of_card_eq_two_pow hL
  let θ : SL(3, L) →* G := (A ⊔ B).subtype.comp θ₀
  have hrange : θ.range = A ⊔ B := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hker : θ.ker ≤ Subgroup.center SL(3, L) := by
    intro x hx
    exact hker₀ (Subtype.ext hx)
  obtain ⟨c, hc1, hc2⟩ := linear_edge_standardPair θ hker (by rw [hL]; exact hq4) hp hp2
    (by rw [hL]; exact hpq) hE hrange.symm (by rw [hLi, hL]) (by rw [hLj, hL]) ρi ρj
  have hLB : LinearBlockStandardPair L (A ⊔ B) A B :=
    ⟨θ, c, hrange, hker, Or.inl ⟨hc1, hc2⟩⟩
  obtain ⟨e⟩ := exists_ringEquiv_of_card_eq (K := L) (K' := F) (by rw [hL, hF])
  exact ⟨A ⊔ B, hLB.of_ringEquiv e⟩

end Linear

theorem extCurtisTitsCThreeSp : ExtCurtisTitsCThreeSp := by
  intro G _ _ f p K₁ K₂ K₃ E hf hp hpq hE hgen h₁ h₂ h₃ hcomm₁₃ hL3 hSp htor
  obtain ⟨hadm2, F, _, _, hF, ⟨e⟩⟩ := hSp
  have : CharP F 2 := charP_two_of_card_eq_two_pow hF
  have hq4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  let ψ : StatedSp 2 F ≃* ↥(K₂ ⊔ K₃) := (projSpEquiv F).trans e.symm
  let θ : StatedSp 2 F →* G := (K₂ ⊔ K₃).subtype.comp ψ.toMonoidHom
  have hθrange : θ.range = K₂ ⊔ K₃ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hθker : θ.ker ≤ Subgroup.center (StatedSp 2 F) := by
    have hθinj : Function.Injective θ := (Subgroup.subtype_injective _).comp ψ.injective
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθinj]
    exact bot_le
  have hE₂₃ : EdgeTorus p E K₂ K₃ :=
    ⟨(htor.1 1).1, (htor.1 1).2, (htor.1 2).1, (htor.1 2).2, htor.2 1 2 (by decide)⟩
  have hE₁₂ : EdgeTorus p E K₁ K₂ :=
    ⟨(htor.1 0).1, (htor.1 0).2, (htor.1 1).1, (htor.1 1).2, htor.2 0 1 (by decide)⟩
  obtain ⟨L₂, _, _, _, hL₂, ⟨ρ₂⟩⟩ := exists_sl2_equiv_of_model h₂
  obtain ⟨L₃, _, _, _, hL₃, ⟨ρ₃⟩⟩ := exists_sl2_equiv_of_model h₃
  have hsp : ∃ W, SymplecticBlockStandardPair F W K₃ K₂ := by
    refine ⟨K₃ ⊔ K₂, ?_⟩
    rcases sp_edge_pair_cases (K := F) hf hF θ hθker hp hpq hE₂₃.symm
      (by rw [sup_comm, hθrange]) hL₃ hL₂ ρ₃ ρ₂ with h | h
    · exact h
    · exact symplecticBlockStandardPair_swap h
  have hpair : ∃ W, LinearBlockStandardPair F W K₁ K₂ :=
    exists_linearBlockStandardPair hf hp hpq hE₁₂ h₁ h₂ hL3 hF
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, by omega, by omega, by simp⟩
  have hgen' : (⨆ k : Fin 3, (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) = ⊤ := by
    rw [← hgen]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · fin_cases k
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 0)
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 1))
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 2)
  obtain ⟨Ψ, hsurj, hker, -⟩ := weakCT_symplectic_even (n := 3) (f := f) hadm le_rfl hF hq4
    (U := ![K₁, K₂, K₃]) hgen'
    (fun i j hij a ha b hb => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact (Subgroup.mem_centralizer_iff.mp (hcomm₁₃.1 ha) b hb).symm)
    (fun i j hij hj => by
      fin_cases i <;> fin_cases j <;> simp at hij hj
      exact hpair)
    (fun i j hi hj => by
      fin_cases i <;> fin_cases j <;> simp at hi hj
      exact hsp)
  have hcenter : Subgroup.center (StatedSp 3 F) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hcenter.le
  have hπ := UnitaryHigher.proj_bijective_of_charTwo (r := 3) (K := F)
  exact ⟨hadm, F, inferInstance, inferInstance, hF,
    ⟨(MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm.trans (MulEquiv.ofBijective (proj 3 F) hπ)⟩⟩

end CFSG.RankThree.PartOne.CTP
