module

public import CFSG.Quasithin.Vol2.Ch11SecA02Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem false_of_concl701J4 (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (hM24c : Nat.card ↥NativeSporadic.M24 = 2 ^ 10 * 239085) (h : Hyp11 G T L I n)
    {X : Type} [Group X] {f : X →* ↥(autOn L (fsuV T I))} (hc : RecogCtx X _ n f)
    [IsMulCommutative ↥(fsuV T I)] (hJ : Concl701J4 T L I) : False := by
  obtain ⟨-, -, -, -, ⟨π, hπ⟩, -⟩ := hJ
  have hLB : L ≤ fsuM T L := by rw [fsuM_eq h]; exact Subgroup.le_normalizer
  have hBL : fsuM T L ≤ Subgroup.normalizer (L : Set G) := (fsuM_eq h).le
  have hsub : autOn L (fsuV T I) ≤ autOn (fsuM T L) (fsuV T I) :=
    Subgroup.map_mono fun _ hx => hLB hx
  have hne : ∃ y : ↥(autOn (fsuM T L) (fsuV T I)), y ≠ 1 := by
    obtain ⟨y, hy⟩ := hc.exists_ne_one
    refine ⟨⟨y, hsub y.2⟩, fun h1 => hy (Subtype.ext ?_)⟩
    exact congrArg (fun z : ↥(autOn (fsuM T L) (fsuV T I)) => (z : MulAut ↥(fsuV T I))) h1
  have hinj := @injective_of_isSimpleGroup _ _ _ _ hM24 π hπ.1 hne
  have hB : IsSimpleGroup ↥(autOn (fsuM T L) (fsuV T I)) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hM24 (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm
  have hcard : Nat.card ↥(autOn L (fsuV T I)) = 2 ^ 10 * 239085 := by
    rw [autOn_eq_of_isSimpleGroup hc hLB hBL hB,
      @card_eq_of_simple_quot _ _ _ _ hM24 π hπ.1 hne]
    exact hM24c
  exact hc.false_of_ten (by decide) hcard

theorem false_of_concl701Orth (h : Hyp11 G T L I n) {X : Type} [Group X]
    {f : X →* ↥(autOn L (fsuV T I))} (hc : RecogCtx X _ n f) [IsMulCommutative ↥(fsuV T I)]
    (hO : Concl701Orth T L I) : False := by
  obtain ⟨m, -, K, _, _, _, hK, π, hπ⟩ := hO
  have e := MulEquiv.subgroupCongr
    (show autOn (fsuL0 T L) (fsuV T I) = autOn L (fsuV T I) by rw [fsuL0_eq h])
  exact hc.false_of_SL2 hK (e.toMonoidHom.comp π) (e.surjective.comp hπ.1)

theorem not_concl701Four (h : Hyp11 G T L I n) : ¬ Concl701Four T L I := by
  rintro ⟨hlt, -⟩
  rw [fsuL0_eq h] at hlt
  exact lt_irrefl L hlt

theorem isFFModule_of_701 (h701 : Stmt7_0_1) (hM24 : IsSimpleGroup ↥NativeSporadic.M24)
    (hM24c : Nat.card ↥NativeSporadic.M24 = 2 ^ 10 * 239085) (hG2 : FactG2AdjointOrder)
    (h8 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n) :
    ∃ _ : IsMulCommutative ↥(fsuV T I), IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
  obtain ⟨hcomm, -, -, hcases⟩ := h701 G T L I h.fsu
  obtain ⟨f, hc⟩ := exists_recogCtx hG2 h8 h
  refine ⟨hcomm, ?_⟩
  rcases hcases with ⟨A, hA⟩ | hJ | hO | hF
  · have := isFFModule_of_offender hA
    rwa [fsuL0_eq h] at this
  · exact (false_of_concl701J4 hM24 hM24c h hc hJ).elim
  · exact (false_of_concl701Orth h hc hO).elim
  · exact (not_concl701Four h hF).elim

end CFSG.Quasithin.Vol2.Ch11.SecA
