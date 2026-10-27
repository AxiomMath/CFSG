module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515bMain

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem main_one (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r)
    {z' : G} (hz'2 : z' * z' = 1) (h3 : z' • T.line.vert (a + 3) = T.line.vert (a + 3))
    (h4 : z' • T.line.vert (a + 4) = T.line.vert (a + 4))
    (hm : z' • T.line.vert (a + 2) ≠ T.line.vert (a + 2))
    (hzb : z ∈ ballStab Γ G 2 (T.line.vert (a + 3))) {k : ℕ} (hk : 3 ≤ k)
    (hC : ∀ g : G, g * fcomm z z' = fcomm z z' * g →
      g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + k)) →
        g ∈ MulAction.stabilizer G (T.line.vert (a + 1 + k + 1)))
    (hns : ¬ RightSingular Γ G (T.line.arc (a + 1) k).vert 0 k)
    {y : G} (hy : y ∈ Arc.GcircL G (T.line.arc (a + 3) (k - 1))) :
    y * fcomm z z' = fcomm z z' * y := by
  obtain ⟨αs, α's, d, zz, -, hzzv, B⟩ := mkBlk F C h3 hzb
  have hz2 : z * z = 1 := C.cinv.2.1
  have hu : fcomm z z' = z * zz := by rw [hzzv]; exact fcomm_eq hz2 hz'2
  rw [hu] at hC ⊢
  by_contra hyu
  set δ := T.line.vert (a + 3) with hδ
  set β := T.line.vert (a + 2) with hβ
  have hδ4 : Γ.Adj δ (T.line.vert (a + 4)) := by
    have := T.line.adj (a + 3)
    rwa [show a + 3 + 1 = a + 4 by ring] at this
  have hδβ : Γ.Adj δ β := (adj_a23 T a).symm
  have hβ4 : β ≠ T.line.vert (a + 4) := by
    have := T.line.nb (a + 2)
    rwa [show a + 2 + 2 = a + 4 by ring] at this
  have hδβ' : Γ.Adj δ (z' • β) := by
    have := (F.adj_smul z' β δ).2 (adj_a23 T a)
    rw [h3] at this
    exact this.symm
  obtain ⟨x, hxfix, hxmove⟩ := T.line.exists_fixer_right' (a + 1) k 0 k (by omega) hns
  have hxf : ∀ m : ℤ, a + 1 ≤ m → m ≤ a + 1 + k → x • T.line.vert m = T.line.vert m :=
    fun m h1 h2 => hxfix m (by simpa using h1) h2
  have hxδ : x • δ = δ := hxf (a + 3) (by omega) (by omega)
  have hxβ : x • β = β := hxf (a + 2) (by omega) (by omega)
  have hx4 : x • T.line.vert (a + 4) = T.line.vert (a + 4) := hxf (a + 4) (by omega) (by omega)
  have hxK : x ∈ nbrStab Γ G δ := F.fix_two_nbrs hδβ hδ4 hβ4 hxβ hx4
  have hxβ' : x • (z' • β) = z' • β := mem_nbrStab.1 hxK _ hδβ'
  have hyf : ∀ m : ℕ, m ≤ k - 1 → y • T.line.vert (a + 3 + m) = T.line.vert (a + 3 + m) :=
    fun m hm => (Arc.mem_stab G).1 hy.1 m hm
  have hyδ : y • δ = δ := by simpa using hyf 0 (by omega)
  have hy4 : y • T.line.vert (a + 4) = T.line.vert (a + 4) := by
    have := hyf 1 (by omega)
    rwa [show a + 3 + ((1 : ℕ) : ℤ) = a + 4 by norm_num; ring] at this
  have hγ0 : (T.line.arc (a + 3) (k - 1)).vert 0 = δ := by simp [Line.arc, hδ]
  have hγ1 : (T.line.arc (a + 3) (k - 1)).vert 1 = T.line.vert (a + 4) := by
    show T.line.vert (a + 3 + ((1 : ℕ) : ℤ)) = _
    congr 1
    push_cast
    ring
  have hyy : y * y ∈ nbrStab Γ G δ := by
    refine mem_nbrStab.2 fun w hw => ?_
    by_cases hw4 : w = T.line.vert (a + 4)
    · rw [hw4, mul_smul, hy4, hy4]
    · refine mem_fixSet.1 hy.2 w ?_
      show w ∈ Γ.neighborSet ((T.line.arc (a + 3) (k - 1)).vert 0) \
        {(T.line.arc (a + 3) (k - 1)).vert 1}
      rw [hγ0, hγ1]
      exact ⟨hw, hw4⟩
  have hz'K : z' ∉ nbrStab Γ G δ := fun h => hm (mem_nbrStab.1 h β hδβ)
  have hz'e : z' ∈ MulAction.stabilizer G δ ⊓ MulAction.stabilizer G (T.line.vert (a + 4)) :=
    ⟨MulAction.mem_stabilizer_iff.2 h3, MulAction.mem_stabilizer_iff.2 h4⟩
  have hye : y ∈ MulAction.stabilizer G δ ⊓ MulAction.stabilizer G (T.line.vert (a + 4)) :=
    ⟨MulAction.mem_stabilizer_iff.2 hyδ, MulAction.mem_stabilizer_iff.2 hy4⟩
  have hyblk : (y • β = β ∧ y • (z' • β) = z' • β) ∨ (y • β = z' • β ∧ y • (z' • β) = β) := by
    by_cases hyK : y ∈ nbrStab Γ G δ
    · exact Or.inl ⟨mem_nbrStab.1 hyK β hδβ, mem_nbrStab.1 hyK _ hδβ'⟩
    · have hzy := mul_mem_nbrStab_of_sq_mem F hδ4 hz'e hye hz'2 hyy hz'K hyK
      have e1 := mem_nbrStab.1 hzy β hδβ
      have e2 := mem_nbrStab.1 hzy (z' • β) hδβ'
      rw [mul_smul] at e1 e2
      have back : ∀ w : V, z' • z' • w = w := fun w => by rw [smul_smul, hz'2, one_smul]
      refine Or.inr ⟨?_, MulAction.injective z' e2⟩
      have := congrArg (fun w => z' • w) e1
      simpa [back] using this
  have hxu : x * (z * zz) ≠ (z * zz) * x := fun h =>
    hxmove (MulAction.mem_stabilizer_iff.1 (hC x h (MulAction.mem_stabilizer_iff.2
      (hxf _ (by omega) le_rfl))))
  have hxyc := final F B hxδ hyδ (Or.inl ⟨hxβ, hxβ'⟩) hyblk hxu hyu
  have hyk : y • T.line.vert (a + 1 + k) = T.line.vert (a + 1 + k) := by
    have := hyf (k - 2) (by omega)
    rwa [show a + 3 + ((k - 2 : ℕ) : ℤ) = a + 1 + k by omega] at this
  have hyk1 : y • T.line.vert (a + 1 + k + 1) = T.line.vert (a + 1 + k + 1) := by
    have := hyf (k - 1) le_rfl
    rwa [show a + 3 + ((k - 1 : ℕ) : ℤ) = a + 1 + k + 1 by omega] at this
  have hmem : x * y ∈ MulAction.stabilizer G (T.line.vert (a + 1 + k)) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hyk]
    exact hxf _ (by omega) le_rfl
  have hfin := MulAction.mem_stabilizer_iff.1 (hC (x * y) hxyc hmem)
  rw [mul_smul, hyk1] at hfin
  exact hxmove hfin

theorem fan515b_of (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h515a : Fan515a F) : Fan515b F := by
  intro h40 T z z' a tL tR a' b' tL' tR' hXi hz hz1 hc hz'ZZ hpos hval hr k hk hC hns g hg
  obtain ⟨-, -, C⟩ := mkCtx F h513b h510 h511 h512cen h512b h40 T z a tL tR hXi hz hz1 hc hval hr
  obtain ⟨i, j, hi, hj, hiR, hjL⟩ := hpos.pos
  have hz'2 : z' * z' = 1 := hz'ZZ.1
  have hfx := hpos.right.fix
  have hab : a' < b' := hpos.right.core.1
  have hfa := (hfx a').1 (hpos.right.core.2.1 a' le_rfl hab.le)
  have hfb := (hfx b').1 (hpos.right.core.2.1 b' hab.le le_rfl)
  have fixz' : ∀ m, tL' ≤ m → m ≤ tR' → z' • T.line.vert m = T.line.vert m :=
    fun m h1 h2 => (hfx m).2 ⟨h1, h2⟩
  have movez' : ∀ m, m < tL' → z' • T.line.vert m ≠ T.line.vert m := fun m h1 h => by
    have := (hfx m).1 h
    omega
  rcases hj with rfl | rfl
  · have hu : fcomm z z' = lab T z 1 := main_zero F C hz'2 (fixz' (a + 2) (by omega) (by omega))
      (fixz' (a + 3) (by omega) (by omega)) (movez' (a + 1) (by omega))
    rw [hu]
    have hg0 : g • T.line.vert (a + 3) = T.line.vert (a + 3) := by
      have := (Arc.mem_stab G).1 hg.1 0 (Nat.zero_le _)
      simpa [Line.arc] using this
    exact (lab_one_cinv F C).2.2.2 g (MulAction.mem_stabilizer_iff.2 hg0)
  · have hzb : z ∈ ballStab Γ G 2 (T.line.vert (a + 3)) := by
      have h := (h515a h40 T z a tL tR hXi hz hz1 hc hval hr 1 1 (by norm_num) (by omega)).2
      rw [sub_self, show a + 1 + 2 * 1 = a + 3 by ring] at h
      simpa using h
    exact main_one F C hz'2 (fixz' (a + 3) (by omega) (by omega))
      (fixz' (a + 4) (by omega) (by omega)) (movez' (a + 2) (by omega)) hzb hk hC hns hg

end P515

theorem fan_5_15b {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (F : FanTree Γ G) (h513b : Fan513b F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h515a : Fan515a F) : Fan515b F :=
  P515.fan515b_of F h513b h510 h511 h512cen h512b h515a

end CFSG.Quasithin.Fan86
