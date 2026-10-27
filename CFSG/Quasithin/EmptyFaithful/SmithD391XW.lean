module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918N2
public import CFSG.Quasithin.Background.F918N6
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section Abstract

variable {X : Type} [CommGroup X] [Finite X] {Mb Tb Lb : Subgroup (MulAut X)} {Vb : Subgroup X}

theorem z35_split_sum (h : Z35 Mb Tb Lb Vb) {t : MulAut X} (htT : t ∈ Tb)
    (hsplit : ∀ s ∈ Tb, s ∈ stabSub Vb ∨ t⁻¹ * s ∈ stabSub Vb) :
    t ∉ stabSub Vb ∧ Vb ⊔ Vb.map t.toMonoidHom = ⊤ ∧ Vb ⊓ Vb.map t.toMonoidHom = ⊥ ∧
      ¬ XMod.Iso ↥Mb (Vb.map t.toMonoidHom) Vb := by
  have htn : t ∉ stabSub Vb := by
    intro ht
    apply z35_not_le_stab h
    intro s hs
    rcases hsplit s hs with h1 | h1
    · exact h1
    · have := (stabSub Vb).mul_mem ht h1
      rwa [mul_inv_cancel_left] at this
  have hmapt : Vb.map t.toMonoidHom ≠ Vb := fun he => htn (mem_stabSub_iff_map_eq.2 he)
  have hsum : Vb ⊔ Vb.map t.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← h.gen]
    refine iSup₂_le fun s hs => ?_
    rcases hsplit s hs with h1 | h1
    · rw [mem_stabSub_iff_map_eq.1 h1]
      exact le_sup_left
    · rw [show s = t * (t⁻¹ * s) by group, map_mul_aut', mem_stabSub_iff_map_eq.1 h1]
      exact le_sup_right
  have hinf : Vb ⊓ Vb.map t.toMonoidHom = ⊥ := by
    have hmem1 : Vb ∈ {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} :=
      ⟨1, Tb.one_mem, (n6_map_one Vb).symm⟩
    have hmem2 : Vb.map t.toMonoidHom ∈
        {S : Subgroup X | ∃ t ∈ Tb, S = Vb.map t.toMonoidHom} := ⟨t, htT, rfl⟩
    have hd := h.indep.pairwiseDisjoint hmem1 hmem2 hmapt.symm
    exact disjoint_iff.1 hd
  refine ⟨htn, hsum, hinf, fun hiso => ?_⟩
  have h1 := h.homog t htT 1 Tb.one_mem (by rw [n6_map_one]; exact hiso)
  rw [n6_map_one] at h1
  exact hmapt h1

theorem isFFModule_of_rkIdx_le (hX : ∀ x : X, x ^ 2 = 1) {G A : Subgroup (MulAut X)}
    (hA : IsA2 G A) (h : rkIdx (fixV A) ≤ rk ↥A) : IsFFModule G := by
  refine (isFFModule_iff hX).2 ⟨A, hA, ?_⟩
  unfold rAV
  rw [div_le_one (by exact_mod_cast hA.rk_pos)]
  exact_mod_cast h

end Abstract

section Transfer

variable {W : Type} [CommGroup W] {T : Subgroup (MulAut W)} {V VT C : Subgroup W}

theorem n2Rho_mem_stabSub (g : ↥(stabSub VT ⊓ stabSub C)) (hg : (g : MulAut W) ∈ stabSub V) :
    n2Rho VT C g ∈ stabSub (sec35Img VT C V) := by
  rw [mem_stabSub_iff_map_eq, n2_map_rho_sec35Img, mem_stabSub_iff_map_eq.1 hg]

theorem split_autSec (hT : T ≤ stabSub VT ⊓ stabSub C) {t : MulAut W} (htT : t ∈ T)
    (hsplit : ∀ s ∈ T, s ∈ stabSub V ∨ t⁻¹ * s ∈ stabSub V) :
    n2Rho VT C ⟨t, hT htT⟩ ∈ autSec T VT C ∧
      ∀ s ∈ autSec T VT C, s ∈ stabSub (sec35Img VT C V) ∨
        (n2Rho VT C ⟨t, hT htT⟩)⁻¹ * s ∈ stabSub (sec35Img VT C V) := by
  refine ⟨(n2_mem_autSec hT).2 ⟨⟨t, hT htT⟩, htT, rfl⟩, fun s hs => ?_⟩
  obtain ⟨g, hgT, rfl⟩ := (n2_mem_autSec hT).1 hs
  rcases hsplit g hgT with h | h
  · exact Or.inl (n2Rho_mem_stabSub g h)
  · right
    rw [← map_inv, ← map_mul]
    exact n2Rho_mem_stabSub _ h

end Transfer

end CFSG.Quasithin.SmithD391
