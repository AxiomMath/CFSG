module

public import CFSG.Monster.B.TwoA.Amalgam.Flag1Planes
public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.TwoA.Unitary.Coinv

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Co2 CFSG.Monster.B.Short

theorem b6Iso_vals : b6Iso 0 = 0 ∧ b6Iso 1 = 1 ∧ b6Iso 3 = 4 := by decide +kernel

theorem Lp_zero : Lp 0 = Tsp := by rw [Lp, b6Iso_vals.1, Tsp_eq_plane]

theorem Lp_zero' : Lp 0 = plane 0 := by rw [Lp, b6Iso_vals.1]

theorem Lp_one : Lp 1 = plane 1 := by rw [Lp, b6Iso_vals.2.1]

theorem Lp_three : Lp 3 = plane 4 := by rw [Lp, b6Iso_vals.2.2]

theorem natIdx_eq_iff
    (u : Usig) (j m : Fin 891) :
    natIdx u j = m ↔ sigmaAct (Lp j) (phiU u) = Lp m := by
  rw [← Lp_injective.eq_iff]
  change plane (b6Iso (natIdx u j)) = Lp m ↔ _
  rw [plane_natIdx]
  rfl

theorem natIdx_mem_iff
    (u : Usig) (j : Fin 891) :
    (natIdx u j = 0 ∨ natIdx u j = 1 ∨ natIdx u j = 3) ↔
      ThroughH (sigmaAct (Lp j) (phiU u)) := by
  rw [natIdx_eq_iff, natIdx_eq_iff, natIdx_eq_iff, Lp_zero', Lp_one, Lp_three]
  rfl

theorem mem_Mfr_iff_sigmaAct
    (u : Usig) :
    (u : Kstab v0) ∈ Mfr ↔ sigmaAct Tsp (phiU u) = Tsp := by
  rw [Mfr, mem_wStab, ← n6vec_zero, ← n6vec_natIdx, n6vec_injective.eq_iff, natIdx_eq_iff,
    Lp_zero]

theorem n6vec_three :
    n6vec 3 = sW := by
  rw [n6vec, sW, pairW23_eq_decW]
  exact congrArg decW n6Vec_one_three.2

theorem n6vec_one :
    n6vec 1 = wFr + sW := by
  have hs := n6vec_sum_zero
  rw [n6vec_zero, n6vec_three] at hs
  apply add_eq_zero_iff_W.1
  rw [← hs]
  abel

theorem n6vec_ne_zero
    (m : Fin 891) : n6vec m ≠ 0 := by
  intro h
  obtain ⟨u, -, e⟩ := exists_wAct_wFr m
  apply wFr_ne_zero
  rw [← wAct_inv_apply u wFr, e, h, map_zero]

theorem n6vec_mem_Uplane_iff
    (m : Fin 891) : n6vec m ∈ Uplane ↔ m = 0 ∨ m = 1 ∨ m = 3 := by
  constructor
  · intro hm
    rcases (mem_Uplane_iff _).1 hm with h | h | h | h
    · exact absurd h (n6vec_ne_zero m)
    · exact Or.inl (n6vec_injective (h.trans n6vec_zero.symm))
    · exact Or.inr (Or.inr (n6vec_injective (h.trans n6vec_three.symm)))
    · exact Or.inr (Or.inl (n6vec_injective (h.trans n6vec_one.symm)))
  · rintro (rfl | rfl | rfl)
    · rw [n6vec_zero]
      exact wFr_mem_Uplane
    · rw [n6vec_one]
      exact Uplane.add_mem wFr_mem_Uplane sW_mem_Uplane
    · rw [n6vec_three]
      exact sW_mem_Uplane

theorem mem_NU_iff_natIdx
    (u : Usig) : (u : Kstab v0) ∈ wSetStab Uplane ↔
    (natIdx u 0 = 0 ∨ natIdx u 0 = 1 ∨ natIdx u 0 = 3) ∧
      (natIdx u 3 = 0 ∨ natIdx u 3 = 1 ∨ natIdx u 3 = 3) := by
  rw [← n6vec_mem_Uplane_iff, ← n6vec_mem_Uplane_iff, n6vec_natIdx, n6vec_natIdx, n6vec_zero,
    n6vec_three]
  constructor
  · intro h
    exact ⟨(mem_wSetStab.1 h) _ wFr_mem_Uplane, (mem_wSetStab.1 h) _ sW_mem_Uplane⟩
  · rintro ⟨h1, h2⟩
    exact mem_NU_of h1 h2

theorem mem_NU_iff_sigmaAct
    (u : Usig) :
    (u : Kstab v0) ∈ wSetStab Uplane ↔ sigmaAct Hsp (phiU u) = Hsp := by
  rw [mem_NU_iff_natIdx, natIdx_mem_iff, natIdx_mem_iff, Lp_zero', Lp_three]
  exact sigmaAct_Hsp_iff _

theorem genK_six :
    genK 6 = rK := by
  apply Subtype.ext
  change n6Elt 6 = CFSG.Monster.B.Co2.alpha 12
  rw [n6Elt_of_ge (k := 6) (by decide)]
  have hw : n6WordArr[((6 : Fin 17) : ℕ) - 6]! = [12] := by decide +kernel
  rw [hw]
  simp only [alphaWordL, mul_one]
  rw [alphaN, dite_eq_left (by norm_num : (12 : ℕ) < 24)]
  rfl

theorem mem_Cr_iff_commute
    (u : Usig) :
    (u : Kstab v0) ∈ Cr ↔ phiU u * slElt 6 = slElt 6 * phiU u := by
  rw [Cr, Subgroup.mem_centralizer_singleton_iff, ← genK_six, ← phiU_genU 6, ← map_mul, ← map_mul,
    phiU.injective.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem mem_Cr_iff_sigmaAct
    (u : Usig) :
    (u : Kstab v0) ∈ Cr ↔ sigmaAct Rsp (phiU u) = Rsp := by
  rw [mem_Cr_iff_commute, commute_slElt_six_iff]

theorem Pc_zero_eq_P1 :
    Pc 0 = P1 := rfl

@[expose] def rhoP1 :
    Pc 0 →* SigmaU6 :=
  phiU.toMonoidHom.comp (p1Proj.comp (MulEquiv.subgroupCongr Pc_zero_eq_P1).toMonoidHom)

theorem rhoP1_apply
    (g : Pc 0) : rhoP1 g = phiU (p1Proj ⟨g, g.2⟩) := rfl

theorem rhoP1_surjective :
    Function.Surjective rhoP1 :=
  phiU.surjective.comp (p1Proj_surjective.comp (MulEquiv.subgroupCongr Pc_zero_eq_P1).surjective)

theorem ker_rhoP1 :
    rhoP1.ker = (Nc 0).subgroupOf (Pc 0) := by
  ext g
  rw [MonoidHom.mem_ker, rhoP1_apply, map_eq_one_iff _ phiU.injective, ← MonoidHom.mem_ker,
    ker_p1Proj, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Nc_zero]
  rfl

theorem mem_wSetStab_span_wFr
    (k : Kstab v0) :
    k ∈ wSetStab (Submodule.span (ZMod 2) {wFr}) ↔ k ∈ Mfr := by
  rw [mem_wSetStab, Mfr, mem_wStab]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (h wFr (Submodule.mem_span_singleton_self _))
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) a with rfl | rfl
    · exfalso
      rw [zero_smul] at ha
      apply wFr_ne_zero
      rw [← wAct_inv_apply k wFr, ← ha, map_zero]
    · rw [one_smul] at ha
      exact ha.symm
  · intro h x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul, h]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_P1_centralizer
    (g : Pc 0) : (g : Dfull) ∈ Subgroup.centralizer {cQ} := g.2.2

theorem mem_P1_Jhat
    (g : Pc 0) : (g : Dfull) ∈ Jhat := g.2.1

theorem mem_Pc_one_iff_sigmaAct
    (g : Pc 0) :
    (g : Dfull) ∈ Pc 1 ↔ sigmaAct Tsp (rhoP1 g) = Tsp := by
  rw [rhoP1_apply, ← mem_Mfr_iff_sigmaAct, ← mem_wSetStab_span_wFr, coe_p1Proj, Pc_one,
    Subgroup.mem_inf, and_iff_left (mem_P1_centralizer g), Ntwo, Vhat_eq_EU]
  exact mem_normalizer_EU_iff _

theorem mem_Pc_two_iff_sigmaAct
    (g : Pc 0) :
    (g : Dfull) ∈ Pc 2 ↔ sigmaAct Hsp (rhoP1 g) = Hsp := by
  rw [rhoP1_apply, ← mem_NU_iff_sigmaAct, coe_p1Proj, Pc_two, Subgroup.mem_inf,
    and_iff_left (mem_P1_centralizer g)]
  change (g : Dfull) ∈ Subgroup.normalizer (E3 : Set Dfull) ↔ _
  rw [E3_eq_EU]
  exact mem_normalizer_EU_iff _

theorem mem_Pc_three_iff_sigmaAct
    (g : Pc 0) :
    (g : Dfull) ∈ Pc 3 ↔ sigmaAct Rsp (rhoP1 g) = Rsp := by
  rw [rhoP1_apply, ← mem_Cr_iff_sigmaAct, coe_p1Proj, Pc_three, Subgroup.mem_inf,
    and_iff_left (mem_P1_centralizer g)]
  constructor
  · intro hX
    have hH : (g : Dfull) ∈ H1 := by
      rw [← Xgrp_inf_centralizer_xhat]
      exact ⟨hX, by rw [centralizer_xhat]; exact mem_P1_Jhat g⟩
    obtain ⟨hJ, hk⟩ := (mem_H1_iff _).1 hH
    exact hk
  · intro hk
    exact H1_le_Xgrp ((mem_H1_iff _).2 ⟨mem_P1_Jhat g, hk⟩)

theorem Pc_one_subgroupOf :
    (Pc 1).subgroupOf (Pc 0) = (sigStab Tsp).comap rhoP1 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_sigStab]
  exact mem_Pc_one_iff_sigmaAct g

theorem Pc_two_subgroupOf :
    (Pc 2).subgroupOf (Pc 0) = (sigStab Hsp).comap rhoP1 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_sigStab]
  exact mem_Pc_two_iff_sigmaAct g

theorem Pc_three_subgroupOf :
    (Pc 3).subgroupOf (Pc 0) = (sigStab Rsp).comap rhoP1 := by
  ext g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, mem_sigStab]
  exact mem_Pc_three_iff_sigmaAct g

end CFSG.Monster.B.TwoA.Amalgam
