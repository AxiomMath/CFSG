module

public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddModel
public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddBlock
public import CFSG.RankThree.PartTwo.Sec21.KS21U4Transport
import CFSG.RankThree.PartTwo.Sec21.Item222ProofStar
import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4OddLines

open CFSG CFSG.RankThree CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU diagU_val torusVec symAct coe_symAct permGL
  permGL_mem_unitarySU apply_eq_zero_of_commute_diagU)

variable {K : Type} [Field K]

theorem commute_diagU_of {n : ℕ} {e d : Fin n → Kˣ} {g : GL (Fin n) K}
    (hg : g * diagU e = diagU e * g) (hed : ∀ i j, e i = e j → d i = d j) :
    g * diagU d = diagU d * g := by
  apply Units.ext
  simp only [Units.val_mul, diagU_val]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : e i = e j
  · rw [hed i j h, mul_comm]
  · rw [apply_eq_zero_of_commute_diagU hg h, zero_mul, mul_zero]

@[expose] def d0 {ω : Kˣ} (hω : ω ^ 3 = 1) : torusVec 3 4 K :=
  ⟨dvecD0 ω, fun i => by fin_cases i <;> simp [dvecD0, hω], by
    simp [dvecD0, Fin.prod_univ_four]⟩

theorem coe_d0 {ω : Kˣ} (hω : ω ^ 3 = 1) : ((d0 hω : torusVec 3 4 K) : Fin 4 → Kˣ) = dvecD0 ω :=
  rfl

theorem dvecD0_eq {ω : Kˣ} (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹) {k l : Fin 4}
    (h : dvecD0 ω k = dvecD0 ω l) : k = l ∨ (k.val < 2 ∧ l.val < 2) := by
  have h1' : ω⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
  fin_cases k <;> fin_cases l <;> simp [dvecD0] at h ⊢ <;>
    first | exact h1 h.symm | exact h1 h | exact h1' h.symm | exact h1' h | exact h2 h |
      exact h2 h.symm

namespace U4OddCtx

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {c : G} {f : ℕ}
  (C : U4OddCtx G L A c f K)

theorem mapL_inf_centralizer_fixed {a b : Fin 4} {π : Equiv.Perm (Fin 4)} (hπ0 : π 0 = a)
    (hπ1 : π 1 = b) {ω : Kˣ} (hω3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹) :
    U4Lines.mapL C.ψ.symm
        (L ⊓ Subgroup.centralizer (fixedInG A (C.actA (Equiv.swap a b)) : Set G)) =
      unitarySU 2 f K 4 ⊓ Subgroup.centralizer
        {((C.torU (symAct 3 K π (d0 hω3)) : unitarySU 2 f K 4) : GL (Fin 4) K)} := by
  set e := symAct 3 K π (d0 hω3) with he
  have hπa : π.symm a = 0 := by rw [Equiv.symm_apply_eq, hπ0]
  have hπb : π.symm b = 1 := by rw [Equiv.symm_apply_eq, hπ1]
  have hea : (e : Fin 4 → Kˣ) a = 1 := by
    rw [he, coe_symAct, hπa, coe_d0]
    rfl
  have heb : (e : Fin 4 → Kˣ) b = 1 := by
    rw [he, coe_symAct, hπb, coe_d0]
    rfl
  have he_fix : symAct 3 K (Equiv.swap a b) e = e := by
    apply Subtype.ext
    funext i
    rw [coe_symAct, Equiv.symm_swap]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, hea, heb]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, hea, heb]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
  have hlev : ∀ d : torusVec 3 4 K, (d : Fin 4 → Kˣ) a = (d : Fin 4 → Kˣ) b →
      ∀ i j, (e : Fin 4 → Kˣ) i = (e : Fin 4 → Kˣ) j →
        (d : Fin 4 → Kˣ) i = (d : Fin 4 → Kˣ) j := by
    intro d hd i j hij
    rw [he, coe_symAct, coe_symAct, coe_d0] at hij
    rcases dvecD0_eq h1 h2 hij with h | ⟨hk, hl⟩
    · rw [π.symm.injective h]
    · have hmem : ∀ m : Fin 4, (π.symm m).val < 2 → m = a ∨ m = b := by
        intro m hm
        have hm' : π.symm m = 0 ∨ π.symm m = 1 := by
          rcases (by omega : (π.symm m).val = 0 ∨ (π.symm m).val = 1) with h0 | h0
          · exact Or.inl (Fin.ext h0)
          · exact Or.inr (Fin.ext h0)
        rcases hm' with h0 | h0
        · left
          rw [← hπ0, ← h0, Equiv.apply_symm_apply]
        · right
          rw [← hπ1, ← h0, Equiv.apply_symm_apply]
      rcases hmem i hk with rfl | rfl <;> rcases hmem j hl with rfl | rfl
      · rfl
      · exact hd
      · exact hd.symm
      · rfl
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxC : (x : G) ∈ Subgroup.centralizer (fixedInG A (C.actA (Equiv.swap a b)) : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
    have hθe : C.theta e ∈ fixedInG A (C.actA (Equiv.swap a b)) := by
      refine ⟨⟨C.theta e, C.theta_mem_A e⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_fixedSubgroupOf, C.actA_theta, he_fix]
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC _ hθe
    refine Subgroup.mem_inf.mpr ⟨(C.ψ.symm x).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hx' : (x : G) = C.phi (C.ψ.symm x) := by rw [coe_phi, MulEquiv.apply_symm_apply]
    rw [theta_apply, hx', ← map_mul, ← map_mul] at hcomm
    have h' := C.phi_injective hcomm
    show ((C.ψ.symm x : unitarySU 2 f K 4) : GL (Fin 4) K) * (C.torU e : GL (Fin 4) K) =
      (C.torU e : GL (Fin 4) K) * (C.ψ.symm x : unitarySU 2 f K 4)
    exact (congrArg Subtype.val h').symm
  · intro hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgD := Subgroup.mem_centralizer_singleton_iff.mp hgC
    refine ⟨C.ψ ⟨g, hgU⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨(C.ψ _).2, ?_⟩),
      by simp [U4Lines.embedOf]⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf] at hy
    obtain ⟨d, i, hdi⟩ := C.decomp y.2
    have hfix : symAct 3 K (Equiv.swap a b) d = d := by
      apply C.theta_injective
      have h := congrArg Subtype.val hy
      rw [actA_apply_coe, hdi, C.conj_theta_zpow] at h
      exact mul_right_cancel h
    have hdab : (d : Fin 4 → Kˣ) a = (d : Fin 4 → Kˣ) b := by
      have := congrFun (congrArg Subtype.val hfix) a
      rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_left] at this
      exact this.symm
    have hgd : g * diagU (d : Fin 4 → Kˣ) = diagU (d : Fin 4 → Kˣ) * g := by
      have hgD' : g * diagU (e : Fin 4 → Kˣ) = diagU (e : Fin 4 → Kˣ) * g := hgD
      exact commute_diagU_of hgD' (hlev d hdab)
    have hθ : C.theta d * C.phi ⟨g, hgU⟩ = C.phi ⟨g, hgU⟩ * C.theta d := by
      rw [theta_apply, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hgd.symm
    have hcg : c ^ i * C.phi ⟨g, hgU⟩ = C.phi ⟨g, hgU⟩ * c ^ i :=
      ((Commute.zpow_left (show Commute c (C.phi ⟨g, hgU⟩) from
        (C.comm_c (C.phi_mem_L _)).symm) i)).eq
    show (y : G) * C.phi ⟨g, hgU⟩ = C.phi ⟨g, hgU⟩ * y
    rw [hdi, mul_assoc, hcg, ← mul_assoc, hθ, mul_assoc]

theorem nonempty_perfectResidual_fixed_swap {a b : Fin 4} (hab : a ≠ b) :
    Nonempty (inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer (fixedInG A (C.actA (Equiv.swap a b)) : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) C.hU.fixedField) := by
  have := C.hU.finite
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hω3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have h1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have h2 : ζ ≠ ζ⁻¹ := by
    intro h
    have hsq : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := sq ζ
        _ = ζ * ζ⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel ζ
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq
  obtain ⟨π, hπ0, hπ1⟩ := CFSG.RankThree.PartOne.KFU.exists_perm_pair
    (show (0 : Fin 4) ≠ 1 by decide) hab
  have hmap := C.mapL_inf_centralizer_fixed hπ0 hπ1 hω3 h1 h2
  have hD : ((C.torU (symAct 3 K π (d0 hω3)) : unitarySU 2 f K 4) : GL (Fin 4) K) =
      permGL π * diagU (dvecD0 ζ) * (permGL π)⁻¹ := by
    rw [← C.permU_conj_torU]
    rfl
  have hz : (Subgroup.zpowers (diagU (dvecD0 ζ))).map (MulAut.conj (permGL π)).toMonoidHom =
      Subgroup.zpowers (permGL π * diagU (dvecD0 ζ) * (permGL π)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hconj := U4Lines.perfectResidual_conj (Y := unitarySU 2 f K 4)
    (permGL_mem_unitarySU C.hU π) (Subgroup.zpowers (diagU (dvecD0 ζ)))
  rw [hz, Item222Proof.centralizer_zpowers_eq, Item222Proof.centralizer_zpowers_eq,
    perfectResidual_centralizer_D0 C.hU C.hf2 h1 h2] at hconj
  obtain ⟨eSL⟩ := nonempty_blkSU2_mulEquiv C.hU
  have hZ : inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer (fixedInG A (C.actA (Equiv.swap a b)) : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  refine ⟨(U4Lines.mapLEquiv C.ψ.symm hZ).trans
    ((MulEquiv.subgroupCongr (U4Lines.mapL_perfectResidual C.ψ.symm inf_le_left)).trans
      ((MulEquiv.subgroupCongr (congrArg (inSubgroup perfectResidual) hmap)).trans
        ((MulEquiv.subgroupCongr (by rw [hD, hconj])).trans
          ((Subgroup.equivMapOfInjective _ _ (MulAut.conj (permGL π)).injective).symm.trans
            eSL))))⟩

end U4OddCtx

end CFSG.RankThree.PartTwo.Sec21.U4OddLines
