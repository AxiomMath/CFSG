module

public import CFSG.Milestones.ASVolI.C121.P1b
public import CFSG.CGT.PushingUpLit.SixThreeBasic

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups

theorem burnsideC121_le_normalizer_commutator {Ω : Type} [Group Ω] {K A B : Subgroup Ω}
    (hA : K ≤ Subgroup.normalizer (A : Set Ω)) (hB : K ≤ Subgroup.normalizer (B : Set Ω)) :
    K ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup Ω) : Set Ω) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hk),
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hB hk)]

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c

theorem commutator_commutator_W : ⁅⁅W, Y⁆, Y⁆ = ⁅W, Y⁆ :=
  CFSG.CGT.PushingUpLit.SixThree.commutator_commutator_eq c.noTwoQuotient
    (B2F.isPGroup_of_isElemAbelian c.W_elem) c.Y_le_normalizer_W

theorem commW_le_W : ⁅W, Y⁆ ≤ W := burnsideC121_commutator_le c.Y_le_normalizer_W

theorem commW_elem : IsElemAbelian 2 ⁅W, Y⁆ := B2F.isElemAbelian_mono c.commW_le_W c.W_elem

theorem H_le_normalizer_commW :
    burnsideC121_H X T Y ≤ Subgroup.normalizer ((⁅W, Y⁆ : Subgroup Ω) : Set Ω) :=
  burnsideC121_le_normalizer_commutator c.H_le_normalizer_W c.H_le_normalizer

theorem commW_le_pCore_Y : ⁅W, Y⁆ ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : ⁅W, Y⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (c.W_le_H.trans c.H_le_normalizer)
  exact le_pCoreOf_of_le_normalizer 2 hY (c.Y_le_H.trans c.H_le_normalizer_commW)
    (B2F.isPGroup_of_isElemAbelian c.commW_elem)

include D

theorem not_le_centralizer_commW : ¬ Y ≤ Subgroup.centralizer ((⁅W, Y⁆ : Subgroup Ω) : Set Ω) := by
  intro h
  have h1 : ⁅⁅W, Y⁆, Y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.le_centralizer_iff).1 h
  rw [c.commutator_commutator_W] at h1
  apply c.not_le_centralizer_W D
  exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)

theorem inf_centralizer_eq_of_le {M : Subgroup Ω} (hMW : M ≤ W)
    (hHM : burnsideC121_H X T Y ≤ Subgroup.normalizer (M : Set Ω))
    (hYM : ¬ Y ≤ Subgroup.centralizer (M : Set Ω)) :
    Y ⊓ Subgroup.centralizer (M : Set Ω) = pCoreOf 2 Y := by
  have hn : Y ≤ Subgroup.normalizer ((Y ⊓ Subgroup.centralizer (M : Set Ω) : Subgroup Ω) : Set Ω) :=
    fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy,
        B2F.normalizer_le_normalizer_centralizer M (hHM (c.Y_le_H hy))⟩
  rcases c.normal_le_or_eq D inf_le_left hn with h | h
  · exact le_antisymm h (le_inf (pCoreOf_le 2 Y)
      (c.pCore_Y_le_centralizer.trans (Subgroup.centralizer_le hMW)))
  · exact absurd (h ▸ inf_le_right) hYM

theorem isTwoReducedIn_of_le {M : Subgroup Ω} (hMW : M ≤ W)
    (hHM : burnsideC121_H X T Y ≤ Subgroup.normalizer (M : Set Ω))
    (hYM : ¬ Y ≤ Subgroup.centralizer (M : Set Ω)) :
    IsTwoReducedIn (burnsideC121_H X T Y) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hMW.trans c.W_le_H, hHM, B2F.isElemAbelian_mono hMW c.W_elem, ?_⟩
  intro Dd hDH hHD h2
  have hCY := c.inf_centralizer_eq_of_le D hMW hHM hYM
  have hDp : IsPGroup 2 Dd := by
    rintro ⟨d, hd⟩
    obtain ⟨k, hk⟩ := h2 d hd
    obtain ⟨j, hj⟩ := C124.exists_pow_mem_of_prod c.Y_le_H c.H_le_normalizer c.P_le_H c.P_pGroup
      (Subgroup.pow_mem _ (hDH hd) _) (c.H_prod _ (Subgroup.pow_mem _ (hDH hd) _))
    have hmem : (d ^ 2 ^ k) ^ 2 ^ j ∈ Y ⊓ Subgroup.centralizer (M : Set Ω) :=
      ⟨hj, Subgroup.pow_mem _ hk _⟩
    rw [hCY] at hmem
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hmem⟩
    refine ⟨k + j + m, Subtype.ext ?_⟩
    have hm' : ((d ^ 2 ^ k) ^ 2 ^ j) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_add, pow_mul, pow_mul, hm']
  exact (le_pCoreOf_of_le_normalizer 2 hDH hHD hDp).trans
    (c.pCore_H_le_centralizer.trans (Subgroup.centralizer_le hMW))

theorem isTwoReducedIn_commW : IsTwoReducedIn (burnsideC121_H X T Y) ⁅W, Y⁆ :=
  c.isTwoReducedIn_of_le D c.commW_le_W c.H_le_normalizer_commW (c.not_le_centralizer_commW D)

theorem inf_centralizer_commW : Y ⊓ Subgroup.centralizer ((⁅W, Y⁆ : Subgroup Ω) : Set Ω) = pCoreOf 2 Y :=
  c.inf_centralizer_eq_of_le D c.commW_le_W c.H_le_normalizer_commW (c.not_le_centralizer_commW D)

theorem not_le_centralizer_omega_n1 (hn : n = 1) (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    ¬ Y ≤ Subgroup.centralizer (omegaOneCenterOf (baum T) : Set Ω) := by
  intro hYE
  obtain ⟨-, h5⟩ := c.e23 D hn hYS
  rw [← c.baum_P, burnsideC121_omegaOneCenter_baum] at hYE
  set E := omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) with hE
  have hcl : conjClosure E Y ≤ Subgroup.centralizer (Y : Set Ω) := by
    refine conjClosure_le fun y hy e he => ?_
    have hc : e * y = y * e := Subgroup.mem_centralizer_iff.1 (hYE hy) e he
    have : y * e * y⁻¹ = e := by rw [← hc, mul_inv_cancel_right]
    rw [this]
    exact Subgroup.mem_centralizer_iff.2 fun z hz =>
      (Subgroup.mem_centralizer_iff.1 (hYE hz) e he).symm
  rw [h5] at hcl
  apply c.not_le_centralizer_commW D
  exact (Subgroup.le_centralizer_iff).1 (le_sup_left.trans hcl)

end burnsideC121_YCtx

end CFSG.ASVolI
