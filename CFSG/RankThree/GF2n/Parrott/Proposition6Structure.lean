module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Lemma37Defs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXTheta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {z : G}

theorem inSubgroup_pCore_two_le_twoThreeCore (Y : Subgroup G) :
    inSubgroup (CFSG.pCore 2) Y ≤ twoThreeCore Y := by
  intro x hx
  rw [inSubgroup, Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  unfold twoThreeCore
  rw [Subgroup.mem_map]
  refine ⟨y, ?_, rfl⟩
  rw [Subgroup.mem_comap]
  have hmk : (QuotientGroup.mk' (CFSG.pCore 2 Y)) y = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  rw [hmk]
  exact (CFSG.pCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y)).one_mem

theorem sl23Pair_of_local {M L1 L2 : Subgroup G}
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hsup : L1 ⊔ L2 = M)
    (hL1 : Nonempty (↥L1 ≃* CFSG.OddStandard.SmallF3.Omega.SL23))
    (hL2 : Nonempty (↥L2 ≃* CFSG.OddStandard.SmallF3.Omega.SL23)) :
    CFSG.OddStandard.SmallF3.Omega.K5.SL23Pair ↥M (L1.subgroupOf M) (L2.subgroupOf M) where
  comm a ha b hb := by
    apply Subtype.ext
    exact hcomm a ha b hb
  top := by
    have hL1M : L1 ≤ M := hsup ▸ le_sup_left
    have hL2M : L2 ≤ M := hsup ▸ le_sup_right
    rw [← Subgroup.subgroupOf_sup hL1M hL2M, hsup, Subgroup.subgroupOf_self]
  isoA := ⟨(Subgroup.subgroupOfEquivOfLe (hsup ▸ le_sup_left : L1 ≤ M)).trans hL1.some⟩
  isoB := ⟨(Subgroup.subgroupOfEquivOfLe (hsup ▸ le_sup_right : L2 ≤ M)).trans hL2.some⟩

end CFSG.RankThree.GF2n.Parrott

namespace P6Model

open CFSG.OddStandard.SmallF3.Omega
open CFSG.OddStandard.SmallF3.Omega.K5

def alpha : SL23 := ⟨!![0, 1; 2, 0], by decide +kernel⟩

theorem alpha_pow_four : alpha ^ 4 = 1 := by decide +kernel

theorem alpha_sq : alpha ^ 2 = -1 := by decide +kernel

end P6Model

namespace P6Aux

open Subgroup

variable {X : Type} [Group X]

@[expose] noncomputable def conjHom (N : Subgroup X) [N.Normal] : X →* MulAut ↥N :=
  (Subgroup.normalizerMonoidHom (H := N)).comp
    ((Subgroup.topEquiv (G := X)).symm.trans
      (MulEquiv.subgroupCongr (Subgroup.normalizer_eq_top (H := N)).symm)).toMonoidHom

theorem conjHom_apply (N : Subgroup X) [N.Normal] (x : X) (n : ↥N) :
    ((conjHom N x n : ↥N) : X) = x * (n : X) * x⁻¹ := rfl

end P6Aux

namespace CFSG.OddStandard.SmallF3.Omega.K5

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem not_map_A_A_B_A (α : MulAut K) (hA : ∀ a ∈ A, α a ∈ A)
    (hB : ∀ b ∈ B, α b ∈ A) : False := by
  have hK : (⊤ : Subgroup K) = A.map (α : K →* K) ⊔ B.map (α : K →* K) := by
    rw [← h.top, ← Subgroup.map_sup, h.top]
    exact (Subgroup.map_top_of_surjective (α : K →* K) α.surjective).symm
  have hKleA : (⊤ : Subgroup K) ≤ A := by
    rw [hK]
    refine sup_le ?_ ?_
    · rintro x ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro x ⟨b, hb, rfl⟩
      exact hB b hb
  have hgenA : h.gen (Sum.inr 0) ∈ A := hKleA (Subgroup.mem_top _)
  exact h.gen_ne_one (Sum.inr 0)
    (h.eq_one_of_mem_inf ⟨hgenA, h.gen_mem_B 0⟩ (h.gen_pow_three _))

theorem not_map_A_B_B_B (α : MulAut K) (hA : ∀ a ∈ A, α a ∈ B)
    (hB : ∀ b ∈ B, α b ∈ B) : False := by
  have hK : (⊤ : Subgroup K) = A.map (α : K →* K) ⊔ B.map (α : K →* K) := by
    rw [← h.top, ← Subgroup.map_sup, h.top]
    exact (Subgroup.map_top_of_surjective (α : K →* K) α.surjective).symm
  have hKleB : (⊤ : Subgroup K) ≤ B := by
    rw [hK]
    refine sup_le ?_ ?_
    · rintro x ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro x ⟨b, hb, rfl⟩
      exact hB b hb
  have hgenB : h.gen (Sum.inl 0) ∈ B := hKleB (Subgroup.mem_top _)
  exact h.gen_ne_one (Sum.inl 0)
    (h.eq_one_of_mem_inf ⟨h.gen_mem_A 0, hgenB⟩ (h.gen_pow_three _))

theorem block_perm (α : MulAut K) :
    ((∀ a ∈ A, α a ∈ A) ∧ (∀ b ∈ B, α b ∈ B)) ∨
      ((∀ a ∈ A, α a ∈ B) ∧ (∀ b ∈ B, α b ∈ A)) := by
  rcases h.s11s_block_A α with hA | hA <;> rcases h.s11s_block_B α with hB | hB
  · exact Or.inl ⟨hA, hB⟩
  · exact (h.not_map_A_A_B_A α hA hB).elim
  · exact (h.not_map_A_B_B_B α hA hB).elim
  · exact Or.inr ⟨hA, hB⟩

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5

namespace CFSG.OddStandard.SmallF3.Omega.K5

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

theorem center_sq_one {z : K} (hz : z ∈ Subgroup.center K) : z * z = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul z
  have hz_comm : ∀ g : K, (a * b) * g = g * (a * b) :=
    fun g => (Subgroup.mem_center_iff.mp hz g).symm
  have ha_cent : (⟨a, ha⟩ : ↥A) ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro a'
    let x : K := (a' : K)
    have hcomm' : (a * b) * x = x * (a * b) := hz_comm x
    apply Subtype.ext
    change x * a = a * x
    have hbx : b * x = x * b :=
      (h.comm (a' : K) (show (a' : K) ∈ A from a'.2) b hb).symm
    have hax : a * x = x * a := by
      calc a * x = a * b * x * b⁻¹ := by rw [mul_assoc a b x, hbx]; group
        _ = x * a * b * b⁻¹ := by rw [hcomm']; simp only [mul_assoc]
        _ = x * a := by simp [mul_assoc]
    exact hax.symm
  have hb_cent : (⟨b, hb⟩ : ↥B) ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro b'
    let y : K := (b' : K)
    have hcomm' : (a * b) * y = y * (a * b) := hz_comm y
    have hacomm : a * y = y * a := h.comm a ha (b' : K) (show (b' : K) ∈ B from b'.2)
    apply Subtype.ext
    change y * b = b * y
    have hby : b * y = y * b := by
      calc b * y = a⁻¹ * (a * b * y) := by group
        _ = a⁻¹ * (y * a * b) := by rw [hcomm']; simp only [mul_assoc]
        _ = a⁻¹ * (a * y * b) := by rw [← hacomm]
        _ = y * b := by group
    exact hby.symm
  have ha2 : a * a = 1 := by
    have hc : h.eA ⟨a, ha⟩ ∈ Subgroup.center SL23 := by
      rw [Subgroup.mem_center_iff]
      intro s
      have hcomm := Subgroup.mem_center_iff.mp ha_cent (h.eA.symm s)
      have := congrArg h.eA hcomm
      simpa using this
    have hsq := sq_of_central (fun t => (Subgroup.mem_center_iff.mp hc t).symm)
    have ha2A : (⟨a, ha⟩ : ↥A) * ⟨a, ha⟩ = 1 := by
      apply h.eA.injective
      rw [map_mul, hsq, map_one]
    exact congrArg Subtype.val ha2A
  have hb2 : b * b = 1 := by
    have hc : h.eB ⟨b, hb⟩ ∈ Subgroup.center SL23 := by
      rw [Subgroup.mem_center_iff]
      intro s
      have hcomm := Subgroup.mem_center_iff.mp hb_cent (h.eB.symm s)
      have := congrArg h.eB hcomm
      simpa using this
    have hsq := sq_of_central (fun t => (Subgroup.mem_center_iff.mp hc t).symm)
    have hb2B : (⟨b, hb⟩ : ↥B) * ⟨b, hb⟩ = 1 := by
      apply h.eB.injective
      rw [map_mul, hsq, map_one]
    exact congrArg Subtype.val hb2B
  have hcomm_ab : a * b = b * a := h.comm a ha b hb
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hcomm_ab]
    _ = (a * a) * (b * b) := by group
    _ = 1 := by rw [ha2, hb2, mul_one]

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5

namespace P6Core

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem centralizer_le_of_pair {M A B : Subgroup X} [M.Normal]
    (hpair : CFSG.OddStandard.SmallF3.Omega.K5.SL23Pair ↥M (A.subgroupOf M) (B.subgroupOf M))
    (hquot2 : ∀ x : X ⧸ M, x ^ 2 = 1)
    (hcore : CFSG.pCore 2 X ≤ M) :
    Subgroup.centralizer (M : Set X) ≤ M := by
  have hfour : ∀ c : X, c ∈ Subgroup.centralizer (M : Set X) → c ^ 4 = 1 := by
    intro c hc
    have hc2M : c ^ 2 ∈ M := by
      have hq := hquot2 (QuotientGroup.mk' M c)
      have h2 : QuotientGroup.mk' M (c ^ 2) = 1 := by
        simpa only [map_pow] using hq
      have h2' : (c ^ 2 : X ⧸ M) = 1 := by
        simpa only [QuotientGroup.mk'_apply, map_pow] using h2
      exact (QuotientGroup.eq_one_iff (c ^ 2)).mp h2'
    let c2 : ↥M := ⟨c ^ 2, hc2M⟩
    have hc2cent : c2 ∈ Subgroup.center ↥M := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      let yx : X := (y : X)
      have hcy : yx * c = c * yx := hc y y.2
      change yx * c ^ 2 = c ^ 2 * yx
      calc yx * c ^ 2 = (yx * c) * c := by rw [pow_two, mul_assoc]
        _ = (c * yx) * c := by rw [hcy]
        _ = c * (yx * c) := by group
        _ = c * (c * yx) := by rw [hcy]
        _ = c ^ 2 * yx := by rw [pow_two]; group
    have hsq := hpair.center_sq_one hc2cent
    have hval : c ^ 2 * c ^ 2 = 1 := by
      have := congrArg Subtype.val hsq
      simpa [c2] using this
    calc c ^ 4 = c ^ 2 * c ^ 2 := by group
      _ = 1 := hval
  have hC2 : IsPGroup 2 (Subgroup.centralizer (M : Set X)) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro d
    refine ⟨2, ?_⟩
    apply Subtype.ext
    simpa [pow_succ, pow_two, mul_assoc] using hfour d d.2
  have hCnormal : (Subgroup.centralizer (M : Set X)).Normal := inferInstance
  exact (le_sSup (show Subgroup.centralizer (M : Set X) ∈
    {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from ⟨hCnormal, hC2⟩)).trans hcore

end P6Core

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {z : G}

theorem p6_core_structure
    [hN : ((twoThreeCore (H z)).subgroupOf (H z)).Normal]
    {L1 L2 : Subgroup G}
    (hL1H : L1 ≤ H z) (hL2H : L2 ≤ H z)
    (hL1 : Nonempty (↥L1 ≃* CFSG.OddStandard.Solomon75.SL23))
    (hL2 : Nonempty (↥L2 ≃* CFSG.OddStandard.Solomon75.SL23))
    (hcomm : ∀ x ∈ L1, ∀ y ∈ L2, x * y = y * x)
    (hinf1 : L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype)
    (hinf2 : L1 ⊓ L2 = (Subgroup.center L2).map L2.subtype)
    (hsup : L1 ⊔ L2 = twoThreeCore (H z))
    (hquot2 : ∀ x : ↥(H z) ⧸
      (twoThreeCore (H z)).subgroupOf (H z), x ^ 2 = 1) :
    Subgroup.centralizer ((twoThreeCore (H z)).subgroupOf (H z) : Set ↥(H z)) ≤
      (twoThreeCore (H z)).subgroupOf (H z) ∧
    ∀ h : ↥(H z),
      ((∀ x ∈ L1.subgroupOf (H z), h * x * h⁻¹ ∈ L1.subgroupOf (H z)) ∧
        (∀ x ∈ L2.subgroupOf (H z), h * x * h⁻¹ ∈ L2.subgroupOf (H z))) ∨
      ((∀ x ∈ L1.subgroupOf (H z), h * x * h⁻¹ ∈ L2.subgroupOf (H z)) ∧
        (∀ x ∈ L2.subgroupOf (H z), h * x * h⁻¹ ∈ L1.subgroupOf (H z))) := by
  classical
  let Hh := ↥(H z)
  let M : Subgroup G := twoThreeCore (H z)
  let M' : Subgroup Hh := M.subgroupOf (H z)
  let L1' : Subgroup Hh := L1.subgroupOf (H z)
  let L2' : Subgroup Hh := L2.subgroupOf (H z)
  have hsup' : L1' ⊔ L2' = M' := by
    change (L1.subgroupOf (H z)) ⊔ (L2.subgroupOf (H z)) = M.subgroupOf (H z)
    rw [← Subgroup.subgroupOf_sup hL1H hL2H, hsup]
  have hcomm' : ∀ x ∈ L1', ∀ y ∈ L2', x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hcomm x hx y hy
  have hL1' : Nonempty (↥L1' ≃* CFSG.OddStandard.SmallF3.Omega.SL23) := by
    obtain ⟨e⟩ := hL1
    exact ⟨(Subgroup.subgroupOfEquivOfLe hL1H).trans e⟩
  have hL2' : Nonempty (↥L2' ≃* CFSG.OddStandard.SmallF3.Omega.SL23) := by
    obtain ⟨e⟩ := hL2
    exact ⟨(Subgroup.subgroupOfEquivOfLe hL2H).trans e⟩
  let hpair : CFSG.OddStandard.SmallF3.Omega.K5.SL23Pair ↥M' (L1'.subgroupOf M')
      (L2'.subgroupOf M') :=
    CFSG.RankThree.GF2n.Parrott.sl23Pair_of_local (G := Hh) (M := M') (L1 := L1') (L2 := L2')
      hcomm' hsup' hL1' hL2'
  have hcore : CFSG.pCore 2 Hh ≤ M' := by
    intro x hx
    have hxG : (x : G) ∈ inSubgroup (CFSG.pCore 2) (H z) := by
      rw [inSubgroup]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact inSubgroup_pCore_two_le_twoThreeCore (H z) hxG
  refine ⟨?_, ?_⟩
  · exact P6Core.centralizer_le_of_pair hpair hquot2 hcore
  · intro h
    have hL1'M : L1' ≤ M' := hsup' ▸ le_sup_left
    have hL2'M : L2' ≤ M' := hsup' ▸ le_sup_right
    have hblock := hpair.block_perm (P6Aux.conjHom M' h)
    rcases hblock with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · left
      refine ⟨?_, ?_⟩
      · intro x hx
        let xM : ↥M' := ⟨x, hL1'M hx⟩
        have hmem : P6Aux.conjHom M' h xM ∈ L1'.subgroupOf M' := hA xM hx
        have hcoe : ((P6Aux.conjHom M' h xM : ↥M') : Hh) = h * x * h⁻¹ :=
          P6Aux.conjHom_apply M' h xM
        change h * x * h⁻¹ ∈ L1'
        rw [← hcoe]
        exact hmem
      · intro x hx
        let xM : ↥M' := ⟨x, hL2'M hx⟩
        have hmem : P6Aux.conjHom M' h xM ∈ L2'.subgroupOf M' := hB xM hx
        have hcoe : ((P6Aux.conjHom M' h xM : ↥M') : Hh) = h * x * h⁻¹ :=
          P6Aux.conjHom_apply M' h xM
        change h * x * h⁻¹ ∈ L2'
        rw [← hcoe]
        exact hmem
    · right
      refine ⟨?_, ?_⟩
      · intro x hx
        let xM : ↥M' := ⟨x, hL1'M hx⟩
        have hmem : P6Aux.conjHom M' h xM ∈ L2'.subgroupOf M' := hA xM hx
        have hcoe : ((P6Aux.conjHom M' h xM : ↥M') : Hh) = h * x * h⁻¹ :=
          P6Aux.conjHom_apply M' h xM
        change h * x * h⁻¹ ∈ L2'
        rw [← hcoe]
        exact hmem
      · intro x hx
        let xM : ↥M' := ⟨x, hL2'M hx⟩
        have hmem : P6Aux.conjHom M' h xM ∈ L1'.subgroupOf M' := hB xM hx
        have hcoe : ((P6Aux.conjHom M' h xM : ↥M') : Hh) = h * x * h⁻¹ :=
          P6Aux.conjHom_apply M' h xM
        change h * x * h⁻¹ ∈ L1'
        rw [← hcoe]
        exact hmem

end CFSG.RankThree.GF2n.Parrott

