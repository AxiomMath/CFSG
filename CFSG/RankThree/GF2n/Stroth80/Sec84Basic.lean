module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec84Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec4Alg
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_Q_le_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) : Q ≤ hc.CN t := fun x hx =>
  Ctx.mem_CN.mpr ⟨hc.Q_le_Rt ht hx, fun v hv => hc.hyp.toHyp79.comm_mem_V hx (hc.Vt_le_Q t hv)⟩

theorem sec8_Z0_le_CN (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ hc.CN t := by
  obtain ⟨m, -, K, fK, finK, hK, φ, hrange, hker, -⟩ := hs.sp
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc hs.toSec5.mem
  intro x hx
  have hxR : x ∈ Rt M (LB M Q B) t := hZ0.le hx
  have haS : φ ⟨x, hxR⟩ ∈ CFSG.Open.StatedSp m K := by
    rw [← hrange]
    exact ⟨_, rfl⟩
  have hcen : (⟨φ ⟨x, hxR⟩, haS⟩ : ↥(CFSG.Open.StatedSp m K)) ∈
      Subgroup.center ↥(CFSG.Open.StatedSp m K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨r, hr⟩ : (g : GL (Fin m ⊕ Fin m) K) ∈ φ.range := by
      rw [hrange]
      exact g.2
    have hkerm : ⁅(⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)), r⁆ ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hQN (hZ0.comm_mem hx r.2)
    have h1 : φ ⁅(⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)), r⁆ = 1 := hkerm
    have h2 : φ (⟨x, hxR⟩ * r) = φ (r * ⟨x, hxR⟩) := by
      have e : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) * r =
          ⁅(⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)), r⁆ * (r * ⟨x, hxR⟩) := by
        simp only [commutatorElement_def]
        group
      rw [e, map_mul, h1, one_mul]
    apply Subtype.ext
    show (g : GL (Fin m ⊕ Fin m) K) * φ ⟨x, hxR⟩ = φ ⟨x, hxR⟩ * (g : GL (Fin m ⊕ Fin m) K)
    rw [← hr, ← map_mul, ← map_mul]
    exact h2.symm
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot, Subgroup.mem_bot] at hcen
  have h3 : φ ⟨x, hxR⟩ = 1 := congrArg Subtype.val hcen
  have h4 : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h3
  rw [hker, Subgroup.mem_subgroupOf] at h4
  exact h4

theorem sec8_Z0_data (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ∃ r : G, Sec7A hc t r ∧
      Nat.card ↥(LB M Q B ⊓ LB M Q (conjSubgroup r B)) = Nat.card Q * Nat.card Z ∧
      IsOppDecomp (hc.CN t) Z0 (LB M Q B) (LB M Q (conjSubgroup r B))
        (LB M Q B ⊓ hc.CN t) (LB M Q (conjSubgroup r B) ⊓ hc.CN t) ∧
      LB M Q B ⊓ LB M Q (conjSubgroup r B) = Z0 := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have h5 := hs.toSec5
  obtain ⟨-, hcard, hcomm, hopp⟩ := h51 G M Q Z B hc n t h5 (Or.inl hs.spNat) r hr.mem
    hr.plane (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t)
    (Rt M (LB M Q B) t) rfl rfl rfl rfl rfl
  have hZN : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  have hQI : Q ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
    le_inf sec39_Q_le_LB sec39_Q_le_LB
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]
    exact le_sup_right
  have hIZ : LB M Q B ⊓ LB M Q (conjSubgroup r B) = Z0 := by
    apply le_antisymm
    · intro x hx
      refine (hZ0 x).mpr ⟨le_Rt (M := M) (LB M Q B) h5.mem hx.1, fun ρ hρ => ?_⟩
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hcomm ρ hρ x hx)
    · intro z hz
      obtain ⟨-, -, -, -, -, hinf, -, -, h9, h10⟩ := hopp
      have hzN := hZN hz
      have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) h5.mem
      have hzA1 : z ∈ LB M Q B ⊓ hc.CN t :=
        (h9 z hzN).mpr fun l hl => by
          rw [← commutatorElement_inv]
          exact hQI (Q.inv_mem (hZ0.comm_mem hz (hLR hl)))
      have hzA2 : z ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t :=
        (h10 z hzN).mpr fun l hl => by
          rw [← commutatorElement_inv]
          exact hQI (Q.inv_mem (hZ0.comm_mem hz (hL'R hl)))
      rw [← hinf]
      exact ⟨hzA1, hzA2⟩
  refine ⟨r, hr, by rw [hcard], ?_, hIZ⟩
  rw [hIZ] at hopp
  exact hopp

theorem sec8_Z0_le_LB (h51 : Stroth51Statement) (hA : Sec8AExistsStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : Z0 ≤ LB M Q B := by
  obtain ⟨r, -, -, -, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  rw [← hIZ]
  exact inf_le_left

theorem sec86ZCard_of_51 (h51 : Stroth51Statement) (hA : Sec8AExistsStatement) :
    Sec86ZCardStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0
  obtain ⟨r, -, hcard, -, hIZ⟩ := sec8_Z0_data h51 hA hc hs hZ0
  rw [← hIZ]
  exact hcard

theorem sec8_not_forall_normalizer (h82 : Stroth82Statement) (hConj : Sec86ConjStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    ¬ ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∈ Subgroup.normalizer (Z0 : Set G) := by
  intro hall
  have hZN : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  obtain ⟨s, hsR, hsc, g, hg, hgL, hgN⟩ := h82 G M Q Z B hc n t hs
  have hsZ0 : s ∈ Z0 := (hZ0 s).mpr ⟨hsR, hsc⟩
  have hsM : s ∈ M := hc.Rt_le_M t hsR
  have hxM : g * s * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hsM) (M.inv_mem hg)
  have hconj : ConjMod M Q s (g * s * g⁻¹) := ⟨hxM, g, hg, by simp [Q.one_mem]⟩
  obtain ⟨ν, hνM, hνL, hνQ⟩ := hConj G M Q Z B hc n t hs Z0 hZ0 s hsZ0 _ hgL hconj
  have hνs : ν * s * ν⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp (hall ν hνM hνL) s).mp hsZ0
  have hgs : g * s * g⁻¹ ∈ Z0 := by
    have e : g * s * g⁻¹ = (g * s * g⁻¹ * (ν * s * ν⁻¹)⁻¹) * (ν * s * ν⁻¹) := by group
    rw [e]
    exact Z0.mul_mem (hQZ0 hνQ) hνs
  exact hgN (hZN hgs)

end CFSG.RankThree.GF2n.Stroth80
