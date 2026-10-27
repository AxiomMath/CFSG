module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Count
public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive
public import CFSG.RankThree.GF2n.Stroth80.Sec83CommSect
public import CFSG.RankThree.GF2n.Stroth80.Sec83ChiEndo

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.F2Fixed
open scoped commutatorElement Matrix


theorem sec83_lower_arith {q a b r v : ℕ} (h : a ^ 2 * b ≤ r * v) :
    (q * a) ^ 2 * (b * q) ≤ q * r * q * (v * q) :=
  calc (q * a) ^ 2 * (b * q) = q ^ 3 * (a ^ 2 * b) := by ring
    _ ≤ q ^ 3 * (r * v) := Nat.mul_le_mul_left _ h
    _ = q * r * q * (v * q) := by ring

theorem sec83Lower_of_53 (h53 : Stroth53Statement) (hInv : Sec8InvStatement) :
    Sec83LowerStatement := by
  intro G _ _ M Q Z B hc n t h8 r hr z hzL
  classical
  have hs := h8.toSec5
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hzR : z ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem hzL
  have hinv := hInv G M Q Z B hc n t h8 r hr
  have hcd := h53.2.2.1 G M Q Z B hc n t hs h8.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have he := h53.2.2.2.2 G M Q Z B hc n t hs h8.spNat (Rt M (LB M Q B) t)
    (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx =>
    ⟨hc.Z_le_Q hx, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hx (hVQ hv)).symm⟩
  have hVV₁ : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hV₁W₁ : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hcd.1.trans hcd.2.1
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hW₁W : Sec8W1 M Q Z B t r ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_iff.mp hx.2 v (hVV₁ hv)⟩
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := hV₁W₁.trans hW₁Q
  have hZV₁ : Z ≤ Sec8V1 M Q Z B t r := hZV.trans hVV₁
  have hZW₁ : Z ≤ Sec8W1 M Q Z B t r := hZV₁.trans hV₁W₁
  have hPQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) x).mp hx
  have hsecQ : SecHyp (Rt M (LB M Q B) t) Q Z :=
    ⟨hc.Z_le_Q, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy,
      fun x hx => hc.hyp.toHyp79.sq_mem_V hx, hPQ, fun ρ hρ x hx =>
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hc.Rt_le_M t hρ)) x).mp hx⟩
  obtain ⟨Mod, iM, iA, κ, hκ⟩ := exists_sectionModule hsecQ
  haveI : Finite Mod := hκ.finite
  obtain ⟨ε, -, hεker, hεrange, hεeq⟩ := exists_chi_endo hκ he hVQ hZW hZV hPQ
  have hVz : ∀ x ∈ Vt M (LB M Q B) B Z t, z * x * z⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt hs.mem hzR) x).mp hx
  have hW₁z : ∀ x ∈ Sec8W1 M Q Z B t r, z * x * z⁻¹ ∈ Sec8W1 M Q Z B t r := fun x hx =>
    conj_mem_of_conjSubgroup_eq (hinv z hzR).2 hx
  have hW₁z' : ∀ x ∈ Sec8W1 M Q Z B t r, z⁻¹ * x * z ∈ Sec8W1 M Q Z B t r := fun x hx => by
    simpa using conj_mem_of_conjSubgroup_eq (hinv z⁻¹ (Subgroup.inv_mem _ hzR)).2 hx
  have hsecinv : ∀ U : Subgroup G, conjSubgroup z U = U →
      ∀ a ∈ secSub κ U, (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) • a ∈ secSub κ U := by
    intro U hU a ha
    have h1 := secSub_conjSubgroup hPQ hκ (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) U
    rw [hU] at h1
    rw [h1]
    exact ⟨a, ha, rfl⟩
  have hδinv : ∀ U : Subgroup G, conjSubgroup z U = U →
      ∀ a ∈ secSub κ U, comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) a ∈ secSub κ U := by
    intro U hU a ha
    rw [comm_apply]
    exact (secSub κ U).sub_mem (hsecinv U hU a ha) ha
  have hcomm : ∀ a, ε (comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) a) =
      comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)) (ε a) := by
    intro a
    rw [comm_apply, comm_apply, map_sub, hεeq]
  have hadd := sec83_lower_additive (comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t))) ε hcomm
    (V := secSub κ (Vt M (LB M Q B) B Z t)) (V₁ := secSub κ (Sec8V1 M Q Z B t r))
    (W₁ := secSub κ (Sec8W1 M Q Z B t r)) hεrange.symm (secSub_mono hVV₁) (secSub_mono hV₁W₁)
    ((secSub_mono hW₁W).trans hεker.ge) (hδinv _ (hinv z hzR).1) (hδinv _ (hinv z hzR).2)
  have hcommQ : ∀ U : Subgroup G, U ≤ Q → ⁅U, Subgroup.zpowers z⁆ ≤ Q := by
    intro U hU
    rw [Subgroup.commutator_le]
    intro h hh k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hn : z ^ m ∈ Rt M (LB M Q B) t := zpow_mem hzR m
    have e : h * z ^ m * h⁻¹ * (z ^ m)⁻¹ = h * (z ^ m * h⁻¹ * (z ^ m)⁻¹) := by group
    rw [commutatorElement_def, e]
    exact Q.mul_mem (hU hh) (hPQ _ hn _ (Q.inv_mem (hU hh)))
  have hcV : Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) =
      Nat.card ↥Z * Nat.card ↥((secSub κ (Vt M (LB M Q B) B Z t)).map
        (comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t)))) :=
    natCard_commutator_sup_of_le hκ hPQ hZV hVQ ⟨z, hzR⟩ hVz
  have hcQ : Nat.card ↥(Ut Q Z z) = Nat.card ↥Z *
      Nat.card ↥(comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t))).range :=
    natCard_commutator_sup hκ hPQ hc.Z_le_Q ⟨z, hzR⟩
  have hsecW₁ : secSub κ (CommSec (Sec8W1 M Q Z B t r) Z z) =
      (secSub κ (Sec8W1 M Q Z B t r)).map (comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t))) :=
    secSub_commutator_sup hκ hPQ hZW₁ hW₁Q ⟨z, hzR⟩ hW₁z hW₁z'
  have hCW : CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z =
      CommSec (Sec8W1 M Q Z B t r) Z z ⊔ Sec8V1 M Q Z B t r :=
    le_antisymm (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (sup_le (sup_le le_sup_left (hZV₁.trans le_sup_right)) le_sup_right)
  have hCWQ : CommSec (Sec8W1 M Q Z B t r) Z z ≤ Q :=
    sup_le (hcommQ _ hW₁Q) hc.Z_le_Q
  have hsecCW : secSub κ (CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) =
      (secSub κ (Sec8W1 M Q Z B t r)).map (comm Mod (⟨z, hzR⟩ : ↥(Rt M (LB M Q B) t))) ⊔
        secSub κ (Sec8V1 M Q Z B t r) := by
    rw [hCW, secSub_sup hCWQ hV₁Q, hsecW₁]
  have hcardCW : Nat.card ↥(secSub κ (CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z)) *
      Nat.card ↥Z = Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) :=
    natCard_secSub_mul hc.Z_le_Q hκ (hZV₁.trans le_sup_right)
      (sup_le (hcommQ _ hW₁Q) hV₁Q)
  have hcardV₁ := natCard_secSub_mul hc.Z_le_Q hκ hZV₁ hV₁Q
  rw [← hcardCW, hsecCW, ← hcardV₁, hcV, hcQ]
  exact sec83_lower_arith hadd

end CFSG.RankThree.GF2n.Stroth80
