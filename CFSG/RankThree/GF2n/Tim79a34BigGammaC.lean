module

public import CFSG.RankThree.GF2n.Tim79a34BigAssembly
public import CFSG.RankThree.GF2n.Tim79a34BigGammaBasic
import CFSG.RankThree.GF2n.Tim79a34BigIWProof
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} {n f : ℕ}
  {Φ : ↥(StatedSp n (GaloisField 2 f)) ≃* Xbar V H}
  {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
  {a : Fin n ⊕ Fin n → GaloisField 2 f} {T : Subgroup ↥(StatedSp n (GaloisField 2 f))}

set_option hygiene false in
local notation "ψG " v:max => ((Additive.toMul (ψ v) : ↥(wOf V H)) : G)

theorem BigEndHyp.commutator_mem_wOf_of_mem_centralizer [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H) {c x : G}
    (hc : c ∈ Q ⊓ Subgroup.centralizer (wOf V H : Set G)) (hx : x ∈ xOf V H) :
    ⁅x, c⁆ ∈ wOf V H := by
  have hVH : V ≤ H := h.setup.mc.toMinCex.V_le_H
  have hxN : x ∈ Subgroup.normalizer (wOf V H : Set G) :=
    H_le_normalizer_wOf V H (xOf_le_H hVH hx)
  have hy1 : x * c * x⁻¹ ∈ Subgroup.centralizer (wOf V H : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hxN) c).mp hc.2
  have hy : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.centralizer (wOf V H : Set G) :=
    (Subgroup.centralizer (wOf V H : Set G)).mul_mem hy1
      ((Subgroup.centralizer (wOf V H : Set G)).inv_mem hc.2)
  have hyX : x * c * x⁻¹ * c⁻¹ ∈ xOf V H := by
    have hzX : c * x⁻¹ * c⁻¹ ∈ xOf V H := by
      rw [← hQX c hc.1, mem_conjSubgroup]
      have e : c⁻¹ * (c * x⁻¹ * c⁻¹) * c = x⁻¹ := by group
      rw [e]
      exact (xOf V H).inv_mem hx
    simpa [mul_assoc] using (xOf V H).mul_mem hx hzX
  have := BigEndHyp.mem_wOf_of_commute h hZ hyX
    (fun w hw => (Subgroup.mem_centralizer_iff.mp hy w hw).symm)
  rwa [commutatorElement_def]

theorem BigEndHyp.eq_one_of_forall_commute_xOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) {z : G}
    (hz : ∀ x ∈ xOf V H, z * x = x * z) : z = 1 := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hPX : P ≤ xOf V H := BigEndHyp.P_le_xOf h hZ
  have hPz : z ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun p hp => (hz p (hPX hp)).symm
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  have hPC := bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ hIW
  have hzV : z ∈ V := by
    simpa [hPC.2.2] using hPz
  have hzX : z ∈ xOf V H := le_xOf (V_mem_omegaOf V H) hzV
  have hzW : ∀ w ∈ wOf V H, z * w = w * z :=
    fun w hw => hz w (wOf_le_xOf V H hw)
  have hzmemW : z ∈ wOf V H := BigEndHyp.mem_wOf_of_commute h hZ hzX hzW
  have hzC : z ∈ Subgroup.centralizer (xOf V H : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hz x hx).symm
  have hbot : z ∈ wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) := ⟨hzmemW, hzC⟩
  rw [hc.wOf_inf_centralizer_xOf_eq_bot] at hbot
  exact Subgroup.mem_bot.mp hbot

private theorem gammaC_sq_commute_xOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H)
    {c x : G} (hc : c ∈ Q ⊓ Subgroup.centralizer (wOf V H : Set G))
    (hx : x ∈ xOf V H) : c * c * x = x * (c * c) := by
  have hxc : x * c * x⁻¹ = ⁅x, c⁆ * c := by
    rw [commutatorElement_def]
    group
  have hw : ⁅x, c⁆ ∈ wOf V H :=
    BigEndHyp.commutator_mem_wOf_of_mem_centralizer h hZ hQX hc hx
  have hwc : ⁅x, c⁆ * c = c * ⁅x, c⁆ :=
    Subgroup.mem_centralizer_iff.mp hc.2 ⁅x, c⁆ hw
  have hw2 : ⁅x, c⁆ * ⁅x, c⁆ = 1 :=
    h.setup.mc.toMinCex.wOf_isElemAbelian.mul_self_eq_one hw
  have hconj : x * (c * c) * x⁻¹ = c * c := by
    have e : x * (c * c) * x⁻¹ = (x * c * x⁻¹) * (x * c * x⁻¹) := by group
    rw [e, hxc]
    calc (⁅x, c⁆ * c) * (⁅x, c⁆ * c) = ⁅x, c⁆ * (c * ⁅x, c⁆) * c := by group
      _ = ⁅x, c⁆ * (⁅x, c⁆ * c) * c := by rw [← hwc]
      _ = (⁅x, c⁆ * ⁅x, c⁆) * (c * c) := by group
      _ = c * c := by rw [hw2, one_mul]
  calc c * c * x = (x * (c * c) * x⁻¹) * x := by rw [hconj]
    _ = x * (c * c) := by group

theorem BigEndHyp.isElemAbelian_inf_centralizer [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H) :
    Assembly.IsElemAbelian 2 (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) := by
  let C : Subgroup G := Q ⊓ Subgroup.centralizer (wOf V H : Set G)
  have hCXW : ⁅C, xOf V H⁆ ≤ wOf V H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr fun x hx c hc =>
      BigEndHyp.commutator_mem_wOf_of_mem_centralizer h hZ hQX hc hx
  have hCCbot : ⁅C, C⁆ = ⊥ := by
    have h1 : ⁅⁅C, xOf V H⁆, C⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hzW : z ∈ wOf V H := hCXW hz
      exact (Subgroup.mem_centralizer_iff.mp hy.2 z hzW).symm
    have h2 : ⁅⁅xOf V H, C⁆, C⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (xOf V H) C]
      exact h1
    have h3 : ⁅⁅C, C⁆, xOf V H⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := C) (H₂ := C)
        (H₃ := xOf V H) h1 h2
    have hCCcent : ⁅C, C⁆ ≤ Subgroup.centralizer (xOf V H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
    rw [eq_bot_iff]
    intro z hz
    have hzX : ∀ x ∈ xOf V H, z * x = x * z := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hCCcent hz) x hx).symm
    have hz1 : z = 1 := eq_one_of_forall_commute_xOf h hZ hzX
    simpa [hz1]
  change Assembly.IsElemAbelian 2 C
  refine ⟨Subgroup.commutator_self_eq_bot_iff.mp hCCbot, fun c hc => ?_⟩
  rw [pow_two]
  exact eq_one_of_forall_commute_xOf h hZ fun x hx => gammaC_sq_commute_xOf h hZ hQX hc hx

private theorem gammaC_K_le [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H) :
    ∃ K : Subgroup G, P ≤ K ∧ Q ⊓ Subgroup.centralizer (wOf V H : Set G) ≤ K ∧
      ∀ x, x ∈ K ↔ x ∈ Q ∧ ∀ p ∈ P, ⁅p, x⁆ ∈ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hPX : P ≤ xOf V H := BigEndHyp.P_le_xOf h hZ
  have hPP : ⁅P, P⁆ = V ⊓ wOf V H :=
    (bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ
      (bigIWStatement_holds G M V Q P H h hZ)).1
  let K : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ ∀ p ∈ P, ⁅p, x⁆ ∈ wOf V H}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hxQ, hx⟩ := hx
        obtain ⟨hyQ, hy⟩ := hy
        refine ⟨Q.mul_mem hxQ hyQ, fun p hp => ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hxN : x ∈ Subgroup.normalizer (wOf V H : Set G) :=
          mem_normalizer_iff_conjSubgroup_eq.mpr (hQW x hxQ)
        have hxy : x * ⁅p, y⁆ * x⁻¹ ∈ wOf V H :=
          (Subgroup.mem_normalizer_iff.mp hxN ⁅p, y⁆).mp (hy p hp)
        simpa [mul_assoc] using (wOf V H).mul_mem (hx p hp) hxy
      one_mem' := ⟨Q.one_mem, by intro p hp; simp⟩
      inv_mem' := by
        intro x hx
        obtain ⟨hxQ, hx⟩ := hx
        refine ⟨Q.inv_mem hxQ, fun p hp => ?_⟩
        rw [commutatorElement_inv_right]
        have hxN : x⁻¹ ∈ Subgroup.normalizer (wOf V H : Set G) :=
          mem_normalizer_iff_conjSubgroup_eq.mpr (hQW x⁻¹ (Q.inv_mem hxQ))
        have hxp : ⁅x, p⁆ ∈ wOf V H := by
          simpa [commutatorElement_inv] using (wOf V H).inv_mem (hx p hp)
        simpa using (Subgroup.mem_normalizer_iff.mp hxN ⁅x, p⁆).mp hxp }
  refine ⟨K, ?_, ?_, fun x => Iff.rfl⟩
  · intro p hp
    change p ∈ Q ∧ ∀ q ∈ P, ⁅q, p⁆ ∈ wOf V H
    refine ⟨hc.P_le_Q hp, fun q hq => ?_⟩
    have hmem : ⁅q, p⁆ ∈ ⁅P, P⁆ := Subgroup.commutator_mem_commutator hq hp
    rw [hPP] at hmem
    exact hmem.2
  · intro c hcC
    change c ∈ Q ∧ ∀ p ∈ P, ⁅p, c⁆ ∈ wOf V H
    exact ⟨hcC.1, fun p hp =>
      BigEndHyp.commutator_mem_wOf_of_mem_centralizer h hZ hQX hcC (hPX hp)⟩

theorem BigEndHyp.commutator_P_le_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H)
    (hQPC : P ⊔ (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) = Q) :
    ⁅P, Q⁆ ≤ P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hQM : Q ≤ M := hc.Q_le_M
  have hPQP : ⁅P, Q⁆ ≤ P :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQM.trans hc.M_le_normalizer_P)
  obtain ⟨K, hPK, hCK, hKm⟩ := gammaC_K_le h hZ hQW hQX
  have hQK : Q ≤ K := by
    rw [← hQPC]
    exact sup_le hPK hCK
  refine le_inf hPQP ?_
  rw [Subgroup.commutator_le]
  intro p hp q hq
  exact ((hKm q).mp (hQK hq)).2 p hp

private theorem not_inf_wOf_le_commutator_P_Q [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H)
    (hQPC : P ⊔ (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) = Q)
    (hmax : ¬ M ≤ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G)) :
    ¬ (P ⊓ wOf V H ≤ ⁅P, Q⁆) := by
  intro hle
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hEq : P ⊓ wOf V H = ⁅P, Q⁆ :=
    le_antisymm hle (BigEndHyp.commutator_P_le_inf_wOf h hZ hQW hQX hQPC)
  have hQN : M ≤ Subgroup.normalizer (Q : Set G) := hc.M_le_normalizer_Q
  have hMN : M ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
    intro m hm
    rw [mem_normalizer_iff_conjSubgroup_eq]
    have hP : conjSubgroup m P = P :=
      mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hm)
    have hQ : conjSubgroup m Q = Q := mem_normalizer_iff_conjSubgroup_eq.mp (hQN hm)
    unfold conjSubgroup at hP hQ ⊢
    rw [Subgroup.map_commutator, hP, hQ]
  exact hmax (hEq.symm ▸ hMN)

private theorem gammaC_conj_S_eq [Finite G] (hc : MinCex M V Q P H) {r : G} (hrX : r ∈ xOf V H)
    (hrV : r ∈ Subgroup.centralizer (V : Set G)) :
    conjSubgroup r (⁅P, Q ⊓ Subgroup.centralizer (wOf V H : Set G)⁆ ⊔ (V ⊓ wOf V H)) =
      ⁅P, Q ⊓ Subgroup.centralizer (wOf V H : Set G)⁆ ⊔ (V ⊓ wOf V H) := by
  have hrN : r ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G) hrV
  have hrM : r ∈ M := hc.normalizer_eq ▸ hrN
  have hrP : conjSubgroup r P = P :=
    mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hrM)
  have hrV' : conjSubgroup r V = V := mem_normalizer_iff_conjSubgroup_eq.mp hrN
  have hrW : conjSubgroup r (wOf V H) = wOf V H :=
    mem_normalizer_iff_conjSubgroup_eq.mp
      (H_le_normalizer_wOf V H (xOf_le_H hc.V_le_H hrX))
  have hrQ : conjSubgroup r Q = Q :=
    mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_Q hrM)
  have hrNW : r ∈ Subgroup.normalizer (wOf V H : Set G) :=
    mem_normalizer_iff_conjSubgroup_eq.mpr hrW
  have hrC : conjSubgroup r (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) =
      Q ⊓ Subgroup.centralizer (wOf V H : Set G) := by
    have h := mem_normalizer_inf
      (mem_normalizer_iff_conjSubgroup_eq.mpr hrQ) (mem_normalizer_centralizer hrNW)
    exact mem_normalizer_iff_conjSubgroup_eq.mp h
  have hrA : conjSubgroup r (V ⊓ wOf V H) = V ⊓ wOf V H := by
    rw [conjSubgroup_inf, hrV', hrW]
  unfold conjSubgroup at hrP hrC hrA ⊢
  rw [Subgroup.map_sup, Subgroup.map_commutator, hrP, hrC, hrA]

theorem BigEndHyp.commutator_mem_inf_of_mem_P_of_mem_centralizer [Finite G]
    (h : BigEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H)
    (hQPC : P ⊔ (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) = Q)
    (hirr : ∀ S : Subgroup G, V ⊓ wOf V H ≤ S → S ≤ P ⊓ wOf V H →
      (∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ s ∈ S, r * s * r⁻¹ ∈ S) →
        S = V ⊓ wOf V H ∨ S = P ⊓ wOf V H)
    (hmax : ¬ M ≤ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G)) {p c : G}
    (hp : p ∈ P) (hc : c ∈ Q ⊓ Subgroup.centralizer (wOf V H : Set G)) :
    ⁅p, c⁆ ∈ V ⊓ wOf V H := by
  have hc' : MinCex M V Q P H := h.setup.mc.toMinCex
  let C : Subgroup G := Q ⊓ Subgroup.centralizer (wOf V H : Set G)
  let S : Subgroup G := ⁅P, C⁆ ⊔ (V ⊓ wOf V H)
  have hPP : ⁅P, P⁆ = V ⊓ wOf V H :=
    (bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ
      (bigIWStatement_holds G M V Q P H h hZ)).1
  have hAle : V ⊓ wOf V H ≤ S := le_sup_right
  have hSle : S ≤ P ⊓ wOf V H := by
    refine sup_le ?_ ?_
    · exact (Subgroup.commutator_mono le_rfl inf_le_left).trans
        (commutator_P_le_inf_wOf h hZ hQW hQX hQPC)
    · refine le_inf ?_ inf_le_right
      rw [← hPP]
      exact Subgroup.commutator_le_self P
  have hRinv : ∀ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G), ∀ s ∈ S,
      r * s * r⁻¹ ∈ S := by
    intro r hr s hs
    have hconjS : conjSubgroup r S = S := gammaC_conj_S_eq hc' hr.1 hr.2
    have hmem : r * s * r⁻¹ ∈ conjSubgroup r S := by
      rw [mem_conjSubgroup]
      have e : r⁻¹ * (r * s * r⁻¹) * r = s := by group
      rw [e]
      exact hs
    rwa [hconjS] at hmem
  rcases hirr S hAle hSle hRinv with hS | hS
  · have hmem : ⁅p, c⁆ ∈ S :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hp hc)
    rwa [hS] at hmem
  · exfalso
    have hle : P ⊓ wOf V H ≤ ⁅P, Q⁆ := by
      rw [← hS]
      refine sup_le ?_ ?_
      · exact Subgroup.commutator_mono le_rfl (show C ≤ Q from inf_le_left)
      · rw [← hPP]
        exact Subgroup.commutator_mono le_rfl hc'.P_le_Q
    exact not_inf_wOf_le_commutator_P_Q h hZ hQW hQX hQPC hmax hle

theorem BigEndHyp.inf_wOf_le_P [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥)
    (hQW : ∀ x ∈ Q, conjSubgroup x (wOf V H) = wOf V H)
    (hQX : ∀ x ∈ Q, conjSubgroup x (xOf V H) = xOf V H)
    (hQPC : P ⊔ (Q ⊓ Subgroup.centralizer (wOf V H : Set G)) = Q)
    (hcov : ∀ b ∈ wOf V H, b ∉ P → ∀ w ∈ P ⊓ wOf V H, ∃ p ∈ P, ⁅p, b⁆ = w)
    (hmax : ¬ M ≤ Subgroup.normalizer ((P ⊓ wOf V H : Subgroup G) : Set G)) :
    Q ⊓ wOf V H ≤ P := by
  have hne := not_inf_wOf_le_commutator_P_Q h hZ hQW hQX hQPC hmax
  intro b hb
  by_contra hbP
  have hle : P ⊓ wOf V H ≤ ⁅P, Q⁆ := by
    intro w hw
    obtain ⟨p, hp, heq⟩ := hcov b hb.2 hbP w hw
    rw [← heq]
    exact Subgroup.commutator_mem_commutator hp hb.1
  exact hne hle

end CFSG.RankThree.GF2n.Tim79a
