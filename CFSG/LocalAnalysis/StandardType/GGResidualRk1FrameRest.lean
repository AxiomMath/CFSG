module

public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724
public import Certificates.Certificate709545
public import Certificates.Certificate709548
public import Certificates.Certificate709549
public import Certificates.Certificate709590
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
import CFSG.LocalAnalysis.StandardType.GGOrthModelInputsHold
import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenPhan
import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGSignedRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
import CFSG.LocalAnalysis.StandardType.GGResidualGenFrameRest
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameTwoSwap
import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoCenter
import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE
import CFSG.LocalAnalysis.StandardType.GGRk1ConclExSix
import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwo
import CFSG.LocalAnalysis.StandardType.GGExcPhanPayloadRk1
import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcConj
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankOne
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwoMember

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Universal Multiplicative

namespace SpCoord

variable {p k : ℕ}

private theorem rk1All_sgnAut_self (i : Fin k) (f : Fin k → Multiplicative (ZMod p)) :
    sgnAut i f i = (f i)⁻¹ := by
  rw [sgnAut_apply, Function.update_self]

private theorem rk1All_sgnAut_ne {i m : Fin k} (h : m ≠ i) (f : Fin k → Multiplicative (ZMod p)) :
    sgnAut i f m = f m := by
  rw [sgnAut_apply, Function.update_of_ne h]

private theorem rk1All_permAut_swap (i j m : Fin k) (f : Fin k → Multiplicative (ZMod p)) :
    permAut (Equiv.swap i j) f m = f (Equiv.swap i j m) := by
  rw [permAut_apply, Equiv.swap_inv, Function.comp_apply]

theorem sgnAut_mul_sgnAut_involutive (i l : Fin k) (f : Fin k → Multiplicative (ZMod p)) :
    (sgnAut i * sgnAut l : MulAut (Fin k → Multiplicative (ZMod p)))
      ((sgnAut i * sgnAut l : MulAut (Fin k → Multiplicative (ZMod p))) f) = f := by
  funext m
  simp only [MulAut.mul_apply]
  by_cases hmi : m = i
  · by_cases hml : m = l
    · subst hmi
      subst hml
      simp only [rk1All_sgnAut_self, inv_inv]
    · rw [hmi] at hml ⊢
      simp only [rk1All_sgnAut_self, rk1All_sgnAut_ne hml, inv_inv]
  · by_cases hml : m = l
    · rw [hml] at hmi ⊢
      simp only [rk1All_sgnAut_ne hmi, rk1All_sgnAut_self, inv_inv]
    · simp only [rk1All_sgnAut_ne hmi, rk1All_sgnAut_ne hml]

theorem sgnAut_conj_swap {i j l : Fin k} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    (f : Fin k → Multiplicative (ZMod p)) :
    (sgnAut i * sgnAut l : MulAut (Fin k → Multiplicative (ZMod p)))
        (permAut (Equiv.swap i j) ((sgnAut i * sgnAut l : MulAut (Fin k → Multiplicative (ZMod p))) f)) =
      (sgnAut i * sgnAut j * permAut (Equiv.swap i j) : MulAut (Fin k → Multiplicative (ZMod p))) f := by
  simp only [MulAut.mul_apply]
  funext m
  by_cases hmi : m = i
  · rw [hmi]
    simp only [rk1All_sgnAut_self, rk1All_sgnAut_ne (Ne.symm hli), rk1All_permAut_swap, Equiv.swap_apply_left,
      rk1All_sgnAut_ne (Ne.symm hij), rk1All_sgnAut_ne (Ne.symm hlj), rk1All_sgnAut_ne hij]
  · by_cases hmj : m = j
    · rw [hmj]
      simp only [rk1All_sgnAut_ne (Ne.symm hij), rk1All_sgnAut_ne (Ne.symm hlj), rk1All_sgnAut_self,
        rk1All_permAut_swap, Equiv.swap_apply_right, rk1All_sgnAut_ne (Ne.symm hli)]
    · by_cases hml : m = l
      · rw [hml]
        simp only [rk1All_sgnAut_ne hli, rk1All_sgnAut_self, rk1All_permAut_swap,
          Equiv.swap_apply_of_ne_of_ne hli hlj, inv_inv, rk1All_sgnAut_ne hlj]
      · simp only [rk1All_sgnAut_ne hmi, rk1All_sgnAut_ne hml, rk1All_sgnAut_ne hmj, rk1All_permAut_swap,
          Equiv.swap_apply_of_ne_of_ne hmi hmj]

theorem sgnAut_mul_swap_pow_ne_one (hp : p.Prime) (hp2 : p ≠ 2) {a b : Fin k} (hab : a ≠ b) :
    (sgnAut a * permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))) ^ 2 ≠ 1 ∧
      (sgnAut a * permAut (Equiv.swap a b) : MulAut (Fin k → Multiplicative (ZMod p))) ^ 3 ≠ 1 := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  set u : MulAut (Fin k → Multiplicative (ZMod p)) := sgnAut a * permAut (Equiv.swap a b) with hu
  have hua : ∀ f, u f a = (f b)⁻¹ := fun f => by
    rw [hu, MulAut.mul_apply, rk1All_sgnAut_self, rk1All_permAut_swap, Equiv.swap_apply_left]
  have hub : ∀ f, u f b = f a := fun f => by
    rw [hu, MulAut.mul_apply, rk1All_sgnAut_ne hab.symm, rk1All_permAut_swap, Equiv.swap_apply_right]
  set δ : Fin k → Multiplicative (ZMod p) := Pi.mulSingle a (ofAdd 1) with hδ
  have hδa : δ a = ofAdd 1 := Pi.mulSingle_eq_same a _
  have hδb : δ b = 1 := Pi.mulSingle_eq_of_ne hab.symm _
  constructor
  · intro h
    have h1 := congrFun (congrArg (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) => φ δ) h) a
    simp only [sq, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hua, hub, hδa] at h1
    have h2 := congrArg toAdd h1
    rw [toAdd_inv, toAdd_ofAdd] at h2
    exact coord_two_ne_zero hp hp2 (by linear_combination -h2)
  · intro h
    have h1 := congrFun (congrArg (fun φ : MulAut (Fin k → Multiplicative (ZMod p)) => φ δ) h) a
    simp only [pow_three, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hua, hub, hua, inv_inv, hδb, hδa] at h1
    have h2 := congrArg toAdd h1
    rw [toAdd_one, toAdd_ofAdd] at h2
    exact one_ne_zero h2.symm

end SpCoord

theorem ggInducedBy_pow_apply {G : Type} [Group G] {Bs : Subgroup G} {φ : MulAut ↥Bs} {g : G}
    (h : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) (n : ℕ) (b : ↥Bs) :
    (((φ ^ n) b : ↥Bs) : G) = g ^ n * b * (g ^ n)⁻¹ := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ φ n, MulAut.mul_apply, ih, h, pow_succ g n]
    group

theorem conj_pow_apply_of_forall {R M : Type} [Group R] [Group M] {τ : M →* R} {v : R} {u : MulAut M}
    (h : ∀ f, v * τ f * v⁻¹ = τ (u f)) (n : ℕ) (f : M) : v ^ n * τ f * (v ^ n)⁻¹ = τ ((u ^ n) f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ u n, MulAut.mul_apply, ← ih, ← h, pow_succ v n]
    group

theorem ggRowP_Rk1Rest_dvd_tag {nb tA tD ltB : Prop} {p : ℕ} {lab : LargeEvenLabel}
    (h : ggRowP_Rk1Rest nb tA tD ltB p lab) :
    p ∣ 2 ^ lab.n + 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
  rcases h with ⟨-, -, ⟨ht, hd⟩, -⟩ | ⟨-, ⟨ht, -, -, hd⟩, -, -, -, -⟩ <;>
    refine ⟨hd, by rw [ht]; decide, fun ht' => ?_⟩ <;> rw [ht] at ht' <;> exact absurd ht' (by decide)

section Proofs

namespace OrthTorus

open SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

variable {p : ℕ} {G : Type} [Group G] {Bs X : Subgroup G}

theorem OrthWeakFrame.eq_one_of_central (Φ : OrthWeakFrame p Bs X) (hΦ : Φ.Recognized)
    {z : ↥(orthDerived Φ.Q)} (hz : ∀ y, z * y = y * z) : z = 1 := by
  have key : ∀ {K : Type} [Group K], Subgroup.center K = ⊥ → Nonempty (K ≃* ↥(orthDerived Φ.Q)) → z = 1 := by
    intro K _ hK ⟨e⟩
    have hc : e.symm z ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact (hz (e y)).symm
    rw [hK, Subgroup.mem_bot] at hc
    have h := congrArg e hc
    simpa using h
  rcases Nat.even_or_odd Φ.r with hev | hodd
  · exact key (center_lieUniversal_POmegaPlus (by have := Φ.hr; omega) Φ.f) (hΦ.1 hev)
  · exact key (center_lieUniversal_POmegaMinus Φ.hr Φ.f) (hΦ.2.1 hodd)

theorem OrthFrameCore.mem_A_iff (Φ : OrthFrameCore p Bs X) (y : ↥(orthDerived Φ.Q)) :
    (y : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.A ↔ ∃ b : ↥Bs, Φ.β b = y := by
  constructor
  · intro hy
    obtain ⟨b, hb⟩ := Φ.hβsurj _ hy
    exact ⟨b, Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    exact Φ.hβA b

theorem OrthFrameCore.mem_range_tauΩ_iff (Φ : OrthFrameCore p Bs X) (y : ↥(orthDerived Φ.Q)) :
    y ∈ (Φ.Δ.τΩ Φ.hA).range ↔ (y : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.A := by
  constructor
  · rintro ⟨f, rfl⟩
    rw [tbjA_coe_tauOmega]
    have h : Φ.Δ.τ f ∈ Φ.Δ.τ.range := MonoidHom.mem_range.mpr ⟨f, rfl⟩
    rwa [Φ.Δ.τ_range] at h
  · intro hy
    rw [← Φ.Δ.τ_range] at hy
    obtain ⟨f, hf⟩ := hy
    exact ⟨f, Subtype.ext (by rw [tbjA_coe_tauOmega]; exact hf)⟩

theorem OrthFrameCore.range_beta (Φ : OrthFrameCore p Bs X) : Φ.β.range = (Φ.Δ.τΩ Φ.hA).range := by
  ext y
  rw [Φ.mem_range_tauΩ_iff, Φ.mem_A_iff, MonoidHom.mem_range]

theorem OrthFrameCore.beta_conj (Φ : OrthFrameCore p Bs X)
    (hZ : ∀ z : ↥(orthDerived Φ.Q), (∀ y, z * y = y * z) → z = 1) {w : ↥(orthDerived Φ.Q)}
    {b b' : ↥Bs} (h : Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ = (b' : G)) : w * Φ.β b * w⁻¹ = Φ.β b' := by
  have hc : ∀ y, ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) * y = y * ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) := by
    intro y
    have h1 : Φ.ψ (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹) = Φ.ψ (Φ.β b' * y * (Φ.β b')⁻¹) := by
      calc Φ.ψ (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹)
          = Φ.ψ w * Φ.ψ (Φ.β b * (w⁻¹ * y * w) * (Φ.β b)⁻¹) * (Φ.ψ w)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = Φ.ψ w * ((b : G) * Φ.ψ (w⁻¹ * y * w) * (b : G)⁻¹) * (Φ.ψ w)⁻¹ := by rw [Φ.hcompat]
        _ = (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹) * Φ.ψ y * (Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹)⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = (b' : G) * Φ.ψ y * (b' : G)⁻¹ := by rw [h]
        _ = Φ.ψ (Φ.β b' * y * (Φ.β b')⁻¹) := (Φ.hcompat b' y).symm
    have h2 := Φ.hinj h1
    calc ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) * y
        = (Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹ * y * (w * Φ.β b * w⁻¹)⁻¹) * (w * Φ.β b * w⁻¹) := by group
      _ = (Φ.β b')⁻¹ * (Φ.β b' * y * (Φ.β b')⁻¹) * (w * Φ.β b * w⁻¹) := by rw [h2]
      _ = y * ((Φ.β b')⁻¹ * (w * Φ.β b * w⁻¹)) := by group
  exact (inv_mul_eq_one.mp (hZ _ hc)).symm

theorem OrthFrameCore.aut_eq_of_tau (Φ : OrthFrameCore p Bs X) {w w' : ↥(orthDerived Φ.Q)}
    {a a' : MulAut ↥Bs} (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹)
    (ha' : ∀ b : ↥Bs, ((a' b : ↥Bs) : G) = Φ.ψ w' * b * (Φ.ψ w')⁻¹)
    (h : ∀ f, w * Φ.Δ.τΩ Φ.hA f * w⁻¹ = w' * Φ.Δ.τΩ Φ.hA f * w'⁻¹) : a = a' := by
  refine MulEquiv.ext fun b => Subtype.ext ?_
  obtain ⟨f, hf⟩ : ∃ f, Φ.Δ.τΩ Φ.hA f = Φ.β b := by
    have hb : Φ.β b ∈ (Φ.Δ.τΩ Φ.hA).range := by
      rw [← Φ.range_beta]
      exact ⟨b, rfl⟩
    exact MonoidHom.mem_range.mp hb
  have hv : (w'⁻¹ * w) * Φ.β b = Φ.β b * (w'⁻¹ * w) := by
    have h1 := h f
    rw [hf] at h1
    calc (w'⁻¹ * w) * Φ.β b = w'⁻¹ * (w * Φ.β b * w⁻¹) * w := by group
      _ = w'⁻¹ * (w' * Φ.β b * w'⁻¹) * w := by rw [h1]
      _ = Φ.β b * (w'⁻¹ * w) := by group
  have h2 := (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat _ b).mpr hv
  rw [ha, ha']
  calc Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹
      = Φ.ψ w' * (Φ.ψ (w'⁻¹ * w) * (b : G) * (Φ.ψ (w'⁻¹ * w))⁻¹) * (Φ.ψ w')⁻¹ := by
        simp only [map_mul, map_inv]
        group
    _ = Φ.ψ w' * (b : G) * (Φ.ψ w')⁻¹ := by rw [h2]

theorem OrthFrameCore.exists_coordAut [Fact p.Prime] [Finite G] (Φ : OrthFrameCore p Bs X)
    (hZ : ∀ z : ↥(orthDerived Φ.Q), (∀ y, z * y = y * z) → z = 1)
    {w : ↥(orthDerived Φ.Q)} {r : MulAut ↥Bs}
    (hr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) (hrR : GGIsReflection p r) :
    ∃ σ : MulAut (Fin Φ.r → Multiplicative (ZMod p)),
      (∀ f, w * Φ.Δ.τΩ Φ.hA f * w⁻¹ = Φ.Δ.τΩ Φ.hA (σ f)) ∧ IsSignedPerm ⇑σ ∧ σ * σ = 1 ∧
        Nat.card {f // σ f = f} * p = Nat.card (Fin Φ.r → Multiplicative (ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hβr : ∀ b : ↥Bs, w * Φ.β b * w⁻¹ = Φ.β (r b) := fun b => Φ.beta_conj hZ (hr b).symm
  have hβτ : ∀ f, ∃ b : ↥Bs, Φ.β b = Φ.Δ.τΩ Φ.hA f := fun f =>
    (Φ.mem_A_iff _).mp ((Φ.mem_range_tauΩ_iff _).mp ⟨f, rfl⟩)
  have hN : w ∈ Subgroup.normalizer (((Φ.Δ.τΩ Φ.hA).range : Subgroup ↥(orthDerived Φ.Q)) :
      Set ↥(orthDerived Φ.Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [SetLike.mem_coe, Φ.mem_range_tauΩ_iff, Φ.mem_A_iff]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨r b, (hβr b).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨r⁻¹ b, ?_⟩
      have h1 := hβr (r⁻¹ b)
      rw [MulAut.apply_inv_self, hb] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  obtain ⟨σ, hσ⟩ := RealKGModelRoot.exists_inducedAut hp (tbjA_tauOmega_injective Φ.Δ Φ.hA) rfl hN
  have hSP : IsSignedPerm ⇑σ := tbjA_isSignedPerm_of_induced Φ.Δ Φ.hA ⟨w, Subgroup.mem_top w, hσ⟩
  have hrr : ∀ b : ↥Bs, r (r b) = b := fun b => by
    have h := congrArg (fun φ : MulAut ↥Bs => φ b) hrR.1
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  have hσ2 : σ * σ = 1 := by
    refine MulEquiv.ext fun f => tbjA_tauOmega_injective Φ.Δ Φ.hA ?_
    obtain ⟨b, hb⟩ := hβτ f
    rw [MulAut.mul_apply, MulAut.one_apply, ← hσ, ← hσ, ← hb, hβr, hβr, hrr]
  set C : Subgroup ↥(orthDerived Φ.Q) := Subgroup.centralizer {w} with hC
  have hfr : Nat.card {b : ↥Bs // r b = b} = Nat.card (C.comap Φ.β) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun b => ?_
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ = b := by rw [← hr b, h]
      exact ((psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat w b).mp h').symm
    · intro h
      have h' := (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat w b).mpr h.symm
      exact Subtype.ext (by rw [hr b, h'])
  have hfσ : Nat.card {f // σ f = f} = Nat.card (C.comap (Φ.Δ.τΩ Φ.hA)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun f => ?_
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := hσ f
      rw [h] at h1
      calc Φ.Δ.τΩ Φ.hA f * w = w * Φ.Δ.τΩ Φ.hA f * w⁻¹ * w := by rw [h1]
        _ = w * Φ.Δ.τΩ Φ.hA f := by group
    · intro h
      apply tbjA_tauOmega_injective Φ.Δ Φ.hA
      rw [← hσ f, ← h]
      group
  have hidx : (C.comap Φ.β).index = (C.comap (Φ.Δ.τΩ Φ.hA)).index := by
    rw [Subgroup.index_comap, Subgroup.index_comap, Φ.range_beta]
  have hBs : Nat.card {b : ↥Bs // r b = b} * p = Nat.card ↥Bs := hrR.2
  rw [hfr] at hBs
  have h1 : Nat.card (C.comap Φ.β) * (C.comap Φ.β).index = Nat.card ↥Bs := Subgroup.card_mul_index _
  have hpos : 0 < Nat.card (C.comap Φ.β) := Nat.card_pos
  have hidxp : (C.comap Φ.β).index = p := Nat.eq_of_mul_eq_mul_left hpos (h1.trans hBs.symm)
  refine ⟨σ, hσ, hSP, hσ2, ?_⟩
  calc Nat.card {f // σ f = f} * p
      = Nat.card (C.comap (Φ.Δ.τΩ Φ.hA)) * (C.comap (Φ.Δ.τΩ Φ.hA)).index := by rw [hfσ, ← hidx, hidxp]
    _ = Nat.card (Fin Φ.r → Multiplicative (ZMod p)) := Subgroup.card_mul_index _

theorem OrthFrameCore.isReflection_of_swapElt [Fact p.Prime] [Finite G] (Φ : OrthFrameCore p Bs X) {i j : Fin Φ.r}
    (hij : i ≠ j) {w : ↥(orthDerived Φ.Q)}
    (hw : ∀ f : Fin Φ.r → Multiplicative (ZMod p), (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (permAut (Equiv.swap i j) f))
    {a : MulAut ↥Bs} (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) : GGIsReflection p a := by
  haveI := Φ.finite_linearEquiv
  exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj (Fact.out : p.Prime).one_lt ha
    (fun t ht => Φ.Δ.swap_sq_comm hw t ht) (fun t => Φ.Δ.mem_reflFixed_iff hw t) (Φ.Δ.card_reflFixed hij)

theorem OrthFrameCore.rk1ConclEx_of_coxRefl [Fact p.Prime] (hp2 : p ≠ 2) [Finite G] (Φ : OrthFrameCore p Bs X)
    (hZ : ∀ z : ↥(orthDerived Φ.Q), (∀ y, z * y = y * z) → z = 1)
    (hsw : ∀ {i j : Fin Φ.r}, i ≠ j → ∀ {w : ↥(orthDerived Φ.Q)},
      (∀ f : Fin Φ.r → Multiplicative (ZMod p), (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (permAut (Equiv.swap i j) f)) →
      ∀ {a : MulAut ↥Bs}, a ∈ ggAutomizer X Bs → (∀ b : ↥Bs, ((a b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) →
        GGRk1ConclEx p Bs X a)
    {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hM : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hC : ∀ a ∈ ggAutomizer X Bs, GGIsReflection p a → a ∈ ggCoxRefl M e) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r) (hrC : r ∈ ggCoxRefl M e) :
    GGRk1ConclEx p Bs X r := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp hrA
  have hgψ : g ∈ Φ.ψ.range := by
    rw [Φ.hrange]
    exact hgX
  obtain ⟨w, rfl⟩ := hgψ
  obtain ⟨σ, hσ, hSP, hσ2, hcard⟩ := Φ.exists_coordAut hZ hg hrR
  have hβτ : ∀ f, ∃ b : ↥Bs, Φ.β b = Φ.Δ.τΩ Φ.hA f := fun f =>
    (Φ.mem_A_iff _).mp ((Φ.mem_range_tauΩ_iff _).mp ⟨f, rfl⟩)
  have hcoe : ∀ (v : ↥(orthDerived Φ.Q)) (u : MulAut (Fin Φ.r → Multiplicative (ZMod p))),
      (∀ f, v * Φ.Δ.τΩ Φ.hA f * v⁻¹ = Φ.Δ.τΩ Φ.hA (u f)) →
      ∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f) := by
    intro v u h f
    have h1 := congrArg (fun y : ↥(orthDerived Φ.Q) => (y : Φ.V ≃ₗ[Φ.F] Φ.V)) (h f)
    simpa using h1
  have hcoe' : ∀ (v : ↥(orthDerived Φ.Q)) (u : MulAut (Fin Φ.r → Multiplicative (ZMod p))),
      (∀ f, (v : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (v : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ = Φ.Δ.τ (u f)) →
      ∀ f, v * Φ.Δ.τΩ Φ.hA f * v⁻¹ = Φ.Δ.τΩ Φ.hA (u f) := by
    intro v u h f
    apply Subtype.ext
    simpa using h f
  have hmemX : ∀ v : ↥(orthDerived Φ.Q), Φ.ψ v ∈ X := fun v => by
    have h : Φ.ψ v ∈ Φ.ψ.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [Φ.hrange] at h
  rcases RealKGSignedRefl.signedRefl_cases hp hp2 hSP hσ2 hcard with ⟨a, rfl⟩ | ⟨⟨⟨⟨i, j⟩, hij⟩, s⟩, rfl⟩
  ·
    exfalso
    haveI : Nontrivial (Fin Φ.r) := Fin.nontrivial_iff_two_le.mpr (by have := Φ.hr; omega)
    obtain ⟨b, hba⟩ := exists_ne a
    obtain ⟨w', hw', hn'⟩ := Φ.swapReal a b hba.symm
    have ha'A := ggConjAut_mem_ggAutomizer (hmemX w') hn'
    have ha'R := Φ.isReflection_of_swapElt hba.symm hw' (ggConjAut_apply Bs hn')
    have hord := ggCoxRefl_mul_orderOf_le_three hM h3 hrC (hC _ ha'A ha'R)
    have hrw : ∀ c : ↥Bs, (((r * ggConjAut Bs hn') c : ↥Bs) : G) =
        Φ.ψ (w * w') * c * (Φ.ψ (w * w'))⁻¹ := by
      intro c
      rw [MulAut.mul_apply, hg, ggConjAut_apply, map_mul]
      group
    have htw : ∀ f, (w * w') * Φ.Δ.τΩ Φ.hA f * (w * w')⁻¹ =
        Φ.Δ.τΩ Φ.hA ((sgnAut a * permAut (Equiv.swap a b) : MulAut (Fin Φ.r → Multiplicative (ZMod p))) f) := by
      intro f
      rw [MulAut.mul_apply, ← hσ, ← hcoe' w' _ hw' f]
      group
    have hpow : ∀ n : ℕ, (r * ggConjAut Bs hn') ^ n = 1 →
        (sgnAut a * permAut (Equiv.swap a b) : MulAut (Fin Φ.r → Multiplicative (ZMod p))) ^ n = 1 := by
      intro n hn
      refine MulEquiv.ext fun f => tbjA_tauOmega_injective Φ.Δ Φ.hA ?_
      rw [MulAut.one_apply, ← conj_pow_apply_of_forall htw n f]
      obtain ⟨c, hc⟩ := hβτ f
      rw [← hc]
      have h1 : Φ.ψ ((w * w') ^ n) * (c : G) * (Φ.ψ ((w * w') ^ n))⁻¹ = c := by
        rw [map_pow, ← ggInducedBy_pow_apply hrw n c, hn, MulAut.one_apply]
      rw [(psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat _ c).mp h1]
      group
    obtain ⟨h2, h3'⟩ := sgnAut_mul_swap_pow_ne_one (p := p) hp hp2 hba.symm
    rcases hord with h | h
    · exact h2 (hpow 2 h)
    · exact h3' (hpow 3 h)
  · cases s
    ·
      have hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
          Φ.Δ.τ (permAut (Equiv.swap i j) f) := by
        intro f
        rw [hcoe w _ hσ f, omPlusRefl_false p hij]
      exact hsw (ne_of_lt hij) hw hrA hg
    ·
      have hij' : i ≠ j := ne_of_lt hij
      obtain ⟨k, hki, hkj⟩ := coord_exists_ne_ne (by have := Φ.hr; omega) i j
      obtain ⟨ws, hws, hns⟩ := Φ.swapReal i j hij'
      obtain ⟨wd, hwd, hnd⟩ := Φ.dinvReal i k hki.symm
      have hsA := ggConjAut_mem_ggAutomizer (hmemX ws) hns
      have hdA := ggConjAut_mem_ggAutomizer (hmemX wd) hnd
      have hs := hsw hij' hws hsA (ggConjAut_apply Bs hns)
      have hws' : ∀ f, ws * Φ.Δ.τΩ Φ.hA f * ws⁻¹ = Φ.Δ.τΩ Φ.hA (permAut (Equiv.swap i j) f) :=
        hcoe' ws _ hws
      have hwd' : ∀ f, wd * Φ.Δ.τΩ Φ.hA f * wd⁻¹ =
          Φ.Δ.τΩ Φ.hA ((sgnAut i * sgnAut k : MulAut (Fin Φ.r → Multiplicative (ZMod p))) f) :=
        hcoe' wd _ fun f => hwd f
      have hinv : ∀ f, wd⁻¹ * Φ.Δ.τΩ Φ.hA f * wd =
          Φ.Δ.τΩ Φ.hA ((sgnAut i * sgnAut k : MulAut (Fin Φ.r → Multiplicative (ZMod p))) f) := by
        intro f
        have h1 := hwd' ((sgnAut i * sgnAut k : MulAut (Fin Φ.r → Multiplicative (ZMod p))) f)
        rw [sgnAut_mul_sgnAut_involutive] at h1
        rw [← h1]
        group
      have hrc : r = ggConjAut Bs hnd * ggConjAut Bs hns * (ggConjAut Bs hnd)⁻¹ := by
        refine Φ.aut_eq_of_tau (w' := wd * ws * wd⁻¹) hg ?_ ?_
        · intro c
          rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply,
            inv_apply_of_forall (ggConjAut_apply Bs hnd)]
          simp only [map_mul, map_inv]
          group
        · intro f
          calc w * Φ.Δ.τΩ Φ.hA f * w⁻¹
              = Φ.Δ.τΩ Φ.hA ((sgnAut i * sgnAut j * permAut (Equiv.swap i j) :
                  MulAut (Fin Φ.r → Multiplicative (ZMod p))) f) := by
                rw [hσ f, omPlusRefl_true p hij]
            _ = Φ.Δ.τΩ Φ.hA ((sgnAut i * sgnAut k : MulAut (Fin Φ.r → Multiplicative (ZMod p)))
                  (permAut (Equiv.swap i j)
                    ((sgnAut i * sgnAut k : MulAut (Fin Φ.r → Multiplicative (ZMod p))) f))) := by
                rw [sgnAut_conj_swap hij' hki hkj]
            _ = wd * (ws * (wd⁻¹ * Φ.Δ.τΩ Φ.hA f * wd) * ws⁻¹) * wd⁻¹ := by
                rw [hinv, hws', hwd']
            _ = wd * ws * wd⁻¹ * Φ.Δ.τΩ Φ.hA f * (wd * ws * wd⁻¹)⁻¹ := by group
      rw [hrc]
      exact ggRk1ConclEx_conj hs hdA

theorem OrthWeakFrame.rk1ConclEx_of_coxRefl (hRig : GGLabelRigidInput) [Fact p.Prime] (hp2 : p ≠ 2) [Finite G]
    (Φ : OrthWeakFrame p Bs X) (hΦ : Φ.Recognized) (hXns : ¬ GGSplitLie p X) {A : Subgroup (MulAut ↥Bs)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (hM : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hC : ∀ a ∈ ggAutomizer X Bs, GGIsReflection p a → a ∈ ggCoxRefl M e) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r) (hrC : r ∈ ggCoxRefl M e) :
    GGRk1ConclEx p Bs X r :=
  Φ.toCore.rk1ConclEx_of_coxRefl hp2 (fun _ hz => Φ.eq_one_of_central hΦ hz)
    (fun hij _ hw _ haA ha => (Φ.rk1Ex_of_swapElt hRig orthRankOneModelInput_holds hp2 hΦ hXns hij hw haA ha).2)
    hM h3 hC hrA hrR hrC

theorem OrthWeakFrame.rk1ConclEx_of_cfg (hRig : GGLabelRigidInput) [Finite G] {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hnsX : ¬ GGSplitLie p X) (Φ : OrthWeakFrame p Bs X)
    (hΦ : Φ.Recognized) : ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  haveI : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
  intro r hrA hrC
  exact Φ.rk1ConclEx_of_coxRefl hRig (ggRouteCfg_prime hcfg).2 hΦ hnsX hpres.1 h3
    (fun a haA haR => ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hXA haA) haR)
    hrA (ggCoxRefl_isReflection hpres.2 hrC) hrC

theorem OrthFrameCore.eq_one_of_center_eq_bot (Φ : OrthFrameCore p Bs X) (hZX : Subgroup.center ↥X = ⊥)
    {z : ↥(orthDerived Φ.Q)} (hz : ∀ y, z * y = y * z) : z = 1 := by
  have hmem : ∀ v : ↥(orthDerived Φ.Q), Φ.ψ v ∈ X := fun v => by
    have h : Φ.ψ v ∈ Φ.ψ.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [Φ.hrange] at h
  have hc : (⟨Φ.ψ z, hmem z⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    have hg' : g ∈ Φ.ψ.range := by rw [Φ.hrange]; exact hg
    obtain ⟨y, rfl⟩ := hg'
    apply Subtype.ext
    show Φ.ψ y * Φ.ψ z = Φ.ψ z * Φ.ψ y
    rw [← map_mul, ← map_mul, hz y]
  rw [hZX, Subgroup.mem_bot] at hc
  apply Φ.hinj
  rw [map_one]
  exact congrArg Subtype.val hc

theorem OrthFrameCore.rk1ConclEx_of_cfg_two (hRig : GGLabelRigidInput) [Finite G] {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hnsX : ¬ GGSplitLie p X) (Φ : OrthFrameCore p Bs X)
    (hK : Nat.card Φ.F = 2) (hZX : Subgroup.center ↥X = ⊥)
    (hlab : GGHasLabel ⟨.D, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.twD, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X)) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  haveI : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
  have hp2 := (ggRouteCfg_prime hcfg).2
  intro r hrA hrC
  exact Φ.rk1ConclEx_of_coxRefl hp2 (fun _ hz => Φ.eq_one_of_center_eq_bot hZX hz)
    (fun hij _ hw _ haA ha => (Φ.rk1Ex_of_swapElt_two hRig hp2 hK hlab hnsX hij hw haA ha).2) hpres.1 h3
    (fun a haA haR => ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3 (hXA haA) haR)
    hrA (ggCoxRefl_isReflection hpres.2 hrC) hrC

end OrthTorus

theorem GGResidualRk1Frame.rk1ConclEx (hRig : GGLabelRigidInput) {p : ℕ} {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hnsX : ¬ GGSplitLie p X) (h : GGResidualRk1Frame p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  obtain ⟨Φ, hΦ⟩ := h
  exact Φ.rk1ConclEx_of_cfg hRig hcfg hpres h3 hXA hnsX hΦ

theorem ggRk1ConclEx_of_orthTwoMarking (hRig : GGLabelRigidInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hnsX : ¬ GGSplitLie p X) {P : ℕ → LargeEvenLabel → Prop}
    (hProw : ∀ lab, P p lab → (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1)
    (hmark : GGInnerDiagOnLabel P p Bs X)
    (hZK : ∀ lab, P p lab → GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → Subgroup.center ↥X = ⊥) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with hXL | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl hXL)
    · exact hw.2
  obtain ⟨lab, hPlab, hhas, Φ, hr, hcard, -⟩ :=
    OrthTorus.exists_orthFrameCore_of_marking hRig hp2 hcfg.1.1.2.1.2.1 hcfg.1.1.2.1.2.2.2
      (fun lab hl => (hProw lab hl).1) hmark hZK (ggResGen_exists_act hcfg hXw)
  obtain ⟨hrow, hn⟩ := hProw lab hPlab
  have hK : Nat.card Φ.F = 2 := by rw [hcard, hn, pow_one]
  have hlab : GGHasLabel ⟨.D, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X) ∨
      GGHasLabel ⟨.twD, Φ.r, 1⟩ (↥X ⧸ Subgroup.center ↥X) := by
    rcases lab with ⟨tag, rank, n⟩
    change n = 1 at hn
    change Φ.r = rank at hr
    subst hn hr
    rcases hrow with ⟨ht, -⟩ | ⟨ht, -⟩
    · change tag = .D at ht
      subst ht
      exact Or.inl hhas
    · change tag = .twD at ht
      subst ht
      exact Or.inr hhas
  exact Φ.rk1ConclEx_of_cfg_two hRig hcfg hpres h3 hXA hnsX hK (hZK lab hPlab hhas) hlab

theorem ggRk1ConclEx_of_D4two_of_lt (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hnsX : ¬ GGSplitLie p X)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hlt : B < Bs) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  exact ggRk1ConclEx_of_orthTwoMarking hRig hcfg hpres h3 hXw hnsX
    (fun _ hl => ⟨Or.inl hl.1, hl.2.1⟩) hmark
    (fun _ _ _ => hcfg.1.1.center_eq_bot_of_D4two_of_lt hlt hmark)

theorem ggRk1ConclEx_of_orthTwo
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X)
    (hnsX : ¬ GGSplitLie p X) (hR : GGInnerDiagOnLabel ggRowP_ResGenRest p Bs X)
    (hR2 : ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M)
            (B < Bs) p lab) p Bs X)
    (hE7 : ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X)
    (hU5 : ¬ (X = L ∧ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X))
    (hE7q : ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X)
    (hTq : ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X)
    (hUlt : ¬ (X ≠ L ∧ B < Bs ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X))
    (hT2L : ¬ (X = L ∧ ¬ GGIsWeylMatrixA M ∧ ¬ NSJoin.NSTypeD M ∧
      GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X))
    (hU3 : X ≠ L → ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) p Bs X)
    (hU5m : ¬ (X ≠ L ∧ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X)) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  have h : GGInnerDiagOnLabel (fun p lab => ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M)
            (B < Bs) p lab ∨
      ((GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M) ∧ (ggRowP_ETwE6 p lab ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab)) ∨
      (¬ GGIsWeylMatrixA M ∧ ¬ NSJoin.NSTypeD M ∧ ggRowP_EE8 p lab) ∨
      (GGIsWeylMatrixA M ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) ∨
      ((ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) ∧ (X = L ∨ B < Bs)) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1 ∧ ¬ (lab.tag = .D ∧ lab.rank = 4)) ∨
      (ggRowP_EE7 p lab ∧ lab.n = 1) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∧ X = L) ∨
      (ggRowP_EE7 p lab ∧ 2 ≤ lab.n) ∨
      (ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) ∨
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∧ X ≠ L ∧ B < Bs) ∨
      ((ggRowP_ETwE6 p lab ∧ lab.n = 1) ∧ X = L ∧ ¬ GGIsWeylMatrixA M ∧ ¬ NSJoin.NSTypeD M) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∧ X ≠ L)) p Bs X :=
    hR.mono_label_of_hasLabel fun lab hΛ _ hl => by
      rcases hl with hl | hl | hl | ⟨hn, hl | hl | hl⟩
      · by_cases hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M
        · exact Or.inr (Or.inl ⟨hAD, Or.inl hl⟩)
        · by_cases hn1 : lab.n = 1
          · by_cases hXL : X = L
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨⟨hl, hn1⟩, hXL, fun h => hAD (Or.inl h), fun h => hAD (Or.inr h)⟩))))))))))))
            · exact Or.inl (Or.inl ⟨fun h => hAD (Or.inl h), fun h => hAD (Or.inr h), hl, hn1, hXL⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hl, by have := hΛ.1; omega⟩)))))))))
      · by_cases hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M
        · exact Or.inr (Or.inl ⟨hAD, Or.inr (Or.inl hl)⟩)
        · by_cases hn1 : lab.n = 1
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl, hn1⟩))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hl, by have := hΛ.1; omega⟩))))))))
      · by_cases hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M
        · exact Or.inr (Or.inl ⟨hAD, Or.inr (Or.inr hl)⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨fun h => hAD (Or.inl h), fun h => hAD (Or.inr h), hl⟩))
      · obtain ⟨hsu, hr⟩ := hl
        rcases hr with hr | hr
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hsu, hn, hr⟩))))))))))
        · by_cases hXL : X = L
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hsu, hn, hr⟩, hXL⟩)))))))
          · by_cases hlt : B < Bs
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨⟨hsu, hn, Or.inr hr⟩, hXL, hlt⟩)))))))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr ⟨⟨hsu, hn, hr⟩, hXL⟩))))))))))))
      · by_cases hA : GGIsWeylMatrixA M
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hA, Or.inl hl⟩)))
        · by_cases h4 : lab.rank = 4
          · by_cases hXL : X = L
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hl, hn, h4⟩, Or.inl hXL⟩))))
            · by_cases hlt : B < Bs
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hl, hn, h4⟩, Or.inr hlt⟩))))
              · exact Or.inl (Or.inr ⟨hn, hl, h4, hXL, hA, hlt⟩)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl hl, hn, fun h => h4 h.2⟩)))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr hl, hn, ?_⟩)))))
        rintro ⟨ht, -⟩
        rw [hl.1] at ht
        exact absurd ht (by decide)
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  · exact absurd h hR2
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨hAD, -⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact (ggResidual_excRow_absurd_AD hRig hRk hcfg hpres h3 hAD hXw (h.mono_label fun _ hl => hl.2)).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨hA, hD, -⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    have hXn : X = L ∨ ∃ y, GGNbr p B x D J y X := hXw.imp_right fun hw => hw.1
    have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
      rcases hXw with rfl | hw
      · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
      · exact hw.2
    exact (ggRow_absurd_EE8 hRig hFix hWA hcfg e (GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 hA hD) hXn hXA
      (h.mono_label fun _ hl => hl.2.2)).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨hA, -⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact (ggResidual_orthRow_absurd_A hRig hcfg hpres h3 hA hXw (h.mono_label fun _ hl => hl.2)).elim
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨⟨-, hcase⟩, -, -⟩⟩ := largeEvenMarking_exists_hasLabel h
    have hD4 : GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X :=
      h.mono_label fun _ hl => hl.1
    rcases hcase with hXL | hlt
    · subst hXL
      exact ggRk1ConclEx_of_orthTwoMarking hRig hcfg hpres h3 (Or.inl rfl) hnsX
        (fun _ hl => ⟨Or.inl hl.1, hl.2.1⟩) hD4 fun _ _ _ => GGConfig.center_eq_bot_of_D4two hRig hcfg.1.1 hD4
    ·
      exact ggRk1ConclEx_of_D4two_of_lt hRig hcfg hpres h3 hXw hnsX hD4 hlt
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    haveI : Group.IsPerfect ↥X := Group.IsPerfect.mk h.1
    refine ggRk1ConclEx_of_orthTwoMarking hRig hcfg hpres h3 hXw hnsX (fun _ hl => ⟨hl.1, hl.2.1⟩) h
      fun lab hl hhas => ?_
    obtain ⟨hrow, hn, h4⟩ := hl
    refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
    rcases hrow with ⟨ht, hr, -, -⟩ | ⟨ht, hr, -, -⟩
    · have h4' : lab.rank ≠ 4 := fun h => h4 ⟨ht, h⟩
      exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr ⟨ht, by omega⟩
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact absurd h hE7
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hXL⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact absurd ⟨hXL, h.mono_label fun _ hl => hl.1⟩ hU5
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact absurd h hE7q
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    exact absurd h hTq
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    by_cases hXL : X = L
    · have hm := h
      subst hXL
      refine absurd (hm.mono_label fun lab hl => ?_) (not_ggInnerDiagOnLabel_unitary_four hcfg.1.1)
      obtain ⟨hsu, -, hr⟩ := hl
      rcases hsu.1 with ⟨ht, -⟩ | ⟨ht, -⟩
      · exact ⟨Or.inl ht, hr, hsu.2⟩
      · exact ⟨Or.inr ht, hr, hsu.2⟩
    · exact absurd h (hU3 hXL)
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hXL, hlt⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact absurd ⟨hXL, hlt, h.mono_label fun _ hl => hl.1⟩ hUlt
  rcases GGInnerDiagOnLabel.elim_or h with h | h
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hXL, hAM, hDM⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact absurd ⟨hXL, hAM, hDM, h.mono_label fun _ hl => hl.1⟩ hT2L
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hXL⟩, -⟩ := largeEvenMarking_exists_hasLabel h
    exact absurd ⟨hXL, h.mono_label fun _ hl => hl.1⟩ hU5m

theorem ggRk1ConclEx_of_residualFrameAway
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hU62 : GGU62OuterDiagInput) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput) (hTCJ : GGTCJKnown)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hA : ¬ (GGIsWeylMatrixA M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) {X : Subgroup G}
    (hX : X = L ∨
      (X ∈ 𝒦 ∧ ¬ (NSJoin.NSTypeD M ∧
        ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) ∨
      (T M ∧ (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
        GGSecFiveWeakNbr p B Bs x L D J 𝒦 X))
    (hnsX : ¬ GGSplitLie p X) (hXU : ¬ GGMemberUnitary p Bs X)
    (hQ4X : X ≠ L → ¬ NSJoin.NSTypeD M →
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) → p = 3 →
      GGInnerDiagOnLabel GGLabQFour p Bs X) (h : X ≠ L → GGRk1ResidualFrameInputExOf T) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
  have hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X := by
    rcases hX with hXL | ⟨hXK, -⟩ | ⟨-, -, hw⟩
    · exact Or.inl hXL
    · exact Or.inr (GGSecFiveWeakNbr.of_mem hcfg hXK)
    · exact Or.inr hw
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with hXL | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl hXL)
    · exact hw.2
  have hF : GGResidualRk1Frame p Bs X ∨
      ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r := by
    by_cases hR : GGInnerDiagOnLabel ggRowP_ResGenRest p Bs X
    · by_cases hR1 : NSJoin.NSTypeD M → X = L → GGInnerDiagOnLabel (fun _ lab => lab.n = 1) p Bs X
      · by_cases hR2 : GGInnerDiagOnLabel (fun p lab => ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M)
            (B < Bs) p lab) p Bs X
        ·
          have hXL₀ : X ≠ L := by
            obtain ⟨_, -, -, -, -, -, -, -, hl, -⟩ := largeEvenMarking_exists_hasLabel hR2
            rcases hl with ⟨-, -, -, -, hXL⟩ | ⟨-, -, -, hXL, -⟩
            · exact hXL
            · exact hXL
          refine h hXL₀ G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hA X hX hnsX hXU ?_ hR1
          by_cases hRB : X ≠ L ∧ ¬ NSJoin.NSTypeD M ∧
              ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6
          ·
            obtain ⟨hXL, hDM, hbig⟩ := hRB
            have hsplit : GGInnerDiagOnLabel (fun p lab =>
                (ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M) (B < Bs) p lab ∧ lab.n ≠ 1) ∨
                (ggRowP_Rk1Rest (X ≠ L) (GGIsWeylMatrixA M) (NSJoin.NSTypeD M) (B < Bs) p lab ∧ lab.n = 1)) p Bs X :=
              hR2.mono' fun lab hl => (em (lab.n = 1)).elim (fun hn => Or.inr ⟨hl, hn⟩) (fun hn => Or.inl ⟨hl, hn⟩)
            rcases GGInnerDiagOnLabel.elim_or hsplit with h1 | h1
            · exact h1.mono' fun lab hl => ⟨hl.1, fun _ _ _ => hl.2⟩
            · have hp3 : p = 3 := NSJoin.eq_three_of_innerDiagOnLabel_n_one (ggRouteCfg_prime hcfg).1
                (fun lab hl => ⟨hl.2, (ggRowP_Rk1Rest_dvd_tag hl.1).1⟩) h1
              exact absurd (hQ4X hXL hDM hbig hp3) (NSJoin.not_innerDiagOnLabel_qFour_of_n_one hRig
                (fun lab hl => ⟨hl.2, (ggRowP_Rk1Rest_dvd_tag hl.1).2⟩) h1)
          · exact hR2.mono' fun lab hl => ⟨hl, fun hXL hDM hbig => absurd ⟨hXL, hDM, hbig⟩ hRB⟩
        · by_cases hE7 : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ lab.n = 1) p Bs X
          ·
            exact Or.inr fun r hrA hrC => ggRk1ConclEx_of_e7Two_marking hRig hcfg (hXw.imp_right fun hw => hw.1)
              hnsX hE7 r hrA (ggCoxRefl_isReflection hpres.2 hrC)
          by_cases hE7q : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∧ 2 ≤ lab.n) p Bs X
          ·
            obtain ⟨t, htA, htR, hcon⟩ : ∃ r ∈ ggAutomizer X Bs, GGIsReflection p r ∧ GGRk1ConclEx p Bs X r := by
              by_cases hp3 : p = 3
              · subst hp3
                exact ExcPay.exists_rk1ConclEx_of_route_E7_three hcfg (hXw.imp_right fun hw => hw.1) hE7q
              · obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
                exact ExcPay.exists_rk1ConclEx_of_marking_E7 (ggRouteCfg_prime hcfg).1 hp3 hBs
                  hcfg.1.1.2.1.2.2.2 hE7q
            exact Or.inr fun r hrA hrC => ggRk1ConclEx_of_isReflection_excRow hRig hcfg
              (hXw.imp_right fun hw => hw.1) (hE7q.mono_label fun _ hl => Or.inl hl.1) htA htR hcon hrA
              (ggCoxRefl_isReflection hpres.2 hrC)
          by_cases hU5 : X = L ∧
              GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X
          ·
            obtain ⟨rfl, hU5⟩ := hU5
            exact Or.inr (ggRk1ConclEx_of_twA5_two_L hFix hU62 hcfg hpres h3 hA hns hXU hU5)
          by_cases hTq : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X
          ·
            by_cases hp3 : p = 3
            · exact Or.inr fun r hrA hrC => ggRk1ConclEx_of_twE6Three_nbr hRig hRk hcfg.1.1
                (hXw.imp_right fun hw => hw.1) hnsX hp3 hTq r hrA (ggCoxRefl_isReflection hpres.2 hrC)
            obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
            obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
            obtain ⟨t, htA, htR, hcon⟩ :=
              ExcPay.exists_rk1ConclEx_of_marking_TwE6 hp hp3 hBs hcfg.1.1.2.1.2.2.2 hTq
            have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
            exact Or.inr fun r hrA hrC => ggRk1ConclEx_of_isReflection_excRow hRig hcfg
              (hXw.imp_right fun hw => hw.1) (hTq.mono_label fun _ hl => Or.inr ⟨hl.1, hp5⟩) htA htR hcon hrA
              (ggCoxRefl_isReflection hpres.2 hrC)
          by_cases hT2L : X = L ∧ ¬ GGIsWeylMatrixA M ∧ ¬ NSJoin.NSTypeD M ∧
              GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ lab.n = 1) p Bs X
          ·
            obtain ⟨rfl, hAM, hDM, hm⟩ := hT2L
            have hlt := hcfg.lt_bstar_of_twE6Two_of_not_AD hRig hFix hWI hLB hTCJ hpres h3 hAM hDM hm
            exact Or.inr fun r hrA hrC => ggRk1ConclEx_of_twE6Two_L_of_lt hRig hcfg.1.1 hns hm hlt r hrA
              (ggCoxRefl_isReflection hpres.2 hrC)
          by_cases hUlt : X ≠ L ∧ B < Bs ∧
              GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X
          ·
            obtain ⟨hXL, hlt, hm⟩ := hUlt
            exact Or.inr (ggRk1ConclEx_of_esuTwo_cell hcfg hpres (hXw.imp_right Or.inr) hnsX
              (hm.mono_label fun _ hl => ⟨hl.1, hl.2.1, hl.2.2.imp_right fun h5 => ⟨h5, hXL⟩⟩) fun _ => hlt)
          by_cases hU5m : X ≠ L ∧
              GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X
          ·
            obtain ⟨hXL, hm⟩ := hU5m
            have hBB : B = Bs := eq_of_le_of_not_lt hcfg.1.1.2.1.1 fun hlt =>
              hUlt ⟨hXL, hlt, hm.mono_label fun _ hl => ⟨hl.1, hl.2.1, Or.inr hl.2.2⟩⟩
            exact Or.inr (ggRk1ConclEx_of_twA5_two_ne_L hRig hFix hU62 hLB hSP hcfg hpres h3 hBB hX hXL hnsX
              (hQ4X hXL) hm)
          have hU3 : X ≠ L →
              ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) p Bs X := fun hXL => by
            obtain ⟨y, hnb⟩ := (hXw.resolve_left hXL).1
            exact not_ggInnerDiagOnLabel_unitary_four_two_of_ggNbr hLB hSP hcfg hnb
          exact Or.inr (ggRk1ConclEx_of_orthTwo hRig hRk hFix hWA hcfg hpres h3 hXw hnsX hR hR2 hE7 hU5 hE7q hTq
            hUlt hT2L hU3 hU5m)
      ·
        obtain ⟨hD, hR1⟩ := not_imp.mp hR1
        obtain ⟨rfl, hn1⟩ := not_imp.mp hR1
        exact Or.inl (NSJoin.exists_orthWeakFrame_L_typeD hcfg hpres hD hns hXU hn1)
    · exact Or.inl (ggResGenFrame_of_not_rest hcfg hpres h3 hXw hnsX hXU hR)
  rcases hF with hF | hC
  · exact hF.rk1ConclEx hRig hcfg hpres h3 hXA hnsX
  · exact hC

theorem GGRk1ResidualFrameInputExOf.apply
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop} (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput)
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hU62 : GGU62OuterDiagInput) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput) (hTCJ : GGTCJKnown) (h : GGRk1ResidualFrameInputExOf T)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hA : ¬ (GGIsWeylMatrixA M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) {X : Subgroup G}
    (hX : X = L ∨
      (X ∈ 𝒦 ∧ ¬ (NSJoin.NSTypeD M ∧
        ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)) ∨
      (T M ∧ (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) ∧
        GGSecFiveWeakNbr p B Bs x L D J 𝒦 X))
    (hnsX : ¬ GGSplitLie p X) (hXU : ¬ GGMemberUnitary p Bs X)
    (hQ4X : X ≠ L → ¬ NSJoin.NSTypeD M →
      (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) → p = 3 →
      GGInnerDiagOnLabel GGLabQFour p Bs X) :
    ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e → GGRk1ConclEx p Bs X r :=
  ggRk1ConclEx_of_residualFrameAway hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ hcfg hns hpres h3 hA hX hnsX hXU hQ4X
    fun _ => h

theorem GGRk1ResidualFrameInputExOf.toWeak
    {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput) (hU62 : GGU62OuterDiagInput) (hFix : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput)
    (hTCJ : GGTCJKnown)
    (hPos : NSJoin.NSWeakOrthPosInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSJoin.NSTypeD M))
    (hNbrQ4 : NSJoin.NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M))
    (h : GGRk1ResidualFrameInputExOf T) : GGRk1ResidualWeakInputExOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX hnsX hNU
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with hXL | hXK | ⟨-, -, hw⟩
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl hXL)
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inr hXK)
    · exact hw.2
  have hA : ¬ (GGIsWeylMatrixA M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) := by
    rintro ⟨⟨_, _, _, hM⟩, hbig⟩
    refine hNU (ggMemberUnitary_anyA hRk hU62 hFix hWA hLB hSP hcfg hns hpres hM hbig ?_ hnsX)
    rcases hX with hXL | hXK | ⟨-, -, hw⟩
    · exact Or.inl hXL
    · exact Or.inr ⟨hcfg.2.2.2.1.2 X hXK, hXA⟩
    · exact Or.inr hw
  by_cases hXD : X ∈ 𝒦 ∧ NSJoin.NSTypeD M ∧
      ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6
  ·
    obtain ⟨hXK, hDM, hbig⟩ := hXD
    exact GGResidualRk1Frame.rk1ConclEx hRig hcfg hpres h3 hXA hnsX
      (hPos G p B Bs x L D J 𝒦 hcfg hns ⟨ι, M, e, hpres, hDM, hbig⟩ X (GGSecFiveWeakNbr.of_mem hcfg hXK) hnsX hNU)
  · refine h.apply hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ hcfg hns hpres h3 hA ?_ hnsX hNU ?_
    · rcases hX with hXL | hXK | hTw
      · exact Or.inl hXL
      · exact Or.inr (Or.inl ⟨hXK, fun hDb => hXD ⟨hXK, hDb⟩⟩)
      · exact Or.inr (Or.inr hTw)
    ·
      intro hXL hDM hbig hp3
      subst hp3
      have hE : GGIsWeylMatrixE M :=
        GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 h3 (fun hAM => hA ⟨hAM, hbig⟩) hDM
      refine NSJoin.innerDiagOnLabel_qFour_of_nbrQFour_E hNbrQ4 hcfg hns hpres hE hbig ?_
      rcases hX with hXL' | hXK | ⟨-, -, hw⟩
      · exact absurd hXL' hXL
      · exact Or.inl hXK
      · exact Or.inr hw

end Proofs

end CFSG.StandardType

end
