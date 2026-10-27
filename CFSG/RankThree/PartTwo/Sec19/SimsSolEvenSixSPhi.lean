module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSym

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

@[expose] def SixSymPhiQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6) (D : C.PiData),
    Nat.card ↥(Rc X) = 2 → Function.Surjective C.θ →
    ∀ (x : G) (hx : x ∈ CFSG.Open.pCoreOf 2 M) (i j : Fin 6), i ≠ j →
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j} → ¬ CGOf x ≤ M →
      CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x →
      ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1

@[expose] def SixSymResidualElem : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6) (D : C.PiData),
    Nat.card ↥(Rc X) = 2 → Function.Surjective C.θ →
    ∀ (x : G) (hx : x ∈ CFSG.Open.pCoreOf 2 M) (i j : Fin 6), i ≠ j →
      Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {i, j} → ¬ CGOf x ≤ M →
      CFSG.Open.pCoreOf 2 (CGOf x) ⊔ CFSG.Open.pCoreOf 2 M = TOf M x →
      (∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) →
      Nonempty (↥M ≃* YamakiHat)

theorem sixSymResidual_of_phiQ (hPhi : SixSymPhiQ) (hElem : SixSymResidualElem) :
    SixSymResidual :=
  fun G _ _ M X C D hR2 hsurj x hx i j hij hπ hK h =>
    hElem G M X C D hR2 hsurj x hx i j hij hπ hK h (hPhi G M X C D hR2 hsurj x hx i j hij hπ hK h)

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem sq_mem_R {q : G} (hq : q ∈ CFSG.Open.pCoreOf 2 M) : q * q ∈ Rc X := by
  have h1 : D.piQ (⟨q, hq⟩ * ⟨q, hq⟩) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, toAdd_mul, toAdd_one, permBar_add_self]
  exact (D.piQ_eq_one_iff _).1 h1

theorem sq_eq_one_of_mem_range (hR : Nat.card ↥(Rc X) ≤ 2) {q : G}
    (hq : q ∈ CFSG.Open.pCoreOf 2 M)
    (h : Multiplicative.toAdd (D.piQ ⟨q, hq⟩) ∈ Set.range (heartToBar (n := 6))) :
    q * q = 1 := by
  obtain ⟨w, hw, r, hr, rfl⟩ := D.exists_mul_of_mem_range h
  have hw2 : w * w = 1 := by
    have := C.S.elemU.2 _ hw
    simpa [pow_two] using this
  have hr2 : r * r = 1 := Rc_mul_self hR hr
  have hrQ : r ∈ CFSG.Open.pCoreOf 2 M := by
    rw [C.S.R_eq_inf] at hr
    exact hr.1
  have hwQ : w ∈ CFSG.Open.pCoreOf 2 M := C.S.W_le_Q hw
  have hc := C.Q_comm hR w hwQ r hrQ
  calc w * r * (w * r) = (w * w) * (r * r) := by
        rw [show w * r * (w * r) = w * (r * w) * r by group, ← hc]
        group
    _ = 1 := by rw [hw2, hr2, one_mul]

theorem sq_eq_parity (hR : Nat.card ↥(Rc X) ≤ 2) :
    (∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) ∨
      ∀ (q : G) (hq : q ∈ CFSG.Open.pCoreOf 2 M),
        (q * q = 1 ↔ Multiplicative.toAdd (D.piQ ⟨q, hq⟩) ∈ Set.range (heartToBar (n := 6))) := by
  by_cases hall : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨q₀, hq₀, hq₀1⟩ := hall
    have hq₀r : Multiplicative.toAdd (D.piQ ⟨q₀, hq₀⟩) ∉ Set.range (heartToBar (n := 6)) :=
      fun h => hq₀1 (D.sq_eq_one_of_mem_range hR hq₀ h)
    intro q hq
    refine ⟨fun h1 => ?_, fun h => D.sq_eq_one_of_mem_range hR hq h⟩
    by_contra hqr
    have hprod : Multiplicative.toAdd (D.piQ (⟨q, hq⟩ * ⟨q₀, hq₀⟩)) ∈
        Set.range (heartToBar (n := 6)) := by
      rw [map_mul, toAdd_mul]
      exact add_mem_range_heartToBar hqr hq₀r
    have h2 := D.sq_eq_one_of_mem_range hR ((CFSG.Open.pCoreOf 2 M).mul_mem hq hq₀) hprod
    have hc := C.Q_comm hR q hq q₀ hq₀
    apply hq₀1
    calc q₀ * q₀ = (q * q) * (q₀ * q₀) := by rw [h1, one_mul]
      _ = q * q₀ * (q * q₀) := by
          rw [show q * q₀ * (q * q₀) = q * (q₀ * q) * q₀ by group, ← hc]
          group
      _ = 1 := h2

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
