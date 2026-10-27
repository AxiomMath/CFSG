module

public import CFSG.RankThree.GF2n.Tim79a34BigAssembly
import CFSG.RankThree.GF2n.Tim79a34BigIWProof
import CFSG.RankThree.GF2n.Tim79a34BigNaturalProof

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

theorem MinCex.Q_le_M (hc : MinCex M V Q P H) : Q ≤ M := by
  rw [hc.hQ]
  exact (inSubgroup_pCore_two M).2.1

theorem MinCex.M_le_normalizer_Q (hc : MinCex M V Q P H) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  rw [hc.hQ]
  exact (inSubgroup_pCore_two M).2.2

theorem MinCex.Q_le_normalizer_V [Finite G] (hc : MinCex M V Q P H) :
    Q ≤ Subgroup.normalizer (V : Set G) :=
  hc.normalizer_eq ▸ hc.Q_le_M

theorem BigEndHyp.P_le_xOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) : P ≤ xOf V H := by
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  obtain ⟨n, f, Φ, ψ, -, hf, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ :=
    bigNaturalStatement_holds G M V Q P H h hZ
  have hNat : BigNatCfg V H h.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨-, -, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H h hZ hIW hf Φ ψ hNat a T ha hT hTV
  rw [hxOf]
  exact h.setup.mc.toMinCex.PleH

theorem BigEndHyp.inf_wOf_lt_P_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) : V ⊓ wOf V H < P ⊓ wOf V H := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  refine lt_of_le_of_ne (le_inf (inf_le_left.trans hc.V_le_P) inf_le_right) ?_
  obtain ⟨n, f, Φ, ψ, hn2, hf, -, -, -⟩ := bigNaturalStatement_holds G M V Q P H h hZ
  have hq4 : 4 ≤ qBar V H := h.q_big
  have hq1 : 1 < qBar V H := by omega
  have hn1 : 1 < 2 * n - 1 := by omega
  have hlt' : qBar V H < qBar V H ^ (2 * n - 1) := by
    simpa using Nat.pow_lt_pow_right hq1 hn1
  intro heq
  have hcard : Nat.card ↥(V ⊓ wOf V H) = Nat.card ↥(P ⊓ wOf V H) := by rw [heq]
  rw [h.module, h.natCard_P_inf_wOf hf ψ] at hcard
  exact (ne_of_lt hlt') hcard

theorem BigEndHyp.M_le_normalizer_inf_wOf [Finite G] (h : BigEndHyp M V Q P H)
    (hZ : Subgroup.center (Xbar V H) = ⊥) :
    M ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) := by
  have hc : MinCex M V Q P H := h.setup.mc.toMinCex
  have hIW : cPbar V H P ≤ wOf V H := bigIWStatement_holds G M V Q P H h hZ
  have hA : ⁅P, P⁆ = V ⊓ wOf V H :=
    (bigPCommutatorStatement_holds bigNaturalStatement_holds G M V Q P H h hZ hIW).1
  intro m hm
  rw [← conjSubgroup_eq_self_iff, ← hA]
  change (⁅P, P⁆).map (MulAut.conj m).toMonoidHom = ⁅P, P⁆
  rw [Subgroup.map_commutator,
    show P.map (MulAut.conj m).toMonoidHom = P from
      mem_normalizer_iff_conjSubgroup_eq.mp (hc.M_le_normalizer_P hm)]

end CFSG.RankThree.GF2n.Tim79a
