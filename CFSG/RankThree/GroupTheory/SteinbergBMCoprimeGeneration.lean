module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_of_le {p : ℕ} {A B : Subgroup G} (hA : CFSG.IsElementaryAbelian p A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_le hA hBA

theorem le_of_forall_inf_centralizer_le [Finite G] {p : ℕ} [Fact p.Prime] {B V W : Subgroup G}
    (hB : CFSG.IsElementaryAbelian p B) (hBcard : p ^ 2 ≤ Nat.card B) (hpV : ¬ p ∣ Nat.card V)
    (hBV : B ≤ normalizer (V : Set G))
    (hle : ∀ b ∈ B, b ≠ 1 → V ⊓ centralizer ({b} : Set G) ≤ W) : V ≤ W := by
  let : MulDistribMulAction B V := MulDistribMulAction.compHom V (Subgroup.inclusion hBV)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := B) (H := V) hBcard hpV
  have hle' : (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) ≤
      W.comap V.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have hfix : a • v = v :=
      (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a v).mp hv
    have hc : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val hfix
    have hcomm : (v : G) ∈ centralizer ({(a : G)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (v : G) * a = a * v * (a : G)⁻¹ * a := by rw [hc]
        _ = a * v := by group
    exact hle a a.2 (fun h => ha (Subtype.ext h)) ⟨v.2, hcomm⟩
  intro x hx
  have hmem : (⟨x, hx⟩ : V) ∈
      (⨆ (a : B) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) V) := by
    rw [hgen]
    exact mem_top _
  exact hle' hmem

theorem mem_inSubgroup_pCore_of_isCharacteristicPType {r : ℕ} (hG : CFSG.IsCharacteristicPType G r)
    {Q : Subgroup G} (hQ : IsPGroup r Q) (hQ1 : Q ≠ ⊥) {x : G}
    (hx : x ∈ normalizer (Q : Set G))
    (hxc : ∀ s ∈ CFSG.inSubgroup (CFSG.pCore r) (normalizer (Q : Set G)), s * x = x * s) :
    x ∈ CFSG.inSubgroup (CFSG.pCore r) (normalizer (Q : Set G)) := by
  have hchar := hG (normalizer (Q : Set G)) ⟨Q, hQ1, hQ, rfl⟩
  have hxC : (⟨x, hx⟩ : normalizer (Q : Set G)) ∈
      centralizer (CFSG.pCore r (normalizer (Q : Set G)) : Set (normalizer (Q : Set G))) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (hxc h ⟨h, hh, rfl⟩)
  exact ⟨⟨x, hx⟩, hchar hxC, rfl⟩

theorem le_inSubgroup_pCore_of_normal {r : ℕ} {Q H : Subgroup G} (hQ : IsPGroup r Q)
    (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G)) :
    Q ≤ CFSG.inSubgroup (CFSG.pCore r) H := by
  have hn : (Q.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hQH).mpr hHQ
  have hp : IsPGroup r (Q.subgroupOf H) := hQ.of_equiv (subgroupOfEquivOfLe hQH).symm
  have hle : Q.subgroupOf H ≤ CFSG.pCore r H := le_sSup ⟨hn, hp⟩
  intro x hx
  exact ⟨⟨x, hQH hx⟩, hle hx, rfl⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
