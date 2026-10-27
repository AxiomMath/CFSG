module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds
public import CFSG.GroupTheory.BaerSuzuki.Helpers

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open scoped commutatorElement

private theorem ggSporK_le_opCent {p : ℕ} {K : Type} [Group K] {x : K} {A : Subgroup K}
    (hAC : A ≤ Subgroup.centralizer ({x} : Set K))
    (hAnorm : ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hAp : ∀ a ∈ A, a ^ p = 1) : A ≤ BMOpCent p x := by
  have hn : (A.subgroupOf (Subgroup.centralizer ({x} : Set K))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hAnorm (g : K) g.2 (n : K) hn
  have hp : IsPGroup p (A.subgroupOf (Subgroup.centralizer ({x} : Set K))) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hAp (g.1 : K) g.2
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
    (G := ↥(Subgroup.centralizer ({x} : Set K))) hn hp
  intro a ha
  have h' : (⟨a, hAC ha⟩ : ↥(Subgroup.centralizer ({x} : Set K))) ∈
      CFSG.pCore p ↥(Subgroup.centralizer ({x} : Set K)) :=
    hle (Subgroup.mem_subgroupOf.mpr ha)
  unfold BMOpCent
  exact Subgroup.mem_map.mpr ⟨⟨a, hAC ha⟩, h', rfl⟩

theorem bmCentreZ_of_F1_F4 (p : ℕ) (K : Type) [Group K] [Finite K] [Fact p.Prime]
    (h1 : BMPCentralF1 p K) (h4 : BMPCentralF4 p K) : BMCentreZ p K := by
  intro x hx hnc A hAC hAnorm hAel
  obtain ⟨hxQ, hcomm, -, -⟩ := h1 x hx hnc
  have hxC : x ∈ Subgroup.centralizer ({x} : Set K) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  have hAQ : A ≤ BMOpCent p x := ggSporK_le_opCent hAC hAnorm hAel.2
  have hNC : A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set K) :=
    sup_le hAC (Subgroup.zpowers_le.mpr hxC)
  have hNQ : A ⊔ Subgroup.zpowers x ≤ BMOpCent p x :=
    sup_le hAQ (Subgroup.zpowers_le.mpr hxQ)
  have hNnorm : ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ n ∈ A ⊔ Subgroup.zpowers x,
      g * n * g⁻¹ ∈ A ⊔ Subgroup.zpowers x := by
    intro g hg n hn
    have hle : A ⊔ Subgroup.zpowers x ≤
        (A ⊔ Subgroup.zpowers x).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_sup_left (hAnorm g hg a ha)
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hc : Commute g x := (Subgroup.mem_centralizer_iff.mp hg x rfl).symm
        show g * x ^ k * g⁻¹ ∈ A ⊔ Subgroup.zpowers x
        rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    exact hle hn
  have hQA : A ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer (A : Set K) := by
    refine sup_le (fun q hq => ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨h, hh⟩ ⟨q, hq⟩)
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hAC hh)) x rfl).symm
  have hxcQ : x ∈ Subgroup.centralizer ((A ⊔ Subgroup.zpowers x : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.mp (hNC hh)) x rfl).symm
  have hQc : A ⊔ Subgroup.zpowers x ≤
      Subgroup.centralizer ((A ⊔ Subgroup.zpowers x : Subgroup K) : Set K) := by
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr hxcQ)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hQA hh) a ha).symm
  have hQQ : ⁅A ⊔ Subgroup.zpowers x, A ⊔ Subgroup.zpowers x⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.mp (hQc h₂) g₁ h₁
  rcases h4 x hx hnc (A ⊔ Subgroup.zpowers x) hNC hNnorm le_sup_right hNQ with hN | hN
  · exact le_sup_left.trans hN.le
  · exfalso
    have hxQQ : x ∈ ⁅A ⊔ Subgroup.zpowers x, A ⊔ Subgroup.zpowers x⁆ := by
      rw [hN, hcomm]
      exact Subgroup.mem_zpowers x
    have hx1 : x = 1 := Subgroup.mem_bot.mp (hQQ hxQQ)
    have hp1 : p = 1 := by rw [← hx, hx1, orderOf_one]
    exact (Fact.out : p.Prime).ne_one hp1

end CFSG.StandardType.SporadicShape
