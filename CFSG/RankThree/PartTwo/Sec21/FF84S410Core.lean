module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Ne
public import CFSG.RankThree.PartTwo.Sec21.FF84S31Tools
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Gen
public import CFSG.RankThree.PartTwo.Sec21.FF84S410Card

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] {S : Subgroup G}

theorem qMinus_zero : qMinus (0 : F6) = 0 := by decide

theorem conjBy_eq_of_mem_nor {n : G} (hn : n ∈ Nor S) : conjBy n S = S := by
  ext x
  rw [S3.mem_conjBy_iff]
  have := Subgroup.mem_normalizer_iff.1 (inv_mem hn) x
  simp only [inv_inv] at this
  exact this.symm

theorem op2_cen_conj_iff [Finite G] {n : G} (hn : n ∈ Nor S) (x : G) :
    Op 2 (Cen (n * x * n⁻¹)) = S ↔ Op 2 (Cen x) = S := by
  rw [S3.Cen_conjBy, S3.Op_conjBy]
  constructor
  · intro h
    have h2 := congrArg (conjBy n⁻¹) h
    rw [S3.conjBy_conjBy_inv, conjBy_eq_of_mem_nor (inv_mem hn)] at h2
    exact h2
  · intro h
    rw [h, conjBy_eq_of_mem_nor hn]

theorem cen_of_psi0_eq_one (e : ↥S ≃* Multiplicative F6) (n : ↥(Nor S)) (h : psi0 e n = 1)
    (z : ↥S) : (n : G) * (z : G) * (n : G)⁻¹ = (z : G) := by
  have h1 := psi0_apply e n z
  rw [h] at h1
  have h2 : e ⟨(n : G) * (z : G) * (n : G)⁻¹, (n.2 (z : G)).mp z.2⟩ = e z :=
    Multiplicative.toAdd.injective h1.symm
  exact congrArg Subtype.val (e.injective h2)

theorem psi0_preserves_q [Finite G] (e : ↥S ≃* Multiplicative F6)
    (hq : ∀ x : ↥S, (x : G) ≠ 1 →
      (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = S))
    (n : ↥(Nor S)) (v : F6) : qMinus (psi0 e n v) = qMinus v := by
  obtain ⟨z, rfl⟩ : ∃ z : ↥S, Multiplicative.toAdd (e z) = v :=
    ⟨e.symm (Multiplicative.ofAdd v), by simp⟩
  rw [psi0_apply]
  by_cases h1 : (z : G) = 1
  · have hz : z = 1 := Subtype.ext h1
    have h2 : (⟨(n : G) * (z : G) * (n : G)⁻¹, (n.2 (z : G)).mp z.2⟩ : ↥S) = z :=
      Subtype.ext (by simp [h1])
    rw [h2]
  · have h2 : ((⟨(n : G) * (z : G) * (n : G)⁻¹, (n.2 (z : G)).mp z.2⟩ : ↥S) : G) ≠ 1 := by
      intro h
      apply h1
      have : (n : G) * (z : G) * (n : G)⁻¹ = 1 := h
      simpa using this
    have hiff : qMinus (Multiplicative.toAdd (e z)) = 1 ↔
        qMinus (Multiplicative.toAdd (e ⟨(n : G) * (z : G) * (n : G)⁻¹,
          (n.2 (z : G)).mp z.2⟩)) = 1 :=
      (hq z h1).trans ((op2_cen_conj_iff n.2 (z : G)).symm.trans
        (hq ⟨(n : G) * (z : G) * (n : G)⁻¹, (n.2 (z : G)).mp z.2⟩ h2).symm)
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hb (qMinus (Multiplicative.toAdd (e z))) with hA | hA <;>
      rcases hb (qMinus (Multiplicative.toAdd (e ⟨(n : G) * (z : G) * (n : G)⁻¹,
        (n.2 (z : G)).mp z.2⟩))) with hA' | hA'
    · rw [hA, hA']
    · exact absurd (hiff.2 hA') (by rw [hA]; decide)
    · exact absurd (hiff.1 hA) (by rw [hA']; decide)
    · rw [hA, hA']

theorem omegaData_of_core [Finite G] {B : Subgroup G} (e : ↥S ≃* Multiplicative F6)
    (hSE : IsElemAb 2 6 S) (hBE : IsElemAb 3 3 B) (hBS : B ≤ Nor S)
    (hq : ∀ x : ↥S, (x : G) ≠ 1 →
      (qMinus (Multiplicative.toAdd (e x)) = 1 ↔ Op 2 (Cen (x : G)) = S))
    (htrans : ∀ x y : G, x ∈ S → y ∈ S → x ≠ 1 → y ≠ 1 → Op 2 (Cen x) = S →
      Op 2 (Cen y) = S → ∃ n ∈ Nor S, n * x * n⁻¹ = y)
    (hker : Nor S ⊓ CenS S ≤ S)
    (hS6 : ∃ s₀ ∈ S, s₀ ≠ 1 ∧ Op 2 (Cen s₀) = S ∧ ∃ H : Subgroup G, H ≤ Cen s₀ ∧
      Nonempty (↥H ≃* Equiv.Perm (Fin 6)) ∧ H ⊓ S = ⊥)
    (hcard : Nat.card ↥(Nor B ⊓ Nor S) ≤ 648) (hE27 : HypOmNormalizerE27) :
    FF84OmegaDataFor S e := by
  classical
  haveI := hSE.1
  have hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : S) ⟨y, hy⟩)
  have hinv := psi0_preserves_q e hq
  have hker' : ∀ n : ↥(Nor S), psi0 e n = 1 → (n : G) ∈ S := by
    intro n hn
    refine hker (Subgroup.mem_inf.2 ⟨n.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := cen_of_psi0_eq_one e n hn ⟨z, hz⟩
    have h2 : (n : G) * z = z * (n : G) := by
      have := congrArg (fun w => w * (n : G)) this
      simpa [mul_assoc] using this
    exact h2.symm
  have hO := range_psi0_le_O e hinv
  obtain ⟨s₀, hs₀S, hs₀1, hs₀O, H, hHc, ⟨hHe⟩, hHS⟩ := hS6
  have hHN : H ≤ Nor S := fun g hg => by
    have := le_nor_op2 (Cen s₀) (hHc hg)
    rwa [hs₀O] at this
  have hq0 : ∀ v : F6, qMinus v = 1 → v ≠ 0 := by
    rintro v hv rfl
    rw [qMinus_zero] at hv
    exact absurd hv (by decide)
  have hq₀ : qMinus (Multiplicative.toAdd (e ⟨s₀, hs₀S⟩)) = 1 := (hq ⟨s₀, hs₀S⟩ hs₀1).2 hs₀O
  have hcardR : 25920 ≤ Nat.card (psi0 e).range := by
    refine card_range_psi0_ge e (Multiplicative.toAdd (e ⟨s₀, hs₀S⟩)) {v : F6 | qMinus v = 1}
      (by rw [Om_nonsing_ncard]) ?_ (H.subgroupOf (Nor S)) ?_ ?_ ?_
    · intro v hv
      have hv' : qMinus v = 1 := hv
      set x : ↥S := e.symm (Multiplicative.ofAdd v) with hx
      have hex : Multiplicative.toAdd (e x) = v := by simp [hx]
      have hx1 : (x : G) ≠ 1 := by
        intro h
        have : x = 1 := Subtype.ext h
        rw [this, map_one] at hex
        exact hq0 v hv' hex.symm
      have hxO : Op 2 (Cen (x : G)) = S := (hq x hx1).1 (by rw [hex]; exact hv')
      obtain ⟨n, hn, hnx⟩ := htrans s₀ x hs₀S x.2 hs₀1 hx1 hs₀O hxO
      refine ⟨⟨n, hn⟩, ?_⟩
      rw [psi0_apply, ← hex]
      congr 2
      exact Subtype.ext hnx
    · intro n hn
      have hn' : (n : G) ∈ H := hn
      have hc : (n : G) * s₀ * (n : G)⁻¹ = s₀ := by
        have := Subgroup.mem_centralizer_singleton_iff.1 (hHc hn')
        rw [this]
        group
      rw [psi0_apply]
      congr 2
      exact Subtype.ext hc
    · intro n hn h1
      have h2 : (n : G) ∈ S := hker' n h1
      have h3 : (n : G) ∈ H := hn
      have : (n : G) ∈ H ⊓ S := Subgroup.mem_inf.2 ⟨h3, h2⟩
      rw [hHS] at this
      exact Subtype.ext (Subgroup.mem_bot.1 this)
    · have h1 : Nat.card (H.subgroupOf (Nor S)) = Nat.card H :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
      rw [h1, Nat.card_congr hHe.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hrΩ : (psi0 e).range = CFSG.Open.timmesfeldOmega qMinus := by
    rcases eq_Omega_or_eq_O _ hO hcardR with h | h
    · exact h
    · exact absurd h (range_psi0_ne_O e hSE hBE hBS hker' hcard hE27)
  have hmemΩ : ∀ n : ↥(Nor S), psi0 e n ∈ CFSG.Open.timmesfeldOmega qMinus := fun n => by
    rw [← hrΩ]
    exact ⟨n, rfl⟩
  refine ⟨(psi0 e).codRestrict _ hmemΩ, ?_, ?_, ?_, hq⟩
  · intro g
    have : (g : F6 ≃ₗ[ZMod 2] F6) ∈ (psi0 e).range := by
      rw [hrΩ]
      exact g.2
    obtain ⟨n, hn⟩ := this
    exact ⟨n, Subtype.ext hn⟩
  · ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine hker' n ?_
      have := congrArg Subtype.val h
      exact this
    · intro h
      refine Subtype.ext ?_
      exact psi0_eq_one_of_cen e n (fun z => hSc _ h _ z.2)
  · intro n hn x
    have hx : n * (x : G) * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hn (x : G)).1 x.2
    refine ⟨hx, ?_⟩
    have := psi0_apply e ⟨n, hn⟩ x
    show e ⟨n * (x : G) * n⁻¹, hx⟩ = Multiplicative.ofAdd (psi0 e ⟨n, hn⟩ (Multiplicative.toAdd (e x)))
    rw [this]
    rfl

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
