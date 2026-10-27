module

public import CFSG.RankThree.GF2n.Tim79a34BigModel
public import CFSG.RankThree.GF2n.Tim79a34CentreSmall
public import CFSG.RankThree.GF2n.Tim79a34IW
public import CFSG.RankThree.GF2n.Tim79a34Lemma12
public import CFSG.RankThree.GF2n.Tim79a34BigBar
public import CFSG.RankThree.GF2n.Tim79a34BigNatural

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem bigPQ_comm_of_sup [Finite G] {M V Q P H : Subgroup G} (hc : MinCex M V Q P H)
    (hcomm : ⁅P, P⁆ = V ⊓ wOf V H) {C : Subgroup G} (hCQ : C ≤ Q) (hPCQ : P ⊔ C = Q)
    (hPC : ∀ p ∈ P, ∀ c ∈ C, ⁅p, c⁆ ∈ V ⊓ wOf V H)
    (hCW : ∀ c ∈ C, ∀ w ∈ wOf V H, c * w = w * c) :
    (∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V ⊓ wOf V H) ∧
      ∀ q ∈ Q, ∀ a ∈ V ⊓ wOf V H, q * a = a * q := by
  have hQM : Q ≤ M := by
    rw [hc.hQ]
    exact (inSubgroup_pCore_two M).2.1
  have hCN : C ≤ Subgroup.normalizer (P : Set G) := fun c hcC =>
    hc.M_le_normalizer_P (hQM (hCQ hcC))
  have hPcentA : ∀ p ∈ P, ∀ v ∈ (V ⊓ wOf V H : Subgroup G), p * v * p⁻¹ = v := by
    intro p hp v hv
    rw [← hc.commute_of_mem_P hp (Subgroup.mem_inf.mp hv).1, mul_inv_cancel_right]
  have hCcentA : ∀ c ∈ C, ∀ v ∈ (V ⊓ wOf V H : Subgroup G), c * v * c⁻¹ = v := by
    intro c hcC v hv
    rw [hCW c hcC v (Subgroup.mem_inf.mp hv).2, mul_inv_cancel_right]
  have hPPc : ∀ p ∈ P, ∀ x ∈ P, ⁅p, x⁆ ∈ (V ⊓ wOf V H : Subgroup G) := fun p hp x hx => by
    have h := Subgroup.commutator_mem_commutator hp hx
    rwa [hcomm] at h
  have key := l12_sup_normalizes (l12_le_normalizer hPcentA) (l12_le_normalizer hCcentA) hPPc hPC
  refine ⟨fun q hq x hx => ?_, fun q hq a ha => ?_⟩
  · rw [← commutatorElement_inv]
    exact (V ⊓ wOf V H).inv_mem (key q (hPCQ ▸ hq) x hx)
  · obtain ⟨p, hp, c, hcC, rfl⟩ :=
      CFSG.RankThree.GF2n.exists_mul_of_mem_sup hCN (hPCQ ▸ hq)
    calc p * c * a = p * (c * a) := mul_assoc _ _ _
      _ = p * (a * c) := by rw [hCW c hcC a (Subgroup.mem_inf.mp ha).2]
      _ = p * a * c := (mul_assoc _ _ _).symm
      _ = a * p * c := by rw [← hc.commute_of_mem_P hp (Subgroup.mem_inf.mp ha).1]
      _ = a * (p * c) := mul_assoc _ _ _

theorem bigPDerivedStatement_of_local (hZ : Sec34CentreTrivialStatement) (hIW : BigIWStatement)
    (hComm : BigPCommutatorStatement) : BigPDerivedStatement := by
  intro G _ _ M V Q P H hH
  have hcentre := hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP := hIW G M V Q P H hH hcentre
  obtain ⟨hcomm, -, -⟩ := hComm G M V Q P H hH hcentre hcP
  refine ⟨fun x hx y hy => ?_, hcomm.ge⟩
  have h := Subgroup.commutator_mem_commutator hx hy
  rwa [hcomm] at h

theorem bigPQCommStatement_of_local (hZ : Sec34CentreTrivialStatement) (hIW : BigIWStatement)
    (hγ : BigGammaStatement) (hComm : BigPCommutatorStatement) : BigPQCommStatement := by
  intro G _ _ M V Q P H hH
  have hcentre := hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP := hIW G M V Q P H hH hcentre
  obtain ⟨hcomm, -, -⟩ := hComm G M V Q P H hH hcentre hcP
  obtain ⟨C, hCQ, hPCQ, hPC, hCW, -, -⟩ := hγ G M V Q P H hH hcentre
  exact bigPQ_comm_of_sup hH.setup.mc.toMinCex hcomm hCQ hPCQ hPC hCW

theorem bigPOrderStatement_of_local (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hLoc : BigPLocalStatement) : BigPOrderStatement := by
  intro G _ _ M V Q P H hH n f hn2 hfq ⟨e⟩
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre := hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP := hIW G M V Q P H hH hcentre
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      have h4 := hH.q_big
      rw [← hfq, h] at h4
      norm_num at h4
    · exact h
  have hV : Nat.card ↥V = 2 ^ (2 * f) := by
    have h1 := twb_card_barOf_mul (V := V) (H := H) (K := V) hVH
    rw [hH.module] at h1
    have h2 : Nat.card ↥(barOf V H V) = qBar V H := rfl
    rw [h2, ← hfq] at h1
    rw [← h1, ← pow_add, two_mul]
  obtain ⟨n', f', Φ, ψ, hn', hf'q, hequiv, ⟨a, T, ha, hTa, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hcentre
  obtain rfl : f' = f := Nat.pow_right_injective (le_refl 2) (hf'q.trans hfq.symm)
  have e' : ↥(StatedSp n (GaloisField 2 f')) ≃* Xbar V H :=
    e.trans (MulEquiv.ofBijective (projZ V H) (iw_projZ_bijective hcentre)).symm
  have hcard : Nat.card ↥(StatedSp n' (GaloisField 2 f')) =
      Nat.card ↥(StatedSp n (GaloisField 2 f')) := Nat.card_congr (Φ.trans e'.symm).toEquiv
  have hval := padicValNat_card_statedSp f' hf n'
  rw [hcard, padicValNat_card_statedSp f' hf n] at hval
  obtain rfl : n' = n := by
    have h1 : n ^ 2 = n' ^ 2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f') hval
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1).symm
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨-, -, -, hPcard⟩ := hLoc G M V Q P H hH hcentre hcP hfq Φ ψ hNat a T ha hTa hTV
  refine ⟨?_, hV⟩
  rw [hPcard, ← hfq, ← pow_mul]

theorem bigQWStatement_of_local (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (hLoc : BigPLocalStatement)
    (hComm : BigPCommutatorStatement) (hCover : BigPCoverStatement) : BigQWStatement := by
  intro G _ _ M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hcentre := hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hfq, hequiv, ⟨a, T, ha, hTa, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hVH Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨hcomm, -, -⟩ := hComm G M V Q P H hH hcentre hcP
  obtain ⟨hPiff, -, -, -⟩ := hLoc G M V Q P H hH hcentre hcP hfq Φ ψ hNat a T ha hTa hTV
  obtain ⟨C, hCQ, hPCQ, hPC, hCW, -, -⟩ := hγ G M V Q P H hH hcentre
  obtain ⟨hPR, -⟩ := bigPQ_comm_of_sup hc hcomm hCQ hPCQ hPC hCW
  have hq4 : 4 ≤ qBar V H := hH.q_big
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [← hfq] at hq4
    norm_num at hq4
  have hWcard : Nat.card ↥(wOf V H) = qBar V H ^ (2 * n) := by
    have h1 : Nat.card (Fin n ⊕ Fin n → GaloisField 2 f) = Nat.card ↥(wOf V H) :=
      Nat.card_congr (ψ.toEquiv.trans Additive.toMul)
    rw [← h1, Nat.card_fun, Nat.card_sum, GaloisField.card 2 f hf0, ← hfq]
    simp [two_mul, Nat.card_eq_fintype_card]
  have hsplit := twistedWSplit_holds G M V Q P H hH.setup hH.concl
  rw [hH.module, hWcard] at hsplit
  have hWQ : ∀ w ∈ wOf V H, w ∈ Q → w ∈ P := by
    intro w hwW hwQ
    by_contra hwP
    obtain ⟨b, hbw⟩ : ∃ b : Fin n ⊕ Fin n → GaloisField 2 f,
        ((Additive.toMul (ψ b) : ↥(wOf V H)) : G) = w :=
      ⟨ψ.symm (Additive.ofMul ⟨w, hwW⟩), by
        rw [AddEquiv.apply_symm_apply]
        rfl⟩
    have hbP : CaseM.spForm a b ≠ 0 := fun h => hwP (hbw ▸ (hPiff b).mpr h)
    have hcov := hCover G M V Q P H hH hcentre hcP hfq Φ ψ hNat a T ha hTa hTV b hbP
    have hPWsub : P ⊓ wOf V H ≤ V ⊓ wOf V H := by
      intro u hu
      obtain ⟨p, hp, hpu⟩ := hcov u hu
      rw [hbw] at hpu
      rw [← hpu, ← commutatorElement_inv]
      exact (V ⊓ wOf V H).inv_mem (hPR w hwQ p hp)
    have hcardle : Nat.card ↥(P ⊓ wOf V H) ≤ qBar V H := by
      rw [← hH.module]
      exact Subgroup.card_le_of_le hPWsub
    have h1 : qBar V H ^ (2 * n) ≤ qBar V H ^ 2 := by
      rw [hsplit, sq]
      exact Nat.mul_le_mul_right _ hcardle
    have h2 : qBar V H ^ 2 < qBar V H ^ (2 * n) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    exact absurd h1 (not_le.mpr h2)
  apply le_antisymm
  · intro w hw
    obtain ⟨hwQ, hwW⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨hWQ w hwW hwQ, hwW⟩
  · intro w hw
    obtain ⟨hwP, hwW⟩ := Subgroup.mem_inf.mp hw
    exact Subgroup.mem_inf.mpr ⟨hc.P_le_Q hwP, hwW⟩

end CFSG.RankThree.GF2n.Tim79a
