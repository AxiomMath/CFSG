module

public import Certificates.Kernel.Co2Three.UqChecks
public import Certificates.Kernel.Co2Three.Glue
public import CFSG.Certificates.Kernel.Co2Three.AbelConj

public section

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2 CertificateChecks.KernelMisc.Co2K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Certificates.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2
open CFSG.KC.Co2Three

@[expose] noncomputable def qσ (i : ℕ) : Equiv.Perm (Fin 2300) :=
  permOfArr 2300 (permOfMat 22 co2FiveV (QP i))

theorem qσ_rep {i : ℕ} (hi : i < 729) : Rep 2300 (permOfMat 22 co2FiveV (QP i)) (qσ i) :=
  rep_of_validA (by rw [← qCert2_pt hi]; exact kqPts_valid i hi)

theorem qσ_mem {i : ℕ} (hi : i < 729) : qσ i ∈ Qg :=
  (kmem_Qg_iff _).2 ⟨i, hi, by rw [qCert2_pt hi]; rfl⟩

theorem qσ_mul {a b c d : ℕ} (ha : a < 729) (hb : b < 729) (hc : c < 729) (hd : d < 729)
    (h : mmK (QP a) (QP b) = mmK (QP c) (QP d)) : qσ b * qσ a = qσ d * qσ c := by
  have e := congrArg (fun M => permOfArr 2300 (permOfMat 22 co2FiveV M)) h
  rw [← compA_good (good_QP ha), ← compA_good (good_QP hc),
    CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_compA (qσ_rep hb) (qσ_rep ha)),
    CFSG.RankThree.Native.permOfArr_eq_of_rep (rep_compA (qσ_rep hd) (qσ_rep hc))] at e
  exact e

theorem qσ_comm {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    comm (QP a) (QP b) = true ↔ qσ a * qσ b = qσ b * qσ a := by
  rw [← commA_good (good_QP ha) (good_QP hb)]
  exact commA_iff (qσ_rep ha) (qσ_rep hb)

theorem qσ_ne {a b : ℕ} (ha : a < 729) (hb : b < 729) (h : Nat.beq (QP a) (QP b) = false) :
    qσ a ≠ qσ b := fun e => by
  have h' := (eqA_iff (qσ_rep ha) (qσ_rep hb)).2 e
  rw [eqA_good (good_QP ha) (good_QP hb), h] at h'
  exact Bool.false_ne_true h'

theorem rec_facts {c : ℕ} (hc : c < 24) :
    (∀ s < 9, uqF (Uq 0) c s < 729 ∧ uqF (Uq 0) c (9 + s) < 729 ∧
      qσ (uqF (Uq 0) c (9 + s)) =
        (qσ (uqF (Uq 0) c s))⁻¹ * qσ (uqF (Uq 0) c 9) * qσ (uqF (Uq 0) c s)) ∧
    (∀ a < 9, ∀ b < 9, a ≠ b → qσ (uqF (Uq 0) c (9 + a)) ≠ qσ (uqF (Uq 0) c (9 + b))) ∧
    uqF (Uq 0) c 18 < 729 ∧ uqF (Uq 0) c 19 < 729 ∧
    qσ (uqF (Uq 0) c 9) * qσ (uqF (Uq 0) c 18) = qσ (uqF (Uq 0) c 18) * qσ (uqF (Uq 0) c 9) ∧
    qσ (uqF (Uq 0) c 9) * qσ (uqF (Uq 0) c 19) = qσ (uqF (Uq 0) c 19) * qσ (uqF (Uq 0) c 9) ∧
    qσ (uqF (Uq 0) c 18) * qσ (uqF (Uq 0) c 19) ≠
      qσ (uqF (Uq 0) c 19) * qσ (uqF (Uq 0) c 18) := by
  have h := ch101704C_all c hc
  unfold ch101704C clsK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.add_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hS, hD⟩, h18⟩, h19⟩, hc1⟩, hc2⟩, hn⟩ := h
  have hS' := allN_spec hS
  have ht0 : uqF (Uq 0) c 9 < 729 := by
    have := hS' 0 (by norm_num)
    simp only [Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.2
  refine ⟨fun s hs => ?_, fun a ha b hb hab => ?_, h18, h19, (qσ_comm ht0 h18).1 hc1,
    (qσ_comm ht0 h19).1 hc2, fun e => ?_⟩
  · have := hS' s hs
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    obtain ⟨⟨hg, ht⟩, he⟩ := this
    refine ⟨hg, ht, ?_⟩
    rw [mul_assoc, qσ_mul hg ht0 ht hg he, ← mul_assoc, inv_mul_cancel, one_mul]
  · have := allN_spec (allN_spec hD a ha) b hb
    simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
    have hlt (s : ℕ) (hs : s < 9) : uqF (Uq 0) c (9 + s) < 729 := by
      have := hS' s hs
      simp only [Bool.and_eq_true, Nat.blt_eq] at this
      exact this.1.2
    rcases this with h' | h'
    · exact absurd h' hab
    · exact qσ_ne (hlt a ha) (hlt b hb) h'
  · rw [← qσ_comm h18 h19, hn] at e
    exact Bool.false_ne_true e

theorem fus_at {j : ℕ} (hj : j < 729) : fusK HM HMI (QP j) (FKd j) (FH j) (FE j) = true :=
  of_chunk81 (f := fun j => fusK HM HMI (QP j) (FKd j) (FH j) (FE j)) hj fun c hc => by
    have h := ch13636Fus_all c hc
    unfold ch13636Fus at h
    exact h

theorem pt_at {j : ℕ} (hj : j < 729) : ptK (Uq 0) FKd UC US j = true :=
  of_chunk81 (f := fun j => ptK (Uq 0) FKd UC US j) hj fun c hc => by
    have h := ch101704P_all c hc
    unfold ch101704P at h
    exact h

theorem false_of_kind {A : Subgroup (Equiv.Perm (Fin 2300))} (hAQ : A ≤ Qg)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcard : Nat.card A = 81) {j : ℕ} (hj : j < 729)
    (hk : ¬FKd j < 2) (hjA : qσ j ∈ A) : False := by
  have hp := pt_at hj
  unfold ptK at hp
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq] at hp
  obtain ⟨⟨hc, hs⟩, hjt⟩ := hp.resolve_left hk
  obtain ⟨hS, hD, h18, h19, c₁, c₂, hn⟩ := rec_facts hc
  obtain ⟨hg, -, hgt⟩ := hS (US j) hs
  rw [hjt] at hgt
  generalize uqF (Uq 0) (UC j) (US j) = g at hg hgt
  set x := qσ (uqF (Uq 0) (UC j) 9)
  set B := A.map (MulAut.conj (qσ g)).toMonoidHom
  have hxB : x ∈ B := ⟨qσ j, hjA, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hgt]
    group⟩
  have hBQ : B ≤ Qg := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Qg.mul_mem (Qg.mul_mem (qσ_mem hg) (hAQ ha)) (Qg.inv_mem (qσ_mem hg))
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA a ha b hb]
  have hBcard : Nat.card B = 81 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (qσ g)).injective, hcard]
  refine false_of_conj (Q := Qg) (m := 9) hBQ hBc (le_of_eq (by rw [kcard_Qg, hBcard])) hxB
    (fun i => (qσ (uqF (Uq 0) (UC j) i.val))⁻¹) (fun i => Qg.inv_mem (qσ_mem (hS i.val i.2).1))
    (fun a b e => ?_) (qσ_mem h18) (qσ_mem h19) c₁ c₂ hn
  have hconj (i : Fin 9) : (qσ (uqF (Uq 0) (UC j) i.val))⁻¹ * x *
      (qσ (uqF (Uq 0) (UC j) i.val))⁻¹⁻¹ = qσ (uqF (Uq 0) (UC j) (9 + i.val)) := by
    rw [inv_inv, (hS i.val i.2).2.2]
  simp only [hconj] at e
  by_contra hab
  exact hD a.val a.2 b.val b.2 (fun h => hab (Fin.ext h)) e

theorem kuniq (A : Subgroup (Equiv.Perm (Fin 2300))) (hAQ : A ≤ Qg)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h3 : ∀ x ∈ A, x ^ 3 = 1) (hcard : Nat.card A = 81) :
    A ≤ Subgroup.closure {x | ∃ k < 81, dEltP k = x} := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := (kmem_Qg_iff a).1 (hAQ ha)
  rw [qCert2_pt hj] at ha ⊢
  change qσ j ∈ A at ha
  change qσ j ∈ _
  have hf := fus_at hj
  by_cases h0 : FKd j = 0
  · rw [h0] at hf
    change (!(Nat.beq (pwK (QP j) 3) I22) || Nat.beq (QP j) I22) = true at hf
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hf
    rcases hf with hf | hf
    · have h' := (eqA_iff (rep_powArr (qσ_rep hj) 3) rep_idA).2 (h3 _ ha)
      rw [pow_good (good_QP hj), idA_eq, eqA_good (good_pw (good_QP hj) 3) good_I22, hf] at h'
      exact absurd h' Bool.false_ne_true
    · have h' : eqA 2300 (permOfMat 22 co2FiveV (QP j)) (idA 2300) = true := by
        rw [idA_eq, eqA_good (good_QP hj) good_I22]
        exact hf
      rw [(eqA_iff (qσ_rep hj) rep_idA).1 h']
      exact Subgroup.one_mem _
  by_cases h1 : FKd j = 1
  · rw [h1] at hf
    change (Nat.blt (FE j) 81 && Nat.beq (CertificateChecks.KernelCo2Pump.ED (FE j)) (QP j)) =
      true at hf
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hf
    refine Subgroup.subset_closure ⟨FE j, hf.1, ?_⟩
    rw [dEltP, (CertificateChecks.KernelCo2Pump.eG hf.1).1, hf.2]
    rfl
  exact (false_of_kind hAQ hA hcard hj (by omega) ha).elim

end CertificateChecks.KernelCo2Three

end
