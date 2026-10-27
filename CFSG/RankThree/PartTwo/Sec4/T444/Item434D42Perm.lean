module

public import Certificates.Certificate9542
public import Certificates.Certificate9544
public import Certificates.Certificate9545
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434D42

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.RankThree.PartTwo.KFacts.K426

theorem d4_chain_check :
    caseChainOK2P 2457 d4ChainAArrs d4ChainABaseArr d4ChainAWords d4GenA d4GenB = true ∧
      rawOrbitSizes 2457 d4ChainAArrs d4ChainABaseArr = [2457, 2048, 7, 1, 1, 3, 2] :=
  Certificates.certificate9542.1

theorem d4_lines_check :
    linesOK3 3 81 31 2457 d4QGens d4Keys d4QCert d4Lines = true ∧
      allLt d4QGens.size (fun l => siftA 2457 d4LevelsA d4ChainABaseArr 0 d4QGens[l]!) = true ∧
      transOK2 31 2457 d4Trans d4Lines d4Lines d4Rec d4LevelsA d4ChainABaseArr = true ∧
      allLt 31 (fun j => decide (d4Rec.getD j 0 < 2)) = true :=
  Certificates.certificate9542.2.1

theorem d4_caseA_check :
    centOKP 3 2457 d4ChainAArrs d4ChainABaseArr d4Lines[0]! d4RelsA d4CAGens d4Keys d4CACert
      1512 = true :=
  Certificates.certificate9542.2.2

theorem d4_caseB_check :
    caseChainOK2P 2457 d4ChainBArrs d4ChainBBaseArr d4ChainBWords d4GenA d4GenB = true ∧
      centOKP 3 2457 d4ChainBArrs d4ChainBBaseArr d4Lines[1]! d4RelsB d4CBGens d4Keys d4CBCert
        648 = true :=
  Certificates.certificate9545

theorem d4_local_check :
    localOK 2457 2457 d4Lines[0]! d4CACert.pts d4SelfPtA d4PairWitA = true ∧
      localOK 2457 2457 d4Lines[1]! d4CBCert.pts d4SelfPtB d4PairWitB = true :=
  Certificates.certificate9544

@[expose] noncomputable def d4A : Equiv.Perm (Fin 2457) := permOfArr 2457 d4GenA

@[expose] noncomputable def d4B : Equiv.Perm (Fin 2457) := permOfArr 2457 d4GenB

@[expose] noncomputable def d4P : Subgroup (Equiv.Perm (Fin 2457)) := closure {d4A, d4B}

theorem rep_d4A : Rep 2457 d4GenA d4A := by
  obtain ⟨hc, -, -⟩ := caseChainOK2P_parts d4_chain_check.1
  exact (rep_permOfArr ((chainCheckFacts hc).strong_inv 0 (by simp [d4ChainAArrs]))).1

theorem rep_d4B : Rep 2457 d4GenB d4B := by
  obtain ⟨hc, -, -⟩ := caseChainOK2P_parts d4_chain_check.1
  exact (rep_permOfArr ((chainCheckFacts hc).strong_inv 1 (by simp [d4ChainAArrs]))).1

theorem d4ChainABase_nodup : d4ChainABase.Nodup := by decide

theorem d4ChainBBase_nodup : d4ChainBBase.Nodup := by decide

theorem d4Keys_lt : ∀ q ∈ d4Keys, q < 2457 := by decide

theorem mem_d4P_of_sift {g : Array ℕ}
    {G : Equiv.Perm (Fin 2457)} (hG : Rep 2457 g G)
    (h : siftA 2457 d4LevelsA d4ChainABaseArr 0 g = true) : G ∈ d4P :=
  mem_closure_two_of_siftG (by norm_num) (by simp [d4ChainAArrs]) d4ChainABase_nodup rep_d4A
    rep_d4B d4_chain_check.1 hG h

theorem card_d4P : Nat.card d4P = 211341312 := by
  have h := card_closure_two_of_chainOK (by norm_num) (by simp [d4ChainAArrs])
    d4ChainABase_nodup rep_d4A rep_d4B d4_chain_check.1
  rw [d4P, h]
  change (rawOrbitSizes 2457 d4ChainAArrs d4ChainABaseArr).prod = _
  rw [d4_chain_check.2]
  norm_num

theorem factorization_card_d4P_three :
    (Nat.card d4P).factorization 3 = 4 := by
  rw [card_d4P, show (211341312 : ℕ) = 3 ^ 4 * 2609152 by norm_num]
  exact factorization_pow_mulG Nat.prime_three (by norm_num)

@[expose] noncomputable def d4Q : Subgroup (Equiv.Perm (Fin 2457)) :=
  closure (permsA 2457 d4QGens)

theorem d4Q_le : d4Q ≤ d4P := by
  rw [d4Q, closure_le]
  rintro _ ⟨l, hl, rfl⟩
  exact mem_d4P_of_sift (rep_of_validA (enumOK_gens_valid (linesOK3_parts d4_lines_check.1).1 hl))
    (allLt_spec d4_lines_check.2.1 hl)

theorem card_d4Q :
    Nat.card d4Q = 3 ^ (Nat.card d4P).factorization 3 := by
  rw [factorization_card_d4P_three, d4Q, linesOK3_card d4Keys_lt d4_lines_check.1]
  norm_num

theorem d4Lines_valid {j : ℕ} (hj : j < 31) :
    validA 2457 d4Lines[j]! = true :=
  (linesOK3_line d4_lines_check.1 hj).1

theorem d4_lines {g : Equiv.Perm (Fin 2457)} (hg : g ∈ d4Q)
    (hg3 : g ^ 3 = 1) : g = 1 ∨ ∃ j < 31, ∃ e < 3, g = permOfArr 2457 d4Lines[j]! ^ e :=
  linesOK3_spec d4Keys_lt d4_lines_check.1 hg hg3

theorem d4_trans {j : ℕ} (hj : j < 31) :
    permOfArr 2457 d4Trans[j]! ∈ d4P ∧
      permOfArr 2457 d4Trans[j]! * permOfArr 2457 d4Lines[d4Rec.getD j 0]! *
        (permOfArr 2457 d4Trans[j]!)⁻¹ = permOfArr 2457 d4Lines[j]! :=
  transOK2_spec mem_d4P_of_sift
    (fun j hj => d4Lines_valid (lt_trans (of_decide_eq_true
      (allLt_spec d4_lines_check.2.2.2 hj)) (by norm_num)))
    (fun j hj => d4Lines_valid hj) d4_lines_check.2.2.1 hj

@[expose] noncomputable def d4X (c : ℕ) : Equiv.Perm (Fin 2457) := permOfArr 2457 d4Lines[c]!

theorem d4X_cube {c : ℕ} (hc : c < 31) : d4X c ^ 3 = 1 :=
  (linesOK3_line d4_lines_check.1 hc).2

theorem d4_caseA :
    closure (permsA 2457 d4CAGens) = centralizer {d4X 0} ⊓ d4P ∧
      Nat.card (closure (permsA 2457 d4CAGens)) = 1512 :=
  case_centralizer2P (by norm_num) (by simp [d4ChainAArrs]) d4ChainABase_nodup rep_d4A rep_d4B
    d4_chain_check.1 (rep_of_validA (d4Lines_valid (by norm_num))) d4Keys_lt d4_caseA_check

theorem d4_caseB :
    closure (permsA 2457 d4CBGens) = centralizer {d4X 1} ⊓ d4P ∧
      Nat.card (closure (permsA 2457 d4CBGens)) = 648 :=
  case_centralizer2P (by norm_num) (by simp [d4ChainBArrs]) d4ChainBBase_nodup rep_d4A rep_d4B
    d4_caseB_check.1 (rep_of_validA (d4Lines_valid (by norm_num))) d4Keys_lt d4_caseB_check.2

theorem exists_mem_not_mem_zpowers {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE9 : Nat.card E = 9) (t : H) (ht3 : t ^ 3 = 1) : ∃ f ∈ E, f ∉ zpowers t := by
  by_contra hc
  push Not at hc
  have h1 := Subgroup.card_le_of_le (show E ≤ zpowers t from hc)
  rw [hE9, Nat.card_zpowers] at h1
  have h2 : orderOf t ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ht3)
  omega

theorem d4_step {gs : Array (Array ℕ)} {c : ArrCert} {x : Array ℕ} {X : Equiv.Perm (Fin 2457)}
    (hx : Rep 2457 x X) (hX3 : X ^ 3 = 1) {fuel : ℕ} {selfPt pairWit : Array ℕ}
    (hE : enumOK 2457 gs d4Keys c = true)
    (hloc : localOK 2457 fuel x c.pts selfPt pairWit = true)
    (hC : closure (permsA 2457 gs) = centralizer {X} ⊓ d4P)
    {E W : Subgroup (Equiv.Perm (Fin 2457))} (hEP : E ≤ d4P) (hWP : W ≤ d4P)
    (hEa : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hW : ¬ 3 ∣ Nat.card W)
    (hEW : E ≤ normalizer (W : Set (Equiv.Perm (Fin 2457)))) {e : ℕ} (he : e = 1 ∨ e = 2)
    (hXE : X ^ e ∈ E) : W ⊓ centralizer {X ^ e} ≤ ⊥ := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨u, huE, hu⟩ := exists_mem_not_mem_zpowers hE9 X hX3
  have hcomm : u * X ^ e = X ^ e * u := hEc u huE _ hXE
  have hcommX : u * X = X * u := by
    rcases he with rfl | rfl
    · simpa using hcomm
    · have h4 : X = (X ^ 2) ^ 2 := by
        rw [← pow_mul]
        calc X = X ^ 1 * 1 := by simp
          _ = X ^ 1 * X ^ 3 := by rw [hX3]
          _ = X ^ 4 := by rw [← pow_add]
      rw [h4]
      exact ((Commute.pow_right (show Commute u (X ^ 2) from hcomm) 2)).eq
  have huC : u ∈ closure (permsA 2457 gs) := by
    rw [hC]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcommX, hEP huE⟩
  have hu3 : u ^ 3 = 1 := hEa.2 u huE
  have hu1 : u ≠ 1 := fun h => hu (h ▸ one_mem _)
  have huX : u ≠ X := fun h => hu (h ▸ mem_zpowers X)
  have huX2 : u ≠ X ^ 2 := fun h => hu (h ▸ (pow_mem (mem_zpowers X) 2))
  have hcent : centralizer {X ^ e} ≤ centralizer {X} := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    rcases he with rfl | rfl
    · simpa using hz
    · have h4 : X = (X ^ 2) ^ 2 := by
        rw [← pow_mul]
        calc X = X ^ 1 * 1 := by simp
          _ = X ^ 1 * X ^ 3 := by rw [hX3]
          _ = X ^ 4 := by rw [← pow_add]
      rw [h4]
      exact ((Commute.pow_left (show Commute (X ^ 2) z from hz.symm) 2)).eq.symm
  set D := W ⊓ centralizer {X ^ e} with hD
  have hDC : D ≤ closure (permsA 2457 gs) := by
    rw [hC]
    exact le_inf (le_trans inf_le_right hcent) (le_trans inf_le_left hWP)
  have hD3 : ¬ 3 ∣ Nat.card D := fun h => hW (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have huD : u ∈ normalizer (D : Set (Equiv.Perm (Fin 2457))) := by
    have hCu : u ∈ centralizer {X ^ e} := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hEW huE, Subgroup.le_normalizer hCu⟩
  have hbot := eq_bot_of_localOK d4Keys_lt hE hx hloc huC hu3 hu1 huX huX2 hDC hD3 huD
  rw [hD] at hbot
  exact hbot.le

theorem d4_k3
    {E W : Subgroup (Equiv.Perm (Fin 2457))} (hEP : E ≤ d4P)
    (hWP : W ≤ d4P) (hEa : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hW : ¬ 3 ∣ Nat.card W) (hEW : E ≤ normalizer (W : Set (Equiv.Perm (Fin 2457)))) :
    W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hEa (by rw [hE9]; norm_num) hEW
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hW) fun v hvE hv1 => ?_
  have hv3 : v ^ 3 = 1 := hEa.2 v hvE
  have hvo : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  obtain ⟨k, hk, j, hj, e, he, hvk⟩ := exists_conj_rep d4Q_le card_d4Q
    (fun j => permOfArr 2457 d4Lines[j]!) (fun c => permOfArr 2457 d4Lines[c]!)
    (fun j => permOfArr 2457 d4Trans[j]!) (fun j => d4Rec.getD j 0) (r := 31)
    (fun g hg hg3 => d4_lines hg hg3) (fun j hj => d4_trans hj) (hEP hvE) hvo
  have hrec : d4Rec.getD j 0 < 2 := of_decide_eq_true (allLt_spec d4_lines_check.2.2.2 hj)
  set φ : Equiv.Perm (Fin 2457) →* Equiv.Perm (Fin 2457) := (MulAut.conj k⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj k⁻¹).injective
  have hφP : ∀ z ∈ d4P, φ z ∈ d4P := fun z hz => by
    change k⁻¹ * z * k⁻¹⁻¹ ∈ d4P
    exact d4P.mul_mem (d4P.mul_mem (d4P.inv_mem hk) hz) (by simpa using hk)
  have hφv : φ v = d4X (d4Rec.getD j 0) ^ e := by
    have h1 : φ v = k⁻¹ * v * k := by
      change k⁻¹ * v * k⁻¹⁻¹ = _
      rw [inv_inv]
    rw [h1, hvk]
    simp only [d4X]
    group
  have hE'P : E.map φ ≤ d4P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφP z (hEP hz)
  have hW'P : W.map φ ≤ d4P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hφP z (hWP hz)
  have hE'a : CFSG.Assembly.IsElemAbelian 3 (E.map φ) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 φ E hEa
  have hE'9 : Nat.card (E.map φ) = 9 := by rw [Subgroup.card_map_of_injective hφinj, hE9]
  have hW'3 : ¬ 3 ∣ Nat.card (W.map φ) := by rw [Subgroup.card_map_of_injective hφinj]; exact hW
  have hE'W' : E.map φ ≤ normalizer ((W.map φ : Subgroup _) : Set (Equiv.Perm (Fin 2457))) :=
    (Subgroup.map_mono hEW).trans (Subgroup.le_normalizer_map φ)
  have hvE' : φ v ∈ E.map φ := ⟨v, hvE, rfl⟩
  rw [hφv] at hvE'
  have hstep : W.map φ ⊓ centralizer {d4X (d4Rec.getD j 0) ^ e} ≤ ⊥ := by
    rcases (by omega : d4Rec.getD j 0 = 0 ∨ d4Rec.getD j 0 = 1) with h | h
    · rw [h] at hvE' ⊢
      exact d4_step (rep_of_validA (d4Lines_valid (by norm_num)))
        (d4X_cube (by norm_num)) (centOKP_enum d4_caseA_check) d4_local_check.1 d4_caseA.1
        hE'P hW'P hE'a hE'9 hW'3 hE'W' he hvE'
    · rw [h] at hvE' ⊢
      exact d4_step (rep_of_validA (d4Lines_valid (by norm_num)))
        (d4X_cube (by norm_num)) (centOKP_enum d4_caseB_check.2) d4_local_check.2 d4_caseB.1
        hE'P hW'P hE'a hE'9 hW'3 hE'W' he hvE'
  intro y hy
  have hyc : φ y ∈ centralizer ({φ v} : Set (Equiv.Perm (Fin 2457))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [← map_mul, ← map_mul, this]
  rw [hφv] at hyc
  have hy' : φ y ∈ W.map φ ⊓ centralizer {d4X (d4Rec.getD j 0) ^ e} := ⟨⟨y, hy.1, rfl⟩, hyc⟩
  have h1 : φ y = 1 := Subgroup.mem_bot.mp (hstep hy')
  rw [Subgroup.mem_bot]
  exact hφinj (by rw [h1, map_one])

theorem d4_k3_of_injective
    {X : Type*} [Group X] (ψ : X →* Equiv.Perm (Fin 2457))
    (hψ : Function.Injective ψ) (hrange : ∀ x, ψ x ∈ d4P) {E W : Subgroup X}
    (hEa : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hW : ¬ 3 ∣ Nat.card W)
    (hEW : E ≤ normalizer (W : Set X)) : W = ⊥ := by
  have hbot := d4_k3 (E := E.map ψ) (W := W.map ψ)
    (by rintro _ ⟨x, -, rfl⟩; exact hrange x) (by rintro _ ⟨x, -, rfl⟩; exact hrange x)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ E hEa)
    (by rw [Subgroup.card_map_of_injective hψ, hE9])
    (by rw [Subgroup.card_map_of_injective hψ]; exact hW)
    ((Subgroup.map_mono hEW).trans (Subgroup.le_normalizer_map ψ))
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).mp hbot

end CFSG.RankThree.PartTwo.Sec4.Item434D42
