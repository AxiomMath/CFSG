module

public import CFSG.GH74.GLS.C3.Prop121.Card7H2Inputs
public import CFSG.GH74.GLS.C3.Prop121.Card7Gen2
public import CFSG.Permutation.FinPack64
public import Certificates.Data.Kernel.Card7H2.HLCodes

public section

namespace CFSG.Certificates.Kernel.Card7H2

open Equiv CFSG.KS.PCnt CFSG.Permutation.FinPack64 CFSG.GH74.GLS.C3.Prop121.Card7.HC

@[expose] def oC : Nat := 11693627636546543680

@[expose] def t1C : Nat := 9406080500819042368

@[expose] def t1iC : Nat := 10523254683383636032

@[expose] def yC : Nat := 11693623306162286593

theorem pk_one : pkw 6 (1 : P11) = oC := by decide +kernel

theorem pk_T1 : pkw 6 T1 = t1C := by decide +kernel

theorem pk_T1i : pkw 6 T1⁻¹ = t1iC := by decide +kernel

theorem pk_Y11 : pkw 6 Y11 = yC := by decide +kernel

@[expose] noncomputable def cmC (a b : Nat) : Bool := Nat.beq (mulW 11 a b) (mulW 11 b a)

@[expose] noncomputable def ccC (s r : Nat) : Nat := hlC.countP fun c => cmC c s && cmC c r

@[expose] noncomputable def memC (a : Nat) : Bool := hlC.any (Nat.beq a)

@[expose] noncomputable def cjE (W : List (Nat × Nat)) (R : List Nat) (z s : Nat) : Bool :=
  W.any fun p => Nat.beq s p.1 && memC p.2 && cmC p.2 z &&
    R.any fun r => Nat.beq (mulW 11 p.2 s) (mulW 11 r p.2)

@[expose] noncomputable def r3Ok : Bool := r3C.all fun r => memC r && decide (ccC r r ≤ 36)

@[expose] noncomputable def r2Ok : Bool :=
  r2C.all fun r => memC r && (decide (ccC t1C r = 48) || decide (ccC t1C r = 96))

@[expose] noncomputable def o3E (s : Nat) : Bool :=
  !(Nat.beq (powW 11 oC s 3) oC) || Nat.beq s oC ||
    ((Nat.beq s t1C || Nat.beq s t1iC) && decide (ccC s s = 576)) || cjE w3C r3C oC s

@[expose] noncomputable def ord3C : Bool := hlC.all o3E

@[expose] noncomputable def cenE (s : Nat) : Bool :=
  !(hlC.all fun h => cmC h s) || Nat.beq s oC || Nat.beq s yC

@[expose] noncomputable def centerC : Bool := hlC.all cenE

@[expose] noncomputable def b0E (b : Nat) : Bool :=
  !(cmC b t1C) || !(Nat.beq (mulW 11 b b) oC) || Nat.beq b oC || Nat.beq b yC ||
    cjE w2C r2C t1C b

@[expose] noncomputable def b0invC : Bool := hlC.all b0E

theorem decide_eq_beq (σ τ : P11) : decide (σ = τ) = Nat.beq (pkw 6 σ) (pkw 6 τ) := by
  by_cases e : σ = τ
  · subst e
    rw [decide_eq_true rfl, Nat.beq_refl]
  · rw [decide_eq_false e, beq_false_of_ne (by norm_num) rfl rfl e]

theorem decide_comm (c σ : P11) : decide (c * σ = σ * c) = cmC (pkw 6 c) (pkw 6 σ) := by
  rw [decide_eq_beq, pk_mul (by norm_num) rfl rfl, pk_mul (by norm_num) rfl rfl]
  rfl

theorem decide_sq (b : P11) : decide (b * b = 1) = Nat.beq (mulW 11 (pkw 6 b) (pkw 6 b)) oC := by
  rw [decide_eq_beq, pk_mul (by norm_num) rfl rfl, pk_one]

theorem decide_cube (σ : P11) : decide (σ ^ 3 = 1) = Nat.beq (powW 11 oC (pkw 6 σ) 3) oC := by
  rw [decide_eq_beq, pk_npow (by norm_num) pk_one rfl, pk_one]

theorem ccL_conj {g σ ρ : P11} (hg : g ∈ HL) (hσ : σ ∈ HL) (hρ : ρ ∈ HL) :
    ccL (g * σ * g⁻¹) (g * ρ * g⁻¹) = ccL σ ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, ev k = g := ⟨_, ev_mkH g (HL_hp g hg)⟩
  obtain ⟨u, rfl⟩ : ∃ u, ev u = σ := ⟨_, ev_mkH σ (HL_hp σ hσ)⟩
  obtain ⟨v, rfl⟩ : ∃ v, ev v = ρ := ⟨_, ev_mkH ρ (HL_hp ρ hρ)⟩
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← ccard_eq, ← ccard_eq,
    CFSG.GH74.GLS.C3.Prop121.Card7.ccard_conj]

theorem T1_mem : T1 ∈ HL := ev_tau1 ▸ HL_complete CFSG.GH74.GLS.C3.Prop121.Card7.tau1

variable (h : HL.map (pkw 6) = hlC)
include h

theorem mem_of_memC {a : Nat} (ha : memC a = true) : ∃ γ ∈ HL, pkw 6 γ = a := by
  unfold memC at ha
  obtain ⟨x, hx, e⟩ := List.any_eq_true.1 ha
  rw [← h] at hx
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
  exact ⟨γ, hγ, (Nat.eq_of_beq_eq_true e).symm⟩

theorem cjE_spec {W : List (Nat × Nat)} {R : List Nat} {z : Nat} {ζ σ : P11} (hz : pkw 6 ζ = z)
    (hc : cjE W R z (pkw 6 σ) = true) :
    ∃ γ ∈ HL, ∃ r ∈ R, γ * ζ = ζ * γ ∧ ∀ ρ : P11, pkw 6 ρ = r → γ * σ * γ⁻¹ = ρ := by
  unfold cjE at hc
  obtain ⟨p, -, hp⟩ := List.any_eq_true.1 hc
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨⟨-, hm⟩, hcm⟩, hr⟩ := hp
  obtain ⟨γ, hγ, hγc⟩ := mem_of_memC h hm
  obtain ⟨r, hr, hrr⟩ := List.any_eq_true.1 hr
  refine ⟨γ, hγ, r, hr, ?_, fun ρ hρ =>
    conj_of (by norm_num) hγc rfl hρ (Nat.eq_of_beq_eq_true hrr)⟩
  have e := decide_comm γ ζ
  rw [hγc, hz, hcm] at e
  exact of_decide_eq_true e

theorem mem_hlC {σ : P11} (hσ : σ ∈ HL) : pkw 6 σ ∈ hlC := h ▸ List.mem_map_of_mem hσ

theorem ccL_eq (σ ρ : P11) : ccL σ ρ = ccC (pkw 6 σ) (pkw 6 ρ) := by
  unfold ccL ccC
  rw [← h, List.countP_map]
  have e : (fun c : P11 => decide (c * σ = σ * c ∧ c * ρ = ρ * c)) =
      (fun c => cmC c (pkw 6 σ) && cmC c (pkw 6 ρ)) ∘ pkw 6 := by
    funext c
    rw [Function.comp_apply, Bool.decide_and, decide_comm, decide_comm]
  rw [e]

theorem all_eq (σ : P11) : (HL.all fun c => decide (c * σ = σ * c)) =
    hlC.all fun c => cmC c (pkw 6 σ) := by
  rw [← h, List.all_map]
  have e : (fun c : P11 => decide (c * σ = σ * c)) = (fun c => cmC c (pkw 6 σ)) ∘ pkw 6 := by
    funext c
    rw [Function.comp_apply, decide_comm]
  rw [e]

theorem cc3_of (hR : r3Ok = true) {σ : P11} (hσ : σ ∈ HL)
    (hc : cjE w3C r3C oC (pkw 6 σ) = true) : ccL σ σ ≤ 36 := by
  obtain ⟨γ, hγ, r, hr, -, hconj⟩ := cjE_spec h pk_one hc
  have k := List.all_eq_true.1 hR r hr
  rw [Bool.and_eq_true, decide_eq_true_eq] at k
  obtain ⟨ρ, -, hρc⟩ := mem_of_memC h k.1
  rw [← ccL_conj hγ hσ hσ, hconj ρ hρc, ccL_eq h, hρc]
  exact k.2

theorem cc2_of (hR : r2Ok = true) {b : P11} (hb : b ∈ HL)
    (hc : cjE w2C r2C t1C (pkw 6 b) = true) : ccL T1 b = 48 ∨ ccL T1 b = 96 := by
  obtain ⟨γ, hγ, r, hr, hcm, hconj⟩ := cjE_spec h pk_T1 hc
  have k := List.all_eq_true.1 hR r hr
  rw [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at k
  obtain ⟨ρ, -, hρc⟩ := mem_of_memC h k.1
  have hT : γ * T1 * γ⁻¹ = T1 := by rw [hcm, mul_inv_cancel_right]
  rw [← ccL_conj hγ T1_mem hb, hT, hconj ρ hρc, ccL_eq h, pk_T1, hρc]
  exact k.2

theorem ord3Check_of (hR : r3Ok = true) (hc : ord3C = true) : ord3Check = true := by
  unfold ord3Check
  rw [List.all_eq_true]
  intro σ hσ
  have k := List.all_eq_true.1 hc _ (mem_hlC h hσ)
  have e : o3E (pkw 6 σ) = (!decide (σ ^ 3 = 1) || decide (σ = 1) ||
      ((decide (σ = T1) || decide (σ = T1⁻¹)) && decide (ccL σ σ = 576)) ||
      cjE w3C r3C oC (pkw 6 σ)) := by
    rw [decide_cube, decide_eq_beq σ 1, decide_eq_beq σ T1, decide_eq_beq σ T1⁻¹, ccL_eq h,
      pk_one, pk_T1, pk_T1i]
    rfl
  rw [e] at k
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at k
  refine decide_eq_true fun h3 h1 => ?_
  rcases k with ((k | k) | k) | k
  · exact absurd h3 k
  · exact absurd k h1
  · exact Or.inl k
  · exact Or.inr (cc3_of h hR hσ k)

theorem centerCheck_of (hc : centerC = true) : centerCheck = true := by
  unfold centerCheck
  rw [List.all_eq_true]
  intro σ hσ
  have k := List.all_eq_true.1 hc _ (mem_hlC h hσ)
  have e : cenE (pkw 6 σ) = (!(HL.all fun c => decide (c * σ = σ * c)) || decide (σ = 1) ||
      decide (σ = Y11)) := by
    rw [all_eq h, decide_eq_beq σ 1, decide_eq_beq σ Y11, pk_one, pk_Y11]
    rfl
  rw [e] at k
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at k
  refine decide_eq_true fun ha => ?_
  rcases k with (k | k) | k
  · rw [ha] at k
    exact absurd k Bool.noConfusion
  · exact Or.inl k
  · exact Or.inr k

theorem B0invCheck_of (hR : r2Ok = true) (hc : b0invC = true) : B0invCheck = true := by
  unfold B0invCheck
  rw [List.all_eq_true]
  intro b hb
  have k := List.all_eq_true.1 hc _ (mem_hlC h hb)
  have e : b0E (pkw 6 b) = (!decide (b * T1 = T1 * b) || !decide (b * b = 1) ||
      decide (b = 1) || decide (b = Y11) || cjE w2C r2C t1C (pkw 6 b)) := by
    rw [decide_comm, decide_sq, decide_eq_beq b 1, decide_eq_beq b Y11, pk_one, pk_T1, pk_Y11]
    rfl
  rw [e] at k
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at k
  refine decide_eq_true fun h1 h2 h3 h4 => ?_
  rcases k with ((((k | k) | k) | k) | k)
  · exact absurd h1 k
  · exact absurd h2 k
  · exact absurd k h3
  · exact absurd k h4
  · exact cc2_of h hR hb k

theorem ccL_T1_of (hc : ccC t1C t1C = 576) : ccL T1 T1 = 576 := by
  rw [ccL_eq h, pk_T1, hc]

end CFSG.Certificates.Kernel.Card7H2
