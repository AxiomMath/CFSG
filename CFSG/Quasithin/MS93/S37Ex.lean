module

public import CFSG.Quasithin.MS93.S37Lin
public import CFSG.Quasithin.MS93.MSPGen3

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Geo

variable {F : Type} [Field F]

theorem eq_ln₀_of_Q₁_le_stab {l : Submodule F (V4 F)} (hl : IsLine l) (h : Q₁ F ≤ MSP.stab l) :
    l = ln₀ F := by
  have hfin : Module.finrank F l = Module.finrank F (ln₀ F) := by
    rw [hl.1, isLine_ln₀.1]
  by_contra hne
  have hnle : ¬ l ≤ ln₀ F := fun hle => hne (Submodule.eq_of_le_of_finrank_eq hle hfin)
  obtain ⟨v, hvl, hv⟩ := Set.not_subset.1 hnle
  have hv' : v (.inr 0) ≠ 0 ∨ v (.inr 1) ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv (mem_ln₀.2 h')
  have hsub : ln₀ F ≤ l := by
    intro w hw
    obtain ⟨hw0, hw1⟩ := mem_ln₀.1 hw
    obtain ⟨b, c, d, hbcd⟩ : ∃ b c d : F, b * v (.inr 0) + c * v (.inr 1) = w (.inl 0) ∧
        c * v (.inr 0) + d * v (.inr 1) = w (.inl 1) := by
      rcases hv' with h0 | h1
      · refine ⟨(w (.inl 0) - w (.inl 1) / v (.inr 0) * v (.inr 1)) / v (.inr 0),
          w (.inl 1) / v (.inr 0), 0, ?_, ?_⟩
        · rw [div_mul_cancel₀ _ h0]
          ring
        · rw [div_mul_cancel₀ _ h0]
          ring
      · refine ⟨0, w (.inl 0) / v (.inr 1),
          (w (.inl 1) - w (.inl 0) / v (.inr 1) * v (.inr 0)) / v (.inr 1), ?_, ?_⟩
        · rw [div_mul_cancel₀ _ h1]
          ring
        · rw [div_mul_cancel₀ _ h1]
          ring
    have hτ : tau (sym2_transpose b c d) ∈ MSP.stab l := h (tau_mem_Q₁ _)
    have hτv : mat (tau (sym2_transpose b c d)) *ᵥ v ∈ l := mulVec_mem_of_mem_stab hτ hvl
    have e : w = mat (tau (sym2_transpose b c d)) *ᵥ v - v := by
      obtain ⟨e0, e1, e2, e3⟩ := mulVec_tau_sym2 b c d v
      funext i
      rcases i with i | i <;> fin_cases i
      · simp only [Pi.sub_apply, Fin.zero_eta, Fin.isValue]
        rw [e0, ← hbcd.1]
        ring
      · simp only [Pi.sub_apply, Fin.mk_one, Fin.isValue]
        rw [e1, ← hbcd.2]
        ring
      · simp only [Pi.sub_apply, Fin.zero_eta, Fin.isValue]
        rw [e2, hw0, sub_self]
      · simp only [Pi.sub_apply, Fin.mk_one, Fin.isValue]
        rw [e3, hw1, sub_self]
    rw [e]
    exact l.sub_mem hτv hvl
  exact hne (Submodule.eq_of_le_of_finrank_eq hsub hfin.symm).symm

theorem entry_tau (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C) (i j : Fin 2) :
    mat (tau hC) (.inl i) (.inr j) = C i j := by
  rw [mat, coe_tau]
  rfl

theorem lam_conj_mem_Q₁ [CharP F 2] {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) :
    lam a * g * (lam a)⁻¹ ∈ Q₁ F ∧
      mat (lam a * g * (lam a)⁻¹) (.inl 0) (.inr 0) =
        mat g (.inl 0) (.inr 0) + a ^ 2 * mat g (.inl 1) (.inr 1) ∧
      mat (lam a * g * (lam a)⁻¹) (.inl 0) (.inr 1) =
        mat g (.inl 0) (.inr 1) + a * mat g (.inl 1) (.inr 1) ∧
      mat (lam a * g * (lam a)⁻¹) (.inl 1) (.inr 1) = mat g (.inl 1) (.inr 1) := by
  rw [Q₁_eq_radical] at hg
  obtain ⟨C, hC, rfl⟩ := hg
  have e1 : tau hC = tau (sym2_transpose (C 0 0) (C 0 1) (C 1 1)) :=
    tau_congr _ _ (eq_sym2 hC)
  rw [e1, lam_mul_tau_mul_inv]
  have e2 := unitri_mul_sym2_mul_transpose a (C 0 0) (C 0 1) (C 1 1)
  rw [tau_congr _ (sym2_transpose _ _ _) e2]
  refine ⟨tau_mem_Q₁ _, ?_, ?_, ?_⟩ <;> simp only [entry_tau] <;> rfl

theorem lam_comm_iff [CharP F 2] {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) :
    lam a * g = g * lam a ↔ a * mat g (.inl 1) (.inr 1) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := lam_conj_mem_Q₁ hg a
  constructor
  · intro h
    have e : lam a * g * (lam a)⁻¹ = g := by rw [h, mul_inv_cancel_right]
    rw [e] at h3
    linear_combination -h3
  · intro h
    have e : lam a * g * (lam a)⁻¹ = g := by
      refine eq_of_mem_Q₁ h1 hg ?_ ?_ h4
      · rw [h2, show a ^ 2 * mat g (.inl 1) (.inr 1) = a * (a * mat g (.inl 1) (.inr 1)) by ring,
          h, mul_zero, add_zero]
      · rw [h3, h, add_zero]
    calc lam a * g = lam a * g * (lam a)⁻¹ * lam a := by group
      _ = g * lam a := by rw [e]

theorem lam_comm_entries [CharP F 2] {g : Sp4 F} (hg : g ∈ Q₁ F) (a : F) :
    lam a * g * (lam a)⁻¹ * g⁻¹ ∈ Q₁ F ∧
      mat (lam a * g * (lam a)⁻¹ * g⁻¹) (.inl 0) (.inr 0) = a ^ 2 * mat g (.inl 1) (.inr 1) ∧
      mat (lam a * g * (lam a)⁻¹ * g⁻¹) (.inl 0) (.inr 1) = a * mat g (.inl 1) (.inr 1) ∧
      mat (lam a * g * (lam a)⁻¹ * g⁻¹) (.inl 1) (.inr 1) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := lam_conj_mem_Q₁ hg a
  have hgi : g⁻¹ ∈ Q₁ F := inv_mem hg
  refine ⟨mul_mem h1 hgi, ?_, ?_, ?_⟩
  · rw [entry_mul_of_mem_Q₁ h1 hgi, entry_inv_of_mem_Q₁ hg, h2]
    ring
  · rw [entry_mul_of_mem_Q₁ h1 hgi, entry_inv_of_mem_Q₁ hg, h3]
    ring
  · rw [entry_mul_of_mem_Q₁ h1 hgi, entry_inv_of_mem_Q₁ hg, h4]
    ring

theorem card_inf_centralizer_lam [Finite F] [CharP F 2] {E : Subgroup (Sp4 F)} (hEQ : E ≤ Q₁ F)
    (hE : ∀ a : F, ∀ g ∈ E, lam a * g * (lam a)⁻¹ ∈ E)
    (hcard : Nat.card E = Nat.card F ^ 2) :
    (∀ g ∈ E, mat g (.inl 1) (.inr 1) = 0) ∨
      2 * Nat.card ↥(E ⊓ Subgroup.centralizer ({lam (1 : F)} : Set (Sp4 F))) = Nat.card E := by
  let δ : ↥E →* Multiplicative F :=
    { toFun := fun g => Multiplicative.ofAdd (mat (g : Sp4 F) (.inl 1) (.inr 1))
      map_one' := by
        show Multiplicative.ofAdd (mat (1 : Sp4 F) (.inl 1) (.inr 1)) = 1
        rw [entry_one]
        rfl
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (mat ((g : Sp4 F) * (h : Sp4 F)) (.inl 1) (.inr 1)) = _
        rw [entry_mul_of_mem_Q₁ (hEQ g.2) (hEQ h.2)]
        rfl }
  have hδ : ∀ g : ↥E, Multiplicative.toAdd (δ g) = mat (g : Sp4 F) (.inl 1) (.inr 1) :=
    fun _ => rfl
  have hker : Nat.card δ.ker =
      Nat.card ↥(E ⊓ Subgroup.centralizer ({lam (1 : F)} : Set (Sp4 F))) := by
    refine Nat.card_congr ⟨fun g => ⟨((g : ↥E) : Sp4 F), Subgroup.mem_inf.2 ⟨(g : ↥E).2, ?_⟩⟩,
      fun g => ⟨⟨g, g.2.1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      refine (lam_comm_iff (hEQ (g : ↥E).2) 1).2 ?_
      have := g.2
      rw [MonoidHom.mem_ker] at this
      have h0 := congrArg Multiplicative.toAdd this
      rw [hδ] at h0
      rw [one_mul]
      exact h0
    · rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [hδ]
      have hc := Subgroup.mem_centralizer_iff.1 g.2.2 (lam 1) rfl
      have := (lam_comm_iff (hEQ g.2.1) 1).1 hc
      rw [one_mul] at this
      exact this
  have hsplit := Subgroup.card_ker_mul_card_range δ
  by_cases hall : ∀ g ∈ E, mat g (.inl 1) (.inr 1) = 0
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨g₁, hg₁E, hg₁⟩ := hall
  set δ₁ := mat g₁ (.inl 1) (.inr 1) with hδ₁
  have hval : ∀ g ∈ E, mat g (.inl 1) (.inr 1) = 0 ∨ mat g (.inl 1) (.inr 1) = δ₁ := by
    intro g₂ hg₂E
    by_contra hne
    push Not at hne
    obtain ⟨hne0, hne1⟩ := hne
    set δ₂ := mat g₂ (.inl 1) (.inr 1) with hδ₂
    have hcomm : ∀ (a : F) (g : Sp4 F), g ∈ E → lam a * g * (lam a)⁻¹ * g⁻¹ ∈ E :=
      fun a g hg => E.mul_mem (hE a g hg) (E.inv_mem hg)
    let φ : F × F → ↥δ.ker := fun x =>
      ⟨⟨(lam x.1 * g₁ * (lam x.1)⁻¹ * g₁⁻¹) * (lam x.2 * g₂ * (lam x.2)⁻¹ * g₂⁻¹),
        E.mul_mem (hcomm x.1 g₁ hg₁E) (hcomm x.2 g₂ hg₂E)⟩, by
        rw [MonoidHom.mem_ker]
        apply Multiplicative.toAdd.injective
        rw [hδ]
        show mat ((lam x.1 * g₁ * (lam x.1)⁻¹ * g₁⁻¹) * (lam x.2 * g₂ * (lam x.2)⁻¹ * g₂⁻¹))
          (.inl 1) (.inr 1) = 0
        rw [entry_mul_of_mem_Q₁ (lam_comm_entries (hEQ hg₁E) x.1).1
          (lam_comm_entries (hEQ hg₂E) x.2).1, (lam_comm_entries (hEQ hg₁E) x.1).2.2.2,
          (lam_comm_entries (hEQ hg₂E) x.2).2.2.2, add_zero]⟩
    have hφ : Function.Injective φ := by
      rintro ⟨a, a'⟩ ⟨b, b'⟩ h
      have h' := congrArg (fun k : ↥δ.ker => ((k : ↥E) : Sp4 F)) h
      have e0 : mat ((lam a * g₁ * (lam a)⁻¹ * g₁⁻¹) * (lam a' * g₂ * (lam a')⁻¹ * g₂⁻¹))
          (.inl 0) (.inr 0) = mat ((lam b * g₁ * (lam b)⁻¹ * g₁⁻¹) *
            (lam b' * g₂ * (lam b')⁻¹ * g₂⁻¹)) (.inl 0) (.inr 0) :=
        congrArg (fun g : Sp4 F => mat g (.inl 0) (.inr 0)) h'
      have e1 : mat ((lam a * g₁ * (lam a)⁻¹ * g₁⁻¹) * (lam a' * g₂ * (lam a')⁻¹ * g₂⁻¹))
          (.inl 0) (.inr 1) = mat ((lam b * g₁ * (lam b)⁻¹ * g₁⁻¹) *
            (lam b' * g₂ * (lam b')⁻¹ * g₂⁻¹)) (.inl 0) (.inr 1) :=
        congrArg (fun g : Sp4 F => mat g (.inl 0) (.inr 1)) h'
      rw [entry_mul_of_mem_Q₁ (lam_comm_entries (hEQ hg₁E) a).1
          (lam_comm_entries (hEQ hg₂E) a').1, (lam_comm_entries (hEQ hg₁E) a).2.1,
          (lam_comm_entries (hEQ hg₂E) a').2.1, entry_mul_of_mem_Q₁
          (lam_comm_entries (hEQ hg₁E) b).1 (lam_comm_entries (hEQ hg₂E) b').1,
          (lam_comm_entries (hEQ hg₁E) b).2.1, (lam_comm_entries (hEQ hg₂E) b').2.1] at e0
      rw [entry_mul_of_mem_Q₁ (lam_comm_entries (hEQ hg₁E) a).1
          (lam_comm_entries (hEQ hg₂E) a').1, (lam_comm_entries (hEQ hg₁E) a).2.2.1,
          (lam_comm_entries (hEQ hg₂E) a').2.2.1, entry_mul_of_mem_Q₁
          (lam_comm_entries (hEQ hg₁E) b).1 (lam_comm_entries (hEQ hg₂E) b').1,
          (lam_comm_entries (hEQ hg₁E) b).2.2.1, (lam_comm_entries (hEQ hg₂E) b').2.2.1] at e1
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have hl1 : (a - b) * δ₁ + (a' - b') * δ₂ = 0 := by linear_combination e1
      have hl2 : (a - b) ^ 2 * δ₁ + (a' - b') ^ 2 * δ₂ = 0 := by
        linear_combination e0 + (b ^ 2 * δ₁ + b' ^ 2 * δ₂ - a * b * δ₁ - a' * b' * δ₂) * h2
      have hx' : a' - b' = 0 := by
        have h3 : (a' - b') ^ 2 * δ₂ * (δ₂ - δ₁) = 0 := by
          linear_combination δ₁ * hl2 - ((a - b) * δ₁ - (a' - b') * δ₂) * hl1 -
            ((a' - b') ^ 2 * δ₂ * δ₁) * h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · rcases mul_eq_zero.1 h4 with h5 | h5
          · exact pow_eq_zero_iff two_ne_zero |>.1 h5
          · exact absurd h5 hne0
        · exact absurd (sub_eq_zero.1 h4) hne1
      have hx : a - b = 0 := by
        rw [hx', zero_mul, add_zero] at hl1
        exact (mul_eq_zero.1 hl1).resolve_right hg₁
      rw [Prod.mk.injEq]
      exact ⟨sub_eq_zero.1 hx, sub_eq_zero.1 hx'⟩
    have hk : Nat.card F ^ 2 ≤ Nat.card δ.ker := by
      have := Nat.card_le_card_of_injective φ hφ
      rwa [Nat.card_prod, ← sq] at this
    have hr : 3 ≤ Nat.card δ.range := by
      let ψ : Fin 3 → ↥δ.range := ![1, ⟨δ ⟨g₁, hg₁E⟩, ⟨_, rfl⟩⟩, ⟨δ ⟨g₂, hg₂E⟩, ⟨_, rfl⟩⟩]
      have hψ : Function.Injective ψ := by
        intro i j hij
        have h' := congrArg (fun r : ↥δ.range => Multiplicative.toAdd (r : Multiplicative F)) hij
        fin_cases i <;> fin_cases j <;> simp [ψ, hδ] at h' ⊢
        all_goals first
          | exact absurd h'.symm hg₁ | exact absurd h' hg₁ | exact absurd h'.symm hne0
          | exact absurd h' hne0 | exact absurd h'.symm hne1 | exact absurd h' hne1
      have := Nat.card_le_card_of_injective ψ hψ
      simpa using this
    have hq : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
    rw [hcard] at hsplit
    nlinarith
  have hr2 : Nat.card δ.range = 2 := by
    refine (Nat.card_eq_two_iff' (1 : ↥δ.range)).2 ⟨⟨δ ⟨g₁, hg₁E⟩, ⟨_, rfl⟩⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg (fun r : ↥δ.range => Multiplicative.toAdd (r : Multiplicative F)) h
      simp only [hδ] at h'
      exact hg₁ h'
    · rintro ⟨_, ⟨g, rfl⟩⟩ hg
      rcases hval g g.2 with h0 | h1
      · refine absurd (Subtype.ext ?_) hg
        show δ g = 1
        apply Multiplicative.toAdd.injective
        rw [hδ]
        exact h0
      · apply Subtype.ext
        show δ g = δ ⟨g₁, hg₁E⟩
        apply Multiplicative.toAdd.injective
        rw [hδ, hδ]
        exact h1
  rw [← hker, ← hsplit, hr2, mul_comm]

end Geo

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

section Sub

variable {S : Subgroup G}

theorem q_ge_four : 4 ≤ Nat.card F := by
  rw [Nat.card_eq_fintype_card, C.hF]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ C.k := Nat.pow_le_pow_right (by norm_num) C.hk

theorem relIndex_inv_eq (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hcrit : ¬ Uq M T L ≤ Qt M θ) (hU : Ut M T L θ ≤ T1 M T L) (hU' : Ut M T L θ⁻¹ ≤ T1 M T L)
    (hle : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L θ)) :
    (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) = (pCoreOf 2 M).relIndex (Ut M T L θ) ∧
      Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) = Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  set q := Nat.card F with hq
  have hq4 : 4 ≤ q := C.q_ge_four
  have hV := C.card_V4_eq hQS hST θ hU
  rw [C.relIndex_Qt_eq hQS θ, MSP.card_V4] at hV
  have hV' := C.card_V4_eq hQS hST θ⁻¹ hU'
  rw [C.relIndex_Qt_eq hQS θ⁻¹, inv_inv, MSP.card_V4] at hV'
  have hcardE : Nat.card ↥(C.rhoIm (Ut M T L θ)) = (pCoreOf 2 M).relIndex (Ut M T L θ) :=
    C.card_rhoIm (hU.trans T1_le_sup)
  have hfix' : q ^ 2 ≤ Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) := by
    rw [MSP.card_fixSp]
    exact Nat.pow_le_pow_right (by omega)
      (two_le_finrank_fixSp_of_quad (C.commSp_le_fixSp hQS hST θ⁻¹))
  set n := (pCoreOf 2 M).relIndex (Ut M T L θ) with hn
  set n' := (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) with hn'
  have hnn' : n' = n := by
    rcases C.case_I_or_II hQS hST θ hcrit hU hle with ⟨p, hp, hE⟩ | ⟨hl, -⟩
    ·
      have h1 : n = q := by rw [← hcardE, hE, card_xPoint hp]
      have h2 : Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) = q ^ 3 := by
        rw [MSP.card_fixSp, hE, fixSp_xPoint hp]
        have := finrank_perp p
        rw [hp] at this
        rw [show Module.finrank F ↥(perp p) = 3 by omega]
      rw [h2] at hV
      have h3 : n' * q ^ 3 = q * q ^ 3 := by rw [← hV]; ring
      rw [h1]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 3) h3
    ·
      have h2 : Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ))) = q ^ 2 := by
        rw [MSP.card_fixSp, hl.1]
      rw [h2] at hV
      have h3 : n' = q ^ 2 := by
        have h4 : n' * q ^ 2 = q ^ 2 * q ^ 2 := by rw [← hV]; ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 2) h4
      have h5 : n ≤ q ^ 2 := by
        by_contra hlt
        push Not at hlt
        have h6 : q ^ 2 * q ^ 2 < n * Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) :=
          Nat.mul_lt_mul_of_lt_of_le hlt hfix' Nat.card_pos
        rw [← hV', show q ^ 2 * q ^ 2 = q ^ 4 by ring] at h6
        exact lt_irrefl _ h6
      omega
  refine ⟨hnn', ?_⟩
  have hpos : 0 < n := relIndex_pos' _ _
  rw [hnn'] at hV
  rw [hV'] at hV
  exact Nat.eq_of_mul_eq_mul_left hpos hV

theorem rho1_mem_normalizer (hST : S ≤ T) (θ : MulAut ↥S) {t : G} (ht : t ∈ T1 M T L)
    (htS : t ∈ S) :
    C.rho1 ⟨t, ht⟩ ∈ Subgroup.normalizer (C.rhoIm (Ut M T L θ) : Set (Sp4 F)) := by
  have htK : t ∈ L ⊔ pCoreOf 2 M := T1_le_sup ht
  have hconj : ∀ {s : G} (hsS : s ∈ S) (hsK : s ∈ L ⊔ pCoreOf 2 M), ∀ y ∈ C.rhoIm (Ut M T L θ),
      C.rho ⟨s, hsK⟩ * y * (C.rho ⟨s, hsK⟩)⁻¹ ∈ C.rhoIm (Ut M T L θ) := by
    intro s hsS hsK y hy
    obtain ⟨z, hzK, hz, rfl⟩ := (C.mem_rhoIm).1 hy
    refine (C.mem_rhoIm).2 ⟨s * z * s⁻¹, (L ⊔ pCoreOf 2 M).mul_mem
      ((L ⊔ pCoreOf 2 M).mul_mem hsK hzK) ((L ⊔ pCoreOf 2 M).inv_mem hsK),
      C.conj_mem_Ut hST θ hsS hz, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [C.rho1_apply, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj htS htK y, fun hy => ?_⟩
  have := hconj (S.inv_mem htS) ((L ⊔ pCoreOf 2 M).inv_mem htK) _ hy
  have e : (⟨t⁻¹, (L ⊔ pCoreOf 2 M).inv_mem htK⟩ : ↥(L ⊔ pCoreOf 2 M)) = ⟨t, htK⟩⁻¹ := rfl
  rw [e, map_inv, inv_inv] at this
  simpa [mul_assoc] using this

end Sub

theorem commSp_T0bar_le (θ : MulAut ↥T) (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hU' : Ut M T L θ⁻¹ ≤ T1 M T L)
    (hcomm : ∀ t ∈ T1 M T L, ∀ x ∈ Ut M T L θ, ⁅t, x⁆ ∈ pCoreOf 2 M) :
    commSp C.T0bar ≤ fixSp (C.rhoIm (Ut M T L θ⁻¹)) := by
  have hinv : ∀ (t : G) (ht : t ∈ T1 M T L), ((θ⁻¹ ⟨t, T1_le_T ht⟩ : ↥T) : G) ∈ T1 M T L :=
    fun t ht => C.mem_T1_of_comm θ hcrit hU' (T1_le_T ht) (hcomm t ht)
  have hT1 := (tImage_T1_eq θ hinv).2
  rw [commSp_le_iff]
  rintro _ ⟨s, rfl⟩ v
  have hθs : ((θ ⟨s, T1_le_T s.2⟩ : ↥T) : G) ∈ T1 M T L := by
    have : ((θ ⟨s, T1_le_T s.2⟩ : ↥T) : G) ∈ tImage θ (T1 M T L) :=
      mem_tImage.2 ⟨(s : G), T1_le_T s.2, s.2, rfl⟩
    rwa [hT1] at this
  have h := C.act_sub_mem_of_comm θ hU' (T1_le_T hθs) (hcomm _ hθs) v
  have e : θ⁻¹ ⟨((θ ⟨s, T1_le_T s.2⟩ : ↥T) : G), T1_le_T hθs⟩ = ⟨s, T1_le_T s.2⟩ := by
    rw [show (⟨((θ ⟨s, T1_le_T s.2⟩ : ↥T) : G), T1_le_T hθs⟩ : ↥T) = θ ⟨s, T1_le_T s.2⟩ from rfl,
      MulAut.inv_apply_self]
  have e2 : C.act (C.h.le (θ⁻¹ ⟨((θ ⟨s, T1_le_T s.2⟩ : ↥T) : G), T1_le_T hθs⟩).2) v =
      mat (C.rho1 s) *ᵥ v := by
    rw [C.rho1_apply, ← C.rho_spec]
    exact congrArg (fun f => f v) (C.N.act_congr C.hMU C.hMA (congrArg Subtype.val e) _ _)
  rw [e2] at h
  exact h

theorem not_caseII_Q₂ (hT : C.T0bar = Q₂ F) (θ : MulAut ↥T) (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hU : Ut M T L θ ≤ T1 M T L) (hU' : Ut M T L θ⁻¹ ≤ T1 M T L)
    (hle : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L θ))
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have hab : ∀ a ∈ C.T0bar, ∀ b ∈ C.T0bar, a * b = b * a := by
    rw [hT]
    exact fun a ha b hb => Q₂_comm ha hb
  have hcomm : ∀ t ∈ T1 M T L, ∀ x ∈ Ut M T L θ, ⁅t, x⁆ ∈ pCoreOf 2 M :=
    fun t ht x hx => C.comm_of_abelian hab ht (hU hx)
  have h1 := C.commSp_T0bar_le θ hcrit hU' hcomm
  rw [hT, commSp_Q₂] at h1
  have h2 := Submodule.finrank_mono h1
  have h3 : Module.finrank F ↥(perp (pt₀ F)) = 3 := by
    have := finrank_perp (pt₀ F)
    rw [isPoint_pt₀] at this
    omega
  have h4 : Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) = 2 := by
    have hc := (C.relIndex_inv_eq C.h.pCore_le le_rfl θ hcrit hU hU' hle).2
    rw [MSP.card_fixSp, MSP.card_fixSp, hII.1] at hc
    exact Nat.pow_right_injective (le_trans (by norm_num) C.q_ge_four) hc
  omega

theorem comm_mem_iff (θ : MulAut ↥T) (hU' : Ut M T L θ⁻¹ ≤ T1 M T L) {t : G} (ht : t ∈ T)
    (u : ↥(Uq M T L)) :
    ⁅t, ((θ ⟨u, C.Uq_le_T u.2⟩ : ↥T) : G)⁆ ∈ pCoreOf 2 M ↔
      C.act (C.h.le (θ⁻¹ ⟨t, ht⟩).2) (C.N.co u) - C.N.co u ∈ fixSp (C.rhoIm (Ut M T L θ⁻¹)) := by
  set s : G := ((θ⁻¹ ⟨t, ht⟩ : ↥T) : G) with hs
  have hsT : s ∈ T := (θ⁻¹ ⟨t, ht⟩).2
  have huT : (u : G) ∈ T := C.Uq_le_T u.2
  have hc : ⁅s, (u : G)⁆ ∈ Uq M T L := by
    rw [commutatorElement_def]
    exact (Uq M T L).mul_mem
      ((Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.le hsT)) u).1 u.2) ((Uq M T L).inv_mem u.2)
  rw [← C.co_comm (C.h.le hsT) u.2 hc, C.co_mem_fixSp_iff (hU'.trans T1_le_sup)]
  have hyT : ⁅t, ((θ ⟨u, huT⟩ : ↥T) : G)⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem ht (θ ⟨u, huT⟩).2) (T.inv_mem ht))
      (T.inv_mem (θ ⟨u, huT⟩).2)
  have e : (θ⁻¹ ⟨⁅t, ((θ ⟨u, huT⟩ : ↥T) : G)⁆, hyT⟩ : ↥T) = ⟨⁅s, (u : G)⁆, by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem hsT huT) (T.inv_mem hsT)) (T.inv_mem huT)⟩ := by
    have e1 : (⟨⁅t, ((θ ⟨u, huT⟩ : ↥T) : G)⁆, hyT⟩ : ↥T) = ⁅(⟨t, ht⟩ : ↥T), θ ⟨u, huT⟩⁆ := rfl
    rw [e1, map_commutatorElement, MulAut.inv_apply_self]
    rfl
  constructor
  · intro hQ
    have h1 : ⁅s, (u : G)⁆ ∈ Qt M θ⁻¹ := mem_tImage.2 ⟨_, hyT, hQ, by rw [e]⟩
    rw [C.Qt_eq C.h.pCore_le le_rfl] at h1
    exact h1.2
  · intro hC
    have h1 : ⁅s, (u : G)⁆ ∈ Qt M θ⁻¹ := by
      rw [C.Qt_eq C.h.pCore_le le_rfl]
      exact ⟨T.mul_mem (T.mul_mem (T.mul_mem hsT huT) (T.inv_mem hsT)) (T.inv_mem huT), hC⟩
    obtain ⟨y, hyT', hyQ, hy⟩ := mem_tImage.1 h1
    have h2 : (⟨y, hyT'⟩ : ↥T) = ⟨⁅t, ((θ ⟨u, huT⟩ : ↥T) : G)⁆, hyT⟩ := by
      apply (θ⁻¹).injective
      rw [e]
      exact Subtype.ext hy
    have h3 : y = ⁅t, ((θ ⟨u, huT⟩ : ↥T) : G)⁆ := congrArg Subtype.val h2
    rw [← h3]
    exact hyQ

theorem card_comap_beta (X : Subgroup (Multiplicative (V4 F))) :
    Nat.card ↥(X.comap C.N.β) =
      Nat.card X * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
  set f : ↥(X.comap C.N.β) →* Multiplicative (V4 F) := C.N.β.comp (X.comap C.N.β).subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hrange : f.range = X := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hx
      obtain ⟨u, hu⟩ := C.N.β_surj x
      exact ⟨⟨u, show C.N.β u ∈ X by rw [hu]; exact hx⟩, hu⟩
  have hker : Nat.card f.ker = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Nat.card_congr ⟨fun w => ⟨(((w : ↥(X.comap C.N.β)) : ↥(Uq M T L)) : G), ?_⟩,
      fun a => ⟨⟨⟨a, a.2.1⟩, ?_⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · exact ⟨((w : ↥(X.comap C.N.β)) : ↥(Uq M T L)).2, ((C.N.β_ker _).1 w.2).2⟩
    · show C.N.β ⟨a, a.2.1⟩ ∈ X
      rw [(C.N.β_ker _).2 a.2]
      exact X.one_mem
    · exact (C.N.β_ker _).2 a.2
  rw [← h1, hrange, hker, mul_comm]

theorem card_centralizer_mul (θ : MulAut ↥T) (hU : Ut M T L θ ≤ T1 M T L)
    (hU' : Ut M T L θ⁻¹ ≤ T1 M T L) {t : G} (ht : t ∈ T1 M T L) :
    Nat.card ↥(C.rhoIm (Ut M T L θ) ⊓
        Subgroup.centralizer ({C.rho1 ⟨t, ht⟩} : Set (Sp4 F))) *
        Nat.card ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) =
      Nat.card ↥((fixSp (C.rhoIm (Ut M T L θ⁻¹))).toAddSubgroup.comap
        (C.act (C.h.le (θ⁻¹ ⟨t, T1_le_T ht⟩).2) - AddMonoidHom.id (V4 F))) := by
  set W := fixSp (C.rhoIm (Ut M T L θ⁻¹)) with hW
  set E := C.rhoIm (Ut M T L θ) with hE
  set Cn := Subgroup.centralizer ({C.rho1 ⟨t, ht⟩} : Set (Sp4 F)) with hCn
  set y := C.act (C.h.le (θ⁻¹ ⟨t, T1_le_T ht⟩).2) with hy
  have hθU : ∀ u : ↥(Uq M T L), ((θ ⟨u, C.Uq_le_T u.2⟩ : ↥T) : G) ∈ T1 M T L :=
    fun u => hU (mem_tImage.2 ⟨u, C.Uq_le_T u.2, u.2, rfl⟩)
  let π : ↥(Uq M T L) →* Sp4 F :=
    { toFun := fun u => C.rho1 ⟨_, hθU u⟩
      map_one' := by
        have e : (⟨_, hθU 1⟩ : ↥(T1 M T L)) = 1 := Subtype.ext (by
          show ((θ ⟨(1 : G), C.Uq_le_T (Uq M T L).one_mem⟩ : ↥T) : G) = 1
          rw [show (⟨(1 : G), C.Uq_le_T (Uq M T L).one_mem⟩ : ↥T) = 1 from rfl, map_one]
          rfl)
        show C.rho1 ⟨_, hθU 1⟩ = 1
        rw [e, map_one]
      map_mul' := fun u v => by
        show C.rho1 ⟨_, hθU (u * v)⟩ = C.rho1 ⟨_, hθU u⟩ * C.rho1 ⟨_, hθU v⟩
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show ((θ ⟨(u : G) * v, _⟩ : ↥T) : G) = ((θ ⟨u, _⟩ : ↥T) : G) * ((θ ⟨v, _⟩ : ↥T) : G)
        rw [show (⟨(u : G) * v, C.Uq_le_T (u * v).2⟩ : ↥T) =
          ⟨u, C.Uq_le_T u.2⟩ * ⟨v, C.Uq_le_T v.2⟩ from rfl, map_mul]
        rfl }
  have hπ : ∀ u, π u = C.rho1 ⟨_, hθU u⟩ := fun _ => rfl
  have hrange : ∀ g ∈ E, ∃ u, π u = g := by
    intro g hg
    obtain ⟨x, hxK, hx, rfl⟩ := (C.mem_rhoIm).1 hg
    obtain ⟨u, huT, huU, rfl⟩ := mem_tImage.1 hx
    exact ⟨⟨u, huU⟩, rfl⟩
  have hmemE : ∀ u, π u ∈ E := fun u =>
    (C.mem_rhoIm).2 ⟨_, T1_le_sup (hθU u), mem_tImage.2 ⟨u, C.Uq_le_T u.2, u.2, rfl⟩, rfl⟩
  have hcomm : ∀ u, π u ∈ Cn ↔ y (C.N.co u) - C.N.co u ∈ W := by
    intro u
    rw [← C.comm_mem_iff θ hU' (T1_le_T ht) u, hCn, Subgroup.mem_centralizer_singleton_iff, hπ]
    have hc : ⁅t, ((θ ⟨u, C.Uq_le_T u.2⟩ : ↥T) : G)⁆ ∈ T1 M T L := by
      rw [commutatorElement_def]
      exact (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem ht (hθU u))
        ((T1 M T L).inv_mem ht)) ((T1 M T L).inv_mem (hθU u))
    rw [← C.rho1_eq_one_iff ⟨_, hc⟩]
    have e : (⟨_, hc⟩ : ↥(T1 M T L)) = ⁅(⟨t, ht⟩ : ↥(T1 M T L)), ⟨_, hθU u⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact eq_comm
  have hker : ∀ u, π u = 1 ↔ C.N.co u ∈ W := by
    intro u
    rw [hπ, C.rho1_eq_one_iff, C.co_mem_fixSp_iff (hU'.trans T1_le_sup)]
    constructor
    · intro hQ
      have h1 : (u : G) ∈ Qt M θ⁻¹ :=
        mem_tImage.2 ⟨_, (θ ⟨u, C.Uq_le_T u.2⟩).2, hQ, by rw [MulAut.inv_apply_self]⟩
      rw [C.Qt_eq C.h.pCore_le le_rfl] at h1
      exact h1.2
    · intro hC
      have h1 : (u : G) ∈ Qt M θ⁻¹ := by
        rw [C.Qt_eq C.h.pCore_le le_rfl]
        exact ⟨C.Uq_le_T u.2, hC⟩
      obtain ⟨z, hzT, hzQ, hz⟩ := mem_tImage.1 h1
      have h2 : (⟨z, hzT⟩ : ↥T) = θ ⟨u, C.Uq_le_T u.2⟩ := by
        apply (θ⁻¹).injective
        rw [MulAut.inv_apply_self]
        exact Subtype.ext hz
      have h3 : z = ((θ ⟨u, C.Uq_le_T u.2⟩ : ↥T) : G) := congrArg Subtype.val h2
      show ((θ ⟨u, C.Uq_le_T u.2⟩ : ↥T) : G) ∈ pCoreOf 2 M
      rw [← h3]
      exact hzQ
  set U₀ : Subgroup ↥(Uq M T L) := (E ⊓ Cn).comap π with hU₀
  set π₀ : ↥U₀ →* Sp4 F := π.comp U₀.subtype with hπ₀
  have h1 := Subgroup.card_ker_mul_card_range π₀
  have hr : π₀.range = E ⊓ Cn := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hg
      obtain ⟨u, hu⟩ := hrange g hg.1
      exact ⟨⟨u, show π u ∈ E ⊓ Cn by rw [hu]; exact hg⟩, hu⟩
  have hk : Nat.card π₀.ker = Nat.card π.ker := by
    refine Nat.card_congr ⟨fun w => ⟨((w : ↥U₀) : ↥(Uq M T L)), w.2⟩,
      fun w => ⟨⟨w, ?_⟩, w.2⟩, fun _ => rfl, fun _ => rfl⟩
    show π w ∈ E ⊓ Cn
    rw [w.2]
    exact (E ⊓ Cn).one_mem
  have hU₀β : U₀ = (AddSubgroup.toSubgroup
      ((W.toAddSubgroup).comap (y - AddMonoidHom.id (V4 F)))).comap C.N.β := by
    ext u
    rw [hU₀, Subgroup.mem_comap, Subgroup.mem_comap, Multiplicative.mem_toSubgroup,
      AddSubgroup.mem_comap, Subgroup.mem_inf, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
    show π u ∈ E ∧ π u ∈ Cn ↔ y (C.N.co u) - C.N.co u ∈ W
    rw [hcomm]
    exact ⟨fun h => h.2, fun h => ⟨hmemE u, h⟩⟩
  have hkerβ : π.ker = (AddSubgroup.toSubgroup W.toAddSubgroup).comap C.N.β := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Multiplicative.mem_toSubgroup, hker]
    rfl
  have c1 := C.card_comap_beta (AddSubgroup.toSubgroup
    ((W.toAddSubgroup).comap (y - AddMonoidHom.id (V4 F))))
  have c2 := C.card_comap_beta (AddSubgroup.toSubgroup W.toAddSubgroup)
  have e1 : Nat.card ↥(AddSubgroup.toSubgroup
      ((W.toAddSubgroup).comap (y - AddMonoidHom.id (V4 F)))) =
      Nat.card ↥((W.toAddSubgroup).comap (y - AddMonoidHom.id (V4 F))) :=
    Nat.card_congr ⟨fun x => ⟨Multiplicative.toAdd (x : Multiplicative (V4 F)), x.2⟩,
      fun x => ⟨Multiplicative.ofAdd (x : V4 F), x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have e2 : Nat.card ↥(AddSubgroup.toSubgroup W.toAddSubgroup) = Nat.card W :=
    Nat.card_congr ⟨fun x => ⟨Multiplicative.toAdd (x : Multiplicative (V4 F)), x.2⟩,
      fun x => ⟨Multiplicative.ofAdd (x : V4 F), x.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← hU₀β, e1] at c1
  rw [← hkerβ, e2] at c2
  rw [hr, hk, c2] at h1
  have hA : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  rw [c1] at h1
  refine Nat.eq_of_mul_eq_mul_right hA ?_
  rw [← h1]
  ring

theorem not_two_mul_card {s : G} (hs : s ∈ M) {W : Submodule F (V4 F)}
    (hW : Nat.card W = Nat.card F ^ 2)
    (h2 : 2 * Nat.card ↥(W.toAddSubgroup.comap (C.act hs - AddMonoidHom.id (V4 F))) =
      Nat.card (V4 F)) : False := by
  set Wh := W.toAddSubgroup.comap (C.act hs - AddMonoidHom.id (V4 F)) with hWh
  have hmem : ∀ v, v ∈ Wh ↔ C.act hs v - v ∈ W := fun v => by
    rw [hWh, AddSubgroup.mem_comap, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
    rfl
  set q := Nat.card F with hq
  have hq4 : 4 ≤ q := C.q_ge_four
  have hV : Nat.card (V4 F) = q ^ 4 := MSP.card_V4
  by_cases hσ : C.sig hs = RingHom.id F
  ·
    let WF : Submodule F (V4 F) :=
      { carrier := Wh
        add_mem' := fun ha hb => Wh.add_mem ha hb
        zero_mem' := Wh.zero_mem
        smul_mem' := fun c v hv => by
          have hv' : v ∈ Wh := hv
          change c • v ∈ Wh
          rw [hmem] at hv' ⊢
          rw [C.sig_spec, hσ, RingHom.id_apply, ← smul_sub]
          exact W.smul_mem c hv' }
    have hcard : Nat.card Wh = Nat.card WF := rfl
    rw [hcard, Module.natCard_eq_pow_finrank (K := F), hV, ← hq] at h2
    set j := Module.finrank F ↥WF
    have hqj : 0 < q ^ j := pow_pos (by omega) j
    rcases Nat.lt_or_ge j 4 with hj | hj
    · have e : q ^ 4 = q ^ j * q ^ (4 - j) := by rw [← pow_add]; congr 1; omega
      rw [e, mul_comm 2] at h2
      have h3 : 2 = q ^ (4 - j) := Nat.eq_of_mul_eq_mul_left hqj h2
      rcases Nat.eq_zero_or_pos (4 - j) with h0 | h0
      · rw [h0, pow_zero] at h3
        omega
      · have h4 : q ≤ q ^ (4 - j) := Nat.le_self_pow (by omega) q
        omega
    · have h3 : q ^ 4 ≤ q ^ j := Nat.pow_le_pow_right (by omega) hj
      have h4 : 0 < q ^ 4 := pow_pos (by omega) 4
      omega
  · obtain ⟨c, hc⟩ : ∃ c : F, C.sig hs c ≠ c := by
      by_contra h
      push Not at h
      exact hσ (RingHom.ext h)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hc (map_zero _)
    let mc : V4 F →+ V4 F :=
      { toFun := fun v => c • v
        map_zero' := smul_zero c
        map_add' := smul_add c }
    have hmc : Function.Surjective mc := fun v => ⟨c⁻¹ • v, by
      show c • c⁻¹ • v = v
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]⟩
    set Wh' := Wh.comap mc with hWh'
    have hle : Wh ⊓ Wh' ≤ W.toAddSubgroup := by
      intro v hv
      have h1 := (hmem v).1 hv.1
      have h2' : C.act hs (c • v) - c • v ∈ W := (hmem _).1 hv.2
      have e : (C.sig hs c - c) • v =
          (C.act hs (c • v) - c • v) - C.sig hs c • (C.act hs v - v) := by
        rw [C.sig_spec, smul_sub, sub_smul]
        abel
      have h3 : (C.sig hs c - c) • v ∈ W := by
        rw [e]
        exact W.sub_mem h2' (W.smul_mem _ h1)
      have h4 := W.smul_mem (C.sig hs c - c)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul] at h4
    have hidx : Wh.index = 2 := by
      have h5 := AddSubgroup.card_mul_index Wh
      rw [← h2] at h5
      have hpos : 0 < Nat.card Wh := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h5]; ring)
    have hidx' : Wh'.index = 2 := (AddSubgroup.index_comap_of_surjective (H := Wh) hmc).trans hidx
    have h6 : (Wh ⊓ Wh').index ≤ Wh.index * Wh'.index := AddSubgroup.index_inf_le
    rw [hidx, hidx'] at h6
    have h7 := AddSubgroup.card_mul_index (Wh ⊓ Wh')
    have h8 : Nat.card ↥(Wh ⊓ Wh') ≤ Nat.card W := by
      have := AddSubgroup.card_le_of_le hle
      exact this
    rw [hV] at h7
    rw [hW] at h8
    have h9 : q ^ 4 ≤ q ^ 2 * 4 := by
      calc q ^ 4 = Nat.card ↥(Wh ⊓ Wh') * (Wh ⊓ Wh').index := h7.symm
        _ ≤ q ^ 2 * 4 := Nat.mul_le_mul h8 h6
    have h10 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
    rw [h10] at h9
    have h11 : q ^ 2 ≤ 4 := Nat.le_of_mul_le_mul_left h9 (pow_pos (by omega) 2)
    have h12 : 16 ≤ q ^ 2 := by nlinarith
    omega

theorem not_caseII_S (hT : C.T0bar = sylS F) (θ : MulAut ↥T) (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hU : Ut M T L θ ≤ T1 M T L) (hU' : Ut M T L θ⁻¹ ≤ T1 M T L)
    (hle : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) ≤ (pCoreOf 2 M).relIndex (Ut M T L θ))
    (hII : IsLine (fixSp (C.rhoIm (Ut M T L θ)))) : False := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  set q := Nat.card F with hq
  have hq4 : 4 ≤ q := C.q_ge_four
  set E := C.rhoIm (Ut M T L θ) with hE
  set W := fixSp (C.rhoIm (Ut M T L θ⁻¹)) with hW
  obtain ⟨hn, hfix⟩ := C.relIndex_inv_eq C.h.pCore_le le_rfl θ hcrit hU hU' hle
  have hfixE : Nat.card ↥(fixSp E) = q ^ 2 := by rw [MSP.card_fixSp, hII.1]
  have hWc : Nat.card W = q ^ 2 := by rw [hfix, hfixE]
  have hW2 : Module.finrank F W = 2 := by
    rw [MSP.card_fixSp] at hWc
    exact Nat.pow_right_injective (by omega) hWc
  have hcardE : Nat.card E = q ^ 2 := by
    have h1 := C.card_rhoIm (hU.trans T1_le_sup)
    have hV := C.card_V4_eq C.h.pCore_le le_rfl θ hU
    rw [C.relIndex_Qt_eq C.h.pCore_le θ, MSP.card_V4, hfixE] at hV
    rw [← hE] at h1
    rw [h1, ← hn]
    have : (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) * q ^ 2 = q ^ 2 * q ^ 2 := by rw [← hV]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by omega) 2) this
  have hnorm : ∀ a ∈ sylS F, a ∈ Subgroup.normalizer (E : Set (Sp4 F)) := by
    intro a ha
    rw [← hT] at ha
    obtain ⟨t, rfl⟩ := ha
    exact C.rho1_mem_normalizer le_rfl θ t.2 (T1_le_T t.2)
  have hl : fixSp E = ln₀ F :=
    eq_ln₀_of_Q₁_le_stab hII fun g hg =>
      normalizer_le_stab_fixSp E (hnorm g (Q₁_le_sylS hg))
  have hEQ : E ≤ Q₁ F := by
    show E ≤ fixer (ln₀ F)
    rw [← hl]
    exact le_fixer_iff.2 le_rfl
  have hEl : ∀ a : F, ∀ g ∈ E, lam a * g * (lam a)⁻¹ ∈ E := fun a g hg =>
    (Subgroup.mem_normalizer_iff.1 (hnorm _ (lam_mem_sylS a)) g).1 hg
  rcases card_inf_centralizer_lam hEQ hEl hcardE with hall | hhalf
  ·
    have hcen : ∀ a ∈ sylS F, ∀ g ∈ E, a * g = g * a := by
      intro a ha g hg
      obtain ⟨C', hC', b, rfl⟩ := mem_unipotent_iff.1 ha
      have h1 : tau hC' * g = g * tau hC' :=
        Q₁_comm (tau_mem_Q₁ hC') (hEQ hg)
      have h2 : lam b * g = g * lam b := by
        rw [lam_comm_iff (hEQ hg), hall g hg, mul_zero]
      calc tau hC' * lam b * g = tau hC' * (lam b * g) := by group
        _ = tau hC' * g * lam b := by rw [h2]; group
        _ = g * (tau hC' * lam b) := by rw [h1]; group
    have hcomm : ∀ t ∈ T1 M T L, ∀ x ∈ Ut M T L θ, ⁅t, x⁆ ∈ pCoreOf 2 M := by
      intro t ht x hx
      have hc : ⁅t, x⁆ ∈ T1 M T L := by
        rw [commutatorElement_def]
        exact (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem ht (hU hx))
          ((T1 M T L).inv_mem ht)) ((T1 M T L).inv_mem (hU hx))
      have e : (⟨⁅t, x⁆, hc⟩ : ↥(T1 M T L)) = ⁅(⟨t, ht⟩ : ↥(T1 M T L)), ⟨x, hU hx⟩⁆ := rfl
      rw [← C.rho1_eq_one_iff ⟨_, hc⟩, e, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      have hta : C.rho1 ⟨t, ht⟩ ∈ sylS F := hT ▸ ⟨⟨t, ht⟩, rfl⟩
      have hxE : C.rho1 ⟨x, hU hx⟩ ∈ E :=
        (C.mem_rhoIm).2 ⟨x, T1_le_sup (hU hx), hx, rfl⟩
      exact hcen _ hta _ hxE
    have h1 := C.commSp_T0bar_le θ hcrit hU' hcomm
    rw [hT] at h1
    have h2 := Submodule.finrank_mono ((commSp_mono Q₂_le_sylS).trans h1)
    rw [commSp_Q₂] at h2
    have h3 : Module.finrank F ↥(perp (pt₀ F)) = 3 := by
      have := finrank_perp (pt₀ F)
      rw [isPoint_pt₀] at this
      omega
    have h4 : Module.finrank F ↥(fixSp (C.rhoIm (Ut M T L θ⁻¹))) = 2 := hW2
    omega
  ·
    obtain ⟨t₀, ht₀⟩ : lam (1 : F) ∈ C.T0bar := by rw [hT]; exact lam_mem_sylS 1
    have hcnt := C.card_centralizer_mul θ hU hU' t₀.2
    have e : C.rho1 ⟨(t₀ : G), t₀.2⟩ = lam 1 := ht₀
    rw [e, ← hE, ← hW, hWc] at hcnt
    refine C.not_two_mul_card (C.h.le (θ⁻¹ ⟨t₀, T1_le_T t₀.2⟩).2) hWc ?_
    rw [← hcnt, MSP.card_V4]
    calc 2 * (Nat.card ↥(E ⊓ Subgroup.centralizer ({lam (1 : F)} : Set (Sp4 F))) * q ^ 2) =
        (2 * Nat.card ↥(E ⊓ Subgroup.centralizer ({lam (1 : F)} : Set (Sp4 F)))) * q ^ 2 := by
          ring
      _ = q ^ 4 := by rw [hhalf, hcardE]; ring

end Cfg

end CFSG.Quasithin.MS93.S37
