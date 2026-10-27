module

public import Certificates.Kernel.B433Alt.Bound
public import Certificates.Kernel.B433Alt.Tr
public import CFSG.Certificates.Kernel.B433Alt.TraceSound
public import CFSG.Monster.Existence.TwoPoint.B433CoverNodes

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CFSG.YGroups.DCE.B433 CFSG.Certificates.TwDce
open CFSG.Monster.Existence.B433Cover (nodeProd nodeProd_eq nodeProd_zero nodeWord nodeWord_lt
  nodeParent nodeParent_lt evalWord_inv_of_involutive map_evalWord)

@[expose] noncomputable def nK (l : ℕ) : ℕ := if l = 0 then 0 else CFSG.KD.B4AT.K1.getD (l - 1) 0

@[expose] noncomputable def nA (l : ℕ) : ℕ := if l = 0 then 0 else CFSG.KD.B4AT.A1.getD (l - 1) 0

#kc_forall_tree tr_all (fun i => CFSG.KD.B4AT.trChk i = true) 22 CFSG.KD.B4AT.tr

theorem tr_start : ∀ l < 23, 0 < l → CFSG.KD.B4AT.K0.getD (l - 1) 0 = nK (nodeParent l) ∧
    CFSG.KD.B4AT.A0.getD (l - 1) 0 = nA (nodeParent l) := by
  decide +kernel

theorem even_reached : ∀ j < 64, liveB j = true → CFSG.KD.B4AT.PA.getD j 0 = 0 →
    ∃ l < 23, nK l = j := by
  decide +kernel

theorem tree_data : ∀ j < 64, 0 < j → CFSG.KD.B4AT.TQ.getD j 0 ≠ 0 →
    treeAt CFSG.KD.B4A.RD (nat_lit 5965) (CFSG.KD.B4AT.TQ.getD j 0) j
      (dN1 (CFSG.KD.B4A.RD (CFSG.KD.B4AT.TQ.getD j 0))) = true ∧
    dN1 (CFSG.KD.B4A.RD (CFSG.KD.B4AT.TQ.getD j 0)) < j ∧
    (dN1 (CFSG.KD.B4A.RD (CFSG.KD.B4AT.TQ.getD j 0)) = 0 ∨
      CFSG.KD.B4AT.TQ.getD (dN1 (CFSG.KD.B4A.RD (CFSG.KD.B4AT.TQ.getD j 0))) 0 ≠ 0) ∧
    CFSG.KD.B4AT.PA.getD j 0 + CFSG.KD.B4AT.PA.getD
      (dN1 (CFSG.KD.B4A.RD (CFSG.KD.B4AT.TQ.getD j 0))) 0 = 1 := by
  decide +kernel

theorem live_tree : ∀ j < 64, liveB j = true → j = 0 ∨ CFSG.KD.B4AT.TQ.getD j 0 ≠ 0 := by
  decide +kernel

theorem pa_zero : CFSG.KD.B4AT.PA.getD 0 0 = 0 := by decide +kernel

theorem treeAt_spec {q j i : ℕ} (h : treeAt CFSG.KD.B4A.RD (nat_lit 5965) q j i = true) :
    q < 5965 ∧ dKind (CFSG.KD.B4A.RD q) = 0 ∧ dN2 (CFSG.KD.B4A.RD q) = j ∧
      dN1 (CFSG.KD.B4A.RD q) = i := by
  unfold treeAt at h
  rw [sB_eq] at h
  simp only [andB_iff] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

section

@[expose] noncomputable def eps : Ghat hsw →* Multiplicative (ZMod 2) := SemidirectProduct.rightHom

theorem eps_inl (b : B433) : eps (SemidirectProduct.inl b : Ghat hsw) = 1 :=
  SemidirectProduct.rightHom_inl b

theorem eps_u : eps (u hsw) = Multiplicative.ofAdd 1 := SemidirectProduct.rightHom_inr _

theorem eps_Hh {h : Ghat hsw} (hh : h ∈ Hh hsw) : eps h = 1 := by
  obtain ⟨y, rfl⟩ := hh
  exact eps_inl _

theorem eps_wVal (w : ℕ) : eps (wVal xG w) = 1 := by
  rw [wVal_xG]
  exact eps_inl _

@[expose] noncomputable def paE (j : ℕ) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (CFSG.KD.B4AT.PA.getD j 0 : ZMod 2)

theorem eps_Xn : ∀ j, j < 64 → (j = 0 ∨ CFSG.KD.B4AT.TQ.getD j 0 ≠ 0) → eps (Xn j) = paE j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hd
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [Xn_zero, map_one, paE, pa_zero]
      rfl
    · have hq : CFSG.KD.B4AT.TQ.getD j 0 ≠ 0 := hd.resolve_left (by omega)
      obtain ⟨htr, hlt, hpd, hpa⟩ := tree_data j hj hpos hq
      set q := CFSG.KD.B4AT.TQ.getD j 0
      set i := dN1 (CFSG.KD.B4A.RD q)
      obtain ⟨hq5, hk, h2, h1⟩ := treeAt_spec htr
      have hfact := (Xn_facts q hq5).1 (by rw [hk]; rfl)
      rw [h1, h2] at hfact
      have he := eps_Hh hfact
      rw [map_mul, map_inv, map_mul, map_mul, map_mul, eps_wVal, eps_wVal, mul_one, mul_one,
        eps_u, ih i hlt (by omega) hpd] at he
      have hpe : paE j = paE i * Multiplicative.ofAdd 1 := by
        rw [paE, paE, ← ofAdd_add]
        congr 1
        have hb : CFSG.KD.B4AT.PA.getD j 0 = 1 - CFSG.KD.B4AT.PA.getD i 0 := by omega
        have hle : CFSG.KD.B4AT.PA.getD i 0 ≤ 1 := by omega
        rw [hb]
        interval_cases CFSG.KD.B4AT.PA.getD i 0 <;> decide
      rw [hpe]
      exact (mul_inv_eq_one.1 he).symm

theorem tr_fact {k₀ a₀ k₁ a₁ J : ℕ} {w : List ℕ}
    (h : trOK CFSG.KD.B4A.LP CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW (nat_lit 5965) k₀ a₀ w J
      k₁ a₁ = true) :
    Xn k₀ * wVal xG a₀ * evalWord (trGen xG (u hsw)) w * (Xn k₁ * wVal xG a₁)⁻¹ ∈ Hh hsw :=
  tr_sound (Hh hsw) xG (u hsw) Xn (fun c _ => ⟨_, rfl⟩)
    (fun c => by rw [xG, ← map_mul, yGen_mul_self, map_one]) (u_mul_self hsw)
    (fun c hc h7 => by rw [data_ok.2.2.2.1 c hc h7, xG, xG, u_conj hsw hc h7])
    (fun w hw h => by rw [wVal_xG, psiG, MonoidHom.comp_apply, isOne_psi hw h, map_one])
    (fun r hr => (Xn_facts r hr).1) (fun r hr => (Xn_facts r hr).2.1)
    (fun r hr => (Xn_facts r hr).2.2) pw_ok h

theorem trGen_lt {c : ℕ} (hc : c < 10) :
    trGen xG (u hsw) c = SemidirectProduct.inl (psi (yGen 4 3 2 c)) := by
  simp only [trGen, hc, ↓reduceIte]
  rfl

theorem trGen_ten : trGen xG (u hsw) 10 = SemidirectProduct.inl tB := by
  have h : ¬(10 : ℕ) < 10 := by norm_num
  simp only [trGen, h, ↓reduceIte]
  rw [xG, psiG, MonoidHom.comp_apply, u_conj_inl, sigma_psi7]

@[expose] noncomputable def xBn : ℕ → B433 := nodeProd (fun c => psi (yGen 4 3 2 c)) tB

theorem inl_trWord {l : ℕ} (hl : l < 23) :
    SemidirectProduct.inl (evalWord (fun c => psi (yGen 4 3 2 c)) (nodeWord l) * tB *
        (evalWord (fun c => psi (yGen 4 3 2 c)) (nodeWord l))⁻¹) =
      evalWord (trGen xG (u hsw)) (CFSG.KD.B4AT.trWord l) := by
  have hw : ∀ c ∈ nodeWord l, trGen xG (u hsw) c = SemidirectProduct.inl (psi (yGen 4 3 2 c)) :=
    fun c hc => trGen_lt (nodeWord_lt l hl c hc)
  have hinv : ∀ c ∈ nodeWord l, trGen xG (u hsw) c * trGen xG (u hsw) c = 1 := by
    intro c hc
    rw [hw c hc, ← map_mul, ← map_mul, yGen_mul_self, map_one, map_one]
  rw [CFSG.KD.B4AT.trWord, CFSG.Monster.Existence.B433Cover.evalWord_append, evalWord_cons,
    ← evalWord_inv_of_involutive _ hinv, trGen_ten,
    CFSG.Monster.Existence.B433Cover.evalWord_congr hw, map_mul, map_mul, map_inv, map_evalWord]
  simp only [mul_assoc]

theorem chain : ∀ l < 23,
    SemidirectProduct.inl (xBn l) * (Xn (nK l) * wVal xG (nA l))⁻¹ ∈ Hh hsw := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ih =>
    intro hl
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · have hw : wVal xG (nA 0) = 1 := rfl
      rw [xBn, nodeProd_zero, nK, if_pos rfl, Xn_zero, hw, map_one, one_mul, one_mul, inv_one]
      exact (Hh hsw).one_mem
    · have hp := nodeParent_lt l hl hpos
      have hP := ih _ hp (hp.trans hl)
      obtain ⟨hk0, ha0⟩ := tr_start l hl hpos
      have hi : l - 1 < 22 := by omega
      have htr := tr_fact (tr_all (l - 1) hi)
      unfold CFSG.KD.B4AT.trChk at htr
      rw [hk0, ha0, Nat.sub_add_cancel hpos] at htr
      have hK : CFSG.KD.B4AT.K1.getD (l - 1) 0 = nK l := by rw [nK, if_neg (by omega)]
      have hA : CFSG.KD.B4AT.A1.getD (l - 1) 0 = nA l := by rw [nA, if_neg (by omega)]
      rw [hK, hA] at htr
      have hx : SemidirectProduct.inl (xBn l) = SemidirectProduct.inl (xBn (nodeParent l)) *
          evalWord (trGen xG (u hsw)) (CFSG.KD.B4AT.trWord l) := by
        rw [xBn, nodeProd_eq _ _ hpos hl, map_mul, inl_trWord hl]
      have e : SemidirectProduct.inl (xBn l) * (Xn (nK l) * wVal xG (nA l))⁻¹ =
          (SemidirectProduct.inl (xBn (nodeParent l)) *
            (Xn (nK (nodeParent l)) * wVal xG (nA (nodeParent l)))⁻¹) *
          (Xn (nK (nodeParent l)) * wVal xG (nA (nodeParent l)) *
            evalWord (trGen xG (u hsw)) (CFSG.KD.B4AT.trWord l) *
            (Xn (nK l) * wVal xG (nA l))⁻¹) := by
        rw [hx]
        group
      rw [e]
      exact (Hh hsw).mul_mem hP htr

theorem b433_cover (g : B433) :
    ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range, g = a * xBn l * b := by
  obtain ⟨i, a, ha, b, hb, hg⟩ :=
    twist.exists_eq (u_mul_self hsw) (u_conj_Th hsw) (closure_Hh_u hsw) (SemidirectProduct.inl g)
  have hmem := nodeAt_mem i
  obtain ⟨hj, hlv⟩ := (liveL_spec _).1 hmem
  have he : eps (Xn (nodeAt i)) = 1 := by
    have h1 := congrArg eps hg
    rw [eps_inl, map_mul, map_mul, eps_Hh ha, eps_Hh hb, one_mul, mul_one] at h1
    exact h1.symm
  have hpa : CFSG.KD.B4AT.PA.getD (nodeAt i) 0 = 0 := by
    have h2 := eps_Xn _ hj (live_tree _ hj hlv)
    rw [he, paE] at h2
    have hle : CFSG.KD.B4AT.PA.getD (nodeAt i) 0 ≤ 1 := by
      have : ∀ j < 64, CFSG.KD.B4AT.PA.getD j 0 ≤ 1 := by decide +kernel
      exact this _ hj
    interval_cases h : CFSG.KD.B4AT.PA.getD (nodeAt i) 0
    · rfl
    · exact absurd h2.symm (by decide)
  obtain ⟨l, hl, hlk⟩ := even_reached _ hj hlv hpa
  have hc := chain l hl
  rw [hlk] at hc
  have hx : (twist).x i = Xn (nodeAt i) := rfl
  obtain ⟨y1, hy1⟩ := (Hh hsw).mul_mem ha ((Hh hsw).inv_mem hc)
  obtain ⟨y2, hy2⟩ := (Hh hsw).mul_mem ((Hh hsw).inv_mem (⟨_, rfl⟩ :
    psiG hsw (wVal (yGen 4 3 2) (nA l)) ∈ Hh hsw)) hb
  refine ⟨l, hl, psi y1, ⟨y1, rfl⟩, psi y2, ⟨y2, rfl⟩,
    SemidirectProduct.inl_injective (φ := act hsw) ?_⟩
  rw [map_mul, map_mul, hg, hx]
  change _ = psiG hsw y1 * _ * psiG hsw y2
  rw [hy1, hy2, wVal_xG]
  group

end

end CertificateChecks.KernelB433

end
