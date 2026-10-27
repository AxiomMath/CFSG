module

public import Certificates.Kernel.Co1.Top
public import CFSG.Certificates.Kernel.BindSound
public import CFSG.Certificates.Kernel.Co1.Data.C1_Sel
public import CFSG.Certificates.Kernel.Co1.Data.C2_Sel
public import Certificates.Data.Kernel.BindRange
public import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co1.Checks.Bind

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem relsEq_spec {CRT PRT : ℕ → ℕ} {R PR Hs : ℕ} (h : relsEq CRT PRT R PR Hs = true) :
    ∀ r < R, ∃ q < PR, CRT r = PRT q := by
  induction R with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (relsEq CRT PRT n PR Hs)
      (andB (Nat.blt (hget Hs n) PR) (Nat.beq (CRT n) (PRT (hget Hs n)))) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h1 r hr
    · obtain ⟨h3, h4⟩ := KB.andB_true h2
      exact ⟨_, by simpa using h3, Nat.eq_of_beq_eq_true h4⟩

theorem lettersBelow_spec' {W n b : ℕ} (h : HO.lettersBelow W n b = true) : ∀ q < n, wLet W q < b := by
  induction n with
  | zero => intro q hq; omega
  | succ n ih =>
    intro q hq
    have h' : andB (HO.lettersBelow W n b) (Nat.blt (wLet W n) b) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
    · exact ih h1 q hq
    · simpa using h2

theorem relsLet_spec {RT : ℕ → ℕ} {nR : ℕ} (h : BindS.relsLet RT nR = true) :
    ∀ r < nR, wLen (RT r) < 256 ∧ ∀ q < wLen (RT r), wLet (wWord (RT r)) q < 254 := by
  induction nR with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (BindS.relsLet RT n) (andB (Nat.blt (wLen (RT n)) (nat_lit 256))
      (HO.lettersBelow (wWord (RT n)) (wLen (RT n)) (nat_lit 254))) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h1 r hr
    · obtain ⟨h3, h4⟩ := KB.andB_true h2
      exact ⟨by simpa using h3, lettersBelow_spec' h4⟩

@[expose] noncomputable def relsBelow (RT : ℕ → ℕ) (nR b : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih
    (HO.lettersBelow (wWord (RT r)) (wLen (RT r)) b)) nR

theorem relsBelow_spec {RT : ℕ → ℕ} {nR b : ℕ} (h : relsBelow RT nR b = true) :
    ∀ r < nR, ∀ q < wLen (RT r), wLet (wWord (RT r)) q < b := by
  induction nR with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (relsBelow RT n b) (HO.lettersBelow (wWord (RT n)) (wLen (RT n)) b) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h1 r hr
    · exact lettersBelow_spec' h2

theorem letV_two {G : Type*} [Group G] (gen : ℕ → G) (c : ℕ) : letV gen (2 * c) = gen c := by
  unfold letV
  have e2 : ¬ 2 * c = 255 := by omega
  have e3 : 2 * c % 2 = 0 := by omega
  have e4 : 2 * c / 2 = c := by omega
  simp only [e2, e3, e4, ↓reduceIte]

theorem bval_single {G : Type*} [Group G] (gen : ℕ → G) {e g : ℕ} (hl : wLen e = 1)
    (hw : wWord e = 2 * g) (hg : g < 128) : bval gen (wWord e) (wLen e) = gen g := by
  rw [hl]
  change ([0].map fun i => letV gen (wLet (wWord e) i)).prod = gen g
  have e0 : wLet (wWord e) 0 = 2 * g := by
    rw [wLet_eq, hw]
    simp only [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, e0]
  exact letV_two gen g

theorem bval_congr_lt {G : Type*} [Group G] {gen gen' : ℕ → G} {K W n : ℕ} (hK : K ≤ 127)
    (h : ∀ k < K, gen k = gen' k) (hW : ∀ q < n, wLet W q < 2 * K) : bval gen W n = bval gen' W n := by
  unfold bval
  congr 1
  apply List.map_congr_left
  intro q hq
  have hq' := hW q (List.mem_range.mp hq)
  unfold letV
  have e : ¬ wLet W q = 255 := by omega
  simp only [e, ↓reduceIte, h _ (by omega : wLet W q / 2 < K)]

theorem stmap_hM {G : Type*} [Group G] (pg : ℕ → G) {ST : ℕ → ℕ} {K M : ℕ}
    (hM : Nat.beq M (stMap ST K) = true) (h0 : M ≠ 0) (hK : K ≤ 127) :
    ∀ g < 128, mget M g < 255 → mget M g < 127 ∧
      (fun j => bval pg (wWord (ST j)) (wLen (ST j))) (mget M g) = pg g := by
  intro g hg hm
  obtain ⟨h1, h2, h3⟩ := BindS.stMap_sound (Nat.eq_of_beq_eq_true hM) h0 g hg hm
  exact ⟨by omega, bval_single pg h2 h3 hg⟩

theorem img_eq {G : Type*} (f : ℕ → G) (a b : ℕ) (h : ∀ x, x < a ↔ 2 * x < b) :
    f '' {j | j < a} = f '' {g | 2 * g < b} := by
  congr 1
  ext x
  exact h x

theorem card_le_step' {G : Type*} [Group G] {H K : Subgroup G} {N M : ℕ}
    (h : H.relIndex K ≠ 0 ∧ H.relIndex K ≤ N) (hH : Nat.card H ≠ 0 ∧ Nat.card H ≤ M) :
    Nat.card K ≠ 0 ∧ Nat.card K ≤ N * M := by
  have hf : Finite H := Nat.finite_of_card_ne_zero hH.1
  have hi : (H ⊓ K).relIndex K = H.relIndex K := Subgroup.inf_relIndex_right H K
  have hf' : Finite (H ⊓ K : Subgroup G) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : H ⊓ K ≤ H))
  have hc : Nat.card (H ⊓ K : Subgroup G) ≠ 0 ∧ Nat.card (H ⊓ K : Subgroup G) ≤ M :=
    ⟨Nat.card_pos.ne', (Subgroup.card_le_of_le inf_le_left).trans hH.2⟩
  exact KB.card_le_step ⟨inf_le_right, hi ▸ h.1, hi ▸ h.2⟩ hc

abbrev Tab {G : Type*} [Group G] (gen : ℕ → G) (ST : ℕ → ℕ) (nS L a : ℕ) : Prop :=
  (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (gen '' {g | 2 * g < L})) ≠ 0 ∧
    (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
      (Subgroup.closure (gen '' {g | 2 * g < L})) ≤ a

noncomputable abbrev cg2 : ℕ → PG :=
  fun j => bval g0 (wWord (CFSG.KD.C1.selST j)) (wLen (CFSG.KD.C1.selST j))

theorem r1 : ∀ r < 45, bval g0 (wWord (CFSG.KD.C1.selRT r)) (wLen (CFSG.KD.C1.selRT r)) = 1 := by
  intro r hr
  obtain ⟨q, hq, e⟩ := relsEq_spec CFSG.KD.Co1B.bT1 r hr
  rw [e]
  exact top_val hq

theorem r2 : ∀ r < 33, bval cg2 (wWord (CFSG.KD.C2.selRT r)) (wLen (CFSG.KD.C2.selRT r)) = 1 :=
  BindS.relsSub_sound g0 cg2 CFSG.KD.Co1B.b2 (stmap_hM g0 CFSG.KD.Co1B.bM12 (by decide) (by decide))
    r1 (relsBelow_spec (by quickRfl))

theorem r2_below : ∀ r < 33, ∀ q < wLen (CFSG.KD.C2.selRT r), wLet (wWord (CFSG.KD.C2.selRT r)) q < 2 * 7 :=
  relsBelow_spec (by quickRfl)

theorem letV_sq {G : Type*} [Group G] (gen : ℕ → G) {W g : ℕ} (h0 : wLet W 0 = 2 * g)
    (h1 : wLet W 1 = 2 * g) : bval gen W 2 = gen g * gen g := by
  change ([0, 1].map fun i => letV gen (wLet W i)).prod = gen g * gen g
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h0, h1, letV_two gen g]

theorem cg2_sq : ∀ g < 7, cg2 g * cg2 g = 1 := by
  intro g hg
  have h := r2 g (by omega)
  have hl : wLen (CFSG.KD.C2.selRT g) = 2 := by
    interval_cases g <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  have h0 : wLet (wWord (CFSG.KD.C2.selRT g)) 0 = 2 * g := by
    interval_cases g <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  have h1 : wLet (wWord (CFSG.KD.C2.selRT g)) 1 = 2 * g := by
    interval_cases g <;> exact Nat.eq_of_beq_eq_true (by quickRfl)
  rw [hl, letV_sq cg2 h0 h1] at h
  exact h

noncomputable abbrev pg2 : ℕ → PG := fun g => if g < 7 then cg2 g else 1

theorem pg2_sq : ∀ g, pg2 g * pg2 g = 1 := by
  intro g
  by_cases hg : g < 7
  · simp only [pg2, hg, ↓reduceIte]
    exact cg2_sq g hg
  · simp only [pg2, hg, ↓reduceIte, mul_one]

theorem r2' : ∀ r < 33, bval pg2 (wWord (CFSG.KD.C2.selRT r)) (wLen (CFSG.KD.C2.selRT r)) = 1 := by
  intro r hr
  rw [bval_congr_lt (gen := pg2) (gen' := cg2) (K := 7) (by norm_num)
    (fun k hk => by simp only [pg2, hk, ↓reduceIte]) (r2_below r hr)]
  exact r2 r hr

end CertificateChecks.KernelCo1

end
