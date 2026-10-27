
module

public import Certificates.Kernel.Co1M.K10075

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.Co1B CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.Co1Orb CFSG.KC.PairCount CFSG.Blueprint
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.TwoBK CFSG.Sporadic.Co1.Module.InvFam
  CFSG.Sporadic.SmallF2 CertificateChecks.KernelVec.Co1

theorem word_elem (w : List Bool) : ∃ g : NativeSporadic.Co1, matHom g = wordMat w := by
  induction w with
  | nil => exact ⟨1, by simp [wordMat]⟩
  | cons b w ih =>
    obtain ⟨g, hg⟩ := ih
    cases b
    · obtain ⟨a, ha⟩ := exists_co1_matB
      refine ⟨a * g, ?_⟩
      have h1 : matHom a = matB := ha
      rw [map_mul, h1, hg]
      simp [wordMat, letterMat]
    · obtain ⟨a, ha⟩ := exists_co1_matA
      refine ⟨a * g, ?_⟩
      have h1 : matHom a = matA := ha
      rw [map_mul, h1, hg]
      simp [wordMat, letterMat]

theorem pm_word {w : List Bool} {M : Nat}
    (h : Nat.beq (wordABFrom CertificateChecks.KernelCo1Cover.R0 CertificateChecks.KernelCo1Cover.R1
      w oneK) M = true) : ∃ x, PM x M := by
  obtain ⟨g, hg⟩ := word_elem w
  refine ⟨g, ?_⟩
  unfold PM
  rw [hg, ← rowsMatrix_wordRows, CertificateChecks.KernelCo1B.wordRows_eq, Nat.eq_of_beq_eq_true h]

theorem and3 {a b c : Bool} (h : andB a (andB b c) = true) : a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [andB]

theorem and2 {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem hits_of {w : Nat} {J : Nat → Nat} (h : ∀ s < 384, hitSl w J s = true) :
    ∀ j < 98304, hitAt 98280 (hitTest w) 552 J 10 j = true := by
  intro j hj
  have hs := h (j / 256) (by omega)
  unfold hitSl allS at hs
  have := allN_spec hs (j % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (j / 256) 256) (j % 256) = j := by
    change j / 256 * 256 + j % 256 = j
    omega
  rwa [e] at this

theorem count_le {w : Nat} {J : Nat → Nat} (hw : w < 2 ^ 24) (h : ∀ s < 384, hitSl w J s = true) :
    ((orb co1Act v₂).filter fun a => toVecD 24 w + a ∈ orb co1Act v₂).card ≤ 552 := by
  rw [count_O2 hw]
  exact hits_card (N := 98304) (test := hitTest w) (by norm_num) (by norm_num) (hits_of h)

theorem e3 : v₂ + toVecD 24 u3v75 = toVecD 24 w3v75 := by
  have h : (2 ^^^ u3v75) = w3v75 := Nat.eq_of_beq_eq_true xor75
  rw [← toVecD_v₂, ← toVecD_xor, h]

theorem e4 : v₂ + toVecD 24 3 = toVecD 24 1 := by
  have h : (2 ^^^ 3 : Nat) = 1 := by decide
  rw [← toVecD_v₂, ← toVecD_xor, h]

theorem stab_gens : ∃ x₁ x₂ : NativeSporadic.Co1, PM x₁ RS1v75 ∧ PM x₂ RS2v75 ∧
    ∃ xg, PM xg RGv75 := by
  obtain ⟨h1, h2, h3⟩ := and3 words75
  obtain ⟨x₁, p₁⟩ := pm_word h1
  obtain ⟨x₂, p₂⟩ := pm_word h2
  obtain ⟨xg, pg⟩ := pm_word h3
  exact ⟨x₁, x₂, p₁, p₂, xg, pg⟩

theorem images {x₁ x₂ : NativeSporadic.Co1} (p₁ : PM x₁ RS1v75) (p₂ : PM x₂ RS2v75) {u n : Nat}
    {T : STree} (hT : T.OK (actV RT75 [0, 1]) 2 u 24 n) (hu : u < 2 ^ 24) :
    ∃ H : Finset Vec24, (∀ h ∈ H, ∃ x, co1Act x v₂ = v₂ ∧ co1Act x (toVecD 24 u) = h) ∧
      n ≤ H.card := by
  obtain ⟨t1, t2, -⟩ := and3 trs75
  obtain ⟨f1, f2, -⟩ := and3 fixes75
  have tr1 : trK 24 RS1v75 = getL 0 RT75 0 := Nat.eq_of_beq_eq_true t1
  have tr2 : trK 24 RS2v75 = getL 0 RT75 1 := Nat.eq_of_beq_eq_true t2
  let gen : Nat → NativeSporadic.Co1 := fun l => if l = 0 then x₁ else x₂
  have hact : ∀ l < lenL [0, 1], ∀ v, co1Act (gen l) (toVecD 24 v) =
      toVecD 24 (vmF 24 (getL 0 RT75 (getL 0 [0, 1] l)) v) := by
    intro l hl v
    have hl' : l = 0 ∨ l = 1 := by
      have : lenL [0, 1] = 2 := rfl
      omega
    rcases hl' with rfl | rfl
    · change co1Act x₁ (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 RT75 0) v)
      exact pm_act p₁ tr1 v
    · change co1Act x₂ (toVecD 24 v) = toVecD 24 (vmF 24 (getL 0 RT75 1) v)
      exact pm_act p₂ tr2 v
  have hgen : ∀ l < lenL [0, 1], gen l ∈ stabOf v₂ := by
    intro l hl
    have hl' : l = 0 ∨ l = 1 := by
      have : lenL [0, 1] = 2 := rfl
      omega
    rcases hl' with rfl | rfl
    · change co1Act x₁ v₂ = v₂
      have e : vmF 24 (getL 0 RT75 0) 2 = 2 := Nat.eq_of_beq_eq_true f1
      rw [← toVecD_v₂, pm_act p₁ tr1 2, e]
    · change co1Act x₂ v₂ = v₂
      have e : vmF 24 (getL 0 RT75 1) 2 = 2 := Nat.eq_of_beq_eq_true f2
      rw [← toVecD_v₂, pm_act p₂ tr2 2, e]
  have hT' : T.OK (actV RT75 [0, 1]) (lenL [0, 1]) u 24 n := hT
  obtain ⟨t, ht, hd⟩ := vec_family (stabOf v₂) (RT := RT75) (I := [0, 1]) (root := u) (n := n)
    (T := T) hT' hu gen hgen hact
  refine ⟨(Finset.range n).image fun i => co1Act (t i) (toVecD 24 u), fun h hh => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hh
    exact ⟨t i, (ht i (Finset.mem_range.1 hi)).1, rfl⟩
  · rw [Finset.card_image_of_injOn (fun i hi j hj e => hd i (Finset.mem_range.1 hi) j
      (Finset.mem_range.1 hj) e), Finset.card_range]

end CertificateChecks.KernelCo1M

end
