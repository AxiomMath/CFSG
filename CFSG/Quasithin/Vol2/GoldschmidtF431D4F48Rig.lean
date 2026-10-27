module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4F48Spec

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem rep_f48PowLoop (fuel : ℕ) {b r : Array ℕ} {σ ρ : Equiv.Perm (Fin 819)} {e : ℕ}
    (hb : Rep 819 b σ) (hr : Rep 819 r ρ) (he : e < 2 ^ fuel) :
    Rep 819 (f48PowLoop fuel b e r) (σ ^ e * ρ) := by
  induction fuel generalizing b r σ ρ e with
  | zero =>
    have he0 : e = 0 := by simpa using he
    subst he0
    simpa [f48PowLoop] using hr
  | succ fuel ih =>
    by_cases he0 : e = 0
    · subst he0
      simpa [f48PowLoop] using hr
    · simp only [f48PowLoop, he0, ↓reduceIte, beq_iff_eq]
      have hr' : Rep 819 (if e % 2 = 1 then compA 819 b r else r) (σ ^ (e % 2) * ρ) := by
        split_ifs with hodd
        · rw [hodd, pow_one]
          exact rep_compA hb hr
        · have h0 : e % 2 = 0 := by omega
          rw [h0, pow_zero, one_mul]
          exact hr
      have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      have := ih (rep_compA hb hb) hr' hlt
      have e1 : (σ * σ) ^ (e / 2) * (σ ^ (e % 2) * ρ) = σ ^ e * ρ := by
        rw [← mul_assoc, ← sq, ← pow_mul, ← pow_add, Nat.div_add_mod]
      rwa [e1] at this

theorem rep_f48PowA {b : Array ℕ} {σ : Equiv.Perm (Fin 819)} (hb : Rep 819 b σ) {e : ℕ}
    (he : e < 2 ^ 40) : Rep 819 (f48PowA b e) (σ ^ e) := by
  have := rep_f48PowLoop 40 hb (rep_idA (n := 819)) he
  rwa [mul_one] at this

variable {lay n q : Array ℕ} {F : Array (Array ℕ)} {r : OrbRec} {M p0 : ℕ}
  {fE : ℕ → Equiv.Perm (Fin 819)} {σ : Equiv.Perm (Fin 819)}

theorem rep_of_candOK {a : Array ℕ} {k : ℕ} (hlay : f48LayOK lay p0 = true)
    (horb : f48OrbOK lay F r p0 = true) (hcand : f48CandOK lay F r p0 a k = true)
    (hFR : ∀ j < F.size, Rep 819 F[j]! (fE j))
    (hnear : ∀ p : Fin 819, lay[(p : ℕ)]! ≤ 4 → σ p = p)
    (hcomm : ∀ j < F.size, σ * fE j = fE j * σ) (hp0 : p0 < 819)
    (hk : (σ ⟨p0, hp0⟩ : ℕ) = k) : Rep 819 a σ := by
  obtain ⟨-, hlay'⟩ := f48LayOK_spec hlay
  obtain ⟨h0, hlt, hstep, hcov⟩ := f48OrbOK_facts horb
  simp only [f48CandOK, Bool.and_eq_true, beq_iff_eq] at hcand
  obtain ⟨⟨hA, hB⟩, hC⟩ := hcand
  have hind : ∀ i, i < 512 → ∀ y : Fin 819, (y : ℕ) = r.ord[i]! → a[(y : ℕ)]! = σ y := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi y hy
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · have hy' : y = ⟨p0, hp0⟩ := Fin.ext (by rw [hy, h0])
        subst hy'
        rw [hk]
        exact hA
      · obtain ⟨hpar, hlab, hF'⟩ := hstep i hi0 hi
        have hparlt : r.par[i]! < 512 := by omega
        let z : Fin 819 := ⟨r.ord[r.par[i]!]!, hlt _ hparlt⟩
        have hfz : fE r.lab[i]! z = y := by
          apply Fin.ext
          rw [← (hFR _ hlab) z, hy, ← hF']
        have ihz : a[r.ord[r.par[i]!]!]! = σ z := ih _ hpar hparlt z rfl
        have hcz := congrArg (fun g : Equiv.Perm (Fin 819) => g z) (hcomm _ hlab)
        simp only [Equiv.Perm.mul_apply] at hcz
        have hCi := allLt_spec hC hi
        simp only [Bool.or_eq_true, beq_iff_eq, show i ≠ 0 by omega, false_or] at hCi
        rw [hy, hCi, ihz, (hFR _ hlab) (σ z)]
        exact congrArg Fin.val (by rw [← hfz]; exact hcz.symm)
  intro x
  rcases hlay' x x.2 with hle | h6
  · have hx : σ x = x := hnear x hle
    have h4 := allLt_spec hB x.2
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h4
    rw [hx]
    omega
  · obtain ⟨hp, ho⟩ := hcov x x.2 h6
    exact hind _ hp x ho.symm

theorem hex_sigma_eq_one {nE qE : Equiv.Perm (Fin 819)} (hM : M < 2 ^ 40)
    (hlay : f48LayOK lay p0 = true) (horb : f48OrbOK lay F r p0 = true)
    (hkey : f48KeyAll lay F r M p0 n q = true) (hnR : Rep 819 n nE) (hqR : Rep 819 q qE)
    (hFR : ∀ j < F.size, Rep 819 F[j]! (fE j))
    (hnear : ∀ p : Fin 819, lay[(p : ℕ)]! ≤ 4 → σ p = p)
    (hcomm : ∀ j < F.size, σ * fE j = fE j * σ)
    (hsq : (nE * σ) * (nE * σ) = 1) (hexp : ((nE * σ) * qE) ^ M = 1) : σ = 1 := by
  obtain ⟨hp0, hlay'⟩ := f48LayOK_spec hlay
  obtain ⟨h0, hlt, -, -⟩ := f48OrbOK_facts horb
  have hp0lt : p0 < 819 := by simpa [h0] using hlt 0 (by omega)
  let p0' : Fin 819 := ⟨p0, hp0lt⟩
  have hfar : lay[(σ p0' : ℕ)]! = 6 := by
    rcases hlay' (σ p0') (σ p0').2 with hle | h6
    · exfalso
      have h2 : σ p0' = p0' := σ.injective (hnear _ hle)
      rw [h2] at hle
      have : lay[p0]! ≤ 4 := hle
      omega
    · exact h6
  obtain ⟨hcand, hid, hfail⟩ := f48KeyAll_spec hkey (σ p0').2 hfar
  have hrep := rep_of_candOK hlay horb hcand hFR hnear hcomm hp0lt rfl
  by_cases hkp : (σ p0' : ℕ) = p0
  · exact (eqA_iff hrep rep_idA).1 (hid hkp)
  · exfalso
    have hf := hfail hkp
    have hm : Rep 819 (compA 819 n (f48TArr F r p0 (σ p0' : ℕ))) (nE * σ) := rep_compA hnR hrep
    have e1 := (eqA_iff (rep_compA hm hm) rep_idA).2 hsq
    have e2 := (eqA_iff (rep_f48PowA (rep_compA hm hqR) hM) rep_idA).2 hexp
    simp only [f48FullFail, e1, e2] at hf
    simp at hf

end CFSG.Quasithin.D4Hex
