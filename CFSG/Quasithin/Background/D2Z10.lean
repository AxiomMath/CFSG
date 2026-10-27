module

public import CFSG.Quasithin.Background.D2Z9

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

theorem diag_le_commSub (hV : ∀ v : V, v ^ 2 = 1) {a b : MulAut V} {N : Subgroup V}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hNa : ∀ n ∈ N, a n ∈ N) (hNb : ∀ n ∈ N, b n ∈ N)
    (hfa : ∀ n ∈ N, a n = n → n = 1) :
    N ⊓ fixV (Subgroup.zpowers (a * b)) ≤ commSub N (Subgroup.zpowers (a * b * b)) := by
  have hcab : Commute a b := hab
  have hsa : a ∈ stabSub N := mem_stabSub_of_cube ha3 hNa
  have hsb : b ∈ stabSub N := mem_stabSub_of_cube hb3 hNb
  have hsc' : a * b * b ∈ stabSub N := (stabSub N).mul_mem ((stabSub N).mul_mem hsa hsb) hsb
  have hNc' : ∀ x ∈ Subgroup.zpowers (a * b * b), ∀ n ∈ N, x n ∈ N := fun x hx n hn =>
    ((mem_stabSub.mp (Subgroup.zpowers_le.mpr hsc' hx)) n).mpr hn
  have hc'3 : (a * b * b) ^ 3 = 1 := by
    have h1 : Commute a (b * b) := hcab.mul_right hcab
    calc (a * b * b) ^ 3 = (a * (b * b)) ^ 3 := by rw [mul_assoc]
      _ = a ^ 3 * (b * b) ^ 3 := h1.mul_pow 3
      _ = 1 := by
        rw [(Commute.refl b).mul_pow, ha3, hb3]
        simp
  set F : Subgroup V := N ⊓ fixV (Subgroup.zpowers (a * b)) with hF
  have hcomm_c : ∀ x ∈ Subgroup.zpowers (a * b * b), x * (a * b) = (a * b) * x := by
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : Commute b (a * b) := hcab.symm.mul_right (Commute.refl b)
    have : Commute (a * b * b) (a * b) := (Commute.refl (a * b)).mul_left h2
    exact (this.zpow_left j).eq
  have hFc' : ∀ x ∈ Subgroup.zpowers (a * b * b), ∀ n ∈ F, x n ∈ F := fun x hx n hn =>
    ⟨hNc' x hx n hn.1, fixV_inv_comm (hcomm_c x hx) n hn.2⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers (a * b * b))) := by
    rw [Nat.card_zpowers]
    have hd : orderOf (a * b * b) ∣ 3 := orderOf_dvd_of_pow_eq_one hc'3
    have hp3 : Nat.Prime 3 := by norm_num
    rcases (Nat.dvd_prime hp3).mp hd with h1 | h1 <;> rw [h1] <;> decide
  have hfix : F ⊓ fixV (Subgroup.zpowers (a * b * b)) = ⊥ := by
    rw [eq_bot_iff]
    rintro n ⟨hnF, hnfix⟩
    have hc' : (a * b * b) n = n := mem_fixV_zpowers_iff.mp hnfix
    have hc : (a * b) n = n := mem_fixV_zpowers_iff.mp hnF.2
    have h1 : a (b n) = n := hc
    have h2 : (a * b * b) n = b n := by
      calc (a * b * b) n = (a * b) (b n) := rfl
        _ = (b * a) (b n) := by rw [hab]
        _ = b (a (b n)) := rfl
        _ = b n := by rw [h1]
    have h3 : b n = n := h2.symm.trans hc'
    have h4 : a n = n := by rwa [h3] at h1
    exact Subgroup.mem_bot.mpr (hfa n hnF.1 h4)
  obtain ⟨hsup, -⟩ := coprime_decomp hodd hV hFc'
  rw [hfix, sup_bot_eq] at hsup
  rw [← hsup]
  exact commSub_mono inf_le_left le_rfl


theorem iSup_fin_two_eq {α : Type*} [CompleteLattice α] (f : Fin 2 → α) : ⨆ i, f i = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le fun i => by fin_cases i <;> simp) (sup_le (le_iSup f 0) (le_iSup f 1))

theorem iSupIndep_fin_two_iff {α : Type*} [CompleteLattice α] {f : Fin 2 → α} :
    iSupIndep f ↔ Disjoint (f 0) (f 1) := iSupIndep_pair (by decide) (by decide)

section Two

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem pdecomp_two (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥)
    (h3 : centR X (t * u) = ⊥) :
    ∃ a b : MulAut V, a ∈ centR X t ∧ b ∈ centR X u ∧ Subgroup.zpowers a = centR X t ∧
      Subgroup.zpowers b = centR X u ∧ orderOf a = 3 ∧ orderOf b = 3 ∧
      PDecomp X ![Subgroup.zpowers (a * b), Subgroup.zpowers (a * b * b)] ∧
      conjBy t (Subgroup.zpowers (a * b)) = Subgroup.zpowers (a * b * b) ∧
      conjBy t (Subgroup.zpowers (a * b * b)) = Subgroup.zpowers (a * b) ∧
      conjBy u (Subgroup.zpowers (a * b)) = Subgroup.zpowers (a * b * b) ∧
      conjBy u (Subgroup.zpowers (a * b * b)) = Subgroup.zpowers (a * b) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨-, hNeq, hrk4⟩ := caseTwo hV h k h1 h2 h3
  have hPsup : pCoreOf 3 X = centR X t ⊔ centR X u := by
    rw [pCoreOf_eq_sup_triple hV h k.toTriple, h3, sup_bot_eq]
  have hcU : commV (pCoreOf 3 X) = commV (centR X t) := by
    rw [hPsup, commV_sup, ← hNeq, sup_idem]
  have c1 : Nat.card (centR X t) = 3 := (centR_data hV h k h1).1
  have c2 : Nat.card (centR X u) = 3 := (centR_data hV h k.symm h2).1
  obtain ⟨a, haQ, ha1, haz, hao⟩ := exists_generator_of_prime_card (p := 3) c1
  obtain ⟨b, hbQ, hb1, hbz, hbo⟩ := exists_generator_of_prime_card (p := 3) c2
  have ha3 : a ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hbo]; exact pow_orderOf_eq_one b
  have hab : a * b = b * a := centR_comm hV h t u a haQ b hbQ
  have haP : a ∈ pCoreOf 3 X := centR_le_pCoreOf X t haQ
  have hbP : b ∈ pCoreOf 3 X := centR_le_pCoreOf X u hbQ
  have hne : Subgroup.zpowers a ≠ Subgroup.zpowers b := by
    rw [haz, hbz]
    intro heq
    apply h1
    have := centR_inf_eq_bot hV h k
    rwa [← heq, inf_idem] at this
  have hcab : Commute a b := hab
  have hc3 : (a * b) ^ 3 = 1 := by rw [hcab.mul_pow, ha3, hb3, one_mul]
  have hc'3 : (a * b * b) ^ 3 = 1 := by
    have h1 : Commute a (b * b) := hcab.mul_right hcab
    calc (a * b * b) ^ 3 = (a * (b * b)) ^ 3 := by rw [mul_assoc]
      _ = a ^ 3 * (b * b) ^ 3 := h1.mul_pow 3
      _ = 1 := by
        rw [(Commute.refl b).mul_pow, ha3, hb3]
        simp
  have hc1 : a * b ≠ 1 := by
    intro hh
    apply hne
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hh
    rw [hb', Subgroup.zpowers_inv]
  have hc'1 : a * b * b ≠ 1 := by
    intro hh
    apply hne
    have e1 : a * (b * b) = 1 := by rwa [← mul_assoc]
    have e2 : a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left e1
    have e3 : (b * b)⁻¹ = b := by
      rw [inv_eq_iff_mul_eq_one]
      calc b * b * b = b ^ 3 := (pow_three' b).symm
        _ = 1 := hb3
    have : a = b := by rw [e2, e3]
    rw [this]
  have hoc : orderOf (a * b) = 3 := orderOf_eq_prime hc3 hc1
  have hoc' : orderOf (a * b * b) = 3 := orderOf_eq_prime hc'3 hc'1
  have hcc : Nat.card (Subgroup.zpowers (a * b)) = 3 := by rw [Nat.card_zpowers, hoc]
  have hcc' : Nat.card (Subgroup.zpowers (a * b * b)) = 3 := by rw [Nat.card_zpowers, hoc']
  have hE9 := rk_commV_sum_E9 hV hao hbo hab hne
  have ra : rk (commV (Subgroup.zpowers a)) = 4 := by rw [haz]; exact hrk4
  have rb : rk (commV (Subgroup.zpowers b)) = 4 := by rw [hbz, ← hNeq]; exact hrk4
  have rab : rk (commV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) = 4 := by
    rw [haz, hbz, ← hPsup, hcU]; exact hrk4
  rw [ra, rb, rab] at hE9
  obtain ⟨m1, hm1⟩ := (commV_card_three hV hcc).2.2.2
  obtain ⟨m2, hm2⟩ := (commV_card_three hV hcc').2.2.2
  have p1 := one_le_rk_commV_zpowers hV hc1
  have p2 := one_le_rk_commV_zpowers hV hc'1
  have rc : rk (commV (Subgroup.zpowers (a * b))) = 2 := by omega
  have rc' : rk (commV (Subgroup.zpowers (a * b * b))) = 2 := by omega
  set N := commV (centR X t) with hN
  have hPodd : Odd (Nat.card (pCoreOf 3 X)) :=
    odd_card_of_isPGroup_odd (by norm_num) (pCoreOf_isPGroup 3 X)
  have hstab : ∀ x ∈ pCoreOf 3 X, ∀ n ∈ N, x n ∈ N := fun x hx n hn =>
    Nt_inv_P (pCoreOf_comm hV h) t hx n hn
  have hzle : Subgroup.zpowers (a * b) ≤ pCoreOf 3 X :=
    Subgroup.zpowers_le.mpr ((pCoreOf 3 X).mul_mem haP hbP)
  have hzle' : Subgroup.zpowers (a * b * b) ≤ pCoreOf 3 X :=
    Subgroup.zpowers_le.mpr ((pCoreOf 3 X).mul_mem ((pCoreOf 3 X).mul_mem haP hbP) hbP)
  have hNc : ∀ x ∈ Subgroup.zpowers (a * b), ∀ n ∈ N, x n ∈ N := fun x hx n hn =>
    hstab x (hzle hx) n hn
  have hNc' : ∀ x ∈ Subgroup.zpowers (a * b * b), ∀ n ∈ N, x n ∈ N := fun x hx n hn =>
    hstab x (hzle' hx) n hn
  have hfa : ∀ n ∈ N, a n = n → n = 1 := by
    intro n hn hfix
    have hn' : n ∈ fixV (Subgroup.zpowers a) := mem_fixV_zpowers_iff.mpr hfix
    rw [haz] at hn'
    have : n ∈ commV (centR X t) ⊓ fixV (centR X t) := ⟨hn, hn'⟩
    rwa [(commV_card_three hV c1).2.1, Subgroup.mem_bot] at this
  have D1 := diag_le_commSub hV ha3 hb3 hab (fun n hn => hstab a haP n hn)
    (fun n hn => hstab b hbP n hn) hfa
  have hbb3 : (b * b) ^ 3 = 1 := by rw [(Commute.refl b).mul_pow, hb3]; simp
  have D2 := diag_le_commSub hV ha3 hbb3 (hcab.mul_right hcab).eq
    (fun n hn => hstab a haP n hn)
    (fun n hn => hstab b hbP (b n) (hstab b hbP n hn)) hfa
  have e1 : a * (b * b) = a * b * b := (mul_assoc a b b).symm
  have e2 : a * (b * b) * (b * b) = a * b := by
    have : b * b * (b * b) = b := by
      calc b * b * (b * b) = (b * b * b) * b := by group
        _ = b ^ 3 * b := by rw [pow_three']
        _ = b := by rw [hb3, one_mul]
    calc a * (b * b) * (b * b) = a * (b * b * (b * b)) := by group
      _ = a * b := by rw [this]
  rw [e2, e1] at D2
  have hsub1 : commV (Subgroup.zpowers (a * b)) = commSub N (Subgroup.zpowers (a * b)) := by
    rw [commV_eq_commSub_commV hV hPodd hzle, hcU]
  have hsub2 : commV (Subgroup.zpowers (a * b * b)) =
      commSub N (Subgroup.zpowers (a * b * b)) := by
    rw [commV_eq_commSub_commV hV hPodd hzle', hcU]
  have hF1 : rk (commSub N (Subgroup.zpowers (a * b)) : Subgroup V) +
      rk (N ⊓ fixV (Subgroup.zpowers (a * b)) : Subgroup V) = rk N :=
    rk_commSub_add_rk_inf_fixV hNc
  have hF2 : rk (commSub N (Subgroup.zpowers (a * b * b)) : Subgroup V) +
      rk (N ⊓ fixV (Subgroup.zpowers (a * b * b)) : Subgroup V) = rk N :=
    rk_commSub_add_rk_inf_fixV hNc'
  rw [← hsub1, rc] at hF1
  rw [← hsub2, rc'] at hF2
  have hrkN : rk N = 4 := hrk4
  have Eq1 : N ⊓ fixV (Subgroup.zpowers (a * b)) = commV (Subgroup.zpowers (a * b * b)) := by
    rw [hsub2]
    exact eq_of_le_of_rk_le hV D1 (by rw [← hsub2, rc']; omega)
  have Eq2 : N ⊓ fixV (Subgroup.zpowers (a * b * b)) = commV (Subgroup.zpowers (a * b)) := by
    rw [hsub1]
    exact eq_of_le_of_rk_le hV D2 (by rw [← hsub1, rc]; omega)
  have hbmem : b ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_zpowers (a * b)) : a * b ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (a * b * b)) :
        a * b * b ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b))
    have e : (a * b)⁻¹ * (a * b * b) = b := by group
    rwa [e] at h
  have hamem : a ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b) := by
    have h := Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers (a * b)) :
        a * b ∈ Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b))
      (Subgroup.inv_mem _ hbmem)
    have e : (a * b) * b⁻¹ = a := by group
    rwa [e] at h
  have hdisj : Subgroup.zpowers (a * b) ⊓ Subgroup.zpowers (a * b * b) = ⊥ := by
    apply inf_eq_bot_of_card_prime hcc hcc'
    intro heq
    have hc'mem : a * b * b ∈ Subgroup.zpowers (a * b) := heq ▸ Subgroup.mem_zpowers (a * b * b)
    have hb' : b ∈ Subgroup.zpowers (a * b) := by
      have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers (a * b))) hc'mem
      have e : (a * b)⁻¹ * (a * b * b) = b := by group
      rwa [e] at h
    have ha' : a ∈ Subgroup.zpowers (a * b) := by
      have h := Subgroup.mul_mem _ (Subgroup.mem_zpowers (a * b)) (Subgroup.inv_mem _ hb')
      have e : (a * b) * b⁻¹ = a := by group
      rwa [e] at h
    exact hne ((zpowers_eq_of_prime_card hcc ha' ha1).trans
      (zpowers_eq_of_prime_card hcc hb' hb1).symm)
  have hcomm_cc' : ∀ x ∈ Subgroup.zpowers (a * b), ∀ y ∈ Subgroup.zpowers (a * b * b),
      x * y = y * x := by
    intro x hx y hy
    exact pCoreOf_comm hV h x (hzle hx) y (hzle' hy)
  have hPeq : Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers (a * b * b) = pCoreOf 3 X := by
    apply le_antisymm (sup_le hzle hzle')
    rw [hPsup, ← haz, ← hbz]
    exact sup_le (Subgroup.zpowers_le.mpr hamem) (Subgroup.zpowers_le.mpr hbmem)
  have e1 : t * a * t⁻¹ = a := (centR_actions hV h k haQ).1
  have e2 : t * b * t⁻¹ = b⁻¹ := inverts_centR hV h k.symm b hbQ
  have hbinv : b⁻¹ = b * b := by
    rw [inv_eq_iff_mul_eq_one]
    calc b * (b * b) = b ^ 3 := (pow_three b).symm
      _ = 1 := hb3
  have hbb : b * b * (b * b) = b := by
    calc b * b * (b * b) = (b * b * b) * b := by group
      _ = b ^ 3 * b := by rw [pow_three']
      _ = b := by rw [hb3, one_mul]
  have f1 : u * a * u⁻¹ = a⁻¹ := inverts_centR hV h k a haQ
  have f2 : u * b * u⁻¹ = b := (centR_actions hV h k.symm hbQ).1
  refine ⟨a, b, haQ, hbQ, haz, hbz, hao, hbo, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hzle
    · exact hzle'
  · intro i
    fin_cases i
    · exact hcc
    · exact hcc'
  · rw [iSupIndep_fin_two_iff]
    exact disjoint_iff.mpr hdisj
  · rw [iSup_fin_two_eq]
    exact hPeq
  · rw [← hPeq, card_sup_of_commute hcomm_cc' hdisj, hcc, hcc']
    norm_num
  · intro i
    fin_cases i
    · exact rc
    · exact rc'
  · rw [iSupIndep_fin_two_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
    have h1x : x ∈ N ⊓ fixV (Subgroup.zpowers (a * b * b)) := by rw [Eq2]; exact hx.1
    have h2x : x ∈ commV (Subgroup.zpowers (a * b * b)) := hx.2
    have : x ∈ commV (Subgroup.zpowers (a * b * b)) ⊓ fixV (Subgroup.zpowers (a * b * b)) :=
      ⟨h2x, h1x.2⟩
    rwa [(commV_card_three hV hcc').2.1, Subgroup.mem_bot] at this
  · rw [iSup_fin_two_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hPeq, commV_sup]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · rw [← Eq2]; exact inf_le_right
    · rw [← Eq1]; exact inf_le_right
  · rw [← zpowers_conj]
    congr 1
    calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = a * b⁻¹ := by rw [e1, e2]
      _ = a * b * b := by rw [hbinv, mul_assoc]
  · rw [← zpowers_conj]
    congr 1
    calc t * (a * b * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * b * t⁻¹) := by group
      _ = a * b⁻¹ * b⁻¹ := by rw [e1, e2]
      _ = a * (b * b) * (b * b) := by rw [hbinv]
      _ = a * b := by rw [mul_assoc a (b * b), hbb]
  · rw [← zpowers_conj]
    have e₁ : (a⁻¹ * b)⁻¹ = a * b * b := by
      rw [mul_inv_rev, inv_inv, hbinv, mul_assoc a b b]
      exact (hcab.mul_right hcab).eq.symm
    have e₀ : u * (a * b) * u⁻¹ = a⁻¹ * b := by
      calc u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
        _ = a⁻¹ * b := by rw [f1, f2]
    rw [e₀]
    calc Subgroup.zpowers (a⁻¹ * b) = Subgroup.zpowers ((a⁻¹ * b)⁻¹) := Subgroup.zpowers_inv.symm
      _ = Subgroup.zpowers (a * b * b) := by rw [e₁]
  · rw [← zpowers_conj]
    have e₂ : (a⁻¹ * b * b)⁻¹ = a * b := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, hbinv]
      calc b * b * (b * b * a) = (b * b * (b * b)) * a := by group
        _ = b * a := by rw [hbb]
        _ = a * b := hab.symm
    have e₀ : u * (a * b * b) * u⁻¹ = a⁻¹ * b * b := by
      calc u * (a * b * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) * (u * b * u⁻¹) := by group
        _ = a⁻¹ * b * b := by rw [f1, f2]
    rw [e₀]
    calc Subgroup.zpowers (a⁻¹ * b * b) = Subgroup.zpowers ((a⁻¹ * b * b)⁻¹) :=
          Subgroup.zpowers_inv.symm
      _ = Subgroup.zpowers (a * b) := by rw [e₂]

end Two

end CFSG.Quasithin
