module

public import CFSG.Timmesfeld.ARS.ExclNSChain

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {n : ℕ}

theorem exists_weylAction_eq_neg_ev {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)
    (P : EpsCoords A) {i₀ : Fin n} (hi₀ : i₀.val + 1 < n) :
    ∃ w : (coxeterMatrix hA).Group,
      P.E (weylAction hA w (Pi.single i₀ 1)) = -ev n 0 - ev n 1 := by
  set vs : Fin 1 → Fin n → ℤ := fun _ => Pi.single i₀ 1
  have h0 : Reach hA P vs (fun _ => (1 : ℤ) • ev n i₀.val + (-1 : ℤ) • ev n (i₀.val + 1)) := by
    obtain ⟨w, hw⟩ := Reach.refl (hA := hA) (P := P) vs
    refine ⟨w, fun i => ?_⟩
    rw [hw i]
    simp only [vs, P.single i₀ hi₀]
    simp [sub_eq_add_neg]
  have h1 : Reach hA P vs (fun _ => (1 : ℤ) • ev n (0 + i₀.val) + (1 : ℤ) • ev n (i₀.val + 1)) := by
    simpa only [Nat.zero_add, neg_neg] using h0.neg_snd (by omega) hi₀
  have h2 : Reach hA P vs (fun _ => (1 : ℤ) • ev n 0 + (1 : ℤ) • ev n (1 + i₀.val)) := by
    simpa only [add_comm i₀.val 1] using Reach.moveDown_fst (a' := 0) i₀.val h1 (by omega) hi₀
  have h3 : Reach hA P vs (fun _ => (1 : ℤ) • ev n 0 + (1 : ℤ) • ev n 1) :=
    Reach.moveDown_snd (b' := 1) i₀.val h2 (by omega) (by omega)
  have h4 : Reach hA P vs (fun _ => (1 : ℤ) • ev n 0 + (-1 : ℤ) • ev n (0 + 1)) :=
    h3.neg_snd (by omega) (by omega)
  have h5 := h4.swap_fst_snd (a := 0) (by omega)
  have h6 := h5.neg_snd (by omega) (by omega)
  obtain ⟨w, hw⟩ := h6
  refine ⟨w, ?_⟩
  have := hw 0
  simp only [vs] at this
  rw [this]
  simp [sub_eq_add_neg]

theorem roots_cartanB {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)
    (hC : A = Spin.cartanB n) : roots hA ∅ = roots (Spin.isFiniteType_cartanB n) ∅ := by
  subst hC
  rfl

theorem exists_ht_le_cartanB {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)
    (hC : A = Spin.cartanB n) (hn : 2 ≤ n) {i₀ : Fin n} (hi₀ : i₀.val + 1 < n) :
    ∃ w : (coxeterMatrix hA).Group,
      ∀ ε ∈ roots hA ∅, ht (weylAction hA w (Pi.single i₀ 1)) ≤ ht ε := by
  subst hC
  obtain ⟨w, hw⟩ := exists_weylAction_eq_neg_ev hA (epsB n) hi₀
  refine ⟨w, fun ε hε => ?_⟩
  have hγ : Spin.toStdB n (weylAction hA w (Pi.single i₀ 1)) =
      Pi.single (⟨0, by omega⟩ : Fin n) (-1) + Pi.single (⟨1, by omega⟩ : Fin n) (-1) := by
    have : (epsB n).E (weylAction hA w (Pi.single i₀ 1)) = _ := hw
    change Spin.toStdB n _ = _ at this
    rw [this, ev_eq_single (show 0 < n by omega), ev_eq_single (show 1 < n by omega),
      Pi.single_neg, Pi.single_neg, sub_eq_add_neg]
  rw [Spin.ht_of_toStdB_eq_add n hγ]
  rw [show roots hA ∅ = roots (Spin.isFiniteType_cartanB n) ∅ from rfl, Spin.rootsB_eq] at hε
  rcases hε with ⟨i, j, s, t, hij, hs, ht, he⟩ | ⟨i, s, hs, he⟩
  · rw [Spin.ht_of_toStdB_eq_add n he]
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> push_cast <;> omega
  · rw [Spin.ht_of_toStdB_eq_single n he]
    have hi := i.isLt
    rcases hs with rfl | rfl <;> push_cast <;> omega

theorem two_mul_ht_of_stdVec {γ : Fin n → ℤ} {r : TauCeti.GLSymplecticFin.RootSubgroupIndex n}
    (hr : Symplectic.stdVec r = Symplectic.toStd n γ) :
    2 * ht γ = Symplectic.SpExtras.lv n (Symplectic.stdVec r) := by
  rw [Symplectic.SpExtras.two_mul_ht, hr]

theorem toStd_eq_of_ht_lt {γ : Fin n → ℤ} (hγ : γ ∈ roots (Symplectic.isFiniteType_cartanC n) ∅)
    (hn : 2 ≤ n) (h : 2 * ht γ < -(4 * n - 4)) :
    Symplectic.toStd n γ = -(2 • Pi.single (⟨0, by omega⟩ : Fin n) 1) := by
  rw [Symplectic.roots_eq] at hγ
  obtain ⟨r, hr⟩ := hγ
  rw [two_mul_ht_of_stdVec hr] at h
  rw [← hr]
  cases r with
  | positiveLong i =>
    simp only [Symplectic.stdVec, map_nsmul, Symplectic.SpExtras.lv_single] at h
    rw [nsmul_eq_mul] at h
    have := i.isLt
    push_cast at h
    omega
  | negativeLong i =>
    simp only [Symplectic.stdVec, map_neg, map_nsmul, Symplectic.SpExtras.lv_single] at h
    rw [nsmul_eq_mul] at h
    have hi : i.val = 0 := by push_cast at h; omega
    rw [show i = ⟨0, by omega⟩ from Fin.ext hi]
    rfl
  | difference i j hij =>
    simp only [Symplectic.stdVec, map_sub, Symplectic.SpExtras.lv_single] at h
    have := i.isLt
    have := j.isLt
    omega
  | positiveSum i j hij =>
    simp only [Symplectic.stdVec, map_add, Symplectic.SpExtras.lv_single] at h
    have := i.isLt
    have := j.isLt
    omega
  | negativeSum i j hij =>
    simp only [Symplectic.stdVec, map_neg, map_add, Symplectic.SpExtras.lv_single] at h
    have := i.isLt
    have := j.isLt
    have hij' : i.val < j.val := hij
    omega

theorem two_mul_ht_neg_ev (hn : 2 ≤ n) {γ : Fin n → ℤ}
    (hγ : Symplectic.toStd n γ = -ev n 0 - ev n 1) : 2 * ht γ = -(4 * n - 4) := by
  rw [Symplectic.SpExtras.two_mul_ht, hγ, map_sub, map_neg, ev_eq_single (show 0 < n by omega),
    ev_eq_single (show 1 < n by omega), Symplectic.SpExtras.lv_single,
    Symplectic.SpExtras.lv_single]
  push_cast
  ring

theorem eq_neg_single_of_mem_openCone_cartanC (hn : 2 ≤ n) {γ₁ δ ε : Fin n → ℤ}
    (hγ₁ : Symplectic.toStd n γ₁ = -ev n 0 - ev n 1) (hδ0 : ht δ < 0)
    (hε : ε ∈ roots (Symplectic.isFiniteType_cartanC n) ∅) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (he : ε = a • γ₁ + b • δ) : δ = -Pi.single (⟨0, by omega⟩ : Fin n) 1 := by
  have hγ₁ht := two_mul_ht_neg_ev hn hγ₁
  have hεht : 2 * ht ε = a * (2 * ht γ₁) + b * (2 * ht δ) := by
    rw [he, ht_add, ht_nsmul, ht_nsmul]
    ring
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hlt : 2 * ht ε < -(4 * n - 4) := by
    rw [hεht, hγ₁ht]
    nlinarith
  have hε' := toStd_eq_of_ht_lt hε hn hlt
  have h2 : 2 * ht ε = -(2 * (2 * n - 1)) := by
    rw [Symplectic.SpExtras.two_mul_ht, hε', map_neg, map_nsmul, Symplectic.SpExtras.lv_single,
      nsmul_eq_mul]
    push_cast
    ring
  rw [hεht, hγ₁ht] at h2
  have ha1 : (a : ℤ) = 1 := by nlinarith
  have hb1 : (b : ℤ) * ht δ = -1 := by nlinarith
  have hb2 : (b : ℤ) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hb1 with h | h
    · exact h
    · omega
  have ha2 : a = 1 := by exact_mod_cast ha1
  have hb3 : b = 1 := by exact_mod_cast hb2
  subst ha2 hb3
  rw [one_smul, one_smul] at he
  apply Symplectic.SpExtras.toStd_inj
  have hδ' : δ = ε - γ₁ := by rw [he]; abel
  rw [hδ', Symplectic.SpExtras.toStd_neg', Symplectic.SpExtras.toStd_single_of_lt' (by simp; omega)]
  rw [show Symplectic.toStd n (ε - γ₁) = Symplectic.toStd n ε - Symplectic.toStd n γ₁ from
    map_sub (toStdCLin n) ε γ₁, hε', hγ₁, ev_eq_single (show 0 < n by omega),
    ev_eq_single (show 1 < n by omega)]
  funext j
  simp only [Pi.sub_apply, Pi.neg_apply, two_nsmul, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem exists_weylAction_pair_cartanC (hn : 3 ≤ n) :
    ∃ w : (coxeterMatrix (Symplectic.isFiniteType_cartanC n)).Group,
      Symplectic.toStd n (weylAction (Symplectic.isFiniteType_cartanC n) w
          (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1)) = -ev n 0 - ev n 1 ∧
      Symplectic.toStd n (weylAction (Symplectic.isFiniteType_cartanC n) w
          (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 + Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) =
        -ev n 0 + ev n 1 := by
  set hA := Symplectic.isFiniteType_cartanC n
  set P := epsC n
  set vs : Fin 2 → Fin n → ℤ := ![Pi.single (⟨n - 2, by omega⟩ : Fin n) 1,
    Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 + Pi.single (⟨n - 1, by omega⟩ : Fin n) 1]
  have hE0 : P.E (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1) = ev n (n - 2) - ev n (n - 2 + 1) :=
    P.single _ (by simp; omega)
  have hE1 : P.E (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) = (2 : ℤ) • ev n (n - 2 + 1) := by
    rw [P.last _ (by simp; omega)]
    congr 2
    simp only
    omega
  have h0 : Reach hA P vs (fun i => ![(1 : ℤ), 1] i • ev n (n - 2) +
      ![(-1 : ℤ), 1] i • ev n (n - 2 + 1)) := by
    obtain ⟨w, hw⟩ := Reach.refl (hA := hA) (P := P) vs
    refine ⟨w, fun i => ?_⟩
    rw [hw i]
    fin_cases i
    · simp only [vs, Fin.zero_eta, Matrix.cons_val_zero, hE0]
      simp [sub_eq_add_neg]
    · simp only [vs, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, hE0, hE1]
      module
  have h1 := h0.swap_fst_snd (a := n - 2) (by omega)
  have h2 := h1.negLast (b := n - 2 + 1) (by omega) (by omega)
  have h3 := h2.swap_fst_snd (a := n - 2) (by omega)
  have h4 : Reach hA P vs (fun i => (-![(1 : ℤ), 1] i) • ev n (0 + (n - 2)) +
      ![(-1 : ℤ), 1] i • ev n (n - 2 + 1)) := by
    simpa only [Nat.zero_add] using h3
  have h5 := Reach.moveDown_fst (a' := 0) (n - 2) h4 (by omega) (by omega)
  have h6 : Reach hA P vs (fun i => (-![(1 : ℤ), 1] i) • ev n 0 +
      ![(-1 : ℤ), 1] i • ev n (1 + (n - 2))) := by
    simpa only [add_comm (n - 2) 1] using h5
  have h7 := Reach.moveDown_snd (b' := 1) (n - 2) h6 (by omega) (by omega)
  obtain ⟨w, hw⟩ := h7
  refine ⟨w, ?_, ?_⟩
  · have := hw 0
    simp only [vs, Matrix.cons_val_zero] at this
    change P.E _ = _
    rw [this]
    simp [sub_eq_add_neg]
  · have := hw 1
    simp only [vs, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    change P.E _ = _
    rw [this]
    simp

theorem exists_lowest_cartanC {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A)
    (hC : A = Symplectic.cartanC n) (hn : 3 ≤ n) {i₀ : Fin n} (hi₀ : i₀.val + 1 < n) :
    ∃ w w' : (coxeterMatrix hA).Group,
      weylAction hA w' (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1) =
        weylAction hA w (Pi.single i₀ 1) ∧
      weylAction hA w' (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 +
        Pi.single (⟨n - 1, by omega⟩ : Fin n) 1) = -Pi.single (⟨0, by omega⟩ : Fin n) 1 ∧
      ht (weylAction hA w (Pi.single i₀ 1)) < 0 ∧
      ∀ δ, ht δ < 0 → ∀ ε ∈ roots hA ∅, ∀ a b : ℕ, 0 < a → 0 < b →
        ε = a • weylAction hA w (Pi.single i₀ 1) + b • δ →
          δ = -Pi.single (⟨0, by omega⟩ : Fin n) 1 := by
  subst hC
  obtain ⟨w, hw⟩ := exists_weylAction_eq_neg_ev hA (epsC n) hi₀
  have hw' : Symplectic.toStd n (weylAction hA w (Pi.single i₀ 1)) = -ev n 0 - ev n 1 := hw
  obtain ⟨w', h1, h2⟩ := exists_weylAction_pair_cartanC hn
  refine ⟨w, w', Symplectic.SpExtras.toStd_inj (h1.trans hw'.symm), ?_, ?_, ?_⟩
  · apply Symplectic.SpExtras.toStd_inj
    rw [h2, Symplectic.SpExtras.toStd_neg', Symplectic.SpExtras.toStd_single_of_lt'
      (by simp; omega), ev_eq_single (show 0 < n by omega), ev_eq_single (show 1 < n by omega)]
    abel
  · have := two_mul_ht_neg_ev (by omega) hw'
    omega
  · intro δ hδ ε hε a b ha hb he
    exact eq_neg_single_of_mem_openCone_cartanC (by omega) hw' hδ hε ha hb he

end CFSG.Timmesfeld.ARS.ExclNS
