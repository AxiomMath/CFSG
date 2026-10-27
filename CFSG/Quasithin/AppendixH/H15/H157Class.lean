module

public import CFSG.Quasithin.AppendixH.H15.H157Basic
public import Certificates.Certificate490013

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.Code

theorem exists_conj_fixCnt {T : PT 24} [Fact (T.check = true)]
    (hT : T.allOK okAut = true) {p : ℕ} [Fact p.Prime]
    (hsyl : Nat.card T.Elem = p ^ (Nat.card ↥AutPerm).factorization p)
    {mats : Array (List ℕ)} (hmats : mats = matsOf11 T) {y : ↥AutPerm} (hy : orderOf y = p) :
    ∃ (c : ↥AutPerm) (s : T.Elem), s ≠ 1 ∧
      c * y * c⁻¹ = T.toSub AutPerm (T.mem_autPerm (ok := okAut) (fun _ _ h => h) hT) s ∧
      Nat.card ↥(fixW y) = fixCnt mats s := by
  set φ : T.Elem →* ↥AutPerm :=
    T.toSub AutPerm (T.mem_autPerm (ok := okAut) (fun _ _ h => h) hT) with hφ
  obtain ⟨g, s, hs1, hc⟩ := exists_conj_of_prime φ
    (T.toSub_injective AutPerm (T.mem_autPerm (ok := okAut) (fun _ _ h => h) hT)) hsyl hy
  have hcard : Nat.card ↥(fixW (φ s)) = fixCnt mats s := by
    have hfix : fixMasks 11 (fun q m => actM (mats[q.idx]!) m) [s]
        = (List.range (2 ^ 11)).filter (fun m => actM (mats[s.idx]!) m == m) := by
      simp [fixMasks]
    have hP : ∀ m < 2 ^ 11, (MaskCoords.std 11).vm m ∈ fixW (φ s) ↔
        (actM (mats[s.idx]!) m == m) = true := by
      intro m hm
      have hact : rhoM24 (φ s) (toW 11 m) = toW 11 (actM (mats[s.idx]!) m) := by
        rw [actM_mats11 T hmats s hm]
        exact rho11_toW AutPerm le_rfl (φ s)
          (T.hasArr_toSub AutPerm (T.mem_autPerm (ok := okAut) (fun _ _ h => h) hT) s) m
      change toW 11 m ∈ fixW (φ s) ↔ (actM (mats[s.idx]!) m == m) = true
      rw [mem_fixW, hact, beq_iff_eq]
      constructor
      · intro h
        exact toW_inj (by rw [actM_mats11 T hmats s hm]; exact act11_lt _ _) hm h
      · intro h
        rw [h]
    have h := (MaskCoords.std 11).card_eq (fixW (φ s))
      (fun m => actM (mats[s.idx]!) m == m) hP
    rw [h, fixCnt, hfix]
  refine ⟨g, s, hs1, hc, ?_⟩
  have hcy := card_fixW_conj g y
  rw [hc] at hcy
  exact hcy.symm.trans hcard

theorem classify_odd
    (y : ↥AutPerm)
    (hp : (orderOf y).Prime)
    (hodd : Odd (orderOf y)) (h : 16 ≤ Nat.card ↥(fixW y)) : Is3A y := by
  have hcls := Certificates.certificate490013
  have hdvd : orderOf y ∣ 244823040 := by
    rw [← card_AutPerm]
    exact orderOf_dvd_natCard y
  have hp2 : orderOf y ≠ 2 := by
    intro h2
    rw [h2] at hodd
    norm_num at hodd
  rcases prime_dvd_m24 hp hdvd hp2 with h3 | h5 | h7 | h11 | h23
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hsyl : Nat.card T24s3.Elem = 3 ^ (Nat.card ↥AutPerm).factorization 3 :=
      card_T24sp (T := T24s3) (p := 3) (n := 3) (by norm_num) T24s3_ok.2.1
        (by norm_num : (244823040 : ℕ) = 3 ^ 3 * 9067520) (by norm_num)
    obtain ⟨c, s, hs1, hc, hcard⟩ :=
      exists_conj_fixCnt (T := T24s3) T24s3_ok.2.2 (mats := mats24s3) hsyl rfl h3
    have hcount : 16 ≤ fixCnt mats24s3 s := by rw [← hcard]; exact h
    obtain ⟨hA, -, hAok, hAconj⟩ := hcls.1 s hs1 hcount
    obtain ⟨σh, hσhA, hσh⟩ := exists_of_inAutOK hAok
    set a : ↥AutPerm := ⟨σh, hσhA⟩ with ha
    set φ3 : T24s3.Elem →* ↥AutPerm :=
      T24s3.toSub AutPerm (T24s3.mem_autPerm (ok := okAut) (fun _ _ h => h) T24s3_ok.2.2) with hφ3
    have hcφ : c * y * c⁻¹ = φ3 s := hc
    have haφ : a * φ3 s * a⁻¹ = tA := by
      apply Subtype.ext
      have h0 : HasArr ((a * φ3 s * a⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) tStd := by
        have hcA : ∀ i < 24, hA[(T24s3.arr s)[i]!]! = tStd[hA[i]!]! := by
          intro i hi
          have := List.all_eq_true.1 hAconj i (List.mem_range.2 hi)
          simpa using this
        have hs : HasArr ((φ3 s : ↥AutPerm) : Equiv.Perm (Fin 24)) (T24s3.arr s) :=
          T24s3.hasArr_toSub AutPerm
            (T24s3.mem_autPerm (ok := okAut) (fun _ _ h => h) T24s3_ok.2.2) s
        intro j
        have hj : σh (σh⁻¹ j) = j := by simp
        have hσ0j : ((a * φ3 s * a⁻¹ : ↥AutPerm) : Equiv.Perm (Fin 24)) j =
            σh (((φ3 s : ↥AutPerm) : Equiv.Perm (Fin 24)) (σh⁻¹ j)) := rfl
        rw [hσ0j, hσh, hs, hcA _ (σh⁻¹ j).2, ← hσh (σh⁻¹ j), hj]
      exact CFSG.Quasithin.H.ModChk.perm_eq_of_hasArr h0 CFSG.Quasithin.H153.hasArr_tP
    refine ⟨a * c, ?_⟩
    have hgroup : (a * c) * y * (a * c)⁻¹ = a * (c * y * c⁻¹) * a⁻¹ := by group
    rw [hgroup, hcφ, haφ]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hsyl : Nat.card T24s5.Elem = 5 ^ (Nat.card ↥AutPerm).factorization 5 :=
      card_T24sp (T := T24s5) (p := 5) (n := 1) (by norm_num) T24s5_ok.2.1
        (by norm_num : (244823040 : ℕ) = 5 ^ 1 * 48964608) (by norm_num)
    obtain ⟨c, s, hs1, -, hcard⟩ :=
      exists_conj_fixCnt (T := T24s5) T24s5_ok.2.2 (mats := mats24s5) hsyl rfl h5
    have hlt := hcls.2.1 s hs1
    rw [hcard] at h
    omega
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hsyl : Nat.card T24s7.Elem = 7 ^ (Nat.card ↥AutPerm).factorization 7 :=
      card_T24sp (T := T24s7) (p := 7) (n := 1) (by norm_num) T24s7_ok.2.1
        (by norm_num : (244823040 : ℕ) = 7 ^ 1 * 34974720) (by norm_num)
    obtain ⟨c, s, hs1, -, hcard⟩ :=
      exists_conj_fixCnt (T := T24s7) T24s7_ok.2.2 (mats := mats24s7) hsyl rfl h7
    have hlt := hcls.2.2.1 s hs1
    rw [hcard] at h
    omega
  · haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have hsyl : Nat.card T24s11.Elem = 11 ^ (Nat.card ↥AutPerm).factorization 11 :=
      card_T24sp (T := T24s11) (p := 11) (n := 1) (by norm_num) T24s11_ok.2.1
        (by norm_num : (244823040 : ℕ) = 11 ^ 1 * 22256640) (by norm_num)
    obtain ⟨c, s, hs1, -, hcard⟩ :=
      exists_conj_fixCnt (T := T24s11) T24s11_ok.2.2 (mats := mats24s11) hsyl rfl h11
    have hlt := hcls.2.2.2.1 s hs1
    rw [hcard] at h
    omega
  · haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    have hsyl : Nat.card T24s23.Elem = 23 ^ (Nat.card ↥AutPerm).factorization 23 :=
      card_T24sp (T := T24s23) (p := 23) (n := 1) (by norm_num) T24s23_ok.2.1
        (by norm_num : (244823040 : ℕ) = 23 ^ 1 * 10644480) (by norm_num)
    obtain ⟨c, s, hs1, -, hcard⟩ :=
      exists_conj_fixCnt (T := T24s23) T24s23_ok.2.2 (mats := mats24s23) hsyl rfl h23
    have hlt := hcls.2.2.2.2 s hs1
    rw [hcard] at h
    omega

end CFSG.ASVolI.AppH.H157
