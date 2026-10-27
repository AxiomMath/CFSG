module

public import CFSG.OddTranspositions.SevenThreeTransitive

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_conj_u_of_mem {u : G} (hu2 : u * u = 1) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {s : G} (hsA : s ∈ A) (hs2 : s * s = 1) :
    Commute (s * u * s) u := by
  let b : G := u * s * u
  have hb : b = u * s * u := rfl
  have hbB : b ∈ B := by rw [hb]; exact hAB s hsA
  have hbs : Commute s b := by rw [hb]; exact hcommAB s hsA _ hbB
  have hubu : u * b * u = s := by
    rw [hb]
    calc u * (u * s * u) * u = (u * u) * s * (u * u) := by group
      _ = s := by rw [hu2, one_mul, mul_one]
  have hsueq : s * u = u * b := by
    rw [hb]
    calc s * u = (u * u) * s * u := by rw [hu2, one_mul]
      _ = u * (u * s * u) := by group
  have huseq : u * s = b * u := by
    rw [hb]
    calc u * s = u * s * (u * u) := by rw [hu2, mul_one]
      _ = (u * s * u) * u := by group
  have h1 : s * u * s * u = s * b := by
    calc s * u * s * u = (s * u) * (s * u) := by group
      _ = (u * b) * (u * b) := by rw [hsueq]
      _ = (u * b * u) * b := by group
      _ = s * b := by rw [hubu]
  have h2 : u * (s * u * s) = b * s := by
    calc u * (s * u * s) = (u * s) * (u * s) := by group
      _ = (b * u) * (b * u) := by rw [huseq]
      _ = b * (u * b * u) := by group
      _ = b * s := by rw [hubu]
  rw [commute_iff_eq]
  calc s * u * s * u = s * b := h1
    _ = b * s := hbs.eq
    _ = u * (s * u * s) := h2.symm

theorem orderOf_conj_mul_conj {u : G} (hu2 : u * u = 1) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hdisj : A ⊓ B = ⊥)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {s s' : G} (hsA : s ∈ A) (hs'A : s' ∈ A) :
    orderOf ((s * u * s) * (s' * u * s')) = orderOf (s * s') := by
  have h1 : s * u = u * (u * s * u) := by
    calc s * u = (u * u) * s * u := by rw [hu2, one_mul]
      _ = u * (u * s * u) := by group
  have h2 : u * s' = (u * s' * u) * u := by
    calc u * s' = u * s' * (u * u) := by rw [hu2, mul_one]
      _ = (u * s' * u) * u := by group
  have hbb : (u * s * u) * (u * s' * u) = u * (s * s') * u := by
    calc (u * s * u) * (u * s' * u) = u * s * (u * u) * s' * u := by group
      _ = u * s * s' * u := by rw [hu2, mul_one]
      _ = u * (s * s') * u := by group
  have hbs : Commute s (u * s * u) := hcommAB s hsA _ (hAB s hsA)
  have hbs' : Commute s (u * s' * u) := hcommAB s hsA _ (hAB s' hs'A)
  have hs'b : Commute s' (u * s * u) := hcommAB s' hs'A _ (hAB s hsA)
  have hs'b' : Commute s' (u * s' * u) := hcommAB s' hs'A _ (hAB s' hs'A)
  have hb_ss' : Commute (u * s * u) (s * s') := (hbs.mul_left hs'b).symm
  have hb'_ss' : Commute (u * s' * u) (s * s') := (hbs'.mul_left hs'b').symm
  have hxt : (s * u * s) * (s' * u * s') = (s * s') * (u * (s * s') * u) := by
    calc (s * u * s) * (s' * u * s') = (s * u) * (s * s') * (u * s') := by group
      _ = (u * (u * s * u)) * (s * s') * ((u * s' * u) * u) := by
            conv_lhs => rw [h1, h2]
      _ = u * ((u * s * u) * (s * s') * (u * s' * u)) * u := by group
      _ = u * ((s * s') * ((u * s * u) * (u * s' * u))) * u := by
            rw [hb_ss'.eq]
            group
      _ = u * ((s * s') * (u * (s * s') * u)) * u := by
            rw [hbb]
      _ = (s * s') * (u * (s * s') * u) := by
            let r : G := s * s'
            have hcomm_r : Commute r (u * r * u) :=
              hcommAB r (A.mul_mem hsA hs'A) _ (hAB r (A.mul_mem hsA hs'A))
            have h1 : MulAut.conj u r = u * r * u := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
            have h2 : MulAut.conj u (u * r * u) = r := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
              calc u * (u * r * u) * u = (u * u) * r * (u * u) := by group
                _ = r := by rw [hu2, one_mul, mul_one]
            have hconj : MulAut.conj u (r * (u * r * u)) = r * (u * r * u) := by
              rw [map_mul, h1, h2]
              exact hcomm_r.symm.eq
            have hu : (MulAut.conj u) (r * (u * r * u)) = u * (r * (u * r * u)) * u := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
            rw [hu] at hconj
            exact hconj
  rw [hxt]
  let r : G := s * s'
  have hrA : r ∈ A := A.mul_mem hsA hs'A
  have hrB : u * r * u ∈ B := hAB r hrA
  have hcomm : Commute r (u * r * u) := hcommAB r hrA _ hrB
  have hconjpow : (u * r * u) ^ orderOf r = 1 := by
    have h := conj_pow (a := u) (b := r) (i := orderOf r)
    rw [pow_orderOf_eq_one] at h
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    simpa [hui, hu2] using h
  have hdvd1 : orderOf (r * (u * r * u)) ∣ orderOf r := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [hcomm.mul_pow (orderOf r), pow_orderOf_eq_one, hconjpow, mul_one]
  have hdvd2 : orderOf r ∣ orderOf (r * (u * r * u)) := by
    set d := orderOf (r * (u * r * u)) with hd
    have hpow : (r * (u * r * u)) ^ d = 1 := pow_orderOf_eq_one _
    have hsplit : r ^ d * (u * r * u) ^ d = 1 := by
      rwa [hcomm.mul_pow d] at hpow
    have hmem : r ^ d ∈ A ⊓ B := by
      constructor
      · exact A.pow_mem hrA d
      · have heq : r ^ d = ((u * r * u) ^ d)⁻¹ := eq_inv_of_mul_eq_one_left hsplit
        rw [heq]
        exact B.inv_mem (B.pow_mem hrB d)
    have hbot : r ^ d = 1 := by
      have := hmem
      rw [hdisj] at this
      simpa using this
    exact orderOf_dvd_iff_pow_eq_one.mpr hbot
  exact Nat.dvd_antisymm hdvd1 hdvd2

theorem conj_mul_conj_eq {u : G} (hu2 : u * u = 1) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {s s' : G} (hsA : s ∈ A) (hs'A : s' ∈ A) :
    (s * u * s) * (s' * u * s') = (s * s') * (u * (s * s') * u) := by
  have h1 : s * u = u * (u * s * u) := by
    calc s * u = (u * u) * s * u := by rw [hu2, one_mul]
      _ = u * (u * s * u) := by group
  have h2 : u * s' = (u * s' * u) * u := by
    calc u * s' = u * s' * (u * u) := by rw [hu2, mul_one]
      _ = (u * s' * u) * u := by group
  have hbb : (u * s * u) * (u * s' * u) = u * (s * s') * u := by
    calc (u * s * u) * (u * s' * u) = u * s * (u * u) * s' * u := by group
      _ = u * s * s' * u := by rw [hu2, mul_one]
      _ = u * (s * s') * u := by group
  have hbs : Commute s (u * s * u) := hcommAB s hsA _ (hAB s hsA)
  have hbs' : Commute s (u * s' * u) := hcommAB s hsA _ (hAB s' hs'A)
  have hs'b : Commute s' (u * s * u) := hcommAB s' hs'A _ (hAB s hsA)
  have hs'b' : Commute s' (u * s' * u) := hcommAB s' hs'A _ (hAB s' hs'A)
  have hb_ss' : Commute (u * s * u) (s * s') := (hbs.mul_left hs'b).symm
  have hb'_ss' : Commute (u * s' * u) (s * s') := (hbs'.mul_left hs'b').symm
  have hxt : (s * u * s) * (s' * u * s') = (s * s') * (u * (s * s') * u) := by
    calc (s * u * s) * (s' * u * s') = (s * u) * (s * s') * (u * s') := by group
      _ = (u * (u * s * u)) * (s * s') * ((u * s' * u) * u) := by
            conv_lhs => rw [h1, h2]
      _ = u * ((u * s * u) * (s * s') * (u * s' * u)) * u := by group
      _ = u * ((s * s') * ((u * s * u) * (u * s' * u))) * u := by
            rw [hb_ss'.eq]
            group
      _ = u * ((s * s') * (u * (s * s') * u)) * u := by
            rw [hbb]
      _ = (s * s') * (u * (s * s') * u) := by
            let r : G := s * s'
            have hcomm_r : Commute r (u * r * u) :=
              hcommAB r (A.mul_mem hsA hs'A) _ (hAB r (A.mul_mem hsA hs'A))
            have h1 : MulAut.conj u r = u * r * u := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
            have h2 : MulAut.conj u (u * r * u) = r := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
              calc u * (u * r * u) * u = (u * u) * r * (u * u) := by group
                _ = r := by rw [hu2, one_mul, mul_one]
            have hconj : MulAut.conj u (r * (u * r * u)) = r * (u * r * u) := by
              rw [map_mul, h1, h2]
              exact hcomm_r.symm.eq
            have hu : (MulAut.conj u) (r * (u * r * u)) = u * (r * (u * r * u)) * u := by
              rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right hu2]
            rw [hu] at hconj
            exact hconj
  exact hxt

theorem conj_mul_conj_mul_conj {u : G} (hu2 : u * u = 1) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {s₁ s₂ s₃ : G} (hs1A : s₁ ∈ A) (hs2A : s₂ ∈ A) (hs3A : s₃ ∈ A) :
    (s₁ * u * s₁) * (s₂ * u * s₂) * (s₃ * u * s₃) =
      (s₁ * s₂ * s₃) * (u * (s₁ * s₂ * s₃) * u) * u := by
  let r : G := s₁ * s₂
  have hrA : r ∈ A := A.mul_mem hs1A hs2A
  have hcomm_r3 : Commute (u * r * u) s₃ := (hcommAB s₃ hs3A _ (hAB r hrA)).symm
  have hxt : (s₁ * u * s₁) * (s₂ * u * s₂) = r * (u * r * u) :=
    conj_mul_conj_eq (s := s₁) (s' := s₂) hu2 hAB hcommAB hs1A hs2A
  have h1 : (u * r * u) * u = u * r := by
    calc (u * r * u) * u = u * r * (u * u) := by group
      _ = u * r := by rw [hu2, mul_one]
  have h2 : u * (r * s₃) * u * u = u * r * s₃ := by
    calc u * (r * s₃) * u * u = u * r * s₃ * (u * u) := by group
      _ = u * r * s₃ := by rw [hu2, mul_one]
  calc (s₁ * u * s₁) * (s₂ * u * s₂) * (s₃ * u * s₃)
      = (r * (u * r * u)) * (s₃ * u * s₃) := by rw [hxt]
    _ = r * ((u * r * u) * s₃) * u * s₃ := by group
    _ = r * (s₃ * (u * r * u)) * u * s₃ := by rw [hcomm_r3.eq]
    _ = r * s₃ * (u * r * u) * u * s₃ := by group
    _ = r * s₃ * ((u * r * u) * u) * s₃ := by group
    _ = r * s₃ * (u * r) * s₃ := by rw [h1]
    _ = r * s₃ * u * r * s₃ := by group
    _ = (r * s₃) * (u * r * s₃) := by group
    _ = (r * s₃) * (u * (r * s₃) * u) * u := by
          rw [← h2]
          group
    _ = (s₁ * s₂ * s₃) * (u * (s₁ * s₂ * s₃) * u) * u := rfl

theorem orderOf_mul_conj_self {u : G} (hu2 : u * u = 1) {A B : Subgroup G}
    (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hdisj : A ⊓ B = ⊥)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {r : G} (hrA : r ∈ A) :
    orderOf (r * (u * r * u)) = orderOf r := by
  have hrB : u * r * u ∈ B := hAB r hrA
  have hcomm : Commute r (u * r * u) := hcommAB r hrA _ hrB
  have hconjpow : (u * r * u) ^ orderOf r = 1 := by
    have h := conj_pow (a := u) (b := r) (i := orderOf r)
    rw [pow_orderOf_eq_one] at h
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    simpa [hui, hu2] using h
  have hdvd1 : orderOf (r * (u * r * u)) ∣ orderOf r := by
    rw [orderOf_dvd_iff_pow_eq_one]
    rw [hcomm.mul_pow (orderOf r), pow_orderOf_eq_one, hconjpow, mul_one]
  have hdvd2 : orderOf r ∣ orderOf (r * (u * r * u)) := by
    set d := orderOf (r * (u * r * u)) with hd
    have hpow : (r * (u * r * u)) ^ d = 1 := pow_orderOf_eq_one _
    have hsplit : r ^ d * (u * r * u) ^ d = 1 := by
      rwa [hcomm.mul_pow d] at hpow
    have hmem : r ^ d ∈ A ⊓ B := by
      constructor
      · exact A.pow_mem hrA d
      · have heq : r ^ d = ((u * r * u) ^ d)⁻¹ := eq_inv_of_mul_eq_one_left hsplit
        rw [heq]
        exact B.inv_mem (B.pow_mem hrB d)
    have hbot : r ^ d = 1 := by
      have := hmem
      rw [hdisj] at this
      simpa using this
    exact orderOf_dvd_iff_pow_eq_one.mpr hbot
  exact Nat.dvd_antisymm hdvd1 hdvd2

theorem commute_u_mul_conj {u g : G} (hu2 : u * u = 1)
    (hcomm : Commute g (u * g * u)) : Commute u (g * (u * g * u)) := by
  have h1 : u * g = (u * g * u) * u := by
    calc u * g = u * g * (u * u) := by rw [hu2, mul_one]
      _ = (u * g * u) * u := by group
  have h2 : u * (u * g * u) = g * u := by
    calc u * (u * g * u) = (u * u) * g * u := by group
      _ = g * u := by rw [hu2, one_mul]
  rw [commute_iff_eq]
  calc u * (g * (u * g * u)) = (u * g) * (u * g * u) := by group
    _ = ((u * g * u) * u) * (u * g * u) := by nth_rewrite 1 [h1]; rfl
    _ = (u * g * u) * (u * (u * g * u)) := by group
    _ = (u * g * u) * (g * u) := by rw [h2]
    _ = ((u * g * u) * g) * u := by group
    _ = (g * (u * g * u)) * u := by rw [← hcomm.eq]

theorem not_localSecond_of_wreath_data (hS : Setup G D) {u : G} (hu : u ∈ D)
    {A B : Subgroup G} (hAB : ∀ a ∈ A, u * a * u ∈ B)
    (hdisj : A ⊓ B = ⊥)
    (hcommAB : ∀ a ∈ A, ∀ b ∈ B, Commute a b)
    {s₁ s₂ s₃ : G} (hs1A : s₁ ∈ A) (hs2A : s₂ ∈ A) (hs3A : s₃ ∈ A)
    (hs1 : s₁ * s₁ = 1) (hs2 : s₂ * s₂ = 1) (hs3 : s₃ * s₃ = 1)
    (hs12 : Commute s₁ s₂) (hne12 : s₁ ≠ s₂)
    (hodd13 : Odd (orderOf (s₁ * s₃))) (hgt13 : 1 < orderOf (s₁ * s₃))
    (hodd23 : Odd (orderOf (s₂ * s₃))) (hgt23 : 1 < orderOf (s₂ * s₃))
    (hoddg : Odd (orderOf (s₁ * s₂ * s₃))) (hgtg : 1 < orderOf (s₁ * s₂ * s₃)) :
    ¬ LocalSecond D := by
  intro hL
  let x : G := s₁ * u * s₁
  let y : G := s₃ * u * s₃
  let t : G := s₂ * u * s₂
  let g : G := s₁ * s₂ * s₃
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hgA : g ∈ A := A.mul_mem (A.mul_mem hs1A hs2A) hs3A
  have hxD : x ∈ D := by
    simpa [x, inv_eq_of_mul_eq_one_right hs1] using hS.normal s₁ u hu
  have hyD : y ∈ D := by
    simpa [y, inv_eq_of_mul_eq_one_right hs3] using hS.normal s₃ u hu
  have htD : t ∈ D := by
    simpa [t, inv_eq_of_mul_eq_one_right hs2] using hS.normal s₂ u hu
  have hxu : Commute x u := commute_conj_u_of_mem hu2 hAB hcommAB hs1A hs1
  have hyu : Commute y u := commute_conj_u_of_mem hu2 hAB hcommAB hs3A hs3
  have htu : Commute t u := commute_conj_u_of_mem hu2 hAB hcommAB hs2A hs2
  have hxt_ord : orderOf (x * t) = 2 := by
    rw [show x * t = (s₁ * u * s₁) * (s₂ * u * s₂) from rfl,
      orderOf_conj_mul_conj hu2 hAB hdisj hcommAB hs1A hs2A]
    have hsq : (s₁ * s₂) * (s₁ * s₂) = 1 := by
      calc (s₁ * s₂) * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
        _ = s₁ * (s₁ * s₂) * s₂ := by rw [← hs12.eq]
        _ = (s₁ * s₁) * (s₂ * s₂) := by group
        _ = 1 := by rw [hs1, hs2, one_mul]
    have hne : s₁ * s₂ ≠ 1 := by
      intro h
      apply hne12
      have h' := congrArg (fun z => z * s₂) h
      simpa [mul_assoc, hs2] using h'
    exact orderOf_eq_prime (p := 2) (by simpa [pow_two] using hsq) hne
  have hxy_ord : orderOf (x * y) = orderOf (s₁ * s₃) :=
    orderOf_conj_mul_conj (s := s₁) (s' := s₃) hu2 hAB hdisj hcommAB hs1A hs3A
  have hty_ord : orderOf (t * y) = orderOf (s₂ * s₃) :=
    orderOf_conj_mul_conj (s := s₂) (s' := s₃) hu2 hAB hdisj hcommAB hs2A hs3A
  have hxt_comm : Commute x t := by
    rw [commute_iff_eq]
    have hsq : (x * t) * (x * t) = 1 := by
      have h := pow_orderOf_eq_one (x * t)
      rw [hxt_ord] at h
      simpa [pow_two] using h
    have hinv : x * t = (x * t)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hS.oddT.mul_self_eq_one hxD)
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hS.oddT.mul_self_eq_one htD)
    calc x * t = (x * t)⁻¹ := hinv
      _ = t⁻¹ * x⁻¹ := mul_inv_rev x t
      _ = t * x := by rw [hxi, hti]
  have hne_xt : x ≠ t := by
    intro h
    have h1 : orderOf (x * t) = 1 := by
      rw [h, hS.oddT.mul_self_eq_one htD]
      simp
    rw [hxt_ord] at h1
    exact absurd h1 (by norm_num)
  have hnc_xy : ¬ Commute x y := by
    intro hc
    have hsq : (x * y) * (x * y) = 1 := by
      rw [commute_iff_eq] at hc
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hc]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hS.oddT.mul_self_eq_one hxD, hS.oddT.mul_self_eq_one hyD, mul_one]
    have hdvd : orderOf (x * y) ∣ 2 := by
      rw [← pow_two] at hsq
      exact orderOf_dvd_of_pow_eq_one hsq
    rw [hxy_ord] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · rw [h] at hgt13
      omega
    · rw [h] at hodd13
      obtain ⟨k, hk⟩ := hodd13
      omega
  have hnc_ty : ¬ Commute t y := by
    intro hc
    have hsq : (t * y) * (t * y) = 1 := by
      rw [commute_iff_eq] at hc
      calc (t * y) * (t * y) = t * (y * t) * y := by group
        _ = t * (t * y) * y := by rw [← hc]
        _ = (t * t) * (y * y) := by group
        _ = 1 := by rw [hS.oddT.mul_self_eq_one htD, hS.oddT.mul_self_eq_one hyD, mul_one]
    have hdvd : orderOf (t * y) ∣ 2 := by
      rw [← pow_two] at hsq
      exact orderOf_dvd_of_pow_eq_one hsq
    rw [hty_ord] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · rw [h] at hgt23
      omega
    · rw [h] at hodd23
      obtain ⟨k, hk⟩ := hodd23
      omega
  have htri : IsTriangle D x y t :=
    ⟨hxD, htD, hyD, hne_xt, hxt_comm, hnc_xy, hnc_ty⟩
  have hord3 : x * t * y = g * (u * g * u) * u :=
    conj_mul_conj_mul_conj hu2 hAB hcommAB hs1A hs2A hs3A
  have hcomm_g : Commute g (u * g * u) := hcommAB g hgA _ (hAB g hgA)
  have hu_gg : Commute u (g * (u * g * u)) := commute_u_mul_conj hu2 hcomm_g
  have hsq_eq : (x * t * y) ^ 2 = (g * (u * g * u)) ^ 2 := by
    rw [hord3]
    calc (g * (u * g * u) * u) ^ 2 = (g * (u * g * u)) ^ 2 * u ^ 2 :=
          (hu_gg.symm).mul_pow 2
      _ = (g * (u * g * u)) ^ 2 := by
          rw [show u ^ 2 = 1 by rw [pow_two, hu2], mul_one]
  have hord_g : orderOf (g * (u * g * u)) = orderOf g :=
    orderOf_mul_conj_self hu2 hAB hdisj hcommAB hgA
  have hsq_ord : orderOf ((x * t * y) ^ 2) = orderOf g := by
    rw [hsq_eq, orderOf_pow, hord_g]
    have hcop : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.mpr hoddg
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one]
  have hnot4 : orderOf (x * t * y) ≠ 4 := by
    intro h4
    have hpow4 : (x * t * y) ^ 4 = 1 := by
      rw [← h4]
      exact pow_orderOf_eq_one _
    have h2sq : ((x * t * y) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      simpa using hpow4
    have hdvd : orderOf ((x * t * y) ^ 2) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one h2sq
    rw [hsq_ord] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · rw [h] at hgtg
      omega
    · rw [h] at hoddg
      obtain ⟨k, hk⟩ := hoddg
      omega
  exact hnot4 (hL u hu x y t hxu hyu htu htri)

end CFSG.OddTranspositions





