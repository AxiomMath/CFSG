module

public import Certificates.Kernel.A45Cls.Glue1051
public import Certificates.Kernel.A45Cls.Checks11
public import Certificates.Kernel.OmegaCY.B0
public import Certificates.Data.OmegaSplitFacts

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin
  CFSG.KC.ConjOrb Certificates.OmegaS107 CFSG.ComponentClassification.GSThmB CFSG.ABGLocalTools

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

local notation "cC" => wvA czW

local notation "BB" => CFSG.OddStandard.SmallF3.Omega.B0

local notation "BS" => Certificates.OmegaSplit.bSet

@[expose] def splX (k : ℕ) : P45 := wvA (splXW.getD k [])

theorem prep_splX : ∀ k < 4, PRep 45 6 (XZ.G k) (splX k) ∧ splX k ∈ A := by
  intro k hk
  have hl : splXW.length = 4 := rfl
  exact prep_word splBinds.1 (j := k) (by rw [hl]; exact hk)

abbrev XS : Subgroup P45 := closure (splX '' {k | k < 4})

theorem x_enum : ∃ c : ℕ → P45, (∀ i < 120, PRep 45 6 (XZ.T i) (c i) ∧ c i ∈ XS) ∧
    ∀ y ∈ XS, ∃ i < 120, c i = y := by
  obtain ⟨c, hc, hall, -⟩ := enum_A (fun k hk => (prep_splX k hk).1) XZ.cl XZ.tr (by norm_num)
    splBinds.2 XZ.k
  exact ⟨c, hc, hall⟩

theorem XS_le_A : XS ≤ A := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (prep_splX k hk).2

theorem x_norm :
    ∀ g ∈ XS, ∀ b ∈ (BB : Set P45), g * b * g⁻¹ ∈ (BB : Set P45) := by
  obtain ⟨cB, hcB, hallB⟩ := b0_enum
  refine conj_closed_A ?_
  rintro _ ⟨k, hk, rfl⟩ b hb
  obtain ⟨i, hi, rfl⟩ := hallB b hb
  have h0 := splNorm
  unfold splNormK at h0
  have h := PK.allN_iff.1 h0 k hk
  unfold nrmP at h
  obtain ⟨j, hj, e⟩ := exN_spec (PK.allN_iff.1 h i hi)
  rw [eq22_sound e (prep_splX k hk).1 (hcB i hi).1 (hcB j hj).1 (prep_splX k hk).1,
    mul_inv_cancel_right]
  exact (hcB j hj).2

theorem x_meet :
    ∀ x ∈ XS, x ∈ BB → x = 1 := by
  obtain ⟨cB, hcB, hallB⟩ := b0_enum
  obtain ⟨cX, hcX, hallX⟩ := x_enum
  intro x hx hxB
  obtain ⟨i, hi, rfl⟩ := hallX x hx
  obtain ⟨j, hj, e⟩ := hallB _ hxB
  have h0 := splMeet
  unfold splMeetK at h0
  have h := PK.allN_iff.1 h0 i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · have hT : PRep 45 6 (B0Z.T j) (cX i) := by
      rw [← e]
      exact (hcB j hj).1
    exact absurd (h.symm.trans (inPts_of hj hT (hcX i hi).1)) Bool.false_ne_true
  · exact (isIdK_iff (hcX i hi).1).1 h

theorem beq_false_of_ne' {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem comm_of_conj {x a e f : P45} (hx : x * e = f * x) (ha : a * e * a⁻¹ = f) :
    x⁻¹ * a * e = e * (x⁻¹ * a) := by
  have h1 : a * e = f * a := by
    rw [← ha]
    group
  have h2 : e * x⁻¹ = x⁻¹ * f := by
    have e' : e = x⁻¹ * (f * x) := by
      rw [← hx]
      group
    rw [e']
    group
  calc x⁻¹ * a * e = x⁻¹ * (a * e) := by group
    _ = x⁻¹ * (f * a) := by rw [h1]
    _ = x⁻¹ * f * a := by group
    _ = e * x⁻¹ * a := by rw [h2]
    _ = e * (x⁻¹ * a) := by group

theorem cent_le
    {cB : ℕ → P45} (hcB : ∀ i < 16, PRep 45 6 (B0Z.T i) (cB i) ∧
      cB i ∈ BB) (hpe : ∀ d < 5, PRep 45 6 (splEP splE d) (cB (splLn splE 4 d)))
    {y : P45} (hyA : y ∈ A) (hyz : y * z0 = z0 * y)
    (hye : ∀ j, 1 ≤ j → j < 4 → y * cB (splLn splE 4 j) = cB (splLn splE 4 j) * y) :
    y ∈ BB := by
  obtain ⟨-, hcz, hczi, -⟩ := z_conj
  have hyCZ : y ∈ CZ := mem_inf.2 ⟨hyA, mem_centralizer_singleton_iff.2 hyz⟩
  obtain ⟨i, hi, hCA⟩ := centA_eq.2.2 _ (conj_mem_centA hyCZ)
  have hu : ∀ j, j < 4 → PRep 45 6 (pcomp 45 6 (mask 6) cziP (pcomp 45 6 (mask 6) (splEP splE j)
      czP)) (cC⁻¹ * (cB (splLn splE 4 j) * cC)) := fun j hj =>
    prep_pcomp hn45 hczi (prep_pcomp hn45 (hpe j (by omega)) hcz)
  have hcm : ∀ j, 1 ≤ j → j < 4 → splCm (CA.T i) (pcomp 45 6 (mask 6) cziP (pcomp 45 6 (mask 6)
      (splEP splE j) czP)) = true := by
    intro j hj1 hj
    refine eq22_of_eq hCA (hu j hj) (hu j hj) hCA ?_
    have e := hye j hj1 hj
    calc cC⁻¹ * y * cC * (cC⁻¹ * (cB (splLn splE 4 j) * cC)) =
        cC⁻¹ * (y * cB (splLn splE 4 j)) * cC := by group
      _ = cC⁻¹ * (cB (splLn splE 4 j) * y) * cC := by rw [e]
      _ = cC⁻¹ * (cB (splLn splE 4 j) * cC) * (cC⁻¹ * y * cC) := by group
  have h0 := splCent
  unfold splCentK at h0
  simp only [strictB_eq'] at h0
  have h := PK.allN_iff.1 h0 i hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · rw [hcm 1 (by norm_num) (by norm_num), hcm 2 (by norm_num) (by norm_num),
      hcm 3 (by norm_num) (by norm_num)] at h
    exact absurd h (by decide)
  · have hP : PRep 45 6 (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP)) y := by
      have e : cC * (cC⁻¹ * y * cC * cC⁻¹) = y := by group
      have h' := prep_pcomp hn45 hcz (prep_pcomp hn45 hCA hczi)
      rwa [e] at h'
    obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hcB i hi).1) h hP
    rw [← e]
    exact (hcB m hm).2

theorem x_cover
    (a : P45) (haA : a ∈ A)
    (haN : ∀ b ∈ (BB : Set P45), a * b * a⁻¹ ∈ (BB : Set P45)) : ∃ x ∈ XS, x⁻¹ * a ∈ BB := by
  obtain ⟨cB, hcB, hallB⟩ := b0_enum
  obtain ⟨cX, hcX, -⟩ := x_enum
  have hcls := splCls
  unfold splClsK at hcls
  simp only [Bool.and_eq_true] at hcls
  obtain ⟨⟨⟨hz, hfix⟩, hall16⟩, hdist⟩ := hcls
  have hlt : ∀ d < 5, splLn splE 4 d < 16 := fun d hd => by
    have h := PK.allN_iff.1 hfix d hd
    simp only [Bool.and_eq_true] at h
    simpa using h.1
  have hpe : ∀ d < 5, PRep 45 6 (splEP splE d) (cB (splLn splE 4 d)) := fun d hd =>
    (hcB _ (hlt d hd)).1
  have hfe : ∀ d < 5, fixC (cB (splLn splE 4 d)) = 13 := fun d hd => by
    have h := PK.allN_iff.1 hfix d hd
    simp only [Bool.and_eq_true] at h
    rw [← fixK_eq (hpe d hd)]
    exact Nat.eq_of_beq_eq_true h.2
  have hne : ∀ j < 5, ∀ k < 5, j ≠ k → cB (splLn splE 4 j) ≠ cB (splLn splE 4 k) := by
    intro j hj k hk hjk e
    have h := PK.allN_iff.1 (PK.allN_iff.1 hdist j hj) k hk
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact hjk (Nat.eq_of_beq_eq_true h)
    · have hk' : PRep 45 6 (splEP splE k) (cB (splLn splE 4 j)) := by
        rw [e]
        exact hpe k hk
      exact absurd (h.symm.trans (eqP_of (hpe j hj) hk')) Bool.false_ne_true
  have himg : ∀ j < 4, ∃ d < 5, a * cB (splLn splE 4 j) * a⁻¹ = cB (splLn splE 4 d) := by
    intro j hj
    obtain ⟨i, hi, e⟩ := hallB _ (haN _ (hcB _ (hlt j (by omega))).2)
    have hf : fixK 45 6 (B0Z.T i) = 13 := by
      rw [fixK_eq (hcB i hi).1, e, fixC_conj, hfe j (by omega)]
    have h := PK.allN_iff.1 hall16 i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · rw [hf] at h
      exact absurd h (by decide)
    · obtain ⟨d, hd, hd'⟩ := exN_spec h
      refine ⟨d, hd, ?_⟩
      rw [← e, Nat.eq_of_beq_eq_true hd']
  obtain ⟨d0, hd0, e0⟩ := himg 0 (by norm_num)
  obtain ⟨d1, hd1, e1⟩ := himg 1 (by norm_num)
  obtain ⟨d2, hd2, e2⟩ := himg 2 (by norm_num)
  obtain ⟨d3, hd3, e3⟩ := himg 3 (by norm_num)
  have hdne : ∀ {j k dj dk : ℕ}, j < 5 → k < 5 → j ≠ k →
      a * cB (splLn splE 4 j) * a⁻¹ = cB (splLn splE 4 dj) →
      a * cB (splLn splE 4 k) * a⁻¹ = cB (splLn splE 4 dk) → dj ≠ dk := by
    intro j k dj dk hj hk hjk ej ek hd
    apply hne j hj k hk hjk
    rw [← hd] at ek
    have h := ej.trans ek.symm
    simpa using h
  have h01 := hdne (by norm_num) (by norm_num) (by norm_num) e0 e1
  have h02 := hdne (by norm_num) (by norm_num) (by norm_num) e0 e2
  have h03 := hdne (by norm_num) (by norm_num) (by norm_num) e0 e3
  have h12 := hdne (by norm_num) (by norm_num) (by norm_num) e1 e2
  have h13 := hdne (by norm_num) (by norm_num) (by norm_num) e1 e3
  have h23 := hdne (by norm_num) (by norm_num) (by norm_num) e2 e3
  set p := 125 * d0 + 25 * d1 + 5 * d2 + d3 with hp
  have hp625 : p < 625 := by omega
  have q0 : p / 125 = d0 := by omega
  have q1 : p / 25 % 5 = d1 := by omega
  have q2 : p / 5 % 5 = d2 := by omega
  have q3 : p % 5 = d3 := by omega
  have hdist' : splDist p = true := by
    unfold splDist
    rw [q0, q1, q2, q3, beq_false_of_ne' h01, beq_false_of_ne' h02, beq_false_of_ne' h03,
      beq_false_of_ne' h12, beq_false_of_ne' h13, beq_false_of_ne' h23]
    rfl
  have h0 := splCov
  unfold splCovK at h0
  have h := PK.allN_iff.1 h0 p hp625
  rw [hdist'] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨hlt120, hact⟩ := h
  have hl : splLn splW 7 p < 120 := by simpa using hlt120
  set x := cX (splLn splW 7 p)
  have hxP : PRep 45 6 (XZ.T (splLn splW 7 p)) x := (hcX _ hl).1
  unfold splActK at hact
  rw [q0, q1, q2, q3] at hact
  simp only [Bool.and_eq_true] at hact
  obtain ⟨⟨⟨a0, a1⟩, a2⟩, a3⟩ := hact
  have c0 := comm_of_conj (eq22_sound a0 hxP (hpe 0 (by norm_num)) (hpe d0 hd0) hxP) e0
  have c1 := comm_of_conj (eq22_sound a1 hxP (hpe 1 (by norm_num)) (hpe d1 hd1) hxP) e1
  have c2 := comm_of_conj (eq22_sound a2 hxP (hpe 2 (by norm_num)) (hpe d2 hd2) hxP) e2
  have c3 := comm_of_conj (eq22_sound a3 hxP (hpe 3 (by norm_num)) (hpe d3 hd3) hxP) e3
  have hz0 : cB (splLn splE 4 0) = z0 := eqP_sound hz (hpe 0 (by norm_num)) prep_z
  rw [hz0] at c0
  refine ⟨x, (hcX _ hl).2, cent_le hcB hpe (mul_mem (inv_mem (XS_le_A (hcX _ hl).2)) haA) c0 ?_⟩
  intro j hj1 hj
  interval_cases j
  · exact c1
  · exact c2
  · exact c3

theorem factsSplit :
    Certificates.OmegaSplit.Facts := by
  have hS : ∀ g : P45, g ∈ Certificates.OmegaSplit.bSet ↔ g ∈ BB := fun g =>
    CFSG.OddStandard.SmallF3.Omega.mem_B0_iff.symm
  refine ⟨XS, fun x hx => mem_inf.2 ⟨XS_le_A hx, ?_⟩, fun x hx hxB => x_meet x hx ((hS x).1 hxB),
    fun a ha => ?_⟩
  · change ∀ h, h ∈ BS ↔ x * h * x⁻¹ ∈ BS
    intro h
    rw [hS, hS]
    constructor
    · exact x_norm x hx h
    · intro h'
      have h2 := x_norm x⁻¹ (inv_mem hx) _ h'
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [e] at h2
  · obtain ⟨haA, haN⟩ := mem_inf.1 ha
    have haN' : ∀ h, h ∈ BS ↔ a * h * a⁻¹ ∈ BS := haN
    have hN : ∀ b ∈ (BB : Set P45), a * b * a⁻¹ ∈ (BB : Set P45) := fun b hb =>
      (hS _).1 ((haN' b).1 ((hS b).2 hb))
    obtain ⟨x, hx, hy⟩ := x_cover a haA hN
    exact ⟨x, hx, x⁻¹ * a, (hS _).2 hy, (mul_inv_cancel_left x a).symm⟩

end CertificateChecks.KernelA45

end
