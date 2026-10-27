module

public import CFSG.Monster.GMS.S37Two
public import CFSG.Monster.GMS.S4Defs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic S36Lines

section Dvd

variable {G : Type*} [Group G]

@[expose] def OddTypeDvd (a z₀ : G) : Prop :=
  ∀ x y : G, ∀ k : Fin 3, IsConj a x → y ∈ oddNbr a z₀ x → OddNbrType z₀ x y k →
    oddTypeStab k ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})

theorem OddTypeOrders.toDvd {a z₀ : G} (h : OddTypeOrders a z₀) : OddTypeDvd a z₀ :=
  fun x y k hx hy hk => (h x y k hx hy hk).symm ▸ dvd_refl _

end Dvd

namespace S37

section Arith

theorem arith_line_big (n c : ℕ) (hc : 2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 ≤ c)
    (h : c * tableVOrderB ≤ n * twoBabyOrder) : 243968 < n := by
  unfold tableVOrderB twoBabyOrder at h
  omega

theorem oddTypeStab_two : oddTypeStab 2 = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 := rfl

theorem oddTypeStab_one : oddTypeStab 1 = 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := rfl

theorem oddTypeStab_zero :
    oddTypeStab 0 = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 := rfl

theorem arith_line_five (n : ℕ) (h : oddTypeStab 2 * tableVOrderB ≤ n * twoBabyOrder) :
    9477 < n := by
  rw [oddTypeStab_two] at h
  unfold tableVOrderB twoBabyOrder at h
  omega

theorem arith_line_five_three (n : ℕ)
    (h : 3 * oddTypeStab 2 * tableVOrderB ≤ n * twoBabyOrder) : 15309 < n := by
  rw [oddTypeStab_two] at h
  unfold tableVOrderB twoBabyOrder at h
  omega

theorem arith_six (n b : ℕ) (hb : 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ≤ b)
    (h : (2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) * b ≤ n * tableVOrderB) : 54463 < n := by
  unfold tableVOrderB at h
  omega

theorem arith_six_four (n : ℕ)
    (h : (2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) * tableVOrderB ≤ n * twoBabyOrder) :
    4756 < n := by
  unfold tableVOrderB twoBabyOrder at h
  omega

theorem low_tableVIIStab (K : TableVIIClass) (h : K ≠ .six_A) :
    2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 ≤ tableVIIStab K := by
  cases K <;> first
    | exact absurd rfl h
    | (unfold tableVIIStab; norm_num [tableVOrderB, tableVOrderZ])

theorem low_tableVIStab (K : TableVIClass) (h : K ≠ .four_A) :
    2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ≤ tableVIStab K := by
  cases K <;> first
    | exact absurd rfl h
    | (unfold tableVIStab; norm_num)

end Arith

section Line

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y z : G}

theorem card_line_mul_le
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hy : IsConj a y)
    (hz : z ∈ twoANbr a y) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) * tableVOrderB ≤
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
        Subgroup.centralizer {z}) * twoBabyOrder := by
  have hprod := card_mul_card_le (A := Subgroup.centralizer ({x} : Set G) ⊓
    Subgroup.centralizer {y}) (B := Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z})
    (L := Subgroup.centralizer ({y} : Set G)) inf_le_right inf_le_left
  have hB := card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hy hz
  have hL := card_centralizer_two I hG hy
  have heq : (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) ⊓
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z}) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
        Subgroup.centralizer {z} := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [heq, hB, hL] at hprod
  exact hprod

omit [Finite G] in
theorem line_contra (hLO : LineOddOrder a) (hy : IsConj a y) (hz : z ∈ twoANbr a y)
    {M : Subgroup G} (hMle : M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z})
    (hodd : Odd (Nat.card M)) (hbig : 54463 < Nat.card M) : False := by
  have := (hLO y z hy hz M hMle hodd).1
  omega

theorem dvd_of_odd_of_dvd_two_pow_mul {d n : ℕ} (k : ℕ) (hd : Odd d) (h : d ∣ 2 ^ k * n) :
    d ∣ n :=
  (Nat.Coprime.pow_right k hd.coprime_two_right).dvd_of_dvd_mul_left h

theorem exists_involution_of_gamma
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a) (hOD : OddTypeDvd a z₀)
    (hx : IsConj a x) (hy : y ∈ gammaNbr a z₀ x) (hz : z ∈ twoANbr a y) :
    ∃ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {z}, orderOf t = 2 := by
  have ha : orderOf a = 2 := hG.1.1
  have hyA : IsConj a y := isConj_of_mem_gammaNbr hx hy
  by_contra hno
  push Not at hno
  have hodd := odd_card_of_forall_orderOf_ne_two _ hno
  set M : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
    Subgroup.centralizer {z} with hM
  have hMle : M ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer {z} := fun g hg =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2,
      (Subgroup.mem_inf.mp hg).2⟩
  have hMxy : M ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} := inf_le_left
  have hprod : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) *
      tableVOrderB ≤ Nat.card M * twoBabyOrder := card_line_mul_le (x := x) I hG hyA hz
  have bigcase : ∀ c : ℕ, 2 ^ 25 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 ≤ c →
      Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) = c → False :=
    fun c hc hcard => line_contra hLO hyA hz hMle hodd
      (by have := arith_line_big _ c hc (hcard ▸ hprod); omega)
  have table7case : ∀ K : TableVIIClass, K ≠ .six_A → y ∈ tableVIISet a z₀ x K → False :=
    fun K hK hyK => bigcase _ (low_tableVIIStab K hK)
      (table7_card I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair hG hx
        hyK)
  rcases mem_gammaNbr_iff.mp hy with hyx | ⟨K, hK⟩
  ·
    subst hyx
    refine hno y ⟨⟨mem_cent_iff.mpr rfl, mem_cent_iff.mpr rfl⟩, ?_⟩
      ((orderOf_eq_of_isConj hx).symm.trans ha)
    exact mem_cent_iff.mpr (mul_comm_of_isConj_mul ha hx hz.1 hz.2)
  cases K with
  | twoA => exact table7case .two_A (by decide) hK
  | twoB => exact table7case .two_B (by decide) hK
  | fourA => exact table7case .four_A (by decide) hK
  | fourB => exact table7case .four_B (by decide) hK
  | threeA =>
    refine bigcase _ (le_trans ?_ (Nat.le_of_dvd Nat.card_pos (hOD x y 0 hx hK.1 hK.2))) rfl
    rw [oddTypeStab_zero]
    norm_num
  | threeC =>
    refine bigcase _ (le_trans ?_ (Nat.le_of_dvd Nat.card_pos (hOD x y 1 hx hK.1 hK.2))) rfl
    rw [oddTypeStab_one]
    norm_num
  | fiveA =>
    obtain ⟨m, hm⟩ := hOD x y 2 hx hK.1 hK.2
    have hpos : 0 < Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) :=
      Nat.card_pos
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm
        omega
      · exact h0
    obtain ⟨hLO1, hLO2, hLO3⟩ := hLO y z hyA hz M hMle hodd
    have hlow : oddTypeStab 2 * m * tableVOrderB ≤ Nat.card M * twoBabyOrder := hm ▸ hprod
    have hm5 : m ≤ 5 := by
      have h2 := le_trans hlow (Nat.mul_le_mul_right twoBabyOrder hLO1)
      rw [oddTypeStab_two] at h2
      unfold tableVOrderB twoBabyOrder at h2
      by_contra hc
      push Not at hc
      have : 6 ≤ m := hc
      nlinarith
    have hmodd : ¬ 2 ∣ m := by
      rintro ⟨k, rfl⟩
      obtain ⟨⟨-, hyx, hodd', w, hw, hwB⟩, hty⟩ := hK
      have hfac := s347_factorization_five_A I.sls I.tableV I.leech I.leechOddPair I.tableIV hG
        hwB (IsOddPair.of_mem_inf hx hyA hyx.symm hodd' hw) (hty w hw hwB)
      have h15 : 2 ^ 15 ∣
          Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) := by
        rw [hm, oddTypeStab_two]
        exact ⟨3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 * k, by ring⟩
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos.ne').mp h15
      omega
    have hdvd : Nat.card M ∣ Nat.gcd (oddTypeStab 2 * m) tableVOrderB :=
      Nat.dvd_gcd (hm ▸ Subgroup.card_dvd_of_le hMxy)
        ((card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hyA hz) ▸
          Subgroup.card_dvd_of_le hMle)
    rw [oddTypeStab_two] at hdvd hlow
    unfold tableVOrderB at hdvd
    interval_cases m
    ·
      have hd : Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 :=
        dvd_of_odd_of_dvd_two_pow_mul 14 hodd (by norm_num at hdvd ⊢; exact hdvd)
      have := arith_line_five (Nat.card M) (by rw [oddTypeStab_two]; simpa using hlow)
      have := hLO2 hd
      omega
    · exact hmodd (dvd_refl 2)
    ·
      have hd : Nat.card M ∣ 3 ^ 7 * 5 ^ 2 * 7 * 11 * 19 :=
        dvd_of_odd_of_dvd_two_pow_mul 14 hodd (by norm_num at hdvd ⊢; exact hdvd)
      have := arith_line_five_three (Nat.card M)
        (by rw [oddTypeStab_two]; linarith [hlow])
      have := hLO3 hd
      omega
    · exact hmodd ⟨2, rfl⟩
    ·
      have hd : Nat.card M ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 :=
        dvd_of_odd_of_dvd_two_pow_mul 14 hodd (by norm_num at hdvd ⊢; exact hdvd)
      have := arith_line_five (Nat.card M)
        (by rw [oddTypeStab_two]; linarith [hlow])
      have := hLO2 hd
      omega
  | sixA =>
    obtain ⟨-, hord6, hbA⟩ := id hK
    have hxx := sq_eq_one_of_isConj ha hx
    have hyy := sq_eq_one_of_isConj ha hyA
    obtain ⟨hbb, -, hbx, hby, -⟩ := dihedral_data (m := 3) hxx hyy (by rw [hord6]) (by norm_num)
    obtain ⟨-, hbyA⟩ := dihedral_isConj (m := 3) hx hyA hxx hyy
    have hbxy : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ≤
        Subgroup.centralizer ({(x * y) ^ 3} : Set G) := centralizer_inf_le_centralizer_pow x y 3
    have hA'card : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) =
        2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 :=
      table7_card I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair hG hx
        (K := .six_A) hK
    generalize hbdef : (x * y) ^ 3 = b at hbA hbx hby hbb hbyA hbxy
    have hbyNbr : y ∈ twoANbr a b := ⟨hyA, hbyA⟩
    have hb2 : orderOf b = 2 := (orderOf_eq_of_isConj hbA).symm.trans ha
    have hbxM : b ∈ Subgroup.centralizer ({x} : Set G) := mem_cent_iff.mpr hbx
    have hbyM : b ∈ Subgroup.centralizer ({y} : Set G) := mem_cent_iff.mpr hby
    by_cases hzb : z = b
    · refine hno b (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hbxM, hbyM⟩, ?_⟩) hb2
      rw [hzb]
      exact mem_cent_iff.mpr rfl
    by_cases hzby : z = b * y
    · refine hno b (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hbxM, hbyM⟩, ?_⟩) hb2
      rw [hzby]
      refine mem_cent_iff.mpr ?_
      calc b * (b * y) = b * (y * b) := by rw [hby]
        _ = (b * y) * b := (mul_assoc _ _ _).symm
    have hzO : z ∈ tableVISet a b y := ⟨hz, hzb, hzby⟩
    obtain ⟨K, hKc, -⟩ :=
      s341_classify I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG hbA hbyNbr hzO
    have hzorb : z ∈ tableVIOrbit a z₀ b y K := ⟨hzO, hKc⟩
    have hB'card := s341_card I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG hbA hbyNbr hzorb
    by_cases hK4 : K = .four_A
    ·
      rw [hK4] at hzorb
      have h4 : 4756 < Nat.card M := arith_six_four _ (by rw [← hA'card]; exact hprod)
      have hMb : M ≤ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} ⊓
          Subgroup.centralizer {z} := fun g hg =>
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hbxy (Subgroup.mem_inf.mp hg).1,
          (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2⟩, (Subgroup.mem_inf.mp hg).2⟩
      have := hF4 b y z hbA hbyNbr hzorb M hMb hodd
      omega
    ·
      have hA'L' : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ≤
          Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} := fun g hg =>
        Subgroup.mem_inf.mpr ⟨hbxy hg, (Subgroup.mem_inf.mp hg).2⟩
      have hB'L' : Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} ⊓
          Subgroup.centralizer {z} ≤ Subgroup.centralizer ({b} : Set G) ⊓
            Subgroup.centralizer {y} := inf_le_left
      have heq : (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) ⊓
          (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y} ⊓
            Subgroup.centralizer {z}) = M := by
        ext g
        simp only [hM, Subgroup.mem_inf]
        constructor
        · rintro ⟨⟨gx, gy⟩, ⟨-, -⟩, gz⟩
          exact ⟨⟨gx, gy⟩, gz⟩
        · rintro ⟨⟨gx, gy⟩, gz⟩
          exact ⟨⟨gx, gy⟩, ⟨hbxy (Subgroup.mem_inf.mpr ⟨gx, gy⟩), gy⟩, gz⟩
      have hL'card : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer {y}) =
          tableVOrderB := card_centralizer_inf_twoANbr I.sls I.tableV I.leech hG hbA hbyNbr
      have hprod' := card_mul_card_le hA'L' hB'L'
      rw [heq, hL'card, hA'card, hB'card] at hprod'
      exact line_contra hLO hyA hz hMle hodd
        (by have := arith_six _ _ (low_tableVIStab K hK4) hprod'; omega)

end Line

end S37

section Headline

open S37

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y z : G}

theorem s372_one
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hCN : CommonNbrTwoB a z₀)
    (hES : EdgeSquares a) (hEC : EightCentOrders a z₀) (hE1 : EightOneOddOrder a z₀)
    (hF4 : FourAOddOrder a z₀) (hLO : LineOddOrder a) (hOD : OddTypeDvd a z₀)
    (hx : IsConj a x) (hy : y ∈ gammaNbr a z₀ x) (hz : z ∈ twoANbr a y) :
    (∃ t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} ⊓
      Subgroup.centralizer {z}, orderOf t = 2) ∧ z ∈ gammaNbr a z₀ x := by
  obtain ⟨t, ht, ht2⟩ := exists_involution_of_gamma I hG hF4 hLO hOD hx hy hz
  refine ⟨⟨t, ht, ht2⟩, ?_⟩
  have htxz : t ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {z} :=
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ht).1).1,
      (Subgroup.mem_inf.mp ht).2⟩
  rcases s31_five I.sls I.tableV I.leech hG I.leechInv ht2 with hA | hB
  · exact s371_two I hG hCN hES hEC hE1 hx hz.1 ⟨t, htxz, hA⟩
  · exact s371_one I hG hCN hx hz.1 (Or.inl ⟨t, htxz, hB⟩)

end Headline

end CFSG.Monster.GMS
