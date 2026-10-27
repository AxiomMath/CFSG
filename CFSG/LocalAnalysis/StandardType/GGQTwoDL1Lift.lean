module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType.QTwo

variable {G : Type} [Group G] [Finite G]

private lemma p9uLF_conj_pow_eq {X : Subgroup G} {c t : G} (htX : t ∈ X)
    (h : ∀ y ∈ X, t * y * t⁻¹ = c * y * c⁻¹) :
    ∀ N : ℕ, ∀ y ∈ X, t ^ N * y * (t ^ N)⁻¹ = c ^ N * y * (c ^ N)⁻¹ := by
  intro N
  induction N with
  | zero => intro y _; simp
  | succ N ih =>
      intro y hy
      have hy' : t * y * t⁻¹ ∈ X := X.mul_mem (X.mul_mem htX hy) (X.inv_mem htX)
      have h1 : t ^ N * (t * y * t⁻¹) * (t ^ N)⁻¹
          = c ^ N * (t * y * t⁻¹) * (c ^ N)⁻¹ := ih _ hy'
      rw [show t ^ (N + 1) * y * (t ^ (N + 1))⁻¹ = t ^ N * (t * y * t⁻¹) * (t ^ N)⁻¹ by
            group,
        h1, h y hy,
        show c ^ N * (c * y * c⁻¹) * (c ^ N)⁻¹ = c ^ (N + 1) * y * (c ^ (N + 1))⁻¹ by group]

theorem qtwoDL1_ggOTwoPrime_eq_of_inner {C X : Subgroup G}
    (hodd : Odd (Nat.card ↥(C ⊓ Subgroup.centralizer (X : Set G))))
    (hin : ∀ c ∈ C, (∃ k : ℕ, c ^ (2 ^ k) = 1) →
      ∃ t ∈ ggOTwoPrime (X ⊓ C), ∀ y ∈ X, c * y * c⁻¹ = t * y * t⁻¹) :
    ggOTwoPrime C = ggOTwoPrime (X ⊓ C) := by
  refine le_antisymm ?_ ?_
  · rw [ggOTwoPrime]
    refine (Subgroup.closure_le _).mpr ?_
    rintro c ⟨hcC, k, hck⟩
    obtain ⟨t, htT, htact⟩ := hin c hcC ⟨k, hck⟩
    have htX : t ∈ X := (Subgroup.mem_inf.mp ((ggOTwoPrime_le (X ⊓ C)) htT)).1
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0] at hck
      simp at hck
      rw [hck]
      exact Subgroup.one_mem _
    · have hk1 : 1 < 2 ^ k := Nat.one_lt_pow hkpos.ne' (by norm_num)
      obtain ⟨a, d, hdodd, hdorder⟩ :=
        Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
      have hcop : Nat.Coprime d (2 ^ k) := (hdodd.coprime_two_right).pow_right k
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk1
      set N := d * m with hNdef
      have hdN : d ∣ N := ⟨m, hNdef⟩
      have hNmod : N % 2 ^ k = 1 := by rw [hNdef]; exact hm
      have hN1 : N ≡ 1 [MOD 2 ^ k] := by
        show N % 2 ^ k = 1 % 2 ^ k
        rw [hNmod, Nat.mod_eq_of_lt hk1]
      obtain ⟨q, hq⟩ := hdN
      have htN2 : (t ^ N) ^ (2 ^ a) = 1 := by
        rw [← pow_mul]
        have he : N * 2 ^ a = orderOf t * q := by rw [hq, hdorder]; ring
        rw [he, pow_mul, pow_orderOf_eq_one, one_pow]
      have hactN : ∀ y ∈ X, t ^ N * y * (t ^ N)⁻¹ = c * y * c⁻¹ := by
        intro y hy
        rw [p9uLF_conj_pow_eq htX (fun y hy => (htact y hy).symm) N y hy,
          pow_eq_pow_of_modEq hN1 hck, pow_one]
      have htNT : t ^ N ∈ ggOTwoPrime (X ⊓ C) :=
        Subgroup.pow_mem _ htT N
      have htNX : t ^ N ∈ X := (Subgroup.mem_inf.mp ((ggOTwoPrime_le (X ⊓ C)) htNT)).1
      have hconjT : c * t ^ N * c⁻¹ = t ^ N := by
        have h := hactN (t ^ N) htNX
        simpa using h.symm
      have hcomm : c * t ^ N = t ^ N * c := by
        have h := congrArg (· * c) hconjT
        simpa [mul_assoc] using h
      have hcomm_inv : (t ^ N)⁻¹ * c = c * (t ^ N)⁻¹ := by
        calc (t ^ N)⁻¹ * c
            = (t ^ N)⁻¹ * (c * t ^ N) * (t ^ N)⁻¹ := by group
          _ = (t ^ N)⁻¹ * (t ^ N * c) * (t ^ N)⁻¹ := by rw [hcomm]
          _ = c * (t ^ N)⁻¹ := by group
      have hcommute : Commute ((t ^ N)⁻¹) c :=
        (commute_iff_eq ((t ^ N)⁻¹) c).mpr hcomm_inv
      have hnD : (t ^ N)⁻¹ * c ∈ C ⊓ Subgroup.centralizer (X : Set G) := by
        refine ⟨C.mul_mem (C.inv_mem (le_trans (ggOTwoPrime_le (X ⊓ C)) inf_le_right htNT))
          hcC, ?_⟩
        change (t ^ N)⁻¹ * c ∈ Subgroup.centralizer (X : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hg : ((t ^ N)⁻¹ * c) * y * ((t ^ N)⁻¹ * c)⁻¹ = y := by
          rw [show ((t ^ N)⁻¹ * c)⁻¹ = c⁻¹ * t ^ N by group,
            show (t ^ N)⁻¹ * c * y * (c⁻¹ * t ^ N)
                = (t ^ N)⁻¹ * (c * y * c⁻¹) * t ^ N by group,
            ← hactN y hy]
          group
        have h := congrArg (· * ((t ^ N)⁻¹ * c)) hg
        simpa [mul_assoc] using h.symm
      have hnpow : ((t ^ N)⁻¹ * c) ^ (2 ^ (a + k)) = 1 := by
        have htN2' : (t ^ N) ^ (2 ^ (a + k)) = 1 := by
          rw [show 2 ^ (a + k) = 2 ^ a * 2 ^ k by rw [pow_add], pow_mul, htN2, one_pow]
        have hc2' : c ^ (2 ^ (a + k)) = 1 := by
          rw [show 2 ^ (a + k) = 2 ^ k * 2 ^ a by rw [pow_add]; ring, pow_mul, hck,
            one_pow]
        rw [hcommute.mul_pow (2 ^ (a + k)), inv_pow, htN2', inv_one, hc2', mul_one]
      have hcop2 : Nat.Coprime (2 ^ (a + k))
          (Nat.card ↥(C ⊓ Subgroup.centralizer (X : Set G))) :=
        (Nat.coprime_two_left.mpr hodd).pow_left (a + k)
      have horder1 : orderOf ((t ^ N)⁻¹ * c) = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop2
          (orderOf_dvd_iff_pow_eq_one.mpr hnpow)
          (Subgroup.orderOf_dvd_natCard _ hnD)
      have hn_eq : (t ^ N)⁻¹ * c = 1 := orderOf_eq_one_iff.mp horder1
      have hc_eq : c = t ^ N := by
        have h := congrArg (fun z => t ^ N * z) hn_eq
        simpa [mul_assoc] using h
      rw [hc_eq]
      exact htNT
  · exact Subgroup.closure_mono fun y hy => ⟨hy.1.2, hy.2⟩

end CFSG.StandardType.QTwo

end
