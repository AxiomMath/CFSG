module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.Sec4.Item434CharThree CFSG.LieType.Universal.Unitary
open CFSG.SectionRank.OddCover (heisSU coe_heisSU coe_heisSU_inv SU_ext)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.RankThreeEven (projSU)
open Matrix

namespace U3Char3

section Torus

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] noncomputable def torusU (hσ : ∀ c, σ (σ c) = c) {t : F} (ht : t ≠ 0) : SU σ 3 :=
  have hs : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  ⟨⟨diagonal ![t, σ t / t, (σ t)⁻¹], diagonal ![t⁻¹, t / σ t, σ t],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp <;> field_simp⟩,
    by simp [det_diagonal, Fin.prod_univ_three]; field_simp,
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, diagonal, Fin.rev, hσ] <;>
        field_simp⟩

theorem torusU_mul_heisSU (hσ : ∀ c, σ (σ c) = c) {t : F} (ht : t ≠ 0) (a b : F)
    (hab : b + σ b + σ a * a = 0)
    (hab' : b * (t * σ t) + σ (b * (t * σ t)) + σ (a * t ^ 2 / σ t) * (a * t ^ 2 / σ t) = 0) :
    torusU hσ ht * heisSU hσ a b hab =
      heisSU hσ (a * t ^ 2 / σ t) (b * (t * σ t)) hab' * torusU hσ ht := by
  have hs : σ t ≠ 0 := (map_ne_zero σ).mpr ht
  apply SU_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_heisSU, coe_heisSU]
  show diagonal ![t, σ t / t, (σ t)⁻¹] * heisenbergMatrix σ 0 1 a b =
    heisenbergMatrix σ 0 1 _ _ * diagonal ![t, σ t / t, (σ t)⁻¹]
  rw [CFSG.LieType.Steinberg.heisenbergMatrix_three, CFSG.LieType.Steinberg.heisenbergMatrix_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, hσ] <;> field_simp

end Torus

section Heis

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

theorem heisSU_zero (h : (0 : F) + σ 0 + σ 0 * 0 = 0) : heisSU hσ 0 0 h = 1 :=
  SU_ext (by rw [coe_heisSU, heisenbergMatrix_zero]; rfl)

theorem heisSU_inj {a b a' b' : F} (hab : b + σ b + σ a * a = 0)
    (hab' : b' + σ b' + σ a' * a' = 0) (h : heisSU hσ a b hab = heisSU hσ a' b' hab') :
    a = a' ∧ b = b' := by
  have h' := congrArg (fun g : SU σ 3 => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_heisSU] at h'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  rw [heisenbergMatrix_apply01, heisenbergMatrix_apply01] at h1
  rw [heisenbergMatrix_apply02, heisenbergMatrix_apply02] at h2
  exact ⟨h1, h2⟩

theorem heisSU_inv_eq' (a b : F) (hab : b + σ b + σ a * a = 0)
    (hab' : -b - a * σ a + σ (-b - a * σ a) + σ (-a) * -a = 0) :
    (heisSU hσ a b hab)⁻¹ = heisSU hσ (-a) (-b - a * σ a) hab' :=
  SU_ext (by rw [coe_heisSU_inv, coe_heisSU])

theorem ent01_heisSU (a b : F) (hab : b + σ b + σ a * a = 0) : ent01 (heisSU hσ a b hab) = a := by
  rw [ent01, coe_heisSU, heisenbergMatrix_apply01]

theorem heisSU_conj_not_mem_zpowers [CharP F 3] {s : F} (hs0 : s ≠ 0) (hs4 : s ^ 4 ≠ 1) {a b : F}
    (hab : b + σ b + σ a * a = 0)
    (hab' : s ^ 2 * b + σ (s ^ 2 * b) + σ (s * a) * (s * a) = 0) (hne : ¬ (a = 0 ∧ b = 0)) :
    heisSU hσ (s * a) (s ^ 2 * b) hab' ∉ Subgroup.zpowers (heisSU hσ a b hab) := by
  intro hmem
  have hq3 : heisSU hσ a b hab ^ 3 = 1 :=
    pow_three_eq_one_of_mem_heisU (hσ := hσ) ⟨a, b, hab, rfl⟩
  apply hs4
  rcases mem_zpowers_cases_of_pow_three hq3 hmem with h | h | h
  ·
    have h0 : (0 : F) + σ 0 + σ 0 * 0 = 0 := by simp
    obtain ⟨h1, h2⟩ := heisSU_inj hσ _ h0 (h.trans (heisSU_zero hσ h0).symm)
    exact absurd ⟨(mul_eq_zero.mp h1).resolve_left hs0,
      (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 2 hs0)⟩ hne
  ·
    obtain ⟨h1, h2⟩ := heisSU_inj hσ _ hab h
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => hne ⟨ha, hb⟩
      have h4 : (s ^ 2 - 1) * b = 0 := by linear_combination h2
      have hs2 : s ^ 2 = 1 := by
        linear_combination (mul_eq_zero.mp h4).resolve_right hb
      linear_combination (s ^ 2 + 1) * hs2
    · have h4 : (s - 1) * a = 0 := by linear_combination h1
      have hs1 : s = 1 := sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right ha)
      rw [hs1]
      norm_num
  ·
    have hinv : -b - a * σ a + σ (-b - a * σ a) + σ (-a) * -a = 0 := by
      rw [map_sub, map_neg, map_mul, map_neg, hσ]
      linear_combination -hab
    rw [heisSU_inv_eq' hσ a b hab hinv] at h
    obtain ⟨h1, h2⟩ := heisSU_inj hσ _ hinv h
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => hne ⟨ha, hb⟩
      have h4 : (s ^ 2 + 1) * b = 0 := by
        rw [ha] at h2
        linear_combination h2
      have hs2 : s ^ 2 = -1 := by
        linear_combination (mul_eq_zero.mp h4).resolve_right hb
      linear_combination (s ^ 2 - 1) * hs2
    · have h4 : (s + 1) * a = 0 := by linear_combination h1
      have hs1 : s = -1 := eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h4).resolve_right ha)
      rw [hs1]
      norm_num

theorem exists_torusU_witness [CharP F 3] {s : F} (hs0 : s ≠ 0) (hsσ : σ s = s) (hs4 : s ^ 4 ≠ 1)
    {q : SU σ 3} (hq : q ∈ heisU hσ) (hq1 : q ≠ 1) :
    ∃ g : SU σ 3, (g * q * g⁻¹) * q = q * (g * q * g⁻¹) ∧ g * q * g⁻¹ ∉ Subgroup.zpowers q := by
  obtain ⟨a, b, hab, hm⟩ := hq
  obtain rfl : q = heisSU hσ a b hab := SU_ext hm
  have hab' : s ^ 2 * b + σ (s ^ 2 * b) + σ (s * a) * (s * a) = 0 := by
    rw [map_mul, map_mul, map_pow, hsσ]
    linear_combination s ^ 2 * hab
  have hab'' : b * (s * σ s) + σ (b * (s * σ s)) + σ (a * s ^ 2 / σ s) * (a * s ^ 2 / σ s) = 0 := by
    rw [hsσ]
    simp only [map_mul, map_div₀, map_pow, hsσ]
    have e : σ a * s ^ 2 / s * (a * s ^ 2 / s) = s ^ 2 * (σ a * a) := by field_simp
    rw [e]
    linear_combination s ^ 2 * hab
  have hX : heisSU hσ (a * s ^ 2 / σ s) (b * (s * σ s)) hab'' =
      heisSU hσ (s * a) (s ^ 2 * b) hab' := by
    apply SU_ext
    rw [coe_heisSU, coe_heisSU, hsσ]
    have e1 : a * s ^ 2 / s = s * a := by field_simp
    have e2 : b * (s * s) = s ^ 2 * b := by ring
    rw [e1, e2]
  have hconj : torusU hσ hs0 * heisSU hσ a b hab * (torusU hσ hs0)⁻¹ =
      heisSU hσ (s * a) (s ^ 2 * b) hab' := by
    rw [mul_inv_eq_iff_eq_mul, torusU_mul_heisSU hσ hs0 a b hab hab'', hX]
  have hne : ¬ (a = 0 ∧ b = 0) := by
    rintro ⟨rfl, rfl⟩
    exact hq1 (heisSU_zero hσ hab)
  refine ⟨torusU hσ hs0, ?_, ?_⟩
  · rw [hconj]
    have hg : heisSU hσ (s * a) (s ^ 2 * b) hab' ∈ heisU hσ := ⟨_, _, hab', rfl⟩
    have hg' : heisSU hσ a b hab ∈ heisU hσ := ⟨_, _, hab, rfl⟩
    refine (commute_iff_of_mem_heisU hg hg').mpr ?_
    rw [ent01_heisSU, ent01_heisSU, map_mul, hsσ]
    ring
  · rw [hconj]
    exact heisSU_conj_not_mem_zpowers hσ hs0 hs4 hab hab' hne

end Heis

theorem not_three_pow_succ_dvd_card_SU_three {e : ℕ} (he : e ≠ 0) :
    ¬ 3 ^ (3 * e + 1) ∣ Nat.card (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) := by
  have hpos : Nat.card (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) ≠ 0 :=
    Nat.card_pos.ne'
  intro hd
  have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).mp hd
  rw [factorization_card_SU_three he] at h
  omega

theorem exists_fixed_pow_four_ne_one {e : ℕ} (he : 2 ≤ e) :
    ∃ s : GaloisField 3 (2 * e), s ≠ 0 ∧
      unitaryInvolution (GaloisField 3 (2 * e)) 3 e s = s ∧ s ^ 4 ≠ 1 := by
  have hF : Nat.card (GaloisField 3 (2 * e)) = (3 ^ e) ^ 2 := card_galois_two_mul (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := (CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 (2 * e)) 3 e)ˣ)
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Nat.card_units, CFSG.LieType.Steinberg.card_fixedSubfield hF] at hord
  have h4 : g ^ 4 ≠ 1 := fun h => by
    have h1 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h)
    have h2 : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  refine ⟨((g : CFSG.LieType.Steinberg.fixedSubfield (GaloisField 3 (2 * e)) 3 e) :
    GaloisField 3 (2 * e)), ?_, ?_, ?_⟩
  · exact fun h => g.ne_zero (Subtype.ext h)
  · exact (CFSG.LieType.Steinberg.mem_fixedSubfield).mp (g : CFSG.LieType.Steinberg.fixedSubfield
      (GaloisField 3 (2 * e)) 3 e).2
  · intro h
    apply h4
    apply Units.ext
    apply Subtype.ext
    simpa using h

end U3Char3

open U3Char3

theorem listRow_SU_three_char_three {e : ℕ} (he : 2 ≤ e) :
    ListRow (SU (unitaryInvolution (GaloisField 3 (2 * e)) 3 e) 3) := by
  have he0 : e ≠ 0 := by omega
  have hF : Nat.card (GaloisField 3 (2 * e)) = (3 ^ e) ^ 2 := card_galois_two_mul he0
  obtain ⟨s, hs0, hsσ, hs4⟩ := exists_fixed_pow_four_ne_one he
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  refine not_weaklyClosed_of_sylow_witness (3 * e) (heisU (unitaryInvolution_involutive hF))
    (by rw [card_heisU hF, ← pow_mul, mul_comm]) (not_three_pow_succ_dvd_card_SU_three he0)
    (fun q hq hqo => ?_) hz
  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hqo
    omega
  exact exists_torusU_witness _ hs0 hsσ hs4 hq hq1

instance finite_projSU_three_u3 (p f : ℕ) [Fact p.Prime] : Finite (projSU 3 p f) := by
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField p (2 * f))) :=
    Finite.of_surjective
      (Matrix.ProjGenLinGroup.mk :
        Matrix.GeneralLinearGroup (Fin 3) (GaloisField p (2 * f)) →* _)
      Matrix.ProjGenLinGroup.mk_surjective
  infer_instance

theorem listRow_projSU_three_char_three {e : ℕ} (he : 2 ≤ e) : ListRow (projSU 3 3 e) :=
  ListRow.of_mulEquiv (suEquivProjSU (by omega)) (listRow_SU_three_char_three he)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
