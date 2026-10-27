module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1120V0Bar

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.Sec11.KS11LieProof
open Matrix

section Arith

theorem factorization_mul_of_not_dvd_left {m n : ℕ} (hm : ¬ 3 ∣ m) :
    (m * n).factorization 3 = n.factorization 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm (dvd_zero 3)
    rw [Nat.factorization_mul hm0 hn.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm, zero_add]

theorem factorization_mul_of_not_dvd_right {m n : ℕ} (hn : ¬ 3 ∣ n) :
    (m * n).factorization 3 = m.factorization 3 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn (dvd_zero 3)
    rw [Nat.factorization_mul hm.ne' hn0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

theorem factorization_three_mul (n : ℕ) (hn : n ≠ 0) :
    (3 * n).factorization 3 = 1 + n.factorization 3 := by
  rw [Nat.factorization_mul (show (3 : ℕ) ≠ 0 by norm_num) hn, Finsupp.add_apply,
    Nat.prime_three.factorization_self]

theorem factorization_twentySeven_mul_sq (c : ℕ) (hc : c ≠ 0) :
    (27 * c ^ 2).factorization 3 = 3 + 2 * c.factorization 3 := by
  have h27 : (27 : ℕ).factorization 3 = 3 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.prime_three.factorization_self, smul_eq_mul, mul_one]
  rw [Nat.factorization_mul (show (27 : ℕ) ≠ 0 by norm_num) (pow_ne_zero 2 hc),
    Finsupp.add_apply, h27, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem factorization_mul_sq_sub_one (π : Bool) (q : ℕ) (hq : ModThree π q) :
    (q * (q ^ 2 - 1)).factorization 3 = (qSubPi π q).factorization 3 := by
  cases π
  · change q % 3 = 2 at hq
    change (q * (q ^ 2 - 1)).factorization 3 = (q + 1).factorization 3
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
    have h2 : (3 * b + 2) ^ 2 - 1 = (3 * b + 1) * (3 * (b + 1)) :=
      Nat.sub_eq_of_eq_add (by ring)
    have hq1 : 3 * b + 2 + 1 = 3 * (b + 1) := by ring
    have h3 : ¬ 3 ∣ 3 * b + 2 := by omega
    have h4 : ¬ 3 ∣ 3 * b + 1 := by omega
    rw [h2, hq1, factorization_mul_of_not_dvd_left h3, factorization_mul_of_not_dvd_left h4]
  · change q % 3 = 1 at hq
    change (q * (q ^ 2 - 1)).factorization 3 = (q - 1).factorization 3
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
    have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
    have h1 : 3 * b + 1 - 1 = 3 * b := by omega
    have h3 : ¬ 3 ∣ 3 * b + 1 := by omega
    have h4 : ¬ 3 ∣ 3 * b + 2 := by omega
    rw [h2, h1, factorization_mul_of_not_dvd_left h3, factorization_mul_of_not_dvd_right h4]

theorem factorization_card_sl3_order (π : Bool) (q : ℕ) (hq : ModThree π q) (hq2 : 2 ≤ q) :
    (q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)).factorization 3 =
      2 * (qSubPi π q).factorization 3 + 1 := by
  cases π
  · change q % 3 = 2 at hq
    change (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 = 2 * (q + 1).factorization 3 + 1
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
    have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have h3 : (3 * b + 2) ^ 3 + 1 = 9 * (b + 1) * (3 * b ^ 2 + 3 * b + 1) := by ring
    have hq1 : 3 * b + 2 + 1 = 3 * (b + 1) := by ring
    have hU : ¬ 3 ∣ (3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · have := Nat.prime_three.dvd_of_dvd_pow h
          omega
        · omega
      · omega
    have e : (3 * b + 2) ^ 3 * (3 * (3 * b + 1) * (b + 1)) * (9 * (b + 1) * (3 * b ^ 2 + 3 * b + 1))
        = 27 * (b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1)) := by
      ring
    rw [h2, h3, hq1, e, factorization_mul_of_not_dvd_right hU,
      factorization_twentySeven_mul_sq (b + 1) (by omega),
      factorization_three_mul (b + 1) (by omega)]
    omega
  · change q % 3 = 1 at hq
    change (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 = 2 * (q - 1).factorization 3 + 1
    obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
    have hb : b ≠ 0 := by omega
    have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
    have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
      Nat.sub_eq_of_eq_add (by ring)
    have h1 : 3 * b + 1 - 1 = 3 * b := by omega
    have hU : ¬ 3 ∣ (3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1) := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · have := Nat.prime_three.dvd_of_dvd_pow h
          omega
        · omega
      · omega
    have e : (3 * b + 1) ^ 3 * (3 * b * (3 * b + 2)) * (9 * b * (3 * b ^ 2 + 3 * b + 1))
        = 27 * b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1)) := by
      ring
    rw [h2, h3, h1, e, factorization_mul_of_not_dvd_right hU, factorization_twentySeven_mul_sq b hb,
      factorization_three_mul b hb]
    omega
end Arith

section Mat

variable {Kf : Type} [Field Kf] {p f : ℕ} {π : Bool}

theorem mem_rootsOfUnity_qSubPi (hKf : PiField π p f Kf) {l : Kfˣ}
    (hl : π = false → (l : Kf) ^ (p ^ f + 1) = 1) :
    l ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf := by
  cases π
  · rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hl rfl
  · haveI := hKf.finite
    have hK : Nat.card Kf = p ^ f := hKf.card
    exact mem_rootsOfUnity_of_card hK l

theorem diagE_cube_eq_scalar_mul_torusHom (u : Kfˣ) :
    diagE (u ^ 3) = GeneralLinearGroup.scalar (Fin 3) u * torusHom (u ^ 2, u⁻¹) := by
  have hs : GeneralLinearGroup.scalar (Fin 3) u = diagUnits u u u := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, coe_diagUnits]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have ht : torusHom (u ^ 2, u⁻¹) = diagUnits (u ^ 2) u⁻¹ (u ^ 2 * u⁻¹)⁻¹ := rfl
  have e1 : u * u ^ 2 = u ^ 3 := by group
  have e2 : u * u⁻¹ = 1 := mul_inv_cancel u
  have e3 : u * (u ^ 2 * u⁻¹)⁻¹ = 1 := by group
  rw [hs, ht, diagUnits_mul, e1, e2, e3, diagE]

theorem exists_mem_projImage_diagE_cube (hKf : PiField π p f Kf) {h₀ : GL (Fin 3) Kf}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {u : Kfˣ}
    (hu : u ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf) :
    ∃ x : projImage (slPi π 3 (p ^ f) Kf),
      (x : ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (h₀ * diagE (u ^ 3) * h₀⁻¹) := by
  have hπ : π = false → UnitaryFieldData p f Kf := fun h' => by
    subst h'
    exact hKf.unitary
  have hT : torusHom (u ^ 2, u⁻¹) ∈ slPi π 3 (p ^ f) Kf :=
    torusHom_mem_slPi hKf (pow_mem hu 2) (inv_mem hu)
  have hs : h₀ * torusHom (u ^ 2, u⁻¹) * h₀⁻¹ ∈ slPi π 3 (p ^ f) Kf :=
    conj_mem_slPi hπ hh₀ hT
  have hcen : GeneralLinearGroup.scalar (Fin 3) u ∈ StatedScalars (Fin 3) Kf := ⟨u, rfl⟩
  have hmk : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) Kf) = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hkey : h₀ * diagE (u ^ 3) * h₀⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * (h₀ * torusHom (u ^ 2, u⁻¹) * h₀⁻¹) := by
    rw [diagE_cube_eq_scalar_mul_torusHom u]
    calc h₀ * (GeneralLinearGroup.scalar (Fin 3) u * torusHom (u ^ 2, u⁻¹)) * h₀⁻¹
        = (h₀ * GeneralLinearGroup.scalar (Fin 3) u) * torusHom (u ^ 2, u⁻¹) * h₀⁻¹ := by
          simp only [mul_assoc]
      _ = (GeneralLinearGroup.scalar (Fin 3) u * h₀) * torusHom (u ^ 2, u⁻¹) * h₀⁻¹ := by
          rw [commute_of_mem_statedScalars hcen h₀]
      _ = GeneralLinearGroup.scalar (Fin 3) u * (h₀ * torusHom (u ^ 2, u⁻¹) * h₀⁻¹) := by
          simp only [mul_assoc]
  have hfin : ProjGenLinGroup.mk (h₀ * diagE (u ^ 3) * h₀⁻¹) =
      ProjGenLinGroup.mk (h₀ * torusHom (u ^ 2, u⁻¹) * h₀⁻¹) := by
    rw [hkey, map_mul ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) u), hmk, one_mul]
  refine ⟨projOf (slPi π 3 (p ^ f) Kf) ⟨h₀ * torusHom (u ^ 2, u⁻¹) * h₀⁻¹, hs⟩, ?_⟩
  rw [coe_projOf]
  exact hfin.symm

theorem exists_cube_root (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) {l : Kfˣ}
    (hl : l ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf) (hl3 : l ^ (qSubPi π (p ^ f) / 3) = 1) :
    ∃ u ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf, u ^ 3 = l := by
  haveI := hKf.finite
  obtain ⟨μ, hμ⟩ := exists_orderOf_eq_qSubPi hKf hq
  have hQ0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hKf hq
  have hμQ : μ ^ qSubPi π (p ^ f) = 1 := by
    rw [← hμ]
    exact pow_orderOf_eq_one μ
  have hμmem : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf := (mem_rootsOfUnity _ _).mpr hμQ
  have hsub : Subgroup.zpowers μ = rootsOfUnity (qSubPi π (p ^ f)) Kf := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hμmem
    · exact le_of_eq (by rw [Nat.card_zpowers, hμ, card_rootsOfUnity_qSubPi hKf hq])
  have hlμ : l ∈ Submonoid.powers μ := by
    rw [mem_powers_iff_mem_zpowers, hsub]
    exact hl
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hlμ
  obtain ⟨m, hm⟩ := three_dvd_qSubPi hq
  have hm3 : qSubPi π (p ^ f) / 3 = m := by omega
  rw [hm3] at hl3
  have hn' : μ ^ (n * m) = 1 := by rw [pow_mul, hn, hl3]
  have hdvd : orderOf μ ∣ n * m := orderOf_dvd_of_pow_eq_one hn'
  rw [hμ, hm] at hdvd
  have hm0 : m ≠ 0 := fun h => hQ0 (by rw [hm, h, mul_zero])
  have h3n : 3 ∣ n := (mul_dvd_mul_iff_right hm0).mp hdvd
  obtain ⟨k, hk⟩ := h3n
  exact ⟨μ ^ k, pow_mem hμmem k, by rw [← pow_mul, mul_comm, ← hk, hn]⟩

theorem exists_orderOf_eq_three_pow (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) :
    ∃ u ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf,
      orderOf u = 3 ^ (qSubPi π (p ^ f)).factorization 3 := by
  haveI := hKf.finite
  obtain ⟨μ, hμ⟩ := exists_orderOf_eq_qSubPi hKf hq
  have hQ0 : qSubPi π (p ^ f) ≠ 0 := qSubPi_ne_zero hKf hq
  have hμQ : μ ^ qSubPi π (p ^ f) = 1 := by
    rw [← hμ]
    exact pow_orderOf_eq_one μ
  have hμmem : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) Kf := (mem_rootsOfUnity _ _).mpr hμQ
  have hdvd : 3 ^ (qSubPi π (p ^ f)).factorization 3 ∣ orderOf μ := by
    rw [hμ]
    exact Nat.ordProj_dvd _ _
  have hord : orderOf (μ ^ (orderOf μ / 3 ^ (qSubPi π (p ^ f)).factorization 3)) =
      3 ^ (qSubPi π (p ^ f)).factorization 3 :=
    orderOf_pow_orderOf_div (by rw [hμ]; exact hQ0) hdvd
  rw [hμ] at hord
  exact ⟨μ ^ (qSubPi π (p ^ f) / 3 ^ (qSubPi π (p ^ f)).factorization 3), pow_mem hμmem _, hord⟩

theorem orderOf_conj_of_coe_eq (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) {h₀ : GL (Fin 3) Kf} {t : Kfˣ} (x : projImage (slPi π 3 (p ^ f) Kf))
    (hx : (x : ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹)) :
    orderOf (MulAut.conj x) = orderOf t := by
  have hβ : ∀ m : projImage (slPi π 3 (p ^ f) Kf),
      ((MulAut.conj x) m : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) * m *
          (ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹))⁻¹ := by
    intro m
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx]
  exact orderOf_eq_orderOf_iff.mpr fun n =>
    KS11LieProof.pow_eq_one_iff_of_conj hKf hq hq2 (β := MulAut.conj x) (h₀ := h₀) (l := t)
      hβ n

theorem conj_injective_projImage (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) :
    Function.Injective (MulAut.conj : projImage (slPi π 3 (p ^ f) Kf) →*
      MulAut (projImage (slPi π 3 (p ^ f) Kf))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨⟨g0, hg0⟩, rfl⟩ := projOf_surjective (slPi π 3 (p ^ f) Kf) g
  have hcomm : ∀ s ∈ slPi π 3 (p ^ f) Kf,
      ProjGenLinGroup.mk g0 * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk g0 := by
    intro s hs
    have h1 : MulAut.conj (projOf (slPi π 3 (p ^ f) Kf) ⟨g0, hg0⟩)
        (projOf (slPi π 3 (p ^ f) Kf) ⟨s, hs⟩) =
        projOf (slPi π 3 (p ^ f) Kf) ⟨s, hs⟩ := by
      rw [hg]
      rfl
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
    have h3 := congrArg (fun y : projImage (slPi π 3 (p ^ f) Kf) =>
      (y : ProjGenLinGroup (Fin 3) Kf)) h1
    simpa only [Subgroup.coe_mul, coe_projOf] using h3
  have hscal := Sec13.mem_statedScalars_of_commute_mk hKf hq hq2 hcomm
  exact MonoidHom.mem_ker.mp ((mem_ker_projOf ⟨g0, hg0⟩).mpr hscal)

theorem mk_diagE_commute_blockProj (hKf : PiField π p f Kf) {h₀ : GL (Fin 3) Kf}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) (t : Kfˣ) (B : slPi π 2 (p ^ f) Kf) :
    ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) *
        (blockProj hKf hh₀ B : ProjGenLinGroup (Fin 3) Kf) =
      (blockProj hKf hh₀ B : ProjGenLinGroup (Fin 3) Kf) *
        ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) := by
  have hc := blockHom_commute t (B : GL (Fin 2) Kf)
  have key1 : h₀ * diagE t * h₀⁻¹ * (h₀ * blockHom (B : GL (Fin 2) Kf) * h₀⁻¹) =
      h₀ * (diagE t * blockHom (B : GL (Fin 2) Kf)) * h₀⁻¹ := by
    group
  have key2 : h₀ * blockHom (B : GL (Fin 2) Kf) * h₀⁻¹ * (h₀ * diagE t * h₀⁻¹) =
      h₀ * (blockHom (B : GL (Fin 2) Kf) * diagE t) * h₀⁻¹ := by
    group
  rw [coe_blockProj, ← map_mul, ← map_mul, key1, key2, hc]

theorem mul_blockProj_mul_inv_of_coe_eq (hKf : PiField π p f Kf) {h₀ : GL (Fin 3) Kf}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {t : Kfˣ} (x : projImage (slPi π 3 (p ^ f) Kf))
    (hx : (x : ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹))
    (B : slPi π 2 (p ^ f) Kf) :
    x * blockProj hKf hh₀ B * x⁻¹ = blockProj hKf hh₀ B := by
  have hc := mk_diagE_commute_blockProj hKf hh₀ t B
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hx, hc, mul_inv_cancel_right]

theorem mk_diagE_commute (h₀ : GL (Fin 3) Kf) (e t : Kfˣ) :
    ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) =
      ProjGenLinGroup.mk (h₀ * diagE t * h₀⁻¹) * ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) := by
  have hc : diagE e * diagE t = diagE t * diagE e := by
    rw [diagE, diagE, diagUnits_mul, diagUnits_mul, mul_comm e t]
  have key1 : h₀ * diagE e * h₀⁻¹ * (h₀ * diagE t * h₀⁻¹) =
      h₀ * (diagE e * diagE t) * h₀⁻¹ := by
    group
  have key2 : h₀ * diagE t * h₀⁻¹ * (h₀ * diagE e * h₀⁻¹) =
      h₀ * (diagE t * diagE e) * h₀⁻¹ := by
    group
  rw [← map_mul, ← map_mul, key1, key2, hc]

theorem card_slPi_two (hKf : PiField π p f Kf) :
    Nat.card (slPi π 2 (p ^ f) Kf) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  have := hKf.finite
  have : Fact p.Prime := ⟨hKf.prime⟩
  cases π
  · have hcard : Nat.card Kf = (p ^ f) ^ 2 := hKf.card
    have : CharP Kf p := hKf.unitary.charP
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := Kf) (r := p) (f := f) hcard
    have hF := CFSG.LieType.Steinberg.card_fixedSubfield (F := Kf) (p := p) (f := f) hcard
    change Nat.card (CFSG.Open.StatedSU 2 (p ^ f) Kf) = _
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  · have hcard : Nat.card Kf = p ^ f := hKf.card
    change Nat.card (CFSG.Open.StatedSL 2 Kf) = _
    rw [CFSG.Open.StatedAPI.card_statedSL_two Kf, hcard]

theorem factorization_card_slPi_two (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) :
    (Nat.card (slPi π 2 (p ^ f) Kf)).factorization 3 = (qSubPi π (p ^ f)).factorization 3 := by
  rw [card_slPi_two hKf]
  exact factorization_mul_sq_sub_one π (p ^ f) hq

theorem factorization_card_projImage (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) :
    (Nat.card (projImage (slPi π 3 (p ^ f) Kf))).factorization 3 =
      2 * (qSubPi π (p ^ f)).factorization 3 := by
  have hf : 1 ≤ f := hKf.one_le
  have hq2 : 2 ≤ p ^ f := le_trans hKf.prime.two_le (Nat.le_self_pow (by omega) p)
  have hmul := CFSG.RankThree.PartTwo.Sec13.card_projImage_slPi_mul_three hKf hq
  have hn0 : Nat.card (projImage (slPi π 3 (p ^ f) Kf)) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    have h2 : 2 ≤ (p ^ f) ^ 2 := le_trans hq2 (Nat.le_self_pow two_ne_zero _)
    have h3 : 2 ≤ (p ^ f) ^ 3 := le_trans hq2 (Nat.le_self_pow three_ne_zero _)
    have hpos : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1)
        ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)) ?_
      cases π
      · show (p ^ f) ^ 3 + 1 ≠ 0
        omega
      · show (p ^ f) ^ 3 - 1 ≠ 0
        omega
    exact hpos hmul.symm
  have h3 : (Nat.card (projImage (slPi π 3 (p ^ f) Kf)) * 3).factorization 3 =
      (Nat.card (projImage (slPi π 3 (p ^ f) Kf))).factorization 3 + 1 := by
    rw [mul_comm, factorization_three_mul _ hn0]
    omega
  rw [hmul] at h3
  have key := factorization_card_sl3_order π (p ^ f) hq hq2
  omega

end Mat

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
