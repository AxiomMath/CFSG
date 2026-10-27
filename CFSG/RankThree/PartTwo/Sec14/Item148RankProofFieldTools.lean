module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Item148Rank

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

theorem exists_generator_pow148 {G : Type*} [Group G] [Finite G] [IsCyclic G] :
    ∃ g : G, orderOf g = Nat.card G ∧ ∀ x : G, ∃ i : ℕ, g ^ i = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  refine ⟨g, orderOf_eq_card_of_forall_mem_zpowers hg, fun x => ?_⟩
  have h := hg x
  rw [← (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers] at h
  exact (Submonoid.mem_powers_iff x g).mp h

theorem exists_cube_of_pow_div_three148 {G : Type*} [Group G] [Finite G] [IsCyclic G] {m : ℕ}
    (hm : m ∣ Nat.card G) (h3 : 3 ∣ m) {d : G} (hd : d ^ (m / 3) = 1) :
    ∃ u : G, u ^ m = 1 ∧ u ^ 3 = d := by
  obtain ⟨g, hord, hg⟩ := exists_generator_pow148 (G := G)
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, rfl⟩ := h3
  have hN : 0 < Nat.card G := Nat.card_pos
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hs; omega
    · exact h
  obtain ⟨i, rfl⟩ := hg d
  rw [Nat.mul_div_cancel_left t (by norm_num), ← pow_mul] at hd
  have h1 : orderOf g ∣ i * t := orderOf_dvd_of_pow_eq_one hd
  rw [hord, hs] at h1
  have h2 : 3 * s ∣ i := by
    have : 3 * s * t ∣ i * t := by
      calc 3 * s * t = 3 * t * s := by ring
        _ ∣ i * t := h1
    exact Nat.dvd_of_mul_dvd_mul_right ht this
  obtain ⟨j, rfl⟩ := h2
  refine ⟨g ^ (s * j), ?_, ?_⟩
  · rw [← pow_mul, show s * j * (3 * t) = (3 * t * s) * j by ring, ← hs, pow_mul, ← hord,
      pow_orderOf_eq_one, one_pow]
  · rw [← pow_mul]
    congr 1
    ring

theorem exists_mul_pow_cube148 {G : Type*} [Group G] [Finite G] [IsCyclic G] {m : ℕ}
    (hm : m ∣ Nat.card G) (h3 : 3 ∣ m) {d b : G} (hd : d ^ m = 1) (hb : b ^ m = 1)
    (hnd : ¬ ∃ u : G, u ^ m = 1 ∧ u ^ 3 = d) :
    ∃ k : ℕ, k < 3 ∧ ∃ u : G, u ^ m = 1 ∧ u ^ 3 = b * d ^ k := by
  obtain ⟨g, hord, hg⟩ := exists_generator_pow148 (G := G)
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, rfl⟩ := h3
  have hN : 0 < Nat.card G := Nat.card_pos
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hs; omega
    · exact h
  have hform : ∀ x : G, x ^ (3 * t) = 1 → ∃ i : ℕ, g ^ (s * i) = x := by
    intro x hx
    obtain ⟨i, rfl⟩ := hg x
    rw [← pow_mul] at hx
    have h1 : orderOf g ∣ i * (3 * t) := orderOf_dvd_of_pow_eq_one hx
    rw [hord, hs] at h1
    have h2 : s ∣ i := by
      have : s * (3 * t) ∣ i * (3 * t) := by
        calc s * (3 * t) = 3 * t * s := by ring
          _ ∣ i * (3 * t) := h1
      exact Nat.dvd_of_mul_dvd_mul_right (by omega) this
    obtain ⟨i', rfl⟩ := h2
    exact ⟨i', rfl⟩
  have hcube : ∀ i : ℕ, 3 ∣ i → ∃ u : G, u ^ (3 * t) = 1 ∧ u ^ 3 = g ^ (s * i) := by
    rintro i ⟨j, rfl⟩
    refine ⟨g ^ (s * j), ?_, ?_⟩
    · rw [← pow_mul, show s * j * (3 * t) = (3 * t * s) * j by ring, ← hs, pow_mul, ← hord,
        pow_orderOf_eq_one, one_pow]
    · rw [← pow_mul]
      congr 1
      ring
  obtain ⟨i, rfl⟩ := hform d hd
  obtain ⟨j, rfl⟩ := hform b hb
  have hi : ¬ 3 ∣ i := fun h => hnd (hcube i h)
  have hk : ∃ k : ℕ, k < 3 ∧ 3 ∣ j + i * k := by
    have hi3 : i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hj3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj3 with h | h | h
    · exact ⟨0, by norm_num, by omega⟩
    · rcases hi3 with h' | h'
      · exact ⟨2, by norm_num, by omega⟩
      · exact ⟨1, by norm_num, by omega⟩
    · rcases hi3 with h' | h'
      · exact ⟨1, by norm_num, by omega⟩
      · exact ⟨2, by norm_num, by omega⟩
  obtain ⟨k, hk3, hdiv⟩ := hk
  refine ⟨k, hk3, ?_⟩
  obtain ⟨u, hu1, hu3⟩ := hcube (j + i * k) hdiv
  refine ⟨u, hu1, ?_⟩
  rw [hu3, ← pow_mul, ← pow_add]
  congr 1
  ring

theorem eq_one_of_pow_three_of_coprime148 {G : Type*} [Monoid G] {e : G} {r : ℕ}
    (h3 : e ^ 3 = 1) (hr : e ^ r = 1) (hcop : Nat.Coprime 3 r) : e = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨h3, hr⟩
  rwa [hcop, pow_one] at h

theorem pow_eq_one_of_twisted148 {G : Type*} [CommGroup G] {d l : G} {t : ℕ}
    (hd : d ^ (3 * t + 1) = l ^ 3 * d) (hl : l ^ (1 + (3 * t + 1) + (3 * t + 1) ^ 2) = 1) :
    d ^ (3 * t * (3 * t ^ 2 + 3 * t + 1)) = 1 := by
  have h1 : d ^ (3 * t) = l ^ 3 := by
    rw [pow_succ] at hd
    exact mul_right_cancel hd
  rw [pow_mul, h1, ← pow_mul]
  rw [show 1 + (3 * t + 1) + (3 * t + 1) ^ 2 = 3 * (3 * t ^ 2 + 3 * t + 1) by ring] at hl
  exact hl

theorem pow_three_mod_three148 (a : ℕ) : a ^ 3 % 3 = a % 3 := by
  have h : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rw [Nat.pow_mod]
  rcases h with h | h | h <;> rw [h]

theorem ringAut_eq_or_mul_eq_one148 {K : Type*} [Field K] [Finite K] {p F : ℕ} (hp : p.Prime)
    (hF : 1 ≤ F) (hcard : Nat.card K = p ^ F) {σ τ : K ≃+* K} (hσ : orderOf σ = 3)
    (hτ : orderOf τ = 3) : τ = σ ∨ τ * σ = 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨h3F, hσf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hF hcard hσ
  obtain ⟨-, hτf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hF hcard hτ
  have hpow : ∀ x : K, x ^ p ^ F = x := fun x => by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hsum : p ^ (F / 3) * p ^ (2 * F / 3) = p ^ F := by
    rw [← pow_add]
    congr 1
    omega
  rcases hσf with hσf | hσf <;> rcases hτf with hτf | hτf
  · exact Or.inl (RingEquiv.ext fun x => by rw [hτf, hσf])
  · refine Or.inr (RingEquiv.ext fun x => ?_)
    rw [RingAut.mul_apply, hτf, hσf, ← pow_mul, hsum, hpow, RingAut.one_apply]
  · refine Or.inr (RingEquiv.ext fun x => ?_)
    rw [RingAut.mul_apply, hτf, hσf, ← pow_mul, mul_comm, hsum, hpow, RingAut.one_apply]
  · exact Or.inl (RingEquiv.ext fun x => by rw [hτf, hσf])

theorem exists_pow_form148 {K : Type*} [Field K] [Finite K] {p F : ℕ} (hp : p.Prime)
    (hF : 1 ≤ F) (hcard : Nat.card K = p ^ F) (hK : p ^ F % 3 = 1) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) :
    ∃ t : ℕ, ((3 * t + 1) ^ 3 = p ^ F ∨ (3 * t + 1) ^ 3 = (p ^ F) ^ 2) ∧
      ∀ u : Kˣ, Units.map (σ : K →* K) u = u ^ (3 * t + 1) := by
  obtain ⟨h3F, hσf⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hF hcard hσ
  have hmod : ∀ a : ℕ, (a ^ 3 = p ^ F ∨ a ^ 3 = (p ^ F) ^ 2) → a % 3 = 1 := by
    intro a ha
    have h1 : a ^ 3 % 3 = a % 3 := pow_three_mod_three148 a
    rcases ha with ha | ha
    · rw [← h1, ha, hK]
    · rw [← h1, ha, Nat.pow_mod, hK]
  have hform : ∀ a : ℕ, (a ^ 3 = p ^ F ∨ a ^ 3 = (p ^ F) ^ 2) → (∀ x, σ x = x ^ a) →
      ∃ t : ℕ, ((3 * t + 1) ^ 3 = p ^ F ∨ (3 * t + 1) ^ 3 = (p ^ F) ^ 2) ∧
        ∀ u : Kˣ, Units.map (σ : K →* K) u = u ^ (3 * t + 1) := by
    intro a ha hσa
    have ha3 := hmod a ha
    refine ⟨a / 3, by rwa [show 3 * (a / 3) + 1 = a by omega], fun u => Units.ext ?_⟩
    rw [Units.coe_map, show 3 * (a / 3) + 1 = a by omega, Units.val_pow_eq_pow_val]
    exact hσa u
  rcases hσf with hσf | hσf
  · refine hform (p ^ (F / 3)) (Or.inl ?_) hσf
    rw [← pow_mul]
    congr 1
    omega
  · refine hform (p ^ (2 * F / 3)) (Or.inr ?_) hσf
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega

section Linear

variable {K : Type} [Field K]

theorem det_scalar_three148 (c : Kˣ) :
    GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) = c ^ 3 := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, scalar_apply,
    det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Units.val_pow_eq_pow_val]

theorem isInnerAut_conjAut_of_det_eq_cube148 (A : GL (Fin 3) K) {u : Kˣ}
    (hu3 : u ^ 3 = GeneralLinearGroup.det A) : IsInnerAut (conjAut 3 K A) := by
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, det_scalar_three148, ← hu3, inv_pow, inv_mul_cancel]
  have hrange : B ∈ (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  obtain ⟨g, hg⟩ := hrange
  have hAB : conjAut 3 K A = conjAut 3 K B := by rw [hB, map_mul, conjAut_scalar, one_mul]
  rw [hAB, ← hg, ← conj_proj_eq_conjAut]
  exact isInnerAut_conj _

theorem map_eq_glAut148 (σ : K ≃+* K) (A : GL (Fin 3) K) :
    GeneralLinearGroup.map (σ : K →+* K) A = glAut σ A :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem glAut_scalar148 (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  refine Units.ext ?_
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
    scalar_apply, diagonal_map (map_zero σ), Units.coe_map]
  rfl

theorem det_glAut148 (σ : K ≃+* K) (A : GL (Fin 3) K) :
    GeneralLinearGroup.det (glAut σ A) = Units.map (σ : K →* K) (GeneralLinearGroup.det A) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, coe_glAut, Units.coe_map, GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (σ : K →+* K) _).symm

theorem scalar_injective148 : Function.Injective
    (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro a b hab
  have h := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) 0 0) hab
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at h
  exact Units.ext h

theorem norm_eq_one_of_glAut_eq148 {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) {A : GL (Fin 3) K} {c : Kˣ}
    (hA : glAut σ A = GeneralLinearGroup.scalar (Fin 3) c * A) :
    c * Units.map (σ : K →* K) c * Units.map (σ : K →* K) (Units.map (σ : K →* K) c) = 1 := by
  have h3 : glAut σ (glAut σ (glAut σ A)) = A := by
    have h := congrArg (fun τ : MulAut (GL (Fin 3) K) => τ A) (map_pow glAut σ 3)
    simp only [hσ3, map_one, MulAut.one_apply, pow_succ, pow_zero, one_mul,
      MulAut.mul_apply] at h
    exact h.symm
  rw [hA, map_mul, hA, map_mul, map_mul, hA, glAut_scalar148, glAut_scalar148] at h3
  have h4 : GeneralLinearGroup.scalar (Fin 3)
      (Units.map (σ : K →* K) (Units.map (σ : K →* K) c) * Units.map (σ : K →* K) c * c) = 1 := by
    rw [map_mul, map_mul]
    have h5 := h3
    rw [← mul_assoc, ← mul_assoc] at h5
    exact mul_eq_right.mp h5
  have h6 := scalar_injective148 (h4.trans (map_one _).symm)
  rw [← h6]
  ac_rfl

theorem exists_glAut_eq_scalar_mul148 [Finite K] (σ : K ≃+* K) (A : GL (Fin 3) K)
    (h : conjAut 3 K A * fieldAut 3 K σ = fieldAut 3 K σ * conjAut 3 K A) :
    ∃ c : Kˣ, glAut σ A = GeneralLinearGroup.scalar (Fin 3) c * A := by
  rw [fieldAut_mul_conjAut] at h
  have h1 : conjAut 3 K A = conjAut 3 K (GeneralLinearGroup.map (σ : K →+* K) A) :=
    mul_right_cancel h
  have h2 : conjAut 3 K (GeneralLinearGroup.map (σ : K →+* K) A * A⁻¹) * fieldAut 3 K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, ← h1, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one le_rfl _ 1 h2
  refine ⟨c, ?_⟩
  rw [← map_eq_glAut148, hc, inv_mul_cancel_right]

theorem exists_cube_det_of_commute148 [Finite K] {p F : ℕ} (hp : p.Prime) (hF : 1 ≤ F)
    (hcard : Nat.card K = p ^ F) (hK : p ^ F % 3 = 1) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (A : GL (Fin 3) K)
    (h : conjAut 3 K A * fieldAut 3 K σ = fieldAut 3 K σ * conjAut 3 K A) :
    ∃ u : Kˣ, u ^ 3 = GeneralLinearGroup.det A := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := exists_glAut_eq_scalar_mul148 σ A h
  have hN := norm_eq_one_of_glAut_eq148 hσ3 hc
  obtain ⟨t, ht, hσu⟩ := exists_pow_form148 hp hF hcard hK hσ
  set d := GeneralLinearGroup.det A with hd
  have hdσ : d ^ (3 * t + 1) = c ^ 3 * d := by
    rw [← hσu, hd, ← det_glAut148, hc, map_mul, det_scalar_three148]
  have hcN : c ^ (1 + (3 * t + 1) + (3 * t + 1) ^ 2) = 1 := by
    rw [hσu, hσu, ← pow_mul] at hN
    rw [pow_add, pow_add, pow_one, sq]
    exact hN
  have hX := pow_eq_one_of_twisted148 hdσ hcN
  set q := p ^ F with hq
  have hcardU : Nat.card Kˣ = q - 1 := by rw [Nat.card_units, hcard]
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have h3 : 3 ∣ q - 1 := by omega
  have hd3 : d ^ ((q - 1) / 3) = 1 := by
    rcases ht with ht | ht
    · rwa [show (q - 1) / 3 = 3 * t * (3 * t ^ 2 + 3 * t + 1) by
        have : q - 1 = 3 * (3 * t * (3 * t ^ 2 + 3 * t + 1)) := by
          have h' : (3 * t + 1) ^ 3 = 3 * (3 * t * (3 * t ^ 2 + 3 * t + 1)) + 1 := by ring
          omega
        omega]
    · have hdq : d ^ (q - 1) = 1 := by rw [← hcardU]; exact pow_card_eq_one'
      refine eq_one_of_pow_three_of_coprime148 (r := q + 1) ?_ ?_ ?_
      · rw [← pow_mul, Nat.div_mul_cancel h3, hdq]
      · rw [← pow_mul]
        convert hX using 2
        have h' : (3 * t + 1) ^ 3 = 3 * (3 * t * (3 * t ^ 2 + 3 * t + 1)) + 1 := by ring
        have h'' : q ^ 2 - 1 = (q - 1) * (q + 1) := by
          have : q ^ 2 = (q - 1) * (q + 1) + 1 := by
            obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
            rw [hr, Nat.add_sub_cancel]
            ring
          omega
        have h''' : 3 * (3 * t * (3 * t ^ 2 + 3 * t + 1)) = (q - 1) * (q + 1) := by omega
        obtain ⟨r, hr⟩ := h3
        rw [hr, Nat.mul_div_cancel_left r (by norm_num)]
        rw [hr] at h'''
        nlinarith
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  obtain ⟨u, -, hu⟩ := exists_cube_of_pow_div_three148 (G := Kˣ) (m := q - 1)
    (by rw [hcardU]) h3 hd3
  exact ⟨u, hu⟩

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem isInnerAut_psuConj_of_det_eq_cube148 (A : unitaryIsom3 h) {u : Kˣ}
    (hu3 : u ^ 3 = GeneralLinearGroup.det (A : GL (Fin 3) K)) (hun : u ^ (p ^ f + 1) = 1) :
    IsInnerAut (psuConj h A) := by
  have hscal : ∀ v : Kˣ, v ^ (p ^ f + 1) = 1 →
      GeneralLinearGroup.scalar (Fin 3) v ∈ unitaryIsom3 h := by
    intro v hv
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, scalar_apply,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have hv' : h.bar (v : K) * v = 1 := by
      rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hv, Units.val_one]
    simp only [hv']
    exact Matrix.diagonal_one
  have hsu : GeneralLinearGroup.scalar (Fin 3) u⁻¹ ∈ unitaryIsom3 h :=
    hscal _ (by rw [inv_pow, hun, inv_one])
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hBI : B ∈ unitaryIsom3 h := mul_mem hsu A.2
  have hdet : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, det_scalar_three148, ← hu3, inv_pow, inv_mul_cancel]
  have hBSU : B ∈ unitarySU p f K 3 := by
    refine (mem_unitarySU_iff h).mpr ⟨?_, hBI⟩
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  have hAB : psuConj h A = psuConj h ⟨B, hBI⟩ := by
    have : (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨_, hsu⟩ * A := rfl
    rw [this, map_mul, psuConj_scalar, one_mul]
  rw [hAB, show (⟨B, hBI⟩ : unitaryIsom3 h) = ⟨(⟨B, hBSU⟩ : unitarySU p f K 3),
    unitarySU_le_unitaryIsom3 hBSU⟩ from rfl, ← conj_mk_eq_psuConj]
  exact isInnerAut_conj _

theorem exists_glAut_eq_scalar_mul_psu148 (σ : K ≃+* K) (A : unitaryIsom3 h)
    (hc : psuConj h A * psuField h σ = psuField h σ * psuConj h A) :
    ∃ c : Kˣ, glAut σ (A : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c * (A : GL (Fin 3) K) := by
  have h1 : psuConj h ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ = psuConj h A := by
    rw [← psuField_mul_psuConj_mul_inv, ← hc, mul_inv_cancel_right]
  have h2 : psuConj h (⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ * A⁻¹) * psuField h 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨-, c, -, hc'⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ 1 h2
  refine ⟨c, ?_⟩
  have h3 : glAut σ (A : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c := hc'
  rw [← h3, inv_mul_cancel_right]

theorem exists_cube_det_of_commute_psu148 (hq : p ^ f % 3 = 2) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (A : unitaryIsom3 h)
    (hc : psuConj h A * psuField h σ = psuField h σ * psuConj h A) :
    ∃ u : Kˣ, u ^ (p ^ f + 1) = 1 ∧ u ^ 3 = GeneralLinearGroup.det (A : GL (Fin 3) K) := by
  have := h.finite
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  obtain ⟨c, hcA⟩ := exists_glAut_eq_scalar_mul_psu148 σ A hc
  have hN := norm_eq_one_of_glAut_eq148 hσ3 hcA
  set q := p ^ f with hqdef
  have hK : p ^ (2 * f) % 3 = 1 := by
    rw [pow_mul', Nat.pow_mod, ← hqdef, hq]
  obtain ⟨t, ht, hσu⟩ := exists_pow_form148 h.prime (by have := h.one_le; omega) h.card hK hσ
  set d := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd
  have hdσ : d ^ (3 * t + 1) = c ^ 3 * d := by
    rw [← hσu, hd, ← det_glAut148, hcA, map_mul, det_scalar_three148]
  have hcN : c ^ (1 + (3 * t + 1) + (3 * t + 1) ^ 2) = 1 := by
    rw [hσu, hσu, ← pow_mul] at hN
    rw [pow_add, pow_add, pow_one, sq]
    exact hN
  have hX := pow_eq_one_of_twisted148 hdσ hcN
  have hdq : d ^ (q + 1) = 1 := det_pow_succ_eq_one_of_mem_unitaryIsom3 h A.2
  have hq2 : 2 ≤ q := h.prime.two_le.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have h3 : 3 ∣ q + 1 := by omega
  obtain ⟨r, hr⟩ := h3
  have hpow2 : p ^ (2 * f) = q ^ 2 := by rw [pow_mul', hqdef]
  have hd3 : d ^ ((q + 1) / 3) = 1 := by
    rw [hr, Nat.mul_div_cancel_left r (by norm_num)]
    have he3 : (d ^ r) ^ 3 = 1 := by rw [← pow_mul, mul_comm, ← hr, hdq]
    have h' : (3 * t + 1) ^ 3 = 3 * (3 * t * (3 * t ^ 2 + 3 * t + 1)) + 1 := by ring
    set X := 3 * t * (3 * t ^ 2 + 3 * t + 1) with hXdef
    obtain ⟨s, hs⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    have hs2 : s + 2 = 3 * r := by omega
    rcases ht with ht | ht
    ·
      rw [hpow2, hs] at ht
      refine eq_one_of_pow_three_of_coprime148 (r := q - 1) he3 ?_
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
      rw [← pow_mul]
      convert hX using 2
      rw [hs, Nat.add_sub_cancel]
      have h1 : s * (s + 2) = 3 * X := by nlinarith
      rw [hs2] at h1
      nlinarith
    ·
      rw [hpow2, hs] at ht
      refine eq_one_of_pow_three_of_coprime148 (r := (q - 1) * (q ^ 2 + 1)) he3 ?_ ?_
      · rw [← pow_mul]
        convert hX using 2
        rw [hs, Nat.add_sub_cancel]
        have h1 : s * (s + 2) * ((s + 1) ^ 2 + 1) = 3 * X := by nlinarith
        rw [hs2] at h1
        nlinarith
      · refine Nat.Coprime.mul_right
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega))
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
        intro h3
        have : (q ^ 2 + 1) % 3 = 2 := by rw [Nat.add_mod, Nat.pow_mod, hq]
        omega
  have hcardU : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, h.card, hpow2]
  have hm : q + 1 ∣ Nat.card Kˣ := by
    rw [hcardU]
    refine ⟨q - 1, ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = (s + 1 + 1) * s + 1 := by ring
    omega
  exact exists_cube_of_pow_div_three148 (G := Kˣ) hm ⟨r, hr⟩ hd3

end Unitary

end Item148Rank

end CFSG.RankThree.PartTwo.Sec14
