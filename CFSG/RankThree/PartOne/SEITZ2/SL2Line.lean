module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP

section Traces

variable {F : Type} [Field F] [CharP F 2]

theorem trace_one_sl2 : Matrix.trace ((1 : SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.trace_one]
  simpa using (CharTwo.two_eq_zero : (2 : F) = 0)

theorem trace_line_sq (a : F) :
    Matrix.trace (((u2 (1 : F) * l2 a) ^ 2 : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = a ^ 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_two]
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (1 + 2 * a) * h2

theorem trace_line_cube (a : F) :
    Matrix.trace (((u2 (1 : F) * l2 a) ^ 3 : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = a ^ 3 + a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_succ, pow_two]
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (3 * a ^ 2 + 4 * a + 1) * h2

theorem trace_line_five (a : F) :
    Matrix.trace (((u2 (1 : F) * l2 a) ^ 5 : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = a ^ 5 + a ^ 3 + a := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [show (5 : ℕ) = 2 + 2 + 1 by norm_num, pow_succ, pow_add, pow_two]
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (5 * a ^ 4 + 17 * a ^ 3 + 25 * a ^ 2 + 12 * a + 1) * h2

end Traces

section Roots

variable {F : Type} [Field F]

@[expose] def rootHom1 (k : Subfield F) : Multiplicative k →* SpecialLinearGroup (Fin 2) F where
  toFun c := u2 ((c.toAdd : k) : F)
  map_one' := by simp [u2_zero]
  map_mul' c d := by
    rw [← u2_add]
    congr 1

theorem rootHom1_injective (k : Subfield F) : Function.Injective (rootHom1 k) := by
  intro c d hcd
  have h := u2_injective hcd
  exact Multiplicative.toAdd.injective (Subtype.ext h)

theorem card_dvd_card_of_root_line {k : Subfield F} {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c ∈ k, u2 c ∈ M) : Nat.card k ∣ Nat.card M := by
  have hle : (rootHom1 k).range ≤ M := by
    rintro _ ⟨c, rfl⟩
    exact hu _ c.toAdd.2
  have hcard : Nat.card (rootHom1 k).range = Nat.card k := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (rootHom1_injective k)).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end Roots

theorem alternating_five_orders :
    ∀ x : alternatingGroup (Fin 5), x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

theorem mem_of_pow_four_eq_self {F : Type} [Field F] [Finite F] {k : Subfield F}
    (hk : Nat.card k = 4) {a : F} (ha : a ^ 4 = a) : a ∈ k := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype k := Fintype.ofFinite k
  have hck : ∀ c : k, (c : F) ^ 4 = c := by
    intro c
    have h := FiniteField.pow_card c
    rw [← Nat.card_eq_fintype_card, hk] at h
    have h' := congrArg (fun z : k => (z : F)) h
    simpa using h'
  set P : Polynomial F := Polynomial.X ^ 4 - Polynomial.X with hP
  have hdeg : P.natDegree = 4 := FiniteField.X_pow_card_sub_X_natDegree_eq F (by norm_num)
  have hP0 : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have hS : P.roots.toFinset.card ≤ 4 :=
    (Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' P)
  set T : Finset F := Finset.univ.map ⟨((↑) : k → F), Subtype.val_injective⟩ with hT
  have hTcard : T.card = 4 := by
    rw [hT, Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card, hk]
  have hTS : T ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_map.1 hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hck c]
  have hEq : T = P.roots.toFinset := Finset.eq_of_subset_of_card_le hTS (hTcard ▸ hS)
  have haS : a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, ha]
  rw [← hEq] at haS
  obtain ⟨c, -, hc⟩ := Finset.mem_map.1 haS
  exact hc ▸ c.2

section Dickson


open CFSG.Glauberman.Dickson

theorem witness_eq_top_line {F : Type} [Field F] [Finite F] [CharP F 2] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hK : Nat.card F = Nat.card k ^ d) {a : F} (ha : a ∉ k)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (hu : ∀ c ∈ k, u2 c ∈ M)
    (hl : ∀ c ∈ k, l2 (c * a) ∈ M) {m : ℕ}
    (W : SubfieldConjugacyWitness 2 m (M.map (mkPSL F))) : W.K = ⊤ := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ k.zero_mem)
  have hl1 : l2 a ∈ M := by simpa using hl 1 k.one_mem
  have hu1 : u2 (1 : F) ∈ M := hu 1 k.one_mem
  have key : ∀ x y : F, u2 x ∈ M → u2 y ∈ M → x ≠ 0 → (y / x) ^ 2 ∈ W.K := by
    intro x y hx hy hx0
    have hAM : u2 x * l2 a ∈ M := M.mul_mem hx hl1
    have hBM : u2 y * l2 a * u2 (x + y) ∈ M :=
      M.mul_mem (M.mul_mem hy hl1) (by rw [u2_add]; exact M.mul_mem hx hy)
    have hxb : x * a ≠ 0 := mul_ne_zero hx0 ha0
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F (u2 x * l2 a), Subgroup.mem_map_of_mem _ hAM⟩
      ⟨mkPSL F (u2 y * l2 a * u2 (x + y)), Subgroup.mem_map_of_mem _ hBM⟩
      (u2 x * l2 a) (u2 y * l2 a * u2 (x + y)) rfl rfl
      (by rw [trace_u2_mul_l2]; exact hxb)
      (by rw [trace_u2_mul_l2_mul_u2]; exact hxb)
    rw [trace_pair, trace_u2_mul_l2, trace_u2_mul_l2_mul_u2] at h
    have : y ^ 2 * a ^ 2 / (x * a * (x * a)) = (y / x) ^ 2 := by
      field_simp
    rwa [this] at h
  have hkW : k ≤ W.K := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]
      exact W.K.zero_mem
    · have h := key 1 c hu1 (hu c hc) one_ne_zero
      rw [div_one] at h
      exact mem_subfield_of_sq_mem W.K h
  have haW : a ∈ W.K := by
    set A : SpecialLinearGroup (Fin 2) F := u2 1 * l2 a with hA
    have hAM : A ∈ M := M.mul_mem hu1 hl1
    have hBM : A ^ 2 ∈ M := M.pow_mem hAM 2
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F A, Subgroup.mem_map_of_mem _ hAM⟩
      ⟨mkPSL F (A ^ 2), Subgroup.mem_map_of_mem _ hBM⟩ A (A ^ 2) rfl rfl
      (by rw [hA, trace_u2_mul_l2, one_mul]; exact ha0)
      (by rw [hA, trace_line_sq]; exact pow_ne_zero 2 ha0)
    have hA3 : A * A ^ 2 = A ^ 3 := by rw [← pow_succ']
    rw [hA3, hA, trace_line_cube, trace_line_sq, trace_u2_mul_l2, one_mul] at h
    have h1 : (a ^ 3 + a) / (a * a ^ 2) = 1 + (a⁻¹) ^ 2 := by
      field_simp
    rw [h1] at h
    have h2 : (a⁻¹) ^ 2 ∈ W.K := by
      have := W.K.sub_mem h W.K.one_mem
      simpa using this
    have h3 : a⁻¹ ∈ W.K := mem_subfield_of_sq_mem W.K h2
    simpa using W.K.inv_mem h3
  rcases subfield_eq_or_eq_top hkW hd hK with h | h
  · exact absurd (h ▸ haW) ha
  · exact h

theorem sl2_eq_top_of_root_lines {F : Type} [Field F] [Finite F] [CharP F 2] {k : Subfield F}
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hK : Nat.card F = Nat.card k ^ d)
    (hk4 : 4 ∣ Nat.card k) {a : F} (ha : a ∉ k)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (hu : ∀ c ∈ k, u2 c ∈ M)
    (hl : ∀ c ∈ k, l2 (c * a) ∈ M) : M = ⊤ := by
  classical
  obtain ⟨f, hf1, hF⟩ := exists_card_eq_two_pow F
  obtain ⟨m₀, hm₀1, hk⟩ := exists_card_eq_two_pow k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := mkPSL_injective (F := F)
  have ha0 : a ≠ 0 := fun h => ha (h ▸ k.zero_mem)
  have hxM : u2 (1 : F) ∈ M := hu 1 k.one_mem
  have hyM : l2 a ∈ M := by simpa using hl 1 k.one_mem
  have hHcard : Nat.card (M.map (mkPSL F)) = Nat.card M := Subgroup.card_map_of_injective hinj
  have hdodd : Odd d := hd.odd_of_ne_two hd2
  have hfm : f = m₀ * d := by
    have h : 2 ^ f = 2 ^ (m₀ * d) := by rw [← hF, hK, hk, ← pow_mul]
    exact Nat.pow_right_injective (le_refl 2) h
  have h4 : 4 ∣ Nat.card M := hk4.trans (card_dvd_card_of_root_line hu)
  have hFodd : Odd (2 ^ f - 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    rcases h1 with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hFodd' : Odd (2 ^ f + 1) := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    rcases h1 with ⟨c, hc⟩
    exact ⟨c, by omega⟩
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hFodd.not_two_dvd_nat)
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  let x : H := ⟨mkPSL F (u2 1), Subgroup.mem_map_of_mem _ hxM⟩
  let y : H := ⟨mkPSL F (l2 a), Subgroup.mem_map_of_mem _ hyM⟩
  have hxy : x * y ≠ y * x := by
    intro h
    have h' := congrArg Subtype.val h
    apply u2_mul_l2_ne (mul_ne_zero one_ne_zero ha0)
    apply hinj
    rw [map_mul, map_mul]
    exact h'
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simp [x, pow_two, ← map_mul, u2_mul_self]
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simp [y, pow_two, ← map_mul, l2_mul_self]
  have hcomm : ∀ {z : ℕ}, z ∣ 2 ^ f - 1 ∨ z ∣ 2 ^ f + 1 → Odd z := fun {z} hz =>
    hz.elim (fun h => Odd.of_dvd_nat hFodd h) (fun h => Odd.of_dvd_nat hFodd' h)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := 2) (f := f) hF
      H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, -⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  ·
    have hzodd : Odd z := by
      simp only [hF, hg, Nat.div_one] at hz
      exact hcomm hz
    have h42 : 4 ∣ 2 * z := by rw [← hcard, hHcard]; exact h4
    obtain ⟨c, hc⟩ := hzodd
    omega
  · exact absurd (by
      have := alternating_four_involutions_comm (e x) (e y) (by rw [← map_pow, hx2, map_one])
        (by rw [← map_pow, hy2, map_one])
      exact e.injective (by rw [map_mul, map_mul]; exact this)) hxy
  · exfalso
    have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ (2 * f) := Nat.one_le_two_pow
    omega
  ·
    exfalso
    have h60 : Nat.card M = 60 := by
      rw [← hHcard, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    have hkdvd : Nat.card k ∣ 60 := h60 ▸ card_dvd_card_of_root_line hu
    have hk2 : Nat.card k = 4 := by
      have hle : 2 ^ m₀ ≤ 60 := Nat.le_of_dvd (by norm_num) (hk ▸ hkdvd)
      have hm6 : m₀ < 6 := by
        by_contra hcon
        push Not at hcon
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hcon
        omega
      have h4' : 4 ∣ 2 ^ m₀ := hk ▸ hk4
      rw [hk]
      interval_cases m₀ <;> simp_all
    set g : SpecialLinearGroup (Fin 2) F := u2 1 * l2 a with hgdef
    have hgM : g ∈ M := M.mul_mem hxM hyM
    let gH : H := ⟨mkPSL F g, Subgroup.mem_map_of_mem _ hgM⟩
    have hord : g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
      have hpow : ∀ n : ℕ, gH ^ n = 1 → g ^ n = 1 := by
        intro n hn
        apply hinj
        have := congrArg Subtype.val hn
        simpa [gH, map_pow] using this
      rcases alternating_five_orders (e gH) with h | h | h
      · exact Or.inl (hpow 2 (e.injective (by rw [map_pow, h, map_one])))
      · exact Or.inr (Or.inl (hpow 3 (e.injective (by rw [map_pow, h, map_one]))))
      · exact Or.inr (Or.inr (hpow 5 (e.injective (by rw [map_pow, h, map_one]))))
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have htr : ∀ n : ℕ, g ^ n = 1 → Matrix.trace (((g ^ n : SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) = 0 := fun n hn => by rw [hn, trace_one_sl2]
    rcases hord with h | h | h
    · have h' := htr 2 h
      rw [hgdef, trace_line_sq] at h'
      exact ha ((pow_eq_zero_iff two_ne_zero).1 h' ▸ k.zero_mem)
    · have h' := htr 3 h
      rw [hgdef, trace_line_cube] at h'
      have h1 : a * (a + 1) ^ 2 = 0 := by linear_combination h' + a ^ 2 * h2
      rcases mul_eq_zero.1 h1 with h0 | h0
      · exact ha (h0 ▸ k.zero_mem)
      · have h3 : a + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h0
        have h4 : a = 1 := by linear_combination h3 - h2
        exact ha (h4 ▸ k.one_mem)
    · have h' := htr 5 h
      rw [hgdef, trace_line_five] at h'
      have h1 : a * (a ^ 2 + a + 1) ^ 2 = 0 := by
        linear_combination h' + (a ^ 4 + a ^ 3 + a ^ 2) * h2
      rcases mul_eq_zero.1 h1 with h0 | h0
      · exact ha (h0 ▸ k.zero_mem)
      · have h3 : a ^ 2 + a + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h0
        have h4 : a ^ 4 = a := by linear_combination a * (a - 1) * h3
        exact ha (mem_of_pow_four_eq_self hk2 h4)
  ·
    exfalso
    have htodd : Odd t :=
      Odd.of_dvd_nat hFodd (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)))
    have := hN
    have hxN : x ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hx2
    have hyN : y ∈ N := mem_of_sq_eq_one_of_sup hdisj hsup (hCcard ▸ htodd) hy2
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxy (congrArg Subtype.val hcN)
  ·
    have hWK : W.K = ⊤ := witness_eq_top_line hd hK ha hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have e2 : GaloisField 2 m ≃+* F := by
      have := Fintype.ofFinite (GaloisField 2 m)
      have := Fintype.ofFinite F
      exact FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card 2 m hm0, hmf'])
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      rw [Nat.card_congr eP.toEquiv]
      exact Nat.card_congr (h826_pslEquiv e2).toEquiv
    have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcardH
    refine eq_top_iff.2 fun g _ => ?_
    have hg' : mkPSL F g ∈ H := hHtop ▸ Subgroup.mem_top _
    obtain ⟨g', hg'M, hgg'⟩ := Subgroup.mem_map.mp hg'
    rwa [← hinj hgg']
  ·
    exfalso
    have hWK : W.K = ⊤ := witness_eq_top_line hd hK ha hu hl W
    have hmf' : m = f := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective (le_refl 2) h1
    have := Nat.le_of_dvd (by omega) hmf
    omega

end Dickson

end CFSG.RankThree.PartOne.SEITZ2
