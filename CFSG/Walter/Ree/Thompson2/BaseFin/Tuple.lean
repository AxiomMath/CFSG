module

public import CFSG.Walter.Ree.Thompson2.BaseFin.Codes

public section

namespace CFSG.Walter.Ree.T2.BaseFin

open BaseRel

@[expose] noncomputable def condB (b : ℕ) : Bool :=
  and (peq [1, b] [b, 1]) (and (! peq [b] []) (and (! peq [b] [1]) (peq [b, b] [])))

@[expose] noncomputable def condC (b c : ℕ) : Bool :=
  and (peq [1, c] [c, 1]) (and (! peq [c] []) (and (peq (List.replicate 3 c) [])
    (peq [b, c, b, c, b, c] [])))

@[expose] noncomputable def condE (c e : ℕ) : Bool :=
  and (peq [1, e, 1] [pinv e]) (and (peq (List.replicate 9 e) [])
    (and (! peq (List.replicate 3 e) []) (peq [pinv c, e, c] [pinv e, pinv e])))

@[expose] noncomputable def resTup (b c e g k : ℕ) : Bool :=
  and (or (Nat.beq k 1) (or (Nat.beq k 4) (Nat.beq k 7))) (and (peq [1] [pinv g, 1, g])
    (and (peq [b] [pinv g, 2, g]) (and (peq [c] [pinv g, 3, g])
      (peq (List.replicate k e) [pinv g, 5, g]))))

@[expose] def tupTab : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(2, 3, 5, 0, 1), (2, 3, 6, 1, 1), (2, 3, 25, 1, 4), (2, 3, 29, 0, 4), (2, 3, 67, 0, 7),
   (2, 3, 70, 1, 7), (2, 12, 497, 62, 7), (2, 12, 507, 112, 7), (2, 12, 1161, 112, 1),
   (2, 12, 1173, 62, 1), (2, 12, 1421, 112, 4), (2, 12, 1428, 62, 4), (2, 16, 558, 71, 4),
   (2, 16, 567, 121, 4), (2, 16, 621, 121, 7), (2, 16, 651, 121, 1), (2, 16, 705, 71, 7),
   (2, 16, 724, 71, 1), (2, 48, 54, 2, 1), (2, 48, 58, 7, 1), (2, 48, 170, 7, 4),
   (2, 48, 180, 2, 4), (2, 48, 418, 2, 7), (2, 48, 423, 7, 7), (62, 3, 5, 4, 4), (62, 3, 6, 9, 4),
   (62, 3, 25, 9, 7), (62, 3, 29, 4, 7), (62, 3, 67, 4, 1), (62, 3, 70, 9, 1), (62, 12, 497, 13, 1),
   (62, 12, 507, 31, 1), (62, 12, 1161, 31, 4), (62, 12, 1173, 13, 4), (62, 12, 1421, 31, 7),
   (62, 12, 1428, 13, 7), (62, 16, 558, 51, 7), (62, 16, 567, 101, 7), (62, 16, 621, 101, 1),
   (62, 16, 651, 101, 4), (62, 16, 705, 51, 1), (62, 16, 724, 51, 4), (62, 48, 54, 19, 4),
   (62, 48, 58, 37, 4), (62, 48, 170, 37, 7), (62, 48, 180, 19, 7), (62, 48, 418, 19, 1),
   (62, 48, 423, 37, 1), (71, 3, 5, 3, 7), (71, 3, 6, 8, 7), (71, 3, 25, 8, 1), (71, 3, 29, 3, 1),
   (71, 3, 67, 3, 4), (71, 3, 70, 8, 4), (71, 12, 497, 48, 4), (71, 12, 507, 98, 4),
   (71, 12, 1161, 98, 7), (71, 12, 1173, 48, 7), (71, 12, 1421, 98, 1), (71, 12, 1428, 48, 1),
   (71, 16, 558, 12, 1), (71, 16, 567, 30, 1), (71, 16, 621, 30, 4), (71, 16, 651, 30, 7),
   (71, 16, 705, 12, 4), (71, 16, 724, 12, 7), (71, 48, 54, 16, 7), (71, 48, 58, 34, 7),
   (71, 48, 170, 34, 1), (71, 48, 180, 16, 1), (71, 48, 418, 16, 4), (71, 48, 423, 34, 4)]

@[expose] def tupFind (b c e : ℕ) : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | p :: l => cond (and (Nat.beq p.1 b) (and (Nat.beq p.2.1 c) (Nat.beq p.2.2.1 e))) p.2.2.2
    (tupFind b c e l)

@[expose] noncomputable def tupOK : Bool :=
  allFrom (fun b => or (! condB b) (allFrom (fun c => or (! condC b c) (allFrom (fun e =>
    or (! condE c e) (resTup b c e (tupFind b c e tupTab).1 (tupFind b c e tupTab).2)) 0 1512))
      0 1512)) 0 1512

theorem tupOK_eq : tupOK = true := by decide +kernel

theorem tuple_of_j {b c e : PGammaL28} (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (hjb : PGammaL28.j ≠ b)
    (hjbc : PGammaL28.j * b = b * PGammaL28.j) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hjc : PGammaL28.j * c = c * PGammaL28.j) (hbc : (b * c) ^ 3 = 1) (he9 : e ^ 9 = 1)
    (he3 : e ^ 3 ≠ 1) (hje : PGammaL28.j * e * PGammaL28.j = e⁻¹)
    (hce : c⁻¹ * e * c = (e ^ 2)⁻¹) :
    ∃ g : PGammaL28, ∃ k ∈ ({1, 4, 7} : Finset ℕ), PGammaL28.j = g⁻¹ * PGammaL28.j * g ∧
      b = g⁻¹ * PGammaL28.k * g ∧ c = g⁻¹ * PGammaL28.t * g ∧
      e ^ k = g⁻¹ * PGammaL28.y * g := by
  obtain ⟨ib, hib, rfl⟩ := exists_pg b
  obtain ⟨ic, hic, rfl⟩ := exists_pg c
  obtain ⟨ie, hie, rfl⟩ := exists_pg e
  have hB : condB ib = true := by
    simp only [condB, Bool.and_eq_true, Bool.not_eq_true', peq_iff, peq_false_iff, ppg_cons,
      ppg_nil, mul_one, pg_one]
    exact ⟨hjbc, hb1, fun h => hjb h.symm, by rw [← sq]; exact hb2⟩
  have hC : condC ib ic = true := by
    simp only [condC, Bool.and_eq_true, Bool.not_eq_true', peq_iff, peq_false_iff, ppg_cons,
      ppg_nil, ppg_replicate, mul_one, pg_one, ← mul_assoc]
    exact ⟨hjc, hc1, hc3, by rw [← hbc, pow_three]; simp only [mul_assoc]⟩
  have hE : condE ic ie = true := by
    simp only [condE, Bool.and_eq_true, Bool.not_eq_true', peq_iff, peq_false_iff, ppg_cons,
      ppg_nil, ppg_replicate, mul_one, pg_one, pg_pinv, ← mul_assoc]
    exact ⟨hje, he9, he3, by rw [hce, sq, mul_inv_rev]⟩
  have h := of_allFrom tupOK_eq ib (Nat.zero_le _) (by omega)
  simp only [hB, Bool.not_true, Bool.false_or] at h
  have h' := of_allFrom h ic (Nat.zero_le _) (by omega)
  simp only [hC, Bool.not_true, Bool.false_or] at h'
  have h'' := of_allFrom h' ie (Nat.zero_le _) (by omega)
  simp only [hE, Bool.not_true, Bool.false_or] at h''
  set g := (tupFind ib ic ie tupTab).1
  set k := (tupFind ib ic ie tupTab).2
  simp only [resTup, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, peq_iff, ppg_cons, ppg_nil,
    ppg_replicate, mul_one, pg_one, pg_two, pg_three, pg_five, pg_pinv, ← mul_assoc] at h''
  obtain ⟨hk, h1, h2, h3, h4⟩ := h''
  refine ⟨pg g, k, ?_, h1, h2, h3, h4⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact hk

theorem tuple_lemma {a b c e : PGammaL28} (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (habc : a * b = b * a) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hac : a * c = c * a) (hbc : (b * c) ^ 3 = 1) (he9 : e ^ 9 = 1) (he3 : e ^ 3 ≠ 1)
    (hae : a * e * a = e⁻¹) (hce : c⁻¹ * e * c = (e ^ 2)⁻¹) :
    ∃ g : PGammaL28, ∃ k ∈ ({1, 4, 7} : Finset ℕ), a = g⁻¹ * PGammaL28.j * g ∧
      b = g⁻¹ * PGammaL28.k * g ∧ c = g⁻¹ * PGammaL28.t * g ∧
      e ^ k = g⁻¹ * PGammaL28.y * g := by
  obtain ⟨g, rfl⟩ := exists_conj_j ha2 ha1
  set φ := MulAut.conj g
  have hφ : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
  have hφs : ∀ x, x = g⁻¹ * φ x * g := fun x => by rw [hφ]; group
  have hφa : φ (g⁻¹ * PGammaL28.j * g) = PGammaL28.j := by rw [hφ]; group
  have hne : ∀ {x y : PGammaL28}, x ≠ y → φ x ≠ φ y := fun h => φ.injective.ne h
  obtain ⟨g', k, hk, h1, h2, h3, h4⟩ := tuple_of_j (b := φ b) (c := φ c) (e := φ e)
    (by rw [← map_pow, hb2, map_one]) (by rw [← map_one φ]; exact hne hb1)
    (by rw [← hφa]; exact hne hab) (by rw [← hφa, ← map_mul, ← map_mul, habc])
    (by rw [← map_pow, hc3, map_one]) (by rw [← map_one φ]; exact hne hc1)
    (by rw [← hφa, ← map_mul, ← map_mul, hac]) (by rw [← map_mul, ← map_pow, hbc, map_one])
    (by rw [← map_pow, he9, map_one]) (by rw [← map_pow, ← map_one φ]; exact hne he3)
    (by rw [← hφa, ← map_mul, ← map_mul, hae, map_inv])
    (by rw [← map_inv, ← map_mul, ← map_mul, hce, map_inv, map_pow])
  refine ⟨g' * g, k, hk, ?_, ?_, ?_, ?_⟩
  · calc g⁻¹ * PGammaL28.j * g = g⁻¹ * (g'⁻¹ * PGammaL28.j * g') * g := by rw [← h1]
      _ = (g' * g)⁻¹ * PGammaL28.j * (g' * g) := by group
  · rw [hφs b, h2]; group
  · rw [hφs c, h3]; group
  · rw [hφs (e ^ k), map_pow, h4]; group

end CFSG.Walter.Ree.T2.BaseFin
