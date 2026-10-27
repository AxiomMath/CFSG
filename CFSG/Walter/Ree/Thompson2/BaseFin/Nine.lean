module

public import CFSG.Walter.Ree.Thompson2.BaseFin.Codes

public section

namespace CFSG.Walter.Ree.T2.BaseFin

open BaseRel

@[expose] noncomputable def condT (t : ℕ) : Bool :=
  and (peq [1, t] [t, 1]) (and (! peq [t] []) (peq (List.replicate 3 t) []))

@[expose] noncomputable def condW (t w : ℕ) : Bool :=
  and (peq [1, w, 1] [pinv w]) (and (! peq [w] []) (and (peq (List.replicate 3 w) [])
    (and (peq [t, w] [w, t]) (and (! peq [w] [t]) (! peq [w] [t, t])))))

@[expose] noncomputable def resNine (t w e : ℕ) : Bool :=
  and (peq (List.replicate 9 e) []) (and (! peq (List.replicate 3 e) [])
    (and (or (peq (List.replicate 3 e) [w]) (peq (List.replicate 3 e) [pinv w]))
      (and (anyFrom (fun m => peq [pinv t, e, t] (List.replicate m e)) 0 9)
        (peq [1, e, 1] [pinv e]))))

@[expose] def nineTab : List (ℕ × ℕ × ℕ) :=
  [(3, 87, 5), (3, 97, 5), (4, 87, 5), (4, 97, 5), (12, 1494, 497), (12, 1499, 497), (13, 671, 558),
   (13, 746, 558), (16, 671, 558), (16, 746, 558), (19, 1494, 497), (19, 1499, 497), (48, 465, 54),
   (48, 491, 54), (51, 465, 54), (51, 491, 54)]

@[expose] def nineE (t w : ℕ) : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | p :: l => cond (and (Nat.beq p.1 t) (Nat.beq p.2.1 w)) p.2.2 (nineE t w l)

@[expose] noncomputable def nineOK : Bool :=
  allFrom (fun t => or (! condT t) (allFrom (fun w => or (! condW t w)
    (resNine t w (nineE t w nineTab))) 0 1512)) 0 1512

theorem nineOK_eq : nineOK = true := by decide +kernel

theorem nine_of_j {t w : PGammaL28} (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1)
    (hjt : PGammaL28.j * t = t * PGammaL28.j) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (htw : t * w = w * t) (hjw : PGammaL28.j * w * PGammaL28.j = w⁻¹)
    (hwt : w ∉ Subgroup.zpowers t) :
    ∃ e : PGammaL28, e ^ 9 = 1 ∧ e ^ 3 ≠ 1 ∧ (e ^ 3 = w ∨ e ^ 3 = w⁻¹) ∧
      t⁻¹ * e * t ∈ Subgroup.zpowers e ∧ PGammaL28.j * e * PGammaL28.j = e⁻¹ := by
  obtain ⟨it, hit, rfl⟩ := exists_pg t
  obtain ⟨iw, hiw, rfl⟩ := exists_pg w
  have hT : condT it = true := by
    simp only [condT, Bool.and_eq_true, Bool.not_eq_true', peq_iff, peq_false_iff, ppg_cons,
      ppg_nil, ppg_replicate, mul_one, pg_one]
    exact ⟨hjt, ht1, ht3⟩
  have hW : condW it iw = true := by
    simp only [condW, Bool.and_eq_true, Bool.not_eq_true', peq_iff, peq_false_iff, ppg_cons,
      ppg_nil, ppg_replicate, mul_one, pg_one, pg_pinv, ← mul_assoc]
    refine ⟨hjw, hw1, hw3, htw, fun h => hwt (h ▸ Subgroup.mem_zpowers _), fun h => hwt ?_⟩
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have h := of_allFrom nineOK_eq it (Nat.zero_le _) (by omega)
  simp only [hT, Bool.not_true, Bool.false_or] at h
  have h' := of_allFrom h iw (Nat.zero_le _) (by omega)
  simp only [hW, Bool.not_true, Bool.false_or] at h'
  set ie := nineE it iw nineTab
  simp only [resNine, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', peq_iff,
    peq_false_iff, ppg_cons, ppg_nil, ppg_replicate, mul_one, pg_one, pg_pinv,
    ← mul_assoc] at h'
  obtain ⟨h9, h3, hw, hn, hj⟩ := h'
  obtain ⟨m, -, -, hm⟩ := of_anyFrom hn
  rw [peq_iff] at hm
  simp only [ppg_cons, ppg_nil, ppg_replicate, mul_one, pg_pinv, ← mul_assoc] at hm
  exact ⟨pg ie, h9, h3, hw, Subgroup.mem_zpowers_iff.mpr ⟨m, by rw [zpow_natCast, hm]⟩, hj⟩

theorem nine_lemma {a t w : PGammaL28} (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (ht3 : t ^ 3 = 1)
    (ht1 : t ≠ 1) (hat : a * t = t * a) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (htw : t * w = w * t)
    (haw : a * w * a = w⁻¹) (hwt : w ∉ Subgroup.zpowers t) :
    ∃ e : PGammaL28, e ^ 9 = 1 ∧ e ^ 3 ≠ 1 ∧ (e ^ 3 = w ∨ e ^ 3 = w⁻¹) ∧
      t⁻¹ * e * t ∈ Subgroup.zpowers e ∧ a * e * a = e⁻¹ := by
  obtain ⟨g, rfl⟩ := exists_conj_j ha2 ha1
  set φ := MulAut.conj g
  have hφ : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
  have hφs : ∀ x, φ.symm x = g⁻¹ * x * g := fun x => by
    rw [MulEquiv.symm_apply_eq, hφ]; group
  have hφa : φ (g⁻¹ * PGammaL28.j * g) = PGammaL28.j := by rw [hφ]; group
  have hne : ∀ {x y : PGammaL28}, x ≠ y → φ x ≠ φ y := fun h => φ.injective.ne h
  obtain ⟨e, h9, h3, hw, hn, hj⟩ := nine_of_j (t := φ t) (w := φ w)
    (by rw [← map_pow, ht3, map_one]) (by rw [← map_one φ]; exact hne ht1)
    (by rw [← hφa, ← map_mul, ← map_mul, hat]) (by rw [← map_pow, hw3, map_one])
    (by rw [← map_one φ]; exact hne hw1) (by rw [← map_mul, ← map_mul, htw])
    (by rw [← hφa, ← map_mul, ← map_mul, haw, map_inv])
    (by
      rintro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← map_zpow] at hk
      exact hwt (Subgroup.mem_zpowers_iff.mpr ⟨k, φ.injective hk⟩))
  refine ⟨φ.symm e, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h9, map_one]
  · rw [← map_pow, ← map_one φ.symm]
    exact φ.symm.injective.ne h3
  · rcases hw with hw | hw
    · left; rw [← map_pow, hw, MulEquiv.symm_apply_apply]
    · right; rw [← map_pow, hw, map_inv, MulEquiv.symm_apply_apply]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow, hk, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  · have := congrArg φ.symm hj
    rw [map_mul, map_mul, map_inv, ← hφa, MulEquiv.symm_apply_apply] at this
    exact this

end CFSG.Walter.Ree.T2.BaseFin
