module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelComm

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups Matrix

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open CFSG.QuasithinUnique.Setup.X7
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
  {l : ℕ} (hF : Fintype.card F = 2 ^ (2 * l))

theorem mul_sig_mul_fix (hF : Fintype.card F = 2 ^ (2 * l)) (c a : F)
    (ha : a ^ 2 ^ l = a) :
    (c * c ^ 2 ^ l * a) ^ 2 ^ l = c * c ^ 2 ^ l * a := by
  rw [mul_pow, mul_pow]
  have hc : (c ^ 2 ^ l) ^ 2 ^ l = c := by
    rw [← pow_mul, ← pow_add, ← two_mul, ← hF, FiniteField.pow_card]
  rw [hc, ha]
  ring

private theorem exists_mul_sig_mul_eq (hF : Fintype.card F = 2 ^ (2 * l))
    (a b : F) (ha : a ^ 2 ^ l = a) (hb : b ^ 2 ^ l = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ c * c ^ 2 ^ l * a = b := by
  have hainv : a⁻¹ ^ 2 ^ l = a⁻¹ := by rw [inv_pow, ha]
  have hbdiv : (b * a⁻¹) ^ 2 ^ l = b * a⁻¹ := by rw [mul_pow, hb, hainv]
  obtain ⟨c, hc0, hc⟩ := exists_mul_sig_eq (hF := hF) hbdiv
    (mul_ne_zero hb0 (inv_ne_zero ha0))
  exact ⟨c, hc0, by rw [hc]; field_simp⟩

private theorem inv_tMat (c : F) (hc : c ≠ 0) :
    (tMat c hc)⁻¹ = tMat c⁻¹ (inv_ne_zero hc) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tMat_coe, Matrix.mul_apply, Fin.sum_univ_two, hc]

theorem tMat_mem_normalizer (c : F) (hc : c ≠ 0) :
    tMat c hc ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨t, rfl⟩ := mem_upperSylow_iff.mp hg
    rw [tMat_conj]
    exact mem_upperSylow_iff.mpr ⟨c ^ 2 * t, rfl⟩
  · intro hg
    obtain ⟨t, ht⟩ := mem_upperSylow_iff.mp hg
    have h2 : g = (tMat c hc)⁻¹ * uMat t * tMat c hc := by
      calc g = (tMat c hc)⁻¹ * (tMat c hc * g * (tMat c hc)⁻¹) * tMat c hc := by group
        _ = (tMat c hc)⁻¹ * uMat t * tMat c hc := by rw [ht]
    have hlast : (tMat c⁻¹ (inv_ne_zero hc))⁻¹ = tMat c hc := by
      simpa using (inv_tMat (c⁻¹) (inv_ne_zero hc))
    rw [h2, inv_tMat c hc, ← hlast, tMat_conj]
    exact mem_upperSylow_iff.mpr ⟨(c⁻¹) ^ 2 * t, rfl⟩

theorem hermAct_tMat_hermDiag (c : F) (hc : c ≠ 0) (a : F) (ha : a ^ 2 ^ l = a) :
    hermAct l (sig_sig hF) (tMat c hc) (hermDiag l hF a ha) =
      hermDiag l hF (c * c ^ 2 ^ l * a) (mul_sig_mul_fix (hF := hF) c a ha) := by
  refine hermA_ext ?_ ?_ ?_
  · rw [hermAct_tMat_00, sig_apply, hermDiag_coe, hermDiag_coe]
    simp
  · rw [hermAct_tMat_01, hermDiag_coe, hermDiag_coe]
    simp
  · rw [hermAct_tMat_11, hermDiag_coe, hermDiag_coe]
    simp

theorem normalizer_transitive_fixed (v w : ↥(hermA l F))
    (hv : v ∈ fixedSub (hermRep l hF) upperSylow)
    (hw : w ∈ fixedSub (hermRep l hF) upperSylow) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ n ∈ Subgroup.normalizer (upperSylow (F := F) : Set (SL(2, F))),
      hermRep l hF n v = w := by
  have hv' : v ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
    rwa [← fixedSub_upperSylow (hF := hF)]
  have hw' : w ∈ AddSubgroup.toZModSubmodule (n := 2) (herm1101 l F) := by
    rwa [← fixedSub_upperSylow (hF := hF)]
  obtain ⟨h11, h01⟩ := hv'
  obtain ⟨k11, k01⟩ := hw'
  have hvE : v = hermDiag l hF ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) v) := eq_hermDiag_of_mem_herm1101 (hF := hF) v ⟨h11, h01⟩
  have hwE : w = hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) w) := eq_hermDiag_of_mem_herm1101 (hF := hF) w ⟨k11, k01⟩
  have ha0 : (v : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hv0
    rw [hvE]
    apply Subtype.ext
    have hD : (hermDiag l hF ((v : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) v) :
        Matrix (Fin 2) (Fin 2) F) = !![(v : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  have hb0 : (w : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hw0
    rw [hwE]
    apply Subtype.ext
    have hD : (hermDiag l hF ((w : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) w) :
        Matrix (Fin 2) (Fin 2) F) = !![(w : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
    rw [hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]
  obtain ⟨c, hc0, hc⟩ := exists_mul_sig_mul_eq (hF := hF)
    ((v : Matrix (Fin 2) (Fin 2) F) 0 0) ((w : Matrix (Fin 2) (Fin 2) F) 0 0)
    (hermA_00 (a := l) v) (hermA_00 (a := l) w) ha0 hb0
  refine ⟨tMat c hc0, tMat_mem_normalizer (F := F) c hc0, ?_⟩
  rw [hvE, hwE, hermRep_apply,
    hermAct_tMat_hermDiag (hF := hF) c hc0 ((v : Matrix (Fin 2) (Fin 2) F) 0 0)
      (hermA_00 (a := l) v)]
  apply Subtype.ext
  change (!![c * c ^ 2 ^ l * (v : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] :
    Matrix (Fin 2) (Fin 2) F) = !![(w : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0]
  rw [hc]

theorem hermDiag_one_mem_fixedSub :
    hermDiag l hF 1 (one_pow (2 ^ l)) ∈ fixedSub (hermRep l hF) upperSylow := by
  rw [fixedSub_upperSylow (hF := hF)]
  exact hermDiag_mem_herm1101 (hF := hF) 1 (by simp)

theorem hermAct_hermDiag_one_eq_iff (g : SL(2, F)) :
    hermAct l (sig_sig hF) g (hermDiag l hF 1 (one_pow (2 ^ l))) =
      hermDiag l hF 1 (one_pow (2 ^ l)) ↔
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * ((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l = 1 := by
  have hD : (hermDiag l hF 1 (by simp) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, 0] := rfl
  have hM : ((hermAct l (sig_sig hF) g (hermDiag l hF 1 (by simp)) : ↥(hermA l F)) :
      Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, 0] *
        (frobPow l (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
    rw [hermAct_coe, hD]
  constructor
  · intro h
    have hEq : (g : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, 0] *
        (frobPow l (g : Matrix (Fin 2) (Fin 2) F))ᵀ = !![1, 0; 0, 0] := by
      have := congrArg (fun X : ↥(hermA l F) => (X : Matrix (Fin 2) (Fin 2) F)) h
      rwa [hM, hD] at this
    have h00 := congrFun (congrFun hEq 0) 0
    have h10 := congrFun (congrFun hEq 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] at h00 h10
    have hg00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h00
      exact zero_ne_one h00
    refine ⟨?_, h00⟩
    by_contra hg10
    exact hg00 (h10.resolve_left hg10)
  · rintro ⟨h10, h00⟩
    apply Subtype.ext
    rw [hM, hD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
        Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, h10,
        h00, sig_apply, mul_assoc, mul_comm, mul_left_comm]

theorem mem_cenOn_fixedSub (g : SL(2, F)) :
    g ∈ cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow) ↔
      (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 * ((g : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 ^ l = 1 := by
  constructor
  · intro hg
    have hfix : hermRep l hF g (hermDiag l hF 1 (by simp)) = hermDiag l hF 1 (by simp) :=
      hg.2 _ (hermDiag_one_mem_fixedSub (hF := hF))
    exact (hermAct_hermDiag_one_eq_iff (hF := hF) g).mp (by
      rwa [← hermRep_apply])
  · rintro ⟨h10, h00⟩
    refine ⟨Subgroup.mem_top g, ?_⟩
    intro X hX
    obtain ⟨h11, h01⟩ := (mem_fixedSub_upperSylow (hF := hF)).mp hX
    rw [eq_hermDiag_of_mem_herm1101 (hF := hF) X ⟨h11, h01⟩, hermRep_apply]
    have hD : (hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0) (hermA_00 (a := l) X) :
        Matrix (Fin 2) (Fin 2) F) = !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] := rfl
    have hmat : ((hermAct l (sig_sig hF) g (hermDiag l hF ((X : Matrix (Fin 2) (Fin 2) F) 0 0)
          (hermA_00 (a := l) X)) : ↥(hermA l F)) : Matrix (Fin 2) (Fin 2) F) =
        (g : Matrix (Fin 2) (Fin 2) F) * !![(X : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0] *
          (frobPow l (g : Matrix (Fin 2) (Fin 2) F))ᵀ := by
      rw [hermAct_coe, hD]
    apply Subtype.ext
    rw [hmat, hD]
    ext i j
    fin_cases i <;> fin_cases j
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
        Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, mul_one,
        mul_zero, add_zero, zero_add, sig_apply, h10]
      linear_combination ((X : Matrix (Fin 2) (Fin 2) F) 0 0) * h00
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
        Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, h10]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
        Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, h10]
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, frobPow,
        Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, h10]


private theorem card_roots_pow (hF : Fintype.card F = 2 ^ (2 * l)) :
    Nat.card {x : F // x ^ (2 ^ l + 1) = 1} = 2 ^ l + 1 := by
  have hq : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  let e : {x : F // x ^ (2 ^ l + 1) = 1} ≃
      (powMonoidHom (2 ^ l + 1) : Fˣ →* Fˣ).ker :=
    { toFun := fun x => by
        have hx0 : (x : F) ≠ 0 := by
          intro hx
          have := x.2
          rw [hx] at this
          exact zero_ne_one (show (0 : F) = 1 by simpa using this)
        refine ⟨Units.mk0 x hx0, ?_⟩
        rw [MonoidHom.mem_ker]
        apply Units.ext
        change ((x : F) : F) ^ (2 ^ l + 1) = 1
        exact x.2
      invFun := fun u => ⟨(u : Fˣ), by
        change ((u : Fˣ) : F) ^ (2 ^ l + 1) = 1
        have hu := u.2
        rw [MonoidHom.mem_ker] at hu
        exact congrArg Units.val hu⟩
      left_inv := fun x => rfl
      right_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        rfl }
  rw [Nat.card_congr e, IsCyclic.card_powMonoidHom_ker, Nat.card_units,
    Nat.card_eq_fintype_card, hF]
  have hfac : 2 ^ (2 * l) - 1 = (2 ^ l - 1) * (2 ^ l + 1) := by
    apply Nat.cast_injective (R := ℤ)
    have h1 : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (2 * l) := Nat.one_le_two_pow
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  rw [hfac, Nat.gcd_eq_right (dvd_mul_left _ _)]

private theorem coe_cenOn_eq (g : ↥(cenOn (hermRep l hF) ⊤
    (fixedSub (hermRep l hF) upperSylow))) :
    (g : SL(2, F)) = ⟨!![(g : SL(2, F)) 0 0, (g : SL(2, F)) 0 1; 0,
      ((g : SL(2, F)) 0 0)⁻¹], by
        have h := (mem_cenOn_fixedSub (hF := hF) g.1).mp g.2
        have hg00 : (g : SL(2, F)) 0 0 ≠ 0 := by
          intro h0
          have := h.2
          rw [h0, zero_mul] at this
          exact zero_ne_one (show (0 : F) = 1 from this)
        rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
        exact mul_inv_cancel₀ hg00⟩ := by
  have h := (mem_cenOn_fixedSub (hF := hF) g.1).mp g.2
  have hdet : ((g : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).det = 1 := (g : SL(2, F)).2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact h.1
  · have hg11 : (g : SL(2, F)) 1 1 = ((g : SL(2, F)) 0 0)⁻¹ := by
      have h1 : (g : SL(2, F)) 0 0 * (g : SL(2, F)) 1 1 = 1 := by
        have hd := hdet
        rw [Matrix.det_fin_two] at hd
        linear_combination hd + (g : SL(2, F)) 0 1 * h.1
      exact eq_inv_of_mul_eq_one_right h1
    exact hg11

private theorem exists_injective_cenOn :
    ∃ f : ↥(cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow)) →
      {x : F // x ^ (2 ^ l + 1) = 1} × F, Function.Injective f := by
  refine ⟨fun g => (⟨(g : SL(2, F)) 0 0, by
    have h := (mem_cenOn_fixedSub (hF := hF) g.1).mp g.2
    rw [pow_succ, mul_comm]
    exact h.2⟩, (g : SL(2, F)) 0 1), ?_⟩
  intro g1 g2 h
  have h00 : (g1 : SL(2, F)) 0 0 = (g2 : SL(2, F)) 0 0 := congrArg
    (fun p : {x : F // x ^ (2 ^ l + 1) = 1} × F => (p.1 : F)) h
  have h01 : (g1 : SL(2, F)) 0 1 = (g2 : SL(2, F)) 0 1 := congrArg
    (fun p : {x : F // x ^ (2 ^ l + 1) = 1} × F => (p.2 : F)) h
  apply Subtype.ext
  rw [coe_cenOn_eq (hF := hF) g1, coe_cenOn_eq (hF := hF) g2]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01]

private theorem exists_injective_roots :
    ∃ f : ({x : F // x ^ (2 ^ l + 1) = 1} × F) →
      ↥(cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow)),
      Function.Injective f := by
  refine ⟨fun p => ⟨⟨!![p.1, p.2; 0, p.1⁻¹], by
      have hp0 : (p.1 : F) ≠ 0 := by
        intro h
        have := p.1.2
        rw [h] at this
        exact zero_ne_one (show (0 : F) = 1 by simpa using this)
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero]
      exact mul_inv_cancel₀ hp0⟩, by
        refine (mem_cenOn_fixedSub (hF := hF) _).mpr ⟨by simp, ?_⟩
        change (p.1 : F) * (p.1 : F) ^ 2 ^ l = 1
        rw [← pow_succ', p.1.2]⟩, ?_⟩
  intro p q h
  have h00 : (p.1 : F) = (q.1 : F) := congrArg
    (fun g : ↥(cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow)) =>
      (g : SL(2, F)) 0 0) h
  have h01 : (p.2 : F) = q.2 := congrArg
    (fun g : ↥(cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow)) =>
      (g : SL(2, F)) 0 1) h
  apply Prod.ext
  · apply Subtype.ext
    exact h00
  · exact h01

theorem card_cenOn_fixedSub :
    Nat.card ↥(cenOn (hermRep l hF) ⊤ (fixedSub (hermRep l hF) upperSylow)) =
      2 ^ (2 * l) * (2 ^ l + 1) := by
  obtain ⟨f, hf⟩ := exists_injective_cenOn (hF := hF)
  obtain ⟨g, hg⟩ := exists_injective_roots (hF := hF)
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  have hprod : Nat.card ({x : F // x ^ (2 ^ l + 1) = 1} × F) =
      2 ^ (2 * l) * (2 ^ l + 1) := by
    rw [Nat.card_prod, card_roots_pow (hF := hF), Nat.card_eq_fintype_card, hF, Nat.mul_comm]
  rw [hprod] at h1 h2
  exact le_antisymm h1 h2

end CFSG.RankThree.GF2n.Tim81.Sec2
