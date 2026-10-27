module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofSeitzFour
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenLinI

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

section Planes

variable {G : Type*} [Group G]

theorem zpow_apply_eq_self' {Y : Type*} [Group Y] {ψ : MulAut Y} {y : Y} (h : ψ y = y) (n : ℤ) :
    (ψ ^ n) y = y := by
  have hmem : ψ ∈ MulAction.stabilizer (MulAut Y) y := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := (MulAction.stabilizer (MulAut Y) y).zpow_mem hmem n
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

theorem le_of_card_nine {E R : Subgroup G} (hE : Nat.card E = 9) {a b : G} (haE : a ∈ E)
    (hbE : b ∈ E) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) (haR : a ∈ R)
    (hbR : b ∈ R) : E ≤ R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b with hH
  have hHE : H ≤ E := sup_le (Subgroup.zpowers_le.2 haE) (Subgroup.zpowers_le.2 hbE)
  have hHR : H ≤ R := sup_le (Subgroup.zpowers_le.2 haR) (Subgroup.zpowers_le.2 hbR)
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have ha : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha]
  have hfinH : Finite H := Finite.of_injective _ (Subgroup.inclusion_injective hHE)
  have h1 : Nat.card H ∣ 9 := hE ▸ Subgroup.card_dvd_of_le hHE
  have h2 : 3 ∣ Nat.card H := hza ▸ Subgroup.card_dvd_of_le (le_sup_left : _ ≤ H)
  have h3 : Nat.card H ≠ 3 := by
    intro h
    apply hb
    have heq : Subgroup.zpowers a = H :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, hza])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have h9 : Nat.card H = 9 := by
    have : Nat.card H ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨h1, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · rw [h] at h2; norm_num at h2
    · exact absurd h h3
    · exact h
  have hHeq : H = E := Subgroup.eq_of_le_of_card_ge hHE (by rw [h9, hE])
  rw [← hHeq]
  exact hHR

end Planes

variable {k : Type} [Field k]

theorem isConjBy_conj (s : SpecialLinearGroup (Fin 3) k) :
    IsConjBy (MulAut.conj s) (SpecialLinearGroup.toGL s) := by
  intro t
  rw [MulAut.conj_apply, ← map_inv]
  rfl

theorem eq_of_isConjBy {σ τ : MulAut (SpecialLinearGroup (Fin 3) k)} {M : GL (Fin 3) k}
    (hσ : IsConjBy σ M) (hτ : IsConjBy τ M) : σ = τ := by
  ext1 t
  apply Subtype.ext
  rw [hσ t, hτ t]

theorem det_heisC (α : k) : (heisC α).det = α := by
  simp [heisC, Matrix.det_fin_three]

theorem apply_mem_closure_fixSet {S : Type*} [Group S] {E : Subgroup (MulAut S)}
    (hEab : Open.IsElemAbelian 3 E) {e : MulAut S} (he : e ∈ E) {x : S}
    (hx : x ∈ Subgroup.closure (fixSet E)) : e x ∈ Subgroup.closure (fixSet E) := by
  have hle : Subgroup.closure (fixSet E) ≤ (Subgroup.closure (fixSet E)).comap e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨φ, hφ, hφ1, hφy⟩
    refine Subgroup.subset_closure ⟨φ, hφ, hφ1, ?_⟩
    have hc : φ * e = e * φ := congrArg Subtype.val (hEab.1.is_comm.comm ⟨φ, hφ⟩ ⟨e, he⟩)
    have h1 : (φ * e) y = (e * φ) y := by rw [hc]
    simp only [MulAut.mul_apply] at h1
    show φ (e y) = e y
    rw [h1, hφy]
  exact hle hx

theorem fix_conjUnit_of_comm {φ : MulAut (SpecialLinearGroup (Fin 3) k)} {M P : GL (Fin 3) k}
    (hφ : IsConjBy φ M) {N : Matrix (Fin 3) (Fin 3) k} {c : k}
    (hM : (M : Matrix (Fin 3) (Fin 3) k) = c • ((P : Matrix (Fin 3) (Fin 3) k) * N *
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)))
    {y : SpecialLinearGroup (Fin 3) k} (hy : N * (y : Matrix (Fin 3) (Fin 3) k) =
      (y : Matrix (Fin 3) (Fin 3) k) * N) :
    φ (conjUnit P y) = conjUnit P y := by
  refine hφ.fix ?_
  have hPi : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
      1 := Units.inv_mul P
  rw [hM, conjUnit_coe, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
    (P : Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul, ← Matrix.mul_assoc N, hy,
    ← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
    (P : Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul, Matrix.mul_assoc]

theorem closure_fixSet_sl_of_conj_outer [Finite k] (h4 : 4 ≤ Nat.card k)
    (E : Subgroup (MulAut (SpecialLinearGroup (Fin 3) k))) (hEab : Open.IsElemAbelian 3 E)
    (hEcard : Nat.card E = 9)
    (hout : ¬ E ≤ (MulAut.conj : SpecialLinearGroup (Fin 3) k →*
      MulAut (SpecialLinearGroup (Fin 3) k)).range)
    (hconj : ∀ e ∈ E, ∃ g : GL (Fin 3) k, IsConjBy e g)
    (hHeis : ∃ e ∈ E, ∃ s : SpecialLinearGroup (Fin 3) k, s ^ 3 = 1 ∧ MulAut.conj s ∈ E ∧
      e s ≠ s) :
    Subgroup.closure (fixSet E) = ⊤ := by
  classical
  obtain ⟨e, heE, s, hs3, hsE, hes⟩ := hHeis
  obtain ⟨g, hg⟩ := hconj e heE
  have hsG := isConjBy_conj s
  have hcomm : MulAut.conj s * e = e * MulAut.conj s :=
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨_, hsE⟩ ⟨e, heE⟩)
  obtain ⟨w, hw3, hmat⟩ := exists_commutation_scalar hsG hg hcomm
  have hw1 : (w : k) ≠ 1 := by
    intro h1
    apply hes
    apply Subtype.ext
    rw [hg s, hmat, h1, one_smul]
  have he3 : e ^ 3 = 1 := hEab.2 e heE
  obtain ⟨a, ha⟩ := exists_pow_three_scalar hg he3
  have hwprim : IsPrimitiveRoot (w : k) 3 := by
    refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) hw3 ?_
    intro l hl0 hl3
    interval_cases l
    · simpa using hw1
    · intro h2
      apply hw1
      have h' : (w : k) ^ 3 = (w : k) ^ 2 * (w : k) := by ring
      rw [hw3, h2, one_mul] at h'
      exact h'.symm
  set ω : k := (w : k)⁻¹ with hωdef
  have hωprim : IsPrimitiveRoot ω 3 := hwprim.inv
  have hw0 : (w : k) ≠ 0 := w.ne_zero
  have hyx : ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
      (g : Matrix (Fin 3) (Fin 3) k) =
      ω • ((g : Matrix (Fin 3) (Fin 3) k) *
        ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix]
    have h1 : (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) =
        (w : k) • ((s : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) := by
      calc (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k)
          = ((g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
              ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *
            (g : Matrix (Fin 3) (Fin 3) k) := by
            rw [Matrix.mul_assoc _ _ (g : Matrix (Fin 3) (Fin 3) k), Units.inv_mul,
              Matrix.mul_one]
        _ = (w : k) • ((s : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k)) := by
            rw [hmat, Matrix.smul_mul]
    rw [h1, smul_smul, hωdef, inv_mul_cancel₀ hw0, one_smul]
  have hy3 : ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) ^ 3 = 1 := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, ← Matrix.SpecialLinearGroup.coe_pow, hs3,
      Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨P, ξ, hξ3, hyP, hxP⟩ := exists_heisenberg_basis_gl hωprim hyx hy3 ha
  set α : k := (a : k) with hαdef
  have hα : α ≠ 0 := a.ne_zero
  have hCα : (!![0, 0, α; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) k) = heisC α := rfl
  rw [hCα] at hxP
  have hdiag_s : (s : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
      (P : Matrix (Fin 3) (Fin 3) k) * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] := by
    rw [← hyP, SpecialLinearGroup.coe_GL_coe_matrix]
  have hPi : ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (P : Matrix (Fin 3) (Fin 3) k) =
      1 := Units.inv_mul P
  have hPi' : (P : Matrix (Fin 3) (Fin 3) k) * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      1 := Units.mul_inv P
  have he1 : e ≠ 1 := fun h => hes (by rw [h]; rfl)
  have hs1 : MulAut.conj s ≠ 1 := by
    intro h
    have hcs : ∀ t : SpecialLinearGroup (Fin 3) k,
        ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *
          (t : Matrix (Fin 3) (Fin 3) k) = (t : Matrix (Fin 3) (Fin 3) k) *
            ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      intro t
      have ht : MulAut.conj s t = t := by rw [h]; rfl
      rw [MulAut.conj_apply] at ht
      rw [SpecialLinearGroup.coe_GL_coe_matrix, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul]
      congr 1
      calc s * t = s * t * s⁻¹ * s := by group
        _ = t * s := by rw [ht]
    obtain ⟨c, hc⟩ := eq_scalar_of_forall_commute _ hcs
    rw [SpecialLinearGroup.coe_GL_coe_matrix] at hc
    have h2 : (g : Matrix (Fin 3) (Fin 3) k) * (s : Matrix (Fin 3) (Fin 3) k) *
        ((g⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = (s : Matrix (Fin 3) (Fin 3) k) := by
      rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]
    rw [hmat] at h2
    have h3 : ((w : k) - 1) • (s : Matrix (Fin 3) (Fin 3) k) = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    have hs0 := (smul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hw1)
    have hdet : (s : Matrix (Fin 3) (Fin 3) k).det = 1 := s.det_coe
    rw [hs0] at hdet
    simp at hdet
  have hαc : ¬ ∃ μ : k, μ ^ 3 = α := by
    rintro ⟨μ, hμ⟩
    apply hout
    have hμ0 : μ ≠ 0 := by rintro rfl; apply hα; rw [← hμ]; ring
    have hdetg : (g : Matrix (Fin 3) (Fin 3) k).det = α := by
      have h1 := congrArg Matrix.det hxP
      rw [Matrix.det_mul, Matrix.det_mul, det_heisC] at h1
      have hP0 : (P : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
      exact mul_right_cancel₀ hP0 (h1.trans (mul_comm _ _))
    let g' : SpecialLinearGroup (Fin 3) k := ⟨μ⁻¹ • (g : Matrix (Fin 3) (Fin 3) k), by
      rw [Matrix.det_smul, hdetg, Fintype.card_fin, inv_pow, ← hμ, inv_mul_cancel₀
        (pow_ne_zero 3 hμ0)]⟩
    have hg'm : (g' : Matrix (Fin 3) (Fin 3) k) = μ⁻¹ • (g : Matrix (Fin 3) (Fin 3) k) := rfl
    have heg : e = MulAut.conj g' := by
      ext1 t
      rw [MulAut.conj_apply, eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hg t, hg'm,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc _ _ (g : Matrix (Fin 3) (Fin 3) k),
        Units.inv_mul, Matrix.mul_one]
    have hsnot : e ∉ Subgroup.zpowers (MulAut.conj s) := by
      rintro ⟨n, hn⟩
      apply hes
      rw [← hn]
      exact zpow_apply_eq_self' (by rw [MulAut.conj_apply]; group) n
    have hs3' : MulAut.conj s ^ 3 = 1 := hEab.2 _ hsE
    exact le_of_card_nine hEcard hsE heE hs3' hs1 hsnot ⟨s, rfl⟩ ⟨g', heg.symm⟩
  set K : Subgroup (SpecialLinearGroup (Fin 3) k) := Subgroup.closure (fixSet E) with hKdef
  apply eq_top_of_comap_conjUnit P
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have := hωprim.pow_eq_one
      linear_combination this
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hωprim.ne_one (by norm_num)))
  set gα : GL (Fin 3) k := P⁻¹ * g * P with hgαdef
  have hgα : (gα : Matrix (Fin 3) (Fin 3) k) = heisC α := by
    rw [hgαdef, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, hPi,
      Matrix.one_mul]
  have hdiagK : ∀ (a' b' d' : k) (h : a' * b' * d' = 1),
      diagSL a' b' d' h ∈ K.comap (conjUnit P) := by
    intro a' b' d' h
    refine Subgroup.subset_closure ⟨MulAut.conj s, hsE, hs1, hsG.fix ?_⟩
    rw [SpecialLinearGroup.coe_GL_coe_matrix, conjUnit_coe]
    have hD : (diagSL a' b' d' h : Matrix (Fin 3) (Fin 3) k) * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] =
        diagonal ![ξ, ξ * ω, ξ * ω ^ 2] * (diagSL a' b' d' h : Matrix (Fin 3) (Fin 3) k) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    have hs' : (s : Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) *
        diagonal ![ξ, ξ * ω, ξ * ω ^ 2] * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [← hdiag_s, Matrix.mul_assoc, hPi', Matrix.mul_one]
    rw [hs']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (P :
      Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul, ← Matrix.mul_assoc
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (P : Matrix (Fin 3) (Fin 3) k), hPi,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal ![ξ, ξ * ω, ξ * ω ^ 2]), ← hD,
      Matrix.mul_assoc]
  have hK0 : ∀ y : SpecialLinearGroup (Fin 3) k,
      heisC α * (y : Matrix (Fin 3) (Fin 3) k) = (y : Matrix (Fin 3) (Fin 3) k) * heisC α →
        y ∈ K.comap (conjUnit P) := by
    intro y hy
    refine Subgroup.subset_closure ⟨e, heE, he1, hg.fix ?_⟩
    have hg' : (g : Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) * heisC α *
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [← hxP, Matrix.mul_assoc, hPi', Matrix.mul_one]
    rw [conjUnit_coe, hg']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (P :
      Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul, ← Matrix.mul_assoc
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) (P : Matrix (Fin 3) (Fin 3) k), hPi,
      Matrix.one_mul, ← Matrix.mul_assoc (heisC α), hy, Matrix.mul_assoc]
  have hinvK : ∀ x ∈ K.comap (conjUnit P), conjUnit gα x ∈ K.comap (conjUnit P) := by
    intro x hx
    have hx' : conjUnit P x ∈ K := hx
    show conjUnit P (conjUnit gα x) ∈ K
    have e1 : conjUnit P (conjUnit gα x) = e (conjUnit P x) := by
      apply Subtype.ext
      rw [hg, conjUnit_coe, conjUnit_coe, conjUnit_coe, hgαdef]
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P : Matrix (Fin 3) (Fin 3) k)
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k), hPi', Matrix.one_mul]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_one]
    rw [e1]
    exact apply_mem_closure_fixSet hEab heE hx'
  by_cases hk4 : Nat.card k = 4
  ·
    have : Fintype k := Fintype.ofFinite k
    have hk4' : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card]; exact hk4
    have h2 : (2 : k) = 0 := by
      have h4' : ((Fintype.card k : ℕ) : k) = 0 := FiniteField.cast_card_eq_zero k
      rw [hk4'] at h4'
      have : (2 : k) ^ 2 = 0 := by rw [← h4']; norm_num
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    have hα3 : α ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one α hα
      rwa [hk4'] at this
    have hα1 : α ≠ 1 := fun h => hαc ⟨1, by rw [h]; ring⟩
    have hα2 : α ^ 2 + α + 1 = 0 := by
      have h1 : (α - 1) * (α ^ 2 + α + 1) = 0 := by linear_combination hα3
      exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hα1)
    have hω3 : ω ^ 3 = 1 := hωprim.pow_eq_one
    have hαω : α = ω ∨ α = ω ^ 2 := by
      have h1 : (α - ω) * (α - ω ^ 2) = 0 := by
        linear_combination hα2 - α * hω + hω3
      rcases mul_eq_zero.1 h1 with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
    have hsD : ((SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ξ • ((P : Matrix (Fin 3) (Fin 3) k) * heisD ω *
          ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
      have hdξ : diagonal ![ξ, ξ * ω, ξ * ω ^ 2] = ξ • heisD ω := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [heisD]
      rw [SpecialLinearGroup.coe_GL_coe_matrix, ← Matrix.mul_one (s : Matrix (Fin 3) (Fin 3) k),
        ← hPi', ← Matrix.mul_assoc, hdiag_s, hdξ, Matrix.mul_smul, Matrix.smul_mul]
    have hgC : (g : Matrix (Fin 3) (Fin 3) k) = (P : Matrix (Fin 3) (Fin 3) k) * heisC α *
        ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [← hxP, Matrix.mul_assoc, hPi', Matrix.mul_one]
    have hconjP : ∀ N N' : Matrix (Fin 3) (Fin 3) k,
        ((P : Matrix (Fin 3) (Fin 3) k) * N * ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) *
          ((P : Matrix (Fin 3) (Fin 3) k) * N' *
            ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) =
          (P : Matrix (Fin 3) (Fin 3) k) * (N * N') *
            ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      intro N N'
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)
        (P : Matrix (Fin 3) (Fin 3) k), hPi, Matrix.one_mul]
    have hne1 : MulAut.conj s * e ≠ 1 := by
      intro h
      apply hes
      have he' : e = (MulAut.conj s)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [he', ← map_inv, MulAut.conj_apply]
      group
    have hne2 : MulAut.conj s * MulAut.conj s * e ≠ 1 := by
      intro h
      apply hes
      have he' : e = (MulAut.conj s * MulAut.conj s)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [he', ← map_mul, ← map_inv, MulAut.conj_apply]
      group
    have hK1 : ∀ y : SpecialLinearGroup (Fin 3) k,
        (heisD ω * heisC α) * (y : Matrix (Fin 3) (Fin 3) k) =
          (y : Matrix (Fin 3) (Fin 3) k) * (heisD ω * heisC α) → y ∈ K.comap (conjUnit P) := by
      intro y hy
      refine Subgroup.subset_closure ⟨MulAut.conj s * e, E.mul_mem hsE heE, hne1,
        fix_conjUnit_of_comm (hsG.mul hg) (c := ξ) ?_ hy⟩
      rw [Units.val_mul, hsD, hgC]
      simp only [Matrix.smul_mul, hconjP]
    have hK2 : ∀ y : SpecialLinearGroup (Fin 3) k,
        (heisD ω * heisD ω * heisC α) * (y : Matrix (Fin 3) (Fin 3) k) =
          (y : Matrix (Fin 3) (Fin 3) k) * (heisD ω * heisD ω * heisC α) →
            y ∈ K.comap (conjUnit P) := by
      intro y hy
      refine Subgroup.subset_closure ⟨MulAut.conj s * MulAut.conj s * e,
        E.mul_mem (E.mul_mem hsE hsE) heE, hne2,
        fix_conjUnit_of_comm ((hsG.mul hsG).mul hg) (c := ξ * ξ) ?_ hy⟩
      rw [Units.val_mul, Units.val_mul, hsD, hgC]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hconjP]
    exact eq_top_of_tori_four h2 hω hαω hdiagK ⟨hK0, hK1, hK2⟩ hgα hinvK
  · exact eq_top_of_torus_singer (by omega) hω (hωprim.ne_one (by norm_num)) hα hαc hdiagK hK0
      hgα hinvK

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
