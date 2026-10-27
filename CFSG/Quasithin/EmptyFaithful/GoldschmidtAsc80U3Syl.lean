module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Quat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Abs

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover CFSG.RankThree.Classical
  CFSG.GH74.GLS.IVK.Proofs2 CFSG.Quasithin.A312U3 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem exists_scalar_of_mem_ker (hF : Nat.card F = p ^ 2) {g : SU3F p F}
    (hg : g ∈ (piU p F).ker) : ∃ c : F, c ^ 3 = 1 ∧ matU g = Matrix.scalar (Fin 3) c := by
  have h3 := Lemma41aU3.ker_pow_three (uniData hF) g hg
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hm : matU g = Matrix.scalar (Fin 3) (c : F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar, matU] using this.symm
  refine ⟨c, ?_, hm⟩
  have h3' : g * g * g = 1 := by simpa [pow_succ, mul_assoc] using h3
  have h3m : matU g * matU g * matU g = 1 := by
    rw [← matU_mul, ← matU_mul, h3', matU_one]
  rw [hm] at h3m
  have := congrFun (congrFun h3m 0) 0
  simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Fin.sum_univ_three,
    pow_succ, mul_assoc] using this

omit [Fact (Nat.Prime p)] [Finite F] in
theorem su2_le_gu2 : StatedSU 2 (p ^ 1) F ≤ GU2Stated (p ^ 1) F :=
  Subgroup.closure_mono fun _ hA => hA.2

@[expose] noncomputable def ofSU2 (hF : Nat.card F = p ^ 2) :
    ↥(StatedSU 2 (p ^ 1) F) →* SU3F p F :=
  (Lemma41aU3.blkU (uniData hF)).comp (Subgroup.inclusion su2_le_gu2)

omit [Finite F] in
theorem det_of_mem_su2 (hF : Nat.card F = p ^ 2) (A : ↥(StatedSU 2 (p ^ 1) F)) :
    ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
  ((mem_unitarySU_iff (uniData hF)).mp A.2).1

omit [Finite F] in
theorem matU_ofSU2 (hF : Nat.card F = p ^ 2) (A : ↥(StatedSU 2 (p ^ 1) F)) :
    matU (ofSU2 hF A) = Lemma41aL3.blkMat ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 := by
  have hd := det_of_mem_su2 hF A
  show Lemma41aL3.blkMat ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    (((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det)⁻¹ = _
  rw [hd, inv_one]

omit [Finite F] in
theorem ofSU2_injective (hF : Nat.card F = p ^ 2) : Function.Injective (ofSU2 hF) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  have h1 := congrArg matU h
  rw [matU_ofSU2, matU_ofSU2] at h1
  ext i j
  have h2 := congrFun (congrFun h1 (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [Lemma41aL3.blkMat] using h2

omit [Finite F] in
theorem ofSU2_mem_leviU (hF : Nat.card F = p ^ 2) (A : ↥(StatedSU 2 (p ^ 1) F)) :
    ofSU2 hF A ∈ leviU hF :=
  ⟨Subgroup.inclusion su2_le_gu2 A, rfl⟩

theorem exists_quatPair_su2 (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    ∃ c d : ↥(StatedSU 2 (p ^ 1) F), QuatPair c d := by
  obtain ⟨c, d, h⟩ := exists_quatPair_sl2 hp2
  obtain ⟨e⟩ := exists_su2_equiv hF
  exact ⟨e c, e d, h.map e.toMonoidHom e.injective⟩

theorem exists_special_sylow_u (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    ∃ (U : Subgroup (PSU3F p F)) (c d : ↥(StatedSU 2 (p ^ 1) F)), IsSylowTwoOf U ⊤ ∧
      U ≤ leviCU hF ∧ QuatPair c d ∧ piU p F (ofSU2 hF c) ∈ U ∧ piU p F (ofSU2 hF d) ∈ U := by
  obtain ⟨c, d, hQ⟩ := exists_quatPair_su2 hp2 hF
  have hQ' : QuatPair (ofSU2 hF c) (ofSU2 hF d) := hQ.map (ofSU2 hF) (ofSU2_injective hF)
  have hX : IsPGroup 2 ↥((Subgroup.closure ({ofSU2 hF c, ofSU2 hF d} : Set (SU3F p F))).map
      (piU p F)) := hQ'.isPGroup_two_closure.map _
  have hXB : (Subgroup.closure ({ofSU2 hF c, ofSU2 hF d} : Set (SU3F p F))).map (piU p F) ≤
      leviCU hF := by
    refine Subgroup.map_mono ((Subgroup.closure_le _).mpr ?_)
    intro x hx
    rcases hx with rfl | rfl
    · exact ofSU2_mem_leviU hF c
    · exact ofSU2_mem_leviU hF d
  obtain ⟨S, hS, hXS⟩ := exists_isSylowTwoOf_ge hX hXB
  refine ⟨S, c, d, isSylowTwoOf_top_of_odd_index (odd_index_leviCU hp2 hF) hS, hS.1, hQ, ?_, ?_⟩
  · exact hXS ⟨ofSU2 hF c, Subgroup.subset_closure (by simp), rfl⟩
  · exact hXS ⟨ofSU2 hF d, Subgroup.subset_closure (by simp), rfl⟩

omit [Finite F] in
theorem commute_of_piU_commute (hF : Nat.card F = p ^ 2) {A B : ↥(GU2Stated (p ^ 1) F)}
    (h : piU p F (Lemma41aU3.blkU (uniData hF) A) * piU p F (Lemma41aU3.blkU (uniData hF) B) =
      piU p F (Lemma41aU3.blkU (uniData hF) B) * piU p F (Lemma41aU3.blkU (uniData hF) A)) :
    A * B = B * A := by
  set bk := Lemma41aU3.blkU (uniData hF) with hbk
  set X : ↥(GU2Stated (p ^ 1) F) := A * B * A⁻¹ * B⁻¹ with hXdef
  have hdet : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have hc : ∀ a b : Fˣ, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right, mul_inv_cancel]
    have h1 : Matrix.GeneralLinearGroup.det (X : GL (Fin 2) F) = 1 := by
      rw [hXdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      exact hc _ _
    have := congrArg (fun u : Fˣ => (u : F)) h1
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    simpa using this
  have h1 : piU p F (bk X) = 1 := by
    rw [hXdef]
    simp only [map_mul, map_inv]
    rw [h]
    group
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr h1)
  have h22 := congrFun (congrFun hc 2) 2
  have e22 : ∀ (M : Matrix (Fin 2) (Fin 2) F) (d : F),
      (Lemma41aL3.blkMat M d : Matrix (Fin 3) (Fin 3) F) 2 2 = d := fun M d => by
    simp [Lemma41aL3.blkMat]
  have hX : matU (bk X) 2 2 = 1 := by
    have : matU (bk X) 2 2 = ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det⁻¹ := e22 _ _
    rw [this, hdet, inv_one]
  rw [hX] at h22
  have hc1 : c = 1 := by simpa [Matrix.scalar_apply] using h22.symm
  have hone : bk X = 1 := by
    apply ext_matU
    rw [hc, hc1, matU_one]
    simp
  have hX1 : X = 1 := Lemma41aU3.blkU_injective (uniData hF) (hone.trans (map_one bk).symm)
  calc A * B = X * (B * A) := by rw [hXdef]; group
    _ = B * A := by rw [hX1, one_mul]

theorem two_ne_zero_u (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) : (2 : F) ≠ 0 :=
  two_ne_zero_of_card_sq hp2 hF

theorem zOf_comm_leviU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {U : Subgroup (PSU3F p F)}
    {c d : ↥(StatedSU 2 (p ^ 1) F)} (hQ : QuatPair c d) (hc : piU p F (ofSU2 hF c) ∈ U)
    (hd : piU p F (ofSU2 hF d) ∈ U) (hUB : U ≤ leviCU hF) {w b : PSU3F p F} (hw : w ∈ zOf U)
    (hb : b ∈ leviCU hF) : w * b = b * w := by
  have h2 := two_ne_zero_u hp2 hF
  obtain ⟨gw, ⟨A, rfl⟩, rfl⟩ := hUB hw.1
  obtain ⟨gb, ⟨B, rfl⟩, rfl⟩ := hb
  have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
  obtain ⟨hC, hD, hDC⟩ := quat_relations h2 (det_of_mem_su2 hF c) hQ'
  have hAcomm : ∀ e : ↥(StatedSU 2 (p ^ 1) F), piU p F (ofSU2 hF e) ∈ U →
      (A : GL (Fin 2) F).1 * (e : GL (Fin 2) F).1 =
        (e : GL (Fin 2) F).1 * (A : GL (Fin 2) F).1 := by
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.mp hw.2 (piU p F (ofSU2 hF e)) he
    have h2' := commute_of_piU_commute hF (A := Subgroup.inclusion su2_le_gu2 e) (B := A) h1
    have := congrArg
      (fun g : ↥(GU2Stated (p ^ 1) F) => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h2'
    simpa [Units.val_mul] using this.symm
  obtain ⟨x, hx⟩ := scalar_of_commute_quat h2 hC hD hDC (hAcomm c hc) (hAcomm d hd)
  have hAB : A * B = B * A := by
    apply Subtype.ext
    apply Units.ext
    show (A : GL (Fin 2) F).1 * (B : GL (Fin 2) F).1 = (B : GL (Fin 2) F).1 * (A : GL (Fin 2) F).1
    rw [hx]
    exact (Matrix.scalar_commute x (fun r => Commute.all _ _) _).eq
  calc _ = piU p F (Lemma41aU3.blkU (uniData hF) (A * B)) := by simp only [map_mul]
    _ = piU p F (Lemma41aU3.blkU (uniData hF) (B * A)) := by rw [hAB]
    _ = _ := by simp only [map_mul]

noncomputable abbrev tU (hF : Nat.card F = p ^ 2) : SU3F p F := unitaryInvT (uniData hF)

noncomputable abbrev zcU (hF : Nat.card F = p ^ 2) : PSU3F p F := piU p F (tU hF)

omit [Finite F] in
theorem matU_tU (hF : Nat.card F = p ^ 2) : matU (tU hF) = negNegOneDiag F := rfl

theorem mem_leviCU_of_commute_z (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) {g : PSU3F p F}
    (h : g * zcU hF = zcU hF * g) : g ∈ leviCU hF := by
  obtain ⟨g, rfl⟩ := piU_surjective g
  have h1 : piU p F ((g * tU hF)⁻¹ * (tU hF * g)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul]
    exact inv_mul_eq_one.mpr h
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr h1)
  set q := (g * tU hF)⁻¹ * (tU hF * g) with hqdef
  have hq : (g * tU hF) * q = tU hF * g := mul_inv_cancel_left _ _
  have hm := congrArg matU hq
  rw [matU_mul, matU_mul, hr, matU_mul, matU_tU] at hm
  have hr1 : r + 1 ≠ 0 := by
    intro h0
    have : r = -1 := by linear_combination h0
    rw [this] at hr3
    apply two_ne_zero_u hp2 hF
    linear_combination -hr3
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  have e20 := congrFun (congrFun hm 2) 0
  have e21 := congrFun (congrFun hm 2) 1
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, negNegOneDiag]
    at e02 e12 e20 e21
  refine ⟨g, (mem_leviU_iff hp2 hF).mpr ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · exact (mul_eq_zero.mp (by linear_combination e02 : matU g 0 2 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination e12 : matU g 1 2 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination -e20 : matU g 2 0 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination -e21 : matU g 2 1 * (r + 1) = 0)).resolve_right hr1

end CFSG.Quasithin.E2P.Asc80
