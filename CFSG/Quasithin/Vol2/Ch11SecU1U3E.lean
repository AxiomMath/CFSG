module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Hat

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
open CFSG.Quasithin.A312U3 (uniData exists_su2_equiv)
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

@[expose] noncomputable def leviSL (hF : Nat.card F = p ^ 2) : Subgroup (PSU3F p F) :=
  ((piU p F).comp (sl2ToSU3 hF)).range

theorem piU_comp_sl2ToSU3_injective (hF : Nat.card F = p ^ 2) :
    Function.Injective ((piU p F).comp (sl2ToSU3 hF)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_ker hF (MonoidHom.mem_ker.mpr hx)
  set e := Classical.choice (exists_su2_equiv (p := p) hF) with he
  have hm : matU (sl2ToSU3 hF x) =
      Lemma41aL3.blkMat (((e x : ↥(StatedSU 2 (p ^ 1) F)) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) 1 := matU_ofSU2 hF (e x)
  have h22 := congrFun (congrFun hc 2) 2
  rw [hm] at h22
  have hc1 : c = 1 := by simpa [Lemma41aL3.blkMat, Matrix.scalar_apply] using h22.symm
  have h1 : sl2ToSU3 hF x = 1 := by
    apply ext_matU
    rw [hc, hc1, matU_one]
    simp
  exact sl2ToSU3_injective hF (h1.trans (map_one _).symm)

@[expose] noncomputable def leviSLEquiv (hF : Nat.card F = p ^ 2) :
    SL(2, ZMod p) ≃* ↥(leviSL hF) :=
  MonoidHom.ofInjective (piU_comp_sl2ToSU3_injective hF)

theorem leviSL_le_leviCU (hF : Nat.card F = p ^ 2) : leviSL hF ≤ leviCU hF := by
  rintro _ ⟨x, rfl⟩
  exact ⟨sl2ToSU3 hF x, sl2ToSU3_mem_leviU hF x, rfl⟩

theorem piU_ofSU2_mem_leviSL (hF : Nat.card F = p ^ 2) (S : ↥(StatedSU 2 (p ^ 1) F)) :
    piU p F (ofSU2 hF S) ∈ leviSL hF := by
  set e := Classical.choice (exists_su2_equiv (p := p) hF) with he
  refine ⟨e.symm S, ?_⟩
  show piU p F (ofSU2 hF (e (e.symm S))) = _
  rw [MulEquiv.apply_symm_apply]

theorem zcU_mem_leviSL (hF : Nat.card F = p ^ 2) : zcU hF ∈ leviSL hF := by
  have hm1 : (-1 : GL (Fin 2) F) ∈ StatedSU 2 (p ^ 1) F := by
    rw [mem_unitarySU_iff (uniData hF)]
    refine ⟨by simp [Matrix.det_neg], ?_⟩
    simp [Matrix.map_neg, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ofSU2 hF ⟨-1, hm1⟩ = tU hF := by
    apply ext_matU
    rw [matU_ofSU2, matU_tU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Lemma41aL3.blkMat, negNegOneDiag]
  show piU p F (tU hF) ∈ leviSL hF
  rw [← h1]
  exact piU_ofSU2_mem_leviSL hF _

theorem commutator_leviCU (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2) :
    ⁅leviCU hF, leviCU hF⁆ = leviSL hF := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [← map_commutatorElement, ← map_commutatorElement]
    set X : ↥(GU2Stated (p ^ 1) F) := ⁅A, B⁆ with hX
    have hdet : ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have hc : ∀ a b : Fˣ, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
        rw [mul_comm a b, mul_inv_cancel_right, mul_inv_cancel]
      have h1 : Matrix.GeneralLinearGroup.det (X : GL (Fin 2) F) = 1 := by
        rw [hX, commutatorElement_def]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        exact hc _ _
      have := congrArg (fun u : Fˣ => (u : F)) h1
      rw [Matrix.GeneralLinearGroup.val_det_apply] at this
      simpa using this
    have hXsu : (X : GL (Fin 2) F) ∈ StatedSU 2 (p ^ 1) F :=
      (mem_unitarySU_iff (uniData hF)).mpr
        ⟨hdet, (Lemma41aU3.mem_GU2Stated_iff (uniData hF)).mp X.2⟩
    exact piU_ofSU2_mem_leviSL hF ⟨_, hXsu⟩
  · have h4 : ∃ s : Finset (ZMod p), s.card = 4 := by
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (ZMod p)))
        (n := 4) (by rw [Finset.card_univ, ZMod.card]; omega)
      exact ⟨s, hs⟩
    have hperf := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    have hc : ⁅(⊤ : Subgroup SL(2, ZMod p)), ⊤⁆ = ⊤ := hperf.commutator_eq_top
    have h1 : ⁅leviSL hF, leviSL hF⁆ = leviSL hF := by
      rw [leviSL, MonoidHom.range_eq_map, ← Subgroup.map_commutator, hc]
    rw [← h1]
    exact Subgroup.commutator_mono (leviSL_le_leviCU hF) (leviSL_le_leviCU hF)

theorem comm_of_mem_centralizer_leviSL (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {a b : PSU3F p F} (ha : a ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F)))
    (hb : b ∈ Subgroup.centralizer (leviSL hF : Set (PSU3F p F))) : a * b = b * a := by
  have h2 := two_ne_zero_u hp2 hF
  have hz := zcU_mem_leviSL hF
  have haB : a ∈ leviCU hF :=
    mem_leviCU_of_commute_z hp2 hF (Subgroup.mem_centralizer_iff.mp ha _ hz).symm
  have hbB : b ∈ leviCU hF :=
    mem_leviCU_of_commute_z hp2 hF (Subgroup.mem_centralizer_iff.mp hb _ hz).symm
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := haB
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hbB
  obtain ⟨c, d, hQ⟩ := exists_quatPair_su2 hp2 hF
  have hQ' := hQ.map (StatedSU 2 (p ^ 1) F).subtype (StatedSU 2 (p ^ 1) F).subtype_injective
  obtain ⟨hC, hD, hDC⟩ := quat_relations h2 (det_of_mem_su2 hF c) hQ'
  have hAcomm : ∀ e : ↥(StatedSU 2 (p ^ 1) F), (A : GL (Fin 2) F).1 * (e : GL (Fin 2) F).1 =
      (e : GL (Fin 2) F).1 * (A : GL (Fin 2) F).1 := by
    intro e
    have h1 := Subgroup.mem_centralizer_iff.mp ha _ (piU_ofSU2_mem_leviSL hF e)
    have h2' := commute_of_piU_commute hF (A := Subgroup.inclusion su2_le_gu2 e) (B := A) h1
    have := congrArg
      (fun g : ↥(GU2Stated (p ^ 1) F) => ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h2'
    simpa [Units.val_mul] using this.symm
  obtain ⟨x, hx⟩ := scalar_of_commute_quat h2 hC hD hDC (hAcomm c) (hAcomm d)
  have hAB : A * B = B * A := by
    apply Subtype.ext
    apply Units.ext
    show (A : GL (Fin 2) F).1 * (B : GL (Fin 2) F).1 = (B : GL (Fin 2) F).1 * (A : GL (Fin 2) F).1
    rw [hx]
    exact (Matrix.scalar_commute x (fun r => Commute.all _ _) _).eq
  calc _ = piU p F (Lemma41aU3.blkU (uniData hF) (A * B)) := by simp only [map_mul]
    _ = piU p F (Lemma41aU3.blkU (uniData hF) (B * A)) := by rw [hAB]
    _ = _ := by simp only [map_mul]

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
