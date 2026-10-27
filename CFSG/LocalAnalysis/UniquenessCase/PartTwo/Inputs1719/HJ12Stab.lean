module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Facts91
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
public import CFSG.Sporadic.SuzRecog.SuzL34.X16

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 (A12 B12)
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open HJBridge (grpOf)
open HJ12 (wordR)

theorem hjStab_facts :
    MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0 = hjS1 ∧
      hjS1 ≤ Subgroup.normalizer ((hjA1 ⊔ hjA2 : Subgroup (MulAut W12)) : Set (MulAut W12)) ∧
      MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0 = hjE ⊔ hjK ∧ hjE ⊓ hjK = ⊥ ∧
      (∀ e ∈ hjE, ∀ k ∈ hjK, e * k = k * e) ∧
      Nonempty (↥hjE ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      Nonempty (↥hjK ≃* alternatingGroup (Fin 5)) := by
  classical
  let eR : List (Array ℕ) := HJ12.hj_eWords.map wordR
  let kR : List (Array ℕ) := HJ12.hj_stWords.map wordR
  let jR : List (Array ℕ) := (HJ12.hj_a1Words ++ HJ12.hj_a2Words).map wordR
  let sR : List (Array ℕ) := HJ12.hj_stab1Words.map wordR
  have hS1 := HJ12.hjS1Check_eq
  simp only [HJ12.hjS1Check, gensOKN_eq, CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp, CFSG.GF2Type.Smith1979.GammaU.native_appN,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
    CFSG.GF2Type.Smith1979.GammaU.native_invR, Bool.and_eq_true, beq_iff_eq, and_assoc] at hS1
  obtain ⟨hgs1, hc1, hlen1, hfix1, hgs2, hc2, hlen2, hconj1⟩ := hS1
  have hS2 := HJ12.hjS2Check_eq
  simp only [HJ12.hjS2Check, HJ12.commR, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp, CFSG.GF2Type.Smith1979.GammaU.native_appN,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hS2
  obtain ⟨hgsEK, hcE, hcK, hcEK, hlenE, hlenK, hlenEK, hsqChk, _, ha2, hb3, hab5, hfix2,
    hcommEK, hdisj⟩ := hS2
  have hgsE : SigmaP.gensOK eR = true := by
    have h' := hgsEK
    simp only [SigmaP.gensOK, List.all_append, Bool.and_eq_true] at h' ⊢
    exact h'.1
  have hgsK : SigmaP.gensOK kR = true := by
    have h' := hgsEK
    simp only [SigmaP.gensOK, List.all_append, Bool.and_eq_true] at h' ⊢
    exact h'.2
  unfold hjS1 hjE hjK hjA1 hjA2
  have hS1L0 : grpOf sR ≤ hjL0 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    exact hjWord_mem w
  have hS1fix : grpOf sR ≤ MulAction.stabilizer (MulAut W12) hjV1 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    change hjWord w ∈ MulAction.stabilizer (MulAut W12) hjV1
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have hfix : appN (wordR w) 4 = 4 := by
      have h' := List.all_eq_true.1 hfix1 (wordR w) (List.mem_map.2 ⟨w, hw, rfl⟩)
      simpa only [beq_iff_eq] using h'
    show hjWord w (Multiplicative.ofAdd (vecOf 4)) = Multiplicative.ofAdd (vecOf 4)
    rw [HJBridge.rowsOf_hjWord, ← vecOf_appN, hfix]
  have hS1card : Nat.card ↥(grpOf sR) = 384 := by
    rw [HJBridge.card_grpOf_eq hgs1 hc1]
    exact hlen1
  have hStab1card : Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0) = 384 :=
    hjOrbit_facts.2.2.2.2.1
  have hclause1 : MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0 = grpOf sR := by
    have hle : grpOf sR ≤ MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0 := le_inf hS1fix hS1L0
    have hcard : Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0) =
        Nat.card ↥(grpOf sR) := by rw [hStab1card, hS1card]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hjoin : grpOf (HJ12.hj_a1Words.map wordR) ⊔ grpOf (HJ12.hj_a2Words.map wordR) =
      grpOf ((HJ12.hj_a1Words ++ HJ12.hj_a2Words).map wordR) := by
    rw [List.map_append, HJBridge.grpOf_append_eq_sup]
  have hJcard : Nat.card ↥(grpOf jR) = 64 := by
    rw [HJBridge.card_grpOf_eq hgs2 hc2]
    exact hlen2
  have hgen_mem : ∀ ws ∈ HJ12.hj_stab1Words,
      hjWord ws ∈ Subgroup.normalizer ((grpOf (HJ12.hj_a1Words.map wordR) ⊔
        grpOf (HJ12.hj_a2Words.map wordR) : Subgroup (MulAut W12)) : Set (MulAut W12)) := by
    intro ws hws
    have hconj_mem : ∀ w ∈ HJ12.hj_a1Words ++ HJ12.hj_a2Words,
        MulAut.conj (hjWord ws) (hjWord w) ∈ grpOf jR := by
      intro w hw
      refine (HJBridge.mem_grpOf_iff hgs2 hc2 (MulAut.conj (hjWord ws) (hjWord w))).2
        ⟨mulR (mulR (wordR ws) (wordR w)) (Viol.invR (wordR ws)), ?_, ?_⟩
      · refine List.contains_iff_mem.1 (List.all_eq_true.1
          (List.all_eq_true.1 hconj1 (wordR ws) (List.mem_map.2 ⟨ws, hws, rfl⟩))
          (wordR w) (List.mem_map.2 ⟨w, hw, rfl⟩))
      · rw [MulAut.conj_apply]
        exact HJBridge.rowsOf_conj (HJBridge.rowsOf_hjWord ws) (HJBridge.rowsOf_hjWord w)
          (SigmaP.gensOK_spec hgs1 (wordR ws) (List.mem_map.2 ⟨ws, hws, rfl⟩)).2.2.1
    have hmap_le : (grpOf jR).map (MulAut.conj (hjWord ws)).toMonoidHom ≤ grpOf jR := by
      have heq : (grpOf jR).map (MulAut.conj (hjWord ws)).toMonoidHom =
          Subgroup.closure (⇑(MulEquiv.toMonoidHom (MulAut.conj (hjWord ws))) ''
            {x | ∃ w ∈ HJ12.hj_a1Words ++ HJ12.hj_a2Words, x = hjWord w}) := by
        rw [HJBridge.grpOf_words, MonoidHom.map_closure]
      rw [heq, Subgroup.closure_le]
      rintro z ⟨y, hy, rfl⟩
      have hy' : ∃ w ∈ HJ12.hj_a1Words ++ HJ12.hj_a2Words, y = hjWord w := hy
      obtain ⟨w, hw, rfl⟩ := hy'
      exact hconj_mem w hw
    have hcard : Nat.card ↥((grpOf jR).map (MulAut.conj (hjWord ws)).toMonoidHom) = 64 :=
      calc Nat.card ↥((grpOf jR).map (MulAut.conj (hjWord ws)).toMonoidHom)
          = Nat.card ↥(grpOf jR) :=
            Subgroup.card_map_of_injective (MulAut.conj (hjWord ws)).injective
        _ = 64 := hJcard
    rw [hjoin, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap_le (hJcard.trans hcard.symm).le
  have hclause2 : grpOf sR ≤ Subgroup.normalizer
      ((grpOf (HJ12.hj_a1Words.map wordR) ⊔ grpOf (HJ12.hj_a2Words.map wordR) :
        Subgroup (MulAut W12)) : Set (MulAut W12)) := by
    rw [HJBridge.grpOf_words, Subgroup.closure_le]
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hx
    rw [hxw]
    exact hgen_mem w hw
  have hEL0 : grpOf eR ≤ hjL0 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    exact hjWord_mem w
  have hKL0 : grpOf kR ≤ hjL0 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    exact hjWord_mem w
  have hEfix : grpOf eR ≤ MulAction.stabilizer (MulAut W12) hjV2 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    change hjWord w ∈ MulAction.stabilizer (MulAut W12) hjV2
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have hfix : appN (wordR w) 1024 = 1024 := by
      have h' := List.all_eq_true.1 hfix2 (wordR w)
        (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨w, hw, rfl⟩)))
      simpa only [beq_iff_eq] using h'
    show hjWord w (Multiplicative.ofAdd (vecOf 1024)) = Multiplicative.ofAdd (vecOf 1024)
    rw [HJBridge.rowsOf_hjWord, ← vecOf_appN, hfix]
  have hKfix : grpOf kR ≤ MulAction.stabilizer (MulAut W12) hjV2 := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨w, hw, rfl⟩
    change hjWord w ∈ MulAction.stabilizer (MulAut W12) hjV2
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have hfix : appN (wordR w) 1024 = 1024 := by
      have h' := List.all_eq_true.1 hfix2 (wordR w)
        (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨w, hw, rfl⟩)))
      simpa only [beq_iff_eq] using h'
    show hjWord w (Multiplicative.ofAdd (vecOf 1024)) = Multiplicative.ofAdd (vecOf 1024)
    rw [HJBridge.rowsOf_hjWord, ← vecOf_appN, hfix]
  have hEcard : Nat.card ↥(grpOf eR) = 4 := by
    rw [HJBridge.card_grpOf_eq hgsE hcE]
    exact hlenE
  have hKcard : Nat.card ↥(grpOf kR) = 60 := by
    rw [HJBridge.card_grpOf_eq hgsK hcK]
    exact hlenK
  have hEKcard : Nat.card ↥(grpOf (eR ++ kR)) = 240 := by
    rw [HJBridge.card_grpOf_eq hgsEK hcEK]
    exact hlenEK
  have hjoinEK : grpOf eR ⊔ grpOf kR = grpOf (eR ++ kR) :=
    (HJBridge.grpOf_append_eq_sup eR kR).symm
  have hclause3 : MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0 = grpOf eR ⊔ grpOf kR := by
    have hle : grpOf eR ⊔ grpOf kR ≤
        MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0 :=
      le_inf (sup_le hEfix hKfix) (sup_le hEL0 hKL0)
    have hcard : Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0) =
        Nat.card ↥(grpOf eR ⊔ grpOf kR) := by
      rw [hjOrbit_facts.2.2.2.2.2, hjoinEK, hEKcard]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hdisjE : ∀ x ∈ Enum.enumGrp eR, x = idR ∨ x ∉ Enum.enumGrp kR := by
    intro x hx
    have h' := List.all_eq_true.1 hdisj x hx
    rw [Bool.or_eq_true] at h'
    rcases h' with h | h
    · exact Or.inl (beq_iff_eq.1 h)
    · refine Or.inr fun hmem => ?_
      have hc : (Enum.enumGrp kR).contains x = true := List.contains_iff_mem.2 hmem
      rw [hc] at h
      exact Bool.noConfusion h
  have hclause4 : grpOf eR ⊓ grpOf kR = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨r, hr, hry⟩ := (HJBridge.mem_grpOf_iff hgsE hcE y).1 h1
    obtain ⟨r', hr', hry'⟩ := (HJBridge.mem_grpOf_iff hgsK hcK y).1 h2
    have hrr : r = r' :=
      rows_eq_of_rowsOf hry hry' (canon_of_mem_enumGrp hgsE hr) (canon_of_mem_enumGrp hgsK hr')
    subst r'
    rcases hdisjE r hr with hid | hnot
    · rw [hid] at hry
      exact HJBridge.rowsOf_unique hry HJBridge.rowsOf_one
    · exact absurd hr' hnot
  have hEcent : grpOf eR ≤
      Subgroup.centralizer ((grpOf kR : Subgroup (MulAut W12)) : Set (MulAut W12)) := by
    rw [HJBridge.grpOf_words]
    rw [Subgroup.closure_le]
    rintro x ⟨we, hwe, rfl⟩
    change hjWord we ∈ Subgroup.centralizer ((grpOf kR : Subgroup (MulAut W12)) :
      Set (MulAut W12))
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [HJBridge.grpOf_words] at hk
    refine Subgroup.closure_induction (p := fun k _ => k * hjWord we = hjWord we * k) ?_ ?_ ?_ ?_ hk
    · rintro x ⟨wk, hwk, rfl⟩
      have hc : mulR (wordR we) (wordR wk) = mulR (wordR wk) (wordR we) := by
        have h' := List.all_eq_true.1 (List.all_eq_true.1 hcommEK (wordR we)
          (List.mem_map.2 ⟨we, hwe, rfl⟩)) (wordR wk) (List.mem_map.2 ⟨wk, hwk, rfl⟩)
        simpa only [beq_iff_eq] using h'
      have hr1 : HJBridge.RowsOf (hjWord we * hjWord wk) (mulR (wordR we) (wordR wk)) :=
        HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord we) (HJBridge.rowsOf_hjWord wk)
      have hr2 : HJBridge.RowsOf (hjWord wk * hjWord we) (mulR (wordR we) (wordR wk)) := by
        rw [hc]
        exact HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord wk) (HJBridge.rowsOf_hjWord we)
      exact (HJBridge.rowsOf_unique hr1 hr2).symm
    · simp
    · intro x y _ _ hx hy
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    · intro x _ hx
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_inv_cancel_right]
  have hclause5 : ∀ e ∈ grpOf eR, ∀ k ∈ grpOf kR, e * k = k * e := by
    intro e he k hk
    exact (Subgroup.mem_centralizer_iff.1 (hEcent he) k hk).symm
  have hsqAll : ∀ v ∈ grpOf eR, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨r, hr, hrv⟩ := (HJBridge.mem_grpOf_iff hgsE hcE v).1 hv
    have hsqr : mulR r r = idR := by
      have h' := List.all_eq_true.1 hsqChk r hr
      simpa only [beq_iff_eq] using h'
    have hrows : HJBridge.RowsOf (v * v) (mulR r r) := HJBridge.rowsOf_mul hrv hrv
    rw [hsqr] at hrows
    rw [pow_two]
    exact HJBridge.rowsOf_unique hrows HJBridge.rowsOf_one
  have hclause6 : Nonempty (↥(grpOf eR) ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
    obtain ⟨e⟩ := CFSG.Quasithin.F6.GoldAmN.nonempty_mulEquiv_klein_subgroup (D := MulAut W12)
      (grpOf eR) hEcard hsqAll
    exact ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2)).symm⟩
  obtain ⟨w0, w1, hst⟩ := List.length_eq_two.1 (rfl : HJ12.hj_stWords.length = 2)
  have haR : (HJ12.hj_stWords.map wordR).headD idR = wordR w0 := by rw [hst]; rfl
  have hbR : (HJ12.hj_stWords.map wordR).getD 1 idR = wordR w1 := by rw [hst]; rfl
  have ha : hjWord w0 * hjWord w0 = 1 := by
    have ha2' : mulR (wordR w0) (wordR w0) = idR := by rw [← haR]; exact ha2
    have hrows : HJBridge.RowsOf (hjWord w0 * hjWord w0) (mulR (wordR w0) (wordR w0)) :=
      HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w0) (HJBridge.rowsOf_hjWord w0)
    rw [ha2'] at hrows
    exact HJBridge.rowsOf_unique hrows HJBridge.rowsOf_one
  have hb : hjWord w1 ^ 3 = 1 := by
    have hb3' : mulR (mulR (wordR w1) (wordR w1)) (wordR w1) = idR := by
      rw [← hbR]
      exact hb3
    have hrows : HJBridge.RowsOf ((hjWord w1 * hjWord w1) * hjWord w1)
        (mulR (mulR (wordR w1) (wordR w1)) (wordR w1)) :=
      HJBridge.rowsOf_mul (HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w1)
        (HJBridge.rowsOf_hjWord w1)) (HJBridge.rowsOf_hjWord w1)
    rw [hb3'] at hrows
    have h := HJBridge.rowsOf_unique hrows HJBridge.rowsOf_one
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_two]
    exact h
  have hab : (hjWord w0 * hjWord w1) ^ 5 = 1 := by
    have hab5' : mulR (mulR (mulR (mulR (wordR w0) (wordR w1))
        (mulR (wordR w0) (wordR w1)))
        (mulR (mulR (wordR w0) (wordR w1)) (mulR (wordR w0) (wordR w1))))
        (mulR (wordR w0) (wordR w1)) = idR := by
      rw [← haR, ← hbR]
      exact hab5
    have h1 : HJBridge.RowsOf (hjWord w0 * hjWord w1) (mulR (wordR w0) (wordR w1)) :=
      HJBridge.rowsOf_mul (HJBridge.rowsOf_hjWord w0) (HJBridge.rowsOf_hjWord w1)
    have h2 : HJBridge.RowsOf ((hjWord w0 * hjWord w1) ^ 2)
        (mulR (mulR (wordR w0) (wordR w1)) (mulR (wordR w0) (wordR w1))) := by
      rw [pow_two]
      exact HJBridge.rowsOf_mul h1 h1
    have h4 : HJBridge.RowsOf ((hjWord w0 * hjWord w1) ^ 4)
        (mulR (mulR (mulR (wordR w0) (wordR w1)) (mulR (wordR w0) (wordR w1)))
          (mulR (mulR (wordR w0) (wordR w1)) (mulR (wordR w0) (wordR w1)))) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
      exact HJBridge.rowsOf_mul h2 h2
    have h5 : HJBridge.RowsOf ((hjWord w0 * hjWord w1) ^ 5)
        (mulR (mulR (mulR (mulR (wordR w0) (wordR w1))
          (mulR (wordR w0) (wordR w1)))
          (mulR (mulR (wordR w0) (wordR w1)) (mulR (wordR w0) (wordR w1))))
          (mulR (wordR w0) (wordR w1))) := by
      rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, pow_one]
      exact HJBridge.rowsOf_mul h4 h1
    rw [hab5'] at h5
    exact HJBridge.rowsOf_unique h5 HJBridge.rowsOf_one
  have hclosure : Subgroup.closure {hjWord w0, hjWord w1} = grpOf kR := by
    rw [HJBridge.grpOf_words, hst]
    congr 1
    ext x
    simp
  have hclause7 : Nonempty (↥(grpOf kR) ≃* alternatingGroup (Fin 5)) :=
    ⟨(CFSG.Quasithin.L34Amalgam.a5Equiv (C := grpOf kR) (a := hjWord w0) (b := hjWord w1)
        ha hb hab hclosure hKcard).symm.trans
      CFSG.Sporadic.SuzRecog.SuzL34Cert.a5RelsEquivAlternatingGroup⟩
  exact ⟨hclause1, hclause2, hclause3, hclause4, hclause5, hclause6, hclause7⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
