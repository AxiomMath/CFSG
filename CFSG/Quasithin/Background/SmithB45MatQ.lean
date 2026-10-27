module

public import CFSG.Quasithin.Background.SmithB45MatQBase
public import CFSG.Quasithin.H13.A5M12Chain
public import Certificates.Certificate260400

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.QuasithinUnique.Setup.X1
  CFSG.Monster.Code

theorem quad_searches :
    forallGreedyAll pos24s2 inv24s2 (predQ 11 act24s2 true) 6 [] = true ∧
    forallGreedyAll pos24s2 inv24s2 (predQ 11 actC24s2 true) 6 [] = true ∧
    forallGreedyAll pos22s2 inv22s2 (predQ 10 act22s2 true) 5 [] = true ∧
    forallGreedyAll pos22s2 inv22s2 (predQ 10 actC22s2 false) 5 [] = true ∧
    forallGreedyAll pos12s2 inv12s2 (predQ 10 act12s2 true) 4 [] = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Certificates.certificate260400
  exact ⟨h1, h2, h3, h4, h5⟩

section Bound

variable {V : Type*} [CommGroup V] {n : ℕ} {P : Type*} [Group P] [DecidableEq P]
  {c : MaskCoords V n} {aut : P →* MulAut V} {act : P → ℕ → ℕ} {l : List P}
  {A : Subgroup (MulAut V)}

omit [DecidableEq P] in
theorem quadBasisOK_of_quadratic (hc : ChainAct c aut act) (hA : IsChainSub aut l A)
    (hq : commSeries A 2 = ⊥) : quadBasisOK n act l = true := by
  simp only [quadBasisOK, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro s hs t ht j hj
  exact act_fix_of_quadratic hc hA hq hs ht (Nat.pow_lt_pow_right (by norm_num) hj)

theorem lt_of_predQ (hp : predQ n act true l = true) (hc : ChainAct c aut act)
    (hA : IsChainSub aut l A) (hinj : Function.Injective aut) (hl : IndepList l)
    (hne : l ≠ []) (hq : commSeries A 2 = ⊥) : 2 * rk ↥A < rkIdx (fixV A) := by
  rw [rk_of_chain hA hinj hl, rkIdx_fixV_of_chain hc hA]
  have hqb := quadBasisOK_of_quadratic hc hA hq
  have he : l.isEmpty = false := List.isEmpty_eq_false_iff.2 hne
  simpa [predQ, hqb, he] using hp

theorem le_of_predQ (hp : predQ n act false l = true) (hc : ChainAct c aut act)
    (hA : IsChainSub aut l A) (hinj : Function.Injective aut) (hl : IndepList l)
    (hne : l ≠ []) (hq : commSeries A 2 = ⊥) : 2 * rk ↥A ≤ rkIdx (fixV A) := by
  rw [rk_of_chain hA hinj hl, rkIdx_fixV_of_chain hc hA]
  have hqb := quadBasisOK_of_quadratic hc hA hq
  have he : l.isEmpty = false := List.isEmpty_eq_false_iff.2 hne
  simpa [predQ, hqb, he] using hp

omit [DecidableEq P] in
theorem ne_nil_of_chainSub (hA : IsChainSub aut l A) (hne : A ≠ ⊥) : l ≠ [] := by
  rintro rfl
  apply hne
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨s, hs, rfl⟩ := (hA a).1 ha
  simp only [subprods, List.mem_singleton] at hs
  rw [hs, map_one]
  exact Subgroup.one_mem _

end Bound

section Modules

variable {V : Type*} [CommGroup V] [Finite V] {L G : Subgroup (MulAut V)}

theorem card_eq_two_pow_rk {A : Subgroup (MulAut V)} (hA : IsElemAbelian2 A) :
    Nat.card A = 2 ^ rk ↥A := by
  have : Finite (MulAut V) := finite_mulAut V
  exact card_eq_two_pow_of_isPGroup hA.isPGroup

theorem range_rho11_mog23_le :
    (rho11 mog23 inf_le_left).range ≤ (rho11 AutPerm le_rfl).range := by
  rintro _ ⟨σ, rfl⟩
  exact ⟨⟨σ, σ.2.1⟩, MulEquiv.ext fun w => rfl⟩

theorem range_rhoC11_mog23_le :
    (rhoC11 mog23 inf_le_left).range ≤ (rhoC11 AutPerm le_rfl).range := by
  rintro _ ⟨σ, rfl⟩
  exact ⟨⟨σ, σ.2.1⟩, MulEquiv.ext fun w => rfl⟩

theorem two_lt_qOf_cocode24
    (hLG : IsOver L G) (h : MathieuCocode24 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := cocode24_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := cocode24_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 6 [] quad_searches.1 _ hk)) e
    (map_le_range24 hLG he hA.1) hA.isElemAbelian2 hc
  exact lt_of_predQ hpred (chainAct24 e g) hchain (chainAut24_injective e g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_lt_qOf_code24
    (hLG : IsOver L G) (h : MathieuCode24 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := code24_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := code24_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 6 [] quad_searches.2.1 _ hk)) e
    (map_le_of_normalizer hLG he normalizer_rhoC11_autPerm hA.1) hA.isElemAbelian2 hc
  have hact : ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC24 g)) (chainAut e psiC24 phi24 g)
      actC24s2 :=
    chainAct_twist e psiC24 phi24 g (fun s _ hm => psiC24_phi24 s hm)
      (fun s _ hm => by
        rw [actC24s2, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
        exact actC11_lt _ _)
  exact lt_of_predQ hpred hact hchain
    (chainAut_injective (rhoC11_injective _ _) (T24s2.toSub_injective _ _) g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_lt_qOf_cocode23
    (hLG : IsOver L G) (h : MathieuCocode23 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := cocode23_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := cocode23_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel rhoM24 (rho11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 6 [] quad_searches.1 _ (by omega))) e
    ((map_le_of_normalizer hLG he normalizer_rho11_mog23 hA.1).trans range_rho11_mog23_le)
    hA.isElemAbelian2 hc
  exact lt_of_predQ hpred (chainAct24 e g) hchain (chainAut24_injective e g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_lt_qOf_code23
    (hLG : IsOver L G) (h : MathieuCode23 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := code23_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := code23_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC24 (rhoC11_injective _ _) phi24
    (T24s2.toSub_injective _ _) card_T24s2 (fun _ h1 h2 => T24s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos24s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 6 [] quad_searches.2.1 _ (by omega))) e
    ((map_le_of_normalizer hLG he normalizer_rhoC11_mog23 hA.1).trans range_rhoC11_mog23_le)
    hA.isElemAbelian2 hc
  have hact : ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC24 g)) (chainAut e psiC24 phi24 g)
      actC24s2 :=
    chainAct_twist e psiC24 phi24 g (fun s _ hm => psiC24_phi24 s hm)
      (fun s _ hm => by
        rw [actC24s2, actM_matsC11 T24s2 (mats := matsC24) rfl s hm]
        exact actC11_lt _ _)
  exact lt_of_predQ hpred hact hchain
    (chainAut_injective (rhoC11_injective _ _) (T24s2.toSub_injective _ _) g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_lt_qOf_cocode22
    (hLG : IsOver L G) (h : MathieuCocode22 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := cocode22_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := cocode22_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psi22 rho10_mog22plus_injective phi22
    (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos22s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 5 [] quad_searches.2.2.1 _ hk)) e
    (map_le_range22 hLG he hA.1) hA.isElemAbelian2 hc
  exact lt_of_predQ hpred (chainAct22 e g) hchain (chainAut22_injective e g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_le_qOf_code22
    (hLG : IsOver L G) (h : MathieuCode22 L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) ≤ qOf G := by
  obtain ⟨e, he⟩ := code22_std h
  refine two_le_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := code22_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psiC22 rhoC10_mog22plus_injective
    phi22 (T22s2.toSub_injective _ _) card_T22s2 (fun _ h1 h2 => T22s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos22s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 5 [] quad_searches.2.2.2.1 _ hk)) e
    (map_le_of_normalizer hLG he normalizer_rhoC10_mog22 hA.1) hA.isElemAbelian2 hc
  have hact : ChainAct (MaskCoords.ofEquiv (twistEquiv e psiC22 g)) (chainAut e psiC22 phi22 g)
      actC22s2 :=
    chainAct_twist e psiC22 phi22 g (fun s _ hm => psiC22_phi22 s hm)
      (fun s _ hm => by
        rw [actC22s2, actM_matsC10 T22s2 (mats := matsC22) rfl s hm]
        exact actC10_lt _ _)
  exact le_of_predQ hpred hact hchain
    (chainAut_injective rhoC10_mog22plus_injective (T22s2.toSub_injective _ _) g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

theorem two_lt_qOf_m12Ten
    (hLG : IsOver L G) (h : M12Ten L ⊤ ⊥) : ((2 : ℚ) : WithTop ℚ) < qOf G := by
  obtain ⟨e, he⟩ := m12_std h
  refine two_lt_qOf_of_forall fun A hA hq => ?_
  have hc := card_eq_two_pow_rk hA.isElemAbelian2
  have hk := m12_card_le hLG h hA.1 hA.isElemAbelian2 hc
  obtain ⟨g, l, hind, hpred, hchain⟩ := exists_chainModel psi12 rhoC12_m24Pair_injective phi12
    (T12s2.toSub_injective _ _) card_T12s2 (fun _ h1 h2 => T12s2.mem_invols h1 h2)
    ((forallGreedyP_eq pos12s2_eq _ _ []).symm.trans
      (forallGreedyAll_le 4 [] quad_searches.2.2.2.2 _ hk)) e
    (map_le_of_normalizer hLG he normalizer_rhoC12 hA.1) hA.isElemAbelian2 hc
  exact lt_of_predQ hpred (chainAct12 e g) hchain
    (chainAut_injective rhoC12_m24Pair_injective (T12s2.toSub_injective _ _) g) hind
    (ne_nil_of_chainSub hchain hA.ne_bot) hq

end Modules

end CFSG.Quasithin.B45Mat
