module

public import CFSG.OddTranspositions.F25Alg

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

theorem isOddPrimePower_card_F25t : IsOddPrimePower (Nat.card F25t) := by
  rw [card_F25t_nat]
  exact ⟨5, 2, Nat.prime_five, by norm_num, by norm_num, by norm_num⟩

theorem card_PSL2_F25t : Nat.card (PSL2 F25t) = 7800 := by
  rw [psl2_card_formula F25t isOddPrimePower_card_F25t, card_F25t_nat]
  norm_num

noncomputable def ringAutConjEquiv :
    (F25t ≃+* F25t) ≃ (K25 ≃+* K25) where
  toFun f := ringEquiv_F25t.symm.trans (f.trans ringEquiv_F25t)
  invFun g := ringEquiv_F25t.trans (g.trans ringEquiv_F25t.symm)
  left_inv f := by
    apply RingEquiv.ext
    intro x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
  right_inv g := by
    apply RingEquiv.ext
    intro x
    simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]

theorem card_ringAut_F25t : Nat.card (F25t ≃+* F25t) = 2 := by
  rw [Nat.card_congr ringAutConjEquiv, card_ringAut]

instance : Finite (F25t ≃+* F25t) :=
  Finite.of_injective (fun e : F25t ≃+* F25t => (e : F25t → F25t))
    (fun e f h => RingEquiv.ext (congrFun h))

@[expose] def frob25t : F25t ≃+* F25t where
  toFun x := ⟨x.a, -x.b⟩
  invFun x := ⟨x.a, -x.b⟩
  left_inv x := by
    cases x with
    | mk a b =>
      apply F25t.ext
      · rfl
      · simp [neg_neg]
  right_inv x := by
    cases x with
    | mk a b =>
      apply F25t.ext
      · rfl
      · simp [neg_neg]
  map_add' x y := by
    cases x with
    | mk a b =>
      cases y with
      | mk c d =>
        apply F25t.ext <;> simp [add25_def, neg25_def] <;> ring
  map_mul' x y := by
    cases x with
    | mk a b =>
      cases y with
      | mk c d =>
        apply F25t.ext <;> simp [mul25_def, neg25_def] <;> ring

theorem frob25t_mul_self : frob25t * frob25t = 1 := by
  ext x <;> simp [frob25t]

theorem frob25t_ne_one : frob25t ≠ 1 := by
  intro h
  have h1 := congrArg (fun e : F25t ≃+* F25t => e ⟨0, 1⟩) h
  simp [frob25t] at h1
  exact absurd h1 (by decide)

theorem orderOf_frob25t : orderOf frob25t = 2 := by
  refine orderOf_eq_prime ?_ frob25t_ne_one
  rw [pow_two]
  exact frob25t_mul_self

abbrev PSigmaL2t : Type :=
  PSL2 F25t ⋊[CFSG.GorensteinWalter.psl2FieldAut F25t] (F25t ≃+* F25t)

instance : Finite PSigmaL2t :=
  Finite.of_equiv (PSL2 F25t × (F25t ≃+* F25t)) SemidirectProduct.equivProd.symm

theorem card_PSigmaL2t : Nat.card PSigmaL2t = 15600 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    card_PSL2_F25t, card_ringAut_F25t]

def class65t : Set PSigmaL2t :=
  {x | IsConj (SemidirectProduct.inr frob25t) x}

theorem inr_frob25t_mem_class65t : (SemidirectProduct.inr frob25t : PSigmaL2t) ∈ class65t :=
  ⟨1, by simp⟩

theorem zpowers_frob25t_eq_top : Subgroup.zpowers frob25t = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_frob25t, card_ringAut_F25t]

theorem class65t_eq_conjClasses_carrier :
    class65t = (ConjClasses.mk (SemidirectProduct.inr frob25t : PSigmaL2t)).carrier := by
  ext x
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_comm

section CentralizerStabilizer

variable {G : Type*} [Group G]

noncomputable def centralizerEquivStabilizerF25t (g : G) :
    Subgroup.centralizer ({g} : Set G) ≃ MulAction.stabilizer (ConjAct (G := G)) g where
  toFun x := ⟨ConjAct.toConjAct x.1, by
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def]
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_centralizer_iff.mp x.2) g rfl).symm⟩
  invFun y := ⟨ConjAct.toConjAct.symm y.1, by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hy := y.2
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at hy
    exact (mul_inv_eq_iff_eq_mul.mp hy).symm⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

theorem card_stabilizer_eq_card_centralizer (g : G) :
    Nat.card (MulAction.stabilizer (ConjAct (G := G)) g) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) :=
  (Nat.card_congr (centralizerEquivStabilizerF25t g)).symm

end CentralizerStabilizer

theorem card_class65t_mul_card_stabilizer :
    Nat.card class65t * Nat.card (MulAction.stabilizer (ConjAct (G := PSigmaL2t))
      (SemidirectProduct.inr frob25t : PSigmaL2t)) = 15600 := by
  classical
  let d : PSigmaL2t := SemidirectProduct.inr frob25t
  haveI : Fintype PSigmaL2t := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.mk d).carrier := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer (ConjAct (G := PSigmaL2t)) d) := Fintype.ofFinite _
  have h := ConjClasses.card_carrier (G := PSigmaL2t) d
  have hG : Fintype.card PSigmaL2t = 15600 := by
    rw [← Nat.card_eq_fintype_card, card_PSigmaL2t]
  have hdvd0 :
      Nat.card (MulAction.stabilizer (ConjAct (G := PSigmaL2t)) d) ∣ Nat.card PSigmaL2t :=
    Subgroup.card_subgroup_dvd_card _
  rw [Nat.card_eq_fintype_card, card_PSigmaL2t] at hdvd0
  have hdvd : Fintype.card (MulAction.stabilizer (ConjAct (G := PSigmaL2t)) d) ∣ 15600 := hdvd0
  rw [class65t_eq_conjClasses_carrier, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    h, hG]
  exact Nat.div_mul_cancel hdvd

theorem mem_centralizer_inr_frob25t_iff (q : PSL2 F25t) (σ : F25t ≃+* F25t) :
    (SemidirectProduct.mk q σ : PSigmaL2t) ∈
      Subgroup.centralizer ({SemidirectProduct.inr frob25t} : Set PSigmaL2t) ↔
    q = CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hleft := congrArg SemidirectProduct.left h
    change q * (CFSG.GorensteinWalter.psl2FieldAut F25t σ) 1 =
      1 * (CFSG.GorensteinWalter.psl2FieldAut F25t frob25t) q at hleft
    simpa using hleft
  · intro hq
    apply SemidirectProduct.ext
    · change q * (CFSG.GorensteinWalter.psl2FieldAut F25t σ) 1 =
        1 * (CFSG.GorensteinWalter.psl2FieldAut F25t frob25t) q
      simpa using hq
    · have hσ : σ ∈ Subgroup.zpowers frob25t := by
        simpa [zpowers_frob25t_eq_top] using (Subgroup.mem_top σ)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
      change frob25t ^ k * frob25t = frob25t * frob25t ^ k
      rw [← zpow_add_one frob25t k, ← zpow_one_add frob25t k, add_comm]

noncomputable def centralizerEquivFixedProdF25t :
    Subgroup.centralizer ({SemidirectProduct.inr frob25t} : Set PSigmaL2t) ≃
      {q : PSL2 F25t // q = CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q} ×
        (F25t ≃+* F25t) where
  toFun x := (⟨x.1.left, (mem_centralizer_inr_frob25t_iff x.1.left x.1.right).mp x.2⟩, x.1.right)
  invFun y := ⟨SemidirectProduct.mk y.1.1 y.2,
    (mem_centralizer_inr_frob25t_iff y.1.1 y.2).mpr y.1.2⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

theorem card_centralizer_inr_frob25t :
    Nat.card (Subgroup.centralizer ({SemidirectProduct.inr frob25t} : Set PSigmaL2t)) =
      Nat.card {q : PSL2 F25t //
        q = CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q} * 2 := by
  rw [Nat.card_congr centralizerEquivFixedProdF25t, Nat.card_prod, card_ringAut_F25t]

theorem card_stabilizer_inr_frob25t :
    Nat.card (MulAction.stabilizer (ConjAct (G := PSigmaL2t))
      (SemidirectProduct.inr frob25t : PSigmaL2t)) =
    Nat.card (Subgroup.centralizer ({SemidirectProduct.inr frob25t} : Set PSigmaL2t)) :=
  card_stabilizer_eq_card_centralizer _

theorem card_class65t_mul_card_centralizer :
    Nat.card class65t * Nat.card (Subgroup.centralizer
      ({SemidirectProduct.inr frob25t} : Set PSigmaL2t)) = 15600 := by
  rw [← card_stabilizer_inr_frob25t]
  exact card_class65t_mul_card_stabilizer

theorem card_class65t_mul_card_fix :
    Nat.card class65t * (Nat.card {q : PSL2 F25t //
      q = CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q} * 2) = 15600 := by
  rw [← card_centralizer_inr_frob25t]
  exact card_class65t_mul_card_centralizer

theorem card_class65t_of_card_fix
    (h : Nat.card {q : PSL2 F25t //
      q = CFSG.GorensteinWalter.psl2FieldAut F25t frob25t q} = 120) :
    Nat.card class65t = 65 := by
  have := card_class65t_mul_card_fix
  rw [h] at this
  omega

end CFSG.OddTranspositions.QZ
