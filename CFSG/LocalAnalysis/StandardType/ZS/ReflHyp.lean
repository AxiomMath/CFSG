module

public import CFSG.Fischer.Classification.Basic.SixObstruction
public import CFSG.Fischer.Classification.Skeleton
public import CFSG.LocalAnalysis.StandardType.ZS.NoNormalTwoThree
public import CFSG.LocalAnalysis.StandardType.ZS.ReflGraph
public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.SixReflections
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  [Module.Finite (ZMod p) U]

local notation "GLU" => (U ≃ₗ[ZMod p] U)

omit [Module.Finite (ZMod p) U] in
theorem IsRefl.inv_eq_self {A : Subgroup GLU} {x : ↥A}
    (hx : IsRefl p (x : GLU)) : x⁻¹ = x := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_one]
  exact hx.1

omit [Module.Finite (ZMod p) U] in
theorem IsRefl.conj_mem {A : Subgroup GLU} {x y : ↥A} (hx : IsRefl p (x : GLU)) :
    IsRefl p (((y * x * y⁻¹ : ↥A) : GLU)) := by
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx.conj (y : GLU)

omit [Module.Finite (ZMod p) U] in
theorem IsRefl.conj_mul_self {A : Subgroup GLU} {x y : ↥A}
    (hx : IsRefl p (x : GLU)) (hy : IsRefl p (y : GLU)) :
    IsRefl p (((y * x * y : ↥A) : GLU)) := by
  have h := hx.conj_mem (A := A) (y := y)
  rwa [hy.inv_eq_self] at h

omit [Module.Finite (ZMod p) U] in
theorem orderOf_mul_eq_two_of_commute_refl {A : Subgroup GLU} {x y : ↥A}
    (hx : IsRefl p (x : GLU)) (hy : IsRefl p (y : GLU))
    (hcomm : Commute (x : GLU) (y : GLU)) (hne : (x : GLU) ≠ (y : GLU)) :
    orderOf ((x : GLU) * (y : GLU)) = 2 := by
  have hx2 : (x : GLU) * (x : GLU) = 1 := hx.1
  have hy2 : (y : GLU) * (y : GLU) = 1 := hy.1
  have hsq : ((x : GLU) * (y : GLU)) * ((x : GLU) * (y : GLU)) = 1 := by
    calc ((x : GLU) * (y : GLU)) * ((x : GLU) * (y : GLU))
        = (x : GLU) * ((y : GLU) * (x : GLU)) * (y : GLU) := by group
      _ = (x : GLU) * ((x : GLU) * (y : GLU)) * (y : GLU) := by rw [← hcomm.eq]
      _ = ((x : GLU) * (x : GLU)) * ((y : GLU) * (y : GLU)) := by group
      _ = 1 := by rw [hx2, hy2, one_mul]
  have hne1 : (x : GLU) * (y : GLU) ≠ 1 := by
    intro h
    have hyx : (y : GLU) = (x : GLU) := by
      calc (y : GLU) = ((x : GLU) * (x : GLU)) * (y : GLU) := by rw [hx2, one_mul]
        _ = (x : GLU) * ((x : GLU) * (y : GLU)) := by group
        _ = (x : GLU) * 1 := by rw [h]
        _ = (x : GLU) := mul_one (x : GLU)
    exact hne hyx.symm
  exact orderOf_eq_prime (by simpa [pow_two] using hsq) hne1

theorem orderOf_mul_eq_three_of_not_commute {A : Subgroup GLU} {x y : ↥A}
    (hx : IsRefl p (x : GLU)) (hy : IsRefl p (y : GLU))
    (hnc : ¬ Commute (x : GLU) (y : GLU))
    (hle : orderOf ((x : GLU) * (y : GLU)) ≤ 3) :
    orderOf ((x : GLU) * (y : GLU)) = 3 := by
  have hx2 : (x : GLU) * (x : GLU) = 1 := hx.1
  have hy2 : (y : GLU) * (y : GLU) = 1 := hy.1
  have hpos : 0 < orderOf ((x : GLU) * (y : GLU)) := orderOf_pos _
  have hne1 : orderOf ((x : GLU) * (y : GLU)) ≠ 1 := by
    intro h1
    have hxy : (x : GLU) * (y : GLU) = 1 := orderOf_eq_one_iff.mp h1
    have hyx : (y : GLU) = (x : GLU) := by
      calc (y : GLU) = ((x : GLU) * (x : GLU)) * (y : GLU) := by rw [hx2, one_mul]
        _ = (x : GLU) * ((x : GLU) * (y : GLU)) := by group
        _ = (x : GLU) * 1 := by rw [hxy]
        _ = (x : GLU) := mul_one (x : GLU)
    exact hnc (by rw [hyx])
  have hne2 : orderOf ((x : GLU) * (y : GLU)) ≠ 2 := by
    intro h2
    have hsq : ((x : GLU) * (y : GLU)) * ((x : GLU) * (y : GLU)) = 1 := by
      have h := pow_orderOf_eq_one ((x : GLU) * (y : GLU))
      rwa [h2, pow_two] at h
    have hyx : (y : GLU) * (x : GLU) = (x : GLU) * (y : GLU) := by
      calc (y : GLU) * (x : GLU)
          = ((x : GLU) * (x : GLU)) * ((y : GLU) * (x : GLU)) *
            ((y : GLU) * (y : GLU)) := by rw [hx2, hy2, one_mul, mul_one]
        _ = (x : GLU) * (((x : GLU) * (y : GLU)) * ((x : GLU) * (y : GLU))) *
            (y : GLU) := by group
        _ = (x : GLU) * 1 * (y : GLU) := by rw [hsq]
        _ = (x : GLU) * (y : GLU) := by group
    exact hnc hyx.symm
  omega

private theorem zrh_commute_ambient {A : Subgroup GLU} (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U) {x y : ↥A} (hy : IsRefl p (y : GLU))
    (h : Commute (QuotientGroup.mk x : ↥A ⧸ Subgroup.center ↥A)
      (QuotientGroup.mk y : ↥A ⧸ Subgroup.center ↥A)) :
    Commute (x : GLU) (y : GLU) :=
  ((hirr.commute_mk_iff hn (t := y) hy).mp h).map A.subtype

omit [Module.Finite (ZMod p) U] in
private theorem zrh_not_commute_ambient {A : Subgroup GLU} {x y : ↥A}
    (hnc : ¬ Commute (QuotientGroup.mk x : ↥A ⧸ Subgroup.center ↥A)
      (QuotientGroup.mk y : ↥A ⧸ Subgroup.center ↥A)) :
    ¬ Commute (x : GLU) (y : GLU) := by
  intro h
  have hxy : Commute x y :=
    (commute_map_iff (f := A.subtype) (Subgroup.subtype_injective A)).mp h
  apply hnc
  simpa only [QuotientGroup.coe_mk'] using hxy.map (QuotientGroup.mk' (Subgroup.center ↥A))

private structure zrh_Lift (A : Subgroup GLU) (x : ↥A ⧸ Subgroup.center ↥A) where
  elt : ↥A
  isRefl : IsRefl p (elt : GLU)
  mk_eq : QuotientGroup.mk elt = x

private noncomputable def zrh_lift {A : Subgroup GLU} (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    {x : ↥A ⧸ Subgroup.center ↥A} (hx : x ∈ reflImage p A) : zrh_Lift A x :=
  let t := Classical.choose (exists_unique_refl_of_mem_reflImage hirr hn hx)
  let ht := (Classical.choose_spec (exists_unique_refl_of_mem_reflImage hirr hn hx)).1
  ⟨t, ht.1, ht.2⟩

private structure zrh_BaseOrders (A : Subgroup GLU) (aA bA cA sA : ↥A) where
  hac : orderOf ((aA : GLU) * (cA : GLU)) = 2
  hab : orderOf ((aA : GLU) * (bA : GLU)) = 3
  hbc : orderOf ((bA : GLU) * (cA : GLU)) = 3
  hsa : orderOf ((sA : GLU) * (aA : GLU)) = 3
  hsb : orderOf ((sA : GLU) * (bA : GLU)) = 3
  hsc : orderOf ((sA : GLU) * (cA : GLU)) = 3

private structure zrh_ConjOrders (A : Subgroup GLU) (aA bA cA sA : ↥A) where
  hs1 : orderOf ((sA : GLU) * ((bA : GLU) * (aA : GLU) * (bA : GLU))) = 3
  hs2 : orderOf ((sA : GLU) * ((bA : GLU) * (cA : GLU) * (bA : GLU))) = 3
  hs3 : orderOf ((sA : GLU) * ((aA : GLU) * (cA : GLU) * (bA : GLU) *
    (cA : GLU) * (aA : GLU))) = 3

private theorem zrh_base_orders {A : Subgroup GLU} (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {a b c s : ↥A ⧸ Subgroup.center ↥A} {aA bA cA sA : ↥A}
    (ha : IsRefl p (aA : GLU)) (hb : IsRefl p (bA : GLU))
    (hc : IsRefl p (cA : GLU)) (hs : IsRefl p (sA : GLU))
    (hmka : QuotientGroup.mk aA = a) (hmkb : QuotientGroup.mk bA = b)
    (hmkc : QuotientGroup.mk cA = c) (hmks : QuotientGroup.mk sA = s)
    (hac_ne : a ≠ c) (hac_comm : a * c = c * a)
    (hab_nc : a * b ≠ b * a) (hbc_nc : b * c ≠ c * b)
    (hsa_nc : s * a ≠ a * s) (hsb_nc : s * b ≠ b * s) (hsc_nc : s * c ≠ c * s) :
    zrh_BaseOrders A aA bA cA sA := by
  have hac_comm_amb : Commute (aA : GLU) (cA : GLU) :=
    zrh_commute_ambient hirr hn hc (by rw [hmka, hmkc]; exact hac_comm)
  have hne_ac : (aA : GLU) ≠ (cA : GLU) := by
    intro h
    apply hac_ne
    calc a = QuotientGroup.mk aA := hmka.symm
      _ = QuotientGroup.mk cA := congrArg QuotientGroup.mk (Subtype.ext h)
      _ = c := hmkc
  have hab_nc_amb : ¬ Commute (aA : GLU) (bA : GLU) :=
    zrh_not_commute_ambient (x := aA) (y := bA) (by rw [hmka, hmkb]; exact hab_nc)
  have hbc_nc_amb : ¬ Commute (bA : GLU) (cA : GLU) :=
    zrh_not_commute_ambient (x := bA) (y := cA) (by rw [hmkb, hmkc]; exact hbc_nc)
  have hsa_nc_amb : ¬ Commute (sA : GLU) (aA : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := aA) (by rw [hmks, hmka]; exact hsa_nc)
  have hsb_nc_amb : ¬ Commute (sA : GLU) (bA : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := bA) (by rw [hmks, hmkb]; exact hsb_nc)
  have hsc_nc_amb : ¬ Commute (sA : GLU) (cA : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := cA) (by rw [hmks, hmkc]; exact hsc_nc)
  refine ⟨orderOf_mul_eq_two_of_commute_refl ha hc hac_comm_amb hne_ac,
    orderOf_mul_eq_three_of_not_commute ha hb hab_nc_amb (h3 (aA : GLU) aA.2 (bA : GLU) bA.2 ha hb),
    orderOf_mul_eq_three_of_not_commute hb hc hbc_nc_amb (h3 (bA : GLU) bA.2 (cA : GLU) cA.2 hb hc),
    orderOf_mul_eq_three_of_not_commute hs ha hsa_nc_amb (h3 (sA : GLU) sA.2 (aA : GLU) aA.2 hs ha),
    orderOf_mul_eq_three_of_not_commute hs hb hsb_nc_amb (h3 (sA : GLU) sA.2 (bA : GLU) bA.2 hs hb),
    orderOf_mul_eq_three_of_not_commute hs hc hsc_nc_amb (h3 (sA : GLU) sA.2 (cA : GLU) cA.2 hs hc)⟩

private theorem zrh_conj_orders {A : Subgroup GLU}
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {a b c s : ↥A ⧸ Subgroup.center ↥A} {aA bA cA sA : ↥A}
    (ha : IsRefl p (aA : GLU)) (hb : IsRefl p (bA : GLU))
    (hc : IsRefl p (cA : GLU)) (hs : IsRefl p (sA : GLU))
    (hmka : QuotientGroup.mk aA = a) (hmkb : QuotientGroup.mk bA = b)
    (hmkc : QuotientGroup.mk cA = c) (hmks : QuotientGroup.mk sA = s)
    (hs1_nc : s * (b * a * b) ≠ b * a * b * s)
    (hs2_nc : s * (b * c * b) ≠ b * c * b * s)
    (hs3_nc : s * (a * c * b * c * a) ≠ a * c * b * c * a * s) :
    zrh_ConjOrders A aA bA cA sA := by
  let w1 : ↥A := bA * aA * bA
  let w2 : ↥A := bA * cA * bA
  let w3 : ↥A := aA * cA * bA * cA * aA
  have hw1 : IsRefl p (w1 : GLU) := ha.conj_mul_self hb
  have hw2 : IsRefl p (w2 : GLU) := hc.conj_mul_self hb
  have hw3_eq : w3 = (aA * cA) * bA * (aA * cA)⁻¹ := by
    rw [mul_inv_rev, hc.inv_eq_self, ha.inv_eq_self]
    simp only [w3]
    group
  have hw3 : IsRefl p (w3 : GLU) := by
    rw [hw3_eq]
    exact hb.conj_mem (y := aA * cA)
  have hw1_mk : QuotientGroup.mk w1 = b * a * b := by
    simp only [w1, QuotientGroup.mk_mul, hmka, hmkb]
  have hw2_mk : QuotientGroup.mk w2 = b * c * b := by
    simp only [w2, QuotientGroup.mk_mul, hmkb, hmkc]
  have hw3_mk : QuotientGroup.mk w3 = a * c * b * c * a := by
    simp only [w3, QuotientGroup.mk_mul, hmka, hmkc, hmkb]
  have hn1 : ¬ Commute (sA : GLU) (w1 : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := w1) (by rw [hmks, hw1_mk]; exact hs1_nc)
  have hn2 : ¬ Commute (sA : GLU) (w2 : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := w2) (by rw [hmks, hw2_mk]; exact hs2_nc)
  have hn3 : ¬ Commute (sA : GLU) (w3 : GLU) :=
    zrh_not_commute_ambient (x := sA) (y := w3) (by rw [hmks, hw3_mk]; exact hs3_nc)
  have ho1 : orderOf ((sA : GLU) * (w1 : GLU)) = 3 :=
    orderOf_mul_eq_three_of_not_commute hs hw1 hn1 (h3 (sA : GLU) sA.2 (w1 : GLU) w1.2 hs hw1)
  have ho2 : orderOf ((sA : GLU) * (w2 : GLU)) = 3 :=
    orderOf_mul_eq_three_of_not_commute hs hw2 hn2 (h3 (sA : GLU) sA.2 (w2 : GLU) w2.2 hs hw2)
  have ho3 : orderOf ((sA : GLU) * (w3 : GLU)) = 3 :=
    orderOf_mul_eq_three_of_not_commute hs hw3 hn3 (h3 (sA : GLU) sA.2 (w3 : GLU) w3.2 hs hw3)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [w1, Subgroup.coe_mul] using ho1
  · simpa only [w2, Subgroup.coe_mul] using ho2
  · simpa only [w3, Subgroup.coe_mul] using ho3

private theorem zrh_false_of_six (hp : p ≠ 2) {A : Subgroup GLU} (hirr : AbsIrred p A)
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {a b c s : ↥A ⧸ Subgroup.center ↥A}
    (ha : a ∈ reflImage p A) (hb : b ∈ reflImage p A)
    (hc : c ∈ reflImage p A) (hs : s ∈ reflImage p A)
    (hac_ne : a ≠ c) (hac_comm : a * c = c * a)
    (hab_nc : a * b ≠ b * a) (hbc_nc : b * c ≠ c * b)
    (hsa_nc : s * a ≠ a * s) (hsb_nc : s * b ≠ b * s) (hsc_nc : s * c ≠ c * s)
    (hs1_nc : s * (b * a * b) ≠ b * a * b * s)
    (hs2_nc : s * (b * c * b) ≠ b * c * b * s)
    (hs3_nc : s * (a * c * b * c * a) ≠ a * c * b * c * a * s) : False := by
  let La := zrh_lift hirr hn ha
  let Lb := zrh_lift hirr hn hb
  let Lc := zrh_lift hirr hn hc
  let Ls := zrh_lift hirr hn hs
  have BO := zrh_base_orders hirr hn h3 La.isRefl Lb.isRefl Lc.isRefl Ls.isRefl
    La.mk_eq Lb.mk_eq Lc.mk_eq Ls.mk_eq hac_ne hac_comm hab_nc hbc_nc hsa_nc hsb_nc hsc_nc
  have CO := zrh_conj_orders h3 La.isRefl Lb.isRefl Lc.isRefl Ls.isRefl
    La.mk_eq Lb.mk_eq Lc.mk_eq Ls.mk_eq hs1_nc hs2_nc hs3_nc
  exact false_of_six_of_isRefl hp La.isRefl Lb.isRefl Lc.isRefl Ls.isRefl
    BO.hac BO.hab BO.hbc BO.hsa BO.hsb BO.hsc CO.hs1 CO.hs2 CO.hs3

theorem oneClass_of_orderOf_mul_le_three (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3) : OneClass p A := by
  intro x hx y hy hxr hyr
  obtain ⟨g, hgA, hg⟩ :=
    exists_conj_of_orderOf_mul_le_three hp hgen hirr.1 h3 hx hxr hy hyr
  exact ⟨g, hgA, hg.symm⟩

theorem hyp_reflImage (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hn : 4 ≤ Module.finrank (ZMod p) U) (hgen : ReflGen p A) (hirr : AbsIrred p A)
    (hprim : ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV A)
    (h3 : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3) :
    CFSG.Fischer.Classification.Hyp (↥A ⧸ Subgroup.center ↥A) (reflImage p A) := by
  have hn3 : 3 ≤ Module.finrank (ZMod p) U := by omega
  have hone : OneClass p A := oneClass_of_orderOf_mul_le_three hp hgen hirr h3
  have hP : CFSG.Blueprint.Fischer.Pair (↥A ⧸ Subgroup.center ↥A) (reflImage p A) :=
    pair_reflImage hgen hirr hn3 hone h3
  have hZ : Subgroup.center (↥A ⧸ Subgroup.center ↥A) = ⊥ :=
    center_quotient_center_eq_bot hgen hirr hn3
  have h2 : ∀ N : Subgroup (↥A ⧸ Subgroup.center ↥A), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hNr =>
      eq_bot_of_isPGroup_of_normal hp hn hgen hirr hprim h3 (Or.inl rfl) hN hNr
  have h3N : ∀ N : Subgroup (↥A ⧸ Subgroup.center ↥A), N.Normal → IsPGroup 3 N → N = ⊥ :=
    fun N hN hNr =>
      eq_bot_of_isPGroup_of_normal hp hn hgen hirr hprim h3 (Or.inr rfl) hN hNr
  refine ⟨hP, hZ, ?_⟩
  refine CFSG.Fischer.Classification.Pair.isSimpleGroup_commutator_of_six hP hZ h2 h3N ?_
  intro a ha b hb c hc s hs hac_ne hac_comm hab_nc hbc_nc hsa_nc hsb_nc hsc_nc hs1_nc hs2_nc
    hs3_nc
  exact zrh_false_of_six hp hirr hn3 h3 ha hb hc hs hac_ne hac_comm hab_nc hbc_nc hsa_nc
    hsb_nc hsc_nc hs1_nc hs2_nc hs3_nc

end CFSG.StandardType.ZS
