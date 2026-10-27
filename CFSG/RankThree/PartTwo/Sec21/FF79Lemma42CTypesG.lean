module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.GroupTheory.GL52.OrderThreeCover
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Open.StatedZModTwo
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.GroupTheory.GL52.OrderThreeTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TypesG

open CFSG.GroupTheory.GL52 Matrix CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G]

theorem trace_gl3 : ∀ B : Matrix (Fin 3) (Fin 3) (ZMod 2), B ^ 3 = 1 → B ≠ 1 → B.trace = 0 := by
  decide +kernel

theorem trace_K2M (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (ord3K2M B).trace = B.trace := by
  simp only [Matrix.trace, Matrix.diag, ord3K2M, Fin.sum_univ_five, Fin.sum_univ_three]
  simp
  decide +revert

theorem trace_T4_sq : Matrix.trace (ord3T4M ^ 2) = 1 := by decide +kernel

theorem trace_of_mem_K2 {k : G52} (hk : k ∈ ord3K2) (h3 : orderOf k = 3) :
    Matrix.trace (k : M5) = 0 := by
  obtain ⟨B, rfl⟩ := hk
  have hB3 : orderOf B = 3 := (orderOf_injective _ ord3K2Hom_injective B).symm.trans h3
  have h1 : B ≠ 1 := fun h => by rw [h, orderOf_one] at hB3; omega
  have hpow : B ^ 3 = 1 := by
    have := pow_orderOf_eq_one B
    rwa [hB3] at this
  rw [coe_ord3K2Hom, trace_K2M]
  refine trace_gl3 _ ?_ ?_
  · have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) hpow
    simpa [Units.val_pow_eq_pow_val] using this
  · intro h
    exact h1 (Units.ext h)

theorem trace_of_mem_K4 {k : G52} (hk : k ∈ ord3K4) (h3 : orderOf k = 3) :
    Matrix.trace (k : M5) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, hy₀K, hy₀3, hdc⟩ := ord3_exists_T4_mem_K4
  obtain ⟨e4⟩ := ord3_K4_equiv
  have hcard : Nat.card ↥ord3K4 = 3 * 20 := by
    rw [Nat.card_congr e4.toEquiv, ord3_card_SL2_F4]
  let y' : ↥ord3K4 := ⟨y₀, hy₀K⟩
  let k' : ↥ord3K4 := ⟨k, hk⟩
  have hy'3 : orderOf y' = 3 := (orderOf_submonoid y').symm.trans hy₀3
  have hk'3 : orderOf k' = 3 := (orderOf_submonoid k').symm.trans h3
  obtain ⟨P₀, hP₀⟩ := (IsPGroup.of_card (p := 3) (n := 1) (G := Subgroup.zpowers y')
    (by rw [Nat.card_zpowers, hy'3, pow_one])).exists_le_sylow
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 3) (n := 1) (G := Subgroup.zpowers k')
    (by rw [Nat.card_zpowers, hk'3, pow_one])).exists_le_sylow
  have hP₀card : Nat.card P₀ = 3 := card_sylow_of_card_eq_prime_mul hcard (by norm_num) P₀
  have hP₀eq : (P₀ : Subgroup ↥ord3K4) = Subgroup.zpowers y' :=
    (Subgroup.eq_of_le_of_card_ge hP₀ (by rw [hP₀card, Nat.card_zpowers, hy'3])).symm
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow P₀ Q
  have hkQ : k' ∈ (Q : Subgroup ↥ord3K4) := hQ (Subgroup.mem_zpowers k')
  rw [hc, hP₀eq] at hkQ
  obtain ⟨z, hz, hzk⟩ := Subgroup.mem_map.mp hkQ
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hkc : k = (c : G52) * y₀ ^ i * (c : G52)⁻¹ := by
    have := congrArg Subtype.val hzk
    simpa using this.symm
  have hi : i % 3 = 1 ∨ i % 3 = 2 := by
    by_contra hcon
    have h0 : i % 3 = 0 := by omega
    have : y₀ ^ i = 1 := by
      have h := zpow_mod_orderOf y₀ i
      rw [hy₀3] at h
      rw [← h]
      simp [h0]
    rw [this] at hkc
    simp at hkc
    rw [hkc, orderOf_one] at h3
    omega
  have hy₀i : y₀ ^ i = y₀ ^ (i % 3) := by
    have h := zpow_mod_orderOf y₀ i
    rw [hy₀3] at h
    simpa using h.symm
  have hconj : IsConj (y₀ ^ i) k := by
    rw [isConj_iff]
    exact ⟨(c : G52), hkc.symm⟩
  rw [trace_eq_of_isConj hconj, hy₀i]
  rcases hi with h | h <;> rw [h]
  · rw [zpow_one, trace_eq_of_isConj hdc, coe_ord3T4, ord3_trace_T4]
  · obtain ⟨d, hd⟩ := isConj_iff.mp hdc
    have h2 : IsConj (ord3T4 ^ 2) (y₀ ^ 2) := by
      rw [isConj_iff]
      exact ⟨d, by rw [← hd, conj_pow]⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, trace_eq_of_isConj h2,
      Units.val_pow_eq_pow_val, coe_ord3T4, trace_T4_sq]

private theorem layer_eq_of_normal_quasisimple {Y : Type*} [Group Y] (E : Subgroup Y) [E.Normal]
    (hE : CFSG.IsQuasisimple ↥E) (hsolv : Group.IsSolvable (Y ⧸ E)) : CFSG.layer Y = E := by
  refine le_antisymm (sSup_le fun K hK => ?_)
    (le_sSup ⟨hE, Subgroup.Normal.isSubnormal inferInstance⟩)
  have : Group.IsPerfect ↥K := hK.1.1
  let f : ↥K →* Y ⧸ E := (QuotientGroup.mk' E).comp K.subtype
  have : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have := hsolv
  intro x hx
  by_contra hxE
  have hnt : Nontrivial ↥f.range := by
    refine ⟨⟨⟨f ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩, 1, fun h => hxE ?_⟩⟩
    have h1 : f ⟨x, hx⟩ = 1 := congrArg Subtype.val h
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact Group.IsPerfect.not_isSolvable ↥f.range inferInstance

private theorem lay_eq_of_sup {A K C : Subgroup G} (hsup : A ⊔ K = C)
    (hcomm : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    [IsSimpleGroup K] (hK : ∃ a b : K, a * b ≠ b * a) : Lay C = K := by
  have hKC : K ≤ C := le_sup_right.trans hsup.le
  have hAC : A ≤ C := le_sup_left.trans hsup.le
  have hAN : A ≤ Nor K := fun a ha => Subgroup.mem_normalizer_iff.mpr fun k => by
    constructor
    · intro hk
      rw [hcomm a ha k hk, mul_inv_cancel_right]
      exact hk
    · intro hk
      have h1 : a⁻¹ * (a * k * a⁻¹) = a * k * a⁻¹ * a⁻¹ := hcomm a⁻¹ (inv_mem ha) _ hk
      have h2 : a⁻¹ * (a * k * a⁻¹) = k * a⁻¹ := by group
      rw [h2] at h1
      rw [mul_right_cancel h1]
      exact hk
  have hCN : C ≤ Nor K := hsup.ge.trans (sup_le hAN Subgroup.le_normalizer)
  haveI : (K.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mpr hCN
  let eK : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  haveI : IsSimpleGroup ↥(K.subgroupOf C) := eK.isSimpleGroup
  have hnab : ∃ a b : ↥(K.subgroupOf C), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK
    refine ⟨eK.symm a, eK.symm b, fun h => hab ?_⟩
    have := congrArg eK h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hE := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  let ψ : ↥(A.subgroupOf C) →* ↥C ⧸ K.subgroupOf C :=
    (QuotientGroup.mk' (K.subgroupOf C)).comp (A.subgroupOf C).subtype
  have hψ : Function.Surjective ψ := by
    have hle : A.subgroupOf C ⊔ K.subgroupOf C ≤
        ψ.range.comap (QuotientGroup.mk' (K.subgroupOf C)) := by
      refine sup_le (fun a ha => Subgroup.mem_comap.mpr ⟨⟨a, ha⟩, rfl⟩) fun k hk =>
        Subgroup.mem_comap.mpr ?_
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
      exact one_mem _
    rw [← Subgroup.subgroupOf_sup hAC hKC, hsup, Subgroup.subgroupOf_self] at hle
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf C) q
    exact MonoidHom.mem_range.mp (Subgroup.mem_comap.mp (hle (Subgroup.mem_top c)))
  haveI : Group.IsSolvable ↥(A.subgroupOf C) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (Subtype.ext (hA _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))
  have hlay := layer_eq_of_normal_quasisimple (K.subgroupOf C) hE
    (Group.isSolvable_of_surjective hψ)
  show (CFSG.layer ↥C).map C.subtype = K
  rw [hlay, Subgroup.subgroupOf_map_subtype, inf_of_le_left hKC]

private theorem exists_mul_ne_of_not_prime {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hQ : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := h }
  exact hQ IsSimpleGroup.prime_card

private theorem isLnq_of_equiv_SL2F4 {K : Subgroup G}
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F4) : IsLnq 2 2 2 K :=
  ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, F4, inferInstance, inferInstance,
    card_F4.trans (by norm_num),
    ⟨e.trans (((QuotientGroup.quotientMulEquivOfEq ord3_center_SL2_F4).trans
      QuotientGroup.quotientBot).symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F4))⟩⟩

private theorem isLnq_of_equiv_GL3 {K : Subgroup G} (e : K ≃* GL (Fin 3) (ZMod 2)) :
    IsLnq 3 2 1 K :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two le_rfl
    (e.trans (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr
      (CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two (K := ZMod 2) (by simp) 3).symm)))


private theorem isInnerDirectProduct_map' {A B C : Subgroup G52} (f : G52 →* G52)
    (hf : Function.Injective f) (h : IsInnerDirectProduct A B C) :
    IsInnerDirectProduct (A.map f) (B.map f) (C.map f) := by
  obtain ⟨hsup, hinf, hcomm⟩ := h
  refine ⟨by rw [← Subgroup.map_sup, hsup], by rw [← Subgroup.map_inf_eq _ _ _ hf, hinf,
    Subgroup.map_bot], ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, hcomm a ha b hb]

theorem g52_type {y : G52} (hy : orderOf y = 3) :
    ∃ K : Subgroup G52, Lay (Cen y) = K ∧
      IsInnerDirectProduct (Subgroup.zpowers y) K (Cen y) ∧
      ((Matrix.trace (y : M5) = 1 ∧ IsLnq 2 2 2 K) ∨
        (Matrix.trace (y : M5) = 0 ∧ IsLnq 3 2 1 K)) ∧
      ∀ k ∈ K, orderOf k = 3 → Matrix.trace (k : M5) = Matrix.trace (y : M5) := by
  rcases ord3_classify hy with ⟨-, hc⟩ | ⟨-, hc⟩
  ·
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    set f := (MulAut.conj c).toMonoidHom with hf
    have hinj : Function.Injective f := (MulAut.conj c).injective
    have hdp : IsInnerDirectProduct (Subgroup.zpowers (c * ord3T2 * c⁻¹)) (ord3K2.map f)
        (Cen (c * ord3T2 * c⁻¹)) := by
      have h := isInnerDirectProduct_map' f hinj ord3_centralizer_T2
      rwa [MonoidHom.map_zpowers, hf, ← centralizer_conj] at h
    obtain ⟨e2⟩ := ord3_K2_equiv_GL
    haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
    let eK : ↥(ord3K2.map f) ≃* GL (Fin 3) (ZMod 2) :=
      (Subgroup.equivMapOfInjective ord3K2 f hinj).symm.trans e2
    haveI : IsSimpleGroup ↥(ord3K2.map f) := eK.isSimpleGroup
    have hnab : ∃ a b : ↥(ord3K2.map f), a * b ≠ b * a := exists_mul_ne_of_not_prime (by
      rw [Nat.card_congr eK.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]
      norm_num)
    refine ⟨ord3K2.map f, lay_eq_of_sup hdp.1 hdp.2.2 ?_ hnab, hdp, Or.inr ⟨?_, ?_⟩, ?_⟩
    · rintro _ ha _ hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self _ i j).eq
    · rw [trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩), coe_ord3T2]
      exact syl3_trace_ab.1
    · exact isLnq_of_equiv_GL3 eK
    · rintro _ ⟨k₀, hk₀, rfl⟩ h3
      have h3' : orderOf k₀ = 3 := (orderOf_injective f hinj k₀).symm.trans h3
      rw [trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩), coe_ord3T2, syl3_trace_ab.1,
        show f k₀ = c * k₀ * c⁻¹ from rfl]
      have := trace_of_mem_K2 hk₀ h3'
      rwa [← trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩)] at this
  ·
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    set f := (MulAut.conj c).toMonoidHom with hf
    have hinj : Function.Injective f := (MulAut.conj c).injective
    have hdp : IsInnerDirectProduct (Subgroup.zpowers (c * ord3T4 * c⁻¹)) (ord3K4.map f)
        (Cen (c * ord3T4 * c⁻¹)) := by
      have h := isInnerDirectProduct_map' f hinj ord3_centralizer_T4
      rwa [MonoidHom.map_zpowers, hf, ← centralizer_conj] at h
    obtain ⟨e4⟩ := ord3_K4_equiv
    haveI := ord3_isSimple_SL2_F4
    let eK : ↥(ord3K4.map f) ≃* Matrix.SpecialLinearGroup (Fin 2) F4 :=
      (Subgroup.equivMapOfInjective ord3K4 f hinj).symm.trans e4
    haveI : IsSimpleGroup ↥(ord3K4.map f) := eK.isSimpleGroup
    have hnab : ∃ a b : ↥(ord3K4.map f), a * b ≠ b * a := exists_mul_ne_of_not_prime (by
      rw [Nat.card_congr eK.toEquiv, ord3_card_SL2_F4]
      norm_num)
    refine ⟨ord3K4.map f, lay_eq_of_sup hdp.1 hdp.2.2 ?_ hnab, hdp, Or.inl ⟨?_, ?_⟩, ?_⟩
    · rintro _ ha _ hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_zpow_self _ i j).eq
    · rw [trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩), coe_ord3T4]
      exact ord3_trace_T4
    · exact isLnq_of_equiv_SL2F4 eK
    · rintro _ ⟨k₀, hk₀, rfl⟩ h3
      have h3' : orderOf k₀ = 3 := (orderOf_injective f hinj k₀).symm.trans h3
      rw [trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩), coe_ord3T4, ord3_trace_T4,
        show f k₀ = c * k₀ * c⁻¹ from rfl]
      have := trace_of_mem_K4 hk₀ h3'
      rwa [← trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩)] at this

end CFSG.RankThree.PartTwo.Sec21.FF79.TypesG
