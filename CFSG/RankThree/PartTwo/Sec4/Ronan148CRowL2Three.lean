module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GH74.GLS (pPrimeCoreOf)
open CFSG.GorensteinWalter (PSL2 PGL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction pglAction_toPGL
  semilinearEquivAut)
open CFSG.Assembly.RankThreeEven (projSL)

section L2

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem card_centralizer_of_isConj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective,
    map_centralizer_singleton]
  rfl

theorem isPGroup_centralizer_psl2 (h3 : ringChar K = 3) (hq : 5 ≤ Fintype.card K)
    {x : PSL2 K} (hx : orderOf x = 3) : IsPGroup 3 (Subgroup.centralizer ({x} : Set (PSL2 K))) := by
  haveI : CharP K 3 := ringChar.of_eq h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : ringChar K ≠ 2 := by rw [h3]; norm_num
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have hn1 : 1 ≤ (n : ℕ) := n.2
  have hof : ∀ {y : PSL2 K}, IsConj x y → orderOf y = 3 := by
    intro y hxy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    rw [← hx]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  have hpg : ∀ {t : K}, t ≠ 0 → IsConj x (CFSG.PSL2Table.mk (CFSG.PSL2Table.unip t)) →
      IsPGroup 3 (Subgroup.centralizer ({x} : Set (PSL2 K))) := by
    intro t ht hxt
    refine IsPGroup.of_card (n := n) ?_
    rw [card_centralizer_of_isConj hxt, CFSG.PSL2Table.card_centralizer_unip hF ht, hn]
  rcases CFSG.PSL2Table.conj_cases hF hq hν x with h1 | h1 | h1 | ⟨y, hyT, -, hxy⟩ |
    ⟨y, hyS, -, hxy⟩
  · exfalso
    rw [h1, orderOf_one] at hx
    omega
  · exact hpg one_ne_zero h1
  · exact hpg (fun h0 => hν (by rw [h0]; exact ⟨0, by ring⟩)) h1
  · exfalso
    have hy3 : orderOf (⟨y, hyT⟩ : CFSG.PSL2Table.splitTorus K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hof hxy
    have hdvd := orderOf_dvd_natCard (⟨y, hyT⟩ : CFSG.PSL2Table.splitTorus K)
    rw [hy3] at hdvd
    have hT := CFSG.PSL2Table.card_splitTorus (F := K) (Ring.two_ne_zero hF)
    rw [hn] at hT
    obtain ⟨k, hk⟩ := hdvd
    have h3n : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 (by omega)
    omega
  · exfalso
    have hy3 : orderOf (⟨y, hyS⟩ : CFSG.PSL2Table.nonsplitTorus ν) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact hof hxy
    have hdvd := orderOf_dvd_natCard (⟨y, hyS⟩ : CFSG.PSL2Table.nonsplitTorus ν)
    rw [hy3] at hdvd
    have hT := CFSG.PSL2Table.card_nonsplitTorus hF hν
    rw [hn] at hT
    obtain ⟨k, hk⟩ := hdvd
    have h3n : 3 ∣ 3 ^ (n : ℕ) := dvd_pow_self 3 (by omega)
    omega

noncomputable def fieldPart (K : Type) [Field K] [Finite K] : MulAut (PSL2 K) →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom

omit [Fintype K] [DecidableEq K] in
theorem mem_range_pglAction_iff [Finite K] (α : MulAut (PSL2 K)) :
    α ∈ (pglAction K).range ↔ fieldPart K α = 1 := by
  constructor
  · rintro ⟨g, rfl⟩
    have h : (semilinearEquivAut K).symm (pglAction K g) = SemidirectProduct.inl g := by
      rw [MulEquiv.symm_apply_eq]
      exact (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl K g).symm
    change SemidirectProduct.rightHom ((semilinearEquivAut K).symm (pglAction K g)) = 1
    rw [h, SemidirectProduct.rightHom_inl]
  · intro h
    exact KFacts.mem_range_pglAction_of_rightHom_eq_one h

omit [Fintype K] [DecidableEq K] in
theorem range_pglAction_eq_ker [Finite K] : (pglAction K).range = (fieldPart K).ker := by
  ext α
  rw [mem_range_pglAction_iff, MonoidHom.mem_ker]

omit [DecidableEq K] in
theorem index_inner_pglAction (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) :
    ((MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.subgroupOf (pglAction K).range).index = 2 := by
  set φ : PGL2 K →* (pglAction K).range := (pglAction K).rangeRestrict with hφ
  have hsurj : Function.Surjective φ := (pglAction K).rangeRestrict_surjective
  have hker : φ.ker ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    intro g hg
    have : pglAction K g = 1 := by
      have := congrArg Subtype.val ((MonoidHom.mem_ker).mp hg)
      exact this
    rw [KFacts.pglAction_injective (this.trans (map_one _).symm)]
    exact Subgroup.one_mem _
  have hmap : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map φ =
      (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range.subgroupOf (pglAction K).range := by
    ext ⟨d, hd⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hx⟩
      refine ⟨x, ?_⟩
      have := congrArg Subtype.val hx
      change pglAction K (Matrix.ProjectiveSpecialLinearGroup.toPGL x) = d at this
      change MulAut.conj x = d
      rw [← this, pglAction_toPGL]
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, Subtype.ext (pglAction_toPGL K x)⟩
  rw [← hmap, Subgroup.index_map_eq _ hsurj hker]
  exact CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K hK

theorem rowS148_psl2_of_char_three (h3 : ringChar K = 3) (hq : 5 ≤ Fintype.card K)
    (hZ : Subgroup.center (PSL2 K) = ⊥) : RowS148 (PSL2 K) := by
  haveI : CharP K 3 := ringChar.of_eq h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have hKcard : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  set D := (pglAction K).range with hD
  set ι : PSL2 K →* MulAut (PSL2 K) := MulAut.conj with hι
  haveI : D.Normal := by rw [hD, range_pglAction_eq_ker]; infer_instance
  haveI : ι.range.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  refine rowS148_of_inndiag hZ D ?_ ?_ ?_ ?_
  ·
    intro σ τ
    rw [hD, mem_range_pglAction_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
      CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K (fieldPart K σ) (fieldPart K τ)]
    group
  ·
    intro E hE hE9
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ((fieldPart K).comp E.subtype) := by
      rw [injective_iff_map_eq_one]
      intro e he
      by_contra hne
      have he1 : (e : MulAut (PSL2 K)) ≠ 1 := fun h => hne (Subtype.ext h)
      obtain ⟨g, hg⟩ := (mem_range_pglAction_iff (e : MulAut (PSL2 K))).mpr he
      have hg3 : g ^ 3 = 1 :=
        KFacts.pglAction_injective (by rw [map_pow, hg, hE.2 e e.2, map_one])
      obtain ⟨x, hx⟩ := KFacts.exists_toPGL_eq_of_pow_odd (by decide : Odd 3) hg3
      exact hcon e e.2 he1 ⟨x, by rw [← pglAction_toPGL, hx, hg]⟩
    haveI : IsCyclic (K ≃+* K) :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hKcard).2
    haveI hcycE : IsCyclic E :=
      isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
        (MonoidHom.ofInjective hinj).symm.surjective
    obtain ⟨g, hg⟩ := hcycE.exists_generator
    have hord : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hE9]
    have hg3 : g ^ 3 = 1 := Subtype.ext (hE.2 _ g.2)
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hord] at this
    norm_num at this
  ·
    intro s hs
    exact pPrimeCoreOf_eq_bot_of_isPGroup (isPGroup_centralizer_psl2 h3 hq hs)
  ·
    intro d hd f _
    have hidx := index_inner_pglAction (K := K) ⟨3, n, Nat.prime_three, by decide, n.2, hKcard⟩
    have hd' : f * d⁻¹ * f⁻¹ ∈ D := (inferInstance : D.Normal).conj_mem _ (D.inv_mem hd) f
    by_cases hdI : d ∈ ι.range
    · have : d * f * d⁻¹ * f⁻¹ = d * (f * d⁻¹ * f⁻¹) := by group
      rw [this]
      exact ι.range.mul_mem hdI ((inferInstance : ι.range.Normal).conj_mem _ (ι.range.inv_mem hdI) f)
    · have hd'I : f * d⁻¹ * f⁻¹ ∉ ι.range := by
        intro h
        apply hdI
        have h2 := (inferInstance : ι.range.Normal).conj_mem _ h f⁻¹
        rw [show f⁻¹ * (f * d⁻¹ * f⁻¹) * f⁻¹⁻¹ = d⁻¹ by group] at h2
        simpa using h2
      have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨d, hd⟩)
        (b := ⟨f * d⁻¹ * f⁻¹, hd'⟩)).mpr (iff_of_false hdI hd'I)
      have : d * f * d⁻¹ * f⁻¹ = d * (f * d⁻¹ * f⁻¹) := by group
      rw [this]
      exact hmem

end L2

theorem rowSOf148_one_three (e : ℕ) (he : 1 ≤ e) : RowSOf148 (projSL 2 (GaloisField 3 e)) := by
  intro S _ _ hs hna ⟨eS⟩
  haveI : Fintype (GaloisField 3 e) := Fintype.ofFinite _
  classical
  have hchar : ringChar (GaloisField 3 e) = 3 := ringChar.eq (GaloisField 3 e) 3
  have hcard : Fintype.card (GaloisField 3 e) = 3 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 3 e (by omega)
  have φ : S ≃* PSL2 (GaloisField 3 e) := eS.trans (projSLEquivPSL _)
  by_cases he2 : 2 ≤ e
  · have hq : 5 ≤ Fintype.card (GaloisField 3 e) := by
      rw [hcard]
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    have hZ : Subgroup.center (PSL2 (GaloisField 3 e)) = ⊥ :=
      RonanK429.center_eq_bot_of_mulEquiv φ.symm (RonanK429.center_eq_bot_of_isSimpleGroup hs hna)
    exact (rowS148_psl2_of_char_three hchar hq hZ).of_mulEquiv φ
  · exfalso
    have he1 : e = 1 := by omega
    subst he1
    have hc := RonanK432.card_psl2_mul_gcd (GaloisField 3 1)
    rw [Nat.card_eq_fintype_card (α := GaloisField 3 1), hcard] at hc
    norm_num at hc
    haveI : Fintype S := Fintype.ofFinite S
    have h12' : Fintype.card (PSL2 (GaloisField 3 1)) = 12 := by omega
    have h12 : Nat.card (PSL2 (GaloisField 3 1)) = 12 := Nat.card_eq_fintype_card.trans h12'
    have hS : Fintype.card S = 2 ^ 2 * 3 ^ 1 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr φ.toEquiv, h12]
      norm_num
    have hsol := CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) hS
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b)

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
