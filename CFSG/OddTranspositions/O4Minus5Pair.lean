module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.OddTranspositions.MinimalNormalTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

noncomputable section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter
open CFSG.Timmesfeld.Bridge.Asc72
open Matrix
open Polynomial

local instance instFactPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev K25 : Type := GaloisField 5 2

abbrev PSL225 : Type := ProjectiveSpecialLinearGroup (Fin 2) K25

abbrev PSigmaL225 : Type := PSL225 ⋊[psl2FieldAut K25] (K25 ≃+* K25)

@[expose] def frob25 : K25 ≃+* K25 := frobeniusEquiv K25 5

theorem card_K25 : Nat.card K25 = 25 := by
  simpa using GaloisField.card 5 2 (by norm_num)

theorem frob25_mul_self : frob25 * frob25 = 1 := by
  haveI : Fintype K25 := Fintype.ofFinite K25
  ext x
  show frob25 (frob25 x) = x
  change (x ^ 5) ^ 5 = x
  rw [← pow_mul]
  have hc : Fintype.card K25 = 25 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_K25
  have h : x ^ 25 = x := by
    have := FiniteField.pow_card x
    rwa [hc] at this
  norm_num
  exact h

theorem frob25_ne_one : frob25 ≠ 1 := by
  intro h
  classical
  haveI : Fintype K25 := Fintype.ofFinite K25
  haveI : DecidableEq K25 := Classical.decEq K25
  have hroot : ∀ x : K25, (X ^ 5 - X : K25[X]).IsRoot x := by
    intro x
    rw [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
    have hx : frob25 x = x := by rw [h]; rfl
    have hx5 : x ^ 5 = x := by
      simpa [frob25, frobenius_def] using hx
    exact hx5
  have hdeg : (X ^ 5 - X : K25[X]).natDegree = 5 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 5
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      norm_num
  have hp0 : (X ^ 5 - X : K25[X]) ≠ 0 := by
    intro hp
    have := hdeg
    rw [hp, Polynomial.natDegree_zero] at this
    omega
  have hle : (X ^ 5 - X : K25[X]).roots.toFinset.card ≤ 5 := by
    calc (X ^ 5 - X : K25[X]).roots.toFinset.card ≤ (X ^ 5 - X : K25[X]).roots.card :=
          Multiset.toFinset_card_le _
      _ ≤ (X ^ 5 - X : K25[X]).natDegree := Polynomial.card_roots' _
      _ = 5 := hdeg
  have huniv : (Finset.univ : Finset K25) ⊆ (X ^ 5 - X : K25[X]).roots.toFinset := by
    intro x _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hroot x
  have h25 : 25 ≤ 5 := by
    have hc := Finset.card_le_card huniv
    have hcard : Fintype.card K25 = 25 := by
      rw [← Nat.card_eq_fintype_card]
      exact card_K25
    simpa [Finset.card_univ, hcard] using hc.trans hle
  omega

theorem orderOf_frob25 : orderOf frob25 = 2 := by
  refine orderOf_eq_prime ?_ frob25_ne_one
  rw [pow_two]
  exact frob25_mul_self

@[expose] def class65 : Set PSigmaL225 :=
  {x | IsConj (SemidirectProduct.inr frob25) x}

@[expose] def L225Subgroup : Subgroup PSigmaL225 :=
  (SemidirectProduct.inl : PSL225 →* PSigmaL225).range

instance L225Subgroup_normal : L225Subgroup.Normal := by
  rw [L225Subgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

@[expose] noncomputable def L225SubgroupEquiv : PSL225 ≃* L225Subgroup :=
  MonoidHom.ofInjective
    (f := (SemidirectProduct.inl : PSL225 →* PSigmaL225))
    SemidirectProduct.inl_injective

theorem PSL225_isSimple : IsSimpleGroup PSL225 := by
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [show Nat.card K25 = 5 ^ 2 from GaloisField.card 5 2 (by norm_num)]
  norm_num

theorem L225Subgroup_isSimple : IsSimpleGroup L225Subgroup := by
  haveI : IsSimpleGroup PSL225 := PSL225_isSimple
  exact L225SubgroupEquiv.symm.isSimpleGroup

theorem L225Subgroup_isMinimalNormal : IsMinimalNormal L225Subgroup := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro hbot
    haveI : Nontrivial L225Subgroup := L225SubgroupEquiv.symm.toEquiv.nontrivial
    rw [hbot] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  · intro N hNnorm hNle
    exact (Subgroup.isSimpleGroup_iff.mp L225Subgroup_isSimple).2 N hNle
      (hNnorm.subgroupOf L225Subgroup)

theorem L225Subgroup_lieModel : CFSG.Blueprint.LieModel L225Subgroup .PSL 2 5 2 := by
  refine Or.inl ⟨by decide, ?_⟩
  exact CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv L225Subgroup 5 2
    (by norm_num) L225SubgroupEquiv.symm

@[expose] def IsO4Minus5Pair (Y : Type) [Group Y] (Θ : Set Y) : Prop :=
  ∃ e : Y ≃* PSigmaL225, e '' Θ = class65

theorem IsO4Minus5Pair.exists_L225 {Y : Type} [Group Y] {Θ : Set Y}
    (h : IsO4Minus5Pair Y Θ) :
    ∃ (M : Subgroup Y) (_ : M.Normal), IsMinimalNormal M ∧
      CFSG.Blueprint.LieModel M .PSL 2 5 2 := by
  obtain ⟨e, _⟩ := h
  let M : Subgroup Y := L225Subgroup.comap (e : Y →* PSigmaL225)
  have hMnormal : M.Normal :=
    (inferInstance : L225Subgroup.Normal).comap (e : Y →* PSigmaL225)
  have hMminimal : IsMinimalNormal M :=
    CFSG.OddTranspositions.IsMinimalNormal.comap_mulEquiv e L225Subgroup_isMinimalNormal
  have hMlie : CFSG.Blueprint.LieModel M .PSL 2 5 2 := by
    have hmap : M.map (e : Y →* PSigmaL225) = L225Subgroup :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective L225Subgroup
    let eM : M ≃* L225Subgroup :=
      (Subgroup.equivMapOfInjective M (e : Y →* PSigmaL225) e.injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact CFSG.Blueprint.LieModel.of_mulEquiv eM.symm L225Subgroup_lieModel
  exact ⟨M, hMnormal, hMminimal, hMlie⟩

theorem isOddPrimePower_25 : CFSG.GorensteinWalter.IsOddPrimePower 25 :=
  ⟨5, 2, Nat.prime_five, by norm_num, by norm_num, by norm_num⟩

theorem card_PSL225 : Nat.card PSL225 = 7800 := by
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K25) := by
    rw [card_K25]
    exact isOddPrimePower_25
  rw [PSL225, CFSG.GorensteinWalter.psl2_card_formula K25 hodd, card_K25]
  norm_num

theorem card_PSigmaL225_mul :
    Nat.card PSigmaL225 = Nat.card PSL225 * Nat.card (K25 ≃+* K25) := by
  rw [PSigmaL225]
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]

theorem rightHom_mem_class65 {x : PSigmaL225} (hx : x ∈ class65) :
    SemidirectProduct.rightHom x = frob25 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hx
  rw [map_mul, map_mul, map_inv, SemidirectProduct.rightHom_inr]
  set σ := SemidirectProduct.rightHom g
  have hcomm : σ * frob25 = frob25 * σ := by
    ext x
    change σ (x ^ 5) = (σ x) ^ 5
    rw [map_pow]
  calc σ * frob25 * σ⁻¹ = frob25 * σ * σ⁻¹ := by rw [hcomm]
    _ = frob25 * (σ * σ⁻¹) := by rw [mul_assoc]
    _ = frob25 := by rw [mul_inv_cancel, mul_one]

theorem class65_no_sq {d e : PSigmaL225} (hd : d ∈ class65) (he : e ∈ class65) :
    d * e ∉ class65 := by
  intro hde
  have h1 := rightHom_mem_class65 hd
  have h2 := rightHom_mem_class65 he
  have h3 := rightHom_mem_class65 hde
  rw [map_mul, h1, h2, frob25_mul_self] at h3
  exact frob25_ne_one h3.symm

noncomputable def ringAutEquivAlgAut :
    (K25 ≃+* K25) ≃ (K25 ≃ₐ[ZMod 5] K25) where
  toFun f := AlgEquiv.ofRingEquiv (f := f) (by
    intro r
    rw [← ZMod.natCast_zmod_val r]
    simp only [map_natCast])
  invFun e := e.toRingEquiv
  left_inv f := by ext x; rfl
  right_inv e := by ext x; rfl

theorem card_ringAut : Nat.card (K25 ≃+* K25) = 2 := by
  rw [Nat.card_congr ringAutEquivAlgAut]
  rw [IsGalois.card_aut_eq_finrank]
  rw [GaloisField.finrank (p := 5) (n := 2) (by norm_num)]

theorem card_PSigmaL225 : Nat.card PSigmaL225 = 15600 := by
  rw [card_PSigmaL225_mul, card_PSL225, card_ringAut]

theorem inr_frob25_mem_class65 : (SemidirectProduct.inr frob25 : PSigmaL225) ∈ class65 :=
  ⟨1, by simp⟩

theorem inr_frob25_not_mem_psl : (SemidirectProduct.inr frob25 : PSigmaL225) ∉ L225Subgroup := by
  rw [L225Subgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
  intro h
  have h1 : SemidirectProduct.rightHom (SemidirectProduct.inr frob25) = 1 := h
  rw [SemidirectProduct.rightHom_inr] at h1
  exact frob25_ne_one h1

theorem exists_distinct_class65 : ∃ d ∈ class65, ∃ e ∈ class65, d ≠ e := by
  have hinj := CFSG.GorensteinWalter.psl2FieldAut_injective K25
  have hfne : CFSG.GorensteinWalter.psl2FieldAut K25 frob25 ≠ 1 := by
    intro h
    apply frob25_ne_one
    apply hinj
    simpa using h
  have hex : ∃ p, CFSG.GorensteinWalter.psl2FieldAut K25 frob25 p ≠ p := by
    by_contra h
    push Not at h
    exact hfne (MulEquiv.ext (fun p => by simpa using h p))
  obtain ⟨p, hp⟩ := hex
  refine ⟨SemidirectProduct.inr frob25, inr_frob25_mem_class65,
    SemidirectProduct.inl p * SemidirectProduct.inr frob25 * (SemidirectProduct.inl p)⁻¹,
    ?_, ?_⟩
  · exact isConj_iff.mpr ⟨SemidirectProduct.inl p, rfl⟩
  · intro heq
    have hleft := congrArg SemidirectProduct.left heq
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, SemidirectProduct.inv_right, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, SemidirectProduct.left_inr, SemidirectProduct.right_inr,
      map_one, MulAut.one_apply, inv_one, map_inv, SemidirectProduct.one_left] at hleft
    have h2 : p * ((CFSG.GorensteinWalter.psl2FieldAut K25 frob25) p)⁻¹ = 1 := by
      simpa [one_mul, mul_one] using hleft.symm
    exact hp (mul_inv_eq_one.mp h2).symm

theorem closure_class65_eq_top : Subgroup.closure class65 = ⊤ := by
  let H : Subgroup PSigmaL225 := Subgroup.closure class65
  have hHnorm : H.Normal := by
    refine Subgroup.Normal.mk ?_
    intro x hx g
    have hx' : x ∈ H := hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ H) ?base ?one ?mul ?inv hx'
    · intro x hx
      have hxconj : IsConj (SemidirectProduct.inr frob25) x := hx
      exact Subgroup.subset_closure (hxconj.trans (isConj_iff.mpr ⟨g, rfl⟩))
    · simpa using H.one_mem
    · intro x y hx hy hx' hy'
      have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [heq]
      exact H.mul_mem hx' hy'
    · intro x hx hx'
      have heq : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [heq]
      exact H.inv_mem hx'
  have hHnotle : ¬ H ≤ L225Subgroup := by
    intro hle
    exact inr_frob25_not_mem_psl (hle (Subgroup.subset_closure inr_frob25_mem_class65))
  haveI : (H.subgroupOf L225Subgroup).Normal := hHnorm.subgroupOf L225Subgroup
  have hcapne : H.subgroupOf L225Subgroup ≠ ⊥ := by
    intro hbot
    obtain ⟨d, hd, e, he, hde⟩ := exists_distinct_class65
    have hdH : d ∈ H := Subgroup.subset_closure hd
    have heH : e ∈ H := Subgroup.subset_closure he
    have hmemH : d * e⁻¹ ∈ H := H.mul_mem hdH (H.inv_mem heH)
    have hmemPSL : d * e⁻¹ ∈ L225Subgroup := by
      rw [L225Subgroup, SemidirectProduct.range_inl_eq_ker_rightHom]
      show SemidirectProduct.rightHom (d * e⁻¹) = 1
      rw [map_mul, map_inv, rightHom_mem_class65 hd, rightHom_mem_class65 he]
      simp [frob25_mul_self]
    have hsub : (⟨d * e⁻¹, hmemPSL⟩ : L225Subgroup) ∈ H.subgroupOf L225Subgroup := hmemH
    rw [hbot] at hsub
    have hone : d * e⁻¹ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hsub)
    exact hde (mul_inv_eq_one.mp hone)
  haveI : IsSimpleGroup L225Subgroup := L225Subgroup_isSimple
  have hcap : H.subgroupOf L225Subgroup = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf L225Subgroup) with h | h
    · exact absurd h hcapne
    · exact h
  have hPSLle : L225Subgroup ≤ H := by
    intro p hp
    have hsub : (⟨p, hp⟩ : L225Subgroup) ∈ H.subgroupOf L225Subgroup := by
      rw [hcap]
      exact Subgroup.mem_top _
    exact hsub
  have hAutTop : Subgroup.zpowers frob25 = ⊤ := by
    haveI : Finite (K25 ≃+* K25) :=
      Finite.of_injective (fun f : K25 ≃+* K25 => (f : K25 → K25))
        (fun f g h => RingEquiv.ext (congrFun h))
    haveI : Finite (Subgroup.zpowers frob25) :=
      Finite.of_injective (fun x : Subgroup.zpowers frob25 => (x : K25 ≃+* K25))
        Subtype.coe_injective
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, orderOf_frob25, card_ringAut]
  rw [eq_top_iff]
  intro g _
  have hg : g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right := by
    rw [← SemidirectProduct.mk_eq_inl_mul_inr]
  rw [hg]
  apply H.mul_mem
  · exact hPSLle (by rw [L225Subgroup]; exact ⟨g.left, rfl⟩)
  · have hright : g.right ∈ Subgroup.zpowers frob25 := by
      rw [hAutTop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hright
    have hpow : SemidirectProduct.inr g.right = (SemidirectProduct.inr frob25 : PSigmaL225) ^ k := by
      rw [← hk, map_zpow]
    rw [hpow]
    exact H.zpow_mem (Subgroup.subset_closure inr_frob25_mem_class65) k

end CFSG.OddTranspositions.QZ

