module

public import CFSG.Sporadic.Co2Schreier.SylowLemmas
public import CFSG.Sporadic.Schreier.RuSylowB
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co2Schreier.SylowCheck
public import CFSG.Sporadic.Co2Schreier.CoresBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier

structure FratFacts : Prop where
  chain : rawChainOK 2300 fratOrig fratStrong fratBase fratWords 4 = true
  orbits : rawOrbitSizes 2300 fratStrong fratBase = [128, 64]
  invOrig : allInv fratOrig = true
  invStrong : allInv fratStrong = true
  sizeOrig : fratOrig.size = 12
  sizeY : yBasisArrs.size = 5
  conj : ∀ j < 15, ∀ k < 12, siftA 2300 fratLevels fratBase 0
    (compA 2300 (compA 2300 sArrs[j]! fratOrig[k]!) (invCand 2300 sArrs[j]!)) = true
  comm : ∀ i < 15, ∀ j < 15, siftA 2300 fratLevels fratBase 0
    (compA 2300 (compA 2300 (compA 2300 sArrs[i]! sArrs[j]!) (invCand 2300 sArrs[i]!))
      (invCand 2300 sArrs[j]!)) = true
  sq : ∀ j < 15, siftA 2300 fratLevels fratBase 0 (sqArr sArrs[j]!) = true
  invY : ∀ u < 32, isInvA 2300 (yArr u) (invCand 2300 (yArr u)) = true
  sep : ∀ u < 32, ∀ v < 32, (!(decide (u < v)) ||
    !siftA 2300 fratLevels fratBase 0 (compA 2300 (invCand 2300 (yArr u)) (yArr v))) = true
  commZ : ∀ j < 15, commA zArr sArrs[j]! = true

theorem fratFacts : FratFacts := by
  have h := frat_check
  simp only [fratCheck, Bool.and_eq_true, beq_iff_eq, allLt_iff, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem fratStrong_size : fratStrong.size = 16 := by
  rw [fratStrong, extendArrs_size, fratFacts.sizeOrig]
  rfl

theorem fratOrig_le : fratOrig.size ≤ fratStrong.size := by
  rw [fratFacts.sizeOrig, fratStrong_size]
  norm_num

theorem fratBase_lt : ∀ i < fratBase.size, fratBase[i]! < 2300 := by
  rw [fratBase]
  decide

theorem fratBase_nodup : fratBase.toList.Nodup := by
  rw [fratBase]
  decide

@[expose] def fratChain : RawSchreierDatum 2300 :=
  rawOfArrays 2300 fratOrig fratStrong fratBase fratWords (by norm_num) fratOrig_le fratBase_lt
    fratBase_nodup

theorem fratChain_arrays :
    ChainArrays fratChain fratOrig fratStrong fratBase fratWords :=
  chainArrays_rawOfArrays (fun _ hk => allInv_spec fratFacts.invOrig hk)
    (fun _ hj => allInv_spec fratFacts.invStrong hj)

@[expose] def fratTuple : List (Equiv.Perm (Fin 2300)) :=
  fratSpecs.map fun l => prodList sTuple l ^ 2

@[expose] def locF : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ fratTuple}

theorem fratSpecs_lt :
    ∀ l ∈ fratSpecs, ∀ i ∈ l, i < sTuple.length := by
  rw [sTuple_length]
  decide

theorem repTuple_frat :
    RepTuple 2300 fratOrig fratTuple := by
  refine ⟨by rw [fratFacts.sizeOrig]; rfl, fun h hh => ?_⟩
  have hh' : h < fratSpecs.length := by simpa [fratTuple] using hh
  have e1 : fratOrig[h]! = sqArr (prodArr sArrs fratSpecs[h]) := by
    rw [fratOrig, getElem!_pos _ h (by simpa using hh')]
    simp
  have e2 : fratTuple.getD h 1 = prodList sTuple fratSpecs[h] ^ 2 := by
    rw [List.getD_eq_getElem?_getD]
    simp [fratTuple, hh']
  rw [e1, e2, pow_two]
  have hr := rep_prodArr repTuple_s (fratSpecs_lt _ (List.getElem_mem hh'))
  exact rep_compA hr hr

theorem fratChain_original :
    fratChain.originalSubgroup = locF := by
  rw [locF]
  exact originalSubgroup_rawOfArrays_of_eqA repTuple_frat (repTuple_frat.1)
    (fun k hk => (rep_permOfArr (allInv_spec fratFacts.invOrig hk)).1)
    (fun k hk => (eqA_iff (repTuple_frat.rep (repTuple_frat.1 ▸ hk))
      (repTuple_frat.rep (repTuple_frat.1 ▸ hk))).2 rfl)

theorem card_locF :
    Nat.card locF = 8192 := by
  rw [← fratChain_original, card_originalSubgroup_of_chainOK fratChain_arrays (by norm_num)
    fratFacts.chain, fratFacts.orbits]
  rfl

theorem mem_locF_iff
    {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (hg : Rep 2300 t g) :
    siftA 2300 fratLevels fratBase 0 t = true ↔ g ∈ locF := by
  rw [← fratChain_original]
  exact siftA_iff_mem_originalSubgroup fratChain_arrays (by norm_num) fratFacts.chain hg

theorem sTuple_mem_S : ∀ g ∈ sTuple, g ∈ locS := fun _ hg => Subgroup.subset_closure hg

theorem fratTuple_mem_S : ∀ g ∈ fratTuple, g ∈ locS := by
  intro g hg
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
  exact locS.pow_mem (prodList_mem sTuple_mem_S l) 2

theorem locF_le_S : locF ≤ locS := by
  rw [locF, Subgroup.closure_le]
  exact fratTuple_mem_S

theorem sTuple_getD
    {j : ℕ} (hj : j < 15) : Rep 2300 sArrs[j]! (sTuple.getD j 1) :=
  repTuple_s.rep (by rw [sTuple_length]; exact hj)

theorem rep_sInv
    {j : ℕ} (hj : j < 15) : Rep 2300 (invCand 2300 sArrs[j]!) (sTuple.getD j 1)⁻¹ :=
  rep_inv_of_isInvA (sTuple_getD hj) (allInv_spec wordFacts.invS (wordFacts.sizeS ▸ hj))

theorem conj_frat_mem
    {j : ℕ} (hj : j < 15) {k : ℕ} (hk : k < 12) :
    sTuple.getD j 1 * fratTuple.getD k 1 * (sTuple.getD j 1)⁻¹ ∈ locF :=
  (mem_locF_iff (rep_compA (rep_compA (sTuple_getD hj)
    (repTuple_frat.rep (by rw [← repTuple_frat.1, fratFacts.sizeOrig]; exact hk)))
    (rep_sInv hj))).1 (fratFacts.conj j hj k hk)

theorem locS_le_normalizer_F :
    locS ≤ Subgroup.normalizer (locF : Set (Equiv.Perm (Fin 2300))) :=
  le_normalizer_of_gens (Y := {g | g ∈ fratTuple}) (X := {g | g ∈ sTuple}) rfl rfl
    fun x hx y hy => by
      obtain ⟨j, hj, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hx
      obtain ⟨k, hk, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hy
      rw [sTuple_length] at hj
      have hk' : k < 12 := by rw [← fratFacts.sizeOrig, repTuple_frat.1]; exact hk
      exact conj_frat_mem hj hk'

instance locF_normal :
    (locF.subgroupOf locS).Normal :=
  normal_of_conj_mem fun _ hc x hx =>
    (Subgroup.mem_normalizer_iff.1 (locS_le_normalizer_F hc) x).1 hx

@[expose] def sGenSet : Set locS := Subtype.val ⁻¹' {g | g ∈ sTuple}

theorem sGenSet_closure : Subgroup.closure sGenSet = ⊤ := Subgroup.closure_closure_coe_preimage

theorem mem_sGenSet
    {x : locS} (hx : x ∈ sGenSet) : ∃ j < 15, (x : Equiv.Perm (Fin 2300)) =
    sTuple.getD j 1 := by
  obtain ⟨j, hj, h⟩ := (mem_iff_exists_getD (d := 1)).1 (show (x : Equiv.Perm (Fin 2300)) ∈
    sTuple from hx)
  rw [sTuple_length] at hj
  exact ⟨j, hj, h.symm⟩

theorem quotF_comm :
    ∀ a b : locS ⧸ locF.subgroupOf locS, a * b = b * a := by
  refine quotient_comm_of_gens _ sGenSet_closure fun x hx y hy => ?_
  obtain ⟨i, hi, hxi⟩ := mem_sGenSet hx
  obtain ⟨j, hj, hyj⟩ := mem_sGenSet hy
  rw [Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxi, hyj]
  exact (mem_locF_iff (rep_compA (rep_compA (rep_compA (sTuple_getD hi) (sTuple_getD hj))
    (rep_sInv hi)) (rep_sInv hj))).1 (fratFacts.comm i hi j hj)

theorem quotF_sq :
    ∀ a : locS ⧸ locF.subgroupOf locS, a ^ 2 = 1 := by
  refine sq_eq_one_of_gens quotF_comm (X := QuotientGroup.mk '' sGenSet) ?_ ?_
  · rw [← QuotientGroup.coe_mk', ← MonoidHom.map_closure, sGenSet_closure,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hxj⟩ := mem_sGenSet hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, hxj, pow_two]
    exact (mem_locF_iff (rep_compA (sTuple_getD hj) (sTuple_getD hj))).1 (fratFacts.sq j hj)

theorem isPGroup_locS :
    IsPGroup 2 locS :=
  IsPGroup.of_card (n := 18) (by rw [card_locS]; norm_num)

theorem sq_mem_frattini
    (x : locS) : x ^ 2 ∈ frattini locS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 locS) := ⟨isPGroup_locS⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
  exact Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)

theorem frattini_locS :
    frattini locS = locF.subgroupOf locS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary (p := 2) _
    quotF_comm quotF_sq) ?_
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  have hle : locF ≤ (frattini locS).map locS.subtype := by
    rw [locF, Subgroup.closure_le]
    intro g hg
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
    exact ⟨⟨prodList sTuple l, prodList_mem sTuple_mem_S l⟩ ^ 2,
      sq_mem_frattini _, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  rwa [Subtype.ext hyx] at hy

theorem card_frattini_locS :
    Nat.card (frattini locS) = 8192 := by
  rw [frattini_locS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe locF_le_S).toEquiv, card_locF]

theorem card_quot_frattini :
    Nat.card (locS ⧸ frattini locS) = 32 := by
  have h := (frattini locS).card_eq_card_quotient_mul_card_subgroup
  rw [card_locS, card_frattini_locS] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8192) (by rw [← h])

@[expose] def yBasisTuple : List (Equiv.Perm (Fin 2300)) := yBasisSpecs.map (prodList sTuple)

theorem yBasisSpecs_lt :
    ∀ l ∈ yBasisSpecs, ∀ i ∈ l, i < sTuple.length := by
  rw [sTuple_length]
  decide

theorem repTuple_yBasis :
    RepTuple 2300 yBasisArrs yBasisTuple := by
  refine ⟨by rw [fratFacts.sizeY]; rfl, fun h hh => ?_⟩
  have hh' : h < yBasisSpecs.length := by simpa [yBasisTuple] using hh
  have e1 : yBasisArrs[h]! = prodArr sArrs yBasisSpecs[h] := by
    rw [yBasisArrs, getElem!_pos _ h (by simpa using hh')]
    simp
  have e2 : yBasisTuple.getD h 1 = prodList sTuple yBasisSpecs[h] := by
    rw [List.getD_eq_getElem?_getD]
    simp [yBasisTuple, hh']
  rw [e1, e2]
  exact rep_prodArr repTuple_s (yBasisSpecs_lt _ (List.getElem_mem hh'))

theorem yBasisTuple_length : yBasisTuple.length = 5 := rfl

@[expose] def yPerm (w : ℕ) : Equiv.Perm (Fin 2300) := prodList yBasisTuple (bits5 w)

theorem bits5_lt (w : ℕ) : ∀ k ∈ bits5 w, k < yBasisTuple.length := by
  intro k hk
  rw [yBasisTuple_length]
  exact List.mem_range.1 (List.mem_filter.1 hk).1

theorem rep_yArr
    (w : ℕ) : Rep 2300 (yArr w) (yPerm w) :=
  rep_prodArr repTuple_yBasis (bits5_lt w)

theorem yBasisTuple_mem_S : ∀ g ∈ yBasisTuple, g ∈ locS := by
  intro g hg
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hg
  exact prodList_mem sTuple_mem_S l

theorem yPerm_mem (w : ℕ) : yPerm w ∈ locS := prodList_mem yBasisTuple_mem_S _

@[expose] def ySub (w : ℕ) : locS := ⟨yPerm w, yPerm_mem w⟩

@[expose] def cosetY
    (w : ℕ) : locS ⧸ frattini locS := QuotientGroup.mk (ySub w)

theorem cosetY_eq_iff
    (u v : ℕ) : cosetY u = cosetY v ↔ (yPerm u)⁻¹ * yPerm v ∈ locF := by
  rw [cosetY, cosetY, QuotientGroup.eq, frattini_locS, Subgroup.mem_subgroupOf]
  rfl

theorem cosetY_injective
    {u v : ℕ} (hu : u < 32) (hv : v < 32) (h : cosetY u = cosetY v) :
    u = v := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with huv | huv
  · have hs := fratFacts.sep u hu v hv
    rw [decide_eq_true huv, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hs
    have hm := (cosetY_eq_iff u v).1 h
    rw [← mem_locF_iff (rep_compA (rep_inv_of_isInvA (rep_yArr u) (fratFacts.invY u hu))
      (rep_yArr v))] at hm
    rw [hm] at hs
    exact Bool.noConfusion hs
  · have hs := fratFacts.sep v hv u hu
    rw [decide_eq_true huv, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hs
    have hm := (cosetY_eq_iff v u).1 h.symm
    rw [← mem_locF_iff (rep_compA (rep_inv_of_isInvA (rep_yArr v) (fratFacts.invY v hv))
      (rep_yArr u))] at hm
    rw [hm] at hs
    exact Bool.noConfusion hs

theorem exists_cosetY
    (q : locS ⧸ frattini locS) : ∃ w < 32, cosetY w = q := by
  have hbij : Function.Bijective fun w : Fin 32 => cosetY w :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨fun a b h => Fin.ext (cosetY_injective a.2 b.2 h),
      by rw [card_quot_frattini, Nat.card_eq_fintype_card, Fintype.card_fin]⟩
  obtain ⟨w, hw⟩ := hbij.2 q
  exact ⟨w, w.2, hw⟩

end CFSG.Sporadic.Co2Schreier
