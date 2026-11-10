module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG

namespace FiveTransitive.Research.OddFourStabilizerLifts

open scoped Pointwise

@[expose] def baseLeftSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

@[expose] def baseRightSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 2 3

@[expose] def baseDisjointSwapHom :
    Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2) →*
      Equiv.Perm (Fin 4) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin 2) (Fin 2))

private theorem baseDisjointSwapHom_injective :
    Function.Injective baseDisjointSwapHom :=
  finSumFinEquiv.permCongrHom.injective.comp
    Equiv.Perm.sumCongrHom_injective

@[expose] def baseDisjointSwapFour : Subgroup (Equiv.Perm (Fin 4)) :=
  baseDisjointSwapHom.range

@[simp] theorem natCard_baseDisjointSwapFour :
    Nat.card baseDisjointSwapFour = 4 := by
  calc
    Nat.card baseDisjointSwapFour =
        Nat.card (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 2)) :=
      Nat.card_congr
        (MonoidHom.ofInjective baseDisjointSwapHom_injective).toEquiv.symm
    _ = 4 := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]
      norm_num [Nat.factorial]

theorem baseLeftSwap_mem : baseLeftSwap ∈ baseDisjointSwapFour := by
  refine ⟨(Equiv.swap 0 1, 1), ?_⟩
  decide

theorem baseRightSwap_mem : baseRightSwap ∈ baseDisjointSwapFour := by
  refine ⟨(1, Equiv.swap 0 1), ?_⟩
  decide

private theorem exists_monoidHom_section_of_odd_ker_card_four
    {L Q : Type*} [Group L] [Group Q]
    (f : L →* Q) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hQ : Nat.card Q = 4) :
    ∃ s : Q →* L, f.comp s = MonoidHom.id Q := by
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hindex : f.ker.index = 4 := by
    rw [Subgroup.index_ker, hrange]
    simpa using hQ
  have hcoprime : (Nat.card f.ker).Coprime f.ker.index := by
    rw [hindex, show 4 = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_right.mpr hodd).pow_right 2
  obtain ⟨C, hC⟩ :=
    Subgroup.exists_right_complement'_of_coprime hcoprime
  let fC : C →* Q := f.comp C.subtype
  have hfC_injective : Function.Injective fC := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro c hc
      have hcKer : (c : L) ∈ f.ker := by
        exact MonoidHom.mem_ker.mpr hc
      have hcBot : (c : L) ∈ (⊥ : Subgroup L) :=
        hC.disjoint.le_bot ⟨hcKer, c.prop⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hcBot))
    · exact bot_le
  have hfC_surjective : Function.Surjective fC := by
    intro q
    obtain ⟨l, rfl⟩ := hf q
    obtain ⟨⟨n, c⟩, hnc⟩ := hC.2 l
    refine ⟨c, ?_⟩
    change f (c : L) = f l
    have hn : f (n : L) = 1 := MonoidHom.mem_ker.mp n.prop
    calc
      f (c : L) = f (n : L) * f (c : L) := by rw [hn, one_mul]
      _ = f ((n : L) * (c : L)) := (map_mul f _ _).symm
      _ = f l := congrArg f hnc
  let e : C ≃* Q :=
    MulEquiv.ofBijective fC ⟨hfC_injective, hfC_surjective⟩
  let s : Q →* L := C.subtype.comp e.symm.toMonoidHom
  refine ⟨s, ?_⟩
  ext q
  exact e.apply_symm_apply q

section SetwiseAction

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] noncomputable def baseRangeEquiv (e : Fin 4 ↪ X) :
    Fin 4 ≃ (Set.range e : Set X) :=
  Equiv.ofInjective e e.injective

abbrev baseSetwiseStabilizer (e : Fin 4 ↪ X) : Subgroup G :=
  MulAction.stabilizer G (Set.range e)

@[expose] noncomputable def baseSetwisePermHom (e : Fin 4 ↪ X) :
    baseSetwiseStabilizer (G := G) e →*
      Equiv.Perm (Set.range e : Set X) :=
  MulAction.toPermHom _ _

@[expose] noncomputable def baseSubgroupPreimage (e : Fin 4 ↪ X)
    (Q : Subgroup (Equiv.Perm (Set.range e : Set X))) :
    Subgroup (baseSetwiseStabilizer (G := G) e) :=
  Subgroup.comap (baseSetwisePermHom (G := G) e) Q

@[expose] noncomputable def baseSubgroupQuotientHom (e : Fin 4 ↪ X)
    (Q : Subgroup (Equiv.Perm (Set.range e : Set X))) :
    baseSubgroupPreimage (G := G) e Q →* Q :=
  ((baseSetwisePermHom (G := G) e).domRestrict
      (baseSubgroupPreimage (G := G) e Q)).codRestrict Q
    (fun k ↦ k.prop)

@[expose] noncomputable def rangeDisjointSwapFour (e : Fin 4 ↪ X) :
    Subgroup (Equiv.Perm (Set.range e : Set X)) :=
  Subgroup.map (baseRangeEquiv e).permCongrHom.toMonoidHom
    baseDisjointSwapFour

@[simp] theorem natCard_rangeDisjointSwapFour (e : Fin 4 ↪ X) :
    Nat.card (rangeDisjointSwapFour e) = 4 := by
  rw [rangeDisjointSwapFour,
    Subgroup.card_map_of_injective
      (baseRangeEquiv e).permCongrHom.injective]
  exact natCard_baseDisjointSwapFour

@[expose] noncomputable def rangeLeftSwap (e : Fin 4 ↪ X) :
    rangeDisjointSwapFour e :=
  ⟨(baseRangeEquiv e).permCongrHom baseLeftSwap,
    ⟨baseLeftSwap, baseLeftSwap_mem, rfl⟩⟩

@[expose] noncomputable def rangeRightSwap (e : Fin 4 ↪ X) :
    rangeDisjointSwapFour e :=
  ⟨(baseRangeEquiv e).permCongrHom baseRightSwap,
    ⟨baseRightSwap, baseRightSwap_mem, rfl⟩⟩

private noncomputable def disjointSwapPreimage (e : Fin 4 ↪ X) :
    Subgroup (baseSetwiseStabilizer (G := G) e) :=
  Subgroup.comap (baseSetwisePermHom (G := G) e)
    (rangeDisjointSwapFour e)

private noncomputable def disjointSwapQuotientHom (e : Fin 4 ↪ X) :
    disjointSwapPreimage (G := G) e →* rangeDisjointSwapFour e :=
  ((baseSetwisePermHom (G := G) e).domRestrict
      (disjointSwapPreimage (G := G) e)).codRestrict
    (rangeDisjointSwapFour e) (fun k ↦ k.prop)

private theorem baseSetwisePermHom_surjective
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) :
    Function.Surjective (baseSetwisePermHom (G := G) e) := by
  classical
  let _ : MulAction.IsMultiplyPretransitive G X 4 := h4
  intro σ
  let τ : Equiv.Perm (Fin 4) :=
    (baseRangeEquiv e).symm.permCongr σ
  let b : Fin 4 ↪ X :=
    ⟨fun i ↦ e (τ i), e.injective.comp τ.injective⟩
  obtain ⟨g, hg⟩ := h4.exists_smul_eq e b
  have hg_apply : ∀ i, g • e i = b i := by
    intro i
    have hi := congrArg (fun a : Fin 4 ↪ X ↦ a i) hg
    simpa [Function.Embedding.smul_apply] using hi
  have hgset : g ∈ baseSetwiseStabilizer (G := G) e := by
    rw [baseSetwiseStabilizer, MulAction.mem_stabilizer_iff]
    apply Set.Subset.antisymm
    · rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      change g • e i ∈ Set.range e
      rw [hg_apply]
      exact ⟨τ i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := τ.surjective i
      refine ⟨e j, ⟨j, rfl⟩, ?_⟩
      change g • e j = e i
      rw [hg_apply]
      exact congrArg e hj
  let k : baseSetwiseStabilizer (G := G) e := ⟨g, hgset⟩
  refine ⟨k, ?_⟩
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := (baseRangeEquiv e).surjective x
  apply Subtype.ext
  change g • e i = ((σ (baseRangeEquiv e i) : Set.range e) : X)
  rw [hg_apply]
  change e (τ i) = ((σ (baseRangeEquiv e i) : Set.range e) : X)
  exact congrArg Subtype.val
    ((baseRangeEquiv e).apply_symm_apply (σ (baseRangeEquiv e i)))

theorem baseSubgroupQuotientHom_surjective
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (Q : Subgroup (Equiv.Perm (Set.range e : Set X))) :
    Function.Surjective (baseSubgroupQuotientHom (G := G) e Q) := by
  intro q
  obtain ⟨k, hk⟩ := baseSetwisePermHom_surjective h4 e q
  let l : baseSubgroupPreimage (G := G) e Q := ⟨k, by
    change baseSetwisePermHom (G := G) e k ∈ Q
    rw [hk]
    exact q.prop⟩
  refine ⟨l, ?_⟩
  apply Subtype.ext
  exact hk

private theorem disjointSwapQuotientHom_surjective
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X) :
    Function.Surjective (disjointSwapQuotientHom (G := G) e) := by
  intro q
  obtain ⟨k, hk⟩ := baseSetwisePermHom_surjective h4 e q
  let l : disjointSwapPreimage (G := G) e := ⟨k, by
    change baseSetwisePermHom (G := G) e k ∈ rangeDisjointSwapFour e
    rw [hk]
    exact q.prop⟩
  refine ⟨l, ?_⟩
  apply Subtype.ext
  exact hk

private noncomputable def pointwiseStabilizerEquivSetwiseKer
    (e : Fin 4 ↪ X) :
    MulAction.stabilizer G e ≃*
      (baseSetwisePermHom (G := G) e).ker where
  toFun h := by
    have hfix : ∀ i, (h : G) • e i = e i := by
      intro i
      have hi := congrArg (fun a : Fin 4 ↪ X ↦ a i) h.prop
      simpa [Function.Embedding.smul_apply] using hi
    have hset : (h : G) ∈ baseSetwiseStabilizer (G := G) e := by
      rw [MulAction.mem_stabilizer_iff]
      apply Set.Subset.antisymm
      · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        change (h : G) • e i ∈ Set.range e
        rw [hfix]
        exact ⟨i, rfl⟩
      · rintro _ ⟨i, rfl⟩
        refine ⟨e i, ⟨i, rfl⟩, ?_⟩
        change (h : G) • e i = e i
        exact hfix i
    let k : baseSetwiseStabilizer (G := G) e := ⟨h, hset⟩
    refine ⟨k, MonoidHom.mem_ker.mpr ?_⟩
    apply Equiv.ext
    intro x
    obtain ⟨i, rfl⟩ := (baseRangeEquiv e).surjective x
    apply Subtype.ext
    change (h : G) • e i = e i
    exact hfix i
  invFun k := by
    refine ⟨((k : (baseSetwisePermHom (G := G) e).ker) :
      baseSetwiseStabilizer (G := G) e), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    intro i
    have hk := MonoidHom.mem_ker.mp k.prop
    have hi := Equiv.Perm.congr_fun hk (baseRangeEquiv e i)
    exact congrArg Subtype.val hi
  left_inv h := by
    apply Subtype.ext
    rfl
  right_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' h k := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def baseSubgroupKerEquivSetwiseKer
    (e : Fin 4 ↪ X)
    (Q : Subgroup (Equiv.Perm (Set.range e : Set X))) :
    (baseSubgroupQuotientHom (G := G) e Q).ker ≃*
      (baseSetwisePermHom (G := G) e).ker where
  toFun z := by
    refine ⟨(z : baseSubgroupPreimage (G := G) e Q),
      MonoidHom.mem_ker.mpr ?_⟩
    have hz := MonoidHom.mem_ker.mp z.prop
    exact congrArg Subtype.val hz
  invFun z := by
    let l : baseSubgroupPreimage (G := G) e Q :=
      ⟨(z : baseSetwiseStabilizer (G := G) e), by
        change baseSetwisePermHom (G := G) e z ∈ Q
        rw [MonoidHom.mem_ker.mp z.prop]
        exact one_mem _⟩
    refine ⟨l, MonoidHom.mem_ker.mpr ?_⟩
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp z.prop
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' z w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def disjointSwapKerEquivSetwiseKer
    (e : Fin 4 ↪ X) :
    (disjointSwapQuotientHom (G := G) e).ker ≃*
      (baseSetwisePermHom (G := G) e).ker where
  toFun z := by
    refine ⟨(z : disjointSwapPreimage (G := G) e),
      MonoidHom.mem_ker.mpr ?_⟩
    have hz := MonoidHom.mem_ker.mp z.prop
    exact congrArg Subtype.val hz
  invFun z := by
    let l : disjointSwapPreimage (G := G) e :=
      ⟨(z : baseSetwiseStabilizer (G := G) e), by
        change baseSetwisePermHom (G := G) e z ∈ rangeDisjointSwapFour e
        rw [MonoidHom.mem_ker.mp z.prop]
        exact one_mem _⟩
    refine ⟨l, MonoidHom.mem_ker.mpr ?_⟩
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp z.prop
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' z w := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem natCard_setwiseKer_eq_pointwiseStabilizer
    (e : Fin 4 ↪ X) :
    Nat.card (baseSetwisePermHom (G := G) e).ker =
      Nat.card (MulAction.stabilizer G e) := by
  exact Nat.card_congr (pointwiseStabilizerEquivSetwiseKer (G := G) e).symm

theorem natCard_baseSubgroupKer_eq_pointwiseStabilizer
    (e : Fin 4 ↪ X)
    (Q : Subgroup (Equiv.Perm (Set.range e : Set X))) :
    Nat.card (baseSubgroupQuotientHom (G := G) e Q).ker =
      Nat.card (MulAction.stabilizer G e) := by
  calc
    Nat.card (baseSubgroupQuotientHom (G := G) e Q).ker =
        Nat.card (baseSetwisePermHom (G := G) e).ker :=
      Nat.card_congr (baseSubgroupKerEquivSetwiseKer (G := G) e Q)
    _ = Nat.card (MulAction.stabilizer G e) :=
      natCard_setwiseKer_eq_pointwiseStabilizer e

private theorem natCard_disjointSwapKer_eq_pointwiseStabilizer
    (e : Fin 4 ↪ X) :
    Nat.card (disjointSwapQuotientHom (G := G) e).ker =
      Nat.card (MulAction.stabilizer G e) := by
  calc
    Nat.card (disjointSwapQuotientHom (G := G) e).ker =
        Nat.card (baseSetwisePermHom (G := G) e).ker :=
      Nat.card_congr (disjointSwapKerEquivSetwiseKer (G := G) e)
    _ = Nat.card (MulAction.stabilizer G e) :=
      natCard_setwiseKer_eq_pointwiseStabilizer e

private theorem exists_disjointSwap_section
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ∃ s : rangeDisjointSwapFour e →*
        disjointSwapPreimage (G := G) e,
      (disjointSwapQuotientHom (G := G) e).comp s =
        MonoidHom.id (rangeDisjointSwapFour e) := by
  have hoddKer :
      Odd (Nat.card (disjointSwapQuotientHom (G := G) e).ker) := by
    rwa [natCard_disjointSwapKer_eq_pointwiseStabilizer e]
  exact exists_monoidHom_section_of_odd_ker_card_four
    (disjointSwapQuotientHom (G := G) e)
    (disjointSwapQuotientHom_surjective h4 e)
    hoddKer (natCard_rangeDisjointSwapFour e)

theorem exists_commuting_involution_lifts
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    ∃ u v : baseSetwiseStabilizer (G := G) e,
      orderOf u = 2 ∧ orderOf v = 2 ∧ Commute u v ∧
      baseSetwisePermHom (G := G) e u = rangeLeftSwap e ∧
      baseSetwisePermHom (G := G) e v = rangeRightSwap e := by
  classical
  obtain ⟨s, hs⟩ := exists_disjointSwap_section h4 e hodd
  let uL : disjointSwapPreimage (G := G) e := s (rangeLeftSwap e)
  let vL : disjointSwapPreimage (G := G) e := s (rangeRightSwap e)
  let u : baseSetwiseStabilizer (G := G) e := uL
  let v : baseSetwiseStabilizer (G := G) e := vL
  have hsection : ∀ q,
      disjointSwapQuotientHom (G := G) e (s q) = q := by
    intro q
    have hq := DFunLike.congr_fun hs q
    simpa using hq
  have huImage :
      baseSetwisePermHom (G := G) e u = rangeLeftSwap e := by
    exact congrArg Subtype.val (hsection (rangeLeftSwap e))
  have hvImage :
      baseSetwisePermHom (G := G) e v = rangeRightSwap e := by
    exact congrArg Subtype.val (hsection (rangeRightSwap e))
  have hleftSq : (rangeLeftSwap e) ^ 2 = 1 := by
    apply Subtype.ext
    change ((baseRangeEquiv e).permCongrHom baseLeftSwap) ^ 2 = 1
    rw [← map_pow]
    have hsq : baseLeftSwap ^ 2 = 1 := by decide
    rw [hsq, map_one]
  have hrightSq : (rangeRightSwap e) ^ 2 = 1 := by
    apply Subtype.ext
    change ((baseRangeEquiv e).permCongrHom baseRightSwap) ^ 2 = 1
    rw [← map_pow]
    have hsq : baseRightSwap ^ 2 = 1 := by decide
    rw [hsq, map_one]
  have huLSq : uL ^ 2 = 1 := by
    change (s (rangeLeftSwap e)) ^ 2 = 1
    rw [← map_pow, hleftSq, map_one]
  have hvLSq : vL ^ 2 = 1 := by
    change (s (rangeRightSwap e)) ^ 2 = 1
    rw [← map_pow, hrightSq, map_one]
  have huSq : u ^ 2 = 1 := congrArg Subtype.val huLSq
  have hvSq : v ^ 2 = 1 := congrArg Subtype.val hvLSq
  have hleftNe :
      (rangeLeftSwap e : Equiv.Perm (Set.range e : Set X)) ≠ 1 := by
    intro h
    change (baseRangeEquiv e).permCongrHom baseLeftSwap = 1 at h
    exact (show baseLeftSwap ≠ 1 by decide)
      ((baseRangeEquiv e).permCongrHom.injective
        (h.trans (map_one (baseRangeEquiv e).permCongrHom).symm))
  have hrightNe :
      (rangeRightSwap e : Equiv.Perm (Set.range e : Set X)) ≠ 1 := by
    intro h
    change (baseRangeEquiv e).permCongrHom baseRightSwap = 1 at h
    exact (show baseRightSwap ≠ 1 by decide)
      ((baseRangeEquiv e).permCongrHom.injective
        (h.trans (map_one (baseRangeEquiv e).permCongrHom).symm))
  have huNe : u ≠ 1 := by
    intro hu
    apply hleftNe
    calc
      (rangeLeftSwap e : Equiv.Perm (Set.range e : Set X)) =
          baseSetwisePermHom (G := G) e u := huImage.symm
      _ = baseSetwisePermHom (G := G) e 1 := congrArg _ hu
      _ = 1 := map_one _
  have hvNe : v ≠ 1 := by
    intro hv
    apply hrightNe
    calc
      (rangeRightSwap e : Equiv.Perm (Set.range e : Set X)) =
          baseSetwisePermHom (G := G) e v := hvImage.symm
      _ = baseSetwisePermHom (G := G) e 1 := congrArg _ hv
      _ = 1 := map_one _
  have hbaseComm : Commute (rangeLeftSwap e) (rangeRightSwap e) := by
    rw [Commute]
    apply Subtype.ext
    change
      (baseRangeEquiv e).permCongrHom baseLeftSwap *
          (baseRangeEquiv e).permCongrHom baseRightSwap =
        (baseRangeEquiv e).permCongrHom baseRightSwap *
          (baseRangeEquiv e).permCongrHom baseLeftSwap
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  have huvComm : Commute u v := by
    exact (hbaseComm.map s).map
      (disjointSwapPreimage (G := G) e).subtype
  refine ⟨u, v, orderOf_eq_prime huSq huNe,
    orderOf_eq_prime hvSq hvNe, huvComm, huImage, hvImage⟩

end SetwiseAction

end FiveTransitive.Research.OddFourStabilizerLifts

end CFSG
