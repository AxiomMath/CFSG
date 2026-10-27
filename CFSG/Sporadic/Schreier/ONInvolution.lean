module

public import CFSG.Sporadic.Schreier.ONSylowCenter
public import CFSG.GroupActions.FixedPointCentralizerBound

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates

theorem fixCount_eq_card {n : ℕ} {g : Array ℕ} {G : Equiv.Perm (Fin n)} (hg : PRep n g G) :
    fixCount n g = Nat.card {x : Fin n | G x = x} := by
  rw [Nat.card_eq_card_toFinset, Set.toFinset_ofPred, fixCount]
  have e : ((List.range n).filter fun i => g[i]! == i).length = countBelowN n
      (fun i => g[i]! == i) := rfl
  rw [e, countBelowN_eq, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, beq_iff_eq]
  constructor
  · rintro ⟨hi, he⟩
    refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
    rw [← hg ⟨i, hi⟩]
    exact he
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.isLt, ?_⟩
    rw [hg x, hx]

theorem card_fix_z :
    Nat.card {x : Fin N | onz x = x} = 240 := by
  rw [← fixCount_eq_card prep_z, z_cert.2.2.2.1]

theorem onz_x0 :
    onz x0 = x0 := Fin.ext (by rw [← prep_z x0]; exact z_cert.2.2.2.2.1)

theorem qonF :
    CChainFacts nPts 2 qonStrongArrs Data.baseList.toArray Data.strongWords
    Data.baseList.toArray (Array.ofFn (n := Data.baseList.toArray.size) fun i => i.val) false 4 :=
  chainFacts qon_chain_cert.1

abbrev qpts
    (i k : ℕ) : Fin N := CArrays.levPts QON qonStrongArrs Data.baseList.toArray i k

abbrev qtr
    (i k : ℕ) : Equiv.Perm (Fin N) :=
  CArrays.levT QON qonStrongArrs Data.baseList.toArray i k

abbrev qsize (i : ℕ) : ℕ := (CArrays.lev nPts qonStrongArrs Data.baseList.toArray i).pts.size

theorem qsize_eq
    {i : ℕ} (hi : i < 29) :
    qsize i = ([245520, 52136, 36] ++ List.replicate 26 1)[i]'(by simpa using hi) := by
  have hi' : i < QON.baseCount := by rw [qon_baseCount]; exact hi
  have h := qon_point.2 ⟨i, hi'⟩
  rw [QON.orbitSize_eq_card, qon_card_orbit] at h
  exact h.symm

theorem qsize1 :
    qsize 1 = 52136 := by rw [qsize_eq (by norm_num)]; rfl
theorem qsize2 :
    qsize 2 = 36 := by rw [qsize_eq (by norm_num)]; rfl

theorem qtr_facts
    {i k : ℕ} (hi : i < QON.baseCount) (hk : k < qsize i) :
    qtr i k ∈ QON.levelSubgroup i ∧ (∀ b ∈ QON.base.toList.take i, qtr i k b = b) ∧
      qtr i k (QON.base.get ⟨i, hi⟩) = qpts i k :=
  QON.transversal_sound ⟨i, hi⟩ _ _ (qon_arrays.transversal_of_lt qonF hi hk)

theorem qpts_inj
    {i k k' : ℕ} (hi : i < QON.baseCount) (hk : k < qsize i) (hk' : k' < qsize i)
    (h : qpts i k = qpts i k') : k = k' := by
  have F := qon_arrays.levelFacts qonF hi
  have h1 := congrArg Fin.val h
  rw [qon_arrays.levPts_val qonF hi hk, qon_arrays.levPts_val qonF hi hk'] at h1
  rw [← F.pos_pts k hk, ← F.pos_pts k' hk', h1]

theorem qbase_val
    (i : Fin QON.baseCount) : ((QON.base.get i : Fin N) : ℕ) = baseIndex i :=
  cert_on_schreier_action_data.2.2.2.2.2.2.2.2.1 i

theorem qbase0 :
    QON.base.get ⟨0, by rw [qon_baseCount]; norm_num⟩ = x0 :=
  Fin.ext (by rw [qbase_val]; rfl)

theorem qbase1 :
    QON.base.get ⟨1, by rw [qon_baseCount]; norm_num⟩ = ⟨227759, by norm_num⟩ :=
  Fin.ext (by rw [qbase_val]; rfl)

theorem qbase2 :
    QON.base.get ⟨2, by rw [qon_baseCount]; norm_num⟩ = ⟨100817, by norm_num⟩ :=
  Fin.ext (by rw [qbase_val]; rfl)

theorem mem_take_of
    {i j : ℕ} (hj : j < i) (hi : i ≤ QON.baseCount) :
    QON.base.get ⟨j, by omega⟩ ∈ QON.base.toList.take i := by
  rw [List.mem_take_iff_getElem]
  exact ⟨j, by simp; omega, by simp [Vector.get]⟩

@[expose] def pairT
    (k₁ k₂ : ℕ) : Equiv.Perm (Fin N) := qtr 1 k₁ * qtr 2 k₂

theorem pairT_mem
    {k₁ k₂ : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2) :
    pairT k₁ k₂ ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0} := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  obtain ⟨hL1, hf1, -⟩ := qtr_facts hb1 h1
  obtain ⟨hL2, hf2, -⟩ := qtr_facts hb2 h2
  have hP := fun i => QON.levelSubgroup_le_originalSubgroup_of_point qon_point.1 i
  refine Subgroup.mem_inf.2 ⟨?_, (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).2 ?_⟩
  · rw [← qon_originalSubgroup]
    exact mul_mem (hP 1 hL1) (hP 2 hL2)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Equiv.Perm.smul_def, pairT, Equiv.Perm.mul_apply, ← qbase0,
      hf2 _ (mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num)),
      hf1 _ (mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num))]

theorem pairT_inj
    {k₁ k₂ k₁' k₂' : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2)
    (h1' : k₁' < qsize 1) (h2' : k₂' < qsize 2) (h : pairT k₁ k₂ = pairT k₁' k₂') :
    k₁ = k₁' ∧ k₂ = k₂' := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  obtain ⟨-, -, he1⟩ := qtr_facts hb1 h1
  obtain ⟨-, -, he1'⟩ := qtr_facts hb1 h1'
  obtain ⟨-, hf2, he2⟩ := qtr_facts hb2 h2
  obtain ⟨-, hf2', he2'⟩ := qtr_facts hb2 h2'
  have hb : QON.base.get ⟨1, hb1⟩ ∈ QON.base.toList.take 2 :=
    mem_take_of (by norm_num) (by rw [qon_baseCount]; norm_num)
  have e1 := DFunLike.congr_fun h (QON.base.get ⟨1, hb1⟩)
  rw [pairT, pairT, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf2 _ hb, hf2' _ hb, he1,
    he1'] at e1
  have hk1 := qpts_inj hb1 h1 h1' e1
  subst hk1
  refine ⟨rfl, ?_⟩
  have e2 := DFunLike.congr_fun (mul_left_cancel (show qtr 1 k₁ * qtr 2 k₂ = qtr 1 k₁ * qtr 2 k₂'
    from h)) (QON.base.get ⟨2, hb2⟩)
  rw [he2, he2'] at e2
  exact qpts_inj hb2 h2 h2' e2

theorem exists_pairT
    {g : Equiv.Perm (Fin N)}
    (hg : g ∈ Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) :
    ∃ k₁ < qsize 1, ∃ k₂ < qsize 2, g = pairT k₁ k₂ := by
  obtain ⟨hgP, hgfix⟩ := Subgroup.mem_inf.1 hg
  have hg0 : g x0 = x0 := by
    have := (mem_fixingSubgroup_iff (Equiv.Perm (Fin N))).1 hgfix x0 rfl
    rwa [Equiv.Perm.smul_def] at this
  obtain ⟨⟨y, w⟩, hyw, -⟩ := PairDecomp.exists_unique_pair QON qon_three qon_valid qon_singleton
    (by rw [qon_originalSubgroup]; exact hgP) (by rw [qon_base_get_l0]; exact hg0)
  have hpts : ∀ (i : ℕ) (hi : i < QON.baseCount) (x : QON.orbitPoints ⟨i, hi⟩),
      ∃ k < qsize i, (x : Fin N) = qpts i k ∧ QON.orbitTransversal ⟨i, hi⟩ x = qtr i k := by
    intro i hi x
    have h1 := (QON.orbitTransversal_spec ⟨i, hi⟩ x).1
    change (QON.orbitSearch ⟨i, hi⟩).transversal? x = _ at h1
    have h1' := h1
    rw [qon_arrays.orbitSearch_eq qonF hi] at h1'
    change List.lookup (x : Fin N) ((List.range (qsize i)).map fun k => (qpts i k, qtr i k)) =
      _ at h1'
    obtain ⟨before, after, heq, -⟩ := List.lookup_eq_some_iff.1 h1'
    have hmem : ((x : Fin N), QON.orbitTransversal ⟨i, hi⟩ x) ∈
        (List.range (qsize i)).map fun k => (qpts i k, qtr i k) := by
      rw [heq]
      simp
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
    obtain ⟨k, hk, hxk, htk⟩ := hmem
    exact ⟨k, hk, hxk.symm, htk.symm⟩
  obtain ⟨k₁, hk₁, -, ht₁⟩ := hpts 1 _ y
  obtain ⟨k₂, hk₂, -, ht₂⟩ := hpts 2 _ w
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [hyw, pairT]
  exact congrArg₂ (· * ·) ht₁ ht₂

abbrev qLevels : Array CLevel :=
  cLevels nPts Data.baseList.toArray
    (allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray)

abbrev qSteps : Array (Array (Array ℕ)) :=
  allSteps qonStrongArrs (pinvs nPts qonStrongArrs) Data.baseList.toArray

theorem tr2App_eq
    {k₁ k₂ : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2) {p : ℕ} (hp : p < N) :
    tr2App qLevels qSteps 1 2 k₁ k₂ p = (pairT k₁ k₂ ⟨p, hp⟩ : ℕ) := by
  have hb1 : 1 < QON.baseCount := by rw [qon_baseCount]; norm_num
  have hb2 : 2 < QON.baseCount := by rw [qon_baseCount]; norm_num
  unfold tr2App
  rw [qon_arrays.trApp_eq qonF hb2 _ _ h2 h2 p hp,
    qon_arrays.trApp_eq qonF hb1 _ _ h1 h1 _ (Fin.isLt _), pairT, Equiv.Perm.mul_apply]

abbrev testF (k₁ k₂ : ℕ) : Bool :=
  (#[0, 227759, 100817] : Array ℕ).all fun p =>
    tr2App qLevels qSteps 1 2 k₁ k₂ zArr[p]! == zArr[tr2App qLevels qSteps 1 2 k₁ k₂ p]!

theorem testF_point
    {k₁ k₂ : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2) {p : ℕ} (hp : p < N) :
    (tr2App qLevels qSteps 1 2 k₁ k₂ zArr[p]! == zArr[tr2App qLevels qSteps 1 2 k₁ k₂ p]!) =
      true ↔ pairT k₁ k₂ (onz ⟨p, hp⟩) = onz (pairT k₁ k₂ ⟨p, hp⟩) := by
  have hz : zArr[p]! = (onz ⟨p, hp⟩ : ℕ) := prep_z ⟨p, hp⟩
  rw [beq_iff_eq, hz, tr2App_eq h1 h2 (Fin.isLt _), tr2App_eq h1 h2 hp, prep_z, Fin.ext_iff]

theorem testF_point'
    {k₁ k₂ : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2) {p : ℕ}
    (hp : p < N) :
    (tr2App qLevels qSteps 1 2 k₁ k₂ zArr[p]! == zArr[tr2App qLevels qSteps 1 2 k₁ k₂ p]!) =
      true ↔ (pairT k₁ k₂ * onz) ⟨p, hp⟩ = (onz * pairT k₁ k₂) ⟨p, hp⟩ := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact testF_point h1 h2 hp

theorem testF_iff
    {k₁ k₂ : ℕ} (h1 : k₁ < qsize 1) (h2 : k₂ < qsize 2) :
    testF k₁ k₂ = true ↔ pairT k₁ k₂ * onz = onz * pairT k₁ k₂ := by
  have hP : pairT k₁ k₂ ∈ Pv := (Subgroup.mem_inf.1 (pairT_mem h1 h2)).1
  rw [testF, Array.all_eq_true]
  constructor
  · intro h
    have e0 := (testF_point' h1 h2 (p := 0) (by norm_num)).1 (h 0 (by decide))
    have e1 := (testF_point' h1 h2 (p := 227759) (by norm_num)).1 (h 1 (by decide))
    have e2 := (testF_point' h1 h2 (p := 100817) (by norm_num)).1 (h 2 (by decide))
    exact eq_of_three (mul_mem hP (evalS_mem _)) (mul_mem (evalS_mem _) hP) e0 e1 e2
  · intro h j hj
    have hj3 : j < 3 := by simpa using hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · exact (testF_point' h1 h2 (p := 0) (by norm_num)).2 (DFunLike.congr_fun h _)
    · exact (testF_point' h1 h2 (p := 227759) (by norm_num)).2 (DFunLike.congr_fun h _)
    · exact (testF_point' h1 h2 (p := 100817) (by norm_num)).2 (DFunLike.congr_fun h _)

theorem list_sum_range (m : ℕ) (f : ℕ → ℕ) :
    ((List.range m).map f).sum = ∑ a ∈ Finset.range m, f a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sum_filter_length (m₁ m₂ : ℕ) (p : ℕ → ℕ → Bool) :
    ((List.range m₁).map fun a => ((List.range m₂).filter (p a)).length).sum =
      ((Finset.range m₁ ×ˢ Finset.range m₂).filter fun x => p x.1 x.2 = true).card := by
  rw [list_sum_range, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.card_filter]
  exact countBelowN_eq m₂ (p a)

abbrev passing : Finset (ℕ × ℕ) :=
  (Finset.range (qsize 1) ×ˢ Finset.range (qsize 2)).filter fun x => testF x.1 x.2 = true

theorem card_passing : passing.card = 672 := by
  rw [← comm_cert, commCount, ← sum_filter_length]

abbrev cP0 :
    Subgroup (Equiv.Perm (Fin N)) :=
  Subgroup.centralizer {onz} ⊓ (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0})

theorem pairT_mem_cP0
    {x : ℕ × ℕ} (hx : x ∈ passing) : pairT x.1 x.2 ∈ cP0 := by
  simp only [passing, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
  obtain ⟨⟨h1, h2⟩, ht⟩ := hx
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ((testF_iff h1 h2).1 ht),
    pairT_mem h1 h2⟩

theorem card_cP0 :
    Nat.card cP0 = 672 := by
  rw [← card_passing, ← Nat.card_eq_finsetCard]
  symm
  refine Nat.card_eq_of_bijective (fun x => ⟨pairT x.1.1 x.1.2, pairT_mem_cP0 x.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    simp only [passing, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab hcd
    have := pairT_inj hab.1.1 hab.1.2 hcd.1.1 hcd.1.2 (congrArg Subtype.val h)
    simp only [this.1, this.2]
  · rintro ⟨g, hg⟩
    obtain ⟨hgc, hg0⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := exists_pairT hg0
    refine ⟨⟨(k₁, k₂), ?_⟩, rfl⟩
    simp only [passing, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hk₁, hk₂⟩, (testF_iff hk₁ hk₂).2 (Subgroup.mem_centralizer_singleton_iff.1 hgc)⟩

theorem prep_onMgens'' :
    ∀ j (hj : j < onMgens.length), PRep N (wordArrs Data.MWords)[j]! onMgens[j] :=
  prep_wordArrs words_ok.2.1

theorem onM_le_centralizer_z :
    onM ≤ Subgroup.centralizer {onz} := by
  rw [onM, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hj3 : j < 3 := by rw [onMgens_length] at hj; exact hj
  have h := eq_of_peq (prep_pcomp (prep_onMgens'' j hj) prep_z)
    (prep_pcomp prep_z (prep_onMgens'' j hj)) (allBelowN_spec z_cert.2.2.2.2.2 hj3)
  exact Subgroup.mem_centralizer_singleton_iff.2 h

theorem card_subgroupOf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (K.subgroupOf H) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv,
    Subgroup.subgroupOf_map_subtype, inf_comm]

@[expose] def zP :
    Pv := ⟨onz, evalS_mem _⟩

theorem centralizer_zP :
    Subgroup.centralizer {zP} = (Subgroup.centralizer {onz}).subgroupOf Pv := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem stabilizer_x0 :
    MulAction.stabilizer Pv x0 =
    (fixingSubgroup (Equiv.Perm (Fin N)) {x0}).subgroupOf Pv := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rfl

theorem subgroupOf_inf' {G : Type*} [Group G] (A B H : Subgroup G) :
    A.subgroupOf H ⊓ B.subgroupOf H = (A ⊓ B).subgroupOf H := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]

theorem card_centralizer_z_le :
    Nat.card (Pv ⊓ Subgroup.centralizer {onz} : Subgroup (Equiv.Perm (Fin N))) ≤ 161280 := by
  have hb := CFSG.GroupActions.fixed_point_centralizer_order_bound zP x0 (by
    show onz x0 = x0
    exact onz_x0)
  rw [centralizer_zP, stabilizer_x0, subgroupOf_inf', card_subgroupOf, card_subgroupOf] at hb
  have hfix : Nat.card {x : Fin N | zP • x = x} = 240 := card_fix_z
  rw [hfix] at hb
  have h672 : Nat.card (Pv ⊓ (Subgroup.centralizer {onz} ⊓
      fixingSubgroup (Equiv.Perm (Fin N)) {x0}) : Subgroup (Equiv.Perm (Fin N))) = 672 := by
    rw [← card_cP0, inf_left_comm]
  rw [h672] at hb
  exact hb

theorem onM_eq_centralizer_z :
    onM = Pv ⊓ Subgroup.centralizer {onz} :=
  Subgroup.eq_of_le_of_card_ge (le_inf onM_le onM_le_centralizer_z)
    (by rw [card_onM]; exact card_centralizer_z_le)

theorem centralizer_centerIn_T :
    Subgroup.centralizer (CFSG.centerIn onT : Set (Equiv.Perm (Fin N))) =
      Subgroup.centralizer {onz} := by
  rw [onT_centerIn, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem at_on_full_involution_centralizer :
    Nat.card {x : Fin N | onz x = x} = 240 ∧ onz x0 = x0 ∧
      Nat.card (Subgroup.centralizer {onz} ⊓ (Pv ⊓ fixingSubgroup (Equiv.Perm (Fin N)) {x0}) :
        Subgroup (Equiv.Perm (Fin N))) = 672 ∧
      onM = Pv ⊓ Subgroup.centralizer {onz} ∧
      onM = Pv ⊓ Subgroup.centralizer (CFSG.centerIn onT : Set (Equiv.Perm (Fin N))) ∧
      Nat.card onM = 161280 :=
  ⟨card_fix_z, onz_x0, card_cP0, onM_eq_centralizer_z,
    by rw [centralizer_centerIn_T]; exact onM_eq_centralizer_z, card_onM⟩

end CFSG.ONSchreier
