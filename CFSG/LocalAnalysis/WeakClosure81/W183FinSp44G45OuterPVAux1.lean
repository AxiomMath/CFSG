module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44DataOuter
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44ModelAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

open CFSG.Quasithin CFSG.Open Subgroup

theorem w183finSp44pv_nodupE_sound : ∀ {l : List El}, nodupE l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    simp only [nodupE, Bool.and_eq_true, Bool.not_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine List.nodup_cons.mpr ⟨?_, w183finSp44pv_nodupE_sound h2⟩
    intro hx
    have : memK l x = true := by
      rw [memK, List.any_eq_true]
      exact ⟨x, hx, by simp⟩
    rw [this] at h1
    exact Bool.noConfusion h1

theorem w183finSp44pv_getD_valid {l : List El} {d : El} (hl : ∀ x ∈ l, validB x = true)
    (hd : validB d = true) (n : Nat) : validB (l.getD n d) = true := by
  rcases Nat.lt_or_ge n l.length with hn | hn
  · rw [List.getD_eq_getElem l d hn]; exact hl _ (List.getElem_mem hn)
  · rw [List.getD_eq_default l d hn]; exact hd

theorem w183finSp44pv_span2_valid {gens : List El} (h : ∀ x ∈ gens, validB x = true) :
    ∀ x ∈ span2 gens, validB x = true := by
  have aux : ∀ (gens A : List El), (∀ x ∈ A, validB x = true) →
      (∀ x ∈ gens, validB x = true) →
      ∀ x ∈ gens.foldl (fun l g => l ++ l.map fun x => gmulE x g) A, validB x = true := by
    intro gens
    induction gens with
    | nil => intro A hA _; simpa using hA
    | cons g gs ih =>
      intro A hA hg
      rw [List.foldl_cons]
      apply ih (A ++ A.map fun x => gmulE x g)
      · intro x hx
        rcases List.mem_append.mp hx with hxA | hxmap
        · exact hA x hxA
        · rcases List.mem_map.mp hxmap with ⟨a, ha, rfl⟩
          exact validB_gmulE (hA a ha) (hg g (by simp))
      · intro x hx
        exact hg x (List.mem_cons_of_mem g hx)
  simpa [span2] using aux gens [oneE] (by simp [validB_oneE]) h

theorem w183finSp44pv_gmulE_assoc {a b c : El} (ha : validB a = true) (hb : validB b = true)
    (hc : validB c = true) : gmulE (gmulE a b) c = gmulE a (gmulE b c) := by
  apply autOf_inj (validB_gmulE (validB_gmulE ha hb) hc) (validB_gmulE ha (validB_gmulE hb hc))
  rw [autOf_gmulE (validB_gmulE ha hb) hc, autOf_gmulE ha (validB_gmulE hb hc),
    autOf_gmulE ha hb, autOf_gmulE hb hc, mul_assoc]

theorem w183finSp44pv_checkTree_par {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) :
    par.length = T.length ∧
    ∀ i, 1 ≤ i → i < T.length →
      (par.getD i (0, 0)).1 < i ∧
      T.getD i oneE = gmulE (T.getD (par.getD i (0, 0)).1 oneE)
        (gensX.getD (par.getD i (0, 0)).2 oneE) := by
  have ht' := ht
  simp only [checkTree, Bool.and_eq_true] at ht'
  obtain ⟨⟨⟨⟨hhead, hlen⟩, hzip⟩, hnodup⟩, hcl⟩ := ht'
  have hlen' : par.length = T.length := beq_iff_eq.mp hlen
  refine ⟨hlen', ?_⟩
  intro i hi hiT
  have hi' : i < par.length := by rw [hlen']; exact hiT
  have hpari : par.getD i (0, 0) = par[i] := List.getD_eq_getElem par (0, 0) hi'
  have hTi : T.getD i oneE = T[i] := List.getD_eq_getElem T oneE hiT
  set j := i - 1 with hj
  have h1j : 1 + j = i := by omega
  have hjT : j < (T.drop 1).length := by rw [List.length_drop]; omega
  have hjP : j < (par.drop 1).length := by rw [List.length_drop]; omega
  have hjR : j < (List.range par.length).length := by rw [List.length_range]; omega
  have hjI : j < ((par.drop 1).zip (List.range par.length)).length := by
    rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hjP, hjR⟩
  have hjL : j < ((T.drop 1).zip ((par.drop 1).zip (List.range par.length))).length := by
    rw [List.length_zip]; exact Nat.lt_min.mpr ⟨hjT, hjI⟩
  have hget := List.all_eq_true.mp hzip
    (((T.drop 1).zip ((par.drop 1).zip (List.range par.length)))[j]'hjL)
    (List.getElem_mem hjL)
  have helem : ((T.drop 1).zip ((par.drop 1).zip (List.range par.length)))[j]'hjL =
      ((T.drop 1)[j]'hjT, ((par.drop 1)[j]'hjP, j)) := by
    rw [List.getElem_zip (h := hjL), List.getElem_zip (h := hjI), List.getElem_range]
  rw [helem] at hget
  simp only [Bool.and_eq_true] at hget
  obtain ⟨hple, heq⟩ := hget
  have hple' := of_decide_eq_true hple
  have heq' := beq_iff_eq.mp heq
  have hidxP : (par.drop 1)[j]'hjP = par[i] := by
    rw [List.getElem_drop]
    congr 1
  have hidxT : (T.drop 1)[j]'hjT = T[i] := by
    rw [List.getElem_drop]
    congr 1
  rw [hidxP] at hple' heq'
  rw [hidxT] at heq'
  constructor
  · rw [hpari]; omega
  · rw [hTi, hpari]
    exact heq'.symm

private theorem w183finSp44pv_memK_sound {L : List El} {x : El} (h : memK L x = true) : x ∈ L := by
  rw [memK] at h
  obtain ⟨a, ha, hax⟩ := List.any_eq_true.mp h
  exact beq_iff_eq.mp hax ▸ ha

theorem w183finSp44pv_checkTree_zero {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) : T.getD 0 oneE = oneE := by
  have ht' := ht
  simp only [checkTree, Bool.and_eq_true] at ht'
  obtain ⟨⟨⟨⟨hhead, _⟩, _⟩, _⟩, _⟩ := ht'
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp (beq_iff_eq.mp hhead)
  rfl

theorem w183finSp44pv_checkTree_nodup {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) : T.Nodup := by
  have ht' := ht
  simp only [checkTree, Bool.and_eq_true] at ht'
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, hnodup⟩, _⟩ := ht'
  exact w183finSp44pv_nodupE_sound hnodup

theorem w183finSp44pv_checkTree_closed {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) :
    ∀ x ∈ T, ∀ g ∈ gensX, gmulE x g ∈ T := by
  have ht' := ht
  simp only [checkTree, Bool.and_eq_true] at ht'
  obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hcl⟩ := ht'
  intro x hx g hg
  exact w183finSp44pv_memK_sound
    ((List.all_eq_true.mp ((List.all_eq_true.mp hcl) x hx)) g hg)

theorem w183finSp44pv_checkTree_one_mem {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) : oneE ∈ T := by
  have ht' := ht
  simp only [checkTree, Bool.and_eq_true] at ht'
  obtain ⟨⟨⟨⟨hhead, _⟩, _⟩, _⟩, _⟩ := ht'
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp (beq_iff_eq.mp hhead)
  exact List.mem_cons_self ..

theorem w183finSp44pv_gmulE_oneE {x : El} (hx : validB x = true) : gmulE x oneE = x := by
  apply autOf_inj (validB_gmulE hx validB_oneE) hx
  rw [autOf_gmulE hx validB_oneE, autOf_oneE, mul_one]

theorem w183finSp44pv_oneE_gmulE {x : El} (hx : validB x = true) : gmulE oneE x = x := by
  apply autOf_inj (validB_gmulE validB_oneE hx) hx
  rw [autOf_gmulE validB_oneE hx, autOf_oneE, one_mul]

theorem w183finSp44pv_valid_conjE {g x : El} (hg : validB g = true) (hx : validB x = true) :
    validB (conjE g x) = true := by
  unfold conjE
  exact validB_gmulE hg (validB_gmulE hx (validB_invE hg))

theorem w183finSp44pv_conjE_gmulE {g a b : El} (hg : validB g = true) (ha : validB a = true)
    (hb : validB b = true) : gmulE (conjE g a) (conjE g b) = conjE g (gmulE a b) := by
  have hga := w183finSp44pv_valid_conjE hg ha
  have hgb := w183finSp44pv_valid_conjE hg hb
  have hgab : validB (gmulE a b) = true := validB_gmulE ha hb
  apply autOf_inj (validB_gmulE hga hgb) (w183finSp44pv_valid_conjE hg hgab)
  rw [autOf_gmulE hga hgb, autOf_conjE hg ha, autOf_conjE hg hb, autOf_conjE hg hgab,
    autOf_gmulE ha hb]
  group

theorem w183finSp44pv_conjE_oneE {g : El} (hg : validB g = true) : conjE g oneE = oneE := by
  apply autOf_inj (w183finSp44pv_valid_conjE hg validB_oneE) validB_oneE
  rw [autOf_conjE hg validB_oneE, autOf_oneE, mul_one, mul_inv_cancel]

theorem w183finSp44pv_checkTree_valid {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) (hg : ∀ g ∈ gensX, validB g = true) :
    ∀ x ∈ T, validB x = true := by
  obtain ⟨hlen, hpar⟩ := w183finSp44pv_checkTree_par ht
  have hgD : ∀ n, validB (gensX.getD n oneE) = true :=
    w183finSp44pv_getD_valid hg validB_oneE
  have h0 : T.getD 0 oneE = oneE := w183finSp44pv_checkTree_zero ht
  have key : ∀ i, i < T.length → validB (T.getD i oneE) = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hiT
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [h0]; exact validB_oneE
      · obtain ⟨hplt, heq⟩ := hpar i (by omega) hiT
        rw [heq]
        exact validB_gmulE (ih _ hplt (by omega)) (hgD _)
  intro x hx
  obtain ⟨i, hiT, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [← List.getD_eq_getElem T oneE hiT]
  exact key i hiT

theorem w183finSp44pv_checkTree_mem {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) (hg : ∀ g ∈ gensX, validB g = true) :
    ∀ x ∈ T, autOf x ∈ Subgroup.closure (autOf '' {y | y ∈ gensX}) := by
  obtain ⟨hlen, hpar⟩ := w183finSp44pv_checkTree_par ht
  have hvalid := w183finSp44pv_checkTree_valid ht hg
  have hvalidD : ∀ n, validB (T.getD n oneE) = true :=
    w183finSp44pv_getD_valid hvalid validB_oneE
  have hgD : ∀ n, validB (gensX.getD n oneE) = true :=
    w183finSp44pv_getD_valid hg validB_oneE
  have h0 : T.getD 0 oneE = oneE := w183finSp44pv_checkTree_zero ht
  have hgX : ∀ n, autOf (gensX.getD n oneE) ∈ Subgroup.closure (autOf '' {y | y ∈ gensX}) := by
    intro n
    rcases Nat.lt_or_ge n gensX.length with hn | hn
    · rw [List.getD_eq_getElem gensX oneE hn]
      exact Subgroup.subset_closure ⟨gensX[n], List.getElem_mem hn, rfl⟩
    · rw [List.getD_eq_default gensX oneE hn, autOf_oneE]
      exact one_mem _
  have key : ∀ i, i < T.length →
      autOf (T.getD i oneE) ∈ Subgroup.closure (autOf '' {y | y ∈ gensX}) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hiT
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [h0, autOf_oneE]; exact one_mem _
      · obtain ⟨hplt, heq⟩ := hpar i (by omega) hiT
        rw [heq, autOf_gmulE (hvalidD _) (hgD _)]
        exact mul_mem (ih _ hplt (by omega)) (hgX _)
  intro x hx
  obtain ⟨i, hiT, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [← List.getD_eq_getElem T oneE hiT]
  exact key i hiT

theorem w183finSp44pv_checkTree_mul {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) (hg : ∀ g ∈ gensX, validB g = true) :
    ∀ x ∈ T, ∀ y ∈ T, gmulE x y ∈ T := by
  obtain ⟨hlen, hpar⟩ := w183finSp44pv_checkTree_par ht
  have hvalid := w183finSp44pv_checkTree_valid ht hg
  have hvalidD : ∀ n, validB (T.getD n oneE) = true :=
    w183finSp44pv_getD_valid hvalid validB_oneE
  have hgD : ∀ n, validB (gensX.getD n oneE) = true :=
    w183finSp44pv_getD_valid hg validB_oneE
  have h0 : T.getD 0 oneE = oneE := w183finSp44pv_checkTree_zero ht
  have hclosed := w183finSp44pv_checkTree_closed ht
  have hclD : ∀ y ∈ T, ∀ n, gmulE y (gensX.getD n oneE) ∈ T := by
    intro y hy n
    rcases Nat.lt_or_ge n gensX.length with hn | hn
    · rw [List.getD_eq_getElem gensX oneE hn]
      exact hclosed y hy _ (List.getElem_mem hn)
    · rw [List.getD_eq_default gensX oneE hn, w183finSp44pv_gmulE_oneE (hvalid y hy)]
      exact hy
  have key : ∀ i, i < T.length → ∀ x ∈ T, gmulE x (T.getD i oneE) ∈ T := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hiT x hx
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [h0, w183finSp44pv_gmulE_oneE (hvalid x hx)]; exact hx
      · obtain ⟨hplt, heq⟩ := hpar i (by omega) hiT
        rw [heq, ← w183finSp44pv_gmulE_assoc (hvalid x hx) (hvalidD _) (hgD _)]
        exact hclD _ (ih _ hplt (by omega) x hx) _
  intro x hx y hy
  obtain ⟨i, hiT, rfl⟩ := List.mem_iff_getElem.mp hy
  rw [← List.getD_eq_getElem T oneE hiT]
  exact key i hiT x hx

theorem w183finSp44pv_checkTree_card {gensX T : List El} {par : List (Nat × Nat)}
    (ht : checkTree gensX T par = true) (hg : ∀ g ∈ gensX, validB g = true)
    (hinv : ∀ g ∈ gensX, gmulE g g = oneE) :
    Nat.card (Subgroup.closure (autOf '' {y | y ∈ gensX})) = T.length := by
  have hvalid := w183finSp44pv_checkTree_valid ht hg
  have hmem := w183finSp44pv_checkTree_mem ht hg
  have hmul := w183finSp44pv_checkTree_mul ht hg
  have hone := w183finSp44pv_checkTree_one_mem ht
  have hnodup := w183finSp44pv_checkTree_nodup ht
  have hclosed := w183finSp44pv_checkTree_closed ht
  have hinv' : ∀ g ∈ gensX, (autOf g)⁻¹ = autOf g := by
    intro g hg'
    have h2 : autOf g * autOf g = 1 := by
      rw [← autOf_gmulE (hg g hg') (hg g hg'), hinv g hg', autOf_oneE]
    calc (autOf g)⁻¹ = (autOf g)⁻¹ * 1 := (mul_one _).symm
      _ = (autOf g)⁻¹ * (autOf g * autOf g) := by rw [h2]
      _ = ((autOf g)⁻¹ * autOf g) * autOf g := by rw [mul_assoc]
      _ = 1 * autOf g := by rw [inv_mul_cancel]
      _ = autOf g := one_mul _
  have hSinv : (autOf '' {y | y ∈ gensX})⁻¹ = autOf '' {y | y ∈ gensX} := by
    ext α
    rw [Set.mem_inv, Set.mem_image, Set.mem_image]
    constructor
    · rintro ⟨g, hg', hgα⟩
      refine ⟨g, hg', ?_⟩
      calc autOf g = (autOf g)⁻¹ := (hinv' g hg').symm
        _ = (α⁻¹)⁻¹ := by rw [← hgα]
        _ = α := inv_inv α
    · rintro ⟨g, hg', hgα⟩
      exact ⟨g, hg', by rw [← hgα]; exact (hinv' g hg').symm⟩
  have hSsub : autOf '' {y | y ∈ gensX} ⊆ autOf '' {x | x ∈ T} := by
    rintro _ ⟨g, hg', rfl⟩
    have hgT : g ∈ T := by
      have h1 := hclosed oneE hone g hg'
      rwa [w183finSp44pv_oneE_gmulE (hg g hg')] at h1
    exact ⟨g, hgT, rfl⟩
  let M : Submonoid (MulAut S4) :=
    { carrier := autOf '' {x | x ∈ T}
      one_mem' := ⟨oneE, hone, autOf_oneE⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨gmulE x y, hmul x hx y hy, autOf_gmulE (hvalid x hx) (hvalid y hy)⟩ }
  have hsub : (Subgroup.closure (autOf '' {y | y ∈ gensX}) : Set (MulAut S4)) ⊆
      autOf '' {x | x ∈ T} := by
    intro α hα
    have hα' : α ∈ (Subgroup.closure (autOf '' {y | y ∈ gensX})).toSubmonoid := hα
    rw [Subgroup.closure_toSubmonoid, hSinv, Set.union_self] at hα'
    exact (Submonoid.closure_le (s := autOf '' {y | y ∈ gensX}) (S := M)).mpr hSsub hα'
  have heq : (Subgroup.closure (autOf '' {y | y ∈ gensX}) : Set (MulAut S4)) =
      autOf '' {x | x ∈ T} :=
    Set.Subset.antisymm hsub (by
      rintro _ ⟨x, hxT, rfl⟩
      exact hmem x hxT)
  let f : ↥T.toFinset → Subgroup.closure (autOf '' {y | y ∈ gensX}) := fun x =>
    ⟨autOf x.1, hmem x.1 (List.mem_toFinset.mp x.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply autOf_inj (hvalid x.1 (List.mem_toFinset.mp x.2))
        (hvalid y.1 (List.mem_toFinset.mp y.2))
      exact congrArg Subtype.val hxy
    · intro α
      have hα : (α : MulAut S4) ∈ autOf '' {x | x ∈ T} := by
        rw [← heq]; exact α.2
      obtain ⟨x, hxT, hxα⟩ := hα
      exact ⟨⟨x, List.mem_toFinset.mpr hxT⟩, Subtype.ext hxα⟩
  have hcard : Nat.card (Subgroup.closure (autOf '' {y | y ∈ gensX})) = Nat.card ↥T.toFinset :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodup]

theorem w183finSp44pv_map_closure_conj {gens : List El} {g : El} (hg : validB g = true)
    (hval : ∀ x ∈ gens, validB x = true) :
    (Subgroup.closure (autOf '' {x | x ∈ gens})).map (MulAut.conj (autOf g)).toMonoidHom =
      Subgroup.closure (autOf '' {x | x ∈ gens.map (conjE g)}) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext α
  constructor
  · rintro ⟨β, ⟨x, hx, rfl⟩, hβ⟩
    refine ⟨conjE g x, List.mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
    rw [autOf_conjE hg (hval x hx), ← MulAut.conj_apply]
    exact hβ
  · rintro ⟨z, hz, hzα⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    refine ⟨autOf x, ⟨⟨x, hx, rfl⟩, ?_⟩⟩
    change (MulAut.conj (autOf g)) (autOf x) = α
    rw [MulAut.conj_apply, ← autOf_conjE hg (hval x hx)]
    exact hzα

theorem w183finSp44pv_conjE_inj {g a b : El} (hg : validB g = true) (ha : validB a = true)
    (hb : validB b = true) (h : conjE g a = conjE g b) : a = b := by
  have h1 : autOf (conjE g a) = autOf (conjE g b) := by rw [h]
  have h2 : (MulAut.conj (autOf g)) (autOf a) = (MulAut.conj (autOf g)) (autOf b) := by
    rw [show (MulAut.conj (autOf g)) (autOf a) = autOf (conjE g a) from by
      rw [autOf_conjE hg ha, MulAut.conj_apply]]
    rw [show (MulAut.conj (autOf g)) (autOf b) = autOf (conjE g b) from by
      rw [autOf_conjE hg hb, MulAut.conj_apply]]
    exact h1
  exact autOf_inj ha hb ((MulAut.conj (autOf g)).injective h2)

theorem w183finSp44pv_mem_normalizer_iff {Ry : List El} {r : El}
    (hvalRy : ∀ s ∈ Ry, validB s = true) (hr : validB r = true)
    (hRyI : ∀ z, validB z = true → (autOf z ∈ Subgroup.closure (autOf '' {x | x ∈ Ry}) ↔ z ∈ Ry)) :
    autOf r ∈ Subgroup.normalizer (Subgroup.closure (autOf '' {x | x ∈ Ry}) : Set (MulAut S4)) ↔
      ∀ s ∈ Ry, conjE r s ∈ Ry := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h s hs
    have hmem : (MulAut.conj (autOf r)) (autOf s) ∈
        (Subgroup.closure (autOf '' {x | x ∈ Ry})).map
          (MulAut.conj (autOf r)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨autOf s, Subgroup.subset_closure ⟨s, hs, rfl⟩, rfl⟩
    have hmem' : (MulAut.conj (autOf r)) (autOf s) ∈
        Subgroup.closure (autOf '' {x | x ∈ Ry}) := h ▸ hmem
    have : autOf (conjE r s) ∈ Subgroup.closure (autOf '' {x | x ∈ Ry}) := by
      rw [autOf_conjE hr (hvalRy s hs), ← MulAut.conj_apply]
      exact hmem'
    exact (hRyI _ (w183finSp44pv_valid_conjE hr (hvalRy s hs))).mp this
  · intro h
    have hmap : (Subgroup.closure (autOf '' {x | x ∈ Ry})).map
        (MulAut.conj (autOf r)).toMonoidHom ≤ Subgroup.closure (autOf '' {x | x ∈ Ry}) := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro α ⟨β, ⟨s, hs, rfl⟩, rfl⟩
      have hmem : autOf (conjE r s) ∈ Subgroup.closure (autOf '' {x | x ∈ Ry}) :=
        (hRyI _ (w183finSp44pv_valid_conjE hr (hvalRy s hs))).mpr (h s hs)
      rw [autOf_conjE hr (hvalRy s hs), ← MulAut.conj_apply] at hmem
      exact hmem
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj (autOf r)).injective])

theorem w183finSp44pv_card_inf_normalizer {gens R Ry : List El}
    (hnodup : R.Nodup) (hRval : ∀ r ∈ R, validB r = true)
    (hAiff : ∀ α, α ∈ Subgroup.closure (autOf '' {x | x ∈ gens}) ↔
      ∃ r ∈ R, autOf r = α)
    (hRyI : ∀ z, validB z = true → (autOf z ∈ Subgroup.closure (autOf '' {x | x ∈ Ry}) ↔ z ∈ Ry))
    (hvalRy : ∀ s ∈ Ry, validB s = true) :
    Nat.card ↥(Subgroup.closure (autOf '' {x | x ∈ gens}) ⊓
        Subgroup.normalizer (Subgroup.closure (autOf '' {x | x ∈ Ry}) : Set (MulAut S4))) =
      (R.filter (fun r => Ry.all fun s => memK Ry (conjE r s))).length := by
  let A := Subgroup.closure (autOf '' {x | x ∈ gens})
  let H := Subgroup.normalizer (Subgroup.closure (autOf '' {x | x ∈ Ry}) : Set (MulAut S4))
  let P : El → Bool := fun r => Ry.all fun s => memK Ry (conjE r s)
  let Rf := R.filter P
  have hfilter : ∀ r, r ∈ Rf ↔ r ∈ R ∧ ∀ s ∈ Ry, conjE r s ∈ Ry := by
    intro r
    dsimp only [Rf, P]
    rw [List.mem_filter]
    constructor
    · rintro ⟨hr, hPr⟩
      exact ⟨hr, fun s hs => w183finSp44pv_memK_sound ((List.all_eq_true.mp hPr) s hs)⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, List.all_eq_true.mpr fun s hs => by
        rw [memK]; exact List.any_eq_true.mpr ⟨conjE r s, h s hs, by simp⟩⟩
  have hN : ∀ r ∈ R, autOf r ∈ H ↔ ∀ s ∈ Ry, conjE r s ∈ Ry :=
    fun r hr => w183finSp44pv_mem_normalizer_iff hvalRy (hRval r hr) hRyI
  have hset : (↑(A ⊓ H) : Set (MulAut S4)) = autOf '' {r | r ∈ Rf} := by
    ext α
    constructor
    · rintro ⟨hA, hNorm⟩
      obtain ⟨r, hr, rfl⟩ := (hAiff α).mp hA
      exact ⟨r, (hfilter r).mpr ⟨hr, (hN r hr).mp hNorm⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hrR, hP⟩ := (hfilter r).mp hr
      exact ⟨(hAiff (autOf r)).mpr ⟨r, hrR, rfl⟩, (hN r hrR).mpr hP⟩
  have hnodupf : Rf.Nodup := hnodup.filter P
  let f : ↥Rf.toFinset → ↥(A ⊓ H) := fun x =>
    ⟨autOf x.1, by
      have hx := List.mem_toFinset.mp x.2
      obtain ⟨hrR, hP⟩ := (hfilter x.1).mp hx
      exact ⟨(hAiff (autOf x.1)).mpr ⟨x.1, hrR, rfl⟩, (hN x.1 hrR).mpr hP⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply autOf_inj (hRval x.1 ((hfilter x.1).mp (List.mem_toFinset.mp x.2)).1)
        (hRval y.1 ((hfilter y.1).mp (List.mem_toFinset.mp y.2)).1)
      exact congrArg Subtype.val hxy
    · intro α
      have hα : (α : MulAut S4) ∈ autOf '' {r | r ∈ Rf} := by
        rw [← hset]; exact α.2
      obtain ⟨r, hr, hrα⟩ := hα
      exact ⟨⟨r, List.mem_toFinset.mpr hr⟩, Subtype.ext hrα⟩
  have hcard : Nat.card ↥(A ⊓ H) = Nat.card ↥Rf.toFinset :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [show (Subgroup.closure (autOf '' {x | x ∈ gens}) ⊓
      Subgroup.normalizer (Subgroup.closure (autOf '' {x | x ∈ Ry}) : Set (MulAut S4))) = A ⊓ H
      from rfl]
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodupf]

theorem w183finSp44pv_card_of_iff {A : Subgroup (MulAut S4)} {R : List El}
    (hRnodup : R.Nodup) (hRval : ∀ r ∈ R, validB r = true)
    (hAiff : ∀ α, α ∈ A ↔ ∃ r ∈ R, autOf r = α) : Nat.card A = R.length := by
  let f : ↥R.toFinset → A := fun x =>
    ⟨autOf x.1, (hAiff _).mpr ⟨x.1, List.mem_toFinset.mp x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply autOf_inj (hRval x.1 (List.mem_toFinset.mp x.2))
        (hRval y.1 (List.mem_toFinset.mp y.2))
      exact congrArg Subtype.val hxy
    · intro α
      obtain ⟨r, hr, hre⟩ := (hAiff _).mp α.2
      exact ⟨⟨r, List.mem_toFinset.mpr hr⟩, Subtype.ext hre⟩
  have hcard : Nat.card A = Nat.card ↥R.toFinset :=
    (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [hcard, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hRnodup]

theorem w183finSp44pv_card_subgroupOf {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
