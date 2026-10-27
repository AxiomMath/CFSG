module

public import CFSG.Sporadic.Fi22.LH.Root
public import CFSG.Sporadic.Fi22.LH.Orbit

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.F3.Native Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem lh_count63 :
    count63OK tT lhc.B[0]! = true := lh_parts.2.2.2.2.2.2.2.2.2.2.1

theorem lh_row :
    rowOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.rowInv = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lh_phi : phiOK tT lhc.B[0]! lhc.orb[0]! lhc.phi = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lh_far :
    farOK lhc.rowInv lhc.phi lhc.v0 lhc.farTree = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lh_mu :
    muOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.muW lhc.mOrd lhc.mPar lhc.mWit lhc.v0 = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem lh_ed :
    edOK tT lhc.B[0]! lhc.orb[0]! lhc.rowR lhc.rowInv lhc.muW lhc.edW lhc.edF lhc.edK
      lhc.v0 = true :=
  lh_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem permTreeOK_spec {n r : ℕ} {T : Tree} {letters : Array Table} {lv : Array ℕ}
    (h : Perm.Native.treeOK n r T letters lv = true) :
    0 < T.pts.size ∧ ap T.pts 0 = r ∧ ∀ k < T.pts.size, ap T.pts k < n ∧
      (0 < k → ap T.par k < k ∧ ap T.lab k ∈ lv ∧
        ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) = ap T.pts k) := by
  simp only [Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  refine ⟨hm, h0, fun k hk => ?_⟩
  have := (allIn_eq_true.1 hall) k (Nat.zero_le _) hk
  simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Array.all_eq_true,
    Bool.or_eq_true, Array.contains_iff_mem] at this
  obtain ⟨⟨⟨hlt, -⟩, -⟩, hpar⟩ := this
  refine ⟨hlt, fun hk0 => ?_⟩
  rcases hpar with h | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, h3⟩

theorem conjPerm_tv (g : J) (f y : D) :
    Pair.conjPerm pair_D g ((pairModel pair_D).tv f y) =
      (pairModel pair_D).tv (Pair.conjPerm pair_D g f) (Pair.conjPerm pair_D g y) :=
  Pair.conjPerm_tauE pair_D g f y

theorem conjPerm_image_tv (g : J) (f : D) (U : Set D) :
    ⇑(Pair.conjPerm pair_D g) '' ((pairModel pair_D).tv f '' U) =
      (pairModel pair_D).tv (Pair.conjPerm pair_D g f) '' (⇑(Pair.conjPerm pair_D g) '' U) := by
  rw [Set.image_image, Set.image_image]
  simp only [conjPerm_tv]

theorem tv_image_conjPerm (g : J) (f : D) (U : Set D) :
    (pairModel pair_D).tv f '' (⇑(Pair.conjPerm pair_D g) '' U) =
      ⇑(Pair.conjPerm pair_D g) '' ((pairModel pair_D).tv ((Pair.conjPerm pair_D g).symm f) '' U) :=
  by rw [conjPerm_image_tv, Equiv.apply_symm_apply]

theorem conjPerm_commute_iff (g : J) (x y : D) :
    ((Pair.conjPerm pair_D g x : D) : J) * Pair.conjPerm pair_D g y =
      Pair.conjPerm pair_D g y * Pair.conjPerm pair_D g x ↔ (x : J) * y = y * x := by
  rw [Pair.conjPerm_apply, Pair.conjPerm_apply, conj_commute_iff]

theorem notMem_conjPerm_image {g : J} {f : D} {U : Set D}
    (hf : f ∉ ⇑(Pair.conjPerm pair_D g) '' U) :
    (Pair.conjPerm pair_D g).symm f ∉ U :=
  fun hm => hf ⟨_, hm, Equiv.apply_symm_apply _ f⟩

theorem ptD_mem_lhRoot_zero
    {x : Fin 3510} : ptD x ∈ lhRoot 0 ↔ bitAt lhc.B[0]! x.val = true := by
  rw [ptD_mem_lhRoot]
  simp

theorem bitAt_B0_of_notMem
    {k : Fin 3510} (h : ptD k ∉ lhRoot 0) :
    bitAt lhc.B[0]! k.val = false := by
  rw [ptD_mem_lhRoot_zero] at h
  simpa using h

theorem tv_image_lhRoot
    {k : ℕ} (hk : k < 3510) (hkB : bitAt lhc.B[0]! k = false) :
    (pairModel pair_D).tv (ptD ⟨k, hk⟩) '' lhRoot 0 = lhMem 0 lhc.rowR[k]! := by
  obtain ⟨-, -, h, -⟩ := rowOK_spec lh_row
  rw [tv_eq_conjPerm, lhRoot_eq, ptD_val']
  exact conjPerm_image_dset (rep_tT hk) (h k hk hkB).2.2.1

theorem injOn_tv_image_root :
    Set.InjOn (fun f => (pairModel pair_D).tv f '' lhRoot 0) (lhRoot 0)ᶜ := by
  intro f₁ hf₁ f₂ hf₂ h
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  obtain ⟨k₁, rfl⟩ := ptD.surjective f₁
  obtain ⟨k₂, rfl⟩ := ptD.surjective f₂
  have hB₁ := bitAt_B0_of_notMem hf₁
  have hB₂ := bitAt_B0_of_notMem hf₂
  simp only at h
  rw [tv_image_lhRoot k₁.2 hB₁, tv_image_lhRoot k₂.2 hB₂] at h
  have e := lhMem_inj (i := 0) (by norm_num) (hrow _ k₁.2 hB₁).1 (hrow _ k₂.2 hB₂).1 h
  have e1 := (hrow _ k₁.2 hB₁).2.2.2
  have e2 := (hrow _ k₂.2 hB₂).2.2.2
  rw [e] at e1
  exact congrArg ptD (Fin.ext (e1.symm.trans e2))

theorem tv_image_ne_root
    {f : D} (hf : f ∉ lhRoot 0) :
    (pairModel pair_D).tv f '' lhRoot 0 ≠ lhRoot 0 := by
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  obtain ⟨k, rfl⟩ := ptD.surjective f
  have hB := bitAt_B0_of_notMem hf
  rw [tv_image_lhRoot k.2 hB]
  intro h
  have h' : lhMem 0 lhc.rowR[k.val]! = lhMem 0 0 := h.trans (lhRoot_eq_lhMem 0)
  exact (hrow _ k.2 hB).2.1 (lhMem_inj (i := 0) (by norm_num) (hrow _ k.2 hB).1 (by norm_num) h')

theorem injOn_tv_image
    {T : Set D} (hT : T ∈ lhOrbit 0) :
    Set.InjOn (fun f => (pairModel pair_D).tv f '' T) Tᶜ := by
  obtain ⟨g, rfl⟩ := hT
  intro f₁ hf₁ f₂ hf₂ h
  simp only [tv_image_conjPerm] at h
  have h' := Set.image_injective.2 (Pair.conjPerm pair_D g).injective h
  exact (Pair.conjPerm pair_D g).symm.injective
    (injOn_tv_image_root (notMem_conjPerm_image hf₁) (notMem_conjPerm_image hf₂) h')

theorem tv_image_ne
    {T : Set D} (hT : T ∈ lhOrbit 0) {f : D} (hf : f ∉ T) :
    (pairModel pair_D).tv f '' T ≠ T := by
  obtain ⟨g, rfl⟩ := hT
  rw [tv_image_conjPerm]
  intro h
  exact tv_image_ne_root (notMem_conjPerm_image hf)
    (Set.image_injective.2 (Pair.conjPerm pair_D g).injective h)

theorem exists_not_commute
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) {f : D} (hf : f ∉ T) :
    ∃ x ∈ T, ¬ ((f : J) * x = x * f) := by
  obtain ⟨g, rfl⟩ := hT
  have hf' := notMem_conjPerm_image hf
  obtain ⟨k, hk⟩ := ptD.surjective ((Pair.conjPerm pair_D g).symm f)
  rw [← hk] at hf'
  have hkB : bitAt lhc.B[i.val]! k.val = false := by
    rw [ptD_mem_lhRoot] at hf'
    simpa using hf'
  obtain ⟨-, x, hx, hxB, hxc⟩ := domOK_spec (lh_parts.2.2.2.2.2.2.2.2.2.1 i.val i.2).2.2.2.2.2.1
    k.2 hkB
  refine ⟨Pair.conjPerm pair_D g (ptD ⟨x, hx⟩), ⟨ptD ⟨x, hx⟩, ptD_mem_lhRoot.2 hxB, rfl⟩,
    fun hc => hxc ?_⟩
  have hfk : f = Pair.conjPerm pair_D g (ptD k) := by
    rw [hk, Equiv.apply_symm_apply]
  rw [hfk, conjPerm_commute_iff] at hc
  exact (ptD_commute_iff k ⟨x, hx⟩).1 hc

noncomputable abbrev xi23 :
    SimpleGraph (lhOrbit 0) := (pairModel pair_D).xi (lhOrbit 0)

@[expose] noncomputable def xi23Vert
    (k : ℕ) : lhOrbit 0 :=
  ⟨lhMem 0 (k % 14080), lhMem_mem_lhOrbit 0 (Nat.mod_lt _ (by norm_num))⟩

theorem xi23Vert_val
    {k : ℕ} (hk : k < 14080) : (xi23Vert k : Set D) = lhMem 0 k := by
  show lhMem 0 (k % 14080) = lhMem 0 k
  rw [Nat.mod_eq_of_lt hk]

theorem xi23Vert_zero :
    xi23Vert 0 = xi23Root := by
  apply Subtype.ext
  rw [xi23Vert_val (by norm_num)]
  exact (lhRoot_eq_lhMem 0).symm

theorem xi23Vert_inj
    {k m : ℕ} (hk : k < 14080) (hm : m < 14080) (h : xi23Vert k = xi23Vert m) :
    k = m := by
  have := congrArg Subtype.val h
  rw [xi23Vert_val hk, xi23Vert_val hm] at this
  exact lhMem_inj (i := 0) (by norm_num) hk hm this

theorem exists_xi23Vert
    (V : lhOrbit 0) : ∃ k < 14080, V = xi23Vert k := by
  obtain ⟨k, hk, hV⟩ := mem_lhOrbit_iff.1 V.2
  exact ⟨k, hk, Subtype.ext (by rw [xi23Vert_val hk]; exact hV)⟩

theorem xi23_adj {U V : lhOrbit 0} :
    xi23.Adj U V ↔ U ≠ V ∧ ∃ f, f ∉ (U : Set D) ∧ (pairModel pair_D).tv f '' (U : Set D) = V :=
  Iff.rfl

theorem xi23_adj_of_wit
    {m m' h : ℕ} (hm : m < 14080) (hm' : m' < 14080) (hh : h < 3510)
    (hnot : bitAt lhc.orb[0]!.sets[m]! h = false)
    (hmap : mapsOnto tT[h]! lhc.orb[0]!.sets[m]! lhc.orb[0]!.sets[m']! = true) :
    xi23.Adj (xi23Vert m) (xi23Vert m') := by
  have hf : ptD ⟨h, hh⟩ ∉ lhMem 0 m := by
    rw [lhMem, ptD_mem_dset, Fin.val_mk, hnot]
    exact Bool.false_ne_true
  have himg : (pairModel pair_D).tv (ptD ⟨h, hh⟩) '' lhMem 0 m = lhMem 0 m' := by
    rw [tv_eq_conjPerm, ptD_val']
    exact conjPerm_image_dset (rep_tT hh) hmap
  refine ⟨fun e => ?_, ptD ⟨h, hh⟩, by rw [xi23Vert_val hm]; exact hf, by
    rw [xi23Vert_val hm, xi23Vert_val hm', himg]⟩
  have e' := congrArg Subtype.val e
  rw [xi23Vert_val hm, xi23Vert_val hm'] at e'
  exact tv_image_ne (lhMem_mem_lhOrbit 0 hm) hf (himg.trans e'.symm)

theorem xi23_adj_root_iff
    {V : lhOrbit 0} :
    xi23.Adj xi23Root V ↔ ∃ k < 3510, bitAt lhc.B[0]! k = false ∧ V = xi23Vert lhc.rowR[k]! := by
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  constructor
  · rintro ⟨-, f, hf, hfV⟩
    obtain ⟨k, rfl⟩ := ptD.surjective f
    have hB := bitAt_B0_of_notMem hf
    refine ⟨_, k.2, hB, Subtype.ext ?_⟩
    rw [xi23Vert_val (hrow _ k.2 hB).1, ← hfV]
    exact tv_image_lhRoot k.2 hB
  · rintro ⟨k, hk, hkB, rfl⟩
    obtain ⟨h1, h2, -, -⟩ := hrow k hk hkB
    refine ⟨fun e => h2 ?_, ptD ⟨k, hk⟩, ?_, ?_⟩
    · rw [← xi23Vert_zero] at e
      exact (xi23Vert_inj (by norm_num) h1 e).symm
    · show ptD ⟨k, hk⟩ ∉ lhRoot 0
      rw [ptD_mem_lhRoot_zero, Fin.val_mk]
      exact fun h => Bool.false_ne_true (hkB.symm.trans h)
    · show _ = (xi23Vert lhc.rowR[k]! : Set D)
      rw [xi23Vert_val h1]
      exact tv_image_lhRoot hk hkB

theorem far_iff
    {V : lhOrbit 0} : (V ≠ xi23Root ∧ ¬ xi23.Adj xi23Root V) ↔
    ∃ m < 14080, isFar lhc.rowInv m = true ∧ V = xi23Vert m := by
  obtain ⟨-, hsz, hrow, hinv⟩ := rowOK_spec lh_row
  constructor
  · rintro ⟨hne, hadj⟩
    obtain ⟨m, hm, rfl⟩ := exists_xi23Vert V
    refine ⟨m, hm, ?_, rfl⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hne xi23Vert_zero
    rcases hinv m hm with h | ⟨h1, h2, h3⟩
    · simp [isFar, hm0, h]
    · exact absurd (xi23_adj_root_iff.2 ⟨_, h1, h2, by rw [h3]⟩) hadj
  · rintro ⟨m, hm, hfar, rfl⟩
    simp only [isFar, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hfar
    refine ⟨fun e => hfar.1 ?_, fun hadj => ?_⟩
    · rw [← xi23Vert_zero] at e
      exact xi23Vert_inj hm (by norm_num) e
    · obtain ⟨k, hk, hkB, e⟩ := xi23_adj_root_iff.1 hadj
      have := xi23Vert_inj hm (hrow k hk hkB).1 e
      have h4 := (hrow k hk hkB).2.2.2
      rw [← this, hfar.2] at h4
      omega

theorem ncard_bset_inter (A B : Bits) : (bset A ∩ bset B).ncard = commonCount A B := by
  unfold commonCount
  rw [← ncard_fin_eq_countP]
  congr 1
  ext x
  simp [bset]

theorem tv_mem_of_mem_lhOrbit
    {i : Fin 2} {T : Set D} (hT : T ∈ lhOrbit i) {s t : D} (hs : s ∈ T)
    (ht : t ∈ T) : (pairModel pair_D).tv s t ∈ T := by
  obtain ⟨g, rfl⟩ := hT
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨t', ht', rfl⟩ := ht
  rw [← conjPerm_tv]
  refine ⟨_, ?_, rfl⟩
  have h := lhRoot_closed i ⟨s', hs', rfl⟩ ⟨t', ht', rfl⟩
  obtain ⟨y, hy, hyv⟩ := h
  have : y = (pairModel pair_D).tv s' t' := Subtype.ext (by rw [hyv, pairModel_tv])
  rwa [← this]

theorem inter_tv_image
    {i : Fin 2} {U : Set D} (hU : U ∈ lhOrbit i) {f : D} (hf : f ∉ U) :
    U ∩ (pairModel pair_D).tv f '' U = {x | x ∈ U ∧ (x : J) * f = f * x} := by
  ext z
  constructor
  · rintro ⟨hzU, z', hz'U, rfl⟩
    by_cases hc : (z' : J) * f = f * z'
    · have : (pairModel pair_D).tv f z' = z' := Subtype.ext (by
        rw [pairModel_tv]
        exact (Pair.mul_mul_eq_self_iff pair_D f.2 z').2 hc.symm)
      rw [this]
      exact ⟨hz'U, hc⟩
    · exfalso
      apply hf
      have h1 := tv_mem_of_mem_lhOrbit hU hz'U hzU
      have : (pairModel pair_D).tv z' ((pairModel pair_D).tv f z') = f := by
        apply Subtype.ext
        rw [pairModel_tv, pairModel_tv]
        have e := Pair.mul_mul_eq pair_D f.2 z'.2 (fun h => hc h.symm)
        rw [e]
        calc (z' : J) * (z' * f * z') * z' = (z' * z') * f * (z' * z') := by group
          _ = f := by rw [Pair.mul_self pair_D z'.2, one_mul, mul_one]
      rwa [this] at h1
  · rintro ⟨hzU, hc⟩
    refine ⟨hzU, z, hzU, Subtype.ext ?_⟩
    rw [pairModel_tv]
    exact (Pair.mul_mul_eq_self_iff pair_D f.2 z).2 hc.symm

theorem ncard_inter_of_tv
    {U : Set D} (hU : U ∈ lhOrbit 0) {f : D} (hf : f ∉ U) :
    (U ∩ (pairModel pair_D).tv f '' U).ncard = 63 := by
  rw [inter_tv_image hU hf]
  obtain ⟨g, rfl⟩ := hU
  have hf' := notMem_conjPerm_image hf
  obtain ⟨k, hk⟩ := ptD.surjective ((Pair.conjPerm pair_D g).symm f)
  have hfk : f = Pair.conjPerm pair_D g (ptD k) := by rw [hk, Equiv.apply_symm_apply]
  rw [← hk] at hf'
  have hkB : bitAt lhc.B[0]! k.val = false := bitAt_B0_of_notMem hf'
  have e : {x | x ∈ ⇑(Pair.conjPerm pair_D g) '' lhRoot 0 ∧ (x : J) * f = f * x} =
      ⇑(Pair.conjPerm pair_D g) '' (ptD '' {x : Fin 3510 |
        (bitAt lhc.B[0]! x.val && ap tT[k.val]! x.val == x.val) = true}) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hc⟩
      obtain ⟨j, rfl⟩ := ptD.surjective y
      refine ⟨ptD j, ⟨j, ?_, rfl⟩, rfl⟩
      rw [hfk, conjPerm_commute_iff] at hc
      have h1 := (ptD_commute_iff k j).1 hc.symm
      have hy' : bitAt lhc.B[0]! j.val = true := ptD_mem_lhRoot_zero.1 hy
      simp [hy', h1]
    · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
      simp only [Set.mem_ofPred_eq, Bool.and_eq_true, beq_iff_eq] at hx'
      refine ⟨⟨ptD x', ptD_mem_lhRoot_zero.2 hx'.1, rfl⟩, ?_⟩
      rw [hfk, conjPerm_commute_iff]
      exact ((ptD_commute_iff k x').2 hx'.2).symm
  rw [e, Set.ncard_image_of_injective _ (Pair.conjPerm pair_D g).injective,
    Set.ncard_image_of_injective _ ptD.injective,
    ncard_fin_eq_countP 3510 (fun x => bitAt lhc.B[0]! x && ap tT[k.val]! x == x)]
  exact count63OK_spec lh_count63 k.2 hkB

theorem commonCount_of_adj
    {m m' : ℕ} (hm : m < 14080) (hm' : m' < 14080)
    (h : xi23.Adj (xi23Vert m) (xi23Vert m')) :
    commonCount lhc.orb[0]!.sets[m]! lhc.orb[0]!.sets[m']! = 63 := by
  obtain ⟨-, f, hf, hfV⟩ := h
  rw [xi23Vert_val hm] at hf hfV
  rw [xi23Vert_val hm'] at hfV
  rw [← ncard_bset_inter, ← ncard_inter_of_tv (U := lhMem 0 m) (lhMem_mem_lhOrbit 0 hm) hf, hfV,
    lhMem, lhMem, dset, dset, ← Set.image_inter ptD.injective,
    Set.ncard_image_of_injective _ ptD.injective]

theorem conjPerm_image_image (g h : J) (S : Set D) :
    ⇑(Pair.conjPerm pair_D g) '' (⇑(Pair.conjPerm pair_D h) '' S) =
      ⇑(Pair.conjPerm pair_D (g * h)) '' S := by
  rw [← Set.image_comp, ← Equiv.Perm.coe_mul, ← map_mul]

@[expose] noncomputable def xiConj
    (g : J) : Equiv.Perm (lhOrbit 0) where
  toFun V := ⟨⇑(Pair.conjPerm pair_D g) '' V, conjPerm_mem_lhOrbit V.2 g⟩
  invFun V := ⟨⇑(Pair.conjPerm pair_D g⁻¹) '' V, conjPerm_mem_lhOrbit V.2 g⁻¹⟩
  left_inv V := Subtype.ext (by
    dsimp only
    rw [conjPerm_image_image, inv_mul_cancel, map_one, Equiv.Perm.coe_one, Set.image_id])
  right_inv V := Subtype.ext (by
    dsimp only
    rw [conjPerm_image_image, mul_inv_cancel, map_one, Equiv.Perm.coe_one, Set.image_id])

theorem xiConj_val (g : J) (V : lhOrbit 0) :
    (xiConj g V : Set D) = ⇑(Pair.conjPerm pair_D g) '' V := rfl

theorem xi23_adj_xiConj (g : J) {U V : lhOrbit 0} :
    xi23.Adj (xiConj g U) (xiConj g V) ↔ xi23.Adj U V := by
  rw [xi23_adj, xi23_adj, (xiConj g).injective.ne_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨f, hf, hfV⟩
    rw [xiConj_val] at hf
    rw [xiConj_val, xiConj_val, tv_image_conjPerm] at hfV
    exact ⟨(Pair.conjPerm pair_D g).symm f, notMem_conjPerm_image hf,
      Set.image_injective.2 (Pair.conjPerm pair_D g).injective hfV⟩
  · rintro ⟨f, hf, hfV⟩
    refine ⟨Pair.conjPerm pair_D g f, ?_, ?_⟩
    · rw [xiConj_val]
      rintro ⟨y, hy, hyf⟩
      rw [(Pair.conjPerm pair_D g).injective hyf] at hy
      exact hf hy
    · rw [xiConj_val, xiConj_val, ← conjPerm_image_tv, hfV]

@[expose] noncomputable def xiIso (g : J) : xi23 ≃g xi23 :=
  ⟨xiConj g, xi23_adj_xiConj g⟩

theorem xiIso_apply
    (g : J) (V : lhOrbit 0) : xiIso g V = xiConj g V := rfl

theorem xiConj_root
    {c : ℕ} (hc : c < 3510) (hcB : bitAt lhc.B[0]! c = true) :
    xiConj (conjPt c) xi23Root = xi23Root := by
  apply Subtype.ext
  rw [xiConj_val]
  show ⇑(Pair.conjPerm pair_D (conjPt c)) '' lhRoot 0 = lhRoot 0
  have hs : conjPt c ∈ Subtype.val '' lhRoot 0 := (conjPt_mem_lhRoot hc).2 hcB
  have h := conj_image_lhRoot 0 hs
  rw [← val_image_conjPerm] at h
  exact Set.image_injective.2 Subtype.val_injective h

theorem xiConj_xi23Vert
    {l m : ℕ} (hl : l < xiGens.size) (hm : m < 14080) :
    xiConj (conjPt xiGens[l]!) (xi23Vert m) = xi23Vert (ap lhc.phi[l]! m) := by
  obtain ⟨-, h⟩ := phiOK_spec lh_phi
  obtain ⟨hg, -, -, hphi⟩ := h l hl
  apply Subtype.ext
  rw [xiConj_val, xi23Vert_val hm, xi23Vert_val (hphi m hm).1]
  exact conjPerm_image_dset (rep_tT hg) (hphi m hm).2

@[expose] def MUat (v : lhOrbit 0) : Prop :=
  (xi23.induce {x | xi23.Adj xi23Root x ∧ xi23.Adj x v}).Connected

@[expose] def EDat (v : lhOrbit 0) : Prop :=
  ∀ w, w ≠ xi23Root → ¬ xi23.Adj xi23Root w → xi23.Adj v w →
    ∃ x, xi23.Adj xi23Root x ∧ xi23.Adj x v ∧ xi23.Adj x w

theorem MUat_iso
    (φ : xi23 ≃g xi23) (hφ : φ xi23Root = xi23Root) {v : lhOrbit 0}
    (h : MUat v) : MUat (φ v) := by
  have hS : ∀ x, (xi23.Adj xi23Root x ∧ xi23.Adj x v) ↔
      (xi23.Adj xi23Root (φ x) ∧ xi23.Adj (φ x) (φ v)) := by
    intro x
    have e1 : xi23.Adj xi23Root (φ x) ↔ xi23.Adj xi23Root x := by
      conv_lhs => rw [← hφ]
      exact φ.map_adj_iff
    rw [e1, φ.map_adj_iff]
  let e : {x | xi23.Adj xi23Root x ∧ xi23.Adj x v} ≃ {x | xi23.Adj xi23Root x ∧ xi23.Adj x (φ v)} :=
    φ.toEquiv.subtypeEquiv fun x => hS x
  let iso : xi23.induce {x | xi23.Adj xi23Root x ∧ xi23.Adj x v} ≃g
      xi23.induce {x | xi23.Adj xi23Root x ∧ xi23.Adj x (φ v)} :=
    { toEquiv := e
      map_rel_iff' := fun {a b} => by
        show xi23.Adj (φ a.1) (φ b.1) ↔ xi23.Adj a.1 b.1
        exact φ.map_adj_iff }
  exact iso.connected_iff.1 h

theorem EDat_iso
    (φ : xi23 ≃g xi23) (hφ : φ xi23Root = xi23Root) {v : lhOrbit 0}
    (h : EDat v) : EDat (φ v) := by
  intro w hw hrw hvw
  have hw' : φ (φ.symm w) = w := φ.apply_symm_apply w
  obtain ⟨x, h1, h2, h3⟩ := h (φ.symm w)
    (fun e => hw (by rw [← hw', e, hφ]))
    (fun e => hrw (by rw [← hw', ← hφ]; exact φ.map_adj_iff.2 e))
    (φ.map_adj_iff.1 (by rw [hw']; exact hvw))
  refine ⟨φ x, ?_, φ.map_adj_iff.2 h2, ?_⟩
  · rw [← hφ]
    exact φ.map_adj_iff.2 h1
  · rw [← hw']
    exact φ.map_adj_iff.2 h3

theorem mu_mem
    {k : ℕ} (hk : k < lhc.mOrd.size) :
    xi23.Adj xi23Root (xi23Vert lhc.rowR[lhc.mOrd[k]!]!) ∧
      xi23.Adj (xi23Vert lhc.rowR[lhc.mOrd[k]!]!) (xi23Vert lhc.v0) := by
  obtain ⟨-, hw, -, -, -, -, hord, -, -⟩ := muOK_spec lh_mu
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  obtain ⟨hf, hfB, hmu⟩ := hord k hk
  obtain ⟨hv0, -⟩ := farOK_spec lh_far
  obtain ⟨hnot, hmap⟩ := hw _ hf hfB hmu
  exact ⟨xi23_adj_root_iff.2 ⟨_, hf, hfB, rfl⟩,
    xi23_adj_of_wit (hrow _ hf hfB).1 hv0 hmu hnot hmap⟩

theorem MUat_v0 :
    MUat (xi23Vert lhc.v0) := by
  obtain ⟨-, -, hne, hpos, -, -, hord, htree, hcov⟩ := muOK_spec lh_mu
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  obtain ⟨hv0, -⟩ := farOK_spec lh_far
  unfold MUat
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hmem : ∀ k (hk : k < lhc.mOrd.size), xi23Vert lhc.rowR[lhc.mOrd[k]!]! ∈
      {x | xi23.Adj xi23Root x ∧ xi23.Adj x (xi23Vert lhc.v0)} := fun k hk => mu_mem hk
  have hreach : ∀ k (hk : k < lhc.mOrd.size),
      (xi23.induce {x | xi23.Adj xi23Root x ∧ xi23.Adj x (xi23Vert lhc.v0)}).Reachable
        ⟨_, hmem 0 hpos⟩ ⟨_, hmem k hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rfl
      · obtain ⟨hp, hwl, hnot, hmap⟩ := htree k hk0 hk
        have hpk : lhc.mPar[k]! < lhc.mOrd.size := by omega
        refine (ih _ hp hpk).trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.induce_adj]
        obtain ⟨hf1, hfB1, -⟩ := hord _ hpk
        obtain ⟨hf2, hfB2, -⟩ := hord k hk
        exact xi23_adj_of_wit (hrow _ hf1 hfB1).1 (hrow _ hf2 hfB2).1 hwl hnot hmap
  refine ⟨⟨_, hmem 0 hpos⟩, fun x => ?_⟩
  obtain ⟨V, h1, h2⟩ := x
  obtain ⟨f, hf, hfB, rfl⟩ := xi23_adj_root_iff.1 h1
  have hm := (hrow f hf hfB).1
  have hmu : lhc.muW[f]! < 3510 := by
    by_contra hlt
    exact hne f hf hfB hlt (commonCount_of_adj hm hv0 h2)
  obtain ⟨k, hk, hkf⟩ := Array.mem_iff_getElem.1 (hcov f hf hfB (by omega))
  have e : (⟨xi23Vert lhc.rowR[f]!, h1, h2⟩ :
      {x | xi23.Adj xi23Root x ∧ xi23.Adj x (xi23Vert lhc.v0)}) =
      ⟨_, hmem k hk⟩ := by
    apply Subtype.ext
    show xi23Vert lhc.rowR[f]! = xi23Vert lhc.rowR[lhc.mOrd[k]!]!
    rw [getElem!_pos lhc.mOrd k hk, hkf]
  rw [e]
  exact hreach k hk

theorem EDat_v0 :
    EDat (xi23Vert lhc.v0) := by
  obtain ⟨hv0, -⟩ := farOK_spec lh_far
  obtain ⟨-, hw, -, -, -, -, -, -, -⟩ := muOK_spec lh_mu
  obtain ⟨-, -, hrow, -⟩ := rowOK_spec lh_row
  intro w hw0 hrw hvw
  obtain ⟨-, f, hf, hfw⟩ := hvw
  obtain ⟨h, rfl⟩ := ptD.surjective f
  rw [xi23Vert_val hv0] at hf hfw
  have hfV : bitAt lhc.orb[0]!.sets[lhc.v0]! h.val = false := by
    rw [lhMem, ptD_mem_dset] at hf
    simpa using hf
  obtain ⟨he1, he2, he3⟩ := edOK_spec lh_ed h.2 hfV
  have hwv : w = xi23Vert lhc.edW[h.val]! := by
    apply Subtype.ext
    rw [xi23Vert_val he1, ← hfw, tv_eq_conjPerm, ptD_val', lhMem, lhMem]
    exact conjPerm_image_dset (rep_tT h.2) he2
  obtain ⟨m, hm, hfar, hwm⟩ := far_iff.1 ⟨hw0, hrw⟩
  rw [hwv] at hwm
  have := xi23Vert_inj he1 hm hwm
  rw [← this] at hfar
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := he3 hfar
  obtain ⟨hnot, hmap⟩ := hw _ g1 g2 g3
  refine ⟨xi23Vert lhc.rowR[lhc.edF[h.val]!]!, xi23_adj_root_iff.2 ⟨_, g1, g2, rfl⟩,
    xi23_adj_of_wit (hrow _ g1 g2).1 hv0 g3 hnot hmap, ?_⟩
  rw [hwv]
  exact xi23_adj_of_wit (hrow _ g1 g2).1 he1 g4 g5 g6

theorem far_facts :
    ∀ k < lhc.farTree.pts.size,
    MUat (xi23Vert (ap lhc.farTree.pts k)) ∧ EDat (xi23Vert (ap lhc.farTree.pts k)) := by
  obtain ⟨hv0, -, htree, -⟩ := farOK_spec lh_far
  obtain ⟨-, h0, hall⟩ := permTreeOK_spec htree
  obtain ⟨-, hphi⟩ := phiOK_spec lh_phi
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0]
      exact ⟨MUat_v0, EDat_v0⟩
    · obtain ⟨hp, hl, he⟩ := (hall k hk).2 hk0
      rw [Array.mem_range] at hl
      have hpk : ap lhc.farTree.par k < lhc.farTree.pts.size := by omega
      obtain ⟨hmu, hed⟩ := ih _ hp hpk
      have hpm := (hall _ hpk).1
      obtain ⟨hg, hgB, -, -⟩ := hphi _ hl
      have e : xi23Vert (ap lhc.farTree.pts k) = xiIso (conjPt xiGens[ap lhc.farTree.lab k]!)
          (xi23Vert (ap lhc.farTree.pts (ap lhc.farTree.par k))) := by
        rw [xiIso_apply, xiConj_xi23Vert hl hpm, he]
      rw [e]
      exact ⟨MUat_iso _ (xiConj_root hg hgB) hmu, EDat_iso _ (xiConj_root hg hgB) hed⟩

theorem far_MU_ED
    {v : lhOrbit 0} (h0 : v ≠ xi23Root) (h1 : ¬ xi23.Adj xi23Root v) :
    MUat v ∧ EDat v := by
  obtain ⟨m, hm, hfar, rfl⟩ := far_iff.1 ⟨h0, h1⟩
  obtain ⟨-, -, -, hcov⟩ := farOK_spec lh_far
  obtain ⟨hpos, hpts⟩ := hcov m hm hfar
  have := far_facts _ hpos
  rwa [hpts] at this

theorem xi23_MU :
    ∀ v, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    (((pairModel pair_D).xi (lhOrbit 0)).induce
      {x | ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root x ∧
        ((pairModel pair_D).xi (lhOrbit 0)).Adj x v}).Connected :=
  fun _ h0 h1 => (far_MU_ED h0 h1).1

theorem xi23_D2 :
    ∀ v, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    ∃ x, ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root x ∧
      ((pairModel pair_D).xi (lhOrbit 0)).Adj x v := by
  intro v h0 h1
  have := (far_MU_ED h0 h1).1.nonempty
  obtain ⟨⟨x, hx⟩⟩ := this
  exact ⟨x, hx⟩

theorem xi23_ED :
    ∀ v w, v ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root v →
    w ≠ xi23Root → ¬ ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root w →
    ((pairModel pair_D).xi (lhOrbit 0)).Adj v w →
    ∃ x, ((pairModel pair_D).xi (lhOrbit 0)).Adj xi23Root x ∧
      ((pairModel pair_D).xi (lhOrbit 0)).Adj x v ∧ ((pairModel pair_D).xi (lhOrbit 0)).Adj x w :=
  fun _ w h0 h1 hw0 hw1 hvw => (far_MU_ED h0 h1).2 w hw0 hw1 hvw

end CFSG.Sporadic.Fi22
