module

public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native

variable {n : ℕ}

theorem isConj_subgroup_iff {M : Type*} [Group M] {H : Subgroup M} {a b : H} :
    IsConj a b ↔ (b : M) ∈ conjClass H a := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, c.2, by simp⟩
  · rintro ⟨c, hc, hb⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (by simp [hb])⟩

theorem conjClass_subset {M : Type*} [Group M] (H : Subgroup M) {x : M} (hx : x ∈ H) :
    conjClass H x ⊆ H := by
  rintro _ ⟨c, hc, rfl⟩
  exact H.mul_mem (H.mul_mem hc hx) (H.inv_mem hc)

theorem ncard_carrier_mk {M : Type*} [Group M] (H : Subgroup M) {x : M} (hx : x ∈ H) :
    (ConjClasses.mk (⟨x, hx⟩ : H)).carrier.ncard = (conjClass H x).ncard := by
  have e : (ConjClasses.mk (⟨x, hx⟩ : H)).carrier = Subtype.val ⁻¹' conjClass H x := by
    ext y
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm,
      isConj_subgroup_iff]
    rfl
  rw [e, ← Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.image_preimage_eq_of_subset]
  intro y hy
  exact ⟨⟨y, conjClass_subset H hx hy⟩, rfl⟩

theorem conjClass_eq_of_isConj {M : Type*} [Group M] {H : Subgroup M} {x y : M}
    (hy : y ∈ conjClass H x) : conjClass H y = conjClass H x := by
  obtain ⟨c, hc, rfl⟩ := hy
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, H.mul_mem hd hc, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, H.mul_mem hd (H.inv_mem hc), by group⟩

theorem carrier_mk_map {G H : Type*} [Group G] [Group H] (f : G ≃* H) (a : G) :
    (ConjClasses.mk (f a)).carrier = f '' (ConjClasses.mk a).carrier := by
  ext y
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  constructor
  · intro h
    refine ⟨f.symm y, ?_, by simp⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    have := (isConj_iff.1 h)
    obtain ⟨c, hc⟩ := this
    exact isConj_iff.2 ⟨f.symm c, f.injective (by simp [← hc])⟩
  · rintro ⟨x, hx, rfl⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    exact isConj_iff.2 ⟨f c, by simp⟩

theorem conjClasses_equiv_of_mulEquiv {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    ∃ e : ConjClasses G ≃ ConjClasses H, ∀ c, (e c).carrier.ncard = c.carrier.ncard := by
  refine ⟨⟨ConjClasses.map f.toMonoidHom, ConjClasses.map f.symm.toMonoidHom, fun c => ?_,
    fun c => ?_⟩, fun c => ?_⟩
  · obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (f.symm (f a)) = ConjClasses.mk a
    rw [MulEquiv.symm_apply_apply]
  · obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (f (f.symm a)) = ConjClasses.mk a
    rw [MulEquiv.apply_symm_apply]
  · obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective c
    change (ConjClasses.mk (f a)).carrier.ncard = _
    rw [carrier_mk_map, Set.ncard_image_of_injective _ f.injective]

section Closures

variable (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
  {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
  (hg : ∀ l < gens.size,
    Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
  (cap : ℕ)

include hn hQ in
theorem mem_allTables_rep {T : Table} (hT : T ∈ allTables Q) :
    ∃ x ∈ Q.originalSubgroup, Rep n T x := by
  obtain ⟨x, hx, hTx⟩ := exists_mem_of_forall₂_right (forall₂_allTables hn Q) T hT
  rw [List.mem_reverse, mem_enumeration_iff Q hQ] at hx
  exact ⟨x, hx, hTx⟩

include hn hQ in
theorem classes_rep (hok : classOK n gens gensInv (allTables Q) cap = true)
    {c : Table × Array Table × Array ℕ × Array ℕ}
    (hc : c ∈ classes n gens gensInv (allTables Q) cap) :
    (∃ x ∈ Q.originalSubgroup, Rep n c.1 x) ∧ conjTreeOK n gens gensInv c.1 c.2.1 c.2.2.1
      c.2.2.2 = true := by
  have hok' := hok
  simp only [classOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok'
  obtain ⟨⟨⟨hreps, htrees⟩, -⟩, -⟩ := hok'
  refine ⟨?_, htrees c hc⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
  have hlt := of_decide_eq_true (hreps i hi)
  refine mem_allTables_rep hn Q hQ ?_
  rw [getElem!_pos (allTables Q).toArray i (by simpa using hlt), List.getElem_toArray]
  exact List.getElem_mem _

@[expose] def tableElems (n : ℕ) (Ts : List Table) : List (Equiv.Perm (Fin n)) :=
  Ts.map (tablePerm n)

include hn hQ hg in
theorem classes_entries (hok : classOK n gens gensInv (allTables Q) cap = true)
    {c : Table × Array Table × Array ℕ × Array ℕ}
    (hc : c ∈ classes n gens gensInv (allTables Q) cap) {x : Equiv.Perm (Fin n)}
    (hx : Rep n c.1 x) :
    List.Forall₂ (Rep n) c.2.1.toList (tableElems n c.2.1.toList) ∧
      ∀ y ∈ tableElems n c.2.1.toList, y ∈ conjClass Q.originalSubgroup x := by
  have htree := (classes_rep hn Q hQ cap hok hc).2
  have hspec := conjTreeOK_spec Q.originalSubgroup hg hx htree
  have hrep : ∀ T ∈ c.2.1.toList, ∃ y ∈ conjClass Q.originalSubgroup x, Rep n T y := by
    intro T hT
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hT
    have hk' : k < c.2.1.size := by simpa using hk
    obtain ⟨d, hd, hrep⟩ := hspec k hk'
    refine ⟨d * x * d⁻¹, ⟨d, hd, rfl⟩, ?_⟩
    rw [Array.getElem_toList, ← getElem!_pos c.2.1 k hk']
    exact hrep
  refine ⟨?_, fun y hy => ?_⟩
  · rw [tableElems, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨y, -, hTy⟩ := hrep T hT
    rw [tablePerm_eq hTy]
    exact hTy
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hy
    obtain ⟨y, hy, hTy⟩ := hrep T hT
    rw [tablePerm_eq hTy]
    exact hy

include hn hQ in
theorem card_centralizerIn_eq_countP {T : Table} {x : Equiv.Perm (Fin n)} (hT : Rep n T x) :
    Nat.card (centralizerIn Q.originalSubgroup x) = (allTables Q).countP (commT n T) := by
  have h1 : (allTables Q).countP (commT n T) =
      (enumeration Q).reverse.countP fun y => decide (x * y = y * x) :=
    countP_eq_of_forall₂ (forall₂_allTables hn Q) fun T' y hT' _ =>
      ⟨fun h => decide_eq_true ((commT_iff hT hT').1 h),
        fun h => (commT_iff hT hT').2 (of_decide_eq_true h)⟩
  rw [h1, List.countP_reverse, ← card_subtype_eq_countP Q.originalSubgroup (enumeration Q)
    (enumeration_nodup Q hQ) (mem_enumeration_iff Q hQ)]
  refine Nat.card_congr ⟨fun y => ⟨⟨y, y.2.1⟩, (mem_centralizerIn.1 y.2).2.symm⟩,
    fun y => ⟨y.1, mem_centralizerIn.2 ⟨y.1.2, y.2.symm⟩⟩, fun y => rfl, fun y => rfl⟩

include hn hQ in
theorem length_allTables : (allTables Q).length = Nat.card Q.originalSubgroup := by
  rw [(forall₂_allTables hn Q).length_eq, List.length_reverse, length_enumeration,
    Q.orderCertificate_eq_card hQ]

include hn hQ hg in
theorem conjClasses_equiv_of_classOK (hok : classOK n gens gensInv (allTables Q) cap = true)
    {sizes cents : List ℕ}
    (hsizes : (classes n gens gensInv (allTables Q) cap).map (fun c => c.2.1.size) = sizes)
    (hcents : (classes n gens gensInv (allTables Q) cap).map
      (fun c => (allTables Q).countP (commT n c.1)) = cents)
    (hprod : ∀ i (hi : i < sizes.length) (hj : i < cents.length),
      sizes[i] * cents[i] = Nat.card Q.originalSubgroup) :
    ∃ e : Fin sizes.length ≃ ConjClasses Q.originalSubgroup,
      ∀ i, (e i).carrier.ncard = sizes[i] := by
  classical
  set H := Q.originalSubgroup with hHdef
  set cl := classes n gens gensInv (allTables Q) cap with hcl
  have hlen : cl.length = sizes.length := by rw [← hsizes, List.length_map]
  have hlenc : cl.length = cents.length := by rw [← hcents, List.length_map]
  have hok' := hok
  simp only [classOK, Bool.and_eq_true, beq_iff_eq] at hok'
  obtain ⟨⟨-, hkeys⟩, hsum⟩ := hok'
  rw [← hcl] at hkeys hsum
  have hrep : ∀ i : Fin cl.length, ∃ x ∈ H, Rep n cl[i].1 x := fun i =>
    (classes_rep hn Q hQ cap hok (List.getElem_mem _)).1
  choose x hxH hxrep using hrep
  set L : Fin cl.length → List (Equiv.Perm (Fin n)) := fun i => tableElems n cl[i].2.1.toList
    with hL
  have hLspec : ∀ i, List.Forall₂ (Rep n) cl[i].2.1.toList (L i) ∧
      ∀ y ∈ L i, y ∈ conjClass H (x i) := fun i =>
    classes_entries hn Q hQ hg cap hok (List.getElem_mem _) (hxrep i)
  have hLlen : ∀ i : Fin cl.length, (L i).length = sizes[i.val]'(hlen ▸ i.2) := by
    intro i
    rw [(hLspec i).1.length_eq.symm, Array.length_toList]
    have := congrArg (fun l => l[i.val]?) hsizes
    simp only [List.getElem?_map, List.getElem?_eq_getElem i.2,
      List.getElem?_eq_getElem (hlen ▸ i.2 : i.val < sizes.length), Option.map_some,
      Option.some.injEq] at this
    exact this
  set FT := cl.flatMap fun c => c.2.1.toList with hFT
  have hFT2 : List.Forall₂ (Rep n) FT (tableElems n FT) := by
    rw [tableElems, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨c, hc, hTc⟩ := List.mem_flatMap.1 hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨y, -, hTy⟩ := exists_mem_of_forall₂_right ((hLspec ⟨i, hi⟩).1) T hTc
    rw [tablePerm_eq hTy]
    exact hTy
  have hnodup : (tableElems n FT).Nodup := nodup_of_keysDistinct hFT2 hkeys
  have hFTeq : tableElems n FT = (List.finRange cl.length).flatMap L := by
    rw [hFT, tableElems, List.map_flatMap]
    conv_lhs => rw [← List.map_getElem_finRange cl]
    rw [List.flatMap_map]
    rfl
  rw [hFTeq] at hnodup
  have hcard_pos : 0 < Nat.card H := Nat.card_pos
  have hcls : ∀ i : Fin cl.length, (conjClass H (x i)).ncard = sizes[i.val]'(hlen ▸ i.2) := by
    intro i
    have h1 := ncard_conjClass_mul_card H (x i)
    have h2 := card_centralizerIn_eq_countP hn Q hQ (hxrep i)
    have h3 : (allTables Q).countP (commT n cl[i].1) = cents[i.val]'(hlenc ▸ i.2) := by
      have := congrArg (fun l => l[i.val]?) hcents
      simp only [List.getElem?_map, List.getElem?_eq_getElem i.2,
        List.getElem?_eq_getElem (hlenc ▸ i.2 : i.val < cents.length), Option.map_some,
        Option.some.injEq] at this
      exact this
    have h4 := hprod i.val (hlen ▸ i.2) (hlenc ▸ i.2)
    rw [h2, h3] at h1
    have hc0 : 0 < cents[i.val]'(hlenc ▸ i.2) := by
      rcases Nat.eq_zero_or_pos (cents[i.val]'(hlenc ▸ i.2)) with h0 | h0
      · rw [h0, mul_zero] at h1
        omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_right hc0 (h1.trans h4.symm)
  have hLset : ∀ i : Fin cl.length, {y | y ∈ L i} = conjClass H (x i) := by
    intro i
    have hnd : (L i).Nodup := (List.nodup_flatMap.1 hnodup).1 i (List.mem_finRange i)
    refine Set.eq_of_subset_of_ncard_le (fun y hy => (hLspec i).2 y hy) ?_
      ((conjClass_finite H (x i)))
    rw [hcls i, ← hLlen i]
    have : {y | y ∈ L i} = ((L i).toFinset : Set (Equiv.Perm (Fin n))) := by
      ext y
      simp
    rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have hcover : ∀ y ∈ H, ∃ i, y ∈ L i := by
    intro y hy
    have hsub : {g | g ∈ (List.finRange cl.length).flatMap L} ⊆ (H : Set _) := by
      intro g hg
      obtain ⟨i, -, hgi⟩ := List.mem_flatMap.1 hg
      exact conjClass_subset H (hxH i) ((hLspec i).2 g hgi)
    have hlenFL : ((List.finRange cl.length).flatMap L).length = Nat.card H := by
      rw [← hFTeq, tableElems, List.length_map, hFT, List.length_flatMap]
      simp only [Array.length_toList]
      rw [hsum, length_allTables hn Q hQ]
    have heq := Set.eq_of_subset_of_ncard_le hsub (by
      have : {g | g ∈ (List.finRange cl.length).flatMap L} =
          (((List.finRange cl.length).flatMap L).toFinset : Set (Equiv.Perm (Fin n))) := by
        ext g
        simp
      rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnodup, hlenFL,
        ← Nat.card_coe_set_eq]
      rfl) (Set.toFinite _)
    have hy' : y ∈ {g | g ∈ (List.finRange cl.length).flatMap L} := by
      rw [heq]
      exact hy
    obtain ⟨i, -, hyi⟩ := List.mem_flatMap.1 hy'
    exact ⟨i, hyi⟩
  have hdisj : ∀ i j : Fin cl.length, ∀ y, y ∈ L i → y ∈ L j → i = j := by
    intro i j y hi hj
    by_contra hne
    have hpw := (List.nodup_flatMap.1 hnodup).2
    have : Std.Symm (fun a b : Fin cl.length => List.Disjoint (L a) (L b)) :=
      ⟨fun a b h => List.Disjoint.symm h⟩
    exact (hpw.forall (List.mem_finRange i) (List.mem_finRange j) hne) hi hj
  let f : Fin cl.length → ConjClasses H := fun i => ConjClasses.mk ⟨x i, hxH i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hconj := ConjClasses.mk_eq_mk_iff_isConj.1 hij
      rw [isConj_subgroup_iff] at hconj
      have hcj := conjClass_eq_of_isConj hconj
      have hne : 0 < (L i).length := by
        rw [hLlen i, ← hcls i]
        exact Set.ncard_pos (conjClass_finite H (x i)) |>.2 ⟨x i, 1, H.one_mem, by group⟩
      obtain ⟨y, hy⟩ := List.exists_mem_of_length_pos hne
      have hyj : y ∈ L j := by
        have : y ∈ {y | y ∈ L j} := by
          rw [hLset j, hcj, ← hLset i]
          exact hy
        exact this
      exact hdisj i j y hy hyj
    · intro c
      obtain ⟨y, rfl⟩ := ConjClasses.mk_surjective c
      obtain ⟨i, hyi⟩ := hcover y y.2
      refine ⟨i, ConjClasses.mk_eq_mk_iff_isConj.2 ?_⟩
      rw [isConj_subgroup_iff]
      have : (y : Equiv.Perm (Fin n)) ∈ {y | y ∈ L i} := hyi
      rwa [hLset i] at this
  refine ⟨(finCongr hlen.symm).trans (Equiv.ofBijective f hf), fun i => ?_⟩
  simp only [Equiv.trans_apply, Equiv.ofBijective_apply, finCongr_apply, f]
  rw [ncard_carrier_mk, hcls]
  rfl

end Closures

end CFSG.Sporadic.HeldB
