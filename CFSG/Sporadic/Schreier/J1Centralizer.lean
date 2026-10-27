module

public import CFSG.Sporadic.Schreier.J1CentCheck
public import CFSG.Sporadic.Schreier.J1Counts
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem wordG_mem {M : Type*} [Group M] (H : Subgroup M) {gensG : ℤ → M} {w : List ℤ}
    (h : ∀ l ∈ w, gensG l ∈ H) : wordG gensG w ∈ H := by
  unfold wordG
  exact H.list_prod_mem fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact h l hl

@[expose] noncomputable def j1LetterG (l : ℤ) : Equiv.Perm (Fin 3080) :=
  if l = 1 then j1A1 else if l = -1 then j1A1⁻¹ else if l = 2 then j1A2 else j1A2⁻¹

theorem rep_j1Letter
    (l : ℤ) : Rep 3080 (j1LetterTbl l) (j1LetterG l) := by
  unfold j1LetterTbl j1LetterG
  split_ifs
  · exact rep_j1ATbl
  · exact rep_j1AInvTbl
  · exact rep_j1BTbl
  · exact rep_j1BInvTbl

theorem j1LetterG_mem (l : ℤ) : j1LetterG l ∈ j1P := by
  unfold j1LetterG
  split_ifs
  · exact j1A1_mem
  · exact j1P.inv_mem j1A1_mem
  · exact j1A2_mem
  · exact j1P.inv_mem j1A2_mem

@[expose] noncomputable def j1C (i : ℕ) : Equiv.Perm (Fin 3080) :=
  wordG j1LetterG (j1CWords.getD i [])

theorem rep_j1C
    (i : ℕ) : Rep 3080 (j1CTbl i) (j1C i) :=
  Rep.wordT (by norm_num) _ fun l _ => rep_j1Letter l

theorem j1C_mem (i : ℕ) : j1C i ∈ j1P := wordG_mem _ fun l _ => j1LetterG_mem l

@[expose] noncomputable def j1CLetterG (l : ℤ) : Equiv.Perm (Fin 3080) :=
  if 0 < l then j1C (l.toNat - 1) else (j1C ((-l).toNat - 1))⁻¹

theorem rep_j1CLetter
    {l : ℤ} (hl : -4 ≤ l) : Rep 3080 (j1CLetterTbl l) (j1CLetterG l) := by
  unfold j1CLetterTbl j1CLetterG
  split_ifs with h
  · exact rep_j1C _
  · have hi : (-l).toNat - 1 < 4 := by omega
    exact (rep_j1C _).inv_of_invOK (List.all_eq_true.1 j1_c_checks _ (List.mem_range.2 hi))

theorem j1CLetterG_mem (l : ℤ) : j1CLetterG l ∈ j1P := by
  unfold j1CLetterG
  split_ifs
  · exact j1C_mem _
  · exact j1P.inv_mem (j1C_mem _)

@[expose] noncomputable def j1D (j : ℕ) : Equiv.Perm (Fin 3080) :=
  wordG j1CLetterG (j1DWords.getD j [])

theorem j1DWords_ge {j : ℕ} (hj : j < 3) : ∀ l ∈ j1DWords.getD j [], -4 ≤ l := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals decide

theorem rep_j1D
    {j : ℕ} (hj : j < 3) : Rep 3080 (j1DTbl j) (j1D j) :=
  Rep.wordT (by norm_num) _ fun l hl => rep_j1CLetter (j1DWords_ge hj l hl)

theorem j1D_mem (j : ℕ) : j1D j ∈ j1P := wordG_mem _ fun l _ => j1CLetterG_mem l

theorem j1D_check {j : ℕ} (hj : j < 3) :
    invOK 3080 (j1DTbl j) (invT 3080 (j1DTbl j)) = true ∧ commT 3080 (j1DTbl j) j1ATbl = true := by
  have := List.all_eq_true.1 j1_d_checks.1 j (List.mem_range.2 hj)
  simpa only [Bool.and_eq_true] using this

theorem j1D_comm
    {j : ℕ} (hj : j < 3) : j1D j * j1A1 = j1A1 * j1D j :=
  eq_of_commT (rep_j1D hj) rep_j1ATbl (j1D_check hj).2

theorem j1DGens_size : j1DGens.size = 3 := by
  simp [j1DGens]

theorem j1DGens_get {l : ℕ} (hl : l < 3) :
    j1DGens[l]! = j1DTbl l ∧ j1DGensInv[l]! = invT 3080 (j1DTbl l) := by
  obtain rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 := by omega
  all_goals exact ⟨by simp [j1DGens], by simp [j1DGensInv]⟩

theorem j1DGens_spec :
    ∀ l < j1DGens.size,
    Rep 3080 j1DGens[l]! (j1D l) ∧ Rep 3080 j1DGensInv[l]! (j1D l)⁻¹ := by
  intro l hl
  rw [j1DGens_size] at hl
  rw [(j1DGens_get hl).1, (j1DGens_get hl).2]
  exact ⟨rep_j1D hl, (rep_j1D hl).inv_of_invOK (j1D_check hl).1⟩

@[expose] noncomputable def j1DSub : Subgroup (Equiv.Perm (Fin 3080)) :=
  Subgroup.closure (j1D '' {l | l < j1DGens.size})

theorem j1DSub_facts :
    List.Forall₂ (Rep 3080) j1DElts.toList (closurePerms 3080 j1DElts) ∧
      (closurePerms 3080 j1DElts).Nodup ∧
      (∀ g, g ∈ closurePerms 3080 j1DElts ↔ g ∈ j1DSub) ∧ Nat.card j1DSub = j1DElts.size :=
  card_closure_of_mulTree (by norm_num) j1DGens_spec j1_D_closure.1 j1_D_closure.2.1
    j1_D_closure.2.2.1

theorem card_j1DSub :
    Nat.card j1DSub = 60 := by
  rw [j1DSub_facts.2.2.2, j1_D_closure.2.2.2]

theorem j1DSub_le :
    j1DSub ≤ centralizerIn j1P j1A1 := by
  rw [j1DSub, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  rw [Set.mem_ofPred_eq, j1DGens_size] at hl
  exact mem_centralizerIn.2 ⟨j1D_mem l, j1D_comm hl⟩

theorem j1D_mem_sub {j : ℕ} (hj : j < 3) : j1D j ∈ j1DSub :=
  Subgroup.subset_closure ⟨j, by rw [Set.mem_ofPred_eq, j1DGens_size]; exact hj, rfl⟩

theorem j1D_noncomm :
    j1D 0 * j1D 2 ≠ j1D 2 * j1D 0 := by
  intro h
  have := (commT_iff (rep_j1D (j := 0) (by norm_num)) (rep_j1D (j := 2) (by norm_num))).2 h
  rw [j1_d_checks.2] at this
  exact Bool.false_ne_true this

@[expose] noncomputable def j1DElt (k : ℕ) : Equiv.Perm (Fin 3080) := tablePerm 3080 j1DElts[k]!

theorem rep_j1DElt
    {k : ℕ} (hk : k < 60) : Rep 3080 j1DElts[k]! (j1DElt k) := by
  have hk' : k < j1DElts.size := by rw [j1_D_closure.2.2.2]; exact hk
  obtain ⟨g, hg⟩ := exists_rep_of_mulTree (by norm_num) (fun l hl => (j1DGens_spec l hl).1)
    j1_D_closure.1 k hk'
  rw [j1DElt, tablePerm_eq hg]
  exact hg

theorem j1DElt_mem
    {k : ℕ} (hk : k < 60) : j1DElt k ∈ j1DSub := by
  have hk' : k < j1DElts.size := by rw [j1_D_closure.2.2.2]; exact hk
  exact (mem_closure_iff_of_mulTree (by norm_num) j1DGens_spec j1_D_closure.1
    j1_D_closure.2.1 _).2 ⟨k, hk', rep_j1DElt hk⟩

theorem closurePerms_getElem {k : ℕ} (hk : k < (closurePerms 3080 j1DElts).length) :
    (closurePerms 3080 j1DElts)[k] = j1DElt k := by
  have key : ∀ (E : Array Table) (k : ℕ) (hk : k < (closurePerms 3080 E).length),
      (closurePerms 3080 E)[k] = tablePerm 3080 E[k]! := by
    intro E k hk
    have hk' : k < E.size := by simpa [closurePerms] using hk
    simp only [closurePerms, List.getElem_map, Array.getElem_toList]
    rw [getElem!_pos E k hk']
  exact key j1DElts k hk

theorem isSimpleGroup_j1DSub :
    IsSimpleGroup j1DSub := by
  obtain ⟨hF, hnd, hmem, -⟩ := j1DSub_facts
  have hsize := j1_D_closure.2.2.2
  have hlen : (closurePerms 3080 j1DElts).length = 60 := by
    simp [closurePerms, hsize]
  obtain ⟨hr5, hok⟩ := j1_D_labels
  simp only [classLabelsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Array.all_eq_true_iff_forall_mem] at hok
  obtain ⟨⟨⟨hpos, hr0⟩, hrlt⟩, hall⟩ := hok
  rw [hr5] at hpos
  have h0 : j1DElt 0 = 1 := by
    have h := j1_D_closure.1
    simp only [mulTreeOK, Bool.and_eq_true] at h
    exact rep_unique (rep_j1DElt (by norm_num)) (rep_of_tblEq (Rep.idT (by norm_num)) h.1.2)
  refine isSimpleGroup_of_labels j1DSub (N₀ := 60) (r := 5) (by norm_num) card_j1DSub
    (by norm_num) j1DElt (fun k hk => j1DElt_mem hk) (fun i hi j hj hij => ?_) (fun g hg => ?_)
    (fun k => j1DClasses.2.1[k]!) (fun k => j1DClasses.2.2[k]!) (fun i => j1DClasses.1[i]!)
    (by rw [hr0]; exact h0) (fun i hi => ?_) (fun k hk => ?_) j1_D_subsets
  · rw [← closurePerms_getElem (by rw [hlen]; exact hi),
      ← closurePerms_getElem (by rw [hlen]; exact hj)] at hij
    exact (List.Nodup.getElem_inj_iff hnd).1 hij
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ((hmem g).2 hg)
    exact ⟨k, hlen ▸ hk, (closurePerms_getElem hk).symm⟩
  · have hmemi : j1DClasses.1[i]! ∈ j1DClasses.1 := by
      rw [getElem!_pos j1DClasses.1 i (by rw [hr5]; exact hi)]
      exact Array.getElem_mem _
    rw [← hsize]
    exact hrlt _ hmemi
  · have h := allIn_eq_true.1 hall k (Nat.zero_le _) (by rw [hsize]; exact hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hl, hc⟩, hinv⟩, heq⟩ := h
    rw [hr5] at hl
    rw [hsize] at hc
    refine ⟨hl, hc, ?_⟩
    have hcr := rep_j1DElt hc
    have hmeml : j1DClasses.1[j1DClasses.2.1[k]!]! ∈ j1DClasses.1 := by
      rw [getElem!_pos j1DClasses.1 _ (by rw [hr5]; exact hl)]
      exact Array.getElem_mem _
    have hrl : j1DClasses.1[j1DClasses.2.1[k]!]! < 60 := by
      rw [← hsize]
      exact hrlt _ hmeml
    have hc' := rep_of_tblEq (rep_conjT hcr (hcr.inv_of_invOK hinv) (rep_j1DElt hrl)) heq
    exact rep_unique (rep_j1DElt hk) hc'

section Stream

variable {n : ℕ}

theorem forall₂_centTables (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {zT : Table}
    {z : Equiv.Perm (Fin n)} (hz : Rep n zT z) :
    List.Forall₂ (Rep n) (filterProducts n (commT n zT) (levelTables Q) (idT n) [])
      ((enumeration Q).filter fun h => decide (z * h = h * z)).reverse := by
  have h := filterProducts_spec (P := fun h : Equiv.Perm (Fin n) => z * h = h * z)
    (fun T g hT => commT_iff hz hT) (forall₂_levelTables hn Q) (Rep.idT hn) (acc := [])
    (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem mem_centList (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (z g : Equiv.Perm (Fin n)) :
    g ∈ ((enumeration Q).filter fun h => decide (z * h = h * z)).reverse ↔
      g ∈ centralizerIn Q.originalSubgroup z := by
  rw [List.mem_reverse, List.mem_filter, mem_enumeration_iff Q hQ, decide_eq_true_eq,
    mem_centralizerIn, eq_comm (a := z * g)]

theorem card_centralizerIn_eq (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {zT : Table} {z : Equiv.Perm (Fin n)} (hz : Rep n zT z) :
    Nat.card (centralizerIn Q.originalSubgroup z) =
      (filterProducts n (commT n zT) (levelTables Q) (idT n) []).length := by
  rw [(forall₂_centTables hn Q hz).length_eq]
  refine card_eq_length (fun g => g ∈ centralizerIn Q.originalSubgroup z) (fun g => g)
    (fun _ _ h => h) _ (List.nodup_reverse.2 ((enumeration_nodup Q hQ).filter _)) fun g => ?_
  rw [mem_centList Q hQ]
  exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨a, ha, hag⟩ => hag ▸ ha⟩

theorem oddWitness_of_tables (hn : n < 2 ^ 32) {K : Subgroup (Equiv.Perm (Fin n))}
    {Ts : List Table} {gs : List (Equiv.Perm (Fin n))} (hA : List.Forall₂ (Rep n) Ts gs)
    (hmem : ∀ g, g ∈ gs ↔ g ∈ K) {m : ℕ} (h : oddWitnessOK n m Ts = true) : OddWitness K m := by
  intro x hx hx1 hxm
  obtain ⟨X, hX, hXx⟩ := exists_mem_of_forall₂_left hA x ((hmem x).2 hx)
  have hall := (List.all_eq_true.1 h) X hX
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true] at hall
  rcases hall with ((hid | hpow) | ⟨H, hH, hinv, hne⟩) | ⟨H₁, hH₁, hinv₁, H₂, hH₂, hinv₂, hne⟩
  · exact absurd (eq_one_of_tblEq_idT hn hXx hid) hx1
  · have := (powFixW_iff perm_faithful (List.Forall₂.cons hXx List.Forall₂.nil) m).2
      (by simpa using hxm)
    rw [this] at hpow
    exact absurd hpow.symm Bool.false_ne_true
  · obtain ⟨hg, hhg, hHh⟩ := exists_mem_of_forall₂_right hA H hH
    have hHi := Rep.inv_of_invOK hHh hinv
    refine Or.inl ⟨hg, (hmem hg).1 hhg, fun heq => ?_⟩
    have hw : List.Forall₂ (Rep n) [X, H, X, invT n H] [x, hg, x, hg⁻¹] :=
      .cons hXx (.cons hHh (.cons hXx (.cons hHi .nil)))
    have := (powFixW_iff perm_faithful hw m).2 (by
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using heq)
    rw [this] at hne
    exact Bool.false_ne_true hne.symm
  · obtain ⟨hg₁, hhg₁, hH₁h⟩ := exists_mem_of_forall₂_right hA H₁ hH₁
    obtain ⟨hg₂, hhg₂, hH₂h⟩ := exists_mem_of_forall₂_right hA H₂ hH₂
    have hH₁i := Rep.inv_of_invOK hH₁h hinv₁
    have hH₂i := Rep.inv_of_invOK hH₂h hinv₂
    refine Or.inr ⟨hg₁, (hmem hg₁).1 hhg₁, hg₂, (hmem hg₂).1 hhg₂, fun heq => ?_⟩
    have hw : List.Forall₂ (Rep n) [X, H₁, X, invT n H₁, H₂, X, invT n H₂]
        [x, hg₁, x, hg₁⁻¹, hg₂, x, hg₂⁻¹] :=
      .cons hXx (.cons hH₁h (.cons hXx (.cons hH₁i (.cons hH₂h (.cons hXx (.cons hH₂i .nil))))))
    have := (powFixW_iff perm_faithful hw m).2 (by
      simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using heq)
    rw [this] at hne
    exact Bool.false_ne_true hne.symm

end Stream

theorem j1_datum :
    ∃ Q : RawSchreierDatum 3080, J1Certificate.chain.Records Q ∧
    ValidSchreier Q ∧ Q.originalSubgroup = j1P := by
  obtain ⟨Q, hrec, hQ, -, -, -, hP, -, -⟩ := fam_j1_order
  exact ⟨Q, hrec, hQ, hP⟩

theorem card_j1Cent :
    Nat.card (centralizerIn j1P j1A1) = 120 := by
  obtain ⟨Q, hrec, hQ, hP⟩ := j1_datum
  have h := card_centralizerIn_eq (by norm_num) Q hQ rep_j1ATbl
  rw [j1_levelTables hrec, hP] at h
  rw [h]
  exact j1_cent_checks.1

theorem oddWitness_j1Cent :
    OddWitness (centralizerIn j1P j1A1) 15 := by
  obtain ⟨Q, hrec, hQ, hP⟩ := j1_datum
  have hA := forall₂_centTables (by norm_num) Q rep_j1ATbl
  rw [j1_levelTables hrec] at hA
  have hmem := mem_centList Q hQ j1A1
  rw [hP] at hmem
  exact oddWitness_of_tables (by norm_num) hA hmem j1_cent_checks.2

theorem toTable_j1A1 : toTable j1A1 = j1ATbl := by
  unfold toTable j1ATbl listTbl
  congr 1
  funext i
  rw [j1A1, arrPerm_val isPermList_j1A1List]

theorem j1_involution_conj
    (u : Equiv.Perm (Fin 3080)) (hu : u ∈ j1P) (ho : orderOf u = 2) :
    ∃ c ∈ j1P, u = c * j1A1 * c⁻¹ := by
  obtain ⟨Q, hrec, hQ, hP⟩ := j1_datum
  have hok : repsOK 3080 j1GenTbls j1GenInvTbls (cosetOrderTables Q 1 2) ([j1A1].map toTable)
      2000 = true := by
    rw [cosetOrderTables, j1_levelTables hrec, List.map_singleton, toTable_j1A1]
    exact j1_inv_class.1
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK (by norm_num) Q hQ (gens := j1GenTbls)
    (gensInv := j1GenInvTbls) (gg := j1GenPerm)
    (by rw [hP]; exact j1GenPerm_spec) 1 (fun h hh => by simpa using hh) (by norm_num) [j1A1]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [inv_one, one_mul, hP]; exact j1A1_mem, at_j1_image_pair_count.1⟩)
    2000 hok
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by rw [inv_one, one_mul, hP]; exact hu) ho
  rw [List.mem_singleton] at hr
  subst hr
  exact ⟨c, hP ▸ hc, rfl⟩

theorem j1P_involution_centralizer
    (u : Equiv.Perm (Fin 3080)) (hu : u ∈ j1P)
    (ho : orderOf u = 2) :
    Nat.card (centralizerIn j1P u) = 120 ∧ OddWitness (centralizerIn j1P u) 15 ∧
      ∃ K : Subgroup (Equiv.Perm (Fin 3080)), K ≤ centralizerIn j1P u ∧ Nat.card K = 60 ∧
        IsSimpleGroup K ∧ ∃ x ∈ K, ∃ y ∈ K, x * y ≠ y * x := by
  obtain ⟨c, hc, rfl⟩ := j1_involution_conj u hu ho
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  rw [centralizerIn_conj _ hc]
  refine ⟨by rw [Subgroup.card_map_of_injective hinj, card_j1Cent],
    oddWitness_j1Cent.map_conj c, j1DSub.map (MulAut.conj c).toMonoidHom,
    Subgroup.map_mono j1DSub_le, by rw [Subgroup.card_map_of_injective hinj, card_j1DSub], ?_,
    _, Subgroup.mem_map_of_mem _ (j1D_mem_sub (j := 0) (by norm_num)),
    _, Subgroup.mem_map_of_mem _ (j1D_mem_sub (j := 2) (by norm_num)), ?_⟩
  · have : IsSimpleGroup j1DSub := isSimpleGroup_j1DSub
    exact MulEquiv.isSimpleGroup (Subgroup.equivMapOfInjective j1DSub _ hinj).symm
  · intro h
    apply j1D_noncomm
    have h' : (MulAut.conj c).toMonoidHom (j1D 0 * j1D 2) =
        (MulAut.conj c).toMonoidHom (j1D 2 * j1D 0) := by
      rw [map_mul, map_mul]
      exact h
    exact hinj h'

end CFSG.Sporadic.Schreier
