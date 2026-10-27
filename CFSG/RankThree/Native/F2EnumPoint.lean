module

public import CFSG.RankThree.Native.F2Enum

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.KC.Enum CFSG.KS

theorem tree_inv_ex {d : ℕ} (hd : 0 < d) {V : Array ℕ} (hVd : ∀ v ∈ V, v < 2 ^ d)
    {mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d)
    {ngen N : ℕ} {GM GMI PM : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hG : ∀ k < ngen, Inv d V (GM k) (GMI k)) (h0 : PM 0 = I)
    (hp : ∀ i < N, pointM mm ngen N GM PM E PAR LAB i = true) :
    ∀ i < N, ∃ MI, Inv d V (PM i) MI := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [h0, hI]
      exact ⟨_, inv_idM hd hVd⟩
    · obtain ⟨h1, h2, h3⟩ := pointM_tree (hp i hi) (by omega)
      obtain ⟨MI, hMI⟩ := ih _ h1 (by omega)
      rw [h3, hmm]
      exact ⟨_, hMI.mul hd (hG _ h2)⟩

theorem keyA_permOfMat {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) {M : ℕ}
    (hM : ∀ v ∈ V, vmul d v M ∈ V) {PM : ℕ → ℕ} {i : ℕ} (hPM : PM i = M) :
    ∀ ps : List ℕ, (∀ p ∈ ps, p < V.size) →
      keyA V.size ps (permOfMat d V M) = keyM vm V.size VG LK ps PM i
  | [], _ => rfl
  | p :: ps, hps => by
    have hp : p < V.size := hps p List.mem_cons_self
    have ih := keyA_permOfMat hs hvm hM hPM ps fun q hq => hps q (List.mem_cons_of_mem _ hq)
    unfold keyA at ih ⊢
    unfold keyM at ih ⊢
    rw [List.map_cons, Nat.ofDigits_cons, ih, List.foldr_cons, permOfMat_get hp, hs.vg p hp,
      hvm, hPM]
    have hw := getElem_vidx (hM _ (hs.mem hp))
    have e : LK (vmul d (VG p) M) = vidx V (vmul d (VG p) M) := by
      conv_lhs => rw [← hw.2, hs.vg _ hw.1, hs.lk _ hw.1]
    rw [e]
    rfl

theorem inj_of_order {N : ℕ} {f SO SOI : ℕ → ℕ} (hso : ∀ j < N, SO j < N ∧ SOI (SO j) = j)
    (hk : ∀ j, j + 1 < N → f (SO j) < f (SO (j + 1))) {i i' : ℕ} (hi : i < N) (hi' : i' < N)
    (e : f i = f i') : i = i' := by
  classical
  have hinj : Set.InjOn SO (Finset.range N : Set ℕ) := fun a ha b hb hab => by
    have h1 := (hso a (Finset.mem_range.1 ha)).2
    have h2 := (hso b (Finset.mem_range.1 hb)).2
    rw [← h1, ← h2, hab]
  have hsub : (Finset.range N).image SO ⊆ Finset.range N := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (hso j (Finset.mem_range.1 hj)).1
  have heq : (Finset.range N).image SO = Finset.range N :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have hmono : ∀ j j', j < j' → j' < N → f (SO j) < f (SO j') := by
    intro j j' hjj' hj'
    induction j' with
    | zero => omega
    | succ j' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hjj' with h | rfl
      · exact (ih h (by omega)).trans (hk j' hj')
      · exact hk j hj'
  have hs : ∀ x < N, ∃ j < N, SO j = x := fun x hx => by
    have : x ∈ (Finset.range N).image SO := by rw [heq]; exact Finset.mem_range.2 hx
    obtain ⟨j, hj, e⟩ := Finset.mem_image.1 this
    exact ⟨j, Finset.mem_range.1 hj, e⟩
  obtain ⟨j, hj, rfl⟩ := hs i hi
  obtain ⟨j', hj', rfl⟩ := hs i' hi'
  rcases lt_trichotomy j j' with h | rfl | h
  · exact absurd e (ne_of_lt (hmono j j' h hj'))
  · rfl
  · exact absurd e.symm (ne_of_lt (hmono j' j h hj))

theorem enumOK_of_pointM {d : ℕ} {V : Array ℕ} {VG LK : ℕ → ℕ} (hs : Sys d V VG LK)
    {vm mm : ℕ → ℕ → ℕ} (hvm : ∀ v M, vm v M = vmul d v M) (hmm : ∀ A B, mm A B = mmul d A B)
    {I : ℕ} (hI : I = idM d) {ngen N : ℕ} {GM GMI PM : ℕ → ℕ} {gs : Array (Array ℕ)}
    (hgs : gs.size = ngen) (hG : ∀ k < ngen, gs[k]! = permOfMat d V (GM k))
    (hGI : ∀ k < ngen, Inv d V (GM k) (GMI k)) {ps : List ℕ} (hps : ∀ p ∈ ps, p < V.size)
    {c : ArrCert} (hN : c.pts.size = N) (hP : ∀ i < N, c.pts[i]! = permOfMat d V (PM i))
    {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ}
    (hE : ∀ i < N, (c.edges[i]!).size = ngen ∧ ∀ k < ngen, (c.edges[i]!)[k]! = E i k)
    (hPL : ∀ i < N, c.par[i]! = PAR i ∧ c.lab[i]! = LAB i)
    (h0 : 0 < N) (hroot : PM 0 = I)
    (hp : ∀ i < N, pointM mm ngen N GM PM E PAR LAB i = true)
    {SO SOI : ℕ → ℕ} (hso : ∀ j < N, SO j < N ∧ SOI (SO j) = j)
    (hk : ∀ j, j + 1 < N →
      keyM vm V.size VG LK ps PM (SO j) < keyM vm V.size VG LK ps PM (SO (j + 1))) :
    CFSG.RankThree.Native.enumOK V.size gs ps c = true := by
  have hd := hs.hd
  have hgood := tree_good hd hs.lt hmm hI (fun k hk => (hGI k hk).1) hroot hp
  have hinv := tree_inv_ex hd hs.lt hmm hI hGI hroot hp
  have hval : ∀ i < N, CFSG.RankThree.Native.validA V.size c.pts[i]! = true := fun i hi => by
    obtain ⟨MI, hMI⟩ := hinv i hi
    rw [hP i hi]
    exact validA_permOfMat hd hs.nodup hs.lt hMI
  have hleft : ∀ k < ngen, ∀ i < N, CFSG.RankThree.Native.leftA V.size gs k c.pts[i]! =
      permOfMat d V (mm (PM i) (GM k)) := fun k hk i hi => by
    rw [CFSG.RankThree.Native.leftA, hG k hk, hP i hi, compA_permOfMat (hgood i hi).1, hmm]
  have hkeyA : ∀ i < N, CFSG.RankThree.Native.keyA V.size ps c.pts[i]! =
      keyM vm V.size VG LK ps PM i := fun i hi => by
    rw [hP i hi]
    exact keyA_permOfMat hs hvm (hgood i hi).1 rfl ps hps
  unfold CFSG.RankThree.Native.enumOK arrCertOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    allLt_iff]
  refine ⟨fun k hk => ?_, ⟨⟨⟨by omega, ?_⟩, fun i hi => ?_⟩, ?_⟩⟩
  · rw [hgs] at hk
    rw [hG k hk]
    exact validA_permOfMat hd hs.nodup hs.lt (hGI k hk)
  · rw [hP 0 (by omega), hroot, hI, permOfMat_idM hd hs.nodup hs.lt]
  · rw [hN] at hi
    have hpi := hp i hi
    unfold arrPointOK
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      decide_eq_true_eq]
    unfold pointM at hpi
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.blt_eq] at hpi
    obtain ⟨hed, htr⟩ := hpi
    refine ⟨⟨⟨hval i hi, by rw [(hE i hi).1, hgs]⟩, fun k hk => ?_⟩, ?_⟩
    · rw [hgs] at hk
      have he := allN_spec hed k hk
      rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at he
      rw [(hE i hi).2 k hk, hN, hleft k hk i hi, hP _ he.1, he.2]
      exact ⟨he.1, rfl⟩
    · rcases htr with h | ⟨⟨h1, h2⟩, h3⟩
      · exact Or.inl h
      · right
        rw [(hPL i hi).1, (hPL i hi).2, hgs]
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [hleft _ h2 _ (h1.trans hi), hP i hi, h3]
  ·
    have hlen : c.pts.toList.length = N := by rw [Array.length_toList, hN]
    have hmap : c.pts.toList.map (CFSG.RankThree.Native.keyA V.size ps) =
        (List.range N).map fun i => keyM vm V.size VG LK ps PM i := by
      apply List.ext_getElem (by simp [hN])
      intro i h1 h2
      have hi : i < N := by simpa [hN] using h1
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList,
        ← getElem!_pos c.pts i (by rw [hN]; exact hi), hkeyA i hi]
    have hnd : (c.pts.toList.map (CFSG.RankThree.Native.keyA V.size ps)).Nodup := by
      rw [hmap]
      refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
      exact inj_of_order (f := keyM vm V.size VG LK ps PM) hso hk (List.mem_range.1 hx)
        (List.mem_range.1 hy) e
    have hsort := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab)
        (of_decide_eq_true hbc)))
      (fun a b => by
        rcases le_total a b with h | h <;> simp [h])
      (c.pts.toList.map (CFSG.RankThree.Native.keyA V.size ps))
    have hnd' := (List.mergeSort_perm (c.pts.toList.map (CFSG.RankThree.Native.keyA V.size ps))
      (fun a b : ℕ => decide (a ≤ b))).nodup_iff.2 hnd
    exact (hsort.and hnd').imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (of_decide_eq_true h1) h2

end CFSG.RankThree.Native.F2

end
