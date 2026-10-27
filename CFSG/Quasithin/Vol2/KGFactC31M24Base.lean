module

public import CFSG.Quasithin.Vol2.KGFactC31M24Ref
public import CFSG.Quasithin.Vol2.KGFactC31Fix
public import CFSG.Quasithin.Vol2.KGFactC31OrbSound
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31 CFSG.Sporadic.Mathieu

abbrev G₀ : Type := ↥NativeSporadic.M24

theorem hn24 : (24 : ℕ) < 2 ^ 32 := by norm_num

theorem hgens : ∀ l, gensG l ∈ NativeSporadic.M24 := fun l => by
  rw [← m24Certificate_originalSubgroup]
  unfold gensG
  split_ifs
  · exact m24_gens_mem _ (by simp)
  · exact m24_gens_mem _ (by simp)

theorem hrep : ∀ l, Rep 24 (gensT l) (gensG l) := fun l => by
  unfold gensT gensG
  split_ifs
  · exact rep_toTable hn24 _
  · exact rep_toTable hn24 _

@[expose] def elt (w : List ℤ) : G₀ := ⟨wordG gensG w, wordG_mem_of _ hgens w⟩

theorem rep_elt (w : List ℤ) : Rep 24 (wordT 24 gensT w) ((elt w : G₀) : Equiv.Perm (Fin 24)) :=
  Rep.wordT hn24 w fun l _ => hrep l

@[expose] noncomputable def b0 : Equiv.Perm (Fin 24) := (elt (oW.headD []) : G₀)

@[expose] noncomputable def b1 : Equiv.Perm (Fin 24) := (elt (u6W.headD []) : G₀)

theorem rep_b0 : Rep 24 b0T b0 := rep_elt _

theorem rep_b1 : Rep 24 b1T b1 := rep_elt _

theorem b0_eq : b0 = m24Rep2 :=
  (tblEq_iff_eq rep_b0 (rep_toTable hn24 _)).mp c_b0

theorem b1_eq : b1 = m24Rep1 :=
  (tblEq_iff_eq rep_b1 (rep_toTable hn24 _)).mp c_b1

theorem closure_size_le :
    ∀ r ∈ m24InvReps, (Native.conjClosure 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
      (toTable r) 40000).1.size ≤ (conjClass m24Certificate.originalSubgroup r).ncard := by
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  refine (exists_conj_of_repsOK hn24 m24Certificate m24Certificate_check
    (pairTables_spec hn24 hA hB) 1 (fun h hh => by simpa using hh) (by norm_num) m24InvReps
    ?_ 40000 hok).2
  intro r hr
  rw [m24InvReps_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨by simpa using hr1, hro1⟩
  · exact ⟨by simpa using hr2, hro2⟩

theorem centralizerIn_b0 :
    centralizerIn NativeSporadic.M24 b0 = m24CentQ2.originalSubgroup := by
  obtain ⟨-, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨-, -, hK, hKc, -⟩ := m24_rep_data2
  rw [m24InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [b0_eq, ← m24Certificate_originalSubgroup]
  refine centralizerIn_eq_of_le _ _ hK (c := 11385) ?_ ?_
  · rw [← hsz.2]
    exact closure_size_le _ (by rw [m24InvReps_eq]; simp)
  · rw [hKc, m24Certificate_originalSubgroup, m24_card]

theorem centralizerIn_b1 :
    centralizerIn NativeSporadic.M24 b1 = m24CentQ1.originalSubgroup := by
  obtain ⟨-, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨-, -, hK, hKc, -⟩ := m24_rep_data1
  rw [m24InvReps_eq] at hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [b1_eq, ← m24Certificate_originalSubgroup]
  refine centralizerIn_eq_of_le _ _ hK (c := 31878) ?_ ?_
  · rw [← hsz.1]
    exact closure_size_le _ (by rw [m24InvReps_eq]; simp)
  · rw [hKc, m24Certificate_originalSubgroup, m24_card]

theorem card_eq_countP_of_centralizerIn {b : Equiv.Perm (Fin 24)} {Q : RawSchreierDatum 24}
    (hQ : ValidSchreier Q) (hC : centralizerIn NativeSporadic.M24 b = Q.originalSubgroup)
    {f : Table → Bool} {P : Equiv.Perm (Fin 24) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 24 T g → (f T = true ↔ P g)) (hPb : ∀ g, P g → g * b = b * g) :
    Nat.card {x : NativeSporadic.M24 // P x} = (allTables Q).countP f := by
  have hQM : Q.originalSubgroup ≤ NativeSporadic.M24 := hC ▸ inf_le_left
  have hmem : ∀ g, P g → g ∈ NativeSporadic.M24 → g ∈ Q.originalSubgroup := fun g hP hg => by
    rw [← hC]
    exact mem_centralizerIn.mpr ⟨hg, hPb g hP⟩
  rw [countP_eq_of_forall₂ (forall₂_allTables hn24 Q) (q := fun g => decide (P g))
    (fun T g hT _ => by rw [hfP T g hT, decide_eq_true_iff]), List.countP_reverse,
    ← card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
      (mem_enumeration_iff Q hQ) P]
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x.1, hmem x.1 x.2 x.1.2⟩, x.2⟩
      invFun := fun x => ⟨⟨x.1, hQM x.1.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_eq_countP_cb0
    {f : Table → Bool}
    {P : Equiv.Perm (Fin 24) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 24 T g → (f T = true ↔ P g)) (hPb : ∀ g, P g → g * b0 = b0 * g) :
    Nat.card {x : NativeSporadic.M24 // P x} = cb0T.countP f :=
  card_eq_countP_of_centralizerIn m24_oddcore_cent2.1 centralizerIn_b0 hfP hPb

theorem card_eq_countP_cb1
    {f : Table → Bool}
    {P : Equiv.Perm (Fin 24) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 24 T g → (f T = true ↔ P g)) (hPb : ∀ g, P g → g * b1 = b1 * g) :
    Nat.card {x : NativeSporadic.M24 // P x} = cb1T.countP f :=
  card_eq_countP_of_centralizerIn m24_oddcore_cent1.1 centralizerIn_b1 hfP hPb

theorem forall₂_words (ws : List (List ℤ)) :
    List.Forall₂ (Rep 24) (ws.map (wordT 24 gensT))
      (ws.map fun w => ((elt w : G₀) : Equiv.Perm (Fin 24))) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (rep_elt w) ih

theorem commT_b0_of_mem
    {T : Table} (hT : T ∈ cb0T) :
    commT 24 b0T T = true := by
  obtain ⟨g, hg, hTg⟩ := exists_rep_of_mem (forall₂_allTables hn24 m24CentQ2) hT
  rw [List.mem_reverse, mem_enumeration_iff _ m24_oddcore_cent2.1, ← centralizerIn_b0] at hg
  rw [commT_iff rep_b0 hTg]
  exact (mem_centralizerIn.mp hg).2.symm

theorem card_le_cosetCount
    {f : Table → Bool}
    {P : Equiv.Perm (Fin 24) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep 24 T g → (f T = true ↔ P g)) {rsT : List Table}
    {rsG : List (Equiv.Perm (Fin 24))} (hrs : List.Forall₂ (Rep 24) rsT rsG)
    (hrsM : ∀ r ∈ rsG, r ∈ NativeSporadic.M24)
    (hP : ∀ g ∈ NativeSporadic.M24, P g → ∃ r ∈ rsG, g * b0 * g⁻¹ = r * b0 * r⁻¹) :
    Nat.card {g : NativeSporadic.M24 // P g} ≤ cosetCount 24 cb0T rsT f := by
  classical
  refine (card_le_sum_coset b0 rsG P hP hrsM).trans (le_of_eq ?_)
  rw [cosetCount]
  refine (sum_map_eq_of_forall₂ hrs fun rT r hr _ => ?_).symm
  rw [card_eq_countP_cb0 (P := fun c => c * b0 = b0 * c ∧ P (r * c))
    (f := fun c => commT 24 b0T c && f (compT 24 rT c)) (fun T g hT => by
      rw [Bool.and_eq_true, commT_iff rep_b0 hT, hfP _ _ (Rep.compT hr hT)]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩) fun g h => h.1]
  refine List.countP_congr fun c hc => ?_
  rw [commT_b0_of_mem hc, Bool.true_and]

theorem exists_invTab {t : G₀}
    (ht : orderOf t = 2) : ∃ T ∈ invs, Rep 24 T (t : Equiv.Perm (Fin 24)) := by
  obtain ⟨hok, -, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  refine exists_tab_of_repsOK hn24 m24Certificate m24Certificate_check
    (pairTables_spec hn24 hA hB) 1 (fun h hh => by simpa using hh) (by norm_num) m24InvReps
    ?_ 40000 hok (t : Equiv.Perm (Fin 24)) ?_ ?_
  · intro r hr
    rw [m24InvReps_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨by simpa using hr1, hro1⟩
    · exact ⟨by simpa using hr2, hro2⟩
  · rw [inv_one, one_mul, m24Certificate_originalSubgroup]
    exact t.2
  · rw [← ht]
    exact Subgroup.orderOf_coe t

end CFSG.Quasithin.KGC31.M24

end
