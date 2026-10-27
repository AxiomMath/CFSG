module

public import CFSG.Quasithin.Vol2.KGFactC31FrameCheck
public import CFSG.Quasithin.Vol2.KGFactC31Hat
public import CFSG.Quasithin.Vol2.KGFactC31Gen

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Certificates CFSG.Quasithin.KGC31.Native

variable {n : ℕ}

theorem eElt_mem_of_forall {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (c : Fin k → ZMod 2)
    (K : Subgroup (Equiv.Perm (Fin n))) (hK : ∀ i, w i ∈ K) : eElt w c ∈ K := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact Subgroup.pow_mem _ (hK i) _

theorem inSpan_iff (hn : n < 2 ^ 32) {bs : List Table} {gs : List (Equiv.Perm (Fin n))}
    (hbs : List.Forall₂ (Rep n) bs gs) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    inSpan n bs T = true ↔ ∃ c, g = eElt gs.get c := by
  have hbs' : List.Forall₂ (Rep n) bs (List.ofFn gs.get) := by rw [List.ofFn_get]; exact hbs
  exact mem_spanTabs_iff hn hbs' (f := tblEq n T) (P := fun u => g = u)
    fun U u hU => tblEq_iff_eq hT hU

theorem mem_closure_of_span {gs : List (Equiv.Perm (Fin n))} (c : Fin gs.length → ZMod 2) :
    eElt gs.get c ∈ Subgroup.closure {g | g ∈ gs} :=
  eElt_mem_of_forall _ c _ fun i => Subgroup.subset_closure (List.get_mem gs i)

@[expose] def orbList (m : ℕ) (x v : Equiv.Perm (Fin n)) : List (Equiv.Perm (Fin n)) :=
  (List.range m).map fun j => x ^ j * v * x⁻¹ ^ j

theorem forall₂_orbTabs (hn : n < 2 ^ 32) {m : ℕ} {x xi T : Table} {xg v : Equiv.Perm (Fin n)}
    (hx : Rep n x xg) (hxi : Rep n xi xg⁻¹) (hT : Rep n T v) :
    List.Forall₂ (Rep n) (orbTabs n m x xi T) (orbList m xg v) := by
  unfold orbTabs orbList
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun j _ => ?_
  exact Rep.compT (Rep.compT (Rep.powT hn hx j) hT) (Rep.powT hn hxi j)

theorem forall₂_frame (hn : n < 2 ^ 32) {m : ℕ} {x xi T : Table} {xg v : Equiv.Perm (Fin n)}
    (hx : Rep n x xg) (hxi : Rep n xi xg⁻¹) (hT : Rep n T v) {ub : List Table}
    {ug : List (Equiv.Perm (Fin n))} (hub : List.Forall₂ (Rep n) ub ug) :
    List.Forall₂ (Rep n) (ub ++ orbTabs n m x xi T) (ug ++ orbList m xg v) :=
  List.rel_append hub (forall₂_orbTabs hn hx hxi hT)

theorem elabOK_of (hn : n < 2 ^ 32) {bs : List Table} {gs : List (Equiv.Perm (Fin n))}
    (hbs : List.Forall₂ (Rep n) bs gs) (hsq : ∀ g ∈ gs, g * g = 1)
    (hcomm : ∀ g ∈ gs, ∀ h ∈ gs, g * h = h * g) : elabOK n bs = true := by
  unfold elabOK
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun b hb => ?_, fun b hb => List.all_eq_true.mpr fun c hc => ?_⟩
  · obtain ⟨g, hg, hbg⟩ := exists_rep_of_mem hbs hb
    exact (tblEq_iff_eq (Rep.compT hbg hbg) (Rep.idT hn)).mpr (hsq g hg)
  · obtain ⟨g, hg, hbg⟩ := exists_rep_of_mem hbs hb
    obtain ⟨h, hh, hch⟩ := exists_rep_of_mem hbs hc
    exact (tblEq_iff_eq (Rep.compT hbg hch) (Rep.compT hch hbg)).mpr (hcomm g hg h hh)

theorem closure_frame_eq {m : ℕ} (hm : 0 < m) {xg v : Equiv.Perm (Fin n)} (hxm : xg ^ m = 1)
    (ug : List (Equiv.Perm (Fin n))) :
    Subgroup.closure {g | g ∈ ug ∨ ∃ j : ℕ, g = xg ^ j * v * xg⁻¹ ^ j} =
      Subgroup.closure {g | g ∈ ug ++ orbList m xg v} := by
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, List.mem_append, orbList, List.mem_map, List.mem_range]
  constructor
  · rintro (h | ⟨j, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨j % m, Nat.mod_lt _ hm, ?_⟩
      have h1 : xg ^ j = xg ^ (j % m) := by
        conv_lhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul, hxm, one_pow, mul_one]
      rw [inv_pow, inv_pow, h1]
  · rintro (h | ⟨j, -, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, rfl⟩

theorem closure_eq_of_frameCheck (hn : n < 2 ^ 32) {m : ℕ} (hm : 0 < m) {x : Table}
    {ub vs : List Table} {cands : List (List Table)}
    (hchk : frameCheck n m x ub vs cands = true)
    {candG : List (List (Equiv.Perm (Fin n)))}
    (hcands : List.Forall₂ (List.Forall₂ (Rep n)) cands candG)
    {ug : List (Equiv.Perm (Fin n))} (hub : List.Forall₂ (Rep n) ub ug)
    {xg : Equiv.Perm (Fin n)} (hx : Rep n x xg) (hxm : xg ^ m = 1) {T : Table} (hT : T ∈ vs)
    {v : Equiv.Perm (Fin n)} (hv : Rep n T v) (hvU : v ∉ Subgroup.closure {g | g ∈ ug})
    (hsq : ∀ g ∈ ug ++ orbList m xg v, g * g = 1)
    (hcomm : ∀ g ∈ ug ++ orbList m xg v, ∀ h ∈ ug ++ orbList m xg v, g * h = h * g) :
    ∃ cg ∈ candG, Subgroup.closure {g | g ∈ ug ∨ ∃ j : ℕ, g = xg ^ j * v * xg⁻¹ ^ j} =
      Subgroup.closure {g | g ∈ cg} := by
  unfold frameCheck at hchk
  rw [Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hinv, hall⟩ := hchk
  have hxi : Rep n (invT n x) xg⁻¹ := Rep.inv_of_invOK hx hinv
  have hfr := forall₂_frame (m := m) hn hx hxi hv hub
  have h1 := hall T hT
  have hspan : inSpan n ub T = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨c, hc⟩ := (inSpan_iff hn hub hv).mp h
    exact hvU (hc ▸ mem_closure_of_span c)
  rw [hspan, Bool.false_or, elabOK_of hn hfr hsq hcomm, Bool.not_true, Bool.false_or,
    List.any_eq_true] at h1
  obtain ⟨cand, hcand, hok⟩ := h1
  obtain ⟨cg, hcg, hrel⟩ : ∃ cg ∈ candG, List.Forall₂ (Rep n) cand cg :=
    exists_mem_of_forall₂ hcands.flip hcand |>.imp fun _ h => ⟨h.1, h.2⟩
  refine ⟨cg, hcg, ?_⟩
  rw [closure_frame_eq hm hxm]
  unfold orbIs at hok
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
  obtain ⟨hsub, hsup⟩ := hok
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨b, hb, hbg⟩ := exists_tab_of_mem hfr hg
    obtain ⟨c, hc⟩ := (inSpan_iff hn hrel hbg).mp (hsub b hb)
    rw [SetLike.mem_coe, hc]
    exact mem_closure_of_span c
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨b, hb, hbg⟩ := exists_tab_of_mem hrel hg
    obtain ⟨c, hc⟩ := (inSpan_iff hn hfr hbg).mp (hsup b hb)
    rw [SetLike.mem_coe, hc]
    exact mem_closure_of_span c

section Blocks

variable {k : ℕ} {B : Fin k → Finset (Fin n)}

theorem blocksOK_spec {bl : List (List ℕ)} (hbl : bl.length = k)
    (hB : ∀ i : Fin k, ∀ p : Fin n, p ∈ B i ↔ p.val ∈ bl.getD i []) {T : Table}
    {g : Equiv.Perm (Fin n)} (hT : Rep n T g) (h : blocksOK bl T = true) :
    ∀ i, ∃ j, ∀ p ∈ B i, g p ∈ B j := by
  intro i
  unfold blocksOK at h
  rw [List.all_eq_true] at h
  have hi : i.val < bl.length := hbl ▸ i.2
  have h1 := h (bl[i.val]'hi) (List.getElem_mem hi)
  rw [List.any_eq_true] at h1
  obtain ⟨T', hT', h2⟩ := h1
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT'
  refine ⟨⟨j, hbl ▸ hj⟩, fun p hp => ?_⟩
  rw [hB] at hp ⊢
  rw [List.getD_eq_getElem _ _ hi] at hp
  rw [List.getD_eq_getElem _ _ hj]
  rw [List.all_eq_true] at h2
  have h3 := h2 p.val hp
  rw [List.contains_iff_mem] at h3
  rwa [rep_apply hT p] at h3

theorem mem_blockStab_of_blocksOK (hBi : Function.Injective B) {bl : List (List ℕ)}
    (hbl : bl.length = k) (hB : ∀ i : Fin k, ∀ p : Fin n, p ∈ B i ↔ p.val ∈ bl.getD i [])
    {s : ℕ} (hs : ∀ i, (B i).card = s) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (h : blocksOK bl T = true) : g ∈ blockStab B hBi := by
  intro i
  obtain ⟨j, hj⟩ := blocksOK_spec hbl hB hT h i
  refine ⟨j, Finset.eq_of_subset_of_card_le (fun q hq => ?_) ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact hj p hp
  · rw [Finset.card_image_of_injective _ g.injective, hs, hs]

theorem fixesBlocks_iff {bl : List (List ℕ)} (hbl : bl.length = k)
    (hB : ∀ i : Fin k, ∀ p : Fin n, p ∈ B i ↔ p.val ∈ bl.getD i [])
    (hlt : ∀ T ∈ bl, ∀ p ∈ T, p < n) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    fixesBlocks bl T = true ↔ ∀ i, (B i).image g = B i := by
  unfold fixesBlocks
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hi : i.val < bl.length := hbl ▸ i.2
    refine Finset.eq_of_subset_of_card_le (fun q hq => ?_) ?_
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      rw [hB, List.getD_eq_getElem _ _ hi] at hp ⊢
      have h2 := List.all_eq_true.mp (h (bl[i.val]'hi) (List.getElem_mem hi)) p.val hp
      rw [List.contains_iff_mem, rep_apply hT p] at h2
      exact h2
    · rw [Finset.card_image_of_injective _ g.injective]
  · intro h T' hT'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT'
    rw [List.all_eq_true]
    intro p hp
    have hpn : p < n := hlt _ hT' p hp
    have hjk : j < k := hbl ▸ hj
    have hmem : (⟨p, hpn⟩ : Fin n) ∈ B ⟨j, hjk⟩ := by
      rw [hB, List.getD_eq_getElem _ _ hj]
      exact hp
    have h1 : g ⟨p, hpn⟩ ∈ B ⟨j, hjk⟩ := by
      rw [← h ⟨j, hjk⟩]
      exact Finset.mem_image_of_mem g hmem
    rw [hB, List.getD_eq_getElem _ _ hj] at h1
    rw [List.contains_iff_mem, show p = (⟨p, hpn⟩ : Fin n).val from rfl, rep_apply hT]
    exact h1

end Blocks

end CFSG.Quasithin.KGC31

end
