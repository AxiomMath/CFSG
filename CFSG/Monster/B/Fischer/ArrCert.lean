module

public import CFSG.Perm.OrbitTree
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Interval.Set.Nat

public section

namespace CFSG.Monster.B.Fischer

@[expose] def PermArrN (n : ℕ) (a : Array ℕ) : Bool :=
  a.size == n && (List.range n).all (fun i => decide (a[i]! < n)) &&
    (List.range n).all (fun j => (List.range n).any fun i => a[i]! == j)

variable {n : ℕ}

theorem PermArrN_lt {a : Array ℕ} (h : PermArrN n a = true) (i : Fin n) : a[(i : ℕ)]! < n := by
  simp only [PermArrN, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.1.2 i i.2

theorem PermArrN_size {a : Array ℕ} (h : PermArrN n a = true) : a.size = n := by
  simp only [PermArrN, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem PermArrN_surj {a : Array ℕ} (h : PermArrN n a = true) (j : Fin n) :
    ∃ i : Fin n, a[(i : ℕ)]! = j := by
  simp only [PermArrN, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨i, hi, e⟩ := h.2 j j.2
  exact ⟨⟨i, hi⟩, e⟩

@[expose] def arrFunN (n : ℕ) (a : Array ℕ) : Fin n → Fin n :=
  fun i => if h : a[(i : ℕ)]! < n then ⟨a[(i : ℕ)]!, h⟩ else i

theorem arrFunN_val {a : Array ℕ} (h : PermArrN n a = true) (i : Fin n) :
    (arrFunN n a i : ℕ) = a[(i : ℕ)]! := by
  simp [arrFunN, PermArrN_lt h i]

theorem arrFunN_bijective {a : Array ℕ} (h : PermArrN n a = true) :
    Function.Bijective (arrFunN n a) := by
  have hs : Function.Surjective (arrFunN n a) := fun j => by
    obtain ⟨i, e⟩ := PermArrN_surj h j
    exact ⟨i, Fin.ext (by rw [arrFunN_val h, e])⟩
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

@[expose] noncomputable def decodeN (n : ℕ) (a : Array ℕ) : Equiv.Perm (Fin n) :=
  if h : PermArrN n a = true then Equiv.ofBijective (arrFunN n a) (arrFunN_bijective h) else 1

theorem decodeN_apply {a : Array ℕ} (h : PermArrN n a = true) (i : Fin n) :
    (decodeN n a i : ℕ) = a[(i : ℕ)]! := by
  unfold decodeN
  simp only [h, ↓reduceDIte, Equiv.ofBijective_apply, arrFunN_val h]

theorem decodeN_inj {a b : Array ℕ} (ha : PermArrN n a = true) (hb : PermArrN n b = true)
    (h : decodeN n a = decodeN n b) : a = b := by
  apply Array.ext (by rw [PermArrN_size ha, PermArrN_size hb])
  intro i hia hib
  have hi : i < n := PermArrN_size ha ▸ hia
  have e := congrArg (fun p : Equiv.Perm (Fin n) => (p ⟨i, hi⟩ : ℕ)) h
  simp only [decodeN_apply ha, decodeN_apply hb] at e
  rwa [getElem!_pos a i hia, getElem!_pos b i hib] at e

@[expose] def amulN (s x : Array ℕ) : Array ℕ := x.map fun i => s[i]!

@[expose] def ainvN (n : ℕ) (s : Array ℕ) : Array ℕ :=
  ((List.range n).map fun j => (List.range n).findIdx fun i => s[i]! == j).toArray

@[expose] def idArrN (n : ℕ) : Array ℕ := (List.range n).toArray

theorem amulN_getElem {s x : Array ℕ} (hx : PermArrN n x = true) (i : Fin n) :
    (amulN s x)[(i : ℕ)]! = s[x[(i : ℕ)]!]! := by
  have hi : (i : ℕ) < x.size := by rw [PermArrN_size hx]; exact i.2
  rw [amulN, getElem!_pos _ _ (by rw [Array.size_map]; exact hi), Array.getElem_map,
    getElem!_pos x (i : ℕ) hi]

theorem PermArrN_amulN {s x : Array ℕ} (hs : PermArrN n s = true) (hx : PermArrN n x = true) :
    PermArrN n (amulN s x) = true := by
  have hval : ∀ i : Fin n, (amulN s x)[(i : ℕ)]! = (decodeN n s (decodeN n x i) : ℕ) := by
    intro i
    rw [amulN_getElem hx, decodeN_apply hs, decodeN_apply hx]
  simp only [PermArrN, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨by rw [amulN, Array.size_map, PermArrN_size hx], fun i hi => ?_⟩, fun j hj => ?_⟩
  · rw [hval ⟨i, hi⟩]
    exact (decodeN n s (decodeN n x ⟨i, hi⟩)).2
  · obtain ⟨i, hi⟩ := (decodeN n s * decodeN n x).surjective ⟨j, hj⟩
    refine ⟨i, i.2, ?_⟩
    rw [hval i]
    exact congrArg Fin.val hi

theorem decodeN_amulN {s x : Array ℕ} (hs : PermArrN n s = true) (hx : PermArrN n x = true) :
    decodeN n (amulN s x) = decodeN n s * decodeN n x := by
  ext i
  rw [decodeN_apply (PermArrN_amulN hs hx), amulN_getElem hx, Equiv.Perm.mul_apply,
    decodeN_apply hs, decodeN_apply hx]

theorem idArrN_get {i : ℕ} (hi : i < n) : (idArrN n)[i]! = i := by
  rw [getElem!_pos _ i (by simp [idArrN, hi])]
  simp [idArrN]

theorem PermArrN_idArrN : PermArrN n (idArrN n) = true := by
  simp only [PermArrN, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.any_eq_true]
  refine ⟨⟨by simp [idArrN], fun i hi => ?_⟩, fun j hj => ⟨j, hj, ?_⟩⟩
  · rw [idArrN_get hi]; exact hi
  · rw [idArrN_get hj]

theorem decodeN_idArrN : decodeN n (idArrN n) = 1 := by
  ext i
  rw [decodeN_apply PermArrN_idArrN, idArrN_get i.2]
  rfl

@[expose] def akeyN (n : ℕ) (a : Array ℕ) : ℕ := Nat.ofDigits n a.toList

theorem akeyN_inj {a b : Array ℕ} (ha : PermArrN n a = true) (hb : PermArrN n b = true)
    (h : akeyN n a = akeyN n b) : a = b := by
  have hn : 1 < n ∨ n ≤ 1 := by omega
  have hla : ∀ l ∈ a.toList, l < n := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < n := by rw [Array.length_toList, PermArrN_size ha] at hi; exact hi
    have := PermArrN_lt ha ⟨i, hi'⟩
    rwa [getElem!_pos a i (by rw [PermArrN_size ha]; exact hi'), ← Array.getElem_toList] at this
  have hlb : ∀ l ∈ b.toList, l < n := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < n := by rw [Array.length_toList, PermArrN_size hb] at hi; exact hi
    have := PermArrN_lt hb ⟨i, hi'⟩
    rwa [getElem!_pos b i (by rw [PermArrN_size hb]; exact hi'), ← Array.getElem_toList] at this
  have hlen : a.toList.length = b.toList.length := by
    rw [Array.length_toList, Array.length_toList, PermArrN_size ha, PermArrN_size hb]
  rcases hn with hn | hn
  · exact Array.toList_inj.1 (Nat.ofDigits_inj_of_len_eq hn hlen hla hlb h)
  ·
    apply Array.ext (by rw [PermArrN_size ha, PermArrN_size hb])
    intro i hia hib
    have hi : i < n := PermArrN_size ha ▸ hia
    have h1 := PermArrN_lt ha ⟨i, hi⟩
    have h2 := PermArrN_lt hb ⟨i, hi⟩
    rw [getElem!_pos a i hia] at h1
    rw [getElem!_pos b i hib] at h2
    omega

structure ArrCert where
  pts : Array (Array ℕ)
  edges : Array (Array ℕ)
  par : Array ℕ
  lab : Array ℕ

@[expose] def arrPointOK (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (valid : Array ℕ → Bool)
    (c : ArrCert) (i : ℕ) : Bool :=
  valid c.pts[i]! && (c.edges[i]!).size == ngen &&
    (List.range ngen).all (fun k => decide (c.edges[i]![k]! < c.pts.size) &&
      c.pts[c.edges[i]![k]!]! == act k c.pts[i]!) &&
    (i == 0 || (decide (c.par[i]! < i) && decide (c.lab[i]! < ngen) &&
      c.pts[i]! == act c.lab[i]! c.pts[c.par[i]!]!))

@[expose] def arrCertOK (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (valid : Array ℕ → Bool)
    (key : Array ℕ → ℕ) (root : Array ℕ) (c : ArrCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    (List.range c.pts.size).all (arrPointOK act ngen valid c) &&
    ((c.pts.toList.map key).mergeSort (fun a b => decide (a ≤ b))).Pairwise (· < ·)

@[expose] def arrBfsStep (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ) (i : ℕ)
    (st : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  (List.range ngen).foldl (fun (acc : Array (Array ℕ) × Array ℕ × Array ℕ ×
      Std.HashMap ℕ ℕ × Array ℕ) k =>
    let (pts, par, lab, idx, row) := acc
    let y := act k pts[i]!
    let ky := key y
    match idx.get? ky with
    | some j => (pts, par, lab, idx, row.push j)
    | none => (pts.push y, par.push i, lab.push k, idx.insert ky pts.size, row.push pts.size))
    (st.1, st.2.1, st.2.2.1, st.2.2.2, #[])

@[expose] def arrBfsLoop (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ) :
    ℕ → ℕ → Array (Array ℕ) → Array (Array ℕ) → Array ℕ → Array ℕ → Std.HashMap ℕ ℕ → ArrCert
  | 0, _, pts, edges, par, lab, _ => ⟨pts, edges, par, lab⟩
  | fuel + 1, i, pts, edges, par, lab, idx =>
    if i < pts.size then
      let (pts', par', lab', idx', row) := arrBfsStep act ngen key i (pts, par, lab, idx)
      arrBfsLoop act ngen key fuel (i + 1) pts' (edges.push row) par' lab' idx'
    else ⟨pts, edges, par, lab⟩

@[expose] def arrBfs (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ)
    (root : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfsLoop act ngen key fuel 0 #[root] #[] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert (key root) 0)

section Soundness

variable {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ} {valid : Array ℕ → Bool}
  {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}

theorem arrCertOK_pointOK (h : arrCertOK act ngen valid key root c = true) {i : ℕ}
    (hi : i < c.pts.size) : arrPointOK act ngen valid c i = true := by
  simp only [arrCertOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1.2 i hi

theorem arrCertOK_pos (h : arrCertOK act ngen valid key root c = true) : 0 < c.pts.size := by
  simp only [arrCertOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem arrCertOK_root (h : arrCertOK act ngen valid key root c = true) : c.pts[0]! = root := by
  simp only [arrCertOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem arrCertOK_valid (h : arrCertOK act ngen valid key root c = true) {i : ℕ}
    (hi : i < c.pts.size) : valid c.pts[i]! = true := by
  have := arrCertOK_pointOK h hi
  simp only [arrPointOK, Bool.and_eq_true] at this
  exact this.1.1.1

theorem arrCertOK_edge (h : arrCertOK act ngen valid key root c = true) {i : ℕ}
    (hi : i < c.pts.size) {k : ℕ} (hk : k < ngen) :
    c.edges[i]![k]! < c.pts.size ∧ c.pts[c.edges[i]![k]!]! = act k c.pts[i]! := by
  have := arrCertOK_pointOK h hi
  simp only [arrPointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at this
  exact this.1.2 k hk

theorem arrCertOK_tree (h : arrCertOK act ngen valid key root c = true) {i : ℕ} (hi0 : 0 < i)
    (hi : i < c.pts.size) :
    c.par[i]! < i ∧ c.lab[i]! < ngen ∧ c.pts[i]! = act c.lab[i]! c.pts[c.par[i]!]! := by
  have := arrCertOK_pointOK h hi
  simp only [arrPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this.2 with h0 | ⟨⟨hp, hl⟩, e⟩
  · omega
  · exact ⟨hp, hl, e⟩

theorem arrCertOK_keys_inj (h : arrCertOK act ngen valid key root c = true) {i j : ℕ}
    (hi : i < c.pts.size) (hj : j < c.pts.size) (hij : key c.pts[i]! = key c.pts[j]!) :
    i = j := by
  simp only [arrCertOK, Bool.and_eq_true] at h
  have hnd : (c.pts.toList.map key).Nodup := by
    have hp := List.mergeSort_perm (c.pts.toList.map key) (fun a b => decide (a ≤ b))
    exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') (of_decide_eq_true h.2))
  have hlen : (c.pts.toList.map key).length = c.pts.size := by simp
  have hgi : (c.pts.toList.map key)[i]'(hlen ▸ hi) = key c.pts[i]! := by
    simp [getElem!_pos c.pts i hi]
  have hgj : (c.pts.toList.map key)[j]'(hlen ▸ hj) = key c.pts[j]! := by
    simp [getElem!_pos c.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans (hij.trans hgj.symm))

end Soundness

section Action

variable {G X : Type*} [Group G] [MulAction G X] {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ}
  {valid : Array ℕ → Bool} {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
  {dec : Array ℕ → X} {gens : ℕ → G}

theorem arrCertOK_closed (h : arrCertOK act ngen valid key root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {i : ℕ} (hi : i < c.pts.size) {s : G} (hs : s ∈ gens '' {k | k < ngen}) :
    ∃ j < c.pts.size, dec c.pts[j]! = s • dec c.pts[i]! := by
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨hj, e⟩ := arrCertOK_edge h hi hk
  exact ⟨_, hj, by rw [e, hact k hk _ (arrCertOK_valid h hi)]⟩

theorem arrCertOK_treeWord (h : arrCertOK act ngen valid key root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {i : ℕ} (hi : i < c.pts.size) :
    CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens i • dec c.pts[0]! =
        dec c.pts[i]! ∧
      CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens i ∈
        Subgroup.closure (gens '' {k | k < ngen}) := by
  refine ⟨CFSG.Perm.treeWord_smul (n := c.pts.size) (P := fun i => dec c.pts[i]!)
    (fun i h0 hi => (arrCertOK_tree h h0 hi).1) (fun i h0 hi => ?_) hi,
    CFSG.Perm.treeWord_mem (n := c.pts.size) (fun i h0 hi => (arrCertOK_tree h h0 hi).1)
      (fun i h0 hi => Subgroup.subset_closure
        (Set.mem_image_of_mem gens (arrCertOK_tree h h0 hi).2.1)) hi⟩
  obtain ⟨hp, hl, e⟩ := arrCertOK_tree h h0 hi
  show dec c.pts[i]! = gens c.lab[i]! • dec c.pts[c.par[i]!]!
  rw [e, hact _ hl _ (arrCertOK_valid h (hp.trans hi))]

theorem orbit_of_arrCertOK (h : arrCertOK act ngen valid key root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a) :
    MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) =
      (fun i => dec c.pts[i]!) '' {i | i < c.pts.size} := by
  have h0 : dec c.pts[0]! = dec root := by rw [arrCertOK_root h]
  rw [← h0]
  exact CFSG.Perm.orbit_closure_eq_image (P := fun i => dec c.pts[i]!) (arrCertOK_pos h)
    (fun i hi s hs => arrCertOK_closed h hact hi hs)
    (τ := CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens)
    (fun i hi => (arrCertOK_treeWord h hact hi).2) (fun i hi => (arrCertOK_treeWord h hact hi).1)

theorem arrCertOK_dec_inj (h : arrCertOK act ngen valid key root c = true)
    (hkey : ∀ a b, valid a = true → valid b = true → dec a = dec b → key a = key b) {i j : ℕ}
    (hi : i < c.pts.size) (hj : j < c.pts.size) (hij : dec c.pts[i]! = dec c.pts[j]!) : i = j :=
  arrCertOK_keys_inj h hi hj (hkey _ _ (arrCertOK_valid h hi) (arrCertOK_valid h hj) hij)

theorem ncard_orbit_of_arrCertOK (h : arrCertOK act ngen valid key root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    (hkey : ∀ a b, valid a = true → valid b = true → dec a = dec b → key a = key b) :
    (MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root)).ncard =
      c.pts.size := by
  rw [orbit_of_arrCertOK h hact,
    Set.InjOn.ncard_image (s := {i | i < c.pts.size}) (f := fun i => dec c.pts[i]!)
      (fun i hi j hj e => arrCertOK_dec_inj h hkey hi hj e)]
  exact Set.ncard_Iio_nat _

end Action

section Order

variable {G : Type*} [Group G] {act : ℕ → Array ℕ → Array ℕ} {ngen : ℕ}
  {valid : Array ℕ → Bool} {key : Array ℕ → ℕ} {root : Array ℕ} {c : ArrCert}
  {dec : Array ℕ → G} {gens : ℕ → G}

theorem card_closure_of_arrCertOK (h : arrCertOK act ngen valid key root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k * dec a)
    (hkey : ∀ a b, valid a = true → valid b = true → dec a = dec b → key a = key b)
    (hroot : dec root = 1) :
    (∀ x : G, x ∈ Subgroup.closure (gens '' {k | k < ngen}) ↔
      ∃ i < c.pts.size, dec c.pts[i]! = x) ∧
    Nat.card (Subgroup.closure (gens '' {k | k < ngen})) = c.pts.size := by
  set H := Subgroup.closure (gens '' {k | k < ngen})
  have horb := orbit_of_arrCertOK (G := G) (X := G) h hact
  rw [hroot] at horb
  have hmem : ∀ x : G, x ∈ H ↔ ∃ i < c.pts.size, dec c.pts[i]! = x := by
    intro x
    constructor
    · intro hx
      have : x ∈ MulAction.orbit H (1 : G) := ⟨⟨x, hx⟩, by simp⟩
      rw [horb] at this
      obtain ⟨i, hi, e⟩ := this
      exact ⟨i, hi, e⟩
    · rintro ⟨i, hi, rfl⟩
      have : dec c.pts[i]! ∈ MulAction.orbit H (1 : G) := by
        rw [horb]
        exact ⟨i, hi, rfl⟩
      obtain ⟨g, hg⟩ := this
      rw [← hg]
      show (g : G) * 1 ∈ H
      rw [mul_one]
      exact g.2
  refine ⟨hmem, ?_⟩
  have hncard := ncard_orbit_of_arrCertOK (G := G) (X := G) h hact hkey
  rw [hroot] at hncard
  have hset : MulAction.orbit H (1 : G) = (H : Set G) := by
    ext x
    rw [SetLike.mem_coe, hmem x, horb]
    rfl
  rw [hset] at hncard
  rw [← hncard]
  exact Nat.card_coe_set_eq _

end Order

end CFSG.Monster.B.Fischer
