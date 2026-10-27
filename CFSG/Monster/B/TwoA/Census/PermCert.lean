module

public import CFSG.Perm.OrbitTree
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Order.Interval.Set.Nat

public section

namespace CFSG.Monster.B.TwoA.Census

@[expose] def PermArr (a : Array ℕ) : Bool :=
  a.size == 24 && (List.range 24).all (fun i => decide (a[i]! < 24)) &&
    (List.range 24).all (fun j => (List.range 24).any fun i => a[i]! == j)

theorem PermArr_lt {a : Array ℕ} (h : PermArr a = true) (i : Fin 24) : a[(i : ℕ)]! < 24 := by
  simp only [PermArr, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h.1.2 i i.2

theorem PermArr_size {a : Array ℕ} (h : PermArr a = true) : a.size = 24 := by
  simp only [PermArr, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem PermArr_surj {a : Array ℕ} (h : PermArr a = true) (j : Fin 24) :
    ∃ i : Fin 24, a[(i : ℕ)]! = j := by
  simp only [PermArr, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨i, hi, e⟩ := h.2 j j.2
  exact ⟨⟨i, hi⟩, e⟩

@[expose] def arrFun (a : Array ℕ) : Fin 24 → Fin 24 :=
  fun i => ⟨a[(i : ℕ)]! % 24, Nat.mod_lt _ (by norm_num)⟩

theorem arrFun_val {a : Array ℕ} (h : PermArr a = true) (i : Fin 24) :
    (arrFun a i : ℕ) = a[(i : ℕ)]! := Nat.mod_eq_of_lt (PermArr_lt h i)

theorem arrFun_bijective {a : Array ℕ} (h : PermArr a = true) :
    Function.Bijective (arrFun a) := by
  have hs : Function.Surjective (arrFun a) := fun j => by
    obtain ⟨i, e⟩ := PermArr_surj h j
    exact ⟨i, Fin.ext (by rw [arrFun_val h, e])⟩
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

@[expose] noncomputable def decode (a : Array ℕ) : Equiv.Perm (Fin 24) :=
  if h : PermArr a = true then Equiv.ofBijective (arrFun a) (arrFun_bijective h) else 1

theorem decode_apply {a : Array ℕ} (h : PermArr a = true) (i : Fin 24) :
    (decode a i : ℕ) = a[(i : ℕ)]! := by
  unfold decode
  simp only [h, ↓reduceDIte, Equiv.ofBijective_apply, arrFun_val h]

theorem decode_inj {a b : Array ℕ} (ha : PermArr a = true) (hb : PermArr b = true)
    (h : decode a = decode b) : a = b := by
  apply Array.ext (by rw [PermArr_size ha, PermArr_size hb])
  intro i hia hib
  have hi : i < 24 := PermArr_size ha ▸ hia
  have e := congrArg (fun p : Equiv.Perm (Fin 24) => (p ⟨i, hi⟩ : ℕ)) h
  simp only [decode_apply ha, decode_apply hb] at e
  rwa [getElem!_pos a i hia, getElem!_pos b i hib] at e

@[expose] def akey (a : Array ℕ) : ℕ := Nat.ofDigits 24 a.toList

theorem akey_inj {a b : Array ℕ} (ha : PermArr a = true) (hb : PermArr b = true)
    (h : akey a = akey b) : a = b := by
  have hla : ∀ l ∈ a.toList, l < 24 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < 24 := by rw [Array.length_toList, PermArr_size ha] at hi; exact hi
    have := PermArr_lt ha ⟨i, hi'⟩
    rwa [getElem!_pos a i (by rw [PermArr_size ha]; exact hi'), ← Array.getElem_toList] at this
  have hlb : ∀ l ∈ b.toList, l < 24 := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < 24 := by rw [Array.length_toList, PermArr_size hb] at hi; exact hi
    have := PermArr_lt hb ⟨i, hi'⟩
    rwa [getElem!_pos b i (by rw [PermArr_size hb]; exact hi'), ← Array.getElem_toList] at this
  have hlen : a.toList.length = b.toList.length := by
    rw [Array.length_toList, Array.length_toList, PermArr_size ha, PermArr_size hb]
  exact Array.toList_inj.1 (Nat.ofDigits_inj_of_len_eq (by norm_num) hlen hla hlb h)

@[expose] def amul (s x : Array ℕ) : Array ℕ := x.map fun i => s[i]!

@[expose] def ainv (s : Array ℕ) : Array ℕ :=
  ((List.range 24).map fun j => (List.range 24).findIdx fun i => s[i]! == j).toArray

@[expose] def aconj (g x : Array ℕ) : Array ℕ := amul (amul g x) (ainv g)

theorem amul_size {s x : Array ℕ} (hx : PermArr x = true) : (amul s x).size = 24 := by
  rw [amul, Array.size_map, PermArr_size hx]

theorem amul_getElem {s x : Array ℕ} (hx : PermArr x = true) (i : Fin 24) :
    (amul s x)[(i : ℕ)]! = s[x[(i : ℕ)]!]! := by
  have hi : (i : ℕ) < x.size := by rw [PermArr_size hx]; exact i.2
  rw [amul, getElem!_pos _ _ (by rw [Array.size_map]; exact hi), Array.getElem_map,
    getElem!_pos x (i : ℕ) hi]

theorem PermArr_amul {s x : Array ℕ} (hs : PermArr s = true) (hx : PermArr x = true) :
    PermArr (amul s x) = true := by
  have hval : ∀ i : Fin 24, (amul s x)[(i : ℕ)]! = (decode s (decode x i) : ℕ) := by
    intro i
    rw [amul_getElem hx, decode_apply hs, decode_apply hx]
  simp only [PermArr, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨amul_size hx, fun i hi => ?_⟩, fun j hj => ?_⟩
  · rw [hval ⟨i, hi⟩]
    exact (decode s (decode x ⟨i, hi⟩)).2
  · obtain ⟨i, hi⟩ := (decode s * decode x).surjective ⟨j, hj⟩
    refine ⟨i, i.2, ?_⟩
    rw [hval i]
    exact congrArg Fin.val hi

theorem decode_amul {s x : Array ℕ} (hs : PermArr s = true) (hx : PermArr x = true) :
    decode (amul s x) = decode s * decode x := by
  ext i
  rw [decode_apply (PermArr_amul hs hx), amul_getElem hx, Equiv.Perm.mul_apply, decode_apply hs,
    decode_apply hx]

theorem ainv_getElem_spec {s : Array ℕ} (hs : PermArr s = true) (j : Fin 24) :
    ∃ h : (ainv s)[(j : ℕ)]! < 24, decode s ⟨(ainv s)[(j : ℕ)]!, h⟩ = j := by
  obtain ⟨i, hi⟩ := PermArr_surj hs j
  have hex : ∃ k ∈ List.range 24, (s[k]! == (j : ℕ)) = true :=
    ⟨(i : ℕ), List.mem_range.2 i.2, by rw [beq_iff_eq, hi]⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  rw [List.length_range] at hlt
  have hget : (ainv s)[(j : ℕ)]! = (List.range 24).findIdx fun i => s[i]! == (j : ℕ) := by
    rw [ainv, getElem!_pos _ _ (by simp), List.getElem_toArray, List.getElem_map,
      List.getElem_range]
  refine ⟨hget ▸ hlt, Fin.ext ?_⟩
  rw [decode_apply hs]
  have hw : ((List.range 24).findIdx fun i => s[i]! == (j : ℕ)) < (List.range 24).length := by
    rw [List.length_range]; exact hlt
  have := List.findIdx_getElem (w := hw)
  simp only [List.getElem_range, beq_iff_eq] at this
  simp only [hget]
  exact this

theorem PermArr_ainv {s : Array ℕ} (hs : PermArr s = true) : PermArr (ainv s) = true := by
  have hsize : (ainv s).size = 24 := by simp [ainv]
  have hval : ∀ j : Fin 24, (ainv s)[(j : ℕ)]! = ((decode s)⁻¹ j : ℕ) := by
    intro j
    obtain ⟨h, e⟩ := ainv_getElem_spec hs j
    conv_rhs => rw [← e]
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  simp only [PermArr, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨hsize, fun i hi => ?_⟩, fun j hj => ?_⟩
  · rw [hval ⟨i, hi⟩]
    exact ((decode s)⁻¹ ⟨i, hi⟩).2
  · refine ⟨(decode s ⟨j, hj⟩ : ℕ), (decode s ⟨j, hj⟩).2, ?_⟩
    rw [hval (decode s ⟨j, hj⟩), Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem decode_ainv {s : Array ℕ} (hs : PermArr s = true) : decode (ainv s) = (decode s)⁻¹ := by
  ext j
  rw [decode_apply (PermArr_ainv hs)]
  obtain ⟨h, e⟩ := ainv_getElem_spec hs j
  conv_rhs => rw [← e]
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem PermArr_aconj {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    PermArr (aconj g x) = true :=
  PermArr_amul (PermArr_amul hg hx) (PermArr_ainv hg)

theorem decode_aconj {g x : Array ℕ} (hg : PermArr g = true) (hx : PermArr x = true) :
    decode (aconj g x) = decode g * decode x * (decode g)⁻¹ := by
  rw [aconj, decode_amul (PermArr_amul hg hx) (PermArr_ainv hg), decode_amul hg hx,
    decode_ainv hg]

structure TreeCert where
  pts : Array (Array ℕ)
  edges : Array (Array ℕ)
  par : Array ℕ
  lab : Array ℕ

@[expose] def pointOK (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ))
    (c : TreeCert) (i : ℕ) : Bool :=
  PermArr c.pts[i]! && (c.edges[i]!).size == gens.size &&
    (List.range gens.size).all (fun k => decide (c.edges[i]![k]! < c.pts.size) &&
      c.pts[c.edges[i]![k]!]! == act gens[k]! c.pts[i]!) &&
    (i == 0 || (decide (c.par[i]! < i) && decide (c.lab[i]! < gens.size) &&
      c.pts[i]! == act gens[c.lab[i]!]! c.pts[c.par[i]!]!))

@[expose] def certOK (act : Array ℕ → Array ℕ → Array ℕ) (gens : Array (Array ℕ))
    (root : Array ℕ) (c : TreeCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    (List.range c.pts.size).all (pointOK act gens c) &&
    ((c.pts.toList.map akey).mergeSort (fun a b => decide (a ≤ b))).Pairwise (· < ·)

section Soundness

variable {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)} {root : Array ℕ}
  {c : TreeCert}

theorem certOK_pointOK (h : certOK act gens root c = true) {i : ℕ} (hi : i < c.pts.size) :
    pointOK act gens c i = true := by
  simp only [certOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1.2 i hi

theorem certOK_pos (h : certOK act gens root c = true) : 0 < c.pts.size := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem certOK_root (h : certOK act gens root c = true) : c.pts[0]! = root := by
  simp only [certOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem certOK_perm (h : certOK act gens root c = true) {i : ℕ} (hi : i < c.pts.size) :
    PermArr c.pts[i]! = true := by
  have := certOK_pointOK h hi
  simp only [pointOK, Bool.and_eq_true] at this
  exact this.1.1.1

theorem certOK_edge (h : certOK act gens root c = true) {i : ℕ} (hi : i < c.pts.size) {k : ℕ}
    (hk : k < gens.size) :
    c.edges[i]![k]! < c.pts.size ∧ c.pts[c.edges[i]![k]!]! = act gens[k]! c.pts[i]! := by
  have := certOK_pointOK h hi
  simp only [pointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at this
  exact this.1.2 k hk

theorem certOK_tree (h : certOK act gens root c = true) {i : ℕ} (hi0 : 0 < i)
    (hi : i < c.pts.size) :
    c.par[i]! < i ∧ c.lab[i]! < gens.size ∧
      c.pts[i]! = act gens[c.lab[i]!]! c.pts[c.par[i]!]! := by
  have := certOK_pointOK h hi
  simp only [pointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this.2 with h0 | ⟨⟨hp, hl⟩, e⟩
  · omega
  · exact ⟨hp, hl, e⟩

theorem certOK_keys_inj (h : certOK act gens root c = true) {i j : ℕ} (hi : i < c.pts.size)
    (hj : j < c.pts.size) (hij : akey c.pts[i]! = akey c.pts[j]!) : i = j := by
  simp only [certOK, Bool.and_eq_true] at h
  have hsorted := h.2
  have hnd : (c.pts.toList.map akey).Nodup := by
    have hp := List.mergeSort_perm (c.pts.toList.map akey) (fun a b => decide (a ≤ b))
    exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') (of_decide_eq_true hsorted))
  have hlen : (c.pts.toList.map akey).length = c.pts.size := by simp
  have hgi : (c.pts.toList.map akey)[i]'(hlen ▸ hi) = akey c.pts[i]! := by
    simp [getElem!_pos c.pts i hi]
  have hgj : (c.pts.toList.map akey)[j]'(hlen ▸ hj) = akey c.pts[j]! := by
    simp [getElem!_pos c.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans (hij.trans hgj.symm))

theorem certOK_inj (h : certOK act gens root c = true) {i j : ℕ} (hi : i < c.pts.size)
    (hj : j < c.pts.size) (hij : decode c.pts[i]! = decode c.pts[j]!) : i = j :=
  certOK_keys_inj h hi hj (by
    rw [decode_inj (certOK_perm h hi) (certOK_perm h hj) hij])

end Soundness

section Action

variable {G : Type*} [Group G] [MulAction G (Equiv.Perm (Fin 24))]
  {act : Array ℕ → Array ℕ → Array ℕ} {gens : Array (Array ℕ)} {gensG : ℕ → G}
  {root : Array ℕ} {c : TreeCert}

@[expose] noncomputable def pt (c : TreeCert) (i : ℕ) : Equiv.Perm (Fin 24) := decode c.pts[i]!

theorem certOK_closed (h : certOK act gens root c = true)
    (hact : ∀ k < gens.size, ∀ a, PermArr a = true → decode (act gens[k]! a) = gensG k • decode a)
    {i : ℕ} (hi : i < c.pts.size) {s : G} (hs : s ∈ gensG '' {k | k < gens.size}) :
    ∃ j < c.pts.size, pt c j = s • pt c i := by
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨hj, e⟩ := certOK_edge h hi hk
  exact ⟨_, hj, by rw [pt, e, hact k hk _ (certOK_perm h hi), pt]⟩

theorem certOK_treeWord (h : certOK act gens root c = true)
    (hact : ∀ k < gens.size, ∀ a, PermArr a = true → decode (act gens[k]! a) = gensG k • decode a)
    {i : ℕ} (hi : i < c.pts.size) :
    CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gensG i • pt c 0 = pt c i ∧
      CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gensG i ∈
        Subgroup.closure (gensG '' {k | k < gens.size}) := by
  refine ⟨CFSG.Perm.treeWord_smul (n := c.pts.size) (P := pt c)
    (fun i h0 hi => (certOK_tree h h0 hi).1) (fun i h0 hi => ?_) hi,
    CFSG.Perm.treeWord_mem (n := c.pts.size) (fun i h0 hi => (certOK_tree h h0 hi).1)
      (fun i h0 hi => Subgroup.subset_closure
        (Set.mem_image_of_mem gensG (certOK_tree h h0 hi).2.1)) hi⟩
  obtain ⟨hp, hl, e⟩ := certOK_tree h h0 hi
  rw [pt, e, hact _ hl _ (certOK_perm h (hp.trans hi)), pt]

theorem orbit_of_certOK (h : certOK act gens root c = true)
    (hact : ∀ k < gens.size, ∀ a, PermArr a = true → decode (act gens[k]! a) = gensG k • decode a) :
    MulAction.orbit (Subgroup.closure (gensG '' {k | k < gens.size})) (decode root) =
      pt c '' {i | i < c.pts.size} := by
  have h0 : pt c 0 = decode root := by rw [pt, certOK_root h]
  rw [← h0]
  exact CFSG.Perm.orbit_closure_eq_image (certOK_pos h)
    (fun i hi s hs => certOK_closed h hact hi hs)
    (τ := CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gensG)
    (fun i hi => (certOK_treeWord h hact hi).2) (fun i hi => (certOK_treeWord h hact hi).1)

theorem ncard_orbit_of_certOK (h : certOK act gens root c = true)
    (hact : ∀ k < gens.size, ∀ a, PermArr a = true → decode (act gens[k]! a) = gensG k • decode a) :
    (MulAction.orbit (Subgroup.closure (gensG '' {k | k < gens.size})) (decode root)).ncard =
      c.pts.size := by
  rw [orbit_of_certOK h hact,
    Set.InjOn.ncard_image (s := {i | i < c.pts.size}) (f := pt c)
      (fun i hi j hj e => certOK_inj h hi hj e)]
  exact Set.ncard_Iio_nat _

end Action

theorem amul_act {gens : Array (Array ℕ)} (hg : ∀ k < gens.size, PermArr gens[k]! = true) :
    ∀ k < gens.size, ∀ a, PermArr a = true →
      decode (amul gens[k]! a) = decode gens[k]! • decode a :=
  fun k hk _a ha => decode_amul (hg k hk) ha

theorem card_closure_of_certOK {gens : Array (Array ℕ)} {root : Array ℕ} {c : TreeCert}
    (hg : ∀ k < gens.size, PermArr gens[k]! = true) (hroot : decode root = 1)
    (h : certOK amul gens root c = true) :
    Nat.card (Subgroup.closure ((fun k => decode gens[k]!) '' {k | k < gens.size})) =
        c.pts.size ∧
      ∀ x : Equiv.Perm (Fin 24),
        x ∈ Subgroup.closure ((fun k => decode gens[k]!) '' {k | k < gens.size}) ↔
        ∃ i < c.pts.size, pt c i = x := by
  set S := (fun k => decode gens[k]!) '' {k | k < gens.size}
  have hact := amul_act hg
  have h0 : pt c 0 = 1 := by rw [pt, certOK_root h, hroot]
  have horb := orbit_of_certOK (gensG := fun k => decode gens[k]!) h hact
  have hcl : ∀ i < c.pts.size, ∀ s ∈ S, ∃ j < c.pts.size, pt c j = s • pt c i :=
    fun i hi s hs => certOK_closed h hact hi hs
  have hτ := fun i (hi : i < c.pts.size) =>
    certOK_treeWord (gensG := fun k => decode gens[k]!) h hact hi
  refine ⟨?_, fun x => ?_⟩
  · have := CFSG.Perm.card_closure_eq_mul (S := S) (P := pt c) (certOK_pos h)
      (fun i hi j hj e => certOK_inj h hi hj e) hcl (τ := fun i => pt c i) h0
      (fun i hi => by rw [← (hτ i hi).1, h0, smul_eq_mul, mul_one]; exact (hτ i hi).2)
      (fun i hi => by rw [h0, smul_eq_mul, mul_one]) (K := ⊥) bot_le bot_le
      (fun i hi s hs j hj e => by
        rw [Subgroup.mem_bot, e, smul_eq_mul, mul_assoc, inv_mul_cancel])
    rw [this, Subgroup.card_bot, mul_one]
  · constructor
    · intro hx
      have hmem : x • pt c 0 ∈ MulAction.orbit (Subgroup.closure S) (pt c 0) := ⟨⟨x, hx⟩, rfl⟩
      rw [h0, ← h0, CFSG.Perm.orbit_closure_eq_image (certOK_pos h) hcl
        (τ := CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) _)
        (fun i hi => (hτ i hi).2) (fun i hi => (hτ i hi).1)] at hmem
      obtain ⟨i, hi, e⟩ := hmem
      refine ⟨i, hi, ?_⟩
      rw [e, h0, smul_eq_mul, mul_one]
    · rintro ⟨i, hi, rfl⟩
      have := (hτ i hi)
      rw [h0, smul_eq_mul, mul_one] at this
      exact this.1 ▸ this.2

end CFSG.Monster.B.TwoA.Census
