
module

public import CFSG.Sporadic.Co1.Module.Forms
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Perm.Chain

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem sum_testBit (x m : ℕ) :
    (∑ j ∈ Finset.range m, (if x.testBit j then (1 : ZMod 2) else 0)) =
      if (List.range m).foldl (fun acc j => acc ^^ x.testBit j) false then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    cases (List.range m).foldl (fun acc j => acc ^^ x.testBit j) false <;>
      cases x.testBit m <;> decide

theorem dot_toVecD (a b : ℕ) :
    toVecD 24 a ⬝ᵥ toVecD 24 b = if parity24 (a &&& b) then 1 else 0 := by
  have h : ∀ j : Fin 24, toVecD 24 a j * toVecD 24 b j =
      if (a &&& b).testBit j.val then 1 else 0 := by
    intro j
    simp only [toVecD, Nat.testBit_and]
    cases a.testBit j.val <;> cases b.testBit j.val <;> simp
  simp only [dotProduct, h]
  rw [Fin.sum_univ_eq_sum_range (fun j => if (a &&& b).testBit j then (1 : ZMod 2) else 0) 24,
    sum_testBit]
  rfl

theorem q₀_toVecD (c : ℕ) : q₀ (toVecD 24 c) = if q0N c then 1 else 0 := by
  unfold q₀ q0N Qm
  rw [Matrix.dotProduct_mulVec, ← toVecD_vecMulN, dot_toVecD]

theorem orbitOK_v₂ :
    vOrbitOK 24 98280 dat.colsA dat.colsB (orbitOf 2 98280) = true :=
  co1BaseFacts.orbit

theorem inPts_iff
    (w : ℕ) (hw : w < 2 ^ 24) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = true ↔
      toVecD 24 w ∈ MulAction.orbit Jmat v₂ := by
  rw [orbit_v₂_eq]
  obtain ⟨-, hfacts⟩ := vOrbitOK_facts orbitOK_v₂
  constructor
  · intro h
    simp only [inPts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact ⟨_, h.1, by rw [orbitVec, h.2]⟩
  · rintro ⟨i, hi, e⟩
    have hi' : i < 98280 := hi
    have := toVecD_injective (hfacts i hi').1 hw e
    simp only [inPts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [← this, (hfacts i hi').2.1]
    exact ⟨hi', rfl⟩

def tyOrb : ℕ → Set Vec24
  | 0 => {0}
  | 1 => MulAction.orbit Jmat v₄
  | 2 => MulAction.orbit Jmat v₃
  | _ => MulAction.orbit Jmat v₂

theorem tyOrb_disjoint
    {j k : ℕ} (hj : j < 4) (hk : k < 4) (hjk : j ≠ k) {z : Vec24}
    (hzj : z ∈ tyOrb j) (hzk : z ∈ tyOrb k) : False := by
  have d23 := Set.disjoint_left.1 disjoint_orbit_v₂_v₃
  have d24 := Set.disjoint_left.1 disjoint_orbit_v₂_v₄
  have d34 := Set.disjoint_left.1 disjoint_orbit_v₃_v₄
  have z2 := zero_not_mem_orbit v₂_ne_zero
  have z3 := zero_not_mem_orbit v₃_ne_zero
  have z4 := zero_not_mem_orbit v₄_ne_zero
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
  simp only [tyOrb, Set.mem_singleton_iff] at hzj hzk
  · exact absurd rfl hjk
  · subst hzj; exact z4 hzk
  · subst hzj; exact z3 hzk
  · subst hzj; exact z2 hzk
  · subst hzk; exact z4 hzj
  · exact absurd rfl hjk
  · exact d34 hzk hzj
  · exact d24 hzk hzj
  · subst hzk; exact z3 hzj
  · exact d34 hzj hzk
  · exact absurd rfl hjk
  · exact d23 hzk hzj
  · subst hzk; exact z2 hzj
  · exact d24 hzj hzk
  · exact d23 hzj hzk
  · exact absurd rfl hjk

theorem tyLab_lt (pts : Array ℕ) (pos : Array UInt32) (n w : ℕ) : tyLab pts pos n w < 4 := by
  unfold tyLab; split_ifs <;> omega

theorem tyLab_spec
    (w : ℕ) (hw : w < 2 ^ 24) (j : ℕ) (hj : j < 4) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = j ↔
      toVecD 24 w ∈ tyOrb j := by
  have hz0 : w = 0 ↔ toVecD 24 w = 0 := by
    constructor
    · rintro rfl; exact toVecD_zero 24
    · intro h; exact toVecD_injective hw (by norm_num) (h.trans (toVecD_zero 24).symm)
  have hq : q0N w = true ↔ q₀ (toVecD 24 w) = 1 := by
    rw [q₀_toVecD]; cases q0N w <;> simp
  have h2 := inPts_iff w hw
  have h3 := q₀_eq_one_iff_mem_orbit (toVecD 24 w)
  have hA : ∀ k, tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = k →
      toVecD 24 w ∈ tyOrb k := by
    intro k hk
    unfold tyLab at hk
    split_ifs at hk with h0 hq0 hin
    · subst hk; exact hz0.1 h0
    · subst hk; exact h3.1 (hq.1 hq0)
    · subst hk; exact h2.1 hin
    · subst hk
      have hq' : q₀ (toVecD 24 w) = 0 := by
        rw [q₀_toVecD]; simp [hq0]
      have hne : toVecD 24 w ≠ 0 := fun h => h0 (hz0.2 h)
      have hmem : toVecD 24 w ∈ {v : Vec24 | q₀ v = 0 ∧ v ≠ 0} := ⟨hq', hne⟩
      rw [singular_eq_union] at hmem
      rcases hmem with h | h
      · exact absurd (h2.2 h) hin
      · exact h
  constructor
  · intro h; exact hA j h
  · intro hz
    by_contra hne
    exact tyOrb_disjoint (tyLab_lt _ _ _ _) hj hne (hA _ rfl) hz

theorem labCheck_spec {D : VecData} (h : labCheck D = true) :
    ∀ p < D.n, (labs D)[p]! = tyLab (O D).pts (posTable D.d (O D).pts) D.n
      ((O D).pts[0]! ^^^ (O D).pts[p]!) := by
  intro p hp
  unfold labCheck at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h p hp

theorem orbit_Co1_eq (v : Vec24) :
    MulAction.orbit NativeSporadic.Co1 v = MulAction.orbit Jmat v :=
  range_co1Act v

theorem orbit_smul_mem (g : NativeSporadic.Co1) {a t : Vec24}
    (ht : t ∈ MulAction.orbit NativeSporadic.Co1 a) :
    g • t ∈ MulAction.orbit NativeSporadic.Co1 a := by
  obtain ⟨h, rfl⟩ := ht
  exact ⟨g * h, mul_smul g h a⟩

def tyOrbC : ℕ → Set Vec24
  | 0 => {0}
  | 1 => MulAction.orbit NativeSporadic.Co1 v₄
  | 2 => MulAction.orbit NativeSporadic.Co1 v₃
  | _ => MulAction.orbit NativeSporadic.Co1 v₂

theorem tyOrbC_eq (j : ℕ) : tyOrbC j = tyOrb j := by
  match j with
  | 0 => rfl
  | 1 => exact orbit_Co1_eq v₄
  | 2 => exact orbit_Co1_eq v₃
  | j + 3 => exact orbit_Co1_eq v₂

def cls (j : ℕ) : Set Vec24 :=
  {y | y ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧ v₂ + y ∈ tyOrbC j}

theorem runWith_map {α β : Type*} (mul : α → α → α) (pow : α → ℕ → α) (mul' : β → β → β)
    (pow' : β → ℕ → β) (φ : α → β) (hmul : ∀ a b, φ (mul a b) = mul' (φ a) (φ b))
    (hpow : ∀ a e, φ (pow a e) = pow' (φ a) e) :
    ∀ (prog : List Instr) (regs : ℕ → α) (r : ℕ),
      φ (runWith mul pow prog regs r) = runWith mul' pow' prog (fun r => φ (regs r)) r := by
  intro prog
  induction prog with
  | nil => intro regs r; rfl
  | cons ins prog ih =>
    intro regs r
    cases ins with
    | mu i j k =>
      simp only [runWith]
      rw [ih]
      congr 1
      funext s
      simp only [upd]
      split_ifs
      · exact hmul _ _
      · rfl
    | pwr e i k =>
      simp only [runWith]
      rw [ih]
      congr 1
      funext s
      simp only [upd]
      split_ifs
      · exact hpow _ _
      · rfl
    | iv i k =>
      simp only [runWith]
      rw [ih]

theorem treeCheckV_spec {f : ℕ → ℕ → ℕ} {L par lab : Array ℕ}
    (h : treeCheckV f L par lab = true) :
    0 < L.size ∧ ∀ k < L.size, k = 0 ∨
      (par[k]! < k ∧ lab[k]! < 2 ∧ L[k]! = f lab[k]! L[par[k]!]!) := by
  unfold treeCheckV at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun k hk => ?_⟩
  rcases h.2 k hk with h0 | ⟨⟨h1, h2⟩, h3⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, h2, h3⟩

theorem distinctB_spec {L : Array ℕ} (h : distinctB L = true) :
    ∀ i < L.size, ∀ j < i, L[i]! ≠ L[j]! := by
  unfold distinctB at h
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  exact fun i hi j hj => h i hi j hj

theorem allLtB_spec {L : Array ℕ} {b : ℕ} (h : allLtB L b = true) :
    ∀ k < L.size, L[k]! < b := by
  unfold allLtB at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

def adjSet (x y : Vec24) : Set Vec24 :=
  {w | w ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
    x + w ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
    w + y ∈ MulAction.orbit NativeSporadic.Co1 v₂}

theorem adjSet_smul_mem {g : NativeSporadic.Co1} {x y : Vec24} (hx : g • x = x) (hy : g • y = y)
    {t : Vec24} (ht : t ∈ adjSet x y) : g • t ∈ adjSet x y := by
  obtain ⟨ht1, ht2, ht3⟩ := ht
  refine ⟨orbit_smul_mem g ht1, ?_, ?_⟩
  · have : x + g • t = g • (x + t) := by rw [smul_add, hx]
    rw [this]; exact orbit_smul_mem g ht2
  · have : g • t + y = g • (t + y) := by rw [smul_add, hy]
    rw [this]; exact orbit_smul_mem g ht3

theorem inO_iff
    (w : ℕ) (hw : w < 2 ^ 24) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = true ↔
      toVecD 24 w ∈ MulAction.orbit NativeSporadic.Co1 v₂ := by
  rw [orbit_Co1_eq]; exact inPts_iff w hw

theorem mclCheckT_spec
    {f : ℕ → ℕ → ℕ} {x0 u w0 : ℕ} {L par lab : Array ℕ}
    (hx0 : x0 < 2 ^ 24) (hu : u < 2 ^ 24) (hw0 : w0 < 2 ^ 24)
    (h : mclCheckT (orbitOf 2 98280) f x0 u w0 L par lab = true) {m₁ m₂ : NativeSporadic.Co1}
    (hf : ∀ l < 2, ∀ x, (if l = 0 then m₁ else m₂) • toVecD 24 x = toVecD 24 (f l x)) :
    toVecD 24 x0 ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      toVecD 24 (x0 ^^^ u) ∈ MulAction.orbit NativeSporadic.Co1 v₂ ∧
      toVecD 24 x0 + toVecD 24 (x0 ^^^ u) ∈ MulAction.orbit NativeSporadic.Co1 v₃ ∧
      Subgroup.closure {m₁, m₂} ≤ MulAction.stabilizer NativeSporadic.Co1 (toVecD 24 x0) ⊓
        MulAction.stabilizer NativeSporadic.Co1 (toVecD 24 (x0 ^^^ u)) ∧
      toVecD 24 w0 ∈ adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)) ∧
      (∀ w ∈ adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)),
        ∃ g ∈ Subgroup.closure {m₁, m₂}, g • toVecD 24 w0 = w) ∧
      (adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u))).ncard = 275 := by
  unfold mclCheckT at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hxy : x0 ^^^ u < 2 ^ 24 := Nat.xor_lt_two_pow hx0 hu
  have key := inO_iff
  have hXo : toVecD 24 x0 ∈ MulAction.orbit NativeSporadic.Co1 v₂ := (key x0 hx0).1 h1
  have hYo : toVecD 24 (x0 ^^^ u) ∈ MulAction.orbit NativeSporadic.Co1 v₂ :=
    (key _ hxy).1 h2
  have hXY : toVecD 24 x0 + toVecD 24 (x0 ^^^ u) = toVecD 24 u := by
    rw [toVecD_xor, ← add_assoc, vec_add_self, zero_add]
  have hq : q₀ (toVecD 24 u) = 1 := by
    rw [q₀_toVecD]; simp [h3]
  have hu3 : toVecD 24 x0 + toVecD 24 (x0 ^^^ u) ∈ MulAction.orbit NativeSporadic.Co1 v₃ := by
    rw [hXY, orbit_Co1_eq]; exact (q₀_eq_one_iff_mem_orbit _).1 hq
  have hm1 : m₁ • toVecD 24 x0 = toVecD 24 x0 := by
    have := hf 0 (by norm_num) x0
    simpa [h4] using this
  have hm1' : m₁ • toVecD 24 (x0 ^^^ u) = toVecD 24 (x0 ^^^ u) := by
    have := hf 0 (by norm_num) (x0 ^^^ u)
    simpa [h5] using this
  have hm2 : m₂ • toVecD 24 x0 = toVecD 24 x0 := by
    have := hf 1 (by norm_num) x0
    simpa [h6] using this
  have hm2' : m₂ • toVecD 24 (x0 ^^^ u) = toVecD 24 (x0 ^^^ u) := by
    have := hf 1 (by norm_num) (x0 ^^^ u)
    simpa [h7] using this
  have hKle : Subgroup.closure {m₁, m₂} ≤ MulAction.stabilizer NativeSporadic.Co1 (toVecD 24 x0) ⊓
      MulAction.stabilizer NativeSporadic.Co1 (toVecD 24 (x0 ^^^ u)) := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨hm1, hm1'⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨hm2, hm2'⟩
  have hmK : ∀ l < 2, (if l = 0 then m₁ else m₂) ∈ Subgroup.closure {m₁, m₂} := by
    intro l hl
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨hLpos, hL⟩ := treeCheckV_spec h14
  have hreach : ∀ k < L.size, ∃ g ∈ Subgroup.closure {m₁, m₂},
      g • toVecD 24 w0 = toVecD 24 L[k]! := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases hL k hk with h0 | ⟨hp, hl, he⟩
      · subst h0
        exact ⟨1, Subgroup.one_mem _, by rw [one_smul, h11]⟩
      · obtain ⟨g', hg'K, hg'⟩ := ih _ hp (lt_trans hp hk)
        refine ⟨(if lab[k]! = 0 then m₁ else m₂) * g', Subgroup.mul_mem _ (hmK _ hl) hg'K, ?_⟩
        rw [mul_smul, hg', hf _ hl, ← he]
  have hWadj : toVecD 24 w0 ∈ adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)) := by
    refine ⟨(key w0 hw0).1 h8, ?_, ?_⟩
    · rw [← toVecD_xor]; exact (key _ (Nat.xor_lt_two_pow hx0 hw0)).1 h9
    · rw [← toVecD_xor]; exact (key _ (Nat.xor_lt_two_pow hw0 hxy)).1 h10
  have hinv : ∀ g ∈ Subgroup.closure {m₁, m₂}, ∀ t ∈ adjSet (toVecD 24 x0)
      (toVecD 24 (x0 ^^^ u)), g • t ∈ adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)) :=
    fun g hg t ht => adjSet_smul_mem (hKle hg).1 (hKle hg).2 ht
  have hcover : ∀ t ∈ adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)),
      ∃ k < L.size, t = toVecD 24 L[k]! := by
    rintro t ⟨ht1, ht2, ht3⟩
    rw [orbit_Co1_eq, orbit_v₂_eq] at ht1
    obtain ⟨p, hp, rfl⟩ := ht1
    have hp' : p < 98280 := hp
    have hpt : (orbitOf 2 98280).pts[p]! < 2 ^ 24 := ((vOrbitOK_facts orbitOK_v₂).2 p hp').1
    have e1 : toVecD 24 x0 + orbitVec 2 98280 p =
        toVecD 24 (x0 ^^^ (orbitOf 2 98280).pts[p]!) := by rw [toVecD_xor]; rfl
    have e2 : orbitVec 2 98280 p + toVecD 24 (x0 ^^^ u) =
        toVecD 24 ((orbitOf 2 98280).pts[p]! ^^^ (x0 ^^^ u)) := by
      rw [toVecD_xor 24 ((orbitOf 2 98280).pts[p]!) (x0 ^^^ u)]; rfl
    rw [e1] at ht2
    rw [e2] at ht3
    have a1 := (key _ (Nat.xor_lt_two_pow hx0 hpt)).2 ht2
    have a2 := (key _ (Nat.xor_lt_two_pow hpt hxy)).2 ht3
    rcases h16 p hp' with h | h
    · rw [a1, a2] at h
      exact absurd h (by decide)
    · rw [Array.contains_iff_mem] at h
      obtain ⟨k, hk, hkp⟩ := Array.mem_iff_getElem.1 h
      refine ⟨k, hk, ?_⟩
      rw [getElem!_pos L k hk, hkp]
      rfl
  have hadj_eq : adjSet (toVecD 24 x0) (toVecD 24 (x0 ^^^ u)) =
      (fun k => toVecD 24 L[k]!) '' {k | k < L.size} := by
    ext t
    constructor
    · intro ht
      obtain ⟨k, hk, rfl⟩ := hcover t ht
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨g, hgK, hg⟩ := hreach k hk
      have := hinv g hgK _ hWadj
      rw [hg] at this
      exact this
  have hLlt := allLtB_spec h13
  have hinjOn : Set.InjOn (fun k => toVecD 24 L[k]!) {k | k < L.size} := by
    intro i hi j hj hij
    have hi' : i < L.size := hi
    have hj' : j < L.size := hj
    have hEq : L[i]! = L[j]! := toVecD_injective (hLlt i hi') (hLlt j hj') hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact distinctB_spec h15 j hj' i hlt hEq.symm
    · exact distinctB_spec h15 i hi' j hlt hEq
  refine ⟨hXo, hYo, hu3, hKle, hWadj, ?_, ?_⟩
  · intro w hw
    rw [hadj_eq] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    exact hreach k hk
  · rw [hadj_eq, Set.InjOn.ncard_image hinjOn, h12]
    exact Set.ncard_Iio_nat 275

noncomputable def coeMat : NativeSporadic.Co1 →* Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  (Submonoid.subtype _).comp (Units.coeHom _)

theorem coeMat_apply (g : NativeSporadic.Co1) :
    coeMat g = (g.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) := rfl

theorem mcl_matrix (r : ℕ) : ∃ m : NativeSporadic.Co1,
    (m.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) =
      rowsMatrix 24 (runWith (mulRows 24) (powRows 24) mclProg mclRegs r) := by
  obtain ⟨a, ha⟩ := exists_co1_matA
  obtain ⟨b, hb⟩ := exists_co1_matB
  let regsG : ℕ → NativeSporadic.Co1 := fun r => if r = 1 then a else if r = 2 then b else 1
  refine ⟨runWith (· * ·) (· ^ ·) mclProg regsG r, ?_⟩
  have h1 := runWith_map (· * ·) (· ^ ·) (· * ·) (· ^ ·) coeMat (map_mul coeMat) (map_pow coeMat)
    mclProg regsG r
  have h2 := runWith_map (mulRows 24) (powRows 24) (· * ·) (· ^ ·) (rowsMatrix 24)
    (rowsMatrix_mulRows 24) (rowsMatrix_powRows 24) mclProg mclRegs r
  have h3 : (fun s => coeMat (regsG s)) = fun s => rowsMatrix 24 (mclRegs s) := by
    funext s
    by_cases hs1 : s = 1
    · subst hs1; simp only [regsG, mclRegs, ite_true, coeMat_apply]; exact ha
    · by_cases hs2 : s = 2
      · subst hs2; simp only [regsG, mclRegs, ite_true, coeMat_apply]; exact hb
      · simp only [regsG, mclRegs, hs1, hs2, ite_false, map_one, rowsMatrix_idRows]
  rw [← coeMat_apply, h1, h2, h3]

theorem act_packed (m : NativeSporadic.Co1) (R : Array ℕ)
    (hm : (m.val.val : Matrix (Fin 24) (Fin 24) (ZMod 2)) = rowsMatrix 24 R) (x : ℕ) :
    m • toVecD 24 x = toVecD 24 (vecMulN 24 (transposeRows 24 R) x) := by
  rw [← rowsMatrix_mulVec, ← hm]; rfl

end CFSG.Sporadic.Co1.Module.Pairs
