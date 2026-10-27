module

public import Certificates.Kernel.Co2Smith.SteinK0
public import Certificates.Kernel.Co2Smith.SteinK1
public import Certificates.Kernel.Co2Smith.SteinK2
public import Certificates.Kernel.Co2Smith.SteinK3
public import Certificates.Kernel.Co2Smith.SteinK4
public import Certificates.Kernel.Co2Smith.SteinK5
public import Certificates.Kernel.Co2Smith.Root
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native
open CFSG.Fischer CFSG.KC.F2W CFSG.KC.M1F2 CFSG.KC.Co1F2

theorem tb_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

theorem tb_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

theorem tb_xor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i

theorem tb_shl (x n i : Nat) : (Nat.shiftLeft x n).testBit i = (decide (i ≥ n) && x.testBit (i - n)) :=
  Nat.testBit_shiftLeft x

theorem tb_shr (x n i : Nat) : (Nat.shiftRight x n).testBit i = x.testBit (n + i) :=
  Nat.testBit_shiftRight x

theorem tb_M36 (i : Nat) : M36.testBit i = decide (i < 36) := by
  rw [show M36 = 2 ^ 36 - 1 by rfl, Nat.testBit_two_pow_sub_one]

theorem tb_M72 (i : Nat) : M72.testBit i = decide (i < 72) := by
  rw [show M72 = 2 ^ 72 - 1 by rfl, Nat.testBit_two_pow_sub_one]

theorem tb_lo (a : Nat) {q : Nat} (hq : q < 36) : (loF a).testBit q = a.testBit q := by
  rw [loF, tb_land, tb_M36]
  simp [hq]

theorem tb_hi (a : Nat) {q : Nat} (hq : q < 36) : (hiF a).testBit q = a.testBit (q + 36) := by
  rw [hiF, tb_land, tb_M36, tb_shr]
  simp [hq, Nat.add_comm]

theorem tb_mulW6 (A B : Nat) {p : Nat} (hp : p < 36) : (mulW 6 A B).testBit p =
    Nat.rec (motive := fun _ => Bool) false
      (fun k b => ((rowF 6 A (p / 6)).testBit k && B.testBit (k * 6 + p % 6)) ^^ b) 6 := by
  rw [mulW_eq, mulF_eq_orN, testBit_orN_fields (fun i _ => vmF_lt 6 B (rowF 6 A i))]
  simp only [show p < 6 * 6 by omega, decide_true, Bool.true_and]
  exact testBit_vmF 6 B _ _ (Nat.mod_lt _ (by norm_num))

theorem tb_mulW6' (A B : Nat) {p : Nat} (hp : p < 36) : (mulW 6 A B).testBit p =
    ((A.testBit (p / 6 * 6 + 5) && B.testBit (5 * 6 + p % 6)) ^^
      ((A.testBit (p / 6 * 6 + 4) && B.testBit (4 * 6 + p % 6)) ^^
      ((A.testBit (p / 6 * 6 + 3) && B.testBit (3 * 6 + p % 6)) ^^
      ((A.testBit (p / 6 * 6 + 2) && B.testBit (2 * 6 + p % 6)) ^^
      ((A.testBit (p / 6 * 6 + 1) && B.testBit (1 * 6 + p % 6)) ^^
      ((A.testBit (p / 6 * 6 + 0) && B.testBit (0 * 6 + p % 6)) ^^ false)))))) := by
  rw [tb_mulW6 A B hp, ← testBit_rowF 6 A _ 5 (by norm_num), ← testBit_rowF 6 A _ 4 (by norm_num),
    ← testBit_rowF 6 A _ 3 (by norm_num), ← testBit_rowF 6 A _ 2 (by norm_num),
    ← testBit_rowF 6 A _ 1 (by norm_num), ← testBit_rowF 6 A _ 0 (by norm_num)]
  rfl

theorem tb_mul4_lo (a b : Nat) {k : Nat} (hk : k < 36) : (mul4 a b).testBit k =
    ((mulW 6 (loF a) (loF b)).testBit k ^^ (mulW 6 (hiF a) (hiF b)).testBit k) := by
  rw [mul4, tb_lor, tb_land, tb_xor, tb_M36, tb_shl]
  simp [hk, show ¬ k ≥ 36 by omega]

theorem tb_mul4_hi (a b : Nat) {k : Nat} (hk : k < 36) : (mul4 a b).testBit (k + 36) =
    ((mulW 6 (loF a) (hiF b)).testBit k ^^ (mulW 6 (hiF a) (loF b)).testBit k ^^
      (mulW 6 (hiF a) (hiF b)).testBit k) := by
  rw [mul4, tb_lor, tb_land, tb_xor, tb_M36, tb_shl, tb_land, tb_xor, tb_xor, tb_M36]
  simp [hk, show ¬ k + 36 < 36 by omega]

theorem mkF_mul (x0 x1 y0 y1 : Bool) : mkF x0 x1 * mkF y0 y1 =
    mkF (x0 && y0 ^^ x1 && y1) (x0 && y1 ^^ x1 && y0 ^^ x1 && y1) := by
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> rfl

theorem mkF_add (u0 u1 v0 v1 : Bool) : mkF u0 u1 + mkF v0 v1 = mkF (u0 ^^ v0) (u1 ^^ v1) := by
  cases u0 <;> cases u1 <;> cases v0 <;> cases v1 <;> rfl

theorem mkF_inj {u0 u1 v0 v1 : Bool} : mkF u0 u1 = mkF v0 v1 ↔ u0 = v0 ∧ u1 = v1 := by
  cases u0 <;> cases u1 <;> cases v0 <;> cases v1 <;> simp [mkF]

theorem decF_size (a : Nat) : (decF a).size = 36 := Array.size_ofFn

theorem decF_get (a : Nat) {k : Nat} (hk : k < (decF a).size) :
    (decF a)[k] = mkF (a.testBit k) (a.testBit (k + 36)) := by
  simp [decF]

theorem m6Get_dec (a i j : Nat) (h : i * 6 + j < 36) :
    m6Get (decF a) i j = mkF (a.testBit (i * 6 + j)) (a.testBit (i * 6 + j + 36)) := by
  unfold m6Get
  rw [Nat.mul_comm i 6] at h ⊢
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [decF_size]; exact h)]
  simp [decF]

theorem mul_dec (a b : Nat) : m6Mul (decF a) (decF b) = decF (mul4 a b) := by
  apply Array.ext
  · simp [m6Mul, decF_size]
  · intro k h1 h2
    have hk : k < 36 := by simpa [m6Mul] using h1
    rw [decF_get _ h2]
    simp only [m6Mul, Array.getElem_ofFn]
    rw [m6Get_dec a _ _ (by omega), m6Get_dec a _ _ (by omega), m6Get_dec a _ _ (by omega),
      m6Get_dec a _ _ (by omega), m6Get_dec a _ _ (by omega), m6Get_dec a _ _ (by omega),
      m6Get_dec b _ _ (by omega), m6Get_dec b _ _ (by omega), m6Get_dec b _ _ (by omega),
      m6Get_dec b _ _ (by omega), m6Get_dec b _ _ (by omega), m6Get_dec b _ _ (by omega)]
    simp only [mkF_mul, mkF_add]
    rw [tb_mul4_lo a b hk, tb_mul4_hi a b hk]
    simp only [tb_mulW6' _ _ hk]
    have hq : ∀ l < 6, k / 6 * 6 + l < 36 := fun l hl => by omega
    have hr : ∀ l < 6, l * 6 + k % 6 < 36 := fun l hl => by omega
    simp only [tb_lo _ (hq 0 (by norm_num)), tb_lo _ (hq 1 (by norm_num)), tb_lo _ (hq 2 (by norm_num)),
      tb_lo _ (hq 3 (by norm_num)), tb_lo _ (hq 4 (by norm_num)), tb_lo _ (hq 5 (by norm_num)),
      tb_hi _ (hq 0 (by norm_num)), tb_hi _ (hq 1 (by norm_num)), tb_hi _ (hq 2 (by norm_num)),
      tb_hi _ (hq 3 (by norm_num)), tb_hi _ (hq 4 (by norm_num)), tb_hi _ (hq 5 (by norm_num)),
      tb_lo _ (hr 0 (by norm_num)), tb_lo _ (hr 1 (by norm_num)), tb_lo _ (hr 2 (by norm_num)),
      tb_lo _ (hr 3 (by norm_num)), tb_lo _ (hr 4 (by norm_num)), tb_lo _ (hr 5 (by norm_num)),
      tb_hi _ (hr 0 (by norm_num)), tb_hi _ (hr 1 (by norm_num)), tb_hi _ (hr 2 (by norm_num)),
      tb_hi _ (hr 3 (by norm_num)), tb_hi _ (hr 4 (by norm_num)), tb_hi _ (hr 5 (by norm_num))]
    rw [mkF_inj]
    have : Std.Associative (· ^^ · : Bool → Bool → Bool) := ⟨Bool.xor_assoc⟩
    have : Std.Commutative (· ^^ · : Bool → Bool → Bool) := ⟨Bool.xor_comm⟩
    constructor <;> simp only [Bool.xor_false] <;> ac_rfl

theorem decF_inj {a b : Nat} : decF a = decF b ↔ Nat.land a M72 = Nat.land b M72 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [tb_land, tb_land, tb_M72]
    by_cases hp : p < 72
    · simp only [hp, decide_true, Bool.and_true]
      by_cases hp' : p < 36
      · have := congrArg (fun x : Array F4 => x[p]?) h
        simp only [Array.getElem?_eq_getElem (show p < (decF a).size by rw [decF_size]; exact hp'),
          Array.getElem?_eq_getElem (show p < (decF b).size by rw [decF_size]; exact hp'),
          Option.some.injEq, decF_get, mkF_inj] at this
        exact this.1
      · have hq : p - 36 < 36 := by omega
        have := congrArg (fun x : Array F4 => x[p - 36]?) h
        simp only [Array.getElem?_eq_getElem (show p - 36 < (decF a).size by rw [decF_size]; exact hq),
          Array.getElem?_eq_getElem (show p - 36 < (decF b).size by rw [decF_size]; exact hq),
          Option.some.injEq, decF_get, mkF_inj, show p - 36 + 36 = p by omega] at this
        exact this.2
    · simp [hp]
  · intro h
    have hb : ∀ p < 72, a.testBit p = b.testBit p := by
      intro p hp
      have := congrArg (fun x => x.testBit p) h
      simpa [tb_land, tb_M72, hp] using this
    apply Array.ext
    · simp [decF_size]
    · intro k h1 h2
      have hk : k < 36 := by rwa [decF_size] at h1
      rw [decF_get, decF_get, hb k (by omega), hb (k + 36) (by omega)]

theorem beq_dec (a b : Nat) : (decF a == decF b) = eqF a b := by
  unfold eqF
  by_cases h : Nat.land a M72 = Nat.land b M72
  · rw [h, Nat.beq_refl, decF_inj.2 h]
    exact beq_self_eq_true _
  · have h2 : Nat.beq (Nat.land a M72) (Nat.land b M72) = false := by
      cases e : Nat.beq (Nat.land a M72) (Nat.land b M72)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [h2, beq_eq_false_iff_ne]
    exact fun e => h (decF_inj.1 e)

theorem arr_eq_of_codes {a b : Array F4}
    (h : a.toList.map (·.code.val) = b.toList.map (·.code.val)) : a = b := by
  have hc : Function.Injective fun x : F4 => x.code.val := fun x y hxy => by
    cases x
    cases y
    simp only [F4.mk.injEq]
    exact Fin.ext hxy
  exact Array.toList_inj.1 ((List.map_injective_iff.2 hc) h)

theorem elt_eq {r c : Nat} (hr : r < 18) (hc : c < 4) : decF (eltK r c) = stElt r c := by
  have h := elt_k
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact arr_eq_of_codes (h.1 r hr c hc)

theorem one_dec : decF oneF = m6One := by
  have h := elt_k
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact arr_eq_of_codes h.2

@[expose] def dec (p : Nat × Nat) : Array F4 × Array Nat := (decF p.1, unpackR 22 p.2)

theorem dec_dK : dec dK = (m6One, idRows 22) := by
  simp only [dec, dK, one_dec, ← idRows_eq]

theorem params_lt {t c : Nat} (h : c ∈ stParams t) : c < 4 := by
  unfold stParams at h
  split at h <;> simp at h <;> omega

theorem stGens_eq : ∀ B : List Nat, (∀ t ∈ B, t < 18) → stGens B = (gensK B).map dec
  | [], _ => rfl
  | t :: B, hB => by
    have ih := stGens_eq B fun x hx => hB x (List.mem_cons_of_mem _ hx)
    unfold stGens gensK at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, ih, List.map_map]
    refine congrArg (· ++ _) (List.map_congr_left fun c hc => ?_)
    simp only [Function.comp_apply, dec, elt_eq (hB t List.mem_cons_self) (params_lt hc),
      glRootRows_eq]

theorem getD_dec (l : List (Nat × Nat)) (i : Nat) :
    (l.map dec).toArray.getD i (m6One, idRows 22) = dec (l.getD i dK) := by
  rw [← dec_dK, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getD_eq_getElem?_getD]
  cases l[i]? <;> rfl

theorem stStep_sim (gens : List (Nat × Nat)) (acc : List (Nat × Nat)) (p : Nat × Nat) :
    stStep (gens.map dec) (acc.map dec).toArray (dec p) = ((stepK gens acc p).map dec).toArray := by
  unfold stStep stepK
  induction gens generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    simp only [dec, mul_dec, mulRows_unpack, List.any_toArray, List.any_map, Function.comp_def,
      beq_dec, stepG]
    split_ifs <;> simp [dec]

theorem stBFS_sim (gens : List (Nat × Nat)) :
    ∀ (fuel : Nat) (acc : List (Nat × Nat)) (i : Nat),
      stBFS (gens.map dec) fuel (acc.map dec).toArray i = ((bfsK gens fuel acc i).map dec).toArray
  | 0, _, _ => rfl
  | fuel + 1, acc, i => by
    simp only [stBFS, bfsK, List.size_toArray, List.length_map, getD_dec, stStep_sim]
    split_ifs
    · exact stBFS_sim gens fuel _ _
    · rfl

theorem all_range_getD {α : Type} (l : List α) (d : α) (f : α → Bool) :
    ((List.range l.length).all fun i => f (l.getD i d)) = l.all f := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    have := h i hi
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro h i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem _)

theorem any_range_getD {α : Type} (l : List α) (d : α) (f : α → Bool) :
    ((List.range l.length).any fun i => f (l.getD i d)) = l.any f := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [List.getD_eq_getElem _ _ hi] at h
    exact ⟨_, List.getElem_mem _, h⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    exact ⟨i, hi, by rwa [List.getD_eq_getElem _ _ hi]⟩

theorem check_eq (gens : List (Nat × Nat)) : stCheck (gens.map dec) = stCheckK gens := by
  have hB : stBFS (gens.map dec) 200 #[(m6One, idRows 22)] 0 =
      ((bfsK gens 200 [dK] 0).map dec).toArray := by
    rw [← stBFS_sim gens 200 [dK] 0, List.map_cons, List.map_nil, dec_dK]
  unfold stCheck stCheckK
  simp only []
  rw [hB]
  generalize bfsK gens 200 [dK] 0 = L
  simp only [List.size_toArray, List.length_map, getD_dec, List.all_map, Function.comp_def]
  simp only [dec, ← one_dec, beq_dec, idRows_eq, beq_unpack, mul_dec, mulRows_unpack]
  rw [all_range_getD L dK (fun x => gens.all fun g => (List.range L.length).any fun j =>
    eqF (L.getD j dK).1 (mul4 x.1 g.1) && eqK (L.getD j dK).2 (mulV x.2 g.2))]
  have e : ∀ (x g : Nat × Nat), ((List.range L.length).any fun j =>
      eqF (L.getD j dK).1 (mul4 x.1 g.1) && eqK (L.getD j dK).2 (mulV x.2 g.2)) =
      L.any fun y => eqF y.1 (mul4 x.1 g.1) && eqK y.2 (mulV x.2 g.2) := fun x g =>
    any_range_getD L dK (fun y => eqF y.1 (mul4 x.1 g.1) && eqK y.2 (mulV x.2 g.2))
  simp only [e]

#kc_forall_chunks stBlk_all (fun k => stBlkK k = true) 324 CertificateChecks.KernelCo2Smith.stBlkK 1

theorem block_lt (r s : Nat) : ∀ t ∈ stBlock r s, t < 18 := by
  intro t ht
  simp only [stBlock, List.mem_filter, List.mem_range] at ht
  exact ht.1

theorem stein_ok : glSteinOK = true := by
  unfold glSteinOK
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro r hr
    rw [List.all_eq_true]
    intro s hs
    rw [List.mem_range] at hr hs
    have h := stBlk_all (r * 18 + s) (show r * 18 + s < 324 by omega)
    have h1 : (r * 18 + s) / 18 = r := by omega
    have h2 : (r * 18 + s) % 18 = s := by omega
    rw [stBlkK, h1, h2] at h
    rw [stGens_eq _ (block_lt r s), check_eq]
    exact h
  · have h := stOpp_k
    unfold stOppK at h
    rw [List.all_eq_true] at h ⊢
    intro B hB
    have hl : ∀ t ∈ B, t < 18 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl <;> decide
    rw [stGens_eq _ hl, check_eq]
    exact h B hB

end CertificateChecks.KernelCo2Smith
