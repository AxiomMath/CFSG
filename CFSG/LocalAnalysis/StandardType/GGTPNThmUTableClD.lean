module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableClDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggTUClD_sum_eq_zero {l : List ℕ} (h : ∀ k, k < l.length → l.getD k 0 = 0) :
    l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : x = 0 := by simpa using h 0 (by simp)
      have hxs : ∀ k, k < xs.length → xs.getD k 0 = 0 := by
        intro k hk
        simpa using h (k + 1) (by simpa using hk)
      rw [List.sum_cons, hx, ih hxs, Nat.zero_add]

private theorem ggTUClD_sum_eq_of_unique {l : List ℕ} {i a : ℕ} (hi : i < l.length)
    (hia : l.getD i 0 = a)
    (hzero : ∀ k, k < l.length → k ≠ i → l.getD k 0 = 0) : l.sum = a := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          have hx : x = a := by simpa using hia
          have hxs : xs.sum = 0 := by
            apply ggTUClD_sum_eq_zero
            intro k hk
            simpa using hzero (k + 1) (by simpa using hk) (by omega)
          rw [List.sum_cons, hx, hxs, Nat.add_zero]
      | succ i =>
          have hx : x = 0 := by
            have := hzero 0 (by simp) (by omega)
            simpa using this
          have hxs : ∀ k, k < xs.length → k ≠ i → xs.getD k 0 = 0 := by
            intro k hk hki
            simpa using hzero (k + 1) (by simpa using hk) (by omega)
          have hix : xs.getD i 0 = a := by simpa using hia
          have hii : i < xs.length := by simpa using hi
          rw [List.sum_cons, hx, Nat.zero_add, ih hii hix hxs]

private theorem ggTUClD_sum_eq_headD_add {m : List ℕ} {H j a : ℕ}
    (hlen : m.length = H + 1) (hj1 : 1 ≤ j) (hjH : j ≤ H) (hj : m.getD j 0 = a)
    (hzero : ∀ k, k ≤ H → 1 ≤ k → k ≠ j → m.getD k 0 = 0) :
    m.sum = m.headD 0 + a := by
  cases m with
  | nil => simp at hlen
  | cons x xs =>
      have hxs_len : xs.length = H := by simpa using hlen
      have hsum_tail : xs.sum = a := by
        apply ggTUClD_sum_eq_of_unique (i := j - 1)
        · omega
        · have hget : xs.getD (j - 1) 0 = (x :: xs).getD j 0 := by
            have hjeq : (j - 1) + 1 = j := by omega
            rw [← hjeq]
            simp
          rw [hget, hj]
        · intro k hk hki
          have hk1 : 1 ≤ k + 1 := by omega
          have hkH : k + 1 ≤ H := by omega
          have hne : k + 1 ≠ j := by omega
          simpa using hzero (k + 1) hkH hk1 hne
      rw [List.sum_cons, hsum_tail]
      simp

private theorem ggTUClD_sum_eq_headD_of_all_zero {m : List ℕ} {H : ℕ}
    (hlen : m.length = H + 1) (hzero : ∀ k, 1 ≤ k → k ≤ H → m.getD k 0 = 0) :
    m.sum = m.headD 0 := by
  cases m with
  | nil => simp at hlen
  | cons x xs =>
      have hxs_len : xs.length = H := by simpa using hlen
      have hxs : xs.sum = 0 := by
        apply ggTUClD_sum_eq_zero
        intro k hk
        exact hzero (k + 1) (by omega) (by omega)
      rw [List.sum_cons, hxs, Nat.add_zero]
      rfl

private theorem ggTUClD_foldl_fixed_of_mem {l : List ℕ} {j : ℕ} {c : Prop} [Decidable c]
    {a : Bool} (h : ∀ k ∈ l, k ≠ j) :
    l.foldl (fun eps k => if k = j ∧ c then !eps else eps) a = a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons]
      have hx : x ≠ j := h x (by simp)
      have hxs : ∀ k ∈ xs, k ≠ j := fun k hk => h k (by simp [hk])
      rw [show (if x = j ∧ c then !a else a) = a by simp [hx]]
      exact ih hxs

private theorem ggTUClD_foldl_single {l : List ℕ} {j : ℕ} {c : Prop} [Decidable c]
    (hl : l.Nodup) (hj : j ∈ l) (e : Bool) :
    l.foldl (fun eps k => if k = j ∧ c then !eps else eps) e = if c then !e else e := by
  induction l generalizing e with
  | nil => simp at hj
  | cons x xs ih =>
      rw [List.nodup_cons] at hl
      obtain ⟨hx, hxs⟩ := hl
      by_cases hxj : x = j
      · subst x
        rw [List.foldl_cons]
        rw [show (if j = j ∧ c then !e else e) = (if c then !e else e) by simp]
        apply ggTUClD_foldl_fixed_of_mem
        intro k hk
        exact fun hkj => hx (hkj ▸ hk)
      · have hmem : j ∈ xs := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h.symm hxj
          · exact h
        rw [List.foldl_cons]
        rw [show (if x = j ∧ c then !e else e) = e by simp [hxj]]
        exact ih hxs hmem e

private theorem ggTUClD_foldl_getD {L : List ℕ} {d a j : ℕ} {m : List ℕ} (e : Bool)
    (hL : L.Nodup) (hj : j ∈ L)
    (hm : ∀ k ∈ L, m.getD k 0 = if k = j then a else 0) :
    L.foldl (fun eps k => if d = 2 ∧ m.getD k 0 % 2 = 1 then !eps else eps) e =
      if d = 2 ∧ a % 2 = 1 then !e else e := by
  have hfun : ∀ acc, ∀ k ∈ L,
      (fun eps k => if d = 2 ∧ m.getD k 0 % 2 = 1 then !eps else eps) acc k =
      (fun eps k => if k = j ∧ (d = 2 ∧ a % 2 = 1) then !eps else eps) acc k := by
    intro acc k hk
    change (if d = 2 ∧ m.getD k 0 % 2 = 1 then !acc else acc) =
      (if k = j ∧ (d = 2 ∧ a % 2 = 1) then !acc else acc)
    rw [hm k hk]
    by_cases hkj : k = j
    · subst hkj
      simp
    · simp [hkj]
  rw [List.foldl_ext _ _ _ hfun]
  exact ggTUClD_foldl_single hL hj e

private theorem ggTUClD_eps0_eq {p d a j : ℕ} {tw : Bool} {m : List ℕ}
    (hj : j ∈ (List.range ((p - 1) / 2)).map (· + 1))
    (hmj : m.getD j 0 = a)
    (hzero : ∀ k ∈ (List.range ((p - 1) / 2)).map (· + 1), k ≠ j → m.getD k 0 = 0) :
    ggMultEps0 p d tw m = if d = 2 ∧ a % 2 = 1 then tw else !tw := by
  unfold ggMultEps0
  have hLnodup : ((List.range ((p - 1) / 2)).map (· + 1)).Nodup := by
    rw [List.nodup_map_iff (fun a b h => by omega)]
    exact List.nodup_range
  have hm : ∀ k ∈ (List.range ((p - 1) / 2)).map (· + 1),
      m.getD k 0 = if k = j then a else 0 := by
    intro k hk
    by_cases hkj : k = j
    · subst hkj
      simpa using hmj
    · simpa [hkj] using hzero k hk hkj
  rw [ggTUClD_foldl_getD (!tw) hLnodup hj hm]
  by_cases hc : d = 2 ∧ a % 2 = 1 <;> simp [hc]

private theorem ggTUClD_foldl_zero {L : List ℕ} {d : ℕ} {m : List ℕ} (e : Bool)
    (h : ∀ k ∈ L, m.getD k 0 = 0) :
    L.foldl (fun eps k => if d = 2 ∧ m.getD k 0 % 2 = 1 then !eps else eps) e = e := by
  induction L generalizing e with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons]
      have hx : m.getD x 0 = 0 := h x (by simp)
      have hxs : ∀ k ∈ xs, m.getD k 0 = 0 := fun k hk => h k (by simp [hk])
      rw [show (if d = 2 ∧ m.getD x 0 % 2 = 1 then !e else e) = e by rw [hx]; simp]
      exact ih e hxs

private theorem ggTUClD_eps0_eq_of_all_zero {p d : ℕ} {tw : Bool} {m : List ℕ}
    (h : ∀ k ∈ (List.range ((p - 1) / 2)).map (· + 1), m.getD k 0 = 0) :
    ggMultEps0 p d tw m = !tw := by
  unfold ggMultEps0
  exact ggTUClD_foldl_zero (!tw) h

private theorem ggTUClD_block_of_orbJ_singleton {n d N : ℕ} {orbJ : List GGKacOrbit}
    {posJ posF : List ℕ}
    {o : GGKacOrbit} {j a : ℕ} {m : List ℕ}
    (horbJdef : orbJ = posJ.map (fun k => ggMultBlockA (m.getD k 0 - 1) n d))
    (hsingle : posF = [j])
    (hmemF : ∀ k, k ∈ posF ↔ k < N ∧ 1 ≤ k ∧ 0 < m.getD k 0)
    (hmemJ : ∀ k, k ∈ posJ ↔ k < N ∧ 1 ≤ k ∧ 2 ≤ m.getD k 0)
    (ha : a = m.getD j 0) (horbJ_o : orbJ = [o]) :
    o = ggMultBlockA (a - 1) n d := by
  have hposJ_len : posJ.length = 1 := by
    have h : orbJ.length = 1 := by simpa using congrArg List.length horbJ_o
    rwa [horbJdef, List.length_map] at h
  obtain ⟨j', hposJ_single⟩ := List.length_eq_one_iff.mp hposJ_len
  have hj'mem : j' ∈ posJ := by rw [hposJ_single]; simp
  have hj'posF : j' ∈ posF := by
    have h := (hmemJ j').mp hj'mem
    rw [hmemF]
    exact ⟨h.1, h.2.1, by omega⟩
  have hj'j : j' = j := by
    rw [hsingle] at hj'posF
    simpa using hj'posF
  subst j'
  have hblock : orbJ = [ggMultBlockA (m.getD j 0 - 1) n d] := by
    rw [horbJdef, hposJ_single]
    simp
  have ho0 : o = ggMultBlockA (m.getD j 0 - 1) n d := by
    have h : [ggMultBlockA (m.getD j 0 - 1) n d] = [o] := by
      simpa [hblock] using horbJ_o
    exact (List.singleton_injective h).symm
  rw [← ha] at ho0
  exact ho0

private theorem ggTUClD_a_le_of_orbJ_nil {n d N : ℕ} {orbJ : List GGKacOrbit} {posJ : List ℕ}
    {m : List ℕ} {j a : ℕ}
    (horbJdef : orbJ = posJ.map (fun k => ggMultBlockA (m.getD k 0 - 1) n d))
    (hmemJ : ∀ k, k ∈ posJ ↔ k < N ∧ 1 ≤ k ∧ 2 ≤ m.getD k 0)
    (hjlt : j < N) (hj1 : 1 ≤ j) (ha : a = m.getD j 0)
    (horbJ_nil : orbJ = []) : a ≤ 1 := by
  have hposJ_nil : posJ = [] := by
    rw [horbJdef] at horbJ_nil
    exact List.map_eq_nil_iff.mp horbJ_nil
  by_contra h
  have ha2 : 2 ≤ a := by omega
  have hjJ : j ∈ posJ := by
    rw [hmemJ]
    exact ⟨hjlt, hj1, by omega⟩
  rw [hposJ_nil] at hjJ
  simp at hjJ

private theorem ggTUClD_lambda2_blockA_two {r n : ℕ} (hn : 1 ≤ n) (hr : 4 ≤ r) {o : GGKacOrbit}
    (ho : o = ggMultBlockA (r - 2) n 2) (hqs : o.qs = true) :
    LargeEvenInLambda2 o.lab := by
  rw [ho]
  unfold ggMultBlockA
  rw [if_neg (by decide : ¬((2:ℕ) = 1))]
  by_cases hr4 : r = 4
  · subst r
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn1 : n = 1 := by omega
      have hq : (ggMultBlockA (4 - 2) n 2).qs = true := by simpa [ho] using hqs
      simp [ggMultBlockA, hn1] at hq
    rw [if_pos (by omega : 2 ≤ 4 - 2)]
    simp [LargeEvenInLambda2, hn, hn2]
  · have h3 : 3 ≤ r - 2 := by omega
    rw [if_pos (by omega : 2 ≤ r - 2)]
    simp [LargeEvenInLambda2, hn]
    omega

private theorem ggTUClD_v0_of_le_one {m0 n : ℕ} {e : Bool} (h : m0 ≤ 1) :
    ggMultV0 m0 e n = [] := by
  simp [ggMultV0, h]

private theorem ggTUClD_v0_of_ge_four {m0 n : ℕ} {e : Bool} (h : 4 ≤ m0) :
    ggMultV0 m0 e n =
      if e then [⟨⟨.D, m0, n⟩, true⟩] else [⟨⟨.twD, m0, n⟩, true⟩] := by
  simp [ggMultV0, show ¬ m0 ≤ 1 by omega, show m0 ≠ 2 by omega, show m0 ≠ 3 by omega]

private theorem ggTUClD_row_A_D {p n m : ℕ} (hm : 2 ≤ m) (hp : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.A, m, n⟩ ⟨.D, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_A_twD {p n m : ℕ} (hm : 2 ≤ m) (hp : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.A, m, n⟩ ⟨.twD, m+2, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_D_D {p n m : ℕ} (hp : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.D, m, n⟩ ⟨.D, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_D_twD {p n m : ℕ} (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.D, m, n⟩ ⟨.twD, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twD_twD {p n m : ℕ} (hm : 3 ≤ m) (hp : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.twD, m, n⟩ ⟨.twD, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twD_D {p n m : ℕ} (hm : 3 ≤ m) (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twD, m, n⟩ ⟨.D, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twA3_twD4 {p n : ℕ} (hp : p ∣ 2 ^ n - 1) :
    GGTablePRow p ⟨.twA, 3, n⟩ ⟨.twD, 4, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twA_D_odd {p n m : ℕ} (hm : 2 ≤ m) (ho : Odd m)
    (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twA, m, n⟩ ⟨.D, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twA_twD_even {p n m : ℕ} (hm : 2 ≤ m) (ho : Even m)
    (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twA, m, n⟩ ⟨.twD, m+1, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twA_D_odd2 {p n m : ℕ} (hm : 2 ≤ m) (ho : Odd m)
    (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twA, m, n⟩ ⟨.D, m+2, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_twA_twD_even2 {p n m : ℕ} (hm : 2 ≤ m) (ho : Even m)
    (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.twA, m, n⟩ ⟨.twD, m+2, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_row_D3_twD4 {p n : ℕ} (hp : p ∣ 2 ^ n + 1) :
    GGTablePRow p ⟨.D, 3, n⟩ ⟨.twD, 4, n⟩ := by
  unfold GGTablePRow
  simp
  tauto

private theorem ggTUClD_hdvd {p n d : ℕ} (hdD : d = ggMultOrd p n) (hd : d ≠ 0) :
    (d = 1 ∧ p ∣ 2 ^ n - 1) ∨ (d = 2 ∧ p ∣ 2 ^ n + 1) := by
  by_cases h1 : p ∣ 2 ^ n - 1
  · refine Or.inl ⟨?_, h1⟩
    rw [hdD]
    simp [ggMultOrd, h1]
  · by_cases h2 : p ∣ 2 ^ n + 1
    · refine Or.inr ⟨?_, h2⟩
      rw [hdD]
      simp [ggMultOrd, h1, h2]
    · exfalso
      have h0 : ggMultOrd p n = 0 := by simp [ggMultOrd, h1, h2]
      exact hd (by rwa [hdD])

private theorem ggTUClD_hpos_le {m0 d : ℕ} {eps0 : Bool} {posF : List ℕ}
    (hrZ' : (if m0 = 1 ∧ ((eps0 = true ∧ d = 1) ∨ (eps0 = false ∧ d = 2))
      then posF.length + 1 else posF.length) ≤ 1) : posF.length ≤ 1 := by
  by_cases he : m0 = 1 ∧ ((eps0 = true ∧ d = 1) ∨ (eps0 = false ∧ d = 2))
  · rw [if_pos he] at hrZ'
    omega
  · rw [if_neg he] at hrZ'
    exact hrZ'

private theorem ggTUClD_hmemF {H : ℕ} {m posF : List ℕ}
    (hposF : posF = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))) :
    ∀ k, k ∈ posF ↔ k < H + 1 ∧ 1 ≤ k ∧ 0 < m.getD k 0 := by
  intro k
  simp [hposF, List.mem_range, and_assoc]

private theorem ggTUClD_hmemJ {H : ℕ} {m posJ : List ℕ}
    (hposJ : posJ = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))) :
    ∀ k, k ∈ posJ ↔ k < H + 1 ∧ 1 ≤ k ∧ 2 ≤ m.getD k 0 := by
  intro k
  simp [hposJ, List.mem_range, and_assoc]

private theorem ggTUClD_hmemL {H : ℕ} :
    ∀ k, k ∈ (List.range H).map (· + 1) ↔ 1 ≤ k ∧ k ≤ H := by
  intro k
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.mem_range] at hi
    omega
  · rintro ⟨hk1, hkH⟩
    exact ⟨k - 1, by simp [List.mem_range]; omega, by omega⟩

private theorem ggTUClD_hpos_cases {posF : List ℕ} (hpos_le : posF.length ≤ 1) :
    posF = [] ∨ ∃ j, posF = [j] := by
  cases hF : posF with
  | nil => exact Or.inl rfl
  | cons a rest =>
      cases rest with
      | nil => exact Or.inr ⟨a, rfl⟩
      | cons b rest =>
          exfalso
          have : 2 ≤ posF.length := by rw [hF]; simp
          omega

private structure ggTUClDSetup (r p n : ℕ) (tw : Bool) (D : GGKacDatum) (o : GGKacOrbit) where
  hn : 1 ≤ n
  hr : 4 ≤ r
  hqs : o.qs = true
  hX : o.lab ≠ ⟨if tw then .twD else .D, r, n⟩
  m : List ℕ
  hlen : m.length = (p - 1) / 2 + 1
  hsum : m.sum = r
  hD' : D = ggMultDatumD p n (ggMultOrd p n) tw m
  hd : ggMultOrd p n ≠ 0
  H : ℕ
  hH : H = (p - 1) / 2
  d : ℕ
  hdD : d = ggMultOrd p n
  m0 : ℕ
  hm0 : m0 = m.headD 0
  eps0 : Bool
  heps0 : eps0 = ggMultEps0 p d tw m
  hadm : m0 = 0 → eps0 = true
  posF : List ℕ
  hposF : posF = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))
  posJ : List ℕ
  hposJ : posJ = (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))
  orbJ : List GGKacOrbit
  horbJ : orbJ = posJ.map (fun j => ggMultBlockA (m.getD j 0 - 1) n d)
  hDo' : ggMultV0 m0 eps0 n ++ orbJ = [o]
  hrZ' : (if m0 = 1 ∧ ((eps0 = true ∧ d = 1) ∨ (eps0 = false ∧ d = 2))
      then posF.length + 1 else posF.length) ≤ 1
  hdvd : (d = 1 ∧ p ∣ 2 ^ n - 1) ∨ (d = 2 ∧ p ∣ 2 ^ n + 1)
  hpos_le : posF.length ≤ 1
  hmemF : ∀ k, k ∈ posF ↔ k < H + 1 ∧ 1 ≤ k ∧ 0 < m.getD k 0
  hmemJ : ∀ k, k ∈ posJ ↔ k < H + 1 ∧ 1 ≤ k ∧ 2 ≤ m.getD k 0
  hmemL : ∀ k, k ∈ (List.range H).map (· + 1) ↔ 1 ≤ k ∧ k ≤ H
  hpos_cases : posF = [] ∨ ∃ j, posF = [j]

private noncomputable def ggTUClD_setup {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (hn : 1 ≤ n) (hr : 4 ≤ r) (hD : D ∈ ggMultTableCl (.D r) tw p n) (hrZ : D.rZ ≤ 1)
    (hDo : D.orbits = [o]) (hqs : o.qs = true)
    (hX : o.lab ≠ ⟨if tw then .twD else .D, r, n⟩) :
    ggTUClDSetup r p n tw D o := by
  classical
  have hd : ggMultOrd p n ≠ 0 := ggMultOrd_ne_zero_of_mem_ggMultTableCl hD
  have hm : ∃ m : List ℕ, m.length = (p - 1) / 2 + 1 ∧ m.sum = r ∧
      (m.headD 0 = 0 → ggMultEps0 p (ggMultOrd p n) tw m = true) ∧
        D = ggMultDatumD p n (ggMultOrd p n) tw m :=
    (mem_ggMultTableCl_D (tw := tw) hd).mp hD
  set m := Classical.choose hm with hmdef
  obtain ⟨hlen, hsum, hadm, hD'⟩ := Classical.choose_spec hm
  have hlenm : m.length = (p - 1) / 2 + 1 := by rwa [← hmdef] at hlen
  have hsumm : m.sum = r := by rwa [← hmdef] at hsum
  have hadmm : m.headD 0 = 0 → ggMultEps0 p (ggMultOrd p n) tw m = true := by
    rwa [← hmdef] at hadm
  have hD'' : D = ggMultDatumD p n (ggMultOrd p n) tw m := by rwa [← hmdef] at hD'
  rw [hD''] at hDo hrZ
  set H := (p - 1) / 2 with hH
  set d := ggMultOrd p n with hdD
  set m0 := m.headD 0 with hm0
  set eps0 := ggMultEps0 p d tw m with heps0
  have hadm0 : m0 = 0 → eps0 = true := by
    intro h
    have h' : m.headD 0 = 0 := by rw [← hm0]; exact h
    have h'' := hadmm h'
    exact h''
  set posF := (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) with hposF
  set posJ := (List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0)) with hposJ
  set orbJ := posJ.map (fun j => ggMultBlockA (m.getD j 0 - 1) n d) with horbJ
  have hDo' : ggMultV0 m0 eps0 n ++ orbJ = [o] := by
    simpa only [ggMultDatumD, hH, hm0, heps0, hposJ, horbJ] using hDo
  have hrZ' : (if m0 = 1 ∧ ((eps0 = true ∧ d = 1) ∨ (eps0 = false ∧ d = 2))
      then posF.length + 1 else posF.length) ≤ 1 := by
    simpa only [ggMultDatumD, hH, hm0, heps0, hposF] using hrZ
  have hdvd := ggTUClD_hdvd hdD hd
  have hpos_le := ggTUClD_hpos_le hrZ'
  have hmemF := ggTUClD_hmemF hposF
  have hmemJ := ggTUClD_hmemJ hposJ
  have hmemL := ggTUClD_hmemL (H := H)
  have hpos_cases := ggTUClD_hpos_cases hpos_le
  exact
    { hn := hn, hr := hr, hqs := hqs, hX := hX, m := m, hlen := hlenm, hsum := hsumm,
      hadm := hadm0, hD' := hD'', hd := hd, H := H, hH := hH, d := d, hdD := hdD,
      m0 := m0, hm0 := hm0, eps0 := eps0, heps0 := heps0, posF := posF, hposF := hposF,
      posJ := posJ, hposJ := hposJ, orbJ := orbJ, horbJ := horbJ, hDo' := hDo',
      hrZ' := hrZ', hdvd := hdvd, hpos_le := hpos_le, hmemF := hmemF, hmemJ := hmemJ,
      hmemL := hmemL, hpos_cases := hpos_cases }

private theorem ggTUClD_single_facts {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j]) :
    (j < S.H + 1) ∧ (1 ≤ j) ∧ (0 < S.m.getD j 0) ∧
      (∀ k, k < S.H + 1 → 1 ≤ k → k ≠ j → S.m.getD k 0 = 0) ∧
      ∃ a : ℕ, a = S.m.getD j 0 ∧ S.m.sum = S.m0 + a ∧ r = S.m0 + a ∧
        (S.eps0 = if S.d = 2 ∧ a % 2 = 1 then tw else !tw) ∧
        ¬(S.m0 = 1 ∧ ((S.eps0 = true ∧ S.d = 1) ∨ (S.eps0 = false ∧ S.d = 2))) := by
  have hjmem : j ∈ S.posF := by rw [hsingle]; simp
  obtain ⟨hj_lt, hj1, hmj_pos⟩ := (S.hmemF j).mp hjmem
  have hjH : j ≤ S.H := by omega
  have hzero_other : ∀ k, k < S.H + 1 → 1 ≤ k → k ≠ j → S.m.getD k 0 = 0 := by
    intro k hk hk1 hkj
    by_contra hne
    have hkpos : k ∈ S.posF := by
      rw [S.hmemF]
      exact ⟨hk, hk1, Nat.pos_of_ne_zero hne⟩
    rw [hsingle] at hkpos
    simp only [List.mem_singleton] at hkpos
    exact hkj hkpos
  have hjL : j ∈ (List.range S.H).map (· + 1) := by rw [S.hmemL]; omega
  have hsum_eq : S.m.sum = S.m0 + S.m.getD j 0 := by
    have hlen : S.m.length = S.H + 1 := by rw [S.hlen, S.hH]
    have h := ggTUClD_sum_eq_headD_add (m := S.m) (H := S.H) (j := j)
      (a := S.m.getD j 0) hlen hj1 hjH rfl
      (fun k hkH hk1 hkj => hzero_other k (by omega) hk1 hkj)
    simpa only [← S.hm0] using h
  have hr_eq : r = S.m0 + S.m.getD j 0 := by
    have h := S.hsum
    omega
  have heps_eq : S.eps0 =
      if S.d = 2 ∧ S.m.getD j 0 % 2 = 1 then tw else !tw := by
    rw [S.heps0]
    apply ggTUClD_eps0_eq
    · simpa [S.hH] using hjL
    · rfl
    · intro k hk hkj
      have hk' := (S.hmemL k).mp (by simpa [S.hH] using hk)
      exact hzero_other k (by omega) hk'.1 hkj
  have hextra_false :
      ¬(S.m0 = 1 ∧ ((S.eps0 = true ∧ S.d = 1) ∨ (S.eps0 = false ∧ S.d = 2))) := by
    intro he
    have hpos_len1 : S.posF.length = 1 := by rw [hsingle]; simp
    have h := S.hrZ'
    rw [if_pos he] at h
    omega
  exact ⟨hj_lt, hj1, hmj_pos, hzero_other, S.m.getD j 0, rfl, hsum_eq, hr_eq,
    heps_eq, hextra_false⟩

private theorem ggTUClD_m0_2 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 2) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  by_cases he : S.eps0 = true
  · have h := S.hDo'
    rw [hm0, he] at h
    simp [ggMultV0] at h
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    have h := S.hDo'
    rw [hm0, hef] at h
    simp [ggMultV0] at h
    have horbJ_nil : S.orbJ = [] := h.2
    have ha_le := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega

private theorem ggTUClD_posF_nil_low {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o)
    (hr0 : r = S.m0) (hv0 : ggMultV0 S.m0 S.eps0 n = [o]) (hle : S.m0 ≤ 3) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  have hr := S.hr
  by_cases h01 : S.m0 ≤ 1
  · have hv01 : ggMultV0 S.m0 S.eps0 n = [] := ggTUClD_v0_of_le_one h01
    rw [hv01] at hv0
    simp at hv0
  · by_cases hm02 : S.m0 = 2
    · omega
    · by_cases hm03 : S.m0 = 3
      · omega
      · omega

private theorem ggTUClD_posF_nil_high {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) (hnil : S.posF = [])
    (hr0 : r = S.m0) (hv0 : ggMultV0 S.m0 S.eps0 n = [o]) (heps0 : S.eps0 = !tw)
    (hm04 : 4 ≤ S.m0) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  rw [ggTUClD_v0_of_ge_four hm04] at hv0
  by_cases he : S.eps0 = true
  · rw [if_pos he] at hv0
    simp at hv0
    have ho : o = ⟨⟨.D, S.m0, n⟩, true⟩ := hv0.symm
    have htw : tw = false := by
      have h : S.eps0 = !tw := heps0
      rw [he] at h
      cases tw with
      | false => rfl
      | true => simp at h
    have hoD : o.lab = ⟨.D, r, n⟩ := by
      have h := congrArg (fun x : ℕ => (⟨.D, x, n⟩ : LargeEvenLabel)) hr0.symm
      simpa [ho] using h
    have htag : (if tw then LargeEvenLieTag.twD else LargeEvenLieTag.D) =
        LargeEvenLieTag.D := by
      cases tw with
      | false => rfl
      | true => simp at htw
    exact absurd (by rw [hoD, htag]) S.hX
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    rw [if_neg he] at hv0
    simp at hv0
    have ho : o = ⟨⟨.twD, S.m0, n⟩, true⟩ := hv0.symm
    have htw : tw = true := by
      have h : S.eps0 = !tw := heps0
      rw [hef] at h
      cases tw with
      | false => simp at h
      | true => rfl
    have hoD : o.lab = ⟨.twD, r, n⟩ := by
      have h := congrArg (fun x : ℕ => (⟨.twD, x, n⟩ : LargeEvenLabel)) hr0.symm
      simpa [ho] using h
    have htag : (if tw then LargeEvenLieTag.twD else LargeEvenLieTag.D) =
        LargeEvenLieTag.twD := by
      cases tw with
      | false => simp at htw
      | true => rfl
    exact absurd (by rw [hoD, htag]) S.hX

private theorem ggTUClD_posF_nil {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) (hnil : S.posF = []) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  have hzero_all : ∀ k, k < S.H + 1 → 1 ≤ k → S.m.getD k 0 = 0 := by
    intro k hk hk1
    by_contra hne
    have hkpos : k ∈ S.posF := by
      rw [S.hmemF]
      exact ⟨hk, hk1, Nat.pos_of_ne_zero hne⟩
    rw [hnil] at hkpos
    simp at hkpos
  have hsum0 : S.m.sum = S.m0 := by
    have hlen : S.m.length = S.H + 1 := by rw [S.hlen, S.hH]
    have h := ggTUClD_sum_eq_headD_of_all_zero (m := S.m) (H := S.H) hlen
      (fun k hk1 hkH => hzero_all k (by omega) hk1)
    simpa only [← S.hm0] using h
  have hr0 : r = S.m0 := by
    have h := S.hsum
    omega
  have hposJ_nil : S.posJ = [] := by
    by_contra hne
    obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil S.posJ hne
    have hkF : k ∈ S.posF := by
      have h := (S.hmemJ k).mp hk
      rw [S.hmemF]
      exact ⟨h.1, h.2.1, by omega⟩
    rw [hnil] at hkF
    simp at hkF
  have horbJ_nil : S.orbJ = [] := by simp [S.horbJ, hposJ_nil]
  have hv0 : ggMultV0 S.m0 S.eps0 n = [o] := by simpa [horbJ_nil] using S.hDo'
  have heps0 : S.eps0 = !tw := by
    rw [S.heps0]
    apply ggTUClD_eps0_eq_of_all_zero
    intro k hk
    have hk' := (S.hmemL k).mp (by simpa [← S.hH] using hk)
    exact hzero_all k (by omega) hk'.1
  by_cases hle : S.m0 ≤ 3
  · exact ggTUClD_posF_nil_low S hr0 hv0 hle
  · exact ggTUClD_posF_nil_high S hnil hr0 hv0 heps0 (by omega)

private theorem ggTUClD_d1_m0_0 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 0) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hε : S.eps0 = true := S.hadm hm0
  have hv0 : ggMultV0 0 S.eps0 n = [] := by simp [ggMultV0]
  have hDo0 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo0
  rw [har] at ho
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = false := by
    have h : S.eps0 = !tw := heps1
    rw [hε] at h
    cases tw with
    | false => rfl
    | true => simp at h
  have holab : o.lab = ⟨.A, r - 1, n⟩ := by
    rw [ho, hd1]
    unfold ggMultBlockA
    rw [if_pos rfl]
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [holab]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    have h := ggTUClD_row_A_D (p := p) (n := n) (m := r - 1) (by omega) hp1
    simpa [show r - 1 + 1 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_1 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 1) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hεfalse : S.eps0 = false := by
    rcases Bool.eq_false_or_eq_true S.eps0 with h | h
    · exact absurd ⟨hm0, Or.inl ⟨h, hd1⟩⟩ hextra_false
    · exact h
  have hv0 : ggMultV0 1 S.eps0 n = [] := by simp [ggMultV0]
  have hDo1 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r - 1 := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo1
  rw [har] at ho
  have hsub : (r - 1) - 1 = r - 2 := by omega
  rw [hsub] at ho
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = true := by
    have h : S.eps0 = !tw := heps1
    rw [hεfalse] at h
    cases tw with
    | false => simp at h
    | true => rfl
  have holab : o.lab = ⟨.A, r - 2, n⟩ := by
    rw [ho, hd1]
    unfold ggMultBlockA
    rw [if_pos rfl]
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [holab]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_pos (by decide : (true : Bool) = true)]
    have h := ggTUClD_row_A_twD (p := p) (n := n) (m := r - 2) (by omega) hp1
    simpa [show r - 2 + 2 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_3_true {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) (he : S.eps0 = true) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [hm0, he] at h
  simp [ggMultV0] at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoA : o = ⟨⟨.A, 3, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hr4 : r = 4 := by omega
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = false := by
    have h : S.eps0 = !tw := heps1
    rw [he] at h
    cases tw with
    | false => rfl
    | true => simp at h
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoA]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoA, htw, hr4]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    exact ggTUClD_row_A_D (p := p) (n := n) (m := 3) (by omega) hp1
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_3_false {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) (hef : S.eps0 = false) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [hm0, hef] at h
  simp [ggMultV0] at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoA : o = ⟨⟨.twA, 3, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hr4 : r = 4 := by omega
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = true := by
    have h : S.eps0 = !tw := heps1
    rw [hef] at h
    cases tw with
    | false => simp at h
    | true => rfl
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoA]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoA, htw, hr4]
    rw [if_pos (by decide : (true : Bool) = true)]
    exact ggTUClD_row_twA3_twD4 (p := p) (n := n) hp1
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_3 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases he : S.eps0 = true
  · exact ggTUClD_d1_m0_3_true S hsingle hm0 hd1 hp1 he
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    exact ggTUClD_d1_m0_3_false S hsingle hm0 hd1 hp1 hef

private theorem ggTUClD_d1_m0_ge4_true {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) (he : S.eps0 = true) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [ggTUClD_v0_of_ge_four hm04] at h
  rw [if_pos he] at h
  simp at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoD0 : o = ⟨⟨.D, S.m0, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hrX : r = S.m0 + 1 := by omega
  have hm0r : S.m0 = r - 1 := by omega
  have hoD : o.lab = ⟨.D, r - 1, n⟩ := by
    rw [hoD0, hm0r]
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = false := by
    have h : S.eps0 = !tw := heps1
    rw [he] at h
    cases tw with
    | false => rfl
    | true => simp at h
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoD]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoD, htw]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    have hh := ggTUClD_row_D_D (p := p) (n := n) (m := r - 1) hp1
    simpa [show r - 1 + 1 = r by omega] using hh
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_ge4_false {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) (hef : S.eps0 = false) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [ggTUClD_v0_of_ge_four hm04] at h
  rw [hef] at h
  simp at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoD0 : o = ⟨⟨.twD, S.m0, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hrX : r = S.m0 + 1 := by omega
  have hm0r : S.m0 = r - 1 := by omega
  have hoD : o.lab = ⟨.twD, r - 1, n⟩ := by
    rw [hoD0, hm0r]
  have heps1 : S.eps0 = !tw := by simpa [hd1] using heps_eq
  have htw : tw = true := by
    have h : S.eps0 = !tw := heps1
    rw [hef] at h
    cases tw with
    | false => simp at h
    | true => rfl
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoD]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoD, htw]
    rw [if_pos (by decide : (true : Bool) = true)]
    have hh := ggTUClD_row_twD_twD (p := p) (n := n) (m := r - 1) (by omega) hp1
    simpa [show r - 1 + 1 = r by omega] using hh
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d1_m0_ge4 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd1 : S.d = 1) (hp1 : p ∣ 2 ^ n - 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases he : S.eps0 = true
  · exact ggTUClD_d1_m0_ge4_true S hsingle hm04 hd1 hp1 he
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    exact ggTUClD_d1_m0_ge4_false S hsingle hm04 hd1 hp1 hef

private theorem ggTUClD_d2_m0_0_odd {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1)
    (haodd : S.m.getD j 0 % 2 = 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hε : S.eps0 = true := S.hadm hm0
  have hv0 : ggMultV0 0 S.eps0 n = [] := by simp [ggMultV0]
  have hDo0 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo0
  rw [har] at ho
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = true := by
    have h := heps2
    rw [if_pos haodd] at h
    rw [hε] at h
    exact h.symm
  have hEven : Even (r - 1) := by
    rw [Nat.even_iff]
    omega
  have holab : o.lab = ⟨.twA, r - 1, n⟩ := by
    rw [ho, hd2]
    unfold ggMultBlockA
    rw [if_neg (by decide : ¬((2:ℕ) = 1)), if_pos (by omega : 2 ≤ r - 1)]
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [holab]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_pos (by decide : (true : Bool) = true)]
    have h := ggTUClD_row_twA_twD_even (p := p) (n := n) (m := r - 1) (by omega) hEven hp2
    simpa [show r - 1 + 1 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_0_even {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1)
    (haeven : ¬ S.m.getD j 0 % 2 = 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hε : S.eps0 = true := S.hadm hm0
  have hv0 : ggMultV0 0 S.eps0 n = [] := by simp [ggMultV0]
  have hDo0 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo0
  rw [har] at ho
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = false := by
    have h := heps2
    rw [if_neg haeven] at h
    rw [hε] at h
    cases tw with
    | false => rfl
    | true => simp at h
  have hOdd : Odd (r - 1) := by
    rw [Nat.odd_iff]
    omega
  have holab : o.lab = ⟨.twA, r - 1, n⟩ := by
    rw [ho, hd2]
    unfold ggMultBlockA
    rw [if_neg (by decide : ¬((2:ℕ) = 1)), if_pos (by omega : 2 ≤ r - 1)]
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [holab]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    have h := ggTUClD_row_twA_D_odd (p := p) (n := n) (m := r - 1) (by omega) hOdd hp2
    simpa [show r - 1 + 1 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_0 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases haodd : S.m.getD j 0 % 2 = 1
  · exact ggTUClD_d2_m0_0_odd S hsingle hm0 hd2 hp2 haodd
  · exact ggTUClD_d2_m0_0_even S hsingle hm0 hd2 hp2 haodd

private theorem ggTUClD_d2_m0_1_odd {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 1) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1)
    (haodd : S.m.getD j 0 % 2 = 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hε : S.eps0 = true := by
    rcases Bool.eq_false_or_eq_true S.eps0 with h | h
    · exact h
    · exact absurd ⟨hm0, Or.inr ⟨h, hd2⟩⟩ hextra_false
  have hv0 : ggMultV0 1 S.eps0 n = [] := by simp [ggMultV0]
  have hDo1 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r - 1 := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo1
  rw [har] at ho
  have hsub : (r - 1) - 1 = r - 2 := by omega
  rw [hsub] at ho
  rw [hd2] at ho
  have holab : o.lab = ⟨.twA, r - 2, n⟩ := by
    rw [ho]
    unfold ggMultBlockA
    rw [if_neg (by decide : ¬((2:ℕ) = 1)), if_pos (by omega : 2 ≤ r - 2)]
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = true := by
    have h := heps2
    rw [if_pos haodd] at h
    rw [hε] at h
    exact h.symm
  have hEven : Even (r - 2) := by
    rw [Nat.even_iff]
    omega
  have hoΛ : LargeEvenInLambda2 o.lab :=
    ggTUClD_lambda2_blockA_two (r := r) (n := n) S.hn S.hr ho S.hqs
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_pos (by decide : (true : Bool) = true)]
    have h := ggTUClD_row_twA_twD_even2 (p := p) (n := n) (m := r - 2)
      (by omega) hEven hp2
    simpa [show r - 2 + 2 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_1_even {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 1) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1)
    (haeven : ¬ S.m.getD j 0 % 2 = 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have hε : S.eps0 = true := by
    rcases Bool.eq_false_or_eq_true S.eps0 with h | h
    · exact h
    · exact absurd ⟨hm0, Or.inr ⟨h, hd2⟩⟩ hextra_false
  have hv0 : ggMultV0 1 S.eps0 n = [] := by simp [ggMultV0]
  have hDo1 : S.orbJ = [o] := by
    have h := S.hDo'
    rw [hm0, hv0] at h
    simpa using h
  have har : a = r - 1 := by omega
  have ho := ggTUClD_block_of_orbJ_singleton (N := S.H + 1) S.horbJ hsingle S.hmemF S.hmemJ ha hDo1
  rw [har] at ho
  have hsub : (r - 1) - 1 = r - 2 := by omega
  rw [hsub] at ho
  rw [hd2] at ho
  have holab : o.lab = ⟨.twA, r - 2, n⟩ := by
    rw [ho]
    unfold ggMultBlockA
    rw [if_neg (by decide : ¬((2:ℕ) = 1)), if_pos (by omega : 2 ≤ r - 2)]
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = false := by
    have h := heps2
    rw [if_neg haeven] at h
    rw [hε] at h
    cases tw with
    | false => rfl
    | true => simp at h
  have hOdd : Odd (r - 2) := by
    rw [Nat.odd_iff]
    omega
  have hoΛ : LargeEvenInLambda2 o.lab :=
    ggTUClD_lambda2_blockA_two (r := r) (n := n) S.hn S.hr ho S.hqs
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [holab, htw]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    have h := ggTUClD_row_twA_D_odd2 (p := p) (n := n) (m := r - 2)
      (by omega) hOdd hp2
    simpa [show r - 2 + 2 = r by omega] using h
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩
private theorem ggTUClD_d2_m0_1 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 1) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases haodd : S.m.getD j 0 % 2 = 1
  · exact ggTUClD_d2_m0_1_odd S hsingle hm0 hd2 hp2 haodd
  · exact ggTUClD_d2_m0_1_even S hsingle hm0 hd2 hp2 haodd

private theorem ggTUClD_d2_m0_3_true {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) (he : S.eps0 = true) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [hm0, he] at h
  simp [ggMultV0] at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoA : o = ⟨⟨.A, 3, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hr4 : r = 4 := by omega
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = true := by
    have h := heps2
    rw [← ha, if_pos (by omega : a % 2 = 1)] at h
    rw [he] at h
    exact h.symm
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoA]
    simp [LargeEvenInLambda2]
    omega
  have hoΛD : LargeEvenInLambda2 (⟨.D, 3, n⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2, S.hn]
  refine ⟨hoΛ, ⟨⟨.D, 3, n⟩, ?_, hoΛD, ?_⟩⟩
  · rw [hoA]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · rw [htw, hr4]
    rw [if_pos (by decide : (true : Bool) = true)]
    exact ggTUClD_row_D3_twD4 (p := p) (n := n) hp2

private theorem ggTUClD_d2_m0_3_false {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) (hef : S.eps0 = false) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [hm0, hef] at h
  simp [ggMultV0] at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoA : o = ⟨⟨.twA, 3, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hr4 : r = 4 := by omega
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = false := by
    have h := heps2
    rw [← ha, if_pos (by omega : a % 2 = 1)] at h
    rw [hef] at h
    exact h.symm
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoA]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoA, htw, hr4]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    exact ggTUClD_row_twA_D_odd (p := p) (n := n) (m := 3) (by omega) (by decide) hp2
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_3 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm0 : S.m0 = 3) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases he : S.eps0 = true
  · exact ggTUClD_d2_m0_3_true S hsingle hm0 hd2 hp2 he
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    exact ggTUClD_d2_m0_3_false S hsingle hm0 hd2 hp2 hef

private theorem ggTUClD_d2_m0_ge4_true {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) (he : S.eps0 = true) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [ggTUClD_v0_of_ge_four hm04] at h
  rw [if_pos he] at h
  simp at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoD0 : o = ⟨⟨.D, S.m0, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hrX : r = S.m0 + 1 := by omega
  have hm0r : S.m0 = r - 1 := by omega
  have hoD : o.lab = ⟨.D, r - 1, n⟩ := by
    rw [hoD0, hm0r]
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = true := by
    have h := heps2
    rw [if_pos (by omega : S.m.getD j 0 % 2 = 1)] at h
    rw [he] at h
    exact h.symm
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoD]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoD, htw]
    rw [if_pos (by decide : (true : Bool) = true)]
    have hh := ggTUClD_row_D_twD (p := p) (n := n) (m := r - 1) hp2
    simpa [show r - 1 + 1 = r by omega] using hh
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_ge4_false {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) (hef : S.eps0 = false) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  obtain ⟨hj_lt, hj1, hmj_pos, hzero_other, a, ha, hsum_eq, hr_eq, heps_eq, hextra_false⟩ :=
    ggTUClD_single_facts S hsingle
  have hr := S.hr
  have hn := S.hn
  have h := S.hDo'
  rw [ggTUClD_v0_of_ge_four hm04] at h
  rw [hef] at h
  simp at h
  have horbJ_nil : S.orbJ = [] := h.2
  have hoD0 : o = ⟨⟨.twD, S.m0, n⟩, true⟩ := h.1.symm
  have ha1 : a = 1 := by
    have := ggTUClD_a_le_of_orbJ_nil (N := S.H + 1) S.horbJ S.hmemJ hj_lt hj1 ha horbJ_nil
    omega
  have hrX : r = S.m0 + 1 := by omega
  have hm0r : S.m0 = r - 1 := by omega
  have hoD : o.lab = ⟨.twD, r - 1, n⟩ := by
    rw [hoD0, hm0r]
  have heps2 : S.eps0 = if S.m.getD j 0 % 2 = 1 then tw else !tw := by
    simpa [hd2, ha] using heps_eq
  have htw : tw = false := by
    have h := heps2
    rw [if_pos (by omega : S.m.getD j 0 % 2 = 1)] at h
    rw [hef] at h
    exact h.symm
  have hoΛ : LargeEvenInLambda2 o.lab := by
    rw [hoD]
    simp [LargeEvenInLambda2]
    omega
  have hrow : GGTablePRow p o.lab ⟨if tw then .twD else .D, r, n⟩ := by
    rw [hoD, htw]
    rw [if_neg (by decide : ¬((false : Bool) = true))]
    have hh := ggTUClD_row_twD_D (p := p) (n := n) (m := r - 1) (by omega) hp2
    simpa [show r - 1 + 1 = r by omega] using hh
  exact ⟨hoΛ, ⟨o.lab, Or.inl rfl, hoΛ, hrow⟩⟩

private theorem ggTUClD_d2_m0_ge4 {r p n : ℕ} {tw : Bool} {D : GGKacDatum} {o : GGKacOrbit}
    (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j])
    (hm04 : 4 ≤ S.m0) (hd2 : S.d = 2) (hp2 : p ∣ 2 ^ n + 1) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  by_cases he : S.eps0 = true
  · exact ggTUClD_d2_m0_ge4_true S hsingle hm04 hd2 hp2 he
  · have hef : S.eps0 = false := by
      rcases Bool.eq_false_or_eq_true S.eps0 with h | h
      · exact absurd h he
      · exact h
    exact ggTUClD_d2_m0_ge4_false S hsingle hm04 hd2 hp2 hef

private theorem ggTUClD_posF_single {r p n : ℕ} {tw : Bool} {D : GGKacDatum}
    {o : GGKacOrbit} (S : ggTUClDSetup r p n tw D o) {j : ℕ} (hsingle : S.posF = [j]) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  rcases S.hdvd with ⟨hd1, hp1⟩ | ⟨hd2, hp2⟩
  · by_cases hm00 : S.m0 = 0
    · exact ggTUClD_d1_m0_0 S hsingle hm00 hd1 hp1
    · by_cases hm01 : S.m0 = 1
      · exact ggTUClD_d1_m0_1 S hsingle hm01 hd1 hp1
      · by_cases hm02 : S.m0 = 2
        · exact ggTUClD_m0_2 S hsingle hm02
        · by_cases hm03 : S.m0 = 3
          · exact ggTUClD_d1_m0_3 S hsingle hm03 hd1 hp1
          · exact ggTUClD_d1_m0_ge4 S hsingle (by omega) hd1 hp1
  · by_cases hm00 : S.m0 = 0
    · exact ggTUClD_d2_m0_0 S hsingle hm00 hd2 hp2
    · by_cases hm01 : S.m0 = 1
      · exact ggTUClD_d2_m0_1 S hsingle hm01 hd2 hp2
      · by_cases hm02 : S.m0 = 2
        · exact ggTUClD_m0_2 S hsingle hm02
        · by_cases hm03 : S.m0 = 3
          · exact ggTUClD_d2_m0_3 S hsingle hm03 hd2 hp2
          · exact ggTUClD_d2_m0_ge4 S hsingle (by omega) hd2 hp2

theorem ggTablePRow_of_mem_ggMultTableCl_D {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hn : 1 ≤ n)
    (hr : 4 ≤ r) (hD : D ∈ ggMultTableCl (.D r) tw p n) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit}
    (hDo : D.orbits = [o]) (hqs : o.qs = true) (hX : o.lab ≠ ⟨if tw then .twD else .D, r, n⟩) :
    LargeEvenInLambda2 o.lab ∧ ∃ labJ : LargeEvenLabel, GGLabelIso o.lab labJ ∧
      LargeEvenInLambda2 labJ ∧ GGTablePRow p labJ ⟨if tw then .twD else .D, r, n⟩ := by
  have S := ggTUClD_setup hn hr hD hrZ hDo hqs hX
  rcases S.hpos_cases with hnil | ⟨j, hsingle⟩
  · exact ggTUClD_posF_nil S hnil
  · exact ggTUClD_posF_single S hsingle

end CFSG.StandardType

end
