module

public import CFSG.Quasithin.Background.P4InspOrthPlus4

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspOrth CFSG.QuasithinUnique

namespace S143V

namespace O4Aux

abbrev Vec4 : Type := Fin 4 → ZMod 2

private def Q0 (x : Vec4) : ZMod 2 := x 0 * x 2 + x 1 * x 3

private def bitv (a : ZMod 2) : ℕ := if a = 0 then 0 else 1

private def enc (x : Vec4) : ℕ := bitv (x 0) + 2 * bitv (x 1) + 4 * bitv (x 2) + 8 * bitv (x 3)

private def dec (n : ℕ) : Vec4 := fun i => if n / 2 ^ i.val % 2 = 1 then 1 else 0

private theorem dec_enc : ∀ x : Vec4, dec (enc x) = x := by decide +kernel

private theorem enc_lt : ∀ x : Vec4, enc x < 16 := by decide +kernel

private theorem enc_dec : ∀ n < 16, enc (dec n) = n := by decide +kernel

private theorem enc_add : ∀ x y : Vec4, enc (x + y) = enc x ^^^ enc y := by decide +kernel

private theorem dec_xor : ∀ a < 16, ∀ b < 16, dec (a ^^^ b) = dec a + dec b := by
  decide +kernel

private theorem dec_zero : dec 0 = 0 := by decide +kernel

private theorem enc_zero : enc 0 = 0 := by decide +kernel

private def qm : ℕ := 27808

private def qN (n : ℕ) : ℕ := (qm >>> n) % 2

private theorem qN_eq : ∀ n < 16, ((qN n : ℕ) : ZMod 2) = Q0 (dec n) := by decide +kernel

private theorem qN_lt (n : ℕ) : qN n < 2 := by
  unfold qN
  omega

private def combN (v1 v2 v4 v8 n : ℕ) : ℕ :=
  (cond (Nat.beq (n % 2) 1) v1 0) ^^^ (cond (Nat.beq (n / 2 % 2) 1) v2 0) ^^^
    (cond (Nat.beq (n / 4 % 2) 1) v4 0) ^^^ (cond (Nat.beq (n / 8 % 2) 1) v8 0)

private theorem decomp : ∀ n < 16, n = (cond (Nat.beq (n % 2) 1) 1 0) ^^^
    (cond (Nat.beq (n / 2 % 2) 1) 2 0) ^^^ (cond (Nat.beq (n / 4 % 2) 1) 4 0) ^^^
    (cond (Nat.beq (n / 8 % 2) 1) 8 0) := by
  decide +kernel

section Bridge

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (φ : V ≃ₗ[ZMod 2] Vec4)

private def kn (g : GLV V) (n : ℕ) : ℕ := enc (φ (g (φ.symm (dec n))))

private theorem kn_lt (g : GLV V) (n : ℕ) : kn φ g n < 16 := enc_lt _

private theorem kn_mul (g h : GLV V) (n : ℕ) : kn φ (g * h) n = kn φ g (kn φ h n) := by
  show enc (φ (g (h (φ.symm (dec n))))) =
    enc (φ (g (φ.symm (dec (enc (φ (h (φ.symm (dec n)))))))))
  rw [dec_enc, LinearEquiv.symm_apply_apply]

private theorem kn_one {n : ℕ} (hn : n < 16) : kn φ 1 n = n := by
  show enc (φ (φ.symm (dec n))) = n
  rw [LinearEquiv.apply_symm_apply, enc_dec n hn]

private theorem kn_zero (g : GLV V) : kn φ g 0 = 0 := by
  unfold kn
  rw [dec_zero]
  have : φ.symm (0 : Vec4) = 0 := map_zero _
  rw [this, map_zero, map_zero, enc_zero]

private theorem kn_xor (g : GLV V) {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    kn φ g (a ^^^ b) = kn φ g a ^^^ kn φ g b := by
  unfold kn
  rw [dec_xor a ha b hb, ← enc_add]
  congr 1
  rw [map_add, map_add, map_add]

private theorem xor_lt16 {a b : ℕ} (ha : a < 16) (hb : b < 16) : a ^^^ b < 16 :=
  Nat.xor_lt_two_pow (n := 4) ha hb

private theorem kn_xor4 (g : GLV V) {a b c d : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16)
    (hd : d < 16) :
    kn φ g (a ^^^ b ^^^ c ^^^ d) = kn φ g a ^^^ kn φ g b ^^^ kn φ g c ^^^ kn φ g d := by
  rw [kn_xor φ g (xor_lt16 (xor_lt16 ha hb) hc) hd, kn_xor φ g (xor_lt16 ha hb) hc,
    kn_xor φ g ha hb]

private theorem cond_lt (b : Bool) {c : ℕ} (hc : c < 16) : cond b c 0 < 16 := by
  cases b <;> simp [hc]

private theorem kn_cond (g : GLV V) (b : Bool) (c : ℕ) :
    kn φ g (cond b c 0) = cond b (kn φ g c) 0 := by
  cases b
  · exact kn_zero φ g
  · rfl

private theorem kn_decomp (g : GLV V) {n : ℕ} (hn : n < 16) :
    kn φ g n = combN (kn φ g 1) (kn φ g 2) (kn φ g 4) (kn φ g 8) n := by
  have h := decomp n hn
  conv_lhs => rw [h]
  rw [kn_xor4 φ g (cond_lt _ (by norm_num)) (cond_lt _ (by norm_num)) (cond_lt _ (by norm_num))
    (cond_lt _ (by norm_num)), kn_cond, kn_cond, kn_cond, kn_cond]
  rfl

private theorem kn_iso {q : V → ZMod 2} (hφ : ∀ x, Q0 (φ x) = q x) {g : GLV V}
    (hg : g ∈ orthSub q) {n : ℕ} (hn : n < 16) : qN (kn φ g n) = qN n := by
  have h1 : ((qN (kn φ g n) : ℕ) : ZMod 2) = ((qN n : ℕ) : ZMod 2) := by
    rw [qN_eq _ (kn_lt φ g n), qN_eq n hn]
    unfold kn
    rw [dec_enc, hφ, hg, ← hφ, LinearEquiv.apply_symm_apply]
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 h1
  have h3 := qN_lt (kn φ g n)
  have h4 := qN_lt n
  omega

private def klist (g : GLV V) : List ℕ := (List.range 16).map (kn φ g)

private def tabL (v1 v2 v4 v8 : ℕ) : List ℕ := (List.range 16).map (combN v1 v2 v4 v8)

private def lcomp (a b : List ℕ) : List ℕ := b.map (fun x => a.getD x 0)

private def lid : List ℕ := List.range 16

private theorem klist_getD (g : GLV V) {n : ℕ} (hn : n < 16) :
    (klist φ g).getD n 0 = kn φ g n := by
  unfold klist
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp

private theorem klist_mul (g h : GLV V) : klist φ (g * h) = lcomp (klist φ g) (klist φ h) := by
  unfold lcomp
  show List.map (kn φ (g * h)) (List.range 16) =
    List.map (fun x => (klist φ g).getD x 0) (List.map (kn φ h) (List.range 16))
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  simp only [Function.comp]
  rw [klist_getD φ g (kn_lt φ h n), kn_mul]

private theorem klist_one : klist φ (1 : GLV V) = lid := by
  unfold klist lid
  conv_rhs => rw [← List.map_id (List.range 16)]
  apply List.map_congr_left
  intro n hn
  exact kn_one φ (by simpa using hn)

private theorem klist_inj {g h : GLV V} (e : klist φ g = klist φ h) : g = h := by
  have key : ∀ n < 16, kn φ g n = kn φ h n := by
    intro n hn
    rw [← klist_getD φ g hn, ← klist_getD φ h hn, e]
  ext x
  have := key (enc (φ x)) (enc_lt _)
  unfold kn at this
  rw [dec_enc, LinearEquiv.symm_apply_apply] at this
  have e2 : φ (g x) = φ (h x) := by
    have := congrArg dec this
    rwa [dec_enc, dec_enc] at this
  exact φ.injective e2

private theorem klist_tab (g : GLV V) :
    klist φ g = tabL (kn φ g 1) (kn φ g 2) (kn φ g 4) (kn φ g 8) := by
  unfold klist tabL
  apply List.map_congr_left
  intro n hn
  exact kn_decomp φ g (by simpa using hn)

end Bridge

section Finite

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private def allLt (k : ℕ) (p : ℕ → Bool) : Bool := (List.range k).all p

private def okB (v1 v2 v4 v8 n : ℕ) : Bool := Nat.beq (qN (combN v1 v2 v4 v8 n)) (qN n)

private def isoAllL (P : List ℕ → Bool) : Bool :=
  allLt 16 fun v1 => !(allLt 2 fun n => okB v1 0 0 0 n) ||
  allLt 16 fun v2 => !(allLt 4 fun n => okB v1 v2 0 0 n) ||
  allLt 16 fun v4 => !(allLt 8 fun n => okB v1 v2 v4 0 n) ||
  allLt 16 fun v8 => !(allLt 16 fun n => okB v1 v2 v4 v8 n) || P (tabL v1 v2 v4 v8)

private theorem allLt_spec {k : ℕ} {p : ℕ → Bool} :
    allLt k p = true ↔ ∀ n < k, p n = true := by
  simp [allLt, List.all_eq_true, List.mem_range]

private theorem combN_lt2 {v1 v2 v4 v8 n : ℕ} (hn : n < 2) :
    combN v1 v2 v4 v8 n = combN v1 0 0 0 n := by
  interval_cases n <;> rfl

private theorem combN_lt4 {v1 v2 v4 v8 n : ℕ} (hn : n < 4) :
    combN v1 v2 v4 v8 n = combN v1 v2 0 0 n := by
  interval_cases n <;> rfl

private theorem combN_lt8 {v1 v2 v4 v8 n : ℕ} (hn : n < 8) :
    combN v1 v2 v4 v8 n = combN v1 v2 v4 0 n := by
  interval_cases n <;> rfl

private theorem isoAllL_spec {P : List ℕ → Bool} (h : isoAllL P = true) {v1 v2 v4 v8 : ℕ}
    (h1 : v1 < 16) (h2 : v2 < 16) (h4 : v4 < 16) (h8 : v8 < 16)
    (hq : ∀ n < 16, qN (combN v1 v2 v4 v8 n) = qN n) : P (tabL v1 v2 v4 v8) = true := by
  unfold isoAllL at h
  rw [allLt_spec] at h
  have e1 : (allLt 2 fun n => okB v1 0 0 0 n) = true := by
    rw [allLt_spec]
    intro n hn
    unfold okB
    rw [← combN_lt2 (v2 := v2) (v4 := v4) (v8 := v8) hn, hq n (by omega)]
    simp
  have e2 : (allLt 4 fun n => okB v1 v2 0 0 n) = true := by
    rw [allLt_spec]
    intro n hn
    unfold okB
    rw [← combN_lt4 (v4 := v4) (v8 := v8) hn, hq n (by omega)]
    simp
  have e4 : (allLt 8 fun n => okB v1 v2 v4 0 n) = true := by
    rw [allLt_spec]
    intro n hn
    unfold okB
    rw [← combN_lt8 (v8 := v8) hn, hq n (by omega)]
    simp
  have e8 : (allLt 16 fun n => okB v1 v2 v4 v8 n) = true := by
    rw [allLt_spec]
    intro n hn
    unfold okB
    rw [hq n hn]
    simp
  have := h v1 h1
  rw [e1] at this
  simp only [Bool.not_true, Bool.false_or] at this
  rw [allLt_spec] at this
  have := this v2 h2
  rw [e2] at this
  simp only [Bool.not_true, Bool.false_or] at this
  rw [allLt_spec] at this
  have := this v4 h4
  rw [e4] at this
  simp only [Bool.not_true, Bool.false_or] at this
  rw [allLt_spec] at this
  have := this v8 h8
  rw [e8] at this
  simpa using this

private theorem isoAll_apply {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {P : List ℕ → Bool} (h : isoAllL P = true) {g : GLV V}
    (hg : g ∈ orthSub q) : P (klist φ g) = true := by
  rw [klist_tab]
  exact isoAllL_spec h (kn_lt φ g 1) (kn_lt φ g 2) (kn_lt φ g 4) (kn_lt φ g 8)
    (fun n hn => by rw [← kn_decomp φ g hn]; exact kn_iso φ hφ hg hn)

end Finite

section Facts

private def lsq (a : List ℕ) : List ℕ := lcomp a a

private def lcube (a : List ℕ) : List ℕ := lcomp a (lcomp a a)

private def lp9 (a : List ℕ) : List ℕ := lcube (lcube a)

private def ord4 (a : List ℕ) : Bool := !(lsq a == lid) && (lsq (lsq a) == lid)

private def n1L : List ℕ := tabL 4 12 15 6

private def n2L : List ℕ := tabL 6 15 3 2

private def n3L : List ℕ := tabL 2 3 12 4

private def lpw (a : List ℕ) : ℕ → List ℕ
  | 0 => lid
  | k + 1 => lcomp (lpw a k) a

private def Elist : List (List ℕ) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => lcomp (lpw n1L i) (lpw n2L j)

private theorem Elist_nodup : Elist.Nodup := by decide +kernel

private theorem Elist_length : Elist.length = 9 := by decide +kernel

private theorem n1L_mem : n1L ∈ Elist := by decide +kernel

private theorem n3L_mem : n3L ∈ Elist := by decide +kernel

private theorem n1L_ord : lcube n1L = lid ∧ n1L ≠ lid := by decide +kernel

private theorem n3L_ord : lcube n3L = lid ∧ n3L ≠ lid := by decide +kernel

private def normB (n : List ℕ) (T : List (List ℕ)) (a : List ℕ) : Bool :=
  T.any fun m => lcomp a n == lcomp m a

private def T1L : List (List ℕ) := [lid, n1L, lsq n1L]

private def T3L : List (List ℕ) := [lid, n3L, lsq n3L]

private def tsPlane (a b : ℕ) : Bool :=
  !(Nat.beq a 0) && !(Nat.beq b 0) && !(Nat.beq a b) && Nat.beq (qN a) 0 && Nat.beq (qN b) 0 &&
    Nat.beq (qN (a ^^^ b)) 0

private def movesPlane (L : List ℕ) (a b : ℕ) : Bool :=
  [a, b, a ^^^ b].any fun x => !([0, a, b, a ^^^ b].contains (L.getD x 0))

private def factA (L : List ℕ) : Bool := !(lp9 L == lid) || Elist.contains L

private def factB (L : List ℕ) : Bool := normB n1L T1L L || normB n3L T3L L || ord4 L

private def factC (L : List ℕ) : Bool :=
  !(ord4 L) || allLt 16 fun a => allLt 16 fun b => !(tsPlane a b) || movesPlane L a b

private def leafAll (L : List ℕ) : Bool := factA L && factB L && factC L

private theorem finite_facts : isoAllL leafAll = true := by decide +kernel

end Facts

section Group

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem klist_cube (φ : V ≃ₗ[ZMod 2] Vec4) (g : GLV V) :
    lcube (klist φ g) = klist φ (g ^ 3) := by
  unfold lcube
  rw [pow_three, klist_mul φ g (g * g), klist_mul φ g g]

private theorem klist_p9 (φ : V ≃ₗ[ZMod 2] Vec4) (g : GLV V) :
    lp9 (klist φ g) = klist φ (g ^ 9) := by
  unfold lp9
  rw [klist_cube, klist_cube, ← pow_mul]

private theorem klist_sq (φ : V ≃ₗ[ZMod 2] Vec4) (g : GLV V) :
    lsq (klist φ g) = klist φ (g * g) :=
  (klist_mul φ g g).symm

private theorem ord4_iff (φ : V ≃ₗ[ZMod 2] Vec4) (g : GLV V) :
    ord4 (klist φ g) = true ↔ orderOf g = 4 := by
  have hP : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hid : lid = klist φ (1 : GLV V) := (klist_one φ).symm
  unfold ord4
  rw [klist_sq, klist_sq φ (g * g), hid]
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : g * g ≠ 1 := fun h => h1 (by rw [h])
    have h2' : g * g * (g * g) = 1 := klist_inj φ h2
    have e := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g)
      (by simpa [pow_two] using h1') (by
        have : g ^ 2 ^ (1 + 1) = g * g * (g * g) := by
          rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
          simp [pow_succ, mul_assoc]
        rw [this]
        exact h2')
    simpa using e
  · intro h
    have h4 : g ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one g
    have h2 : g * g ≠ 1 := by
      intro h2
      have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      rw [h] at this
      omega
    refine ⟨fun e => h2 (klist_inj φ e), ?_⟩
    have : g * g * (g * g) = 1 := by
      rw [← h4]
      simp [pow_succ, mul_assoc]
    rw [this]

private theorem exists_mem_of_Elist [Finite V] {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {P : Subgroup (GLV V)} (hPq : P ≤ orthSub q)
    (hP9 : Nat.card P = 9) : ∀ L ∈ Elist, ∃ g ∈ P, klist φ g = L := by
  classical
  have hmem : ∀ g ∈ P, klist φ g ∈ Elist := by
    intro g hg
    have h9 : g ^ 9 = 1 := by
      have h1 : orderOf (⟨g, hg⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
      rw [hP9] at h1
      have h2 : (⟨g, hg⟩ : P) ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
      exact congrArg Subtype.val h2
    have hA := isoAll_apply hφ finite_facts (hPq hg)
    have hA' : factA (klist φ g) = true := by
      simp only [leafAll, Bool.and_eq_true] at hA
      exact hA.1.1
    unfold factA at hA'
    rw [klist_p9, h9, klist_one] at hA'
    simpa using hA'
  have : Fintype P := Fintype.ofFinite P
  let S1 : Finset (List ℕ) := Finset.univ.image fun g : P => klist φ (g : GLV V)
  have hS1card : S1.card = 9 := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_eq_nat_card, hP9]
    intro a b hab
    exact Subtype.ext (klist_inj φ hab)
  have hsub : S1 ⊆ Elist.toFinset := by
    intro L hL
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hL
    exact List.mem_toFinset.2 (hmem g g.2)
  have hE : Elist.toFinset.card = 9 := by
    rw [List.toFinset_card_of_nodup Elist_nodup, Elist_length]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hS1card, hE])
  intro L hL
  have : L ∈ S1 := by rw [heq]; exact List.mem_toFinset.2 hL
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 this
  exact ⟨g, g.2, rfl⟩

private theorem exists_order_three {φ : V ≃ₗ[ZMod 2] Vec4} {nL : List ℕ}
    (hcube : lcube nL = lid) (hne : nL ≠ lid) {n' : GLV V} (hn : klist φ n' = nL) :
    n' ^ 3 = 1 ∧ n' ≠ 1 ∧ Nat.card (Subgroup.zpowers n') = 3 := by
  have hP : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : n' ^ 3 = 1 := by
    apply klist_inj φ
    rw [← klist_cube, hn, hcube, klist_one]
  have h1 : n' ≠ 1 := by
    intro h
    apply hne
    rw [← hn, h, klist_one]
  refine ⟨h3, h1, ?_⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime h3 h1

private theorem normB_conj_mem {φ : V ≃ₗ[ZMod 2] Vec4} {n' g : GLV V} {nL : List ℕ}
    (hn : klist φ n' = nL) (hg : normB nL [lid, nL, lsq nL] (klist φ g) = true) :
    g * n' * g⁻¹ ∈ Subgroup.zpowers n' := by
  unfold normB at hg
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hg
  have hmul : ∀ m' : GLV V, lcomp (klist φ g) nL = lcomp (klist φ m') (klist φ g) →
      g * n' * g⁻¹ = m' := by
    intro m' h
    rw [mul_inv_eq_iff_eq_mul]
    apply klist_inj φ
    rw [klist_mul, klist_mul, hn]
    exact h
  rcases hg with h | h | h
  · rw [hmul 1 (by rw [klist_one]; exact h)]
    exact Subgroup.one_mem _
  · rw [hmul n' (by rw [hn]; exact h)]
    exact Subgroup.mem_zpowers n'
  · rw [hmul (n' * n') (by rw [klist_mul, hn]; exact h)]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers n') (Subgroup.mem_zpowers n')

private theorem mem_normalizer_zpowers [Finite V] {n a : GLV V}
    (h : a * n * a⁻¹ ∈ Subgroup.zpowers n) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers n : Set (GLV V)) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ h k

private theorem line_lemma [Finite V] {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {Γ P : Subgroup (GLV V)} (hΓ : Γ ≤ orthSub q) (hPΓ : P ≤ Γ)
    (hP9 : Nat.card P = 9)
    (hnoN : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      Nat.card N ≠ 3)
    {nL : List ℕ} (hmem : nL ∈ Elist) (hcube : lcube nL = lid) (hne : nL ≠ lid) :
    ∃ N : Subgroup (GLV V), (∃ a ∈ Γ, a ∉ Subgroup.normalizer (N : Set (GLV V))) ∧
      ∀ g : GLV V, normB nL [lid, nL, lsq nL] (klist φ g) = true →
        g ∈ Subgroup.normalizer (N : Set (GLV V)) := by
  obtain ⟨n', hn'P, hn'K⟩ := exists_mem_of_Elist hφ (hPΓ.trans hΓ) hP9 nL hmem
  obtain ⟨h3, h1, hcard⟩ := exists_order_three hcube hne hn'K
  refine ⟨Subgroup.zpowers n', ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    refine hnoN (Subgroup.zpowers n') ((Subgroup.zpowers_le).2 (hPΓ hn'P)) ?_ hcard
    intro γ hγ n hn
    exact (Subgroup.mem_normalizer_iff.1 (hcon γ hγ) n).1 hn
  · intro g hg
    exact mem_normalizer_zpowers (normB_conj_mem hn'K hg)

private theorem exists_ord4 [Finite V] {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ orthSub q)
    (h9 : 9 ∣ Nat.card Γ)
    (hnoN : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      Nat.card N ≠ 3) :
    ∃ x ∈ Γ, ord4 (klist φ x) = true := by
  obtain ⟨P, hP9, -, hPΓ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := GLV V)
    Nat.prime_three (n := 2) (H := ⊥) (L := Γ) (by simp) (by simpa using h9) bot_le
  have hP9' : Nat.card P = 9 := by simpa using hP9
  obtain ⟨N1, ⟨a, haΓ, haN⟩, hN1⟩ :=
    line_lemma hφ hΓ hPΓ hP9' hnoN n1L_mem n1L_ord.1 n1L_ord.2
  obtain ⟨N3, ⟨b, hbΓ, hbN⟩, hN3⟩ :=
    line_lemma hφ hΓ hPΓ hP9' hnoN n3L_mem n3L_ord.1 n3L_ord.2
  have hfactB : ∀ g ∈ orthSub q, normB n1L T1L (klist φ g) = true ∨
      normB n3L T3L (klist φ g) = true ∨ ord4 (klist φ g) = true := by
    intro g hg
    have hB := isoAll_apply hφ finite_facts hg
    simp only [leafAll, Bool.and_eq_true] at hB
    have := hB.1.2
    unfold factB at this
    simpa [Bool.or_eq_true, or_assoc] using this
  by_cases h1 : ord4 (klist φ a) = true
  · exact ⟨a, haΓ, h1⟩
  by_cases h2 : ord4 (klist φ b) = true
  · exact ⟨b, hbΓ, h2⟩
  refine ⟨a * b, Γ.mul_mem haΓ hbΓ, ?_⟩
  by_contra h3
  have ha1 : ¬ (normB n1L T1L (klist φ a) = true) := fun h => haN (hN1 a h)
  have hb3 : ¬ (normB n3L T3L (klist φ b) = true) := fun h => hbN (hN3 b h)
  have ha3 : normB n3L T3L (klist φ a) = true := by
    rcases hfactB a (hΓ haΓ) with h | h | h
    · exact absurd h ha1
    · exact h
    · exact absurd h h1
  have hb1 : normB n1L T1L (klist φ b) = true := by
    rcases hfactB b (hΓ hbΓ) with h | h | h
    · exact h
    · exact absurd h hb3
    · exact absurd h h2
  rcases hfactB (a * b) (hΓ (Γ.mul_mem haΓ hbΓ)) with h | h | h
  · apply haN
    have := (Subgroup.normalizer (N1 : Set (GLV V))).mul_mem (hN1 _ h)
      ((Subgroup.normalizer (N1 : Set (GLV V))).inv_mem (hN1 b hb1))
    simpa using this
  · apply hbN
    have := (Subgroup.normalizer (N3 : Set (GLV V))).mul_mem
      ((Subgroup.normalizer (N3 : Set (GLV V))).inv_mem (hN3 a ha3)) (hN3 _ h)
    simpa using this
  · exact h3 h

private theorem orderOf_conj_eq {G : Type*} [Group G] (g s : G) :
    orderOf (g * s * g⁻¹) = orderOf s := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [conj_pow]
  constructor
  · intro h
    have h1 : g * s ^ n = g := mul_inv_eq_one.1 h
    simpa using h1
  · intro h
    rw [h]
    simp

private theorem exists_mem_sylow_of_orderOf {G : Type*} [Group G] [Finite G] {Γ S : Subgroup G}
    (hS : IsSylowTwoOf S Γ) {x : G} (hxΓ : x ∈ Γ) (hx : orderOf x = 4) :
    ∃ y ∈ S, orderOf y = 4 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSΓ, hS2, hSidx⟩ := hS
  have hS'2 : IsPGroup 2 (S.subgroupOf Γ) :=
    IsPGroup.of_equiv hS2 (Subgroup.subgroupOfEquivOfLe hSΓ).symm
  let SS : Sylow 2 Γ := hS'2.toSylow hSidx
  let x' : Γ := ⟨x, hxΓ⟩
  have hx' : orderOf x' = 4 := by rw [Subgroup.orderOf_mk]; exact hx
  have hX2 : IsPGroup 2 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx']; norm_num)
  obtain ⟨Q, hXQ⟩ := hX2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ SS Q
  have hxQ : x' ∈ (Q : Subgroup Γ) := hXQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  have hsx' : g * s * g⁻¹ = x' := by simpa [MulAut.smul_def] using hsx
  refine ⟨(s : G), ?_, ?_⟩
  · exact (Subgroup.mem_subgroupOf.1 hs)
  · rw [Subgroup.orderOf_coe, ← orderOf_conj_eq g s, hsx', hx']

end Group

section Planes

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_basis_two [Finite V] {P : Submodule (ZMod 2) V}
    (hP : Module.finrank (ZMod 2) P = 2) :
    ∃ p1 p2 : V, p1 ∈ P ∧ p2 ∈ P ∧ p1 ≠ 0 ∧ p2 ≠ 0 ∧ p1 ≠ p2 ∧
      ∀ z ∈ P, z = 0 ∨ z = p1 ∨ z = p2 ∨ z = p1 + p2 := by
  have : Module.Finite (ZMod 2) P := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) P hP
  refine ⟨(b 0 : V), (b 1 : V), (b 0).2, (b 1).2, ?_, ?_, ?_, ?_⟩
  · intro h
    exact b.ne_zero 0 (Subtype.ext h)
  · intro h
    exact b.ne_zero 1 (Subtype.ext h)
  · intro h
    have := b.injective (Subtype.ext h)
    exact absurd this (by decide)
  · intro z hz
    have hs := b.sum_repr ⟨z, hz⟩
    rw [Fin.sum_univ_two] at hs
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have hz' : z = (b.repr ⟨z, hz⟩ 0) • (b 0 : V) + (b.repr ⟨z, hz⟩ 1) • (b 1 : V) :=
      congrArg Subtype.val hs.symm
    rcases hc (b.repr ⟨z, hz⟩ 0) with h0 | h0 <;> rcases hc (b.repr ⟨z, hz⟩ 1) with h1 | h1 <;>
      simp [h0, h1] at hz' <;> simp [hz']

private theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff]
  intro h2
  exact h (Nat.eq_of_beq_eq_true h2)

private theorem kn_enc (φ : V ≃ₗ[ZMod 2] Vec4) (g : GLV V) (p : V) :
    kn φ g (enc (φ p)) = enc (φ (g p)) := by
  unfold kn
  rw [dec_enc, LinearEquiv.symm_apply_apply]

private theorem qN_enc_zero {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {z : V} (hz : q z = 0) : qN (enc (φ z)) = 0 := by
  have h1 : ((qN (enc (φ z)) : ℕ) : ZMod 2) = 0 := by
    rw [qN_eq _ (enc_lt _), dec_enc, hφ, hz]
  have h2 := (ZMod.natCast_eq_zero_iff _ 2).1 h1
  have h3 := qN_lt (enc (φ z))
  omega

private theorem enc_phi_ne_zero {φ : V ≃ₗ[ZMod 2] Vec4} {z : V} (hz : z ≠ 0) :
    enc (φ z) ≠ 0 := by
  intro h
  apply hz
  have := congrArg dec h
  rw [dec_enc, dec_zero] at this
  exact φ.injective (by rw [this]; exact (map_zero φ).symm)

private theorem enc_phi_injective {φ : V ≃ₗ[ZMod 2] Vec4} {z w : V}
    (h : enc (φ z) = enc (φ w)) : z = w := by
  have := congrArg dec h
  rw [dec_enc, dec_enc] at this
  exact φ.injective this

private theorem moves_plane [Finite V] {q : V → ZMod 2} {φ : V ≃ₗ[ZMod 2] Vec4}
    (hφ : ∀ x, Q0 (φ x) = q x) {y : GLV V} (hy : y ∈ orthSub q)
    (hord : ord4 (klist φ y) = true) (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 2) (hq0 : ∀ x ∈ P, q x = 0) : ∃ p ∈ P, y p ∉ P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p1, p2, hp1, hp2, hp10, hp20, hp12, hP4⟩ := exists_basis_two hP
  have hC := isoAll_apply hφ finite_facts hy
  simp only [leafAll, Bool.and_eq_true] at hC
  have hC' := hC.2
  unfold factC at hC'
  rw [hord] at hC'
  simp only [Bool.not_true, Bool.false_or] at hC'
  rw [allLt_spec] at hC'
  have hp12P : p1 + p2 ∈ P := P.add_mem hp1 hp2
  have hab : enc (φ (p1 + p2)) = enc (φ p1) ^^^ enc (φ p2) := by rw [map_add, enc_add]
  have hmovesP := hC' (enc (φ p1)) (enc_lt _)
  rw [allLt_spec] at hmovesP
  have hmovesP := hmovesP (enc (φ p2)) (enc_lt _)
  have hts : tsPlane (enc (φ p1)) (enc (φ p2)) = true := by
    unfold tsPlane
    have e1 : Nat.beq (enc (φ p1)) 0 = false := beq_false_of_ne (enc_phi_ne_zero hp10)
    have e2 : Nat.beq (enc (φ p2)) 0 = false := beq_false_of_ne (enc_phi_ne_zero hp20)
    have e3 : Nat.beq (enc (φ p1)) (enc (φ p2)) = false :=
      beq_false_of_ne fun h => hp12 (enc_phi_injective h)
    have e4 : Nat.beq (qN (enc (φ p1))) 0 = true := by
      rw [Nat.beq_eq]
      exact qN_enc_zero hφ (hq0 p1 hp1)
    have e5 : Nat.beq (qN (enc (φ p2))) 0 = true := by
      rw [Nat.beq_eq]
      exact qN_enc_zero hφ (hq0 p2 hp2)
    have e6 : Nat.beq (qN (enc (φ p1) ^^^ enc (φ p2))) 0 = true := by
      rw [← hab, Nat.beq_eq]
      exact qN_enc_zero hφ (hq0 _ hp12P)
    rw [e1, e2, e3, e4, e5, e6]
    rfl
  rw [hts] at hmovesP
  simp only [Bool.not_true, Bool.false_or] at hmovesP
  unfold movesPlane at hmovesP
  obtain ⟨x, hx, hxn⟩ := List.any_eq_true.1 hmovesP
  have hxz : ∃ z ∈ P, enc (φ z) = x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨p1, hp1, rfl⟩
    · exact ⟨p2, hp2, rfl⟩
    · exact ⟨p1 + p2, hp12P, hab⟩
  obtain ⟨z, hzP, rfl⟩ := hxz
  rw [klist_getD φ y (enc_lt _), kn_enc] at hxn
  have hyz := hcon z hzP
  have hmem : enc (φ (y z)) ∈ [0, enc (φ p1), enc (φ p2), enc (φ p1) ^^^ enc (φ p2)] := by
    rcases hP4 _ hyz with h | h | h | h
    · rw [h]
      simp [enc_zero]
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h, hab]
      simp
  simp [hmem] at hxn

end Planes

section ExistsPhi

open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply)

private theorem exists_phi {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {f : LinearMap.BilinForm (ZMod 2) V} {q : V → ZMod 2} (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hq)) :
    ∃ φ : V ≃ₗ[ZMod 2] Vec4, ∀ x, Q0 (φ x) = q x := by
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus (K := ZMod 2)
    (p4insporth_nondegenerate_quad hf hq) (n := 2) (by omega) hplus
  refine ⟨e.toLinearEquiv.trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finSumFinEquiv (m := 2) (n := 2))).symm,
    fun x => ?_⟩
  have h1 := e.map_app x
  rw [quadPlus_apply, Fin.sum_univ_two] at h1
  have h2 : p4insporth_quad hq x = q x := rfl
  rw [h2] at h1
  rw [← h1]
  rfl

end ExistsPhi

end O4Aux

theorem isPlusType_of_nine_dvd {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {f : LinearMap.BilinForm (ZMod 2) V} {q : V → ZMod 2} (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) V = 4)
    {Γ : Subgroup (GLV V)} (hΓ : Γ ≤ orthSub q) (h9 : 9 ∣ Nat.card Γ) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hq) := by
  by_contra hminus
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
    (p4insporth_nondegenerate_quad hf hq) (m := 1) (by omega) (ε := -1) (Or.inr ⟨rfl, hminus⟩)
  rw [p4insporth_orthogonalGroup_quad hq, Nat.card_zmod] at h
  norm_num [Finset.Icc_self] at h
  have h120 : Nat.card ↥(orthSub q) = 120 := by exact_mod_cast h
  have hd := Subgroup.card_dvd_of_le hΓ
  rw [h120] at hd
  have := dvd_trans h9 hd
  omega

theorem o4plus_overgroup {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {f : LinearMap.BilinForm (ZMod 2) V} {q : V → ZMod 2} (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) V = 4)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad hq))
    {Γ S : Subgroup (GLV V)} (hΓ : Γ ≤ orthSub q) (hS : IsSylowTwoOf S Γ)
    (h9 : 9 ∣ Nat.card Γ)
    (hnoN : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      Nat.card N ≠ 3) :
    Γ = orthSub q ∨ ((∃ y : GLV V, S = Subgroup.zpowers y ∧ orderOf y = 4) ∧
      ∀ P : Submodule (ZMod 2) V, Module.finrank (ZMod 2) P = 2 → (∀ x ∈ P, q x = 0) →
        ∃ s ∈ S, ∃ p ∈ P, s p ∉ P) := by
  obtain ⟨φ, hφ⟩ := O4Aux.exists_phi hf hq hdim hplus
  have h72 : Nat.card (orthSub q) = 72 := p4insporth_card_plus_four hf hq hdim hplus
  obtain ⟨x, hxΓ, hx⟩ := O4Aux.exists_ord4 hφ hΓ h9 hnoN
  have hx4 : orderOf x = 4 := (O4Aux.ord4_iff φ x).1 hx
  have hdvd72 : Nat.card Γ ∣ 72 := h72 ▸ Subgroup.card_dvd_of_le hΓ
  have h4 : 4 ∣ Nat.card Γ := by
    have := orderOf_dvd_natCard (⟨x, hxΓ⟩ : Γ)
    rwa [Subgroup.orderOf_mk, hx4] at this
  have h36 : 36 ∣ Nat.card Γ := by
    have hcop : Nat.Coprime 4 9 := by norm_num
    exact hcop.mul_dvd_of_dvd_of_dvd h4 h9
  have hle : Nat.card Γ ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd72
  have hpos : 0 < Nat.card Γ := Nat.card_pos
  have hc : Nat.card Γ = 36 ∨ Nat.card Γ = 72 := by omega
  rcases hc with hc | hc
  · right
    have hS4 : Nat.card S = 4 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
      have h1 := Subgroup.relIndex_mul_card S Γ
      rw [inf_eq_left.2 hS.1, hk, hc] at h1
      have hodd : ¬ 2 ∣ S.relIndex Γ := hS.2.2
      rcases k with _ | _ | _ | _ | k
      · exfalso
        apply hodd
        have : S.relIndex Γ = 36 := by simpa using h1
        rw [this]
        norm_num
      · exfalso
        apply hodd
        have : S.relIndex Γ = 18 := by omega
        rw [this]
        norm_num
      · rw [hk]
        norm_num
      · exfalso
        omega
      · exfalso
        have : 16 ∣ 36 := ⟨S.relIndex Γ * 2 ^ k, by rw [← h1]; ring⟩
        omega
    obtain ⟨y, hyS, hy4⟩ := O4Aux.exists_mem_sylow_of_orderOf hS hxΓ hx4
    have hSy : S = Subgroup.zpowers y := by
      symm
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyS)
      rw [hS4, Nat.card_zpowers, hy4]
    refine ⟨⟨y, hSy, hy4⟩, fun P hP hq0 => ?_⟩
    have hyO : y ∈ orthSub q := hΓ (hS.1 hyS)
    obtain ⟨p, hpP, hpn⟩ := O4Aux.moves_plane hφ hyO ((O4Aux.ord4_iff φ y).2 hy4) P hP hq0
    exact ⟨y, hyS, p, hpP, hpn⟩
  · left
    exact Subgroup.eq_of_le_of_card_ge hΓ (by rw [hc, h72])

end S143V

end CFSG.Quasithin
