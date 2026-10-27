module

public import CFSG.Quasithin.Vol2.Ch12Sec6L22
public import Certificates.Certificate7158

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 Equiv

namespace S126L22F

open S8E

theorem checks : K0 ∧ K34 := by
  have h := Certificates.certificate7158
  simp only [s8Check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

@[expose] def L (σ : Perm (Fin 8)) : List ℕ := List.ofFn fun i => (σ i).val

theorem L_eq (σ : Perm (Fin 8)) :
    L σ = [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val, (σ 5).val, (σ 6).val,
      (σ 7).val] := rfl

theorem ap_L (σ : Perm (Fin 8)) (i : Fin 8) : ap (L σ) i.val = (σ i).val := by
  fin_cases i <;> rfl

theorem L_one : L 1 = id8 := rfl

theorem L_inj {σ τ : Perm (Fin 8)} (h : L σ = L τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext (congrFun (List.ofFn_injective h) i)

theorem cmp_L (σ τ : Perm (Fin 8)) : S8E.cmp (L σ) (L τ) = L (σ * τ) := by
  rw [S8E.cmp, show L τ = List.ofFn fun i => (τ i).val from rfl, List.map_ofFn]
  exact congrArg List.ofFn (funext fun i => ap_L σ (τ i))

theorem comm_L {σ τ : Perm (Fin 8)} (h : σ * τ = τ * σ) : CommL (L σ) (L τ) := by
  unfold CommL
  rw [cmp_L, cmp_L, h]

theorem not_mem_map_L {σ : Perm (Fin 8)} {l : List (Perm (Fin 8))} (h : σ ∉ l) :
    L σ ∉ l.map L := fun hm => by
  obtain ⟨τ, hτ, e⟩ := List.mem_map.1 hm
  exact h (L_inj e ▸ hτ)

theorem mem_id8 (i : Fin 8) : i.val ∈ id8 := by
  fin_cases i <;> decide

theorem lt_of_mem_id8 : ∀ p ∈ id8, p < 8 := by
  decide

theorem fix_iff (σ : Perm (Fin 8)) (p : Fin 8) : ap (L σ) p.val = p.val ↔ σ p = p := by
  rw [ap_L, Fin.val_inj]

theorem fpf_L {σ : Perm (Fin 8)} (h : Fpf (L σ)) (i : Fin 8) : σ i ≠ i := fun e =>
  h i.val (mem_id8 i) ((fix_iff σ i).2 e)

theorem prt_val (v : Fin 8) : prt v.val = (partner v).val := by
  fin_cases v <;> rfl

theorem L_eq_ext4 {σ : Perm (Fin 8)} (h : ∀ i, σ (partner i) = partner (σ i)) :
    L σ = ext4 (σ 0).val (σ 2).val (σ 4).val (σ 6).val := by
  rw [L_eq, ext4, prt_val, prt_val, prt_val, prt_val, ← h 0, ← h 2, ← h 4, ← h 6]
  rfl

theorem halves_L {σ : Perm (Fin 8)}
    (h : (∀ i : Fin 8, i.val < 4 → (σ i).val < 4) ∨ ∀ i : Fin 8, i.val < 4 → 4 ≤ (σ i).val) :
    Halves (L σ) := by
  have key : ∀ i ∈ [0, 1, 2, 3], ∃ j : Fin 8, j.val = i ∧ j.val < 4 := by decide
  rcases h with h | h
  · refine Or.inl fun i hi => ?_
    obtain ⟨j, rfl, hj⟩ := key i hi
    rw [ap_L]
    exact h j hj
  · refine Or.inr fun i hi => ?_
    obtain ⟨j, rfl, hj⟩ := key i hi
    rw [ap_L]
    exact h j hj

theorem mem_INV (hK0 : K0) {σ : Perm (Fin 8)} (hσ : σ ∈ S126Ex.presSub) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : L σ ∈ INV := by
  have hp := S126Ex.presPart_of_mem hσ
  have he := L_eq_ext4 hp.1
  have hinv : S8E.cmp (L σ) (L σ) = id8 := by rw [cmp_L, h2, L_one]
  have hne : L σ ≠ id8 := fun h => h1 (L_inj (h.trans L_one.symm))
  have hh := halves_L hp.2
  rw [he] at hinv hne hh ⊢
  exact hK0 _ (mem_id8 _) _ (mem_id8 _) _ (mem_id8 _) _ (mem_id8 _) hinv hh hne

theorem exists_iv {l : List ℕ} (h : l ∈ INV) : ∃ n < 43, iv n = l := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem h
  exact ⟨n, hn, List.getD_eq_getElem _ _ hn⟩

variable {B : Subgroup (Perm (Fin 8))}

theorem exists_not_mem {s : List (Perm (Fin 8))} (hs : s.length < Nat.card B) :
    ∃ σ ∈ B, σ ∉ s := by
  by_contra hcon
  have h1 := S126F.card_le_of_forall_mem B s.toFinset fun x hx =>
    List.mem_toFinset.2 (by_contra fun h => hcon ⟨x, hx, h⟩)
  have h2 := s.toFinset_card_le
  omega

theorem exists_min (hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV) {s : List (Perm (Fin 8))} (h1 : 1 ∈ s)
    (hs : s.length < Nat.card B) :
    ∃ σ ∈ B, σ ∉ s ∧ ∃ n < 43, iv n = L σ ∧
      ∀ τ ∈ B, τ ∉ s → ∀ m < 43, iv m = L τ → n ≤ m := by
  classical
  have hP : ∃ n, n < 43 ∧ ∃ σ ∈ B, σ ∉ s ∧ iv n = L σ := by
    obtain ⟨σ, hσ, hσs⟩ := exists_not_mem hs
    obtain ⟨n, hn, he⟩ := exists_iv (hI σ hσ fun h => hσs (h ▸ h1))
    exact ⟨n, hn, σ, hσ, hσs, he⟩
  obtain ⟨hn, σ, hσ, hσs, he⟩ := Nat.find_spec hP
  exact ⟨σ, hσ, hσs, Nat.find hP, hn, he, fun τ hτ hτs m hm hme =>
    Nat.find_min' hP ⟨hm, τ, hτ, hτs, hme⟩⟩

theorem lt_of_min {s t : List (Perm (Fin 8))} (hst : ∀ τ, τ ∉ t → τ ∉ s) {σ τ : Perm (Fin 8)}
    {n m : ℕ} (hn : iv n = L σ) (hmin : ∀ τ ∈ B, τ ∉ s → ∀ m < 43, iv m = L τ → n ≤ m)
    (hσt : σ ∈ t) (hτ : τ ∈ B) (hτt : τ ∉ t) (hm : m < 43) (hme : iv m = L τ) : n < m := by
  refine lt_of_le_of_ne (hmin τ hτ (hst τ hτt) m hm hme) fun h => hτt ?_
  subst h
  rw [← L_inj (hn.symm.trans hme)]
  exact hσt

@[expose] def prods3 (x y z : Perm (Fin 8)) : List (Perm (Fin 8)) :=
  [1, x, y, z, x * y, x * z, y * z, x * (y * z)]

@[expose] def prods4 (x y z w : Perm (Fin 8)) : List (Perm (Fin 8)) :=
  prods3 x y z ++ (prods3 x y z).map fun f => f * w

theorem grp3_L (x y z : Perm (Fin 8)) : grp3 (L x) (L y) (L z) = (prods3 x y z).map L := by
  simp only [grp3, prods3, List.map_cons, List.map_nil, cmp_L, L_one]

theorem grp4_L (x y z w : Perm (Fin 8)) :
    grp4 ((prods3 x y z).map L) (L w) = (prods4 x y z w).map L := by
  rw [grp4, prods4, List.map_append, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun f _ => cmp_L f w

theorem prods3_mem {x y z : Perm (Fin 8)} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) :
    ∀ f ∈ prods3 x y z, f ∈ B := by
  simp only [prods3, List.mem_cons, List.not_mem_nil, or_false]
  rintro f (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  exacts [B.one_mem, hx, hy, hz, B.mul_mem hx hy, B.mul_mem hx hz, B.mul_mem hy hz,
    B.mul_mem hx (B.mul_mem hy hz)]

theorem prods4_mem {x y z w : Perm (Fin 8)} (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
    (hw : w ∈ B) : ∀ f ∈ prods4 x y z w, f ∈ B := by
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · exact prods3_mem hx hy hz f h
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h
    exact B.mul_mem (prods3_mem hx hy hz g hg) hw

theorem chain3 (hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV) (hB : 4 < Nat.card B) :
    ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ i j k : ℕ, i < j ∧ j < k ∧ k < 43 ∧ iv i = L x ∧
      iv j = L y ∧ iv k = L z ∧ z ∉ [1, x, y, x * y] ∧
      ∀ τ ∈ B, τ ∉ [1, x, y, x * y] → ∀ m < 43, iv m = L τ → k ≤ m := by
  obtain ⟨x, hx, -, i, -, hix, hxm⟩ := exists_min hI (s := [1]) (by simp) (by simp; omega)
  obtain ⟨y, hy, hys, j, hj, hjy, hym⟩ := exists_min hI (s := [1, x]) (by simp) (by simp; omega)
  obtain ⟨z, hz, hzs, k, hk, hkz, hzm⟩ :=
    exists_min hI (s := [1, x, y, x * y]) (by simp) (by simp; omega)
  have hij : i < j := lt_of_min (s := [1]) (t := [1, x]) (fun τ h h' => h (by simp_all))
    hix hxm (by simp) hy hys hj hjy
  have hjk : j < k := lt_of_min (s := [1, x]) (t := [1, x, y, x * y])
    (fun τ h h' => h (by simp_all)) hjy hym (by simp) hz hzs hk hkz
  exact ⟨x, hx, y, hy, z, hz, i, j, k, hij, hjk, hk, hix, hjy, hkz, hzs, hzm⟩

@[expose] def Wit (a b c : Perm (Fin 8)) : Prop :=
  ∃ u : Fin 8 → ZMod 2, ∑ i, u i = 0 ∧ (∀ i, u (b i) = u i) ∧ (∀ i, u (c i) = u i) ∧
    (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 0 ∧
    (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 4

theorem one_add_one_z2 : (1 : ZMod 2) + 1 = 0 := by
  decide

theorem ite_add_ne {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then (1 : ZMod 2) else 0) + if Q then 1 else 0) ≠ 0 ↔ ¬ (P ↔ Q) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, one_add_one_z2]

theorem ite_add_eq_one {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ ¬ Q) :
    ((if P then (1 : ZMod 2) else 0) + if Q then 1 else 0) = 1 := by
  by_cases hQ : Q <;> simp [hQ, h]

@[expose] def epr (p r : Fin 8) : Fin 8 → ZMod 2 := fun i => if i = p ∨ i = r then 1 else 0

theorem sum_epr {p r : Fin 8} (h : p ≠ r) : ∑ i, epr p r i = 0 := by
  have e : (Finset.univ.filter fun i => i = p ∨ i = r) = {p, r} := by
    ext i
    simp
  simp only [epr]
  rw [Finset.sum_boole, e, Finset.card_pair h]
  rfl

theorem epr_fix {b : Perm (Fin 8)} {p r : Fin 8} (h2 : b p = p) (h4 : b r = r) (i : Fin 8) :
    epr p r (b i) = epr p r i := by
  have e1 : b i = p ↔ i = p := ⟨fun h => b.injective (h.trans h2.symm), fun h => h ▸ h2⟩
  have e2 : b i = r ↔ i = r := ⟨fun h => b.injective (h.trans h4.symm), fun h => h ▸ h4⟩
  simp only [epr, e1, e2]

theorem card_epr {a : Perm (Fin 8)} (ha : ∀ i, a (a i) = i) {p r : Fin 8} (h1 : a p ≠ p)
    (h3 : a r = r) :
    (Finset.univ.filter fun i => epr p r i + epr p r (a i) ≠ 0).card = 2 := by
  have hpr : p ≠ r := fun h => h1 (by rw [h, h3])
  have hap : a p ≠ r := fun h => hpr (by rw [← ha p, h, h3])
  have key : (Finset.univ.filter fun i => epr p r i + epr p r (a i) ≠ 0) = {p, a p} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [epr, epr, ite_add_ne]
    constructor
    · intro h
      by_contra hc
      rw [not_or] at hc
      have h5 : a i ≠ p := fun e => hc.2 (by rw [← e, ha])
      apply h
      by_cases hir : i = r
      · rw [hir]
        exact iff_of_true (Or.inr rfl) (Or.inr h3)
      · have h6 : a i ≠ r := fun e => hir (by rw [← ha i, e, h3])
        exact iff_of_false (fun e => e.elim hc.1 hir) fun e => e.elim h5 h6
    · rintro (rfl | rfl)
      · exact fun e => (e.1 (Or.inl rfl)).elim h1 hap
      · exact fun e => (e.2 (Or.inl (ha _))).elim h1 hap
  rw [key, Finset.card_pair (Ne.symm h1)]

@[expose] def m4 (b c : Perm (Fin 8)) (i : Fin 8) : Fin 8 := min (min i (b i)) (min (c i) (b (c i)))

theorem m4_mem (b c : Perm (Fin 8)) (i : Fin 8) :
    m4 b c i = i ∨ m4 b c i = b i ∨ m4 b c i = c i ∨ m4 b c i = b (c i) := by
  unfold m4
  rcases min_choice (min i (b i)) (min (c i) (b (c i))) with h | h <;> rw [h]
  · rcases min_choice i (b i) with h' | h' <;> rw [h'] <;> simp
  · rcases min_choice (c i) (b (c i)) with h' | h' <;> rw [h'] <;> simp

section W8

variable {a b c : Perm (Fin 8)} (ha : ∀ i, a (a i) = i) (hb : ∀ i, b (b i) = i)
  (hc : ∀ i, c (c i) = i) (hab : ∀ i, a (b i) = b (a i)) (hac : ∀ i, a (c i) = c (a i))
  (hbc : ∀ i, b (c i) = c (b i))

include hb hbc in
theorem m4_b (i : Fin 8) : m4 b c (b i) = m4 b c i := by
  simp only [m4, hb, ← hbc]
  rw [min_comm (b i) i, min_comm (b (c i)) (c i)]

include hc in
theorem m4_c (i : Fin 8) : m4 b c (c i) = m4 b c i := by
  simp only [m4, hc]
  exact min_comm _ _

include ha hb hc hab hac hbc in
theorem m4_ne (h1 : ∀ i, a i ≠ i) (h2 : ∀ i, b (a i) ≠ i) (h3 : ∀ i, c (a i) ≠ i)
    (h4 : ∀ i, c (b (a i)) ≠ i) (i : Fin 8) : m4 b c i ≠ m4 b c (a i) := by
  intro e
  have e1 := congrArg a e
  have e2 := congrArg (fun t => a (b t)) e
  have e3 := congrArg (fun t => a (c t)) e
  have e4 := congrArg (fun t => a (b (c t))) e
  rcases m4_mem b c i with h | h | h | h <;> rcases m4_mem b c (a i) with h' | h' | h' | h' <;>
    simp only [h, h', ha, hb, hc, hab, hac, hbc, h1, h2, h3, h4] at e1 e2 e3 e4

@[expose] def w8w (a b c : Perm (Fin 8)) (i : Fin 8) : ZMod 2 :=
  if m4 b c i < m4 b c (a i) then 1 else 0

theorem sum_half {q : Fin 8 → Prop} [DecidablePred q] {a : Perm (Fin 8)}
    (ha : ∀ i, a (a i) = i) (hq : ∀ i, q (a i) ↔ ¬ q i) :
    ∑ i, (if q i then (1 : ZMod 2) else 0) = 0 := by
  rw [Finset.sum_boole]
  have hbij : (Finset.univ.filter fun i => ¬ q i).card = (Finset.univ.filter q).card := by
    refine Finset.card_bij (fun i _ => a i) (fun i hi => ?_) (fun i _ j _ h => ?_) (fun j hj => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hq]
      exact hi
    · rw [← ha i, h, ha]
    · refine ⟨a j, ?_, ha j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [hq]
      exact not_not.2 hj
  have h8 := Finset.card_filter_add_card_filter_not (s := Finset.univ) q
  rw [hbij, Finset.card_univ, Fintype.card_fin] at h8
  have h4 : (Finset.univ.filter q).card = 4 := by omega
  rw [h4]
  rfl

include ha hb hc hab hac hbc in
theorem w8w_spec (h1 : ∀ i, a i ≠ i) (h2 : ∀ i, b (a i) ≠ i) (h3 : ∀ i, c (a i) ≠ i)
    (h4 : ∀ i, c (b (a i)) ≠ i) :
    ∑ i, w8w a b c i = 0 ∧ (∀ i, w8w a b c (b i) = w8w a b c i) ∧
      (∀ i, w8w a b c (c i) = w8w a b c i) ∧
      (Finset.univ.filter fun i => w8w a b c i + w8w a b c (a i) ≠ 0).card = 8 := by
  have hne := m4_ne ha hb hc hab hac hbc h1 h2 h3 h4
  have hsum : ∀ i, w8w a b c i + w8w a b c (a i) = 1 := by
    intro i
    simp only [w8w, ha]
    exact ite_add_eq_one ⟨fun h h' => lt_asymm h h', fun h =>
      lt_of_le_of_ne (not_lt.1 h) (hne i)⟩
  refine ⟨sum_half ha fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    constructor
    · intro h h'
      exact absurd (h.trans h') (lt_irrefl _)
    · intro h
      exact lt_of_le_of_ne (not_lt.1 h) (hne i).symm
  · simp only [w8w, hab, m4_b hb hbc]
  · simp only [w8w, hac, m4_c hc]
  · rw [show (Finset.univ.filter fun i => w8w a b c i + w8w a b c (a i) ≠ 0) = Finset.univ by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hsum i]
      exact one_ne_zero]
    rfl

end W8

theorem apply_apply_of {σ : Perm (Fin 8)} (h : σ * σ = 1) (i : Fin 8) : σ (σ i) = i := by
  rw [← Perm.mul_apply, h, Perm.one_apply]

theorem apply_comm_of {σ τ : Perm (Fin 8)} (h : σ * τ = τ * σ) (i : Fin 8) :
    σ (τ i) = τ (σ i) := by
  rw [← Perm.mul_apply, h, Perm.mul_apply]

theorem wit_of_W2b {a b c : Perm (Fin 8)} (ha : a * a = 1) (h : W2b (L a) (L b) (L c)) :
    Wit a b c := by
  obtain ⟨⟨p, hp, h1, h2, h3⟩, r, hr, h4, h5, h6⟩ := h
  let p' : Fin 8 := ⟨p, lt_of_mem_id8 p hp⟩
  let r' : Fin 8 := ⟨r, lt_of_mem_id8 r hr⟩
  have e1 : a p' ≠ p' := fun e => h1 ((fix_iff a p').2 e)
  have e4 : a r' = r' := (fix_iff a r').1 h4
  have hc2 := card_epr (apply_apply_of ha) e1 e4
  refine ⟨epr p' r', sum_epr fun e => e1 (e ▸ e4), epr_fix ((fix_iff b p').1 h2)
    ((fix_iff b r').1 h5), epr_fix ((fix_iff c p').1 h3) ((fix_iff c r').1 h6), ?_, ?_⟩ <;>
    rw [hc2] <;> decide

theorem wit_of_W8b {a b c : Perm (Fin 8)} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (h : W8b (L a) (L b) (L c)) : Wit a b c := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [cmp_L] at h2 h3
  rw [cmp_L, cmp_L] at h4
  have hab' := apply_comm_of hab
  have hac' := apply_comm_of hac
  have hbc' := apply_comm_of hbc
  have f2 : ∀ i, b (a i) ≠ i := fun i => by
    rw [← hab']
    exact fpf_L h2 i
  have f3 : ∀ i, c (a i) ≠ i := fun i => by
    rw [← hac']
    exact fpf_L h3 i
  have f4 : ∀ i, c (b (a i)) ≠ i := fun i => by
    rw [← hab', ← hac', ← hbc']
    exact fpf_L h4 i
  obtain ⟨s0, sb, sc, s8⟩ := w8w_spec (apply_apply_of ha) (apply_apply_of hb) (apply_apply_of hc)
    hab' hac' hbc' (fpf_L h1) f2 f3 f4
  exact ⟨w8w a b c, s0, sb, sc, by rw [s8]; decide, by rw [s8]; decide⟩

theorem fact_P8 (hK0 : K0) (hK : K34) (hA : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ)
    (hE : ∀ σ ∈ B, σ * σ = 1) (hP : B ≤ S126Ex.presSub) :
    Nat.card B ≤ 16 ∧ (8 ≤ Nat.card B → ∃ a ∈ B, ∃ b ∈ B, b ≠ 1 ∧ Wit a b b) ∧
      (Nat.card B = 16 → ∃ a ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ ∧
        Wit a b₁ b₂) := by
  have hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV := fun σ hσ h1 => mem_INV hK0 (hP hσ) (hE σ hσ) h1
  have hW : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, W2b (L a) (L b) (L c) ∨ W8b (L a) (L b) (L c) →
      Wit a b c := by
    intro a ha b hb c hc h
    rcases h with h | h
    · exact wit_of_W2b (hE a ha) h
    · exact wit_of_W8b (hE a ha) (hE b hb) (hE c hc) (hA a ha b hb) (hA a ha c hc)
        (hA b hb c hc) h
  have hne1 : ∀ σ : Perm (Fin 8), L σ ≠ id8 → σ ≠ 1 := fun σ h e => h (e ▸ L_one)
  have hT : 4 < Nat.card B → ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ k : ℕ,
      T34 ((prods3 x y z).map L) k (L x) (L y) (L z) ∧ iv k = L z ∧
      ∀ τ ∈ B, τ ∉ [1, x, y, x * y] → ∀ m < 43, iv m = L τ → k ≤ m := by
    intro h4
    obtain ⟨x, hx, y, hy, z, hz, i, j, k, hij, hjk, hk, hix, hjy, hkz, hzs, hzm⟩ := chain3 hI h4
    have h := hK i (List.mem_range.2 (by omega)) j (List.mem_range.2 (by omega)) hij
      (by rw [hix, hjy]; exact comm_L (hA x hx y hy)) k (List.mem_range.2 hk) hjk
      (by rw [hix, hkz]; exact comm_L (hA x hx z hz))
      (by rw [hjy, hkz]; exact comm_L (hA y hy z hz))
      (by rw [hix, hjy, hkz, cmp_L, ← L_one]; exact not_mem_map_L hzs)
    rw [hix, hjy, hkz, grp3_L] at h
    exact ⟨x, hx, y, hy, z, hz, k, h, hkz, hzm⟩
  have hT4 : 8 < Nat.card B → ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ w ∈ B,
      W4 ((prods4 x y z w).map L) (L x) (L y) (L z) (L w) := by
    intro h8
    obtain ⟨x, hx, y, hy, z, hz, k, h, hkz, hzm⟩ := hT (by omega)
    obtain ⟨w, hw, hws, l, hl, hlw, -⟩ :=
      exists_min hI (s := prods3 x y z) (by simp [prods3]) (by simp [prods3]; omega)
    have hkl : k < l := lt_of_min (s := [1, x, y, x * y]) (t := prods3 x y z)
      (fun τ h h' => h (by simp_all [prods3])) hkz hzm (by simp [prods3]) hw hws hl hlw
    have h4 := h.2 l (List.mem_range.2 hl) hkl
      (by rw [hlw]; exact comm_L (hA x hx w hw)) (by rw [hlw]; exact comm_L (hA y hy w hw))
      (by rw [hlw]; exact comm_L (hA z hz w hw)) (by rw [hlw]; exact not_mem_map_L hws)
    rw [hlw, grp4_L] at h4
    exact ⟨x, hx, y, hy, z, hz, w, hw, h4⟩
  refine ⟨?_, fun h8 => ?_, fun h16 => ?_⟩
  · by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, w, hw, h4⟩ := hT4 (by omega)
    obtain ⟨e, he, hes⟩ := exists_not_mem (B := B) (s := prods4 x y z w)
      (by simp [prods4, prods3]; omega)
    obtain ⟨n, hn, hne⟩ := exists_iv (hI e he fun h => hes (by simp [h, prods4, prods3]))
    have hm := h4.2 n (List.mem_range.2 hn) (by rw [hne]; exact comm_L (hA e he x hx))
      (by rw [hne]; exact comm_L (hA e he y hy)) (by rw [hne]; exact comm_L (hA e he z hz))
      (by rw [hne]; exact comm_L (hA e he w hw))
    rw [hne] at hm
    exact not_mem_map_L hes hm
  · obtain ⟨x, hx, y, hy, z, hz, k, h, -⟩ := hT (by omega)
    obtain ⟨b, hb, hb1, a, ha, hab⟩ := h.1
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    have hbB := prods3_mem hx hy hz b' hb'
    exact ⟨a', prods3_mem hx hy hz a' ha', b', hbB, hne1 b' hb1,
      hW a' (prods3_mem hx hy hz a' ha') b' hbB b' hbB hab⟩
  · obtain ⟨x, hx, y, hy, z, hz, w, hw, h4⟩ := hT4 (by omega)
    obtain ⟨b, hb, hb1, c, hc, hc1, hcb, a, ha, habc⟩ := h4.1
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
    have hbB := prods4_mem hx hy hz hw b' hb'
    have hcB := prods4_mem hx hy hz hw c' hc'
    have haB := prods4_mem hx hy hz hw a' ha'
    exact ⟨a', haB, b', hbB, c', hcB, hne1 b' hb1, hne1 c' hc1, fun e => hcb (e ▸ rfl),
      hW a' haB b' hbB c' hcB habc⟩

theorem wit_conj {a b c : Perm (Fin 8)} (g : Perm (Fin 8))
    (h : Wit (g⁻¹ * a * g) (g⁻¹ * b * g) (g⁻¹ * c * g)) : Wit a b c := by
  obtain ⟨u, h0, hb, hc, h1, h2⟩ := h
  have key : ∀ (d : Perm (Fin 8)) (i : Fin 8), (g⁻¹ * d * g) (g⁻¹ i) = g⁻¹ (d i) := by
    intro d i
    simp only [Perm.mul_apply, S126Ex.perm_apply_inv]
  have hcard : (Finset.univ.filter fun i => u (g⁻¹ i) + u (g⁻¹ (a i)) ≠ 0).card =
      (Finset.univ.filter fun i => u i + u ((g⁻¹ * a * g) i) ≠ 0).card := by
    refine Finset.card_equiv g⁻¹ fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, key]
  refine ⟨fun i => u (g⁻¹ i), ?_, fun i => ?_, fun i => ?_, ?_, ?_⟩
  · rw [Equiv.sum_comp g⁻¹ u]
    exact h0
  · show u (g⁻¹ (b i)) = u (g⁻¹ i)
    rw [← key, hb]
  · show u (g⁻¹ (c i)) = u (g⁻¹ i)
    rw [← key, hc]
  · rw [hcard]
    exact h1
  · rw [hcard]
    exact h2

theorem factS8ElemAbE8_holds : FactS8ElemAbE8 := by
  intro B hA hE
  obtain ⟨hK0, hK⟩ := checks
  have h2 : IsPGroup 2 B := fun σ =>
    ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hE σ σ.2)⟩
  obtain ⟨g, hg⟩ := S126Ex.exists_conj_le_P8 h2
  let B' := B.map (MulAut.conj g⁻¹).toMonoidHom
  have hmem : ∀ σ, σ ∈ B' ↔ ∃ q ∈ B, g⁻¹ * q * g = σ := by
    intro σ
    simp only [B', Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hP : B' ≤ S126Ex.presSub := by
    intro σ hσ
    obtain ⟨q, hq, rfl⟩ := (hmem σ).1 hσ
    exact S126Ex.P8_le_presSub (hg q hq)
  have hA' : ∀ σ ∈ B', ∀ τ ∈ B', σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨q, hq, rfl⟩ := (hmem σ).1 hσ
    obtain ⟨r, hr, rfl⟩ := (hmem τ).1 hτ
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc q, hA q hq r hr, mul_assoc]
  have hE' : ∀ σ ∈ B', σ * σ = 1 := by
    intro σ hσ
    obtain ⟨q, hq, rfl⟩ := (hmem σ).1 hσ
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc q, hE q hq, one_mul, inv_mul_cancel]
  obtain ⟨c1, c2, c3⟩ := fact_P8 hK0 hK hA' hE' hP
  have hconj1 : ∀ q : Perm (Fin 8), g⁻¹ * q * g ≠ 1 → q ≠ 1 := fun q h e =>
    h (by rw [e, mul_one, inv_mul_cancel])
  refine ⟨by omega, fun h8 => ?_, fun h16 => ?_⟩
  · obtain ⟨a, ha, b, hb, hb1, hw⟩ := c2 (by omega)
    obtain ⟨a₀, ha₀, rfl⟩ := (hmem a).1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := (hmem b).1 hb
    obtain ⟨u, h0, hu, -, h1, h2⟩ := wit_conj g hw
    exact ⟨a₀, ha₀, b₀, hb₀, hconj1 b₀ hb1, u, h0, hu, h1, h2⟩
  · obtain ⟨a, ha, b, hb, c, hc, hb1, hc1, hbc, hw⟩ := c3 (by omega)
    obtain ⟨a₀, ha₀, rfl⟩ := (hmem a).1 ha
    obtain ⟨b₀, hb₀, rfl⟩ := (hmem b).1 hb
    obtain ⟨c₀, hc₀, rfl⟩ := (hmem c).1 hc
    exact ⟨a₀, ha₀, b₀, hb₀, c₀, hc₀, hconj1 b₀ hb1, hconj1 c₀ hc1,
      fun e => hbc (by rw [e]), wit_conj g hw⟩

end S126L22F

end CFSG.Quasithin.H13
