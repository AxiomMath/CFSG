module

public import CFSG.Quasithin.Vol2.Ch12Sec6L22F
public import Certificates.Certificate7218

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

open S8E S8F

theorem checks : K0 ∧ C2w ∧ C3w ∧ C4w :=
  Certificates.certificate7218

@[expose] def uv (u : List Nat) : Fin 8 → ZMod 2 := fun i => (ap u i.val : ZMod 2)

theorem sum_uv {u : List Nat} (hu : Vec u) : ∑ i, uv u i = 0 := by
  rw [Fin.sum_univ_eight]
  simp only [uv]
  have h := hu.2
  have e : ((ap u 0 + ap u 1 + ap u 2 + ap u 3 + ap u 4 + ap u 5 + ap u 6 + ap u 7 : ℕ) :
      ZMod 2) = 0 := by
    rw [← ZMod.natCast_mod, h]
    rfl
  push_cast at e
  exact e

@[expose] noncomputable def cls (u : List Nat) (hu : Vec u) : D8 :=
  QuotientGroup.mk (⟨Multiplicative.ofAdd (uv u), mem_coreMod.2 (sum_uv hu)⟩ : ↥(coreMod 8))

theorem forall_id8 {P : ℕ → Prop} : (∀ i ∈ id8, P i) ↔ ∀ i : Fin 8, P i.val :=
  ⟨fun h i => h i.val (mem_id8 i), fun h i hi => h ⟨i, lt_of_mem_id8 i hi⟩⟩

theorem fixL_L_iff (σ : Perm (Fin 8)) (u : List Nat) :
    FixL (L σ) u ↔ (∀ i : Fin 8, ap u (σ i).val = ap u i.val) ∨
      ∀ i : Fin 8, ap u (σ i).val ≠ ap u i.val := by
  unfold FixL
  rw [forall_id8, forall_id8]
  simp only [ap_L]

theorem zmod_two_cast : ∀ a : ℕ, a < 2 → ∀ b : ℕ, b < 2 →
    (((a : ZMod 2) = b ↔ a = b) ∧ ((a : ZMod 2) = b + 1 ↔ a ≠ b)) := by
  decide

theorem fixL_iff {σ : Perm (Fin 8)} (hσ : σ * σ = 1) {u : List Nat} (hu : Vec u) :
    FixL (L σ) u ↔ dAct σ (cls u hu) = cls u hu := by
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  have hlt : ∀ i : Fin 8, ap u i.val < 2 := fun i => hu.1 i.val (mem_id8 i)
  have key : ∀ i : Fin 8,
      Multiplicative.toAdd (permAct 8 σ (Multiplicative.ofAdd (uv u))) i = uv u (σ i) := by
    intro i
    rw [permAct_apply, hinv]
    rfl
  rw [fixL_L_iff, cls, dAct_mk, mk_eq_iff, coreAct_coe]
  constructor
  · rintro (h | h)
    · left
      apply Multiplicative.toAdd.injective
      funext i
      rw [key]
      exact ((zmod_two_cast _ (hlt _) _ (hlt _)).1).2 (h i)
    · right
      apply Multiplicative.toAdd.injective
      funext i
      rw [toAdd_mul, Pi.add_apply, key]
      exact ((zmod_two_cast _ (hlt _) _ (hlt _)).2).2 (h i)
  · rintro (h | h)
    · left
      intro i
      have h1 := congrFun (congrArg Multiplicative.toAdd h) i
      rw [key] at h1
      exact ((zmod_two_cast _ (hlt _) _ (hlt _)).1).1 h1
    · right
      intro i
      have h1 := congrFun (congrArg Multiplicative.toAdd h) i
      rw [toAdd_mul, Pi.add_apply, key] at h1
      exact ((zmod_two_cast _ (hlt _) _ (hlt _)).2).1 h1

theorem mem_fixD_closure {S : Set (Perm (Fin 8))} {y : D8} (h : ∀ s ∈ S, dAct s y = y) :
    y ∈ fixD (Subgroup.closure S) := by
  intro σ hσ
  induction hσ using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => exact dAct_one y
  | mul a b _ _ ha hb => rw [dAct_mul, hb, ha]
  | inv a _ ha =>
    conv_lhs => rw [← ha]
    exact dAct_inv_dAct a y

theorem fixD_anti {P Q : Subgroup (Perm (Fin 8))} (h : P ≤ Q) : fixD Q ≤ fixD P :=
  fun _ hy σ hσ => hy σ (h hσ)

theorem relIndex_mul_card_of_le {P Q : Subgroup (Perm (Fin 8))} (h : P ≤ Q) :
    P.relIndex Q * Nat.card P = Nat.card Q := by
  have := Subgroup.relIndex_mul_card (H := P) (K := Q)
  rwa [inf_of_le_left h] at this

section Small

variable {b c : Perm (Fin 8)} (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b)

include hb hc hbc in
theorem pair_mul_mem {x y : Perm (Fin 8)} (hx : x ∈ ({1, b, c, b * c} : Set (Perm (Fin 8))))
    (hy : y ∈ ({1, b, c, b * c} : Set (Perm (Fin 8)))) :
    x * y ∈ ({1, b, c, b * c} : Set (Perm (Fin 8))) := by
  have hb' : ∀ z, b * (b * z) = z := fun z => by rw [← mul_assoc, hb, one_mul]
  have hcb : ∀ z, c * (b * z) = b * (c * z) := fun z => by rw [← mul_assoc, ← hbc, mul_assoc]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp [mul_assoc, hb, hc, hb', hcb, hbc.symm]

@[expose] def pairSub : Subgroup (Perm (Fin 8)) where
  carrier := {1, b, c, b * c}
  one_mem' := Or.inl rfl
  mul_mem' := fun hx hy => pair_mul_mem hb hc hbc hx hy
  inv_mem' := fun {x} hx => by
    have hx' := pair_mul_mem hb hc hbc (x := 1) (y := 1) (Or.inl rfl) (Or.inl rfl)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · right; left; exact inv_eq_of_mul_eq_one_right hb
    · right; right; left; exact inv_eq_of_mul_eq_one_right hc
    · right; right; right
      apply inv_eq_of_mul_eq_one_right
      rw [mul_assoc, ← mul_assoc c b c, ← hbc, mul_assoc, hc, mul_one, hb]

theorem mem_pairSub {x : Perm (Fin 8)} :
    x ∈ pairSub hb hc hbc ↔ x = 1 ∨ x = b ∨ x = c ∨ x = b * c := Iff.rfl

theorem closure_pair_eq : Subgroup.closure ({b, c} : Set (Perm (Fin 8))) = pairSub hb hc hbc := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun x hx => ?_
  · rintro x (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · have hb1 : b ∈ Subgroup.closure ({b, c} : Set (Perm (Fin 8))) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hc1 : c ∈ Subgroup.closure ({b, c} : Set (Perm (Fin 8))) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    rcases (mem_pairSub hb hc hbc).1 hx with rfl | rfl | rfl | rfl
    exacts [Subgroup.one_mem _, hb1, hc1, Subgroup.mul_mem _ hb1 hc1]

include hb hc hbc in
theorem card_pairSub (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hne : b ≠ c) :
    Nat.card (pairSub hb hc hbc) = 4 := by
  have hbc1 : b * c ≠ 1 := fun h => hne (by
    calc b = b⁻¹ := (inv_eq_of_mul_eq_one_right hb).symm
      _ = c := inv_eq_of_mul_eq_one_right h)
  have hbcb : b * c ≠ b := fun h => hc1 (by
    calc c = b * (b * c) := by rw [← mul_assoc, hb, one_mul]
      _ = b * b := by rw [h]
      _ = 1 := hb)
  have hbcc : b * c ≠ c := fun h => hb1 (by
    calc b = b * c * c := by rw [mul_assoc, hc, mul_one]
      _ = c * c := by rw [h]
      _ = 1 := hc)
  change Nat.card ↥({1, b, c, b * c} : Set (Perm (Fin 8))) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair (Ne.symm hbcc)]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, Ne.symm hbcb⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hb1, Ne.symm hc1, Ne.symm hbc1⟩

end Small

theorem card_zpowers_two {b : Perm (Fin 8)} (hb : b * b = 1) (hb1 : b ≠ 1) :
    Nat.card (Subgroup.zpowers b) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq]; exact hb) hb1

theorem mem_zpowers_two {b x : Perm (Fin 8)} (hb : b * b = 1) (hx : x ∈ Subgroup.zpowers b) :
    x = 1 ∨ x = b := by
  have h := pairSub hb hb (Eq.refl _)
  have hle : Subgroup.zpowers b ≤ pairSub hb hb rfl := by
    rw [Subgroup.zpowers_le]
    exact Or.inr (Or.inl rfl)
  rcases (mem_pairSub hb hb rfl).1 (hle hx) with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · exact Or.inr h1
  · exact Or.inl (h1.trans hb)

end S126L28

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

open S8E S8F

variable {B : Subgroup (Perm (Fin 8))}

theorem fix_cls {σ : Perm (Fin 8)} (hσ : σ * σ = 1) {u : List Nat} (hu : Vec u)
    (h : FixL (L σ) u) : dAct σ (cls u hu) = cls u hu :=
  (fixL_iff hσ hu).1 h

theorem not_mem_fixD (hE : ∀ σ ∈ B, σ * σ = 1) {ps : List (Perm (Fin 8))}
    (hps : ∀ p ∈ ps, p ∈ B) {u : List Nat} (hu : Vec u) (h : ∃ a ∈ ps.map L, ¬ FixL a u) :
    cls u hu ∉ fixD B := by
  obtain ⟨a, ha, hna⟩ := h
  obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
  intro hfix
  exact hna ((fixL_iff (hE a' (hps a' ha')) hu).2 (hfix a' (hps a' ha')))

theorem of_mem_map {ps : List (Perm (Fin 8))} (hps : ∀ p ∈ ps, p ∈ B) {b : List Nat}
    (hb : b ∈ ps.map L) : ∃ b' ∈ B, L b' = b := by
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  exact ⟨b', hps b' hb', rfl⟩

@[expose] def prods2 (x y : Perm (Fin 8)) : List (Perm (Fin 8)) := [1, x, y, x * y]

theorem grp2_L (x y : Perm (Fin 8)) : grp2 (L x) (L y) = (prods2 x y).map L := by
  simp only [grp2, prods2, List.map_cons, List.map_nil, cmp_L, L_one]

theorem prods2_mem {x y : Perm (Fin 8)} (hx : x ∈ B) (hy : y ∈ B) :
    ∀ f ∈ prods2 x y, f ∈ B := by
  simp only [prods2, List.mem_cons, List.not_mem_nil, or_false]
  rintro f (rfl | rfl | rfl | rfl)
  exacts [B.one_mem, hx, hy, B.mul_mem hx hy]

theorem fixD_zpowers_ne (hE : ∀ σ ∈ B, σ * σ = 1) {ps : List (Perm (Fin 8))}
    (hps : ∀ p ∈ ps, p ∈ B) {b : Perm (Fin 8)} (hbB : b ∈ B) {u : List Nat}
    (h : SepW [L b] (ps.map L) u) : fixD (Subgroup.zpowers b) ≠ fixD B := by
  obtain ⟨hu, hfix, hsep⟩ := h
  have h1 : cls u hu ∈ fixD (Subgroup.zpowers b) := by
    rw [Subgroup.zpowers_eq_closure]
    refine mem_fixD_closure fun s hs => ?_
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact fix_cls (hE s hbB) hu (hfix _ (List.mem_singleton_self _))
  intro e
  rw [e] at h1
  exact not_mem_fixD hE hps hu hsep h1

theorem fixD_pair_ne (hE : ∀ σ ∈ B, σ * σ = 1) {ps : List (Perm (Fin 8))}
    (hps : ∀ p ∈ ps, p ∈ B) {b c : Perm (Fin 8)} (hbB : b ∈ B) (hcB : c ∈ B) {u : List Nat}
    (h : SepW [L b, L c] (ps.map L) u) :
    cls u (h.1) ∈ fixD (Subgroup.closure ({b, c} : Set (Perm (Fin 8)))) ∧
      cls u (h.1) ∉ fixD B := by
  obtain ⟨hu, hfix, hsep⟩ := h
  refine ⟨mem_fixD_closure fun s hs => ?_, not_mem_fixD hE hps hu hsep⟩
  rcases hs with rfl | rfl
  · exact fix_cls (hE s hbB) hu (hfix _ (by simp))
  · exact fix_cls (hE s hcB) hu (hfix _ (by simp))

theorem chain2 (hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV) (hB : 2 < Nat.card B) :
    ∃ x ∈ B, ∃ y ∈ B, ∃ i j : ℕ, i < j ∧ j < 43 ∧ iv i = L x ∧ iv j = L y := by
  obtain ⟨x, hx, -, i, -, hix, hxm⟩ := exists_min hI (s := [1]) (by simp) (by simp; omega)
  obtain ⟨y, hy, hys, j, hj, hjy, -⟩ :=
    exists_min hI (s := [1, x]) (by simp) (by simp; omega)
  have hij : i < j := lt_of_min (s := [1]) (t := [1, x]) (fun τ h h' => h (by simp_all))
    hix hxm (by simp) hy hys hj hjy
  exact ⟨x, hx, y, hy, i, j, hij, hj, hix, hjy⟩

end S126L28

end CFSG.Quasithin.H13

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126FE S126L22F Equiv

namespace S126L28

open S8E S8F

variable {B : Subgroup (Perm (Fin 8))}

theorem chain4 (hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV) (hB : 8 < Nat.card B) :
    ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ w ∈ B, ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧ l < 43 ∧
      iv i = L x ∧ iv j = L y ∧ iv k = L z ∧ iv l = L w ∧ z ∉ [1, x, y, x * y] ∧
      w ∉ prods3 x y z := by
  obtain ⟨x, hx, y, hy, z, hz, i, j, k, hij, hjk, hk, hix, hjy, hkz, hzs, hzm⟩ :=
    chain3 hI (by omega)
  obtain ⟨w, hw, hws, l, hl, hlw, -⟩ :=
    exists_min hI (s := prods3 x y z) (by simp [prods3]) (by simp [prods3]; omega)
  have hkl : k < l := lt_of_min (s := [1, x, y, x * y]) (t := prods3 x y z)
    (fun τ h h' => h (by simp_all [prods3])) hkz hzm (by simp [prods3]) hw hws hl hlw
  exact ⟨x, hx, y, hy, z, hz, w, hw, i, j, k, l, hij, hjk, hkl, hl, hix, hjy, hkz, hlw, hzs, hws⟩

theorem fixD_bot : fixD (⊥ : Subgroup (Perm (Fin 8))) = ⊤ := by
  ext y
  simp only [Subgroup.mem_top, iff_true]
  intro σ hσ
  rw [Subgroup.mem_bot.1 hσ, dAct_one]

theorem fixD_ne_top (hne : B ≠ ⊥) : fixD B ≠ ⊤ := by
  obtain ⟨b, hb, hb1⟩ := (Subgroup.bot_or_exists_ne_one B).resolve_left hne
  intro h
  apply hb1
  apply eq_one_of_dAct
  intro y
  have : y ∈ fixD B := h ▸ Subgroup.mem_top y
  exact this b hb

theorem relIndex_le_of_card {P : Subgroup (Perm (Fin 8))} (hPB : P ≤ B) {n k : ℕ}
    (hB : Nat.card B = n * k) (hP : k ≤ Nat.card P) (hk : 0 < k) : P.relIndex B ≤ n := by
  have h := relIndex_mul_card_of_le hPB
  by_contra hc
  push Not at hc
  have h1 : (n + 1) * k ≤ P.relIndex B * Nat.card P :=
    Nat.mul_le_mul hc hP
  rw [h, hB] at h1
  nlinarith

theorem relIndex_eq_of_card {P : Subgroup (Perm (Fin 8))} (hPB : P ≤ B) {n k : ℕ}
    (hB : Nat.card B = n * k) (hP : Nat.card P = k) (hk : 0 < k) : P.relIndex B = n := by
  have h := relIndex_mul_card_of_le hPB
  rw [hP, hB] at h
  exact Nat.eq_of_mul_eq_mul_right hk h

theorem pairSub_le {b c : Perm (Fin 8)} (hb : b * b = 1) (hc : c * c = 1) (hbc : b * c = c * b)
    (hbB : b ∈ B) (hcB : c ∈ B) : pairSub hb hc hbc ≤ B := by
  intro x hx
  rcases (mem_pairSub hb hc hbc).1 hx with rfl | rfl | rfl | rfl
  exacts [B.one_mem, hbB, hcB, B.mul_mem hbB hcB]

theorem L_ne_iff {σ τ : Perm (Fin 8)} : L σ ≠ L τ ↔ σ ≠ τ :=
  ⟨fun h e => h (e ▸ rfl), fun h e => h (L_inj e)⟩

theorem L_ne_id8 {σ : Perm (Fin 8)} : L σ ≠ id8 ↔ σ ≠ 1 := by
  rw [← L_one, L_ne_iff]

theorem e_conds3 (hE : ∀ σ ∈ B, σ * σ = 1) {ps : List (Perm (Fin 8))} (hps : ∀ p ∈ ps, p ∈ B)
    {e : Perm (Fin 8)} (heB : e ∈ B) (he1 : e ≠ 1) {u : List Nat}
    (hs : SepW [L e] (ps.map L) u) :
    (⊥ : Subgroup (Perm (Fin 8))) ≤ Subgroup.zpowers e ∧ Subgroup.zpowers e ≤ B ∧
      (⊥ : Subgroup (Perm (Fin 8))).relIndex (Subgroup.zpowers e) = 2 ∧
      fixD B < fixD (Subgroup.zpowers e) := by
  refine ⟨bot_le, (Subgroup.zpowers_le).2 heB, ?_, lt_of_le_of_ne
    (fixD_anti ((Subgroup.zpowers_le).2 heB)) (fixD_zpowers_ne hE hps heB hs).symm⟩
  rw [Subgroup.relIndex_bot_left, card_zpowers_two (hE e heB) he1]

theorem e_conds4 (hA : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ) (hE : ∀ σ ∈ B, σ * σ = 1)
    {ps : List (Perm (Fin 8))} (hps : ∀ p ∈ ps, p ∈ B) {d e : Perm (Fin 8)} (hdB : d ∈ B)
    (heB : e ∈ B) (hd1 : d ≠ 1) (he1 : e ≠ 1) (hde : d ≠ e) {u : List Nat}
    (hs : SepW [L d, L e] (ps.map L) u) :
    Subgroup.zpowers d ≤ pairSub (hE d hdB) (hE e heB) (hA d hdB e heB) ∧
      pairSub (hE d hdB) (hE e heB) (hA d hdB e heB) ≤ B ∧
      (Subgroup.zpowers d).relIndex (pairSub (hE d hdB) (hE e heB) (hA d hdB e heB)) = 2 ∧
      fixD B < fixD (pairSub (hE d hdB) (hE e heB) (hA d hdB e heB)) := by
  have hle : Subgroup.zpowers d ≤ pairSub (hE d hdB) (hE e heB) (hA d hdB e heB) :=
    (Subgroup.zpowers_le).2 (Or.inr (Or.inl rfl))
  have hEB := pairSub_le (hE d hdB) (hE e heB) (hA d hdB e heB) hdB heB
  obtain ⟨hin, hout⟩ := fixD_pair_ne hE hps hdB heB hs
  rw [closure_pair_eq (hE d hdB) (hE e heB) (hA d hdB e heB)] at hin
  refine ⟨hle, hEB, ?_, lt_of_le_of_ne (fixD_anti hEB) fun h => hout (h ▸ hin)⟩
  have h1 := relIndex_mul_card_of_le hle
  rw [card_zpowers_two (hE d hdB) hd1, card_pairSub _ _ _ hd1 he1 hde] at h1
  omega

theorem card_closure_three_ge {b c d : Perm (Fin 8)} (hb : b * b = 1) (hc : c * c = 1)
    (hbc : b * c = c * b) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hne : b ≠ c)
    (hd : d ∉ pairSub hb hc hbc) :
    8 ≤ Nat.card (Subgroup.closure ({b, c, d} : Set (Perm (Fin 8)))) := by
  have hle : pairSub hb hc hbc ≤ Subgroup.closure ({b, c, d} : Set (Perm (Fin 8))) := by
    rw [← closure_pair_eq hb hc hbc]
    exact Subgroup.closure_mono (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl))
  have hdK : d ∈ Subgroup.closure ({b, c, d} : Set (Perm (Fin 8))) :=
    Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have h1 := relIndex_mul_card_of_le hle
  rw [card_pairSub hb hc hbc hb1 hc1 hne] at h1
  have h2 : (pairSub hb hc hbc).relIndex (Subgroup.closure ({b, c, d} : Set (Perm (Fin 8)))) ≠ 1 :=
    fun h => hd ((Subgroup.relIndex_eq_one.1 h) hdK)
  have h3 : 0 < Nat.card (Subgroup.closure ({b, c, d} : Set (Perm (Fin 8)))) := Nat.card_pos
  have h4 : (pairSub hb hc hbc).relIndex (Subgroup.closure ({b, c, d} : Set (Perm (Fin 8)))) ≠ 0 :=
    fun h => by rw [h, zero_mul] at h1; omega
  omega

theorem p8_facts (hA : ∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ)
    (hE : ∀ σ ∈ B, σ * σ = 1) (hP : B ≤ S126Ex.presSub) (hne : B ≠ ⊥) :
    (∃ B' ≤ B, B'.relIndex B ≤ 4 ∧ fixD B' ≠ fixD B) ∧
    ((∀ B' ≤ B, B'.relIndex B ≤ 2 → fixD B' = fixD B) →
      8 ≤ Nat.card B ∧ ∃ D ≤ B, D.relIndex B = 8 ∧ ∃ E₁ E₂ E₃ : Subgroup (Perm (Fin 8)),
        E₁ ≠ E₂ ∧ E₁ ≠ E₃ ∧ E₂ ≠ E₃ ∧ ∀ E ∈ [E₁, E₂, E₃],
          D ≤ E ∧ E ≤ B ∧ D.relIndex E = 2 ∧ fixD B < fixD E) := by
  obtain ⟨hK0, hC2, hC3, hC4⟩ := checks
  have hI : ∀ σ ∈ B, σ ≠ 1 → L σ ∈ INV := fun σ hσ h1 => mem_INV hK0 (hP hσ) (hE σ hσ) h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 B := fun σ => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hE σ σ.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h2
  have hBtop := fixD_ne_top hne
  have hbot_ne : fixD (⊥ : Subgroup (Perm (Fin 8))) ≠ fixD B := by
    rw [fixD_bot]
    exact hBtop.symm
  have hcard1 : 1 < Nat.card B := by
    rcases Nat.lt_or_ge 1 (Nat.card B) with h | h
    · exact h
    · exfalso
      apply hne
      exact Subgroup.eq_bot_of_card_le B h
  have h4data : 8 < Nat.card B → ∃ x ∈ B, ∃ y ∈ B, ∃ z ∈ B, ∃ w ∈ B,
      R4w ((prods4 x y z w).map L) ∧ Max4 ((prods4 x y z w).map L) (L x) (L y) (L z) (L w) := by
    intro h8
    obtain ⟨x, hx, y, hy, z, hz, w, hw, i, j, k, l, hij, hjk, hkl, hl, hix, hjy, hkz, hlw, hzs,
      hws⟩ := chain4 hI h8
    have h := hC4 i (List.mem_range.2 (by omega)) j (List.mem_range.2 (by omega)) hij
      (by rw [hix, hjy]; exact comm_L (hA x hx y hy)) k (List.mem_range.2 (by omega)) hjk
      (by rw [hix, hkz]; exact comm_L (hA x hx z hz))
      (by rw [hjy, hkz]; exact comm_L (hA y hy z hz))
      (by rw [hix, hjy, hkz, cmp_L, ← L_one]; exact not_mem_map_L hzs) l
      (List.mem_range.2 hl) hkl (by rw [hix, hlw]; exact comm_L (hA x hx w hw))
      (by rw [hjy, hlw]; exact comm_L (hA y hy w hw))
      (by rw [hkz, hlw]; exact comm_L (hA z hz w hw))
      (by rw [hix, hjy, hkz, hlw, grp3_L]; exact not_mem_map_L hws)
    rw [hix, hjy, hkz, hlw, grp3_L, grp4_L] at h
    exact ⟨x, hx, y, hy, z, hz, w, hw, h⟩
  have hle16 : Nat.card B ≤ 16 := by
    by_contra hcon
    obtain ⟨x, hx, y, hy, z, hz, w, hw, -, hmax⟩ := h4data (by omega)
    obtain ⟨e, he, hes⟩ := exists_not_mem (B := B) (s := prods4 x y z w)
      (by simp [prods4, prods3]; omega)
    obtain ⟨n, hn, hne'⟩ := exists_iv (hI e he fun h => hes (by simp [h, prods4, prods3]))
    have hmem := hmax n (List.mem_range.2 hn) (by rw [hne']; exact comm_L (hA e he x hx))
      (by rw [hne']; exact comm_L (hA e he y hy)) (by rw [hne']; exact comm_L (hA e he z hz))
      (by rw [hne']; exact comm_L (hA e he w hw))
    rw [hne'] at hmem
    exact not_mem_map_L hes hmem
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at hm
      omega
    · exact h
  have hm4 : m ≤ 4 := by
    by_contra hc
    push Not at hc
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hc
    omega
  interval_cases m
  ·
    refine ⟨⟨⊥, bot_le, ?_, hbot_ne⟩, fun h2 => absurd (h2 ⊥ bot_le ?_) hbot_ne⟩
    · rw [Subgroup.relIndex_bot_left, hm]
      norm_num
    · rw [Subgroup.relIndex_bot_left, hm]
      norm_num
  ·
    refine ⟨⟨⊥, bot_le, ?_, hbot_ne⟩, fun h2 => ?_⟩
    · rw [Subgroup.relIndex_bot_left, hm]
      norm_num
    exfalso
    obtain ⟨x, hx, y, hy, i, j, hij, hj, hix, hjy⟩ := chain2 hI (by rw [hm]; norm_num)
    have h := hC2 i (List.mem_range.2 (by omega)) j (List.mem_range.2 hj) hij
      (by rw [hix, hjy]; exact comm_L (hA x hx y hy))
    rw [hix, hjy, grp2_L] at h
    have hps := prods2_mem hx hy
    obtain ⟨⟨bl, u⟩, hb, hb1, hsep⟩ := h
    obtain ⟨b, hbB, rfl⟩ := of_mem_map hps hb
    have hne1 := fixD_zpowers_ne hE hps hbB hsep
    refine hne1 (h2 _ ((Subgroup.zpowers_le).2 hbB) ?_)
    exact relIndex_le_of_card ((Subgroup.zpowers_le).2 hbB) (n := 2) (k := 2)
      (by rw [hm]; norm_num) (by rw [card_zpowers_two (hE b hbB) (L_ne_id8.1 hb1)])
      (by norm_num)
  ·
    obtain ⟨x, hx, y, hy, z, hz, i, j, k, hij, hjk, hk, hix, hjy, hkz, hzs, -⟩ :=
      chain3 hI (by rw [hm]; norm_num)
    have h := hC3 i (List.mem_range.2 (by omega)) j (List.mem_range.2 (by omega)) hij
      (by rw [hix, hjy]; exact comm_L (hA x hx y hy)) k (List.mem_range.2 hk) hjk
      (by rw [hix, hkz]; exact comm_L (hA x hx z hz))
      (by rw [hjy, hkz]; exact comm_L (hA y hy z hz))
      (by rw [hix, hjy, hkz, cmp_L, ← L_one]; exact not_mem_map_L hzs)
    rw [hix, hjy, hkz, grp3_L] at h
    have hps := prods3_mem hx hy hz
    obtain ⟨⟨⟨bl, u⟩, hb, hb1, hsep⟩, h3⟩ := h
    obtain ⟨b, hbB, rfl⟩ := of_mem_map hps hb
    refine ⟨⟨_, (Subgroup.zpowers_le).2 hbB, ?_, fixD_zpowers_ne hE hps hbB hsep⟩, fun h2 => ?_⟩
    · exact relIndex_le_of_card ((Subgroup.zpowers_le).2 hbB) (n := 4) (k := 2)
        (by rw [hm]; norm_num) (by rw [card_zpowers_two (hE b hbB) (L_ne_id8.1 hb1)])
        (by norm_num)
    rcases h3 with ⟨⟨bl, cl, u⟩, hb, hc, hb1, hc1, hbc, hsep⟩ |
      ⟨⟨⟨e1l, u1⟩, ⟨e2l, u2⟩, ⟨e3l, u3⟩⟩, h12, h13, h23, ⟨he1, h01, hs1⟩, ⟨he2, h02, hs2⟩,
        ⟨he3, h03, hs3⟩⟩
    · exfalso
      obtain ⟨b, hbB, rfl⟩ := of_mem_map hps hb
      obtain ⟨c, hcB, rfl⟩ := of_mem_map hps hc
      obtain ⟨hin, hout⟩ := fixD_pair_ne hE hps hbB hcB hsep
      have hcomm := hA b hbB c hcB
      rw [closure_pair_eq (hE b hbB) (hE c hcB) hcomm] at hin
      have hle := pairSub_le (hE b hbB) (hE c hcB) hcomm hbB hcB
      have he := h2 _ hle (relIndex_le_of_card hle (n := 2) (k := 4) (by rw [hm]; norm_num)
        (by rw [card_pairSub _ _ _ (L_ne_id8.1 hb1) (L_ne_id8.1 hc1) (L_ne_iff.1 hbc)])
        (by norm_num))
      rw [he] at hin
      exact hout hin
    · obtain ⟨e₁, he₁B, rfl⟩ := of_mem_map hps he1
      obtain ⟨e₂, he₂B, rfl⟩ := of_mem_map hps he2
      obtain ⟨e₃, he₃B, rfl⟩ := of_mem_map hps he3
      have hne : ∀ e e' : Perm (Fin 8), e ∈ B → e' ≠ 1 → e ≠ e' →
          Subgroup.zpowers e ≠ Subgroup.zpowers e' := by
        intro e e' heB he'1 hee' heq
        have hmem : e' ∈ Subgroup.zpowers e := heq ▸ Subgroup.mem_zpowers e'
        rcases mem_zpowers_two (hE e heB) hmem with h | h
        · exact he'1 h
        · exact hee' h.symm
      have e1 : e₁ ≠ 1 := L_ne_id8.1 h01
      have e2 : e₂ ≠ 1 := L_ne_id8.1 h02
      have e3 : e₃ ≠ 1 := L_ne_id8.1 h03
      refine ⟨by rw [hm]; norm_num, ⊥, bot_le, by rw [Subgroup.relIndex_bot_left, hm]; norm_num,
        _, _, _, hne _ _ he₁B e2 (L_ne_iff.1 h12), hne _ _ he₁B e3 (L_ne_iff.1 h13),
        hne _ _ he₂B e3 (L_ne_iff.1 h23), ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro E (rfl | rfl | rfl)
      · exact e_conds3 hE hps he₁B e1 hs1
      · exact e_conds3 hE hps he₂B e2 hs2
      · exact e_conds3 hE hps he₃B e3 hs3
  ·
    obtain ⟨x, hx, y, hy, z, hz, w, hw, hR, -⟩ := h4data (by rw [hm]; norm_num)
    have hps := prods4_mem hx hy hz hw
    obtain ⟨⟨⟨bl, cl, u⟩, hb, hc, hb1, hc1, hbc, hsep⟩, h3⟩ := hR
    obtain ⟨b, hbB, rfl⟩ := of_mem_map hps hb
    obtain ⟨c, hcB, rfl⟩ := of_mem_map hps hc
    obtain ⟨hin, hout⟩ := fixD_pair_ne hE hps hbB hcB hsep
    have hcomm := hA b hbB c hcB
    rw [closure_pair_eq (hE b hbB) (hE c hcB) hcomm] at hin
    have hle := pairSub_le (hE b hbB) (hE c hcB) hcomm hbB hcB
    refine ⟨⟨_, hle, relIndex_le_of_card hle (n := 4) (k := 4) (by rw [hm]; norm_num)
      (by rw [card_pairSub _ _ _ (L_ne_id8.1 hb1) (L_ne_id8.1 hc1) (L_ne_iff.1 hbc)])
      (by norm_num), fun h => hout (h ▸ hin)⟩, fun h2 => ?_⟩
    rcases h3 with ⟨⟨bl, cl, dl, u⟩, hb, hc, hd, hb1, hc1, hbc, hdn, hsep⟩ |
      ⟨⟨dl, ⟨e1l, u1⟩, ⟨e2l, u2⟩, ⟨e3l, u3⟩⟩, hd, hd1, he1, he2, he3, hn1, hn2, hn3, hn3',
        hs1, hs2, hs3⟩
    · exfalso
      obtain ⟨b, hbB, rfl⟩ := of_mem_map hps hb
      obtain ⟨c, hcB, rfl⟩ := of_mem_map hps hc
      obtain ⟨d, hdB, rfl⟩ := of_mem_map hps hd
      obtain ⟨hu, hfix, hsep'⟩ := hsep
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdn
      obtain ⟨hd0, hdb, hdc, hdbc⟩ := hdn
      have hcomm := hA b hbB c hcB
      have hb1' : b ≠ 1 := L_ne_id8.1 hb1
      have hc1' : c ≠ 1 := L_ne_id8.1 hc1
      have hdP : d ∉ pairSub (hE b hbB) (hE c hcB) hcomm := by
        intro hd'
        rcases (mem_pairSub _ _ _).1 hd' with rfl | rfl | rfl | rfl
        · exact hd0 L_one
        · exact hdb rfl
        · exact hdc rfl
        · exact hdbc (cmp_L _ _).symm
      have h8 := card_closure_three_ge (hE b hbB) (hE c hcB) hcomm hb1' hc1' (L_ne_iff.1 hbc)
        hdP
      have hK : Subgroup.closure ({b, c, d} : Set (Perm (Fin 8))) ≤ B := by
        rw [Subgroup.closure_le]
        rintro s (rfl | rfl | rfl)
        exacts [hbB, hcB, hdB]
      have hin : cls u hu ∈ fixD (Subgroup.closure ({b, c, d} : Set (Perm (Fin 8)))) := by
        refine mem_fixD_closure fun s hs => ?_
        rcases hs with rfl | rfl | rfl
        · exact fix_cls (hE s hbB) hu (hfix _ (by simp))
        · exact fix_cls (hE s hcB) hu (hfix _ (by simp))
        · exact fix_cls (hE s hdB) hu (hfix _ (by simp))
      have he := h2 _ hK (relIndex_le_of_card hK (n := 2) (k := 8) (by rw [hm]; norm_num) h8
        (by norm_num))
      rw [he] at hin
      exact not_mem_fixD hE hps hu hsep' hin
    · obtain ⟨d, hdB, rfl⟩ := of_mem_map hps hd
      obtain ⟨e₁, he₁B, rfl⟩ := of_mem_map hps he1
      obtain ⟨e₂, he₂B, rfl⟩ := of_mem_map hps he2
      obtain ⟨e₃, he₃B, rfl⟩ := of_mem_map hps he3
      have hd1' : d ≠ 1 := L_ne_id8.1 hd1
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn1 hn2 hn3 hn3'
      obtain ⟨h01, hd1e⟩ := hn1
      obtain ⟨h02, hd2, h21, h2d1⟩ := hn2
      obtain ⟨h03, hd3, h31, h3d1⟩ := hn3
      obtain ⟨-, -, h32, h3d2⟩ := hn3'
      have e1 : e₁ ≠ 1 := L_ne_id8.1 h01
      have e2 : e₂ ≠ 1 := L_ne_id8.1 h02
      have e3 : e₃ ≠ 1 := L_ne_id8.1 h03
      have hne : ∀ (e e' : Perm (Fin 8)) (heB : e ∈ B) (he'B : e' ∈ B),
          ¬ L e' = id8 → ¬ L e' = L d → ¬ L e' = L e → ¬ L e' = S8E.cmp (L d) (L e) →
          pairSub (hE d hdB) (hE e heB) (hA d hdB e heB) ≠
            pairSub (hE d hdB) (hE e' he'B) (hA d hdB e' he'B) := by
        intro e e' heB he'B h1 h2 h3 h4 heq
        have hmem : e' ∈ pairSub (hE d hdB) (hE e heB) (hA d hdB e heB) :=
          heq ▸ (Or.inr (Or.inr (Or.inl rfl)))
        rcases (mem_pairSub _ _ _).1 hmem with h | h | h | h
        · exact h1 (by rw [h, L_one])
        · exact h2 (by rw [h])
        · exact h3 (by rw [h])
        · exact h4 (by rw [h, cmp_L])
      refine ⟨by rw [hm]; norm_num, Subgroup.zpowers d, (Subgroup.zpowers_le).2 hdB, ?_,
        _, _, _, hne _ _ he₁B he₂B h02 hd2 h21 h2d1, hne _ _ he₁B he₃B h03 hd3 h31 h3d1,
        hne _ _ he₂B he₃B h03 hd3 h32 h3d2, ?_⟩
      · exact relIndex_eq_of_card ((Subgroup.zpowers_le).2 hdB) (n := 8) (k := 2)
          (by rw [hm]; norm_num) (card_zpowers_two (hE d hdB) hd1') (by norm_num)
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro E (rfl | rfl | rfl)
      · exact e_conds4 hA hE hps hdB he₁B hd1' e1 (fun h => hd1e (by rw [h])) hs1
      · exact e_conds4 hA hE hps hdB he₂B hd1' e2 (fun h => hd2 (by rw [h])) hs2
      · exact e_conds4 hA hE hps hdB he₃B hd1' e3 (fun h => hd3 (by rw [h])) hs3

end S126L28

end CFSG.Quasithin.H13
