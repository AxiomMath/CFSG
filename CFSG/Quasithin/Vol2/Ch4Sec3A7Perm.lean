module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.H13.Ch4.A7

open Equiv Equiv.Perm

@[expose] def fixSet (s : Finset (Fin 7)) : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | ∀ x ∈ s, (g : Perm (Fin 7)) x = x}
  one_mem' := fun x _ => rfl
  mul_mem' := fun {g h} hg hh x hx => by
    show (g : Perm (Fin 7)) ((h : Perm (Fin 7)) x) = x
    rw [hh x hx, hg x hx]
  inv_mem' := fun {g} hg x hx => by
    show (g : Perm (Fin 7))⁻¹ x = x
    rw [Perm.inv_eq_iff_eq, hg x hx]

theorem mem_fixSet {s : Finset (Fin 7)} {g : alternatingGroup (Fin 7)} :
    g ∈ fixSet s ↔ ∀ x ∈ s, (g : Perm (Fin 7)) x = x := Iff.rfl

theorem card_fixSet (s : Finset (Fin 7)) (hs : s.card ≤ 5) :
    Nat.card (fixSet s) = (7 - s.card).factorial / 2 := by
  classical
  let p : Fin 7 → Prop := fun x => x ∉ s
  have hcardp : Fintype.card {x // p x} = 7 - s.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have : Nontrivial {x // p x} := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hcardp]
    omega
  let f : alternatingGroup {x // p x} →* alternatingGroup (Fin 7) :=
    { toFun := fun g => ⟨ofSubtype (g : Perm {x // p x}), by
        rw [mem_alternatingGroup, sign_ofSubtype]
        exact g.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun g h => Subtype.ext (map_mul ofSubtype (g : Perm {x // p x}) h) }
  have hinj : Function.Injective f := fun g h hgh =>
    Subtype.ext (ofSubtype_injective (congrArg Subtype.val hgh))
  have hrange : f.range = fixSet s := by
    ext g
    constructor
    · rintro ⟨g', rfl⟩ x hx
      exact ofSubtype_apply_of_not_mem _ (by simpa [p] using hx)
    · intro hg
      have h1 : ∀ x, p ((g : Perm (Fin 7)) x) ↔ p x := by
        intro x
        simp only [p]
        constructor
        · intro hgx hx
          exact hgx (by rw [hg x hx]; exact hx)
        · intro hx hgx
          apply hx
          have h3 : (g : Perm (Fin 7)) ((g : Perm (Fin 7)) x) = (g : Perm (Fin 7)) x := hg _ hgx
          rw [(g : Perm (Fin 7)).injective h3] at hgx
          exact hgx
      have h2 : ∀ x, (g : Perm (Fin 7)) x ≠ x → p x := fun x hx hxs => hx (hg x hxs)
      refine ⟨⟨(g : Perm (Fin 7)).subtypePerm h1, ?_⟩, ?_⟩
      · rw [mem_alternatingGroup, sign_subtypePerm _ h1 h2]
        exact g.2
      · apply Subtype.ext
        exact ofSubtype_subtypePerm h1 h2
  have hc := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hrange] at hc
  rw [← hc, nat_card_alternatingGroup, Nat.card_eq_fintype_card, hcardp]

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem eq_top_of_fixSet_le {a b p q : Fin 7} (h : [a, b, p, q].Nodup)
    (J : Subgroup (alternatingGroup (Fin 7))) (h1 : fixSet {a, b} ≤ J) (h2 : fixSet {p, q} ≤ J) :
    J = ⊤ := by
  classical
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at h
  obtain ⟨⟨hab, hap, haq⟩, ⟨hbp, hbq⟩, hpq⟩ := h
  set A := fixSet {a, b} with hA
  set B := fixSet {p, q} with hB
  have hcA : Nat.card A = 60 := by
    rw [hA, card_fixSet _ (by rw [Finset.card_pair hab]; norm_num), Finset.card_pair hab]
    decide
  have hcB : Nat.card B = 60 := by
    rw [hB, card_fixSet _ (by rw [Finset.card_pair hpq]; norm_num), Finset.card_pair hpq]
    decide
  have hAB : A ⊓ B = fixSet {a, b, p, q} := by
    ext g
    simp only [Subgroup.mem_inf, hA, hB, mem_fixSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h1 _ (Or.inl rfl)
      · exact h1 _ (Or.inr rfl)
      · exact h2 _ (Or.inl rfl)
      · exact h2 _ (Or.inr rfl)
    · intro h
      exact ⟨fun x hx => h x (by rcases hx with rfl | rfl <;> simp),
        fun x hx => h x (by rcases hx with rfl | rfl <;> simp)⟩
  have hc4 : ({a, b, p, q} : Finset (Fin 7)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hap, haq]),
      Finset.card_insert_of_notMem (by simp [hbp, hbq]), Finset.card_pair hpq]
  have hcAB : Nat.card ↥(A ⊓ B) = 3 := by
    rw [hAB, card_fixSet _ (by rw [hc4]; norm_num), hc4]
    decide
  have hrel : A.relIndex B = 20 := by
    have e := Subgroup.relIndex_mul_card A B
    rw [hcAB, hcB] at e
    omega
  have hne : A.relIndex (A ⊔ B) ≠ 0 := by
    intro h0
    have e := Subgroup.relIndex_mul_card A (A ⊔ B)
    rw [h0, zero_mul] at e
    exact (Nat.card_pos (α := ↥(A ⊔ B))).ne' e.symm
  have hle := Subgroup.relIndex_le_of_le_right (le_sup_right : B ≤ A ⊔ B) hne
  have hsup : 1200 ≤ Nat.card ↥(A ⊔ B) := by
    have e := Subgroup.relIndex_mul_card A (A ⊔ B)
    rw [inf_eq_left.mpr le_sup_left, hcA] at e
    rw [← e]
    omega
  have hJ : 1200 ≤ Nat.card J := hsup.trans (Subgroup.card_le_of_le (_root_.sup_le h1 h2))
  have hidx := J.index_mul_card
  rw [card_alt7] at hidx
  have hidx2 : J.index ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 3 * 1200 ≤ J.index * Nat.card J := Nat.mul_le_mul hc hJ
    omega
  have hpos : 0 < J.index := by
    rcases Nat.eq_zero_or_pos J.index with h0 | h0
    · rw [h0, zero_mul] at hidx
      omega
    · exact h0
  rcases (by omega : J.index = 1 ∨ J.index = 2) with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hN := Subgroup.normal_of_index_eq_two h2
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases hsimple.eq_bot_or_eq_top_of_normal J with hb | ht
    · rw [hb, Subgroup.card_bot] at hJ
      omega
    · rw [ht, Subgroup.index_top] at h2
      omega

theorem exists_alt_map_pair {a b p q : Fin 7} (hab : a ≠ b) (hpq : p ≠ q) :
    ∃ g : alternatingGroup (Fin 7), (g : Perm (Fin 7)) a = p ∧ (g : Perm (Fin 7)) b = q := by
  classical
  set b' := swap a p b with hb'
  set π₀ : Perm (Fin 7) := swap b' q * swap a p with hπ₀
  have hpb' : p ≠ b' := by
    rw [hb']
    by_cases hbp : b = p
    · rw [hbp, swap_apply_right]
      intro h
      exact hab (h.symm.trans hbp.symm)
    · rw [swap_apply_of_ne_of_ne (Ne.symm ?_) hbp]
      · exact Ne.symm hbp
      · exact hab
  have h1 : π₀ a = p := by
    rw [hπ₀, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hpb' hpq]
  have h2 : π₀ b = q := by
    rw [hπ₀, Perm.mul_apply, ← hb', swap_apply_left]
  rcases Int.units_eq_one_or (sign π₀) with hs | hs
  · exact ⟨⟨π₀, hs⟩, h1, h2⟩
  ·
    have hc : 1 < (Finset.univ \ {p, q} : Finset (Fin 7)).card := by
      rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ,
        Finset.card_pair hpq]
      norm_num
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hc hd
    refine ⟨⟨swap c d * π₀, ?_⟩, ?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hcd, hs]
      rfl
    · show (swap c d) (π₀ a) = p
      rw [h1, swap_apply_of_ne_of_ne (Ne.symm hc.1) (Ne.symm hd.1)]
    · show (swap c d) (π₀ b) = q
      rw [h2, swap_apply_of_ne_of_ne (Ne.symm hc.2) (Ne.symm hd.2)]

theorem fix_or_swap_of_commute {a b : Fin 7} (hab : a ≠ b) {g : Perm (Fin 7)}
    (h : g * swap a b = swap a b * g) :
    (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
  have e := congrArg (fun π : Perm (Fin 7) => π a) h
  simp only [Perm.mul_apply, swap_apply_left] at e
  by_cases h1 : g a = a
  · left
    rw [h1, swap_apply_left] at e
    exact ⟨h1, e⟩
  · by_cases h2 : g a = b
    · right
      rw [h2, swap_apply_right] at e
      exact ⟨h2, e⟩
    · exfalso
      rw [swap_apply_of_ne_of_ne h1 h2] at e
      exact hab (g.injective e).symm

theorem apply_eq_of_perfect {Λ : Type} [Group Λ] (f : Λ →* Perm (Fin 7)) {a b : Fin 7}
    (hab : a ≠ b) (hperf : commutator Λ = ⊤)
    (hf : ∀ x, f x * swap a b = swap a b * f x) (x : Λ) : f x a = a ∧ f x b = b := by
  classical
  let χ : Λ →* ℤˣ :=
    { toFun := fun y => if f y a = a then 1 else -1
      map_one' := by simp
      map_mul' := fun y z => by
        rcases fix_or_swap_of_commute hab (hf y) with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
          rcases fix_or_swap_of_commute hab (hf z) with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩ <;>
          simp [Perm.mul_apply, hy1, hy2, hz1, hab.symm] }
  have hk := Abelianization.commutator_subset_ker χ
  rw [hperf] at hk
  have hx : χ x = 1 := hk (Subgroup.mem_top x)
  have hxa : f x a = a := by
    by_contra hne
    have : χ x = -1 := by simp [χ, hne]
    rw [hx] at this
    exact absurd this (by decide)
  rcases fix_or_swap_of_commute hab (hf x) with h | h
  · exact h
  · exact absurd (h.1.symm.trans hxa) hab.symm

theorem threeCycle_mem_fixSet {a b x y z : Fin 7} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hza : z ≠ a) (hzb : z ≠ b) :
    ∃ c : alternatingGroup (Fin 7), c ∈ fixSet {a, b} ∧
      (c : Perm (Fin 7)) = swap x y * swap x z := by
  refine ⟨⟨swap x y * swap x z, ?_⟩, ?_, rfl⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hxy, sign_swap hxz]
    rfl
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    show (swap x y * swap x z) w = w
    rcases hw with rfl | rfl
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxa.symm hza.symm,
        swap_apply_of_ne_of_ne hxa.symm hya.symm]
    · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxb.symm hzb.symm,
        swap_apply_of_ne_of_ne hxb.symm hyb.symm]

theorem apply_mem_of_commute {g : Perm (Fin 7)} {x y z : Fin 7} (hxz : x ≠ z) (hyz : y ≠ z)
    (h : g * (swap x y * swap x z) = swap x y * swap x z * g) :
    g x = x ∨ g x = y ∨ g x = z := by
  have e := congrArg (fun π : Perm (Fin 7) => π x) h
  simp only [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hxz.symm hyz.symm] at e
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  rw [swap_apply_of_ne_of_ne h1 h3, swap_apply_of_ne_of_ne h1 h2] at e
  exact hxz (g.injective e).symm

theorem exists_two_ne_of_three (a b x : Fin 7) :
    ∃ y z : Fin 7, y ≠ z ∧ y ≠ a ∧ y ≠ b ∧ y ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ x := by
  classical
  have hc : 1 < (Finset.univ \ {a, b, x} : Finset (Fin 7)).card := by
    have h3 : ({a, b, x} : Finset (Fin 7)).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hy hz
  exact ⟨y, z, hyz, hy.1, hy.2.1, hy.2.2, hz.1, hz.2.1, hz.2.2⟩

theorem exists_two_ne_of_four (a b x w : Fin 7) :
    ∃ y z : Fin 7, y ≠ z ∧ y ≠ a ∧ y ≠ b ∧ y ≠ x ∧ y ≠ w ∧ z ≠ a ∧ z ≠ b ∧ z ≠ x ∧ z ≠ w := by
  classical
  have hc : 1 < (Finset.univ \ {a, b, x, w} : Finset (Fin 7)).card := by
    have h4 : ({a, b, x, w} : Finset (Fin 7)).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_sdiff, Finset.card_univ, Fintype.card_fin, Finset.inter_univ]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hc
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hy hz
  exact ⟨y, z, hyz, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩

theorem eq_one_of_commute_fixSet {a b : Fin 7} (hab : a ≠ b) (g : alternatingGroup (Fin 7))
    (hg : ∀ c ∈ fixSet {a, b}, g * c = c * g) : g = 1 := by
  classical
  have key : ∀ x y z : Fin 7, x ≠ y → x ≠ z → y ≠ z → x ≠ a → x ≠ b → y ≠ a → y ≠ b →
      z ≠ a → z ≠ b → (g : Perm (Fin 7)) x = x ∨ (g : Perm (Fin 7)) x = y ∨
        (g : Perm (Fin 7)) x = z := by
    intro x y z hxy hxz hyz hxa hxb hya hyb hza hzb
    obtain ⟨c, hc, hcc⟩ := threeCycle_mem_fixSet hxy hxz hxa hxb hya hyb hza hzb
    have h1 := congrArg Subtype.val (hg c hc)
    simp only [Subgroup.coe_mul, hcc] at h1
    exact apply_mem_of_commute hxz hyz h1
  have hfix : ∀ x, x ≠ a → x ≠ b → (g : Perm (Fin 7)) x = x := by
    intro x hxa hxb
    obtain ⟨y, z, hyz, hya, hyb, hyx, hza, hzb, hzx⟩ := exists_two_ne_of_three a b x
    by_contra hne
    have hw : (g : Perm (Fin 7)) x ≠ a ∧ (g : Perm (Fin 7)) x ≠ b ∧
        (g : Perm (Fin 7)) x ≠ x := by
      rcases key x y z (Ne.symm hyx) (Ne.symm hzx) hyz hxa hxb hya hyb hza hzb with
        h | h | h
      · exact absurd h hne
      · exact ⟨h ▸ hya, h ▸ hyb, hne⟩
      · exact ⟨h ▸ hza, h ▸ hzb, hne⟩
    obtain ⟨y', z', hyz', hya', hyb', hyx', hyw', hza', hzb', hzx', hzw'⟩ :=
      exists_two_ne_of_four a b x ((g : Perm (Fin 7)) x)
    rcases key x y' z' (Ne.symm hyx') (Ne.symm hzx') hyz' hxa hxb hya' hyb' hza' hzb' with
      h | h | h
    · exact hne h
    · exact hyw' h.symm
    · exact hzw' h.symm
  have hab' : ∀ w, (w = a ∨ w = b) → (g : Perm (Fin 7)) w = a ∨ (g : Perm (Fin 7)) w = b := by
    intro w hw
    by_contra hne
    push Not at hne
    have h1 := hfix _ hne.1 hne.2
    have h2 := (g : Perm (Fin 7)).injective h1
    rcases hw with hw | hw
    · exact hne.1 (h2.trans hw)
    · exact hne.2 (h2.trans hw)
  rcases hab' a (Or.inl rfl) with ha | ha
  · rcases hab' b (Or.inr rfl) with hb | hb
    · exact absurd ((g : Perm (Fin 7)).injective (ha.trans hb.symm)) hab
    · apply Subtype.ext
      ext w
      by_cases hwa : w = a
      · rw [hwa, ha]; rfl
      · by_cases hwb : w = b
        · rw [hwb, hb]; rfl
        · rw [hfix w hwa hwb]; rfl
  · rcases hab' b (Or.inr rfl) with hb | hb
    · exfalso
      have hsw : (g : Perm (Fin 7)) = swap a b := by
        ext w
        by_cases hwa : w = a
        · rw [hwa, ha, swap_apply_left]
        · by_cases hwb : w = b
          · rw [hwb, hb, swap_apply_right]
          · rw [hfix w hwa hwb, swap_apply_of_ne_of_ne hwa hwb]
      have hs := g.2
      rw [mem_alternatingGroup, hsw, sign_swap hab] at hs
      exact absurd hs (by decide)
    · exact absurd ((g : Perm (Fin 7)).injective (ha.trans hb.symm)) hab

theorem card_mulAut_alt5 : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have hc := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)
  rw [← Nat.card_congr (Equiv.ofBijective _ hc), Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  decide

theorem card_eq_eight_of_isPGroup (P : Subgroup (alternatingGroup (Fin 7)))
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) : Nat.card P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have h := P.card_mul_index
  rw [hk, card_alt7] at h
  have hk3 : k ≤ 3 := by
    by_contra hk3
    push Not at hk3
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hk3
    have : 2 ^ 4 ∣ 2520 := h16.trans ⟨_, h.symm⟩
    exact absurd this (by decide)
  rw [hk]
  interval_cases k
  · exact absurd (Dvd.intro 1260 (by omega : 2 * 1260 = P.index)) hodd
  · exact absurd (Dvd.intro 630 (by omega : 2 * 630 = P.index)) hodd
  · exact absurd (Dvd.intro 315 (by omega : 2 * 315 = P.index)) hodd
  · rfl

open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def pairVec (a b : Fin 7) : evenWeight 7 :=
  ⟨Pi.single a 1 + Pi.single b 1, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Pi.add_apply,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true]
    decide⟩

theorem coe_pairVec (a b : Fin 7) :
    ((pairVec a b : evenWeight 7) : Fin 7 → ZMod 2) = Pi.single a 1 + Pi.single b 1 := rfl

theorem constWeight_seven : constWeight 7 = ⊥ := by
  ext x
  constructor
  · intro hx
    have hsum : ∑ i, (x : Fin 7 → ZMod 2) i = 0 := by
      have := x.2
      simpa [evenWeight] using this
    have hc : ∀ i, (x : Fin 7 → ZMod 2) i = (x : Fin 7 → ZMod 2) 0 := fun i => hx i 0
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
    rw [h7, one_mul] at hsum
    rw [AddSubgroup.mem_bot]
    apply Subtype.ext
    funext i
    rw [hc i, hsum]
    rfl
  · intro hx
    rw [AddSubgroup.mem_bot] at hx
    rw [hx]
    exact (constWeight 7).zero_mem

theorem mk_injective_seven :
    Function.Injective (QuotientAddGroup.mk : evenWeight 7 → AltHeart 7) := by
  intro x y h
  have h1 := QuotientAddGroup.eq.mp h
  rw [constWeight_seven, AddSubgroup.mem_bot, neg_add_eq_zero] at h1
  exact h1

theorem permWeight_pairVec (π : Perm (Fin 7)) (a b : Fin 7) :
    permWeight 7 π (pairVec a b) = pairVec (π a) (π b) := by
  apply Subtype.ext
  funext i
  simp only [permWeight, coe_pairVec, Pi.add_apply, Pi.single_apply, Perm.inv_eq_iff_eq]

theorem pairVec_sub_pairVec (a p q : Fin 7) : pairVec a p - pairVec a q = pairVec p q := by
  apply Subtype.ext
  funext i
  simp only [AddSubgroup.coe_sub, coe_pairVec, Pi.sub_apply, Pi.add_apply]
  have key : ∀ x y z : ZMod 2, x + y - (x + z) = y + z := by decide
  exact key _ _ _

theorem pairVec_ne_zero {a b : Fin 7} (hab : a ≠ b) : pairVec a b ≠ 0 := by
  intro h
  have := congrFun (congrArg Subtype.val h) a
  simp [coe_pairVec, hab] at this

end CFSG.Quasithin.H13.Ch4.A7
