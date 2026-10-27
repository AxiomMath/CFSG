module

public import CFSG.Quasithin.EmptyFaithful.T1515Concl
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def pairVec (i j : Fin 7) : Fin 7 → ZMod 2 := Pi.single i 1 + Pi.single j 1

theorem pairVec_eq_iff : ∀ a b c d : Fin 7, a ≠ b → c ≠ d →
    (pairVec a b = pairVec c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  unfold pairVec
  decide

theorem swap_eq_swap_iff : ∀ a b c d : Fin 7, a ≠ b → c ≠ d →
    (Equiv.swap a b = Equiv.swap c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  decide

theorem pairVec_mem_evenWeight : ∀ i j : Fin 7, i ≠ j → pairVec i j ∈ evenWeight 7 := by
  unfold pairVec evenWeight
  decide

@[expose] def pairVecΔ (i j : Fin 7) (h : i ≠ j) : ↥(evenWeight 7) :=
  ⟨pairVec i j, pairVec_mem_evenWeight i j h⟩

theorem hasWeightTwo_pairVec : ∀ i j : Fin 7, i ≠ j → HasWeightTwo (pairVec i j) := by
  unfold HasWeightTwo pairVec
  decide

theorem permWeight_pairVec (g : Equiv.Perm (Fin 7)) (i j : Fin 7) (h : i ≠ j) :
    ((permWeight 7 g (pairVecΔ i j h) : ↥(evenWeight 7)) : Fin 7 → ZMod 2) =
      pairVec (g i) (g j) := by
  funext k
  simp only [permWeight, pairVecΔ, pairVec, Pi.add_apply, Pi.single_apply]
  simp only [Equiv.Perm.inv_eq_iff_eq]

theorem permWeight_pairVec_iff (g : Equiv.Perm (Fin 7)) (i j : Fin 7) (h : i ≠ j) :
    permWeight 7 g (pairVecΔ i j h) = pairVecΔ i j h ↔ g * Equiv.swap i j = Equiv.swap i j * g := by
  have hgij : g i ≠ g j := fun e => h (g.injective e)
  have h1 : permWeight 7 g (pairVecΔ i j h) = pairVecΔ i j h ↔
      pairVec (g i) (g j) = pairVec i j := by
    constructor
    · intro e
      rw [← permWeight_pairVec g i j h]
      exact congrArg Subtype.val e
    · intro e
      apply Subtype.ext
      rw [permWeight_pairVec g i j h]
      exact e
  have h2 : g * Equiv.swap i j = Equiv.swap i j * g ↔ Equiv.swap (g i) (g j) = Equiv.swap i j := by
    rw [Equiv.swap_apply_apply, mul_inv_eq_iff_eq_mul]
  rw [h1, h2, pairVec_eq_iff _ _ _ _ hgij h, swap_eq_swap_iff _ _ _ _ hgij h]

@[expose] def threeCycle (a b c : Fin 7) : Equiv.Perm (Fin 7) := Equiv.swap a b * Equiv.swap b c

theorem threeCycle_a {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) : threeCycle a b c a = b := by
  simp [threeCycle, Equiv.swap_apply_of_ne_of_ne hab hac]

theorem threeCycle_b {a b c : Fin 7} (hbc : b ≠ c) (hac : a ≠ c) : threeCycle a b c b = c := by
  simp [threeCycle, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]

theorem threeCycle_c (a b c : Fin 7) : threeCycle a b c c = a := by
  simp [threeCycle]

theorem threeCycle_other {a b c y : Fin 7} (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ c) :
    threeCycle a b c y = y := by
  simp [threeCycle, Equiv.swap_apply_of_ne_of_ne hyb hyc, Equiv.swap_apply_of_ne_of_ne hya hyb]

theorem image_mem_of_stabilizes {P : Finset (Finset (Fin 7))} {g : Equiv.Perm (Fin 7)}
    (h : StabilizesPartition g P) {B : Finset (Fin 7)} (hB : B ∈ P) : B.image g ∈ P := by
  have : B.image g ∈ P.image (Finset.image g) := Finset.mem_image_of_mem _ hB
  rwa [show P.image (Finset.image g) = P from h] at this

theorem card_le_two_of_type {P : Finset (Finset (Fin 7))} (hP : IsPartitionOfType P {2, 2, 2, 1})
    {B : Finset (Fin 7)} (hB : B ∈ P) : B.card ≤ 2 := by
  have h : B.card ∈ P.val.map Finset.card := Multiset.mem_map_of_mem _ hB
  rw [hP.2.2.2] at h
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
  omega

theorem eq_singleton_of_threeCycle_stab {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) {a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (hσ : StabilizesPartition (threeCycle a b c) P) {B : Finset (Fin 7)}
    (hB : B ∈ P) (ha : a ∈ B) : B = {a} := by
  have hσB : B.image (threeCycle a b c) ∈ P := image_mem_of_stabilizes hσ hB
  have hne : B.image (threeCycle a b c) ≠ B := by
    intro h
    have hb : b ∈ B := by
      have : threeCycle a b c a ∈ B.image (threeCycle a b c) := Finset.mem_image_of_mem _ ha
      rw [h, threeCycle_a hab hac] at this
      exact this
    have hc : c ∈ B := by
      have : threeCycle a b c b ∈ B.image (threeCycle a b c) := Finset.mem_image_of_mem _ hb
      rw [h, threeCycle_b hbc hac] at this
      exact this
    have hsub : ({a, b, c} : Finset (Fin 7)) ⊆ B := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have h3 : ({a, b, c} : Finset (Fin 7)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    have h1 := Finset.card_le_card hsub
    have h2 := card_le_two_of_type hP hB
    omega
  have hdisj : Disjoint (B.image (threeCycle a b c)) B := hP.2.1 _ hσB B hB hne
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨ha, fun y hy => ?_⟩
  by_contra hya
  by_cases hyb : y = b
  · subst hyb
    have : threeCycle a y c a ∈ B.image (threeCycle a y c) := Finset.mem_image_of_mem _ ha
    rw [threeCycle_a hab hac] at this
    exact Finset.disjoint_left.1 hdisj this hy
  · by_cases hyc : y = c
    · subst hyc
      have : threeCycle a b y y ∈ B.image (threeCycle a b y) := Finset.mem_image_of_mem _ hy
      rw [threeCycle_c] at this
      exact Finset.disjoint_left.1 hdisj this ha
    · have : threeCycle a b c y ∈ B.image (threeCycle a b c) := Finset.mem_image_of_mem _ hy
      rw [threeCycle_other hya hyb hyc] at this
      exact Finset.disjoint_left.1 hdisj this hy

theorem false_of_threeCycles_stab {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {2, 2, 2, 1}) {X : Finset (Fin 7)} (hX : 3 ≤ X.card)
    (h : ∀ a b c : Fin 7, a ∈ X → b ∈ X → c ∈ X → a ≠ b → b ≠ c → a ≠ c →
      StabilizesPartition (threeCycle a b c) P) : False := by
  have hsing : ∀ a ∈ X, ({a} : Finset (Fin 7)) ∈ P := by
    intro a ha
    obtain ⟨B, hBP, haB⟩ : ∃ B ∈ P, a ∈ B := by
      have : a ∈ P.biUnion id := by
        rw [hP.2.2.1]
        exact Finset.mem_univ a
      simpa using this
    have hXa : 1 < (X.erase a).card := by
      have := Finset.card_erase_of_mem ha
      omega
    obtain ⟨b, hb, c, hc, hbc⟩ := Finset.one_lt_card.1 hXa
    rw [Finset.mem_erase] at hb hc
    have := eq_singleton_of_threeCycle_stab hP (Ne.symm hb.1) hbc (Ne.symm hc.1)
      (h a b c ha hb.2 hc.2 (Ne.symm hb.1) hbc (Ne.symm hc.1)) hBP haB
    rwa [← this]
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < X.card)
  have hS1 : 2 < (P.filter (fun B => B.card = 1)).card := by
    rw [Finset.two_lt_card]
    refine ⟨{a}, ?_, {b}, ?_, {c}, ?_, ?_, ?_, ?_⟩
    · simpa using hsing a ha
    · simpa using hsing b hb
    · simpa using hsing c hc
    · simpa using hab
    · simpa using hac
    · simpa using hbc
  have hS1' : (P.filter (fun B => B.card = 1)).card = 1 := by
    have h1 : (P.filter (fun B => B.card = 1)).card =
        Multiset.countP (fun n => n = 1) (P.val.map Finset.card) := by
      rw [Multiset.countP_map]
      rfl
    rw [h1, hP.2.2.2]
    decide
  omega

theorem mem_stabilizer_iff_stabilizes (σ : Equiv.Perm (Fin 7)) (P : Finset (Finset (Fin 7))) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P ↔ StabilizesPartition σ P := by
  rw [MulAction.mem_stabilizer_iff]
  unfold StabilizesPartition
  have h : σ • P = P.image (Finset.image σ) := by
    ext B
    simp [Finset.smul_finset_def, Equiv.Perm.smul_def]
  rw [h]

theorem threeCycle_mem_alternating {a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c) :
    threeCycle a b c ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup, threeCycle, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hbc]
  decide

theorem threeCycle_mem {a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {B : Finset (Fin 7)} (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) {x : Fin 7} (hx : x ∈ B) :
    threeCycle a b c x ∈ B := by
  by_cases hxa : x = a
  · rw [hxa, threeCycle_a hab hac]
    exact hb
  · by_cases hxb : x = b
    · rw [hxb, threeCycle_b hbc hac]
      exact hc
    · by_cases hxc : x = c
      · rw [hxc, threeCycle_c]
        exact ha
      · rw [threeCycle_other hxa hxb hxc]
        exact hx

theorem stabilizes_of_threeCycle {P : Finset (Finset (Fin 7))}
    (hdisj : ∀ B ∈ P, ∀ B' ∈ P, B ≠ B' → Disjoint B B') {B : Finset (Fin 7)} (hB : B ∈ P)
    {a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (ha : a ∈ B) (hb : b ∈ B)
    (hc : c ∈ B) : StabilizesPartition (threeCycle a b c) P := by
  have hblock : ∀ B' ∈ P, B'.image (threeCycle a b c) = B' := by
    intro B' hB'
    by_cases hBB : B' = B
    · subst hBB
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        exact threeCycle_mem hab hbc hac ha hb hc hx
      · rw [Finset.card_image_of_injective _ (threeCycle a b c).injective]
    · have hd := hdisj B' hB' B hB hBB
      have hna : ∀ y ∈ B', y ≠ a := fun y hy h => Finset.disjoint_left.1 hd hy (h ▸ ha)
      have hnb : ∀ y ∈ B', y ≠ b := fun y hy h => Finset.disjoint_left.1 hd hy (h ▸ hb)
      have hnc : ∀ y ∈ B', y ≠ c := fun y hy h => Finset.disjoint_left.1 hd hy (h ▸ hc)
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        rw [threeCycle_other (hna x hx) (hnb x hx) (hnc x hx)]
        exact hx
      · intro hy
        exact Finset.mem_image.2 ⟨y, hy, threeCycle_other (hna y hy) (hnb y hy) (hnc y hy)⟩
  unfold StabilizesPartition
  calc P.image (Finset.image (threeCycle a b c)) = P.image id := by
        apply Finset.image_congr
        intro B' hB'
        exact hblock B' hB'
    _ = P := Finset.image_id

theorem mem_of_commute_threeCycle {a b c : Fin 7} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    {r : Equiv.Perm (Fin 7)} (hr : r * threeCycle a b c = threeCycle a b c * r) {y : Fin 7}
    (hy : y = a ∨ y = b ∨ y = c) : r y = a ∨ r y = b ∨ r y = c := by
  by_contra hcon
  push Not at hcon
  have h1 : threeCycle a b c (r y) = r y := threeCycle_other hcon.1 hcon.2.1 hcon.2.2
  have h2 : r (threeCycle a b c y) = threeCycle a b c (r y) := by
    have := congrArg (fun π : Equiv.Perm (Fin 7) => π y) hr
    simpa using this
  rw [h1] at h2
  have h3 : threeCycle a b c y = y := r.injective h2
  rcases hy with hy | hy | hy
  · rw [hy, threeCycle_a hab hac] at h3
    exact hab h3.symm
  · rw [hy, threeCycle_b hbc hac] at h3
    exact hbc h3.symm
  · rw [hy, threeCycle_c] at h3
    exact hac h3

theorem fixes_of_involution_commute_threeCycle {x y w : Fin 7} (hxy : x ≠ y) (hyw : y ≠ w)
    (hxw : x ≠ w) {z : Equiv.Perm (Fin 7)} (hz2 : z * z = 1)
    (hz : z * threeCycle x y w = threeCycle x y w * z) {p : Fin 7}
    (hp : p = x ∨ p = y ∨ p = w) : z p = p := by
  have hzz : ∀ q, z (z q) = q := fun q => by
    have := congrArg (fun π : Equiv.Perm (Fin 7) => π q) hz2
    simpa using this
  have hcomm : ∀ q, z (threeCycle x y w q) = threeCycle x y w (z q) := fun q => by
    have := congrArg (fun π : Equiv.Perm (Fin 7) => π q) hz
    simpa using this
  have hmem := fun q (hq : q = x ∨ q = y ∨ q = w) => mem_of_commute_threeCycle hxy hyw hxw hz hq
  by_contra hne
  rcases hp with hp | hp | hp
  · subst hp
    rcases hmem p (Or.inl rfl) with h | h | h
    · exact hne h
    · have h1 : z y = p := by rw [← h, hzz]
      have h2 : z y = w := by
        have := hcomm p
        rw [threeCycle_a hxy hxw, h, threeCycle_b hyw hxw] at this
        exact this
      exact hxw (h1.symm.trans h2)
    · have h1 : z w = p := by rw [← h, hzz]
      have h2 : z y = p := by
        have := hcomm p
        rw [threeCycle_a hxy hxw, h, threeCycle_c] at this
        exact this
      exact hyw (z.injective (h2.trans h1.symm))
  · subst hp
    rcases hmem p (Or.inr (Or.inl rfl)) with h | h | h
    · have h1 : z x = p := by rw [← h, hzz]
      have h2 : z w = p := by
        have := hcomm p
        rw [threeCycle_b hyw hxw, h, threeCycle_a hxy hxw] at this
        exact this
      exact hxw (z.injective (h1.trans h2.symm))
    · exact hne h
    · have h1 : z w = p := by rw [← h, hzz]
      have h2 : z w = x := by
        have := hcomm p
        rw [threeCycle_b hyw hxw, h, threeCycle_c] at this
        exact this
      exact hxy (h2.symm.trans h1)
  · subst hp
    rcases hmem p (Or.inr (Or.inr rfl)) with h | h | h
    · have h1 : z x = p := by rw [← h, hzz]
      have h2 : z x = y := by
        have := hcomm p
        rw [threeCycle_c, h, threeCycle_a hxy hxw] at this
        exact this
      exact hyw (h2.symm.trans h1)
    · have h1 : z y = p := by rw [← h, hzz]
      have h2 : z x = p := by
        have := hcomm p
        rw [threeCycle_c, h, threeCycle_b hyw hxw] at this
        exact this
      exact hxy (z.injective (h2.trans h1.symm))
    · exact hne h

theorem fixes_of_commute_block {B : Finset (Fin 7)} (hB : B.card = 4) {z : Equiv.Perm (Fin 7)}
    (hz : ∀ a b c : Fin 7, a ∈ B → b ∈ B → c ∈ B → a ≠ b → b ≠ c → a ≠ c →
      z * threeCycle a b c = threeCycle a b c * z) {y : Fin 7} (hy : y ∈ B) : z y = y := by
  have h3 : (B.erase y).card = 3 := by rw [Finset.card_erase_of_mem hy, hB]
  obtain ⟨u, v, w, huv, huw, hvw, hUVW⟩ := Finset.card_eq_three.1 h3
  have hu : u ∈ B := (Finset.mem_erase.1 (by rw [hUVW]; simp)).2
  have hv : v ∈ B := (Finset.mem_erase.1 (by rw [hUVW]; simp : v ∈ B.erase y)).2
  have hw : w ∈ B := (Finset.mem_erase.1 (by rw [hUVW]; simp : w ∈ B.erase y)).2
  have hyu : y ≠ u := fun h => (Finset.mem_erase.1 (by rw [hUVW]; simp : u ∈ B.erase y)).1 h.symm
  have hyv : y ≠ v := fun h => (Finset.mem_erase.1 (by rw [hUVW]; simp : v ∈ B.erase y)).1 h.symm
  have hyw : y ≠ w := fun h => (Finset.mem_erase.1 (by rw [hUVW]; simp : w ∈ B.erase y)).1 h.symm
  have h1 := mem_of_commute_threeCycle hyu huv hyv (hz y u v hy hu hv hyu huv hyv) (Or.inl rfl)
  have h2 := mem_of_commute_threeCycle hyu huw hyw (hz y u w hy hu hw hyu huw hyw) (Or.inl rfl)
  have h3' := mem_of_commute_threeCycle hyv hvw hyw (hz y v w hy hv hw hyv hvw hyw) (Or.inl rfl)
  by_contra hne
  rcases h1 with h | h | h
  · exact hne h
  · rcases h3' with h' | h' | h'
    · exact hne h'
    · exact huv (h.symm.trans h')
    · exact huw (h.symm.trans h')
  · rcases h2 with h' | h' | h'
    · exact hne h'
    · exact huv (h'.symm.trans h)
    · exact hvw (h.symm.trans h')

theorem false_of_involution_commuting_stab {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P {4, 3}) {z : Equiv.Perm (Fin 7)} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hcomm : ∀ x : Equiv.Perm (Fin 7), x ∈ alternatingGroup (Fin 7) → StabilizesPartition x P →
      x * z = z * x) : False := by
  obtain ⟨-, hdisj, hcov, hcard⟩ := hP
  have h4 : (4 : ℕ) ∈ P.val.map Finset.card := by
    rw [hcard]
    simp
  have h3 : (3 : ℕ) ∈ P.val.map Finset.card := by
    rw [hcard]
    simp
  obtain ⟨B₄, hB₄, hc4⟩ := Multiset.mem_map.1 h4
  obtain ⟨B₃, hB₃, hc3⟩ := Multiset.mem_map.1 h3
  have hB43 : B₄ ≠ B₃ := fun h => by
    rw [h] at hc4
    omega
  have hd : Disjoint B₄ B₃ := hdisj B₄ hB₄ B₃ hB₃ hB43
  have hunion : B₄ ∪ B₃ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hd, hc4, hc3]
    simp
  have hz4 : ∀ a b c : Fin 7, a ∈ B₄ → b ∈ B₄ → c ∈ B₄ → a ≠ b → b ≠ c → a ≠ c →
      z * threeCycle a b c = threeCycle a b c * z := by
    intro a b c ha hb hc hab hbc hac
    exact (hcomm _ (threeCycle_mem_alternating hab hbc)
      (stabilizes_of_threeCycle hdisj hB₄ hab hbc hac ha hb hc)).symm
  have hfix4 : ∀ y ∈ B₄, z y = y := fun y hy => fixes_of_commute_block hc4 hz4 hy
  obtain ⟨x, y, w, hxy, hxw, hyw, hB3eq⟩ := Finset.card_eq_three.1 hc3
  have hx : x ∈ B₃ := by rw [hB3eq]; simp
  have hy : y ∈ B₃ := by rw [hB3eq]; simp
  have hw : w ∈ B₃ := by rw [hB3eq]; simp
  have hz3 : z * threeCycle x y w = threeCycle x y w * z :=
    (hcomm _ (threeCycle_mem_alternating hxy hyw)
      (stabilizes_of_threeCycle hdisj hB₃ hxy hyw hxw hx hy hw)).symm
  have hfix3 : ∀ p ∈ B₃, z p = p := fun p hp => by
    rw [hB3eq] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact fixes_of_involution_commute_threeCycle hxy hyw hxw hz2 hz3 hp
  apply hz1
  refine Equiv.ext fun p => ?_
  have hp : p ∈ B₄ ∪ B₃ := by
    rw [hunion]
    exact Finset.mem_univ p
  rcases Finset.mem_union.1 hp with hp | hp
  · rw [hfix4 p hp]
    rfl
  · rw [hfix3 p hp]
    rfl

end CFSG.Quasithin.S151TB
