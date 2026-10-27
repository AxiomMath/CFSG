module

public import CFSG.Quasithin.Recognition.M12AmalCheck2
public import CFSG.Quasithin.Recognition.CertTwoLocal
public import CFSG.Quasithin.Recognition.M12AmalCheck

public section

namespace CFSG.Quasithin.M12Amal

open CFSG.Sporadic.Bridge Equiv

theorem mA_mem : mA ∈ CFSG.Open.quasithinM12 := by
  rw [quasithinM12_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem mB_mem : mB ∈ CFSG.Open.quasithinM12 := by
  rw [quasithinM12_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem mLetters : ∀ k < 2, ∀ l ∈ decode (mCodes.getD k []), l.1 < 5 := by decide +kernel

theorem wordProd_genG_coe (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 5) :
    ((wordProd genG w : M12G) : Perm (Fin 12)) = wordProd genP w := by
  rw [coe_wordProd]
  exact wordProd_congr w fun l hl => genG_coe l.1 (hw l hl)

theorem mA_wordG : (⟨mA, mA_mem⟩ : M12G) = wordProd genG (decode (mCodes.getD 0 [])) :=
  Subtype.ext (mA_eq.trans (wordProd_genG_coe _ (mLetters 0 (by norm_num))).symm)

theorem mB_wordG : (⟨mB, mB_mem⟩ : M12G) = wordProd genG (decode (mCodes.getD 1 [])) :=
  Subtype.ext (mB_eq.trans (wordProd_genG_coe _ (mLetters 1 (by norm_num))).symm)

theorem genG_mem_closure (i : ℕ) :
    genG i ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 3, genG 4} : Set M12G) := by
  by_cases hi : i < 5
  · apply Subgroup.subset_closure
    interval_cases i <;> simp
  · have : genG i = 1 := by simp [genG, hi]
    rw [this]
    exact Subgroup.one_mem _

theorem m12_gen :
    Subgroup.closure ({genG 0, genG 1, genG 2, genG 3, genG 4} : Set M12G) = ⊤ := by
  have hk : Subgroup.closure ((Subtype.val : M12G → Perm (Fin 12)) ⁻¹'
      ({mA, mB} : Set (Perm (Fin 12)))) = ⊤ :=
    Subgroup.closure_closure_coe_preimage (k := ({mA, mB} : Set (Perm (Fin 12))))
  rw [eq_top_iff, ← hk, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · have : g = wordProd genG (decode (mCodes.getD 0 [])) := by
      rw [← mA_wordG]
      exact Subtype.ext hg
    rw [SetLike.mem_coe, this]
    exact wordProd_mem genG_mem_closure _
  · have : g = wordProd genG (decode (mCodes.getD 1 [])) := by
      rw [← mB_wordG]
      exact Subtype.ext hg
    rw [SetLike.mem_coe, this]
    exact wordProd_mem genG_mem_closure _

theorem genG_orders : genG 0 ^ 4 = 1 ∧ genG 1 ^ 4 = 1 ∧ genG 2 ^ 2 = 1 ∧ genG 3 ^ 3 = 1 ∧
    genG 4 ^ 3 = 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := genP_orders
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_pow, genG_coe 0 (by norm_num)]
    exact h0
  · rw [Subgroup.coe_pow, genG_coe 1 (by norm_num)]
    exact h1
  · rw [Subgroup.coe_pow, genG_coe 2 (by norm_num)]
    exact h2
  · rw [Subgroup.coe_pow, genG_coe 3 (by norm_num)]
    exact h3
  · rw [Subgroup.coe_pow, genG_coe 4 (by norm_num)]
    exact h4

theorem wordProd_mem_letters {G : Type*} [Group G] {K : Subgroup G} {x : ℕ → G} {P : ℕ → Prop}
    (hx : ∀ i, P i → x i ∈ K) {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, P l.1) :
    wordProd x w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    refine K.mul_mem ?_ (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    split
    · exact hx _ (hw l List.mem_cons_self)
    · exact K.inv_mem (hx _ (hw l List.mem_cons_self))

theorem gen4_mem (d : M12G) (i : ℕ) :
    gen4 d i ∈ Subgroup.closure ({genG 0, genG 1, genG 2, d} : Set M12G) := by
  apply Subgroup.subset_closure
  unfold gen4
  split_ifs <;> simp

theorem xy_mem_closure_D (j : ℕ) (hj3 : 3 ≤ j) (hj : j < 44) :
    genG 3 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, dG j} : Set M12G) ∧
      genG 4 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, dG j} : Set M12G) := by
  obtain ⟨hl1, he1⟩ := ox_chk (j - 3) (by omega)
  obtain ⟨hl2, he2⟩ := oy_chk (j - 3) (by omega)
  have hj' : j - 3 + 3 = j := by omega
  rw [hj'] at he1 he2
  have h1 : wordProd (gen4 (dG j)) (decode (oxCodes.getD (j - 3) [])) = genG 3 := by
    have r1 := wordL4_rep j hj _ hl1
    rw [he1] at r1
    exact eq_of_reprG r1 (reprG_gen 3 (by norm_num))
  have h2 : wordProd (gen4 (dG j)) (decode (oyCodes.getD (j - 3) [])) = genG 4 := by
    have r1 := wordL4_rep j hj _ hl2
    rw [he2] at r1
    exact eq_of_reprG r1 (reprG_gen 4 (by norm_num))
  refine ⟨?_, ?_⟩
  · rw [← h1]
    exact wordProd_mem_letters (P := fun k => k < 4) (fun i _ => gen4_mem _ i) hl1
  · rw [← h2]
    exact wordProd_mem_letters (P := fun k => k < 4) (fun i _ => gen4_mem _ i) hl2

theorem dec_xA (j i : ℕ) (hj : j < 2) (hi : i < 64) :
    ∃ (k : Fin 44) (i₁ i₂ : Fin 64), k.1 < 2 ∧
      dG j * telG i * genG 3 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decX_chk j (by omega) i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, decXA_chk j hj i hi, ?_⟩
  exact reprG_eq (reprG_mul (reprG_mul (reprG_d j (by omega)) (reprG_tel i hi))
    (reprG_gen 3 (by norm_num)))
    (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

theorem dec_yB (j i : ℕ) (hj : j = 0 ∨ j = 2) (hi : i < 64) :
    ∃ (k : Fin 44) (i₁ i₂ : Fin 64), (k.1 = 0 ∨ k.1 = 2) ∧
      dG j * telG i * genG 4 = telG i₁ * dG k * telG i₂ := by
  obtain ⟨hk, h1, h2, he⟩ := decY_chk j (by omega) i hi
  have hB := decYB_chk i hi
  refine ⟨⟨_, hk⟩, ⟨_, h1⟩, ⟨_, h2⟩, ?_, ?_⟩
  · rcases hj with rfl | rfl
    · exact hB.1
    · exact hB.2
  · exact reprG_eq (reprG_mul (reprG_mul (reprG_d j (by omega)) (reprG_tel i hi))
      (reprG_gen 4 (by norm_num)))
      (reprG_mul (reprG_mul (reprG_tel _ h1) (reprG_d _ hk)) (reprG_tel _ h2)) he

@[expose] noncomputable def m12Data : OvergroupData M12G (Fin 64) (Fin 44) where
  a := genG 0
  b := genG 1
  s := genG 2
  x := genG 3
  y := genG 4
  gen := m12_gen
  ha := genG_orders.1
  hb := genG_orders.2.1
  hs := genG_orders.2.2.1
  hx := genG_orders.2.2.2.1
  hy := genG_orders.2.2.2.2
  Tel := fun i => telG i
  i0 := 0
  Tel_zero := tel_zero
  Tel_mem := fun i => tel_mem i i.2
  Tel_next := fun i =>
    ⟨tel_next i i.2 0 (by norm_num), tel_next i i.2 1 (by norm_num),
      tel_next i i.2 2 (by norm_num)⟩
  D := fun j => dG j
  j0 := 0
  ja := 1
  jb := 2
  D_zero := d_zero
  decX := fun j i => dec_x j i j.2 i.2
  decY := fun j i => dec_y j i j.2 i.2
  decXA := fun j hj i => by
    have hj2 : j.1 < 2 := by rcases hj with rfl | rfl <;> decide
    obtain ⟨k, i₁, i₂, hk, he⟩ := dec_xA j i hj2 i.2
    refine ⟨k, ?_, i₁, i₂, he⟩
    have : k.1 = 0 ∨ k.1 = 1 := by omega
    rcases this with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  decYB := fun j hj i => by
    have hj2 : j.1 = 0 ∨ j.1 = 2 := by rcases hj with rfl | rfl <;> decide
    obtain ⟨k, i₁, i₂, hk, he⟩ := dec_yB j i hj2 i.2
    refine ⟨k, ?_, i₁, i₂, he⟩
    rcases hk with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  D_ja := by
    show dG 1 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G)
    rw [dG_one]
    exact Subgroup.subset_closure (by simp)
  D_jb := by
    show dG 2 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G)
    rw [dG_two]
    exact Subgroup.subset_closure (by simp)
  genA := by
    show genG 3 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, dG 1} : Set M12G)
    rw [dG_one]
    exact Subgroup.subset_closure (by simp)
  genB := by
    show genG 4 ∈ Subgroup.closure ({genG 0, genG 1, genG 2, dG 2} : Set M12G)
    rw [dG_two]
    exact Subgroup.subset_closure (by simp)
  genO := fun j h0 ha hb => by
    have h3 : 3 ≤ j.1 := by
      have h0' : j.1 ≠ 0 := fun h => h0 (Fin.ext h)
      have h1' : j.1 ≠ 1 := fun h => ha (Fin.ext h)
      have h2' : j.1 ≠ 2 := fun h => hb (Fin.ext h)
      omega
    exact xy_mem_closure_D j h3 j.2
  sepA := fun i => ne_of_reprG (reprG_tel i i.2) (reprG_d 1 (by norm_num)) (sepA_chk i i.2)
  sepB := fun i => ne_of_reprG (reprG_tel i i.2) (reprG_d 2 (by norm_num)) (sepB_chk i i.2)
  sepAB := fun i₁ i₂ => ne_of_reprG
    (reprG_mul (reprG_mul (reprG_tel i₁ i₁.2) (reprG_d 1 (by norm_num))) (reprG_tel i₂ i₂.2))
    (reprG_d 2 (by norm_num)) (sepAB_chk i₁ i₁.2 i₂ i₂.2)

theorem tel_inj : Function.Injective fun i : Fin 64 => telG i := by
  intro i j h
  have h' : telG i = telG j := h
  exact Fin.ext (tl_inj_chk i i.2 j j.2
    (repL_unique (reprG_tel i i.2) (h' ▸ reprG_tel j j.2)))

theorem m12_card_T : Nat.card m12Data.T = 64 := by
  have h1 : Nat.card m12Data.T = Nat.card (Set.range m12Data.Tel) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => m12Data.mem_T_iff g)
  rw [h1]
  exact (Nat.card_range_of_injective tel_inj).trans (by simp)

theorem isPGroup_T : IsPGroup 2 m12Data.T :=
  IsPGroup.of_card (n := 6) (by rw [m12_card_T]; norm_num)

theorem false_of_isPGroup_two_of_pow_three {G : Type*} [Group G] {H : Subgroup G}
    (h : IsPGroup 2 H) {x : G} (hx : x ∈ H) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : False := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 h ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · exact hx1 (orderOf_eq_one_iff.1 h1)
  · rw [h1] at hk'
    rcases k with _ | _ | k
    · simp at hk'
    · simp at hk'
    · have : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
      omega

theorem m12_syl : IsPGroup 2 m12Data.T ∧ ¬ 2 ∣ m12Data.T.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isPGroup_T, ?_⟩
  obtain ⟨S, hS⟩ := isPGroup_T.exists_le_sylow
  have hx1 : genG 3 ≠ 1 := ne_of_reprG (reprG_gen 3 (by norm_num)) reprG_one x_ne_one_chk
  have hy1 : genG 4 ≠ 1 := ne_of_reprG (reprG_gen 4 (by norm_num)) reprG_one y_ne_one_chk
  rcases m12Data.lattice (S : Subgroup M12G) hS with h | h | h | h
  · have := S.not_dvd_index
    rwa [h] at this
  · exfalso
    have hxS : genG 3 ∈ (S : Subgroup M12G) := by rw [h]; exact m12Data.x_mem_A
    exact false_of_isPGroup_two_of_pow_three S.isPGroup' hxS genG_orders.2.2.2.1 hx1
  · exfalso
    have hyS : genG 4 ∈ (S : Subgroup M12G) := by rw [h]; exact m12Data.y_mem_B
    exact false_of_isPGroup_two_of_pow_three S.isPGroup' hyS genG_orders.2.2.2.2 hy1
  · exfalso
    have hxS : genG 3 ∈ (S : Subgroup M12G) := by rw [h]; trivial
    exact false_of_isPGroup_two_of_pow_three S.isPGroup' hxS genG_orders.2.2.2.1 hx1

theorem mem_normalizer_closure_of_conj {G : Type*} [Group G] (U : Set G) (g : G)
    (h1 : ∀ u ∈ U, g * u * g⁻¹ ∈ U) (h2 : ∀ u ∈ U, g⁻¹ * u * g ∈ U) :
    g ∈ Subgroup.normalizer (Subgroup.closure U : Set G) := by
  apply Subgroup.normalizer_le_normalizer_closure U
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨h1 h, fun hh => ?_⟩
  have h3 := h2 _ hh
  have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
  rwa [e] at h3

theorem closure_le_normalizer_zpowers {G : Type*} [Group G] (S : Set G) (z : G)
    (h : ∀ s ∈ S, s * z = z * s) :
    Subgroup.closure S ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine (Subgroup.closure_le _).2 fun s hs => ?_
  have hc : Commute s z := h s hs
  have hs' : s ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact ((hc.symm).zpow_left n).eq
  exact Subgroup.centralizer_le_normalizer _ hs'

theorem telG_ne_one {i : ℕ} (hi : i < 64) (h : tl i ≠ idl) : telG i ≠ 1 :=
  ne_of_reprG (reprG_tel i hi) reprG_one h

theorem U_conj (k j : ℕ) (hk : k ∈ [0, 1, 2, 4]) (hj : j ∈ [4, 8, 29]) :
    genG k * telG j * (genG k)⁻¹ ∈ ({telG 4, telG 8, telG 29} : Set M12G) ∧
      (genG k)⁻¹ * telG j * genG k ∈ ({telG 4, telG 8, telG 29} : Set M12G) := by
  obtain ⟨h1, h2⟩ := U_norm_chk k hk j hj
  have hk5 : k < 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have hj64 : j < 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    omega
  have r1 : ReprG (compL (compL (gl k) (tl j)) (gil k)) (genG k * telG j * (genG k)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen k hk5) (reprG_tel j hj64)) (reprG_inv_gen k hk5)
  have r2 : ReprG (compL (compL (gil k) (tl j)) (gl k)) ((genG k)⁻¹ * telG j * genG k) :=
    reprG_mul (reprG_mul (reprG_inv_gen k hk5) (reprG_tel j hj64)) (reprG_gen k hk5)
  have key : ∀ (l : List ℕ) (g : M12G), ReprG l g → l ∈ [tl 4, tl 8, tl 29] →
      g ∈ ({telG 4, telG 8, telG 29} : Set M12G) := by
    intro l g hl hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    · left
      exact eq_of_reprG hl (by rw [h]; exact reprG_tel 4 (by norm_num))
    · right; left
      exact eq_of_reprG hl (by rw [h]; exact reprG_tel 8 (by norm_num))
    · right; right
      exact eq_of_reprG hl (by rw [h]; exact reprG_tel 29 (by norm_num))
  exact ⟨key _ _ r1 h1, key _ _ r2 h2⟩

@[expose] noncomputable def m12Extra : m12Data.Extra where
  syl := m12_syl
  g := dG 17
  hg := fun i i' h => by
    have hrep : ReprG (compL (compL (dTab.getD 17 []) (tl i')) (dInvTab.getD 17 []))
        (dG 17 * telG i' * (dG 17)⁻¹) :=
      reprG_mul (reprG_mul (reprG_d 17 (by norm_num)) (reprG_tel i' i'.2))
        (reprG_dInv 17 (by norm_num))
    have h' : dG 17 * telG i' * (dG 17)⁻¹ = telG i := h
    rw [h'] at hrep
    have hid := hg_chk i' i'.2 i i.2 (repL_unique hrep (reprG_tel i i.2))
    exact eq_of_reprG (reprG_tel i i.2) (show ReprG (tl i) 1 by rw [hid]; exact reprG_one)
  a_ne_one := fun h => a_ne_one_chk (repL_unique (reprG_gen 0 (by norm_num))
    (show ReprG idl (genG 0) by rw [show genG 0 = 1 from h]; exact reprG_one))
  xN := ⟨2, fun i' h => by
    have hrep : ReprG (compL (compL (gl 3) (tl 2)) (gil 3))
        (genG 3 * telG 2 * (genG 3)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen 3 (by norm_num)) (reprG_tel 2 (by norm_num)))
        (reprG_inv_gen 3 (by norm_num))
    have h' : genG 3 * telG 2 * (genG 3)⁻¹ = telG i' := h
    rw [h'] at hrep
    exact xN_chk i' i'.2 (repL_unique hrep (reprG_tel i' i'.2))⟩
  yN := ⟨1, fun i' h => by
    have hrep : ReprG (compL (compL (gl 4) (tl 1)) (gil 4))
        (genG 4 * telG 1 * (genG 4)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen 4 (by norm_num)) (reprG_tel 1 (by norm_num)))
        (reprG_inv_gen 4 (by norm_num))
    have h' : genG 4 * telG 1 * (genG 4)⁻¹ = telG i' := h
    rw [h'] at hrep
    exact yN_chk i' i'.2 (repL_unique hrep (reprG_tel i' i'.2))⟩
  PA := Subgroup.zpowers (telG 4)
  PA_ne := fun h => telG_ne_one (by norm_num) z_ne_one_chk (Subgroup.zpowers_eq_bot.1 h)
  PA_p := m12_syl.1.to_le (Subgroup.zpowers_le.2 (m12Data.Tel_mem_T (4 : Fin 64)))
  PA_norm := by
    show Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G) ≤ _
    refine closure_le_normalizer_zpowers _ _ fun s hs => ?_
    have hcomm : ∀ k < 4, genG k * telG 4 = telG 4 * genG k := fun k hk =>
      eq_of_reprG (reprG_mul (reprG_gen k (by omega)) (reprG_tel 4 (by norm_num)))
        (show ReprG (compL (gl k) (tl 4)) (telG 4 * genG k) by
          rw [z_comm_chk k hk]
          exact reprG_mul (reprG_tel 4 (by norm_num)) (reprG_gen k (by omega)))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hcomm 0 (by norm_num)
    · exact hcomm 1 (by norm_num)
    · exact hcomm 2 (by norm_num)
    · exact hcomm 3 (by norm_num)
  PB := Subgroup.closure ({telG 4, telG 8, telG 29} : Set M12G)
  PB_ne := fun h => by
    have hmem : telG 4 ∈ Subgroup.closure ({telG 4, telG 8, telG 29} : Set M12G) :=
      Subgroup.subset_closure (by simp)
    rw [h, Subgroup.mem_bot] at hmem
    exact telG_ne_one (by norm_num) z_ne_one_chk hmem
  PB_p := m12_syl.1.to_le ((Subgroup.closure_le _).2 (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact m12Data.Tel_mem_T (4 : Fin 64)
    · exact m12Data.Tel_mem_T (8 : Fin 64)
    · exact m12Data.Tel_mem_T (29 : Fin 64)))
  PB_norm := by
    show Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G) ≤ _
    refine (Subgroup.closure_le _).2 fun s hs => ?_
    have hU : ∀ k ∈ [0, 1, 2, 4], genG k ∈ Subgroup.normalizer
        (Subgroup.closure ({telG 4, telG 8, telG 29} : Set M12G) : Set M12G) := by
      intro k hk
      refine mem_normalizer_closure_of_conj _ _ (fun u hu => ?_) (fun u hu => ?_)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · exact (U_conj k 4 hk (by simp)).1
        · exact (U_conj k 8 hk (by simp)).1
        · exact (U_conj k 29 hk (by simp)).1
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · exact (U_conj k 4 hk (by simp)).2
        · exact (U_conj k 8 hk (by simp)).2
        · exact (U_conj k 29 hk (by simp)).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hU 0 (by simp)
    · exact hU 1 (by simp)
    · exact hU 2 (by simp)
    · exact hU 4 (by simp)

end CFSG.Quasithin.M12Amal
