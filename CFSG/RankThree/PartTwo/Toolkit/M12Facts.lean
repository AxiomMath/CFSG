module

public import Certificates.Certificate9950

public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open scoped commutatorElement

theorem x_mem_P0 : x ∈ P0 := subset_closure (by simp)

theorem y_mem_P0 : y ∈ P0 := subset_closure (by simp)

theorem z_mem_P0 : ⁅x, y⁆ ∈ P0 := by
  rw [commutatorElement_def]
  exact P0.mul_mem (P0.mul_mem (P0.mul_mem x_mem_P0 y_mem_P0) (P0.inv_mem x_mem_P0))
    (P0.inv_mem y_mem_P0)

theorem cube_of_mem_P0 {g : G12} (hg : g ∈ P0) : g ^ 3 = 1 :=
  pow_three_eq_one_of_mem x_cube z_comm_x z_comm_y y_cube hg

theorem not_comm_P0 : ¬ IsMulCommutative P0 := by
  intro h
  apply z_ne_one
  rw [commutatorElement_eq_one_iff_mul_comm]
  have h1 := congrArg Subtype.val (h.is_comm.comm ⟨x, x_mem_P0⟩ ⟨y, y_mem_P0⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
  exact h1

theorem isExtraspecial_P0 : IsExtraspecialPGroup 3 P0 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three
    (IsPGroup.of_card (n := 3) (by rw [card_P0]; norm_num)) (fun g => Subtype.ext ?_)
    (by rw [card_P0]; norm_num) not_comm_P0
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact cube_of_mem_P0 g.2

theorem exponent_P0 : Monoid.exponent P0 = 3 := by
  have hdvd : Monoid.exponent P0 ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact cube_of_mem_P0 g.2)
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd) with h | h
  · exfalso
    have h1 := Monoid.pow_exponent_eq_one (⟨x, x_mem_P0⟩ : P0)
    rw [h, pow_one] at h1
    have hx1 : x = 1 := by simpa using congrArg Subtype.val h1
    apply z_ne_one
    rw [hx1, commutatorElement_one_left]
  · exact h

theorem center_tables :
    ∀ t ∈ P0T, tmul t xT = tmul xT t → tmul t yT = tmul yT t →
    t = tid ∨ t = zT ∨ t = tmul zT zT := by
  exact Certificates.certificate9950.1

theorem z_mem_center : (⟨⁅x, y⁆, z_mem_P0⟩ : P0) ∈ center P0 := by
  rw [mem_center_iff]
  intro g
  have hle : P0 ≤ centralizer {⁅x, y⁆} := by
    rw [P0, closure_le]
    rintro s (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 z_comm_x.eq.symm
    · exact mem_centralizer_singleton_iff.2 z_comm_y.eq.symm
  exact Subtype.ext (mem_centralizer_singleton_iff.1 (hle g.2))

theorem center_P0 : (center P0).map P0.subtype = zpowers ⁅x, y⁆ := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    have hx := (mem_center_iff.1 hc) ⟨x, x_mem_P0⟩
    have hy := (mem_center_iff.1 hc) ⟨y, y_mem_P0⟩
    have hx' : tmul (tbl c.1.1) xT = tmul xT (tbl c.1.1) := by
      have h1 := congrArg Subtype.val hx
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      rw [← tbl_x, ← tblG_mul, ← tblG_mul]
      exact congrArg (fun g : G12 => tbl g.1) h1.symm
    have hy' : tmul (tbl c.1.1) yT = tmul yT (tbl c.1.1) := by
      have h1 := congrArg Subtype.val hy
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
      rw [← tbl_y, ← tblG_mul, ← tblG_mul]
      exact congrArg (fun g : G12 => tbl g.1) h1.symm
    rcases center_tables _ ((mem_P0_iff _).1 c.2) hx' hy' with h | h | h
    · have : c.1 = 1 := by rw [eq_iff_tbl, h, tblG_one]
      rw [Subgroup.subtype_apply, this]
      exact one_mem _
    · have : c.1 = ⁅x, y⁆ := by rw [eq_iff_tbl, h, tbl_z]
      rw [Subgroup.subtype_apply, this]
      exact mem_zpowers _
    · have : c.1 = ⁅x, y⁆ ^ 2 := by rw [eq_iff_tbl, h, tblG_pow, tbl_z]; rfl
      rw [Subgroup.subtype_apply, this]
      exact (zpowers _).pow_mem (mem_zpowers _) 2
  · rw [zpowers_le]
    exact ⟨_, z_mem_center, rfl⟩

noncomputable abbrev E : Subgroup G12 := basisE.sub

noncomputable abbrev F : Subgroup G12 := basisF.sub

noncomputable abbrev A : Subgroup G12 := basisA.sub

noncomputable abbrev A' : Subgroup G12 := basisA'.sub

theorem mem_E_iff (g : G12) : g ∈ E ↔ tbl g.1 ∈ ET := mem_sub_iff basisE tbl_z tbl_x g

theorem mem_F_iff (g : G12) : g ∈ F ↔ tbl g.1 ∈ FT := mem_sub_iff basisF tbl_z tbl_y g

theorem mem_A'_iff (g : G12) : g ∈ A' ↔ tbl g.1 ∈ A'T := mem_sub_iff basisA' tbl_z tbl_a' g

theorem sub_le_P0 (B : E9Basis G12) (ha : B.a ∈ P0) (hb : B.b ∈ P0) : B.sub ≤ P0 := by
  rw [closure_le]
  rintro s (rfl | rfl)
  · exact ha
  · exact hb

theorem E_le : E ≤ P0 := sub_le_P0 _ z_mem_P0 x_mem_P0

theorem F_le : F ≤ P0 := sub_le_P0 _ z_mem_P0 y_mem_P0

theorem A_le : A ≤ P0 := sub_le_P0 _ z_mem_P0 (P0.mul_mem x_mem_P0 y_mem_P0)

theorem A'_le : A' ≤ P0 :=
  sub_le_P0 _ z_mem_P0 (P0.mul_mem x_mem_P0 (P0.pow_mem y_mem_P0 2))

theorem distinct_tables :
    xT ∉ FT ∧ xT ∉ AT ∧ xT ∉ A'T ∧ yT ∉ AT ∧ yT ∉ A'T ∧ aT ∉ A'T := by
  exact Certificates.certificate9950.2.1

theorem x_mem_E : x ∈ E := subset_closure (Or.inr basisE_b.symm)

theorem y_mem_F : y ∈ F := subset_closure (Or.inr basisF_b.symm)

theorem a_mem_A : x * y ∈ A := subset_closure (Or.inr basisA_b.symm)

theorem a'_mem_A' : x * y ^ 2 ∈ A' := subset_closure (Or.inr basisA'_b.symm)

theorem z_mem_sub (i : Fin 4) :
    ⁅x, y⁆ ∈ (ex27Basis x_cube y_cube z_comm_x z_comm_y z_ne_one i).sub :=
  subset_closure (Or.inl rfl)

theorem E_ne_F : E ≠ F := by
  intro h
  have := (mem_F_iff x).1 (h ▸ x_mem_E)
  rw [tbl_x] at this
  exact distinct_tables.1 this

theorem E_ne_A : E ≠ A := by
  intro h
  have hx : x ∈ A := h ▸ x_mem_E
  have := (mem_A_iff x).1 hx
  rw [tbl_x] at this
  exact distinct_tables.2.1 this

theorem E_ne_A' : E ≠ A' := by
  intro h
  have := (mem_A'_iff x).1 (h ▸ x_mem_E)
  rw [tbl_x] at this
  exact distinct_tables.2.2.1 this

theorem F_ne_A : F ≠ A := by
  intro h
  have hy : y ∈ A := h ▸ y_mem_F
  have := (mem_A_iff y).1 hy
  rw [tbl_y] at this
  exact distinct_tables.2.2.2.1 this

theorem F_ne_A' : F ≠ A' := by
  intro h
  have := (mem_A'_iff y).1 (h ▸ y_mem_F)
  rw [tbl_y] at this
  exact distinct_tables.2.2.2.2.1 this

theorem A_ne_A' : A ≠ A' := by
  intro h
  have := (mem_A'_iff (x * y)).1 (h ▸ a_mem_A)
  rw [tbl_a] at this
  exact distinct_tables.2.2.2.2.2 this

theorem nine_eq : {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} = {E, F, A, A'} := by
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hB, h9⟩
    exact eq_of_le_of_card_eq_nine x_cube y_cube z_comm_x z_comm_y card_P0 hB h9
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨E_le, basisE.card⟩
    · exact ⟨F_le, basisF.card⟩
    · exact ⟨A_le, basisA.card⟩
    · exact ⟨A'_le, basisA'.card⟩

theorem nine_ncard :
    {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9}.ncard = 4 := by
  rw [nine_eq, Set.ncard_insert_of_notMem (by simp [E_ne_F, E_ne_A, E_ne_A']),
    Set.ncard_insert_of_notMem (by simp [F_ne_A, F_ne_A']), Set.ncard_pair A_ne_A']

theorem nine_props
    (B : Subgroup G12) (hB : B ≤ P0) (h9 : Nat.card B = 9) :
    IsElementaryAbelian 3 B ∧ (center P0).map P0.subtype ≤ B := by
  rw [center_P0, zpowers_le]
  have hB' : B ∈ ({E, F, A, A'} : Set (Subgroup G12)) := nine_eq ▸ ⟨hB, h9⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB'
  rcases hB' with rfl | rfl | rfl | rfl
  · exact ⟨basisE.isElementaryAbelian, z_mem_sub 0⟩
  · exact ⟨basisF.isElementaryAbelian, z_mem_sub 1⟩
  · exact ⟨basisA.isElementaryAbelian, z_mem_sub 2⟩
  · exact ⟨basisA'.isElementaryAbelian, z_mem_sub 3⟩


theorem card_NP :
    Nat.card (normalizer (P0 : Set G12)) = 108 :=
  card_normalizer_P0_eq

theorem P0_le_NP : P0 ≤ normalizer (P0 : Set G12) := le_normalizer

theorem NP_le_NE :
    normalizer (P0 : Set G12) ≤ normalizer (E : Set G12) := fun _ hg =>
  (mem_normalizer_P0_facts hg).2.1

theorem NP_le_NF :
    normalizer (P0 : Set G12) ≤ normalizer (F : Set G12) := fun _ hg =>
  (mem_normalizer_P0_facts hg).2.2

abbrev QP : Type := normalizer (P0 : Set G12) ⧸ P0.subgroupOf (normalizer (P0 : Set G12))

theorem mem_P0_of_tbl {g : G12} (h : P0T.contains (tbl g.1) = true) : g ∈ P0 :=
  (mem_P0_iff g).2 (List.contains_iff_mem.1 h)

theorem card_QP :
    Nat.card QP = 4 := by
  have h : Nat.card (normalizer (P0 : Set G12)) =
      Nat.card QP * Nat.card (P0.subgroupOf (normalizer (P0 : Set G12))) :=
    (P0.subgroupOf (normalizer (P0 : Set G12))).card_eq_card_quotient_mul_card_subgroup
  rw [card_NP, Nat.card_congr (subgroupOfEquivOfLe P0_le_NP).toEquiv, card_P0] at h
  omega

theorem isElementaryAbelian_QP :
    IsElementaryAbelian 2 QP where
  is_comm := ⟨IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (G := QP)
    (by rw [card_QP]; norm_num)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun q => by
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact (mem_normalizer_P0_facts g.2).1

@[expose] def g0 : G12 := wE wG0

theorem g0_tables :
    predN [xT, yT] P0T (wordT wG0) = true ∧ tconj (wordT wG0) zT = tmul zT zT ∧
    A'T.contains (tconj (wordT wG0) aT) = true ∧ AT.contains (tconj (wordT wG0) a'T) = true ∧
    predN [zT, aT] AT (wordT wG0) = false := by
  exact Certificates.certificate9950.2.2.1

theorem g0_mem_NP : g0 ∈ normalizer (P0 : Set G12) :=
  (mem_normalizer_pair_iff tbl_x tbl_y mem_P0_iff g0).2 (by rw [g0, tbl_wE]; exact g0_tables.1)

theorem g0_conj_z : g0 * ⁅x, y⁆ * g0⁻¹ = ⁅x, y⁆ ^ 2 := by
  rw [eq_iff_tbl, tblG_conj, tblG_pow, g0, tbl_wE, tbl_z, g0_tables.2.1]
  rfl

theorem g0_not_mem_NA : g0 ∉ normalizer (A : Set G12) := by
  intro h
  have h1 := (mem_normalizer_pair_iff tbl_z tbl_a mem_A_iff g0).1 h
  rw [g0, tbl_wE] at h1
  have h2 := g0_tables.2.2.2.2
  rw [predN, h1] at h2
  exact Bool.noConfusion h2

theorem map_conj_closure_pair (g u v : G12) :
    (closure ({u, v} : Set G12)).map (MulAut.conj g).toMonoidHom =
      closure {g * u * g⁻¹, g * v * g⁻¹} := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_g0_A : A.map (MulAut.conj g0).toMonoidHom = A' := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [map_conj_closure_pair, closure_le]
    rintro s (rfl | rfl)
    · show g0 * ⁅x, y⁆ * g0⁻¹ ∈ A'
      rw [g0_conj_z]
      exact basisA'.sub.pow_mem (z_mem_sub 3) 2
    · rw [SetLike.mem_coe, mem_A'_iff, tblG_conj, basisA_b, tbl_a, g0, tbl_wE]
      exact List.contains_iff_mem.1 g0_tables.2.2.1
  · rw [card_map_conj, basisA.card, basisA'.card]

theorem map_g0_A' : A'.map (MulAut.conj g0).toMonoidHom = A := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [map_conj_closure_pair, closure_le]
    rintro s (rfl | rfl)
    · show g0 * ⁅x, y⁆ * g0⁻¹ ∈ A
      rw [g0_conj_z]
      exact basisA.sub.pow_mem (z_mem_sub 2) 2
    · rw [SetLike.mem_coe, mem_A_iff, tblG_conj, basisA'_b, tbl_a', g0, tbl_wE]
      exact List.contains_iff_mem.1 g0_tables.2.2.2.1
  · rw [card_map_conj, basisA'.card, basisA.card]

theorem eq_of_mem_normalizer {B : Subgroup G12} {g : G12} (hg : g ∈ normalizer (B : Set G12)) :
    B.map (MulAut.conj g).toMonoidHom = B := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (mem_normalizer_iff.1 hg c).1 hc
  · intro hb
    refine ⟨g⁻¹ * b * g, (mem_normalizer_iff.1 hg _).2 ?_, ?_⟩
    · rw [show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
      exact hb
    · change g * (g⁻¹ * b * g) * g⁻¹ = b
      group

theorem not_NP_le_NA :
    ¬ normalizer (P0 : Set G12) ≤ normalizer (A : Set G12) :=
  fun h => g0_not_mem_NA (h g0_mem_NP)

theorem not_NP_le_NA' :
    ¬ normalizer (P0 : Set G12) ≤ normalizer (A' : Set G12) := by
  intro h
  have := eq_of_mem_normalizer (h g0_mem_NP)
  rw [map_g0_A'] at this
  exact A_ne_A' this

theorem gl_tables :
    tconj (wordT wER) zT = tmul (tpow zT 2) (tpow xT 0) ∧
      tconj (wordT wER) xT = tmul (tpow zT 2) (tpow xT 2) ∧
    tconj (wordT wES) zT = tmul (tpow zT 2) (tpow xT 0) ∧
      tconj (wordT wES) xT = tmul (tpow zT 0) (tpow xT 1) ∧
    tconj (wordT wEW) zT = tmul (tpow zT 0) (tpow xT 1) ∧
      tconj (wordT wEW) xT = tmul (tpow zT 1) (tpow xT 0) ∧
    tconj (wordT wFR) zT = tmul (tpow zT 2) (tpow yT 0) ∧
      tconj (wordT wFR) yT = tmul (tpow zT 2) (tpow yT 2) ∧
    tconj (wordT wFS) zT = tmul (tpow zT 2) (tpow yT 0) ∧
      tconj (wordT wFS) yT = tmul (tpow zT 0) (tpow yT 1) ∧
    tconj (wordT wFW) zT = tmul (tpow zT 0) (tpow yT 1) ∧
      tconj (wordT wFW) yT = tmul (tpow zT 1) (tpow yT 0) := by
  exact Certificates.certificate9950.2.2.2.1

theorem conj_eq_of_tbl {g u a b : G12} {p r : ℕ} {gT uT aT' bT : List ℕ} (hg : tbl g.1 = gT)
    (hu : tbl u.1 = uT) (ha : tbl a.1 = aT') (hb : tbl b.1 = bT)
    (h : tconj gT uT = tmul (tpow aT' p) (tpow bT r)) : g * u * g⁻¹ = a ^ p * b ^ r := by
  rw [eq_iff_tbl, tblG_conj, tblG_mul, tblG_pow, tblG_pow, hg, hu, ha, hb, h]

theorem automizer_E :
    Nonempty (Automizer E ≃* GL (Fin 2) (ZMod 3)) := by
  have hg : ∀ w, tbl (wE w).1 = wordT w := tbl_wE
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := gl_tables
  exact basisE.nonempty_gl
    (basisE.mem_range_of_conj (g := wE wER) 2 2 0 2 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h1)
      (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h2) (by decide))
    (basisE.mem_range_of_conj (g := wE wES) 2 0 0 1 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h3)
      (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h4) (by decide))
    (basisE.mem_range_of_conj (g := wE wEW) 0 1 1 0 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_x h5)
      (conj_eq_of_tbl (hg _) tbl_x tbl_z tbl_x h6) (by decide))

theorem automizer_F :
    Nonempty (Automizer F ≃* GL (Fin 2) (ZMod 3)) := by
  have hg : ∀ w, tbl (wE w).1 = wordT w := tbl_wE
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6⟩ := gl_tables
  exact basisF.nonempty_gl
    (basisF.mem_range_of_conj (g := wE wFR) 2 2 0 2 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_y h1)
      (conj_eq_of_tbl (hg _) tbl_y tbl_z tbl_y h2) (by decide))
    (basisF.mem_range_of_conj (g := wE wFS) 2 0 0 1 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_y h3)
      (conj_eq_of_tbl (hg _) tbl_y tbl_z tbl_y h4) (by decide))
    (basisF.mem_range_of_conj (g := wE wFW) 0 1 1 0 (conj_eq_of_tbl (hg _) tbl_z tbl_z tbl_y h5)
      (conj_eq_of_tbl (hg _) tbl_y tbl_z tbl_y h6) (by decide))

theorem le_centralizer_sub (B : E9Basis G12) : B.sub ≤ centralizer (B.sub : Set G12) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  exact ((isElementaryAbelian_iff.1 B.isElementaryAbelian).1 h hh g hg)

theorem centralizer_E :
    centralizer (E : Set G12) = E :=
  (Subgroup.eq_of_le_of_card_ge (le_centralizer_sub basisE)
    (card_centralizer_basisE.trans basisE.card.symm).le).symm

theorem centralizer_F :
    centralizer (F : Set G12) = F :=
  (Subgroup.eq_of_le_of_card_ge (le_centralizer_sub basisF)
    (card_centralizer_basisF.trans basisF.card.symm).le).symm

theorem us_tables :
    predN [zT, aT] AT (wordT wU) = true ∧ predN [zT, aT] AT (wordT wS) = true ∧
    (tmul (tcomm (wordT wU) (wordT wS)) aT == tmul aT (tcomm (wordT wU) (wordT wS))) = false := by
  exact Certificates.certificate9950.2.2.2.2.1

theorem card_automizer_A :
    Nat.card (Automizer A) = 6 := by
  have h := ((centralizer (A : Set G12)).subgroupOf
    (normalizer (A : Set G12))).card_eq_card_quotient_mul_card_subgroup
  rw [card_normalizer_basisA,
    Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv,
    card_centralizer_basisA] at h
  change 54 = Nat.card (Automizer A) * 9 at h
  omega

theorem automizer_A :
    Nonempty (Automizer A ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨hu, hs, hne⟩ := us_tables
  have huN : wE wU ∈ normalizer (A : Set G12) :=
    (mem_normalizer_pair_iff tbl_z tbl_a mem_A_iff _).2 (by rw [tbl_wE]; exact hu)
  have hsN : wE wS ∈ normalizer (A : Set G12) :=
    (mem_normalizer_pair_iff tbl_z tbl_a mem_A_iff _).2 (by rw [tbl_wE]; exact hs)
  refine nonempty_mulEquiv_perm_three_of_card_six card_automizer_A
    (QuotientGroup.mk ⟨_, huN⟩) (QuotientGroup.mk ⟨_, hsN⟩) fun h => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
  replace h := (mem_centralizer_pair_iff tbl_z tbl_a _).1 h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have h2 := h.2
  change (tmul (tbl ((wE wU * wE wS)⁻¹ * (wE wS * wE wU)).1) aT ==
    tmul aT (tbl ((wE wU * wE wS)⁻¹ * (wE wS * wE wU)).1)) = true at h2
  rw [tblG_mul, tblG_inv, tblG_mul, tblG_mul, tbl_wE, tbl_wE] at h2
  rw [show tcomm (wordT wU) (wordT wS) = tmul (tinv (tmul (wordT wU) (wordT wS)))
    (tmul (wordT wS) (wordT wU)) from rfl] at hne
  rw [h2] at hne
  exact Bool.noConfusion hne

theorem automizer_A' :
    Nonempty (Automizer A' ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := automizer_A
  exact ⟨(automizerOfEq map_g0_A).symm.trans ((automizerCongr (MulAut.conj g0) A).symm.trans e)⟩

abbrev Na : Subgroup G12 := normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)

theorem psiT_mul (g h : Na) :
    psiT (tbl (g * h : Na).1.1) = psiT (tbl g.1.1) * psiT (tbl h.1.1) :=
  psiT_mul_of_mem g.2 h.2

noncomputable def psiHom :
    Na →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4) where
  toFun g := psiT (tbl g.1.1)
  map_one' := by
    have h := psiT_mul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  map_mul' g h := psiT_mul g h

theorem psiHom_injective :
    Function.Injective psiHom := by
  intro g h hgh
  exact Subtype.ext (psiT_inj_of_mem g.2 h.2 hgh)

abbrev S3A4 : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 4)) :=
  (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 4))

theorem card_S3A4 : Nat.card S3A4 = 72 := by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_top,
    nat_card_alternatingGroup, Nat.card_perm]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem range_psiHom :
    psiHom.range = S3A4 := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    change (psiT (tbl g.1.1)).2 ∈ alternatingGroup (Fin 4)
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_psiT_of_mem g.2
  · rw [card_S3A4, Nat.card_congr (MonoidHom.ofInjective psiHom_injective).toEquiv.symm,
      card_normalizer_xy]

noncomputable def naEquiv :
    Na ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 4) :=
  (MonoidHom.ofInjective psiHom_injective).trans ((MulEquiv.subgroupCongr range_psiHom).trans
    ((Subgroup.prodEquiv _ _).trans (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl _))))

theorem normalizer_zpowers_equiv {u v c : G12} (h : c * u * c⁻¹ = v) :
    Nonempty (normalizer ((zpowers v : Subgroup G12) : Set G12) ≃*
      normalizer ((zpowers u : Subgroup G12) : Set G12)) := by
  have hmap : (zpowers u).map (MulAut.conj c).toMonoidHom = zpowers v := by
    rw [MonoidHom.map_zpowers]
    rw [← h]
    rfl
  exact ⟨(MulEquiv.subgroupCongr (by rw [hmap])).trans (normalizerCongr (MulAut.conj c) _).symm⟩

theorem conj_tables :
    tconj (wordT wC1) aT = tmul zT aT ∧ tconj (wordT wC2) aT = tmul (tmul zT zT) aT ∧
    tinv (tmul (tpow zT 0) (tpow aT 2)) = tmul (tpow zT 0) (tpow aT 1) ∧
    tinv (tmul (tpow zT 1) (tpow aT 2)) = tmul (tpow zT 2) (tpow aT 1) ∧
    tinv (tmul (tpow zT 2) (tpow aT 2)) = tmul (tpow zT 1) (tpow aT 1) := by
  exact Certificates.certificate9950.2.2.2.2.2

theorem na_equiv_one (i : ℕ) (hi : i < 3) :
    Nonempty (normalizer ((zpowers (⁅x, y⁆ ^ i * (x * y) ^ 1) : Subgroup G12) : Set G12) ≃*
      Na) := by
  obtain ⟨h1, h2, -⟩ := conj_tables
  interval_cases i
  · rw [pow_zero, one_mul, pow_one]
    exact ⟨MulEquiv.refl _⟩
  · refine normalizer_zpowers_equiv (c := wE wC1) ?_
    rw [eq_iff_tbl, tblG_conj, tbl_wE, tbl_a, tblG_mul, tblG_pow, tblG_pow, tbl_z, tbl_a, h1]
    rfl
  · refine normalizer_zpowers_equiv (c := wE wC2) ?_
    rw [eq_iff_tbl, tblG_conj, tbl_wE, tbl_a, tblG_mul, tblG_pow, tblG_pow, tbl_z, tbl_a, h2]
    rfl

theorem na_A
    {a : G12} (ha : a ∈ A) (hZ : a ∉ (center P0).map P0.subtype) :
    Nonempty (normalizer ((zpowers a : Subgroup G12) : Set G12) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) := by
  rw [center_P0] at hZ
  obtain ⟨i, j, hi, hj, rfl⟩ := basisA.exists_pow_mul_pow ha
  have hAa : basisA.a = ⁅x, y⁆ := rfl
  rw [hAa, basisA_b] at hZ ⊢
  obtain ⟨-, -, h0, h1, h2⟩ := conj_tables
  have key : ∀ i' < 3, Nonempty (normalizer ((zpowers (⁅x, y⁆ ^ i' * (x * y) ^ 1) :
      Subgroup G12) : Set G12) ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
    fun i' hi' => let ⟨e⟩ := na_equiv_one i' hi'; ⟨e.trans naEquiv⟩
  interval_cases j
  · exfalso
    apply hZ
    rw [pow_zero, mul_one]
    exact (zpowers _).pow_mem (mem_zpowers _) i
  · exact key i hi
  · have hinv : ∀ i' j', (⁅x, y⁆ ^ i * (x * y) ^ 2)⁻¹ = ⁅x, y⁆ ^ i' * (x * y) ^ j' ↔
        tinv (tmul (tpow zT i) (tpow aT 2)) = tmul (tpow zT i') (tpow aT j') := by
      intro i' j'
      rw [eq_iff_tbl, tblG_inv, tblG_mul, tblG_mul, tblG_pow, tblG_pow, tblG_pow, tblG_pow,
        tbl_z, tbl_a]
    rw [← zpowers_inv]
    interval_cases i
    · rw [(hinv 0 1).2 h0]; exact key 0 (by norm_num)
    · rw [(hinv 2 1).2 h1]; exact key 2 (by norm_num)
    · rw [(hinv 1 1).2 h2]; exact key 1 (by norm_num)

theorem na_A'
    {a : G12} (ha : a ∈ A') (hZ : a ∉ (center P0).map P0.subtype) :
    Nonempty (normalizer ((zpowers a : Subgroup G12) : Set G12) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) := by
  rw [← map_g0_A] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have hZ' : a' ∉ (center P0).map P0.subtype := by
    intro h
    apply hZ
    rw [center_P0] at h ⊢
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 h
    change g0 * ⁅x, y⁆ ^ k * g0⁻¹ ∈ zpowers ⁅x, y⁆
    rw [← conj_zpow, g0_conj_z]
    exact (zpowers _).zpow_mem ((zpowers _).pow_mem (mem_zpowers _) 2) k
  obtain ⟨e⟩ := na_A ha' hZ'
  obtain ⟨f⟩ := normalizer_zpowers_equiv (u := a') (c := g0) rfl
  exact ⟨f.trans e⟩

theorem m12SylowData_P0 :
    M12SylowData P0 :=
  ⟨isExtraspecial_P0, card_P0, exponent_P0, isElementaryAbelian_QP, card_QP, nine_ncard,
    nine_props, E, F, A, A', nine_eq, NP_le_NE, NP_le_NF, not_NP_le_NA, not_NP_le_NA',
    ⟨g0, g0_mem_NP, map_g0_A⟩, automizer_E, automizer_F, centralizer_E, centralizer_F,
    automizer_A, automizer_A', fun _ ha hZ => na_A ha hZ, fun _ ha hZ => na_A' ha hZ⟩

end CFSG.RankThree.PartTwo.Toolkit.M12
