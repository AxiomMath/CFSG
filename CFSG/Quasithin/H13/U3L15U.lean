module

public import CFSG.Quasithin.H13.U3L15Gen
public import CFSG.Quasithin.H13.U3Hull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G]

theorem u3_frame_of_irrPlus
    (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G}
    (hH : QTH13 G T L) (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) :
    ∃ z : G, QTU3InternalFrame T L V z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_lieModel_PSU hU3
  obtain ⟨-, ⟨hTL, -⟩, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨hVT, hTV, -, hcomm, hmod⟩ := hVall V hV
  obtain ⟨hVR, hV1, hLV, -, hVlt, hirr, -⟩ := hV
  have hloc := hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate (hVR hv)
  have hVO : V ≤ pCoreOf 2 (L ⊔ T) := fun v hv => (hVf v hv).1
  have hVC : V ≤ centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    fun v hv => mem_centralizer_iff.2 fun k hk => (hVf v hv).2.1 k hk
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => (hVf v hv).2.2
  have hVe : IsElementaryAbelian 2 V := BlueprintB2.isElementaryAbelian_iff.2
    ⟨fun a ha b hb => ((hVf a ha).2.1 b (hVO hb)).symm, hV2⟩
  have hLC : ¬ L ≤ centralizer (V : Set G) := fun h =>
    (lt_irrefl _) (lt_of_lt_of_le hVlt (le_inf le_rfl (le_centralizer_iff.1 h)))
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup hTL).trans (le_centralizer_iff.1 hVC)
  have hK1 := inf_centralizer_subgroupOf_eq_pCore hs hLV hOL hLC
  have hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := by
    obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    rw [Nat.card_congr (e1.trans e2.symm).toEquiv]
    exact card_u33G
  have haut : Nat.card (autOn L V) = 6048 := by
    rw [card_autOn_eq_relIndex hLV, Subgroup.relIndex, hK1, index_eq_card, hcardL]
  have hcase : G2NaturalDerived (V := ↥V) (autOn L V) ⊤ ⊥ 1 ∧
      V ⊓ centralizer (L : Set G) = ⊥ := by
    rcases hmod with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, h'⟩
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 5))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 5)) ≤ 720 := card_alternatingGroup_le (by norm_num)
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 5)) at h1
      omega
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 6))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 6)) ≤ 720 := card_alternatingGroup_le le_rfl
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 6)) at h1
      omega
    · have h1 := card_le_of_realizes h (by
        change Finite ↥(alternatingGroup (Fin 6))
        infer_instance)
      have h2 : Nat.card (alternatingGroup (Fin 6)) ≤ 720 := card_alternatingGroup_le le_rfl
      change Nat.card (autOn L V) ≤ Nat.card (alternatingGroup (Fin 6)) at h1
      omega
    · obtain ⟨K, _, _, hK, hR⟩ := h
      obtain ⟨hfin, h2⟩ := finite_and_card_le_of_GL_three (hK.trans (pow_one 2)) (StatedSL 3 K)
      have h1 := card_le_of_realizes hR hfin
      change Nat.card (autOn L V) ≤ Nat.card (StatedSL 3 K) at h1
      omega
    · exact ⟨h, h'⟩
  obtain ⟨hG2, hCL0⟩ := hcase
  have hV64 : Nat.card V = 64 := by
    obtain ⟨K, _, _, hK, π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hG2
    have hβi : Function.Injective β := by
      rw [injective_iff_map_eq_one]
      intro u hu
      exact Subtype.ext ((mem_bot).1 ((hβk u).1 hu))
    have h1 := Nat.card_congr (Equiv.ofBijective β ⟨hβi, hβs⟩)
    rw [card_top] at h1
    rw [h1]
    exact card_zornQ_of_card_two (hK.trans (pow_one 2))
  have hirr' : ∀ W : Subgroup G, W ≤ V → (∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W) →
      W = ⊥ ∨ W = V := by
    intro W hWV hW
    have hLW : L ≤ normalizer (W : Set G) := fun l hl => mem_normalizer_iff.2 fun w =>
      ⟨fun hw => hW l hl w hw, fun hw => by
        have := hW l⁻¹ (inv_mem hl) _ hw
        simpa [mul_assoc] using this⟩
    rcases hirr W (by rw [hCL0]; exact bot_le) hWV hLW with h | h
    · exact Or.inl (h.trans hCL0)
    · exact Or.inr h
  have hnt : ∃ l ∈ L, ∃ v ∈ V, l * v * l⁻¹ ≠ v := by
    obtain ⟨v, hv, hvn⟩ := IsConcreteLE.exists_of_lt hVlt
    have hvC : v ∉ centralizer (L : Set G) := fun h => hvn ⟨hv, h⟩
    rw [mem_centralizer_iff] at hvC
    push Not at hvC
    obtain ⟨l, hl, hlv⟩ := hvC
    refine ⟨l, hl, v, hv, fun h => hlv ?_⟩
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
    have h := CFSG.pCore_isPGroup (p := 2) (G := ↥L)
    rw [← hK1] at h
    exact h.of_equiv (subgroupOfEquivOfLe inf_le_left)
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTL)
  have hO : CFSG.pCore 2 ↥L ≤ (SteinbergBS.normalizerConjOn V L hLV).ker := by
    rw [ker_normalizerConjOn, hK1]
  obtain ⟨z, hz, hz2⟩ :=
    exists_inf_centralizer_eq_zpowers hU3 hTLs hloc.1 hLV hTV hVT hV1 hV2 hV64 hO hCL0
  exact ⟨z, hTL, hVT, hVe, hV64, hVO, hVC, hLV, hTV, hirr', hnt,
    inf_centralizer_eq_pCoreOf_sup hTsyl hTL hLV hTV hVC hCL, hz, hz2⟩

@[expose] def invMask (m : ℕ) (i : Fin 5) : Bool :=
  (List.range 64).all fun k => !m.testBit k || m.testBit (vapp (u6c i) k)

@[expose] def sameMask (m m' : ℕ) : Bool := (List.range 64).all fun k => m.testBit k == m'.testBit k

theorem invMask_true {m : ℕ} {i : Fin 5}
    (h : ∀ k < 64, m.testBit k = true → m.testBit (vapp (u6c i) k) = true) :
    invMask m i = true := by
  rw [invMask, List.all_eq_true]
  intro k hk
  cases hb : m.testBit k
  · rfl
  · rw [h k (List.mem_range.1 hk) hb]
    rfl

theorem sameMask_spec {m m' : ℕ} (h : sameMask m m' = true) :
    ∀ k < 64, m.testBit k = m'.testBit k := by
  intro k hk
  rw [sameMask, List.all_eq_true] at h
  exact beq_iff_eq.1 (h k (List.mem_range.2 hk))

theorem cert_V2 : ∀ c < 64, (c != 0 && c != 15 && invMask (spanMask3 15 c 0) 0 &&
    invMask (spanMask3 15 c 0) 1 && invMask (spanMask3 15 c 0) 2) = true →
    sameMask (spanMask3 15 c 0) v2mask = true := by
  decide +kernel

theorem cert_V3 : ∀ c < 64, (!v2mask.testBit c && invMask (spanMask3 15 53 c) 0 &&
    invMask (spanMask3 15 53 c) 1 && invMask (spanMask3 15 53 c) 2) = true →
    sameMask (spanMask3 15 53 c) v3mask = true := by
  decide +kernel

theorem cert_card_four : ∀ c < 64, c ≠ 0 → c ≠ 15 →
    ({0, 15, c, 15 ^^^ c} : Finset ℕ).card = 4 := by
  decide +kernel

theorem cert_card_eight : ∀ c < 64, v2mask.testBit c = false →
    ({0, 15, 53, c, 58, 15 ^^^ c, 53 ^^^ c, 58 ^^^ c} : Finset ℕ).card = 8 := by
  decide +kernel

theorem cert_v2bits : ∀ k < 64, v2mask.testBit k = true ↔ k = 0 ∨ k = 15 ∨ k = 53 ∨ k = 58 := by
  decide +kernel

theorem cert_coset : ∀ a < 64, ∀ b < 64, (v3mask.testBit a && v3mask.testBit b &&
    !v2mask.testBit a && !v2mask.testBit b) = true → v2mask.testBit (a ^^^ b) = true := by
  decide +kernel

theorem cert_y : mul6 (u6c 4) (mul6 (u6c 4) (u6c 4)) = id6 ∧ vapp (u6c 4) 15 ≠ 15 := by
  decide +kernel

theorem hasMask_of_card_four {P : Submodule (ZMod 2) W6} (hP : Nat.card P = 4)
    (h15 : vecOf 15 ∈ P) : ∃ c < 64, c ≠ 0 ∧ c ≠ 15 ∧ HasMask P (spanMask3 15 c 0) := by
  classical
  set S := (Finset.range 64).filter (fun c => vecOf c ∈ P) with hS
  have hmem : ∀ c, c ∈ S ↔ c < 64 ∧ vecOf c ∈ P := fun c => by
    rw [hS, Finset.mem_filter, Finset.mem_range]
  have hcard : S.card = 4 := by
    rw [← hP]
    exact (natCard_eq_of_vecOf (fun c hc => ((hmem c).1 hc).1) fun c hc =>
      ⟨fun h => (hmem c).2 ⟨hc, h⟩, fun h => ((hmem c).1 h).2⟩).symm
  obtain ⟨c, hcS, hc0, hc15⟩ : ∃ c ∈ S, c ≠ 0 ∧ c ≠ 15 := by
    by_contra hne
    have hsub : S ⊆ {0, 15} := by
      intro c hc
      by_cases h0 : c = 0
      · rw [h0]
        exact Finset.mem_insert_self _ _
      · by_cases h1 : c = 15
        · rw [h1]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        · exact absurd ⟨c, hc, h0, h1⟩ hne
    have h1 := Finset.card_le_card hsub
    have h2 : ({0, 15} : Finset ℕ).card = 2 := by decide
    omega
  obtain ⟨hc, hcP⟩ := (hmem c).1 hcS
  have hxc : 15 ^^^ c < 64 := Nat.xor_lt_two_pow (n := 6) (by norm_num) hc
  have hxP : vecOf (15 ^^^ c) ∈ P := by
    rw [vecOf_xor]
    exact P.add_mem h15 hcP
  have hsub : ({0, 15, c, 15 ^^^ c} : Finset ℕ) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact (hmem 0).2 ⟨by norm_num, by rw [vecOf_zero]; exact P.zero_mem⟩
    · exact (hmem 15).2 ⟨by norm_num, h15⟩
    · exact hcS
    · exact (hmem _).2 ⟨hxc, hxP⟩
  have heq : S = {0, 15, c, 15 ^^^ c} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, cert_card_four c hc hc0 hc15])).symm
  refine ⟨c, hc, hc0, hc15, fun k hk => ?_⟩
  have hk' : vecOf k ∈ P ↔ k ∈ ({0, 15, c, 15 ^^^ c} : Finset ℕ) := by
    rw [← heq, hmem]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  rw [hk', testBit_spanMask3]
  simp only [Finset.mem_insert, Finset.mem_singleton, Nat.xor_zero]
  tauto

theorem hasMask_of_card_eight {P : Submodule (ZMod 2) W6} (hP : Nat.card P = 8)
    (h2 : V2sub ≤ P) : ∃ c < 64, v2mask.testBit c = false ∧ HasMask P (spanMask3 15 53 c) := by
  classical
  set S := (Finset.range 64).filter (fun c => vecOf c ∈ P) with hS
  have hmem : ∀ c, c ∈ S ↔ c < 64 ∧ vecOf c ∈ P := fun c => by
    rw [hS, Finset.mem_filter, Finset.mem_range]
  have hcard : S.card = 8 := by
    rw [← hP]
    exact (natCard_eq_of_vecOf (fun c hc => ((hmem c).1 hc).1) fun c hc =>
      ⟨fun h => (hmem c).2 ⟨hc, h⟩, fun h => ((hmem c).1 h).2⟩).symm
  have hV2b := cert_v2bits
  have hin2 : ∀ k < 64, v2mask.testBit k = true → k ∈ S := fun k hk hb =>
    (hmem k).2 ⟨hk, h2 ((hasMask_V2sub k hk).2 hb)⟩
  obtain ⟨c, hcS, hc2⟩ : ∃ c ∈ S, v2mask.testBit c = false := by
    by_contra hne
    have hsub : S ⊆ {0, 15, 53, 58} := by
      intro c hc
      have hb : v2mask.testBit c = true := by
        cases h : v2mask.testBit c
        · exact absurd ⟨c, hc, h⟩ hne
        · rfl
      have := (hV2b c ((hmem c).1 hc).1).1 hb
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h1 := Finset.card_le_card hsub
    have h3 : ({0, 15, 53, 58} : Finset ℕ).card = 4 := by decide
    omega
  obtain ⟨hc, hcP⟩ := (hmem c).1 hcS
  have hxor : ∀ a < 64, v2mask.testBit a = true → a ^^^ c ∈ S := by
    intro a ha hb
    refine (hmem _).2 ⟨Nat.xor_lt_two_pow (n := 6) ha hc, ?_⟩
    rw [vecOf_xor]
    exact P.add_mem (h2 ((hasMask_V2sub a ha).2 hb)) hcP
  have hsub : ({0, 15, 53, c, 58, 15 ^^^ c, 53 ^^^ c, 58 ^^^ c} : Finset ℕ) ⊆ S := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hin2 0 (by norm_num) ((hV2b 0 (by norm_num)).2 (Or.inl rfl))
    · exact hin2 15 (by norm_num) ((hV2b 15 (by norm_num)).2 (Or.inr (Or.inl rfl)))
    · exact hin2 53 (by norm_num) ((hV2b 53 (by norm_num)).2 (Or.inr (Or.inr (Or.inl rfl))))
    · exact hcS
    · exact hin2 58 (by norm_num) ((hV2b 58 (by norm_num)).2 (Or.inr (Or.inr (Or.inr rfl))))
    · exact hxor 15 (by norm_num) ((hV2b 15 (by norm_num)).2 (Or.inr (Or.inl rfl)))
    · exact hxor 53 (by norm_num) ((hV2b 53 (by norm_num)).2 (Or.inr (Or.inr (Or.inl rfl))))
    · exact hxor 58 (by norm_num) ((hV2b 58 (by norm_num)).2 (Or.inr (Or.inr (Or.inr rfl))))
  have heq : S = {0, 15, 53, c, 58, 15 ^^^ c, 53 ^^^ c, 58 ^^^ c} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, cert_card_eight c hc hc2])).symm
  refine ⟨c, hc, hc2, fun k hk => ?_⟩
  have hk' : vecOf k ∈ P ↔ k ∈ ({0, 15, 53, c, 58, 15 ^^^ c, 53 ^^^ c, 58 ^^^ c} :
      Finset ℕ) := by
    rw [← heq, hmem]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  have h58 : (15 : ℕ) ^^^ 53 = 58 := by decide
  rw [hk', testBit_spanMask3, h58]
  simp only [Finset.mem_insert, Finset.mem_singleton]

theorem yGL_cube : yGL ^ 3 = 1 := by
  apply Units.ext
  rw [pow_three, Units.val_mul, Units.val_mul, coe_yGL, ← colMat_mul6, ← colMat_mul6,
    cert_y.1, colMat_id6, Units.val_one]

theorem yGL_pow_four : yGL * yGL * (yGL * yGL) = yGL := by
  have h := yGL_cube
  calc yGL * yGL * (yGL * yGL) = yGL ^ 3 * yGL := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = yGL := by rw [h, one_mul]

theorem yGL_pow_two_pow (a : ℕ) : yGL ^ 2 ^ a = yGL ∨ yGL ^ 2 ^ a = yGL * yGL := by
  induction a with
  | zero => left; rw [pow_zero, pow_one]
  | succ a ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h | h
    · right; rw [h, pow_two]
    · left; rw [h, pow_two, yGL_pow_four]

theorem yGL_eq_u6GL : yGL = u6GL 4 := Units.ext (by rw [coe_yGL]; rfl)

theorem xGL_eq_u6GL : xGL = u6GL 3 := Units.ext (by rw [coe_xGL]; rfl)

theorem pow_four_of_fixes_V2
    {j : GL (Fin 6) (ZMod 2)} (hj : j ∈ N6)
    (hfix : ∀ w ∈ V2sub, glLin j w = w) : j ^ 4 = 1 := by
  have h15 : glLin j (vecOf 15) = vecOf 15 := hfix _ (V1sub_le_V2sub vecOf_fifteen_mem_V1sub)
  have hV3 := map_V3sub_of_fix hj h15
  have hdiff : ∀ w ∈ V3sub, glLin j w - w ∈ V2sub := by
    intro w hw
    have hjw : glLin j w ∈ V3sub := by
      rw [← hV3]
      exact Submodule.mem_map_of_mem hw
    by_cases hw2 : w ∈ V2sub
    · rw [hfix w hw2, sub_self]
      exact zero_mem _
    · have hjw2 : glLin j w ∉ V2sub := by
        intro h
        apply hw2
        have h1 := hfix _ h
        have h2 : glLin j w = w := (glLin j).injective h1
        rwa [h2] at h
      obtain ⟨a, ha, rfl⟩ := exists_vecOf w
      obtain ⟨b, hb, hbe⟩ := exists_vecOf (glLin j (vecOf a))
      rw [← hbe] at hjw hjw2 ⊢
      have hc := cert_coset a ha b hb (by
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨⟨⟨(hasMask_V3sub' a ha).1 hw, (hasMask_V3sub' b hb).1 hjw⟩, ?_⟩, ?_⟩
        · cases h : v2mask.testBit a
          · rfl
          · exact absurd ((hasMask_V2sub a ha).2 h) hw2
        · cases h : v2mask.testBit b
          · rfl
          · exact absurd ((hasMask_V2sub b hb).2 h) hjw2)
      rw [W6_sub_eq_add, ← vecOf_xor, Nat.xor_comm]
      exact (hasMask_V2sub _ (Nat.xor_lt_two_pow (n := 6) ha hb)).2 hc
  have hj2 : ∀ w ∈ V3sub, glLin (j * j) w = w := by
    intro w hw
    set u := glLin j w - w with hu'
    have hu := hdiff w hw
    have hjw : glLin j w = w + u := by rw [hu']; abel
    have hju : glLin j u = u := hfix u hu
    calc glLin (j * j) w = glLin j (glLin j w) := by rw [map_mul]; rfl
      _ = glLin j (w + u) := by rw [hjw]
      _ = glLin j w + glLin j u := map_add _ _ _
      _ = w + u + u := by rw [hjw, hju]
      _ = w := by rw [add_assoc, W6_add_self, add_zero]
  have hsq := sq_eq_one_of_fixes (mul_mem hj hj) hj2
  calc j ^ 4 = j * j * (j * j) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := hsq

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem rho_eq_of_spec
    (S : HullSetting G T L V z)
    {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k) :
    S.rho ⟨n, hn⟩ = k :=
  glLin.injective (by rw [← S.rho_spec, hk])

theorem rho_L_mem
    (S : HullSetting G T L V z)
    {l : G} (hl : l ∈ L) : S.rho ⟨l, S.hLV hl⟩ ∈ J6 := by
  obtain ⟨j, hj, hjl⟩ := S.hL l hl
  rw [S.rho_eq_of_spec _ hjl]
  exact hj

theorem rho_T_mem
    (S : HullSetting G T L V z)
    {t : G} (ht : t ∈ T) : S.rho ⟨t, S.hTV ht⟩ ∈ S0 := by
  obtain ⟨s, hs, hst⟩ := S.hT t ht
  rw [S.rho_eq_of_spec _ hst]
  exact hs

@[expose] noncomputable def tauL
    (S : HullSetting G T L V z)
    : ↥L →* ↥J6 :=
  (S.rho.comp (Subgroup.inclusion S.hLV)).codRestrict J6 fun l => S.rho_L_mem l.2

theorem tauL_surjective
    (S : HullSetting G T L V z)
    : Function.Surjective S.tauL := by
  rintro ⟨j, hj⟩
  obtain ⟨l, hl, hlj⟩ := S.hLs j hj
  exact ⟨⟨l, hl⟩, Subtype.ext (S.rho_eq_of_spec _ hlj)⟩

theorem exists_T_rho
    (S : HullSetting G T L V z)
    {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ rhoT) :
    ∃ t ∈ T ⊓ L, ∃ ht : t ∈ normalizer (V : Set G), S.rho ⟨t, ht⟩ = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc := S.hH.faithful.1
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := ⟨le_sup_right, hloc.1, hloc.2.2.1⟩
  have hTLs : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer S.hTL)
  have hP1 : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTLs.2.1.of_equiv (subgroupOfEquivOfLe hTLs.1).symm
  let P : Sylow 2 ↥L := hP1.toSylow hTLs.2.2
  let Q : Sylow 2 ↥J6 := P.mapSurjective S.tauL_surjective
  have hQS : (Q : Subgroup ↥J6) ≤ S0.subgroupOf J6 := by
    intro q hq
    rw [Sylow.coe_mapSurjective] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [mem_subgroupOf]
    have hpT : (p : G) ∈ T := (mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)).1
    exact S.rho_T_mem hpT
  have hQcard : Nat.card (Q : Subgroup ↥J6) = 32 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have h1 := Subgroup.card_mul_index (Q : Subgroup ↥J6)
    rw [hk, card_J6] at h1
    have h2 := Q.not_dvd_index
    have hk13 : k < 13 := by
      by_contra h
      have h3 : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
      have h4 : 2 ^ k ≤ 6048 := Nat.le_of_dvd (by norm_num) ⟨_, h1.symm⟩
      norm_num at h3
      omega
    rw [hk]
    interval_cases k <;> omega
  have hS0card : Nat.card (S0.subgroupOf J6) ≤ 32 := by
    have hS0 : IsPGroup 2 S0 := IsPGroup.of_card (n := 6) (by rw [card_S0]; norm_num)
    have hS0J : IsPGroup 2 (S0.subgroupOf J6) := hS0.comap_subtype
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS0J
    have hd := Subgroup.card_subgroup_dvd_card (S0.subgroupOf J6)
    rw [hk, card_J6] at hd
    have hk13 : k < 13 := by
      by_contra h
      have h3 : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
      have h4 : 2 ^ k ≤ 6048 := Nat.le_of_dvd (by norm_num) hd
      norm_num at h3
      omega
    rw [hk]
    interval_cases k <;> omega
  have hQeq : (Q : Subgroup ↥J6) = S0.subgroupOf J6 :=
    Subgroup.eq_of_le_of_card_ge hQS (by omega)
  have hgJ : g ∈ J6 := rhoT_le_J6 hg
  have hgQ : (⟨g, hgJ⟩ : ↥J6) ∈ (Q : Subgroup ↥J6) := by
    rw [hQeq, mem_subgroupOf]
    exact mem_sup_right hg
  rw [Sylow.coe_mapSurjective] at hgQ
  obtain ⟨p, hp, hpg⟩ := hgQ
  have hp' := mem_subgroupOf.1 (show p ∈ (T ⊓ L).subgroupOf L from hp)
  exact ⟨p, hp', S.hLV p.2, congrArg Subtype.val hpg⟩

omit [Finite G] [IsElementaryAbelian 2 V] in
theorem u6GL_mem_rhoT
    {i : Fin 5} (hi : i ∈ ([0, 1, 2] : List (Fin 5))) : u6GL i ∈ rhoT := by
  obtain ⟨ha, hb, hs, -, -⟩ := rho6_abs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨_, u33Data.a_mem_T, ha⟩
  · exact ⟨_, u33Data.b_mem_T, hb⟩
  · exact ⟨_, u33Data.s_mem_T, hs⟩

theorem invMask_of_T
    (S : HullSetting G T L V z)
    {X : Subgroup G} (hT : T ≤ normalizer (X : Set G)) {m : ℕ}
    (hm : HasMask (subSpace S.Φ X) m) {i : Fin 5} (hi : i ∈ ([0, 1, 2] : List (Fin 5))) :
    invMask m i = true := by
  obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT hi)
  refine invMask_true fun k hk hbit => ?_
  have h1 := subSpace_invariant (Φ := S.Φ) ht (S.rho_spec ⟨t, ht⟩) (hT htTL.1) (vecOf k)
    ((hm k hk).2 hbit)
  rw [hrho, glLin_vecOf rfl] at h1
  exact (hm _ (vapp_u6c_lt i k)).1 h1

theorem V2_eq
    (S : HullSetting G T L V z)
    {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) : V₂ = pullSub S.Φ V2sub := by
  obtain ⟨h1, h2V, hT2, hc2⟩ := hV2
  set P := subSpace S.Φ V₂ with hP
  have hPV : pullSub S.Φ P = V₂ := pullSub_subSpace h2V
  have hcP : Nat.card P = 4 := by rw [← card_pullSub (Φ := S.Φ) P, hPV, hc2]
  have hz2 : z ∈ V₂ := h1 (by rw [fsuV1_eq S.hF, S.hVz]; exact mem_zpowers z)
  have h15 : vecOf 15 ∈ P := by
    rw [← S.phi_z]
    exact (mem_subSpace S.hzV).2 hz2
  obtain ⟨c, hc, hc0, hc15, hm⟩ := hasMask_of_card_four hcP h15
  have hcert := cert_V2 c hc (by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨⟨⟨⟨hc0, hc15⟩, S.invMask_of_T hT2 hm (by simp)⟩, S.invMask_of_T hT2 hm (by simp)⟩,
      S.invMask_of_T hT2 hm (by simp)⟩)
  have hm2 : HasMask P v2mask := fun k hk => by rw [hm k hk, sameMask_spec hcert k hk]
  rw [← hPV, eq_of_hasMask hm2 hasMask_V2sub]

theorem V3_eq
    (S : HullSetting G T L V z)
    {V₃ : Subgroup G} (h23 : pullSub S.Φ V2sub ≤ V₃) (h3V : V₃ ≤ V)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hc3 : Nat.card V₃ = 8) : V₃ = pullSub S.Φ V3sub := by
  set P := subSpace S.Φ V₃ with hP
  have hPV : pullSub S.Φ P = V₃ := pullSub_subSpace h3V
  have hcP : Nat.card P = 8 := by rw [← card_pullSub (Φ := S.Φ) P, hPV, hc3]
  have h2P : V2sub ≤ P := by
    rw [← pullSub_le_iff (Φ := S.Φ), hPV]
    exact h23
  obtain ⟨c, hc, hc2, hm⟩ := hasMask_of_card_eight hcP h2P
  have hcert := cert_V3 c hc (by
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨⟨hc2, S.invMask_of_T hT3 hm (by simp)⟩, S.invMask_of_T hT3 hm (by simp)⟩,
      S.invMask_of_T hT3 hm (by simp)⟩)
  have hm3 : HasMask P v3mask := fun k hk => by rw [hm k hk, sameMask_spec hcert k hk]
  rw [← hPV, eq_of_hasMask hm3 hasMask_V3sub']

theorem isPGroup_CL
    (S : HullSetting G T L V z)
    : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le S.inf_centralizer_le

theorem rho_pow
    (S : HullSetting G T L V z)
    {n : G} (hn : n ∈ normalizer (V : Set G)) (k : ℕ) :
    S.rho ⟨n ^ k, pow_mem hn k⟩ = S.rho ⟨n, hn⟩ ^ k := by
  rw [← map_pow]
  rfl

theorem exists_X_elem
    (S : HullSetting G T L V z)
    : ∃ x ∈ L₁Of L (pullSub S.Φ V2sub), x ^ 3 = 1 ∧
    x ∉ centralizer (pullSub S.Φ V2sub : Set G) ∧ ∃ hx : x ∈ normalizer (V : Set G),
      S.rho ⟨x, hx⟩ = yGL ∨ S.rho ⟨x, hx⟩ = yGL * yGL := by
  obtain ⟨l, hl, hlN, hspec⟩ := S.exists_lift yGL_mem
  have hrho : S.rho ⟨l, hlN⟩ = yGL := S.rho_eq_of_spec hlN hspec
  have hlV2 : l ∈ normalizer (pullSub S.Φ V2sub : Set G) :=
    mem_normalizer_pullSub hlN hspec map_V2sub_yGL
  have hl3 : l ^ 3 ∈ centralizer (V : Set G) := by
    rw [mem_centralizer_V_iff (pow_mem hlN 3) (S.rho_spec ⟨l ^ 3, pow_mem hlN 3⟩), S.rho_pow hlN,
      hrho]
    exact yGL_cube
  have hlc : l ∉ centralizer (pullSub S.Φ V2sub : Set G) := by
    rw [mem_centralizer_pullSub_iff hlN hspec]
    intro h
    have h1 := h (vecOf 15) (V1sub_le_V2sub vecOf_fifteen_mem_V1sub)
    rw [glLin_vecOf coe_yGL] at h1
    exact cert_y.2 (vecOf_injective (vapp_u6c_lt 4 15) (by norm_num) h1)
  obtain ⟨e, hxX, hx3, hxc⟩ :=
    exists_mem_L₁Of_cube hl hlV2 hl3 hlc (pullSub_le _) S.isPGroup_CL
  refine ⟨l ^ 2 ^ e, hxX, hx3, hxc, pow_mem hlN _, ?_⟩
  rw [S.rho_pow hlN, hrho]
  exact yGL_pow_two_pow e

theorem isPGroup_CL_V2
    (S : HullSetting G T L V z)
    : IsPGroup 2 ↥(L ⊓ centralizer (pullSub S.Φ V2sub : Set G)) := by
  refine isPGroup_two_of_forall' fun x hx => ?_
  have hxN := S.hLV hx.1
  have hfix := (mem_centralizer_pullSub_iff hxN (S.rho_spec ⟨x, hxN⟩) V2sub).1 hx.2
  have h4 := pow_four_of_fixes_V2 (S.rho_mem_N6 ⟨x, hxN⟩) hfix
  have hx4 : x ^ 4 ∈ L ⊓ centralizer (V : Set G) := by
    refine mem_inf.2 ⟨pow_mem hx.1 4, ?_⟩
    rw [mem_centralizer_V_iff (pow_mem hxN 4) (S.rho_spec ⟨x ^ 4, pow_mem hxN 4⟩),
      S.rho_pow hxN, h4]
  obtain ⟨k, hk⟩ := exists_two_pow_eq_one S.isPGroup_CL hx4
  exact ⟨k + 2, by rw [show 2 ^ (k + 2) = 4 * 2 ^ k by ring, pow_mul, hk]⟩

theorem o2Z_le_centralizer
    (S : HullSetting G T L V z)
    : A6.o2Z L ≤ centralizer (V : Set G) := by
  have hs := S.isSimple_quot
  have hcen : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
    · exact h
    · exfalso
      obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel S.hU3
      obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
      obtain ⟨x, y, hxy⟩ := u33Pres_nonabelian
      apply hxy
      have hc' : ∀ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b = b * a := fun a b =>
        (mem_center_iff.1 (h ▸ mem_top a) b).symm
      have := hc' ((e1.trans e2.symm).symm x) ((e1.trans e2.symm).symm y)
      simpa using congrArg (e1.trans e2.symm) this
  intro y hy
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) y') = 1 := by
    have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y' ∈ Subgroup.center _ := hy'
    rw [hcen] at this
    exact (mem_bot).1 this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (S.pCoreOf_L_le (coe_mem_pCoreOf_iff.2 h1)).2

theorem gen
    (S : HullSetting G T L V z)
    {V₃ X : Subgroup G} (hV3 : V₃ = pullSub S.Φ V3sub)
    (hT3 : T ≤ normalizer (V₃ : Set G)) (hXL : X ≤ L)
    (hyX : ∃ x ∈ X, ∃ hx : x ∈ normalizer (V : Set G),
      S.rho ⟨x, hx⟩ = yGL ∨ S.rho ⟨x, hx⟩ = yGL * yGL) :
    autOn (X ⊔ L ⊓ normalizer (V₃ : Set G)) V = autOn L V := by
  set A := X ⊔ L ⊓ normalizer (V₃ : Set G) with hA
  have hAL : A ≤ L := sup_le hXL inf_le_left
  refine le_antisymm (A4.autOn_mono hAL) ?_
  set Ab : Subgroup (GL (Fin 6) (ZMod 2)) := (A.subgroupOf (normalizer (V : Set G))).map S.rho
  have hmem : ∀ {a : G} (ha : a ∈ A) (haN : a ∈ normalizer (V : Set G)),
      S.rho ⟨a, haN⟩ ∈ Ab := fun ha haN => mem_map_of_mem _ (mem_subgroupOf.2 ha)
  have h012 : ∀ i ∈ ([0, 1, 2] : List (Fin 5)), u6GL i ∈ Ab := by
    intro i hi
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho (u6GL_mem_rhoT hi)
    rw [← hrho]
    exact hmem (mem_sup_right ⟨htTL.2, hT3 htTL.1⟩) ht
  have h3 : u6GL 3 ∈ Ab := by
    have hl1 : S.rho ⟨S.l₁, S.l₁_N⟩ = xGL := S.rho_eq_of_spec _ S.l₁_spec
    have hl1V3 : S.l₁ ∈ normalizer (V₃ : Set G) := by
      rw [hV3]
      exact mem_normalizer_pullSub S.l₁_N S.l₁_spec (map_V3sub_of_fix (J6_le_N6 xGL_mem) xGL_fix)
    rw [← xGL_eq_u6GL, ← hl1]
    exact hmem (mem_sup_right ⟨S.l₁_mem, hl1V3⟩) S.l₁_N
  have h4 : u6GL 4 ∈ Ab := by
    obtain ⟨x, hxX, hx, hrho⟩ := hyX
    have hx' := hmem (mem_sup_left hxX) hx
    rw [← yGL_eq_u6GL]
    rcases hrho with h | h
    · rw [← h]
      exact hx'
    · rw [h] at hx'
      rw [← yGL_pow_four]
      exact mul_mem hx' hx'
  have hJ : J6 ≤ Ab := by
    rintro _ ⟨g, rfl⟩
    have hle : (⊤ : Subgroup U33G) ≤ Ab.comap rho6 := by
      rw [← u33Data.gen, closure_le]
      obtain ⟨ha, hb, hs, hx, hy⟩ := rho6_abs
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · show rho6 u33Data.a ∈ Ab
        rw [ha]
        exact h012 0 (by simp)
      · show rho6 u33Data.b ∈ Ab
        rw [hb]
        exact h012 1 (by simp)
      · show rho6 u33Data.s ∈ Ab
        rw [hs]
        exact h012 2 (by simp)
      · show rho6 u33Data.x ∈ Ab
        rw [hx]
        exact h3
      · show rho6 u33Data.y ∈ Ab
        rw [hy]
        exact h4
    exact hle (mem_top g)
  intro f hf
  obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := mem_map.1 hf
  have hlL : l ∈ L := mem_subgroupOf.1 hl
  have hlJ : S.rho ⟨l, hlN⟩ ∈ Ab := hJ (S.rho_L_mem hlL)
  obtain ⟨⟨a, haN⟩, ha, hae⟩ := mem_map.1 hlJ
  have haA : a ∈ A := mem_subgroupOf.1 ha
  have h1 : S.rho ((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, hlN⟩) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  have h2 : (((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, hlN⟩ :
      normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) :=
    (mem_centralizer_V_iff _ (S.rho_spec _)).2 h1
  have h3 := A1b.conjAct_eq_one_iff.2 h2
  rw [map_mul, map_inv, inv_mul_eq_one] at h3
  rw [← h3]
  exact mem_map_of_mem _ (mem_subgroupOf.2 haA)

theorem core15
    (S : HullSetting G T L V z)
    (h13314 : A6.Stmt13_3_14) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    Core15 G T L V V₂ (L₁Of L V₂) := by
  have hirr := u3_isIrrPlusIn S.h1332 S.hH S.hU3 S.hF
  have hzv := inf_centralizer_L_eq_bot S.hF
  have hV2e := S.V2_eq hV2
  obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂ (L := L) S.hTL hV2.2.2.1
  obtain ⟨x, hxX, hx3, hxc, hx, hrho⟩ := S.exists_X_elem
  rw [← hV2e] at hxX hxc
  refine core15_of S.h1332 S.hH hirr hzv hV2
    (h13314 G T L V V₂ S.hH hirr hzv hV2 (not_iso_a5_of_U3 S.hU3 S.hF)) hXL hXN hXT
    hXres ⟨x, hxX, hx3, hxc⟩ ?_ ?_ ?_
  · rw [hV2e]
    exact S.isPGroup_CL_V2.to_le (inf_le_inf_right _ (hV2e ▸ hXL))
  · intro h
    apply hxc
    exact Subgroup.centralizer_le hV2.2.1 (S.o2Z_le_centralizer (h hxX))
  · intro V₃ h23 h3V hT3 hc3
    exact S.gen (S.V3_eq (hV2e ▸ h23) h3V hT3 hc3) hT3 hXL ⟨x, hxX, hx, hrho⟩

end HullSetting

theorem u3Stmt13_3_15_of_U3
    (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) [Finite G]
    {T L V V₂ X I₂ : Subgroup G} (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V) (hV2 : A6.IsV2 T V V₂)
    (hX : X = L₁Of L V₂)
    (hI₂ : I₂ = conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) :
    normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (A6.g1 T V) ∧
      I₂ ⊓ centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (normalizer (V₂ : Set G)) ∧
      CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          centralizer (V₃ : Set G) ≤ normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V) := by
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  subst hX
  exact (S.core15 h13314 hV2).stmt hI₂ fun hP => absurd hU3 hP

end CFSG.Quasithin.H13.U3
