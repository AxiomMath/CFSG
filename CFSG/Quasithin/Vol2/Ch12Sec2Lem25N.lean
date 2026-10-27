module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem25M
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Q
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Excl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem25

variable {G : Type} [Group G]

theorem card_GL_six :
    Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) = 20158709760 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Matrix.card_GL_field (𝔽 := ZMod 2) _).trans ?_
  rw [ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_GL_seven :
    Nat.card (Matrix.GeneralLinearGroup (Fin 7) (ZMod 2)) = 163849992929280 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Matrix.card_GL_field (𝔽 := ZMod 2) _).trans ?_
  rw [ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_GL_eight :
    Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) = 5348063769211699200 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Matrix.card_GL_field (𝔽 := ZMod 2) _).trans ?_
  rw [ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_GL_nine :
    Nat.card (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)) = 699612310033197642547200 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Matrix.card_GL_field (𝔽 := ZMod 2) _).trans ?_
  rw [ZMod.card]
  simp [Fin.prod_univ_succ]

theorem card_U [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ}
    (hC : Config12_2_24 T L V H P U I h n p) : Nat.card U = 2 ^ (n - 1) * 2 ^ (n - 1) := by
  have hA := card_inf_V hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hhH, -, -, -, hUd, hUi, hUe, -, -, -, -, -, -, -, hHU,
    -⟩ := hC
  have hhU : h ∈ Subgroup.normalizer (U : Set G) := hHU hhH
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB : Nat.card ↥(U ⊓ CFSG.conjugate V h) = Nat.card ↥(U ⊓ V) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp hhU x).mp x.2.1,
          BlueprintB2.mem_conjugate_iff.mp x.2.2⟩
        invFun := fun y => ⟨h⁻¹ * y * h, ?_, ?_⟩
        left_inv := fun x => by apply Subtype.ext; simp only; group
        right_inv := fun y => by apply Subtype.ext; simp only; group }
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhU) y).mp y.2.1
      simpa using this
    · refine BlueprintB2.mem_conjugate_iff.mpr ?_
      have : h * (h⁻¹ * (y : G) * h) * h⁻¹ = y := by group
      rw [this]
      exact y.2.2
  have hKU : U ⊓ CFSG.conjugate V h ≤ Subgroup.centralizer ((U ⊓ V : Subgroup G) : Set G) :=
    fun b hb => Subgroup.mem_centralizer_iff.mpr fun a ha => hUab a ha.1 b hb.1
  rw [hUd, card_sup_eq_mul hKU hUi, hB, hA]

theorem card_RR
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) :
    Nat.card (RR T U) = 2 ^ (2 * n - 2) ∨ Nat.card (RR T U) = 2 ^ (2 * n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := card_U hC
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, hc3, hc4, -, -, -, -, hc9, -⟩ := hstar
  have hn : n = 3 ∨ n = 4 ∨ n = 5 := hC.2.2.1
  have hKU : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (U : Set G) := by
    intro c hc
    have : c ∈ T ⊓ Subgroup.centralizer (U : Set G) := hc3 ▸ Subgroup.mem_sup_right hc
    exact this.2
  have hUK : U ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, -, hxL⟩
    have : x ∈ U ⊓ Subgroup.centralizer (L : Set G) := ⟨hxU, hxL⟩
    rw [hc4] at this
    exact this
  have hR : Nat.card (RR T U) = Nat.card U * Nat.card ↥(T ⊓ Subgroup.centralizer (L : Set G)) := by
    show Nat.card ↥(T ⊓ Subgroup.centralizer (U : Set G)) = _
    rw [hc3, card_sup_eq_mul hKU hUK]
  have h2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (L : Set G)) := hH.sylow.1.to_le inf_le_left
  obtain ⟨j, hj⟩ := h2.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra hj1
    have : 2 ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have e1 : 2 ^ (n - 1) * 2 ^ (n - 1) = 2 ^ (2 * n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hR, hU, e1, hj]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj1 with rfl | rfl
  · left
    simp
  · right
    rw [pow_one, ← pow_succ]
    congr 1
    rcases hn with rfl | rfl | rfl <;> omega

theorem card_Kbar_dvd
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) {K : Subgroup G} (hKN : K ≤ NR T U) :
    ∃ k : ℕ, (k = 2 * n - 2 ∨ k = 2 * n - 1) ∧
      Nat.card ↥(modO2Image (NR T U) K) ∣
        Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstar := lem12225Star_of h331 h1222 h323 h1216 h1220 G T L V H P U I h n p hH hNE hC
  obtain ⟨-, -, -, -, -, -, -, hc8, -⟩ := hstar
  obtain ⟨k, hk, hRk⟩ : ∃ k, (k = 2 * n - 2 ∨ k = 2 * n - 1) ∧ Nat.card (RR T U) = 2 ^ k := by
    rcases card_RR h331 h1222 h323 h1216 h1220 hH hNE hC with h1 | h1
    · exact ⟨_, Or.inl rfl, h1⟩
    · exact ⟨_, Or.inr rfl, h1⟩
  refine ⟨k, hk, ?_⟩
  have hRab : ∀ x ∈ RR T U, ∀ y ∈ RR T U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc8.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨e⟩ := Lem24.nonempty_coords hRab hc8.2 hRk
  have hAut : Nat.card (MulAut ↥(RR T U)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  have hRp : IsPGroup 2 (RR T U) := hH.sylow.1.to_le inf_le_left
  set α := A4.actionOn (RR T U) K hKN with hα
  set N := NR T U with hNdef
  let ι : ↥K ≃* ↥(K.subgroupOf N) := (Subgroup.subgroupOfEquivOfLe hKN).symm
  set σ := (QuotientGroup.mk' (CFSG.pCore 2 ↥N)).subgroupMap (K.subgroupOf N) with hσ
  let β : ↥K →* ↥(modO2Image N K) := σ.comp ι.toMonoidHom
  have hβs : Function.Surjective β := (MonoidHom.subgroupMap_surjective _ _).comp ι.surjective
  have hle : α.ker ≤ β.ker := by
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer (RR T U : Set G) :=
      (A4.actionOn_eq_one_iff hKN x).mp hx
    have hxR : (x : G) ∈ RR T U := centralizer_R_le hH hC hxC
    have hxO : (x : G) ∈ pCoreOf 2 N := LieType.BorelTits.le_pCoreOf_normalizer 2 _ hRp hxR
    rw [A7.pCoreOf_eq_map_cfsgPCore] at hxO
    obtain ⟨y, hy, hyx⟩ := hxO
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pCore 2 ↥N) ((ι x : ↥(K.subgroupOf N)) : ↥N) = 1
    have e1 : ((ι x : ↥(K.subgroupOf N)) : ↥N) = y := Subtype.ext hyx.symm
    rw [e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hy
  have h1 : Nat.card ↥(modO2Image N K) ∣ Nat.card α.range := by
    have e1 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv
    have e2 := Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv
    have c1 := β.ker.card_eq_card_quotient_mul_card_subgroup
    have c2 := α.ker.card_eq_card_quotient_mul_card_subgroup
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
    rw [e1] at c1
    rw [e2] at c2
    refine ⟨c, ?_⟩
    have hpos : 0 < Nat.card α.ker := Nat.card_pos
    have h2 : Nat.card α.range * Nat.card α.ker =
        Nat.card ↥(modO2Image N K) * c * Nat.card α.ker := by
      rw [← c2, c1, hc]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  exact h1.trans ((Subgroup.card_subgroup_dvd_card α.range).trans hAut.dvd)

theorem not_dvd_GL {n k q : ℕ} (hk : k = 2 * n - 2 ∨ k = 2 * n - 1)
    (hq : (n = 4 ∧ (q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 23 ∨ q = 25 ∨ q = 343)) ∨
      (n = 5 ∧ (q = 11 ∨ q = 23))) :
    ¬ q ∣ Nat.card (Matrix.GeneralLinearGroup (Fin k) (ZMod 2)) := by
  rcases hq with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> rcases hk with rfl | rfl
  · rw [show 2 * 4 - 2 = 6 by norm_num, card_GL_six]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rw [show 2 * 4 - 1 = 7 by norm_num, card_GL_seven]
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rw [show 2 * 5 - 2 = 8 by norm_num, card_GL_eight]
    rcases hq with rfl | rfl <;> norm_num
  · rw [show 2 * 5 - 1 = 9 by norm_num, card_GL_nine]
    rcases hq with rfl | rfl <;> norm_num

theorem dvd_card_of_mulEquiv {X Z : Type*} [Group X] [Group Z] (e : X ≃* Z) {q : ℕ}
    (h : q ∣ Nat.card Z) : q ∣ Nat.card X := by
  rwa [Nat.card_congr e.toEquiv]

theorem seven_cube_dvd_card {X : Type} [Group X] [Finite X] {s : Bool}
    (h : IsPSLEps3 s 7 1 X ∨ IsSLEps3 s 7 X) : 343 ∣ Nat.card X := by
  cases s with
  | true =>
    rcases h with h | h
    · have hc := Vol2.Ch11.SecA.card_of_isPSL (by norm_num) (h : IsPSL 3 7 1 X)
      rw [hc]
      decide
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (h : IsSL3 7 X)
      rw [Nat.card_congr e.toEquiv]
      have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
        (by norm_num)
      rw [hK] at hc
      have hdvd : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ∣ Nat.card ↥(StatedSL 3 K) :=
        Subgroup.card_quotient_dvd_card _
      refine dvd_trans ?_ hdvd
      rw [hc]
      decide
  | false =>
    rcases h with h | h
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := (h : IsPSU 3 7 1 X)
      rw [Nat.card_congr e.toEquiv]
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (by norm_num) le_rfl hK
        (by norm_num)]
      decide
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := (h : IsSU3 7 X)
      rw [Nat.card_congr e.toEquiv]
      have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 7)
        (f := 1) (n := 3) (by norm_num) le_rfl (by rw [hK]; norm_num) (by norm_num)
      have hdvd : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 (7 ^ 1) K)) ∣ Nat.card ↥(StatedSU 3 7 K) :=
        Subgroup.card_quotient_dvd_card _
      refine dvd_trans ?_ hdvd
      rw [hc]
      decide

theorem case_cut
    (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20)
    [Finite G] {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hH : Hyp1223 G T L V)
    (hNE : NoEscape12_2_13 L V) (hC : Config12_2_24 T L V H P U I h n p) (hn3 : n ≠ 3)
    {K : Subgroup G} (hKN : K ≤ NR T U)
    (hcase : A312Case (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K)) :
    A312C4 (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K) ∨
      A312C5 (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K) ∨
      A312C6 (modO2Image (NR T U) (YY L U V)) (modO2Image (NR T U) K) := by
  have hD := data_Ybar h331 h1222 h323 h1216 h1220 hH hNE hC hn3
  obtain ⟨k, hk, hdvd⟩ := card_Kbar_dvd h331 h1222 h323 h1216 h1220 hH hNE hC hKN
  have hn : n = 4 ∨ n = 5 := by
    obtain ⟨-, -, hn, -⟩ := hC
    omega
  have hno : ∀ q, ((n = 4 ∧ (q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 23 ∨ q = 25 ∨ q = 343)) ∨
      (n = 5 ∧ (q = 11 ∨ q = 23))) →
      ¬ q ∣ Nat.card ↥(modO2Image (NR T U) K) := fun q hq hq' =>
    not_dvd_GL hk hq (hq'.trans hdvd)
  have h168 : Nat.card (Matrix.SpecialLinearGroup (Fin (n - 1)) (ZMod 2)) = 168 → n = 4 :=
    fun hc => by have := hD.k_eq_three hc; omega
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.not_c2 h).elim
  · exact (hD.not_c3 h).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (hD.not_c7 h).elim
  ·
    exfalso
    rcases h with ⟨q, hq, hq3, hB, hK⟩ | ⟨hB, -⟩
    · have h2 := Vol2.Ch11.SecA.two_mul_card_of_isPSL_two hq (by omega) hB
      obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, hc⟩ := eq_seven_of_card hD.c_eq hq hq3 (b := a + 1)
        (by rw [← h2, ha, pow_succ]; ring)
      have hn4 := h168 hc
      have hcard := Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hK
      norm_num at hcard
      exact hno 25 (Or.inl ⟨hn4, by norm_num⟩) (by rw [hcard]; norm_num)
    · exact hD.false_of_card (card_alt_five hB) (by norm_num)
  ·
    exfalso
    rcases h with ⟨s, q, hq, hq3, hB, hK⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · obtain ⟨a, ha⟩ := hD.card
      obtain ⟨rfl, hc⟩ := eq_seven_of_card hD.c_eq hq hq3
        ((Vol2.Ch11.SecA.card_of_isSL2 hq hB).symm.trans ha)
      have hn4 := h168 hc
      exact hno 343 (Or.inl ⟨hn4, by norm_num⟩) (seven_cube_dvd_card hK)
    · exact hD.false_of_card (card_alt_six hB) (by norm_num)
    · exact hD.false_of_card (card_hat_six hB) (by norm_num)
  · exact (hD.not_c10 h).elim
  · exact (hD.not_c11 h).elim
  · exact (hD.not_c12 h).elim
  ·
    exfalso
    obtain ⟨-, ⟨e⟩⟩ := h
    exact hno 23 (by omega) (dvd_card_of_mulEquiv e L34Orders.twentyThree_dvd_card_M23)
  ·
    exfalso
    obtain ⟨-, ⟨e⟩⟩ := h
    exact hno 23 (by omega) (dvd_card_of_mulEquiv e L34Orders.twentyThree_dvd_card_M24)
  · exact (hD.not_c15 h).elim
  · exact (hD.not_c16 h).elim
  ·
    exfalso
    obtain ⟨⟨e⟩, -⟩ := h
    exact hno 11 (by omega) (dvd_card_of_mulEquiv e (by
      show 11 ∣ Nat.card NativeSporadic.J4
      rw [CFSG.Sporadic.J4.card_J4]; norm_num))
  ·
    exfalso
    obtain ⟨hk3, -⟩ := hD.list_c18 h
    obtain ⟨-, ⟨e⟩⟩ := h
    exact hno 11 (Or.inl ⟨by omega, by norm_num⟩)
      (dvd_card_of_mulEquiv e (by
        show 11 ∣ Nat.card NativeSporadic.HS
        rw [CFSG.Sporadic.HS.card_HS]; norm_num))
  ·
    exfalso
    obtain ⟨hk3, -⟩ := hD.list_c19 h
    obtain ⟨-, ⟨e⟩⟩ := h
    exact hno 17 (Or.inl ⟨by omega, by norm_num⟩)
      (dvd_card_of_mulEquiv e (by
        show 17 ∣ Nat.card NativeSporadic.He
        rw [CFSG.Sporadic.He.card_He]; norm_num))
  ·
    exfalso
    obtain ⟨hk3, -⟩ := hD.list_c20 h
    obtain ⟨-, -, ⟨e⟩⟩ := h
    exact hno 13 (Or.inl ⟨by omega, by norm_num⟩)
      (dvd_card_of_mulEquiv e (by
        show 13 ∣ Nat.card NativeSporadic.Ru
        rw [CFSG.Sporadic.Ru.card_Ru]; norm_num))

theorem not_nonquasi
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16) (h1220 : Stmt12_2_20) [Finite G] {T L V H P U I : Subgroup G} {h : G}
    {n p : ℕ} (hH : Hyp1223 G T L V) (hNE : NoEscape12_2_13 L V)
    (hC : Config12_2_24 T L V H P U I h n p) {K : Subgroup G} (hKN : K ≤ NR T U)
    (hK : n = 4 ∧ IsSL27OverE49 ↥(modO2Image (NR T U) K)) : False := by
  obtain ⟨k, hk, hdvd⟩ := card_Kbar_dvd h331 h1222 h323 h1216 h1220 hH hNE hC hKN
  obtain ⟨hn4, hSL⟩ := hK
  apply not_dvd_GL hk (q := 343) (Or.inl ⟨hn4, by norm_num⟩)
  refine dvd_trans ?_ hdvd
  rw [L1294Q.card_of_isSL27OverE49 hSL]
  norm_num

end Lem25

end CFSG.Quasithin.H13
