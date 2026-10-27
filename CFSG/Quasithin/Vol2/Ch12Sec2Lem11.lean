module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7
public import CFSG.Quasithin.Vol2.KGFact4413PGt3
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Lem11

omit [Finite G] in
theorem card_of_lieModel_psl_two {Q : Type} [Group Q] {m : ℕ} (h : LieModel Q .PSL 2 2 m) :
    Nat.card Q = 2 ^ m * (4 ^ m - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have h2 := L34.two_le_card_field K
  rw [hK] at h2
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at h2; norm_num at h2
    · exact h0
  have hodd : Nat.gcd 2 (2 ^ m - 1) = 1 := by
    have h' : Odd (2 ^ m - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hx : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      rw [pow_succ, Nat.odd_iff]
      generalize 2 ^ k = x at *
      omega
    exact Nat.coprime_two_left.mpr h'
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK, hodd,
    Nat.div_one, Finset.Icc_self, Finset.prod_singleton,
    show (2 ^ m) ^ 2 = 4 ^ m by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  norm_num

theorem psl_two_card_ne {m : ℕ} (N : ℕ) (hN : N = 9999360 ∨ N = 1080 ∨ N = 6048) :
    2 ^ m * (4 ^ m - 1) ≠ N := by
  intro h
  by_cases hm : 9 ≤ m
  · have h1 : 2 ^ 9 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h2 : 4 ^ 9 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h3 : 2 ^ 9 * (4 ^ 9 - 1) ≤ 2 ^ m * (4 ^ m - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
    omega
  · interval_cases m <;> omega

theorem card_of_list443 {Q : Type} [Group Q] [Finite Q]
    (h : (∃ n : ℕ, 2 ≤ n ∧ LieModel Q .PSL 2 2 n) ∨ LieModel Q .PSL 3 2 1 ∨
      LieModel Q .PSL 4 2 1 ∨ Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 7)) ∨
      (Group.IsPerfect Q ∧ Nat.card (Subgroup.center Q) = 3 ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6))) ∨
      LieModel Q .PSU 3 3 1) :
    (∃ n : ℕ, Nat.card Q = 2 ^ n * (4 ^ n - 1)) ∨ Nat.card Q = 168 ∨ Nat.card Q = 20160 ∨
      Nat.card Q = 360 ∨ Nat.card Q = 2520 ∨ Nat.card Q = 1080 ∨ Nat.card Q = 6048 := by
  rcases h with ⟨n, -, hn⟩ | h3 | h4 | he | he | ⟨-, hZ, he⟩ | hU
  · exact Or.inl ⟨n, card_of_lieModel_psl_two hn⟩
  · obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel h3
    rw [Nat.card_congr e.toEquiv, card_sl_zmod_two]
    exact Or.inr (Or.inl (by decide))
  · obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel h4
    rw [Nat.card_congr e.toEquiv, card_sl_zmod_two]
    exact Or.inr (Or.inr (Or.inl (by decide)))
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
    exact Or.inr (Or.inr (Or.inr (Or.inl (by decide))))
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide)))))
  · obtain ⟨e⟩ := he
    rw [(Subgroup.center Q).card_eq_card_quotient_mul_card_subgroup, hZ,
      Nat.card_congr e.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by decide))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Lem7.card_of_lieModel_psu_three_three hU))))))

omit [Finite G] in
theorem oTwoUpper_eq_self_of_odd {A : Subgroup G} (hA : Odd (Nat.card A)) : oTwoUpper A = A :=
  le_antisymm (oTwoUpper_le A) fun _ ha =>
    mem_oTwoUpper_of_odd ha (Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha))

end Lem11

open Lem11 Lem7

theorem stmt12_2_11_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3)
    (h12210 : Stmt12_2_10) (hE : E2.E22StatementC) (h443 : Stmt4_4_3') (hB : Lem12211Borel)
    (hA : Lem12211A315) : Stmt12_2_11' := by
  intro G _ _ T L V H U hH hHs hU1 hUV hHU hcase
  have h1226 := stmt12_2_6_of h1222 h323
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hmin := minParabolic h331 hH hHs
  obtain ⟨⟨hmax2, -, -⟩, -, -, hNT0, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  have hNT : Subgroup.normalizer (T : Set G) ≤ M := by rwa [hH.conjClosure_eq] at hNT0
  have hMmax : quasithinIsMaxTwoLocal M := by rwa [hH.conjClosure_eq] at hmax2
  have hTM : T ≤ M := hH.normalizes
  have hLM : L ≤ M := Subgroup.le_normalizer
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have := hred.2.1
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  have hc : ⁅V, L⁆ = V := hH.irrPlus.2.2.2.1
  have hHMV : H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) :=
    (h1226 G T L V hH).2 U H hU1 hUV hHU
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 ∨
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := by
    rcases hcase with ⟨e⟩ | ⟨-, hZ, he, -, -⟩ | ⟨hU, -, -⟩
    · obtain ⟨e⟩ := e
      exact Or.inl (by rw [Nat.card_congr e.toEquiv, Lem8.card_sl_five_zmod_two])
    · obtain ⟨e⟩ := he
      refine Or.inr (Or.inl ?_)
      rw [(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).card_eq_card_quotient_mul_card_subgroup, hZ,
        Nat.card_congr e.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
      decide
    · exact Or.inr (Or.inr (card_of_lieModel_psu_three_three hU))
  have key : 1 < E1.nParam H → ∀ (C : Subgroup G), C ≤ H ⊓ M → Odd (Nat.card C) →
      (∃ k : ℕ, C.relIndex (H ⊓ M) = 2 ^ k) → ∀ (p : ℕ) (A : Subgroup G), p.Prime → 3 < p →
      A ≤ C → A ≠ ⊥ → IsElemAbelian p A → (A : Set G) * (T : Set G) = (T : Set G) * A →
        False := by
    intro hn C hCHM hCodd hChall p A hp hp3 hAC hA1 hAel hAT
    have hAHM : A ≤ H ⊓ M := hAC.trans hCHM
    have hNA := Ch4.lemma4413NAPGt3_of hE G H T (H ⊓ M) hH.simple hH.nonabelian hH.qtke hHs.1.2
      hn hmin.isSylow hmin.uniqueMax C hCHM hCodd hChall p A hp hp3 hAC hAel hAT
    have hAMV : A ≤ hH.MV := fun a ha => ⟨(hAHM ha).2, (hHMV ▸ hAHM ha).2⟩
    have hAN : A ≤ Subgroup.normalizer (V : Set G) := fun a ha => (hAMV ha).2
    have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
    have hAodd : Odd (Nat.card A) := by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAp
      rw [hk]
      exact Odd.pow (hp.odd_of_ne_two (by omega))
    have hALb : autOn A V ≤ autOn L V := by
      rw [← (h12210 G T L V hH).2.1, ← oTwoUpper_eq_self_of_odd hAodd, ← A4.oTwoUpper_autOn hAN]
      exact oTwoUpper_mono (A4.autOn_mono hAMV)
    have hAV := hA G T L V hH A p hp hp3 hAMV hAp hAel.1 hAT hALb
    have hr := remark_4_4_2 hH.simple hH.nonabelian hH.qtke hH.sylow hMmax hTM hH.maximal
      hH.faithful hLM hH.quasisimple le_rfl hVLT hred hc.symm hH.irrPlus.2.1
      (hAHM.trans inf_le_right) hAV hA1 hAel.1 hAodd
    rcases h443 G T M L A T V hH.simple hH.nonabelian hH.qtke hH.sylow hMmax hTM hH.maximal
        hH.faithful hLM hH.quasisimple (hAHM.trans inf_le_right) hA1 hAel.1 hAodd
        hr.commutator_le le_rfl hAT rfl hr.VB_le hr.VB_normalized hr.VB_eq hr.VB_ne_bot
        hr.VB_centralizes with hNAM | ⟨-, hlist, hrest⟩
    · exact hNA fun x hx => ⟨hx.1, hNAM hx.2⟩
    · rcases hcase with ⟨e⟩ | ⟨hperf, hZ, hA6, hcard6, hv⟩ | ⟨hU, hV6, hV3⟩
      ·
        have h9 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 9999360 := by
          obtain ⟨e⟩ := e
          rw [Nat.card_congr e.toEquiv, Lem8.card_sl_five_zmod_two]
        rcases card_of_list443 hlist with ⟨n, hn'⟩ | h | h | h | h | h | h
        · exact psl_two_card_ne (m := n) _ (Or.inl rfl) (hn'.symm.trans h9)
        all_goals rw [h9] at h; exact absurd h (by decide)
      ·
        have h10 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
          obtain ⟨e⟩ := hA6
          rw [(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).card_eq_card_quotient_mul_card_subgroup,
            hZ, Nat.card_congr e.toEquiv, Lem8.card_alternatingGroup_fin (by norm_num)]
          decide
        rcases hrest with ⟨-, -, -, hhat, -⟩ | ⟨m, -, hLie, -⟩ | ⟨hL3, -⟩
        · obtain ⟨⟨z, hzZ, hzV⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
            (omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1 hV2)
          have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
          have hzT : z ∈ Subgroup.centralizer (T : Set G) :=
            ((Subgroup.closure_le (T ⊓ Subgroup.centralizer (T : Set G))).mpr
              (fun _ hx => hx.1) hzZ).2
          have hzTL : z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) :=
            Subgroup.centralizer_le (fun _ hx => hx.1) hzT
          have hord : orderOf z = 2 := orderOf_eq_prime (hV2 z hzV) hz1'
          exact hhat ⟨hperf, hZ, hA6⟩ hcard6 z ⟨hzV, hzTL⟩ hord (hv z ⟨hzV, hzT⟩ hz1')
        · exact psl_two_card_ne (m := 2 * m) _ (Or.inr (Or.inl rfl))
            ((card_of_lieModel_psl_two hLie).symm.trans h10)
        · obtain ⟨e3⟩ := nonempty_mulEquiv_sl_two_of_lieModel hL3
          rw [Nat.card_congr e3.toEquiv] at h10
          rcases card_sl_three_four_five (Or.inl rfl) with h | h | h <;> rw [h] at h10 <;>
            exact absurd h10 (by decide)
      ·
        have h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := card_of_lieModel_psu_three_three hU
        rcases hrest with ⟨-, -, -, -, hU33⟩ | ⟨m, -, hLie, -⟩ | ⟨hL3, -⟩
        · obtain ⟨V₃, hV₃, hV₃c, hV₃n, hno⟩ := hU33 hU hV6
          exact hno (hV3 V₃ hV₃ hV₃c hV₃n)
        · exact psl_two_card_ne (m := 2 * m) _ (Or.inr (Or.inr rfl))
            ((card_of_lieModel_psl_two hLie).symm.trans h60)
        · obtain ⟨e3⟩ := nonempty_mulEquiv_sl_two_of_lieModel hL3
          rw [Nat.card_congr e3.toEquiv] at h60
          rcases card_sl_three_four_five (Or.inl rfl) with h | h | h <;> rw [h] at h60 <;>
            exact absurd h60 (by decide)
  have hBor := fun h2 => hB G T M H hH.simple hH.nonabelian hH.qtke hH.sylow hMmax hTM hNT hHs h2
  refine ⟨?_, fun h2 C hC hCodd hChall => ?_⟩
  · by_contra hgt
    push Not at hgt
    have h2le : 2 ≤ E1.nParam H := hgt.le
    obtain ⟨⟨C, hC, hCodd, hChall⟩, hall'⟩ := hBor h2le
    obtain ⟨p, A, hp, hp3, hAC, hA1, hAel, hAT⟩ := (hall' C hC hCodd hChall).2 (Or.inl hgt)
    exact key (lt_of_lt_of_le (by norm_num) h2le) C hC hCodd hChall p A hp hp3 hAC hA1 hAel hAT
  · have h2le : 2 ≤ E1.nParam H := h2.ge
    obtain ⟨hC1, hex⟩ := (hBor h2le).2 C hC hCodd hChall
    refine ⟨hC1, ?_⟩
    by_contra h3
    obtain ⟨p, A, hp, hp3, hAC, hA1, hAel, hAT⟩ := hex (Or.inr h3)
    exact key (lt_of_lt_of_le (by norm_num) h2le) C hC hCodd hChall p A hp hp3 hAC hA1 hAel hAT

end CFSG.Quasithin.H13
