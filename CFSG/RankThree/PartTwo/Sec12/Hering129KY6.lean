module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KY5
public import CFSG.RankThree.PartTwo.Sec12.Hering129LNotEight
public import CFSG.RankThree.PartTwo.Sec12.Hering129HShape
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY2
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY3
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY4
public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

theorem center_eq_bot_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Subgroup.center X = ⊥) : Subgroup.center X' = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg e hz'

theorem not_three_dvd_of_isSLThreePiAt {X : Type} [Group X] {m : ℕ}
    (h : Sec4.IsSLThreePiAt X m) : ¬ 3 ∣ m := by
  obtain ⟨K, _, _, h⟩ := h
  rcases h with ⟨-, hm, -⟩ | ⟨-, hm, -⟩ <;> omega

theorem gap129YShape_of (h424 : Sec4.Item4_24Used) (h45 : Sec4.Item4_5)
    (hK : KFacts.KS12NormalizerMoves) (h1134N : Sec11.Item1134E27N)
    (h1134ST : Sec21.Item1134E27ST) (hTL : KS129ThreeLocalFix) (hCen : Gap127TwoCfgPlus)
    (hOTwo : KS129OTwo) (hP8 : Hering129L.Psl28ProperSolvable) (hSp : Gap129YSporadic)
    (hG2R : Gap129YG2Range) (hPGL : KS129PGL3Shape) : Gap129YShape := by
  intro G _ _ A c L b a K S cfg q hq x hxD hxb Y hY hXY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd := cfg.std
  have hst : PartTwoStanding G := hstd.toPartTwoStanding
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.isE27.1
  have hA27 : Nat.card A = 27 := hstd.isE27.2
  have hFE : partTwoF G = partTwoE G := hstd.partTwoF_eq
  have hAF : A ∈ partTwoF G := hFE ▸ cfg.mem_E
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, -⟩ := cfg.point_facts
  have hDA : D129 a b ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hxA : x ∈ A := hDA hxD
  have hx1 : x ≠ 1 := fun h => hxb (h ▸ Subgroup.one_mem _)
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hcA : c ∈ A := hstd.mem_A
  have hc1 : c ≠ 1 := hstd.ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hbx : b ∉ Subgroup.zpowers x := fun h =>
    hxb (mem_of_mem_zpowers_of_ne_one (orderOf_eq_prime hx3 hx1) h hb1 (Subgroup.mem_zpowers b))
  obtain ⟨hYx, hAN, hAC, -⟩ := id hY
  have hYle : Y ≤ Subgroup.centralizer ({x} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYx
  have hAle : A ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
  have hKK := gap129KFKStrong_of_fix hTL hCen
  obtain ⟨hcX, hSX, hXq, hZ2⟩ := hKK G A c L b a K S cfg ⟨q, hq⟩ x hxD hxb
  obtain ⟨-, -, δ, hGK, hδ13, F, hFf, hFfin, hFcard, φK, hφK, hkerK⟩ :=
    exists_sl2_quotient_of_fix hTL hCen G A c L b a K S cfg q hq x hxD hxb
  obtain ⟨hq4, hq2, -⟩ := hCen.2 G A c L b a K S cfg q hq
  haveI : Finite F := Finite.of_fintype F
  have hq3card : ¬ 3 ∣ q.card := not_three_dvd_of_isSLThreePiAt hq.1
  have hq3 : q.p ≠ 3 := fun hp => hq3card (by
    rw [TauCeti.PrimePower.card_def, hp]
    exact dvd_pow_self 3 q.exponent_pos.ne')
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    exact fun h => hq3card (Nat.prime_three.dvd_of_dvd_pow h)
  have hδpos : 1 ≤ δ := by rcases hδ13 with rfl | rfl <;> norm_num
  have hF4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hFcard]
    exact hq4.trans (Nat.le_self_pow (by omega) _)
  have hFpow : Nat.card F = q.p ^ (q.exponent * δ) := by
    rw [Nat.card_eq_fintype_card, hFcard, TauCeti.PrimePower.card_def, ← pow_mul]
  have hn1 : 1 ≤ q.exponent * δ := Nat.mul_pos q.exponent_pos hδpos
  haveI hqp : Fact q.p.Prime := ⟨q.prime_p⟩
  have hXT : (∃ n : ℕ, 1 ≤ n ∧
        Nonempty (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x) ≃*
          projSL 2 (GaloisField 2 n))) ∨
      (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
        Nonempty (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x) ≃*
          projSL 2 (GaloisField p n))) := by
    by_cases hp2 : q.p = 2
    · left
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine ⟨q.exponent * δ, hn1, ?_⟩
      obtain ⟨e⟩ := Hering129KYa.nonempty_quotTheta_equiv_projSL (p := 2) (n := q.exponent * δ)
        (by rw [hFpow, hp2]) hF4 φK hφK hkerK
      exact ⟨e⟩
    · right
      have h3p : 3 < q.p := by
        have h2 := q.prime_p.two_le
        have h4 : q.p ≠ 4 := fun h => by
          have := q.prime_p
          rw [h] at this
          norm_num at this
        omega
      exact ⟨q.p, q.exponent * δ, hqp, h3p, hn1,
        Hering129KYa.nonempty_quotTheta_equiv_projSL hFpow hF4 φK hφK hkerK⟩
  have hAX : A ⊓ resCent K x = Subgroup.zpowers c :=
    inf_eq_zpowers_of_sl2_quotient hAe hcA hcX (orderOf_eq_prime hc3 hc1) h3F φK hkerK
  have hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    normalizer_le_of_sec12StdBar_of_list h45 hK hstd cfg.list
  have hNX : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((A ⊓ resCent K x : Subgroup G) : Set G) := by
    rw [hAX]
    exact hW
  have hX := resCent_mem_thetaComponentsIn cfg.hK hYle hXY hXq
  have hsec : Late.sectionCentralizer A Y ((aschbacherSolvableCore 3 Y).map Y.subtype) =
      (Subgroup.zpowers x : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAN, hAC]
  have h4 := yshape_424 h424 hst hAF hFE hA27 hxA hx1 hbA hbx hYx hsec hX hXT hNX
  have hYq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hYx
  have hns : ¬ Group.IsSolvable (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := by
    intro hsolv
    haveI : Nontrivial (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hYq
    haveI : Group.IsPerfect (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) := hYq.1
    exact Group.IsPerfect.not_isSolvable _ hsolv
  have hYperf : Group.IsPerfect ↥Y := Sec6.isPerfect_of_mem_thetaComponentsAt hYx
  have hS4Y : SectionFourHyp ↥Y := by
    obtain ⟨hC4, -, -, -⟩ := Proof128.centralizer_setup hst hAF hA27 hxA hx1
    have h1 := Sec4.sectionFourHyp_subgroup hC4
      (Y.subgroupOf (Subgroup.centralizer ({x} : Set G)))
    exact Sec4.Census.sectionFourHyp_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYle) h1
  have lie_case : ∀ (r : TauCeti.PrimePower) (δ' : ℕ),
      IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r δ' → 4 ≤ r.card → r.p ≠ 3 → (δ' = 3 → r.p = 2) →
      (δ' = 1 ∨ δ' = 3) → ¬ (δ = 1 ∧ δ' = 3) →
      Typ129I K Y ∨ Typ129II K Y ∨ Typ129IV q Y := by
    intro r δ' hGY hr4 hrp3 hrδ hδ'13 hcase
    obtain ⟨F', hF'f, hF'fin, hF'card, φY, hφY, hkerY⟩ :=
      exists_sl2_image_Y hTL h1134N h1134ST hKK cfg ⟨q, hq⟩ hxD hxb hY hXY hGY hr4 hrp3 hrδ
    haveI : Finite F' := Finite.of_fintype F'
    haveI : Fact r.p.Prime := ⟨r.prime_p⟩
    have hδ'pos : 1 ≤ δ' := by rcases hδ'13 with rfl | rfl <;> norm_num
    have hF'pow : Nat.card F' = r.p ^ (r.exponent * δ') := by
      rw [Nat.card_eq_fintype_card, hF'card, TauCeti.PrimePower.card_def, ← pow_mul]
    have hF'4 : 4 ≤ Nat.card F' := by
      rw [Nat.card_eq_fintype_card, hF'card]
      exact hr4.trans (Nat.le_self_pow (by omega) _)
    have hpow := pow_cases_of_two_sl2_quotients hFpow hF'pow (by rw [← hFpow]; exact hF4)
      (by rw [← hF'pow]; exact hF'4) φK φY hφK hφY hkerK hkerY
    have e1 : q.card ^ δ = q.p ^ (q.exponent * δ) := by
      rw [TauCeti.PrimePower.card_def, ← pow_mul]
    have e2 : r.card ^ δ' = r.p ^ (r.exponent * δ') := by
      rw [TauCeti.PrimePower.card_def, ← pow_mul]
    have hs : q.card ^ δ = r.card ^ δ' ∨ (q.card ^ δ = 4 ∧ r.card ^ δ' = 5) ∨
        (q.card ^ δ = 5 ∧ r.card ^ δ' = 4) := by
      rw [e1, e2]
      exact hpow
    exact typ129_of_lie_table hGK hGY hcase hs
  have hLq : ∃ q' : TauCeti.PrimePower,
      Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q'.card := ⟨q, hq.1⟩
  have iii_of_l3 : (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      Sec4.IsoLThreePi (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) p e) →
      Subgroup.center (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) = ⊥ → Typ129IIIcType L Y := by
    rintro ⟨p, e, hp, he1, hIso⟩ hZ
    have hθ : aschbacherSolvableCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
      hOTwo ↥Y hS4Y hYperf (Or.inr (Or.inr ⟨p, e, hp, he1, hIso⟩))
    have ePC := QuotientGroup.quotientMulEquivOfEq hθ
    refine ⟨hLq, Or.inl ⟨p, e, hp, ?_⟩, center_eq_bot_of_mulEquiv ePC hZ⟩
    rcases hIso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
    · exact Or.inl ⟨h1, ⟨ePC.symm.trans f⟩⟩
    · exact Or.inr ⟨h2, ⟨ePC.symm.trans f⟩⟩
  rcases h4 with hfield | ⟨X', _, hX', hXe⟩
  ·
    exfalso
    obtain ⟨h8a, h8b⟩ := Hering129L.gap129YNotEightField_of hKK hP8 G A c L b a K S cfg q hq x
      hxD hxb Y hY hXY hfield
    exact (not_stdKind_of_notEight h1134N h1134ST hst hAF cfg.mem_S hFE hA27 hxA hx1 hYx hAN hAC
      h8a h8b hbA).1 hfield
  · obtain ⟨eXe⟩ := hXe
    obtain ⟨eC⟩ := yshape_424_commutator hYx hAle hAN hAc eXe
    rcases hX' with ⟨r, hr, ⟨eX⟩⟩ | ⟨r, hr, ⟨eX⟩⟩ | ⟨p, e, hp, he, hL3⟩ |
      ⟨π, p, f, K', hfld, hPF, hmod, ⟨eX⟩⟩ | eX | eX
    ·
      have hGr : IsG2D4 X' r 1 := Or.inl ⟨rfl, hr, ⟨eX⟩⟩
      have hS := Hering129KModels.isSimpleGroup_of_isG2D4 hGr
      have hnc : ∃ a b : X', a * b ≠ b * a :=
        Hering129KModels.exists_noncomm_of_perfect (Hering129KModels.isPerfect_of_isG2D4 hGr)
      have eY := equivOfCommutatorTop hS hnc eC
      have hIso : Sec4.IsoGTwo (↥Y ⧸ aschbacherSolvableCore 3 ↥Y) r := ⟨hr, ⟨eY.trans eX⟩⟩
      have hθ : aschbacherSolvableCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        hOTwo ↥Y hS4Y hYperf (Or.inl ⟨r, hIso⟩)
      have ePC := QuotientGroup.quotientMulEquivOfEq hθ
      have hGY : IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r 1 :=
        Or.inl ⟨rfl, hr, ⟨ePC.symm.trans (eY.trans eX)⟩⟩
      obtain ⟨hr4, hrp3⟩ := hG2R G A c L b a K S cfg q hq x hxD hxb Y hY hXY r hIso
      rcases lie_case r 1 hGY hr4 hrp3 (fun h => by omega) (Or.inl rfl) (fun h => by omega) with
        h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    ·
      have hGr : IsG2D4 X' r 3 := Or.inr ⟨rfl, hr, ⟨eX⟩⟩
      have hS := Hering129KModels.isSimpleGroup_of_isG2D4 hGr
      have hnc : ∃ a b : X', a * b ≠ b * a :=
        Hering129KModels.exists_noncomm_of_perfect (Hering129KModels.isPerfect_of_isG2D4 hGr)
      have eY := equivOfCommutatorTop hS hnc eC
      have hθ : aschbacherSolvableCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        hOTwo ↥Y hS4Y hYperf (Or.inr (Or.inl ⟨r, hr, ⟨eY.trans eX⟩⟩))
      have ePC := QuotientGroup.quotientMulEquivOfEq hθ
      have hDY : ∃ hr' : (TauCeti.LieTypeIndex.trialityD4 r).Valid,
          Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr'⟩).Group) :=
        ⟨hr, ⟨ePC.symm.trans (eY.trans eX)⟩⟩
      have hGY : IsG2D4 (↥Y ⧸ CFSG.pCore 2 ↥Y) r 3 :=
        Or.inr ⟨rfl, hr, ⟨ePC.symm.trans (eY.trans eX)⟩⟩
      by_cases hδ1 : δ = 1
      · exact Or.inr (Or.inr (Or.inr (typ129IIIcType_of_d4 hLq hDY)))
      · have hδ3 : δ = 3 := hδ13.resolve_left hδ1
        by_cases hrange : 4 ≤ r.card ∧ r.p ≠ 3 ∧ r.p = 2
        · rcases lie_case r 3 hGY hrange.1 hrange.2.1 (fun _ => hrange.2.2) (Or.inr rfl)
            (fun h => hδ1 h.1) with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (typ129IIIcType_of_d4 hLq hDY)))
    ·
      haveI := hp
      obtain ⟨h1, h2⟩ := l3_shape_of_commutator hns he hL3 ⟨eC⟩
      exact Or.inr (Or.inr (Or.inr (iii_of_l3 ⟨p, e, hp, he, h1⟩ h2)))
    ·
      obtain ⟨h1, h2⟩ := hPGL _ X' hns ⟨π, p, f, K', hfld, hPF, hmod, ⟨eX⟩⟩ ⟨eC⟩
      exact Or.inr (Or.inr (Or.inr (iii_of_l3 h1 h2)))
    · exact absurd ⟨eC⟩ (hSp G A c L b a K S cfg q hq x hxD hxb Y hY hXY X' (Or.inl eX))
    · exact absurd ⟨eC⟩ (hSp G A c L b a K S cfg q hq x hxD hxb Y hY hXY X' (Or.inr eX))

end CFSG.RankThree.PartTwo.Sec12
