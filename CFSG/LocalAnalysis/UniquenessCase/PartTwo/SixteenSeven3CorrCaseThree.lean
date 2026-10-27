module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

variable {G : Type} [Group G] [Finite G]

theorem s16c167_not_case168_2_of_case168_3 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h3 : Case168_3 D V₀ V hV L) : ¬ Case168_2 D V₀ V hV L := by
  have hN : Nat.card ↥(lBar V₀ V hV L) = 27 := h3.1.2.1
  rintro ⟨-, ⟨L₀, -, hshape⟩, -⟩
  rcases hshape with ⟨n, h5, h11, -, hI, -⟩ | ⟨m, h3m, h5m, -, hL, -⟩ | ⟨-, hS, -⟩ |
    ⟨-, hO6, -⟩ | ⟨-, hO8, -⟩
  · have h2 := s16c167_two_mul_card_isAlt (by omega) hI
    rw [hN] at h2
    interval_cases n <;> revert h2 <;> decide
  · have hc := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL
    rw [hN] at hc
    interval_cases m <;> revert hc <;> decide
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
    rw [Nat.card_congr e.toEquiv] at hN
    have := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 3
    rw [show (6 / 2 : ℕ) = 3 from rfl] at hN
    rw [this, hK] at hN
    revert hN
    decide
  · have := s16c167_card_isOmegaMinus_six hO6
    omega
  · obtain ⟨-, K, _, _, b, c, hK, hirr, ⟨e⟩⟩ := hO8
    have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    rw [Nat.card_congr e.toEquiv] at hN
    have h2 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
      (K := K) (n := 8 / 2) (by norm_num) hirr
    rw [hN, hK] at h2
    revert h2
    decide

theorem s16c167_mbar_le_normalizer_lbar (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L) :
    Mbar D.M ⊥ V hV ≤ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
  have h151 : Hyp151 D ⊥ V L := hc.setting.hyp151
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V hV x
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hWcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  intro φ hφ
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub ⊥ V hV D.M φ).1 hφ
  by_contra hne
  have hgne : (m : G) ∉ nBar D.M ⊥ V hV L := by
    intro hmem
    have h1 := (s15_Infra_mem_nBar_iff h151.hyp125 hV hmM).1 hmem
    have h2 := s15_Infra_barSub_conjSubgroup ⊥ V hV m.2 L
    rw [h1] at h2
    apply hne
    have hinv : (actTil ⊥ V hV m)⁻¹ ∈
        normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h2.symm
    have := (normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV)))).inv_mem hinv
    simpa using this
  have hc1 : ⁅lBar ⊥ V hV L, barSub ⊥ V hV (conjSubgroup L (m : G))⁆ = ⊥ := by
    have hproof : h151.isElemAbelian = hV := Subsingleton.elim _ _
    have h := (s15_Kbar_commute_conj h151 (m := (1 : G)) (m' := (m : G))
      D.M.one_mem hmM (by simpa using hgne)).1
    rw [hproof] at h
    simpa [lBar, conjSubgroup_one] using h
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := lBar ⊥ V hV L
  let Lb₁ : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV (conjSubgroup L (m : G))
  haveI hEx : CFSG.IsExtraspecial 3 ↥Lb := h3.1.1
  have hLbcard : Nat.card ↥Lb = 27 := by
    dsimp only [Lb]
    rw [h3.1.2.1]
    norm_num
  have hLb₁card : Nat.card ↥Lb₁ = 27 := by
    dsimp only [Lb₁]
    have h2 := s15_Infra_barSub_conjSubgroup ⊥ V hV m.2 L
    rw [h2, Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact hLbcard
  have hcomm : ∀ a : ↥Lb, ∀ b : ↥Lb₁,
      (a : MulAut (Vtil ⊥ V hV)) * (b : MulAut (Vtil ⊥ V hV)) =
        (b : MulAut (Vtil ⊥ V hV)) * (a : MulAut (Vtil ⊥ V hV)) := by
    intro a b
    have hle : Lb ≤ Subgroup.centralizer (Lb₁ : Set (MulAut (Vtil ⊥ V hV))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1
    have hb := (Subgroup.mem_centralizer_iff.1 (hle a.2)) (b : MulAut (Vtil ⊥ V hV)) b.2
    exact hb.symm
  let f : ↥Lb × ↥Lb₁ →* MulAut (Vtil ⊥ V hV) :=
    { toFun := fun p => (p.1 : MulAut (Vtil ⊥ V hV)) * (p.2 : MulAut (Vtil ⊥ V hV))
      map_one' := by simp
      map_mul' := fun p q => by
        show ((p.1 * q.1 : ↥Lb) : MulAut (Vtil ⊥ V hV)) *
              ((p.2 * q.2 : ↥Lb₁) : MulAut (Vtil ⊥ V hV)) =
            ((p.1 : MulAut (Vtil ⊥ V hV)) * (p.2 : MulAut (Vtil ⊥ V hV))) *
              ((q.1 : MulAut (Vtil ⊥ V hV)) * (q.2 : MulAut (Vtil ⊥ V hV)))
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc ((p.1 : MulAut (Vtil ⊥ V hV)) * (q.1 : MulAut (Vtil ⊥ V hV))) *
                ((p.2 : MulAut (Vtil ⊥ V hV)) * (q.2 : MulAut (Vtil ⊥ V hV)))
            = (p.1 : MulAut (Vtil ⊥ V hV)) *
                ((q.1 : MulAut (Vtil ⊥ V hV)) * (p.2 : MulAut (Vtil ⊥ V hV))) *
                  (q.2 : MulAut (Vtil ⊥ V hV)) := by group
          _ = (p.1 : MulAut (Vtil ⊥ V hV)) *
                ((p.2 : MulAut (Vtil ⊥ V hV)) * (q.1 : MulAut (Vtil ⊥ V hV))) *
                  (q.2 : MulAut (Vtil ⊥ V hV)) := by rw [hcomm q.1 p.2]
          _ = ((p.1 : MulAut (Vtil ⊥ V hV)) * (p.2 : MulAut (Vtil ⊥ V hV))) *
                ((q.1 : MulAut (Vtil ⊥ V hV)) * (q.2 : MulAut (Vtil ⊥ V hV))) := by group }
  have hker : Nat.card ↥f.ker ≤ 3 := by
    let emb : ↥f.ker → ↥(Subgroup.center ↥Lb) := fun p =>
      ⟨p.1.1, by
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hb : (p.1.1 : MulAut (Vtil ⊥ V hV)) *
            (p.1.2 : MulAut (Vtil ⊥ V hV)) = 1 := by
          have h := MonoidHom.mem_ker.1 p.2
          change (p.1.1 : MulAut (Vtil ⊥ V hV)) *
            (p.1.2 : MulAut (Vtil ⊥ V hV)) = 1 at h
          exact h
        have h1 := eq_inv_of_mul_eq_one_left hb
        have hab : Commute (a : MulAut (Vtil ⊥ V hV))
            (p.1.2 : MulAut (Vtil ⊥ V hV)) := hcomm a p.1.2
        rw [h1]
        exact hab.inv_right⟩
    have hinj : Function.Injective emb := by
      intro p q hpq
      have h1 : (p.1.1 : ↥Lb) = q.1.1 := congrArg Subtype.val hpq
      have h2 : (p.1.1 : MulAut (Vtil ⊥ V hV)) = (q.1.1 : MulAut (Vtil ⊥ V hV)) :=
        congrArg Subtype.val h1
      have hp : (p.1.1 : MulAut (Vtil ⊥ V hV)) *
          (p.1.2 : MulAut (Vtil ⊥ V hV)) = 1 := by
        have h := MonoidHom.mem_ker.1 p.2
        change (p.1.1 : MulAut (Vtil ⊥ V hV)) *
          (p.1.2 : MulAut (Vtil ⊥ V hV)) = 1 at h
        exact h
      have hq : (q.1.1 : MulAut (Vtil ⊥ V hV)) *
          (q.1.2 : MulAut (Vtil ⊥ V hV)) = 1 := by
        have h := MonoidHom.mem_ker.1 q.2
        change (q.1.1 : MulAut (Vtil ⊥ V hV)) *
          (q.1.2 : MulAut (Vtil ⊥ V hV)) = 1 at h
        exact h
      have hpv : (p.1.2 : MulAut (Vtil ⊥ V hV)) = (p.1.1 : MulAut (Vtil ⊥ V hV))⁻¹ :=
        eq_inv_of_mul_eq_one_right hp
      have hqv : (q.1.2 : MulAut (Vtil ⊥ V hV)) = (q.1.1 : MulAut (Vtil ⊥ V hV))⁻¹ :=
        eq_inv_of_mul_eq_one_right hq
      apply Subtype.ext
      apply Prod.ext
      · exact h1
      · apply Subtype.ext
        rw [hpv, hqv, h2]
    have hle := Nat.card_le_card_of_injective emb hinj
    calc Nat.card ↥f.ker ≤ Nat.card ↥(Subgroup.center ↥Lb) := hle
      _ = 3 := CFSG.IsExtraspecial.center_order_p 3 ↥Lb
  have hcard : Nat.card ↥f.ker * Nat.card ↥f.range = 3 ^ 6 := by
    rw [card_ker_mul_card_range f, Nat.card_prod, hLbcard, hLb₁card]
    norm_num
  have h243 : 243 ∣ Nat.card ↥f.range := by
    set k := Nat.card ↥f.ker with hk
    set r := Nat.card ↥f.range with hr
    have hkr : k * r = 3 ^ 6 := hcard
    have hk1 : 1 ≤ k := by
      rw [hk]
      haveI : Nonempty ↥f.ker := ⟨1⟩
      exact Nat.card_pos
    have hk3 : k ≤ 3 := by
      rw [hk]
      exact hker
    interval_cases k
    · have : r = 729 := by omega
      exact ⟨3, by omega⟩
    · exfalso; omega
    · have : r = 243 := by omega
      exact ⟨1, by omega⟩
  have hrange_dvd : Nat.card ↥f.range ∣ Nat.card (MulAut (Vtil ⊥ V hV)) :=
    Subgroup.card_subgroup_dvd_card f.range
  have h243aut : 243 ∣ Nat.card (MulAut (Vtil ⊥ V hV)) := h243.trans hrange_dvd
  have hAut : Nat.card (MulAut (Vtil ⊥ V hV)) = 20158709760 := by
    rw [CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hWsq 6 hWcard]
    norm_num [Fin.prod_univ_succ]
  rw [hAut] at h243aut
  norm_num at h243aut

theorem s16c167_mQuot_sum_le_one_of_index_le_two {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A : Subgroup G} (hAst : A ≤ stabTil ⊥ V)
    (h : (⨆ (t : MulAut (Vtil ⊥ V hV)) (_ : t ∈ barSub ⊥ V hV A ∧ t ≠ 1),
      fixV (Subgroup.zpowers t)).index ≤ 2) :
    E3.mQuot V (⨆ (a : G) (_ : a ∈ A ∧ a ∉ centralizer (V : Set G)),
      V ⊓ centralizer ({a} : Set G)) ≤ 1 := by
  let S : Subgroup G := ⨆ (a : G) (_ : a ∈ A ∧ a ∉ centralizer (V : Set G)),
    V ⊓ centralizer ({a} : Set G)
  let F : Subgroup (Vtil ⊥ V hV) := ⨆ (t : MulAut (Vtil ⊥ V hV))
    (_ : t ∈ barSub ⊥ V hV A ∧ t ≠ 1), fixV (Subgroup.zpowers t)
  have hFle : F ≤ imgTil ⊥ V hV S := by
    refine iSup₂_le fun t ht => ?_
    obtain ⟨m, hmA, rfl⟩ := (mem_barSub ⊥ V hV A t).1 ht.1
    have hne : (m : G) ∉ centralizer (V : Set G) := by
      intro hc
      apply ht.2
      refine (actTil_eq_one_iff ⊥ V hV m).2 fun v hv => ?_
      rw [Subgroup.mem_bot]
      have h1 := (Subgroup.mem_centralizer_iff.1 hc) v hv
      rw [← h1]
      group
    rw [s16c167_fixV_actTil hV m.2]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono V
      (le_iSup₂_of_le (m : G) ⟨hmA, hne⟩ le_rfl))
  have himg_le : imgTil ⊥ V hV S ≤ F := by
    rw [← imgTil_preTil ⊥ V hV F]
    refine Subgroup.map_mono (Subgroup.subgroupOf_mono V ?_)
    refine iSup₂_le fun a ha => ?_
    intro v hv
    rw [mem_preTil_iff_of_mem ⊥ V hV F hv.1]
    have hmem : mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv.1⟩) ∈
        fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨a, hAst ha.1⟩)) := by
      rw [s16c167_fixV_actTil hV (hAst ha.1)]
      rw [mem_imgTil]
      exact ⟨IntMod.mk hV ⟨v, hv.1⟩, hv, rfl⟩
    have hne : actTil ⊥ V hV ⟨a, hAst ha.1⟩ ≠ 1 := by
      intro h1
      apply ha.2
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := (actTil_eq_one_iff ⊥ V hV ⟨a, hAst ha.1⟩).1 h1 w hw
      rw [Subgroup.mem_bot] at h2
      have h3 : a * w * a⁻¹ = w := mul_inv_eq_one.1 h2
      have h4 : a * w = w * a := by
        calc a * w = a * w * a⁻¹ * a := by group
          _ = w * a := by rw [h3]
      exact h4.symm
    change mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv.1⟩) ∈
      (⨆ (t : MulAut (Vtil ⊥ V hV)) (_ : t ∈ barSub ⊥ V hV A ∧ t ≠ 1),
        fixV (Subgroup.zpowers t))
    have hle : fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨a, hAst ha.1⟩)) ≤
        (⨆ (t : MulAut (Vtil ⊥ V hV)) (_ : t ∈ barSub ⊥ V hV A ∧ t ≠ 1),
          fixV (Subgroup.zpowers t)) :=
      le_iSup₂_of_le (actTil ⊥ V hV ⟨a, hAst ha.1⟩)
        ⟨actTil_mem_barSub ⊥ V hV ha.1 (hAst ha.1), hne⟩ le_rfl
    exact hle hmem
  have hFimg : F = imgTil ⊥ V hV S := le_antisymm hFle himg_le
  have hindex : S.relIndex V = F.index := by
    rw [hFimg]
    change (S.subgroupOf V).index = (imgTil ⊥ V hV S).index
    exact (Subgroup.index_map_equiv (S.subgroupOf V) (TwelveShort.mkTilEquiv V hV)).symm
  unfold E3.mQuot
  rw [hindex]
  set n := F.index with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hn2 : n ≤ 2 := by
    rw [hn]
    exact h
  interval_cases n
  · have h1 : padicValNat 2 1 = 0 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      simpa using padicValNat.prime_pow (p := 2) 0
    rw [h1] <;> omega
  · have h2 : padicValNat 2 2 = 1 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      simpa using padicValNat.prime_pow (p := 2) 1
    rw [h2] <;> omega

theorem s16c167_sum_fixed_codim_le_one_of_case168_3 (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L)
    {A : Subgroup G} (hAM : A ≤ D.M) (hAel : IsElemAbelian 2 A)
    (hrk : rk ↥(barSub ⊥ V hV A) = 2) :
    E3.mQuot V (⨆ (a : G) (_ : a ∈ A ∧ a ∉ centralizer (V : Set G)),
      V ⊓ centralizer ({a} : Set G)) ≤ 1 := by
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := hh.pairFacts
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  refine s16c167_mQuot_sum_le_one_of_index_le_two hV hAst ?_
  have hE : IsElemAbelian2 (barSub ⊥ V hV A) := isElemAbelian2_barSub hV hAel
  have hEn : barSub ⊥ V hV A ≤ normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    (barSub_mono ⊥ V hV hAM).trans (s16c167_mbar_le_normalizer_lbar D hV hc h3)
  have hEcard : Nat.card ↥(barSub ⊥ V hV A) = 4 := by
    have hp : IsPGroup 2 ↥(barSub ⊥ V hV A) := by
      intro x
      refine ⟨1, ?_⟩
      have h2 := hE.2 x x.2
      have : (x : MulAut (Vtil ⊥ V hV)) ^ 2 = 1 := h2
      exact Subtype.ext (by simpa using this)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    unfold rk at hrk
    rw [hn, padicValNat.prime_pow] at hrk
    rw [hn, hrk]
    norm_num
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V hV x
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hWcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := by
      intro x
      refine ⟨1, ?_⟩
      simpa [pow_two] using hWsq x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  exact s16c167_codim_core hWsq hWcard h3.1 hEn hE hEcard

theorem s16c167_false_of_case168_3 (D : Data G) (hcorr : R16_14Corr D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L)
    (hr : rMV D.M V = ((D.k + 2 : ℕ) : ℕ∞)) {A : Subgroup G} (hAM : A ≤ D.M)
    (hAel : IsElemAbelian 2 A) {g : G} (hAg : A ≤ conjSubgroup V g)
    (hmQ : E3.mQuot (conjSubgroup V g) A = D.k) (hVg : ¬ conjSubgroup V g ≤ D.M)
    (himp : V ≤ conjSubgroup D.M g → Case168_2 D ⊥ V hV L)
    (hrk : rk ↥(barSub ⊥ V hV A) ≤ 2) : False := by
  classical
  have hnot2 : ¬ Case168_2 D ⊥ V hV L := s16c167_not_case168_2_of_case168_3 D hV h3
  have hVnot : ¬ V ≤ conjSubgroup D.M g := fun h => hnot2 (himp h)
  have hh : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hP := hh.pairFacts
  have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hnorm : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hh.inCalV
  have hk1 : 1 ≤ D.k := TwelveShort.one_le_k D
  by_cases hrk1 : rk ↥(barSub ⊥ V hV A) ≤ 1
  · have hlt : ((D.k + 1 : ℕ) : ℕ∞) < rMV D.M V := by
      rw [hr]
      exact_mod_cast (by omega : D.k + 1 < D.k + 2)
    exact hVnot (s16c167_le_conj_of_rk_le_gen D hV hc hlt hAM hAg hmQ hrk1).2
  have hrk2 : rk ↥(barSub ⊥ V hV A) = 2 := by omega
  have hU'le : A ⊓ centralizer (V : Set G) ≤ A := inf_le_left
  have hU'm : E3.mQuot (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) = D.k + 2 := by
    rw [E3.mQuot_add hU'le hAg, hmQ, ← s16c167_rk_barSub_eq_mQuot hV hAst, hrk2]
    omega
  have hCU' : ¬ centralizer ((A ⊓ centralizer (V : Set G) : Subgroup G) : Set G) ≤
      conjSubgroup D.M g := by
    intro h
    apply hVnot
    intro v hv
    apply h
    rw [Subgroup.mem_centralizer_iff]
    intro c hc'
    exact (Subgroup.mem_centralizer_iff.1 hc'.2 v hv).symm
  have hU₀V : conjSubgroup (A ⊓ centralizer (V : Set G)) g⁻¹ ≤ V := by
    have h1 := E3.conjSubgroup_mono_left g⁻¹ (hU'le.trans hAg)
    rwa [E3.conjSubgroup_conj_inv] at h1
  have hU₀m : E3.mQuot V (conjSubgroup (A ⊓ centralizer (V : Set G)) g⁻¹) = D.k + 2 := by
    have h1 := E3.mQuot_conjSubgroup (conjSubgroup V g) (A ⊓ centralizer (V : Set G)) g⁻¹
    rw [E3.conjSubgroup_conj_inv] at h1
    rw [h1]
    exact hU'm
  have hU₀C : ¬ centralizer ((conjSubgroup (A ⊓ centralizer (V : Set G)) g⁻¹ : Subgroup G) :
      Set G) ≤ D.M := by
    intro h
    apply hCU'
    have h1 := E3.conjSubgroup_mono_left g h
    rw [E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj] at h1
    exact h1
  obtain ⟨-, hres⟩ := hcorr V L hV hc
  rcases hres hr with ⟨-, -, hdesc⟩ | ⟨h11, -⟩
  swap
  · have h37 : D.sig = {7} := h11.2.2.2
    have h33 : D.sig = {3} := h3.2.2
    rw [h33] at h37
    simp at h37
  have hidx : (D.M ⊓ centralizer (V : Set G)).relIndex
      (D.M ⊓ centralizer ((conjSubgroup (A ⊓ centralizer (V : Set G)) g⁻¹ : Subgroup G) :
        Set G)) ≤ 2 :=
    Desc1614Three.relIndex_le_two D hc (hdesc _ hU₀V hU₀m hU₀C)
  have hidx' : (conjSubgroup D.M g ⊓ centralizer (conjSubgroup V g : Set G)).relIndex
      (conjSubgroup D.M g ⊓ centralizer ((A ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) ≤
        2 := by
    have h1 := E3.relIndex_conjSubgroup (D.M ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer ((conjSubgroup (A ⊓ centralizer (V : Set G)) g⁻¹ : Subgroup G) :
        Set G)) g
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj] at h1
    rw [h1]
    exact hidx
  have hAp : IsPGroup 2 A := hAel.isPGroup
  have hH : ∀ a : G, a ∈ A → a ∉ centralizer (V : Set G) →
      V ⊓ centralizer ({a} : Set G) ≤ conjSubgroup D.M g := by
    intro a haA haV
    have hDaA : (A ⊓ centralizer (V : Set G)) ⊔ zpowers a ≤ A :=
      sup_le inf_le_left ((Subgroup.zpowers_le).2 haA)
    have hDaV : (A ⊓ centralizer (V : Set G)) ⊔ zpowers a ≤ conjSubgroup V g := hDaA.trans hAg
    have hle : A ⊓ centralizer (V : Set G) ≤ (A ⊓ centralizer (V : Set G)) ⊔ zpowers a :=
      le_sup_left
    have hpos : E3.mQuot ((A ⊓ centralizer (V : Set G)) ⊔ zpowers a)
        (A ⊓ centralizer (V : Set G)) ≠ 0 := by
      intro h0
      have h1 := (E3.mQuot_eq_zero_iff (hAp.to_le hDaA) hle).1 h0
      have h2 : a ∈ A ⊓ centralizer (V : Set G) := by
        rw [h1]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      exact haV h2.2
    have hsum := E3.mQuot_add hle hDaV
    rw [hU'm] at hsum
    have hlt : (E3.mQuot (conjSubgroup V g) ((A ⊓ centralizer (V : Set G)) ⊔ zpowers a) : ℕ∞) <
        rMV (conjSubgroup D.M g) (conjSubgroup V g) := by
      rw [rMV_conj hnorm g, hr]
      exact_mod_cast (by omega : E3.mQuot (conjSubgroup V g)
        ((A ⊓ centralizer (V : Set G)) ⊔ zpowers a) < D.k + 2)
    have hcent := centralizer_le_of_mQuot_lt_rMV hDaV hlt
    intro v hv
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdc : d ∈ centralizer ({v} : Set G) := by
      have hsub : (A ⊓ centralizer (V : Set G)) ⊔ zpowers a ≤ centralizer ({v} : Set G) := by
        refine sup_le ?_ ?_
        · intro x hx
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hx.2 v hv.1).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_singleton_iff.1 hv.2).symm
      exact hsub hd
    exact Subgroup.mem_centralizer_singleton_iff.1 hdc
  have hS := s16c167_sum_fixed_codim_le_one_of_case168_3 D hV hc h3 hAM hAel hrk2
  have hSH : (⨆ (a : G) (_ : a ∈ A ∧ a ∉ centralizer (V : Set G)),
      V ⊓ centralizer ({a} : Set G)) ≤ V ⊓ conjSubgroup D.M g :=
    iSup₂_le fun a ha => le_inf inf_le_left (hH a ha.1 ha.2)
  have hHm : E3.mQuot V (V ⊓ conjSubgroup D.M g) ≤ 1 := (E3.mQuot_mono hSH).trans hS
  have hHB : V ⊓ conjSubgroup D.M g ≤
      conjSubgroup D.M g ⊓ centralizer ((A ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    refine le_inf inf_le_right ?_
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro c hc'
    exact (Subgroup.mem_centralizer_iff.1 hc'.2 v hv.1).symm
  have hCHle : (V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G) ≤
      V ⊓ conjSubgroup D.M g := inf_le_left
  have hKeq : (V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G) =
      (V ⊓ conjSubgroup D.M g) ⊓
        (conjSubgroup D.M g ⊓ centralizer (conjSubgroup V g : Set G)) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hrel : ((V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G)).relIndex
      (V ⊓ conjSubgroup D.M g) ≤ 2 := by
    rw [hKeq, Subgroup.inf_relIndex_left]
    exact (Subgroup.relIndex_le_of_le_right hHB
      (E3.relIndex_ne_zero' _ _)).trans hidx'
  have hCHm : E3.mQuot (V ⊓ conjSubgroup D.M g)
      ((V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G)) ≤ 1 := by
    unfold E3.mQuot
    have hne := E3.relIndex_ne_zero' (V ⊓ conjSubgroup D.M g)
      ((V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G))
    generalize ((V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G)).relIndex
      (V ⊓ conjSubgroup D.M g) = n at hrel hne ⊢
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hne
    interval_cases n <;> simp
  have hCHV : E3.mQuot V ((V ⊓ conjSubgroup D.M g) ⊓ centralizer (conjSubgroup V g : Set G)) ≤
      2 := by
    have h := E3.mQuot_add hCHle (inf_le_left : V ⊓ conjSubgroup D.M g ≤ V)
    omega
  have hlt2 : (E3.mQuot V ((V ⊓ conjSubgroup D.M g) ⊓
      centralizer (conjSubgroup V g : Set G)) : ℕ∞) < rMV D.M V := by
    rw [hr]
    exact_mod_cast (by omega : E3.mQuot V ((V ⊓ conjSubgroup D.M g) ⊓
      centralizer (conjSubgroup V g : Set G)) < D.k + 2)
  have hcentCH := centralizer_le_of_mQuot_lt_rMV (hCHle.trans inf_le_left) hlt2
  apply hVg
  intro w hw
  apply hcentCH
  rw [Subgroup.mem_centralizer_iff]
  intro c hc'
  exact (Subgroup.mem_centralizer_iff.1 hc'.2 w hw).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
