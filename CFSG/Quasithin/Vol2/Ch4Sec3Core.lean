module

public import CFSG.Quasithin.Vol2.Ch4Sec3InspC48
public import CFSG.Quasithin.Vol2.Ch4Sec3Thm432

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_not_mem_sq_mem {S : Subgroup G} {y : G} (hy : y ∉ S) {m : ℕ}
    (hm : y ^ 2 ^ m = 1) : ∃ k : ℕ, y ^ 2 ^ k ∉ S ∧ (y ^ 2 ^ k) ^ 2 ∈ S := by
  classical
  have hex : ∃ k : ℕ, y ^ 2 ^ (k + 1) ∈ S :=
    ⟨m, by rw [pow_succ, pow_mul, hm, one_pow]; exact S.one_mem⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · rcases hk : Nat.find hex with _ | j
    · simpa using hy
    · have := Nat.find_min hex (show j < Nat.find hex by omega)
      exact this
  · rw [← pow_mul, ← pow_succ]
    exact Nat.find_spec hex

omit [Finite G] in
theorem exists_mem_normalizer_sq_mem {S X : Subgroup G} (hX : IsPGroup 2 X) {y : G}
    (hyX : y ∈ X) (hyN : y ∈ Subgroup.normalizer (S : Set G)) (hyS : y ∉ S) :
    ∃ t ∈ X, t ∈ Subgroup.normalizer (S : Set G) ∧ t ∉ S ∧ t ^ 2 ∈ S := by
  obtain ⟨m, hm⟩ := hX ⟨y, hyX⟩
  have hm' : y ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨k, hk, hk2⟩ := exists_pow_not_mem_sq_mem hyS hm'
  exact ⟨y ^ 2 ^ k, X.pow_mem hyX _, Subgroup.pow_mem _ hyN _, hk, hk2⟩

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem le_normalizer_Rp :
    T ≤ Subgroup.normalizer ((T ⊓ centralizerSection M L (pCoreOf 2 L) : Subgroup G) : Set G) :=
  fun _ hx => mem_normalizer_inf (Subgroup.le_normalizer hx)
    (le_normalizer_centralizerSection' s.hyp.normal (s.hyp.T_le hx))

theorem exists_t (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∃ t : G, t ∈ T ∧ t ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G) ∧ t ∉ T ⊓ H ∧
      t ^ 2 ∈ T ⊓ H ∧
      (pCoreOf 2 I < T ⊓ centralizerSection M L (pCoreOf 2 L) →
        t ∈ T ⊓ centralizerSection M L (pCoreOf 2 L)) := by
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRp
  set S := T ⊓ H with hS
  have hT2 : IsPGroup 2 T := s.hyp.sylow.1
  by_cases hR : pCoreOf 2 I < Rp
  ·
    have hRpS : ¬ Rp ≤ S := by
      intro hle
      apply hR.ne
      rw [s.lemma_4_3_4]
      exact inf_eq_right.mpr hle
    have hSRp : S ≤ Subgroup.normalizer (Rp : Set G) :=
      inf_le_left.trans s.le_normalizer_Rp
    have hlt : S < S ⊔ Rp := lt_of_le_of_ne le_sup_left fun e => hRpS (e ▸ le_sup_right)
    have h2 : IsPGroup 2 ↥(S ⊔ Rp) := hT2.to_le (_root_.sup_le inf_le_left inf_le_left)
    obtain ⟨y, hy, hyN, hyS⟩ := exists_mem_normalizer_not_mem h2 hlt
    have hy' : y ∈ ((S : Set G) * (Rp : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S Rp hSRp]
      exact hy
    obtain ⟨a, ha, r, hr, rfl⟩ := hy'
    have hrN : r ∈ Subgroup.normalizer (S : Set G) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer ha)) hyN
      simpa using this
    have hrS : r ∉ S := fun hr' => hyS (S.mul_mem ha hr')
    obtain ⟨t, htR, htN, htS, ht2⟩ :=
      exists_mem_normalizer_sq_mem (hT2.to_le inf_le_left) hr hrN hrS
    exact ⟨t, htR.1, htN, htS, ht2, fun _ => htR⟩
  · obtain ⟨y, hyT, hyN, hyS⟩ := exists_mem_normalizer_not_mem hT2 (s.S_lt_T h37 h38 h39)
    obtain ⟨t, htT, htN, htS, ht2⟩ := exists_mem_normalizer_sq_mem hT2 hyT hyN hyS
    exact ⟨t, htT, htN, htS, ht2, fun h => absurd h hR⟩

end Setting432

structure Setting432K (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ)
    (I H K : Subgroup G) (t : G) : Prop where
  base : Setting432 G T M L n I H
  cComp : K ∈ cComp H
  quasisimple : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)
  L_le_K : L ≤ K
  case1 : C48Case1 H (pCoreOf 2 I) (H ⊓ M) L
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K
  not_le : ¬ K ≤ H ⊓ M
  le_normalizer : H ⊓ M ≤ Subgroup.normalizer (K : Set G)
  desc : C48KDescribed H (pCoreOf 2 I) (H ⊓ M) L
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K
  t_mem : t ∈ T
  t_normalizer : t ∈ Subgroup.normalizer ((T ⊓ H : Subgroup G) : Set G)
  t_not_mem : t ∉ T ⊓ H
  t_sq : t ^ 2 ∈ T ⊓ H
  t_Rp : pCoreOf 2 I < T ⊓ centralizerSection M L (pCoreOf 2 L) →
    t ∈ T ⊓ centralizerSection M L (pCoreOf 2 L)

namespace Setting432

variable {T M L I H : Subgroup G} {n : ℕ} (s : Setting432 G T M L n I H)
include s

theorem exists_setting432K (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    ∃ (K : Subgroup G) (t : G), Setting432K G T M L n I H K t := by
  obtain ⟨K, hK, hKq, hLK, h1, hKM, hMK, hdesc⟩ := s.exists_K hR hC hC48 hInsp h36 h37 h38 h39
  obtain ⟨t, htT, htN, htS, ht2, htR⟩ := s.exists_t h37 h38 h39
  exact ⟨K, t, s, hK, hKq, hLK, h1, hKM, hMK, hdesc, htT, htN, htS, ht2, htR⟩

end Setting432

namespace Setting432K

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (sk : Setting432K G T M L n I H K t)
include sk

theorem lemma_4_3_5 : IsUniqueM (L ⊔ (T ⊓ H ⊔ Subgroup.zpowers t)) M := by
  refine sk.base.lemma_4_3_3_a (lt_of_le_of_ne le_sup_left fun e => sk.t_not_mem ?_)
    (_root_.sup_le inf_le_left (Subgroup.zpowers_le.mpr sk.t_mem))
  rw [e]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

end Setting432K

@[expose] def Lemma436Comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CFSG.Open.IsComponentOf K H →
      C31Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K → False

@[expose] def Lemma437Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K → ¬ IsSp4Block K

@[expose] def Lemma437A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
        ¬ IsAltBlockType K 7

@[expose] def Lemma437SL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K → ¬ IsSL3Block K

@[expose] def Concl438 (H R M L V K : Subgroup G) : Prop :=
  C41Case3 H R M L V K ∧
    (IsC134Case 2 (K ⊔ R) R K ∨ IsC134Case 3 (K ⊔ R) R K ∨
      C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K)

@[expose] def Lemma439 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      Concl438 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
        T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥

@[expose] def Lemma4310 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      Concl438 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ →
        IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K

@[expose] def Lemma43End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K →
      C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      C41Case3 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      IsC134Case 3 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K →
      T ⊓ H ⊓ Subgroup.centralizer (K : Set G) = ⊥ → False

omit [Finite G] in
theorem card_modO2_ne {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) {N : ℕ}
    (hN : N = 168 ∨ N = 20160 ∨ N = 360) : Nat.card (ModO2 L) ≠ N := by
  intro h
  have hcardL : Nat.card (ModO2 L) = 2 ^ n * (4 ^ n - 1) :=
    F420.card_of_statedPSL_two_two (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
      (by decide) hL)
  refine card_psl_two_ne hn ?_ (hcardL.symm.trans h)
  rcases hN with rfl | rfl | rfl <;> simp

theorem concl438_of {T M L I H K : Subgroup G} {n : ℕ} {t : G}
    (sk : Setting432K G T M L n I H K t) (hchar : CharTwo K)
    (h41 : C41Conclusion H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K)
    (hSp4 : Lemma437Sp4) (hA7 : Lemma437A7) (hSL3 : Lemma437SL3) :
    Concl438 H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K := by
  have hn := sk.base.hyp.two_le
  have hlie := sk.base.hyp.lie
  have hLeq := h41.1
  rcases h41.2.2.2 with ⟨m, hm, hAlt, -, hK, -, -⟩ | ⟨hK, -⟩ | h3 | ⟨-, -, h4⟩
  · rcases hm with rfl | rfl
    · exact absurd hK (hA7 G T M L n I H K t sk hchar h41)
    · exfalso
      rw [← hLeq] at hAlt
      obtain ⟨-, α, hα, hker, -⟩ := hAlt
      refine card_modO2_ne hn hlie (N := 360) (by norm_num) ?_
      rw [card_modO2_of_surjective α hα hker, card_of_alt' (by norm_num) (MulEquiv.refl _)]
      decide
  · exact absurd hK (hSp4 G T M L n I H K t sk hchar h41)
  · refine ⟨h3, ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, hcase, -⟩ := h3
    rcases hcase with h1 | h2 | h3 | h4
    · exact absurd h1.1 (hSL3 G T M L n I H K t sk hchar h41)
    · exact Or.inl h2
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)
  · exfalso
    rcases h4 with h | h
    · exact card_modO2_ne hn hlie (Or.inl rfl) (by rw [hLeq]; exact card_of_l32 h)
    · exact card_modO2_ne hn hlie (Or.inr (Or.inl rfl)) (by rw [hLeq]; exact F420.card_of_l42 h)

theorem core432_of (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hInsp : InspC48L2) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h436 : Lemma436Comp) (hSp4 : Lemma437Sp4)
    (hA7 : Lemma437A7) (hSL3 : Lemma437SL3) (h439 : Lemma439) (h4310 : Lemma4310)
    (hEnd : Lemma43End) : Core432 := by
  intro G _ _ T M L n I H s
  obtain ⟨K, t, sk⟩ := s.exists_setting432K hR hC hC48 hInsp h36 h37 h38 h39
  rcases sk.desc with ⟨hcomp, h31⟩ | ⟨-, hchar, -, -, h41⟩
  · exact h436 G T M L n I H K t sk hcomp h31
  · have h438 := concl438_of sk hchar h41 hSp4 hA7 hSL3
    have hCS := h439 G T M L n I H K t sk hchar h41 h438
    have hcase3 := h4310 G T M L n I H K t sk hchar h41 h438 hCS
    exact hEnd G T M L n I H K t sk hchar h41 h438.1 hcase3 hCS

end CFSG.Quasithin.H13.Ch4
