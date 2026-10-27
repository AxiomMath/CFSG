module

public import CFSG.RankThree.PartTwo.Sec15.Item1511Proof
import CFSG.RankThree.PartTwo.Sec15.Item157Proof
import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1511Point : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      A = omegaOneThree P →
        Y = pPrimeCoreOf 3 Y ⊔
            deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
          ((∃ n f : ℕ, 1 ≤ f ∧ e = n * f ∧
              Sec14.IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f) ∨
            Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)))

namespace Proof1511Steps

section Mult


theorem eq_bot_of_isLThreeEpsAt (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : Group.IsPerfect X) (hZc : Z ≤ Subgroup.center X) (hcop : Nat.Coprime 6 (Nat.card Z))
    {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hS : IsLThreeEpsAt (X ⧸ Z) p f) : Z = ⊥ := by
  refine Subgroup.eq_bot_of_card_eq _ (by_contra fun h1 => ?_)
  obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd h1
  have hr6 : Nat.Coprime 6 r := Nat.Coprime.coprime_dvd_right hrZ hcop
  have hr3 : 3 < r := by
    have h2 : r ≠ 2 := by
      rintro rfl
      norm_num at hr6
    have h3 : r ≠ 3 := by
      rintro rfl
      norm_num at hr6
    have := hr.two_le
    omega
  have hr3' : r ∣ 3 := by
    rcases hS with hS1 | ⟨-, hS2⟩
    · obtain ⟨φ⟩ := hS1
      exact KFacts.KS14.prime_dvd_of_forall_cover hX hZc φ hr hrZ fun L _ _ _ η hη hC hCp =>
        (KFacts.KS14.card_ker_dvd_gcd_projSL hf hr hr3 η hη hC hCp).trans (Nat.gcd_dvd_left _ _)
    · obtain ⟨φ⟩ := hS2
      exact KFacts.KS14.prime_dvd_of_forall_cover hX hZc φ hr hrZ fun L _ _ _ η hη hC hCp =>
        (KFacts.KS14.card_ker_dvd_gcd_projSU hf hr hr3 η hη hC hCp).trans (Nat.gcd_dvd_left _ _)
  have := Nat.le_of_dvd (by norm_num) hr3'
  omega

theorem pPrimeCore_eq_pCore_of_quot {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) (h3 : 3 ∣ Nat.card Y)
    (htype : (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧
        IsLThreeEpsAt (Y ⧸ CFSG.pPrimeCore 3 Y) p f) ∨
      Nonempty (Y ⧸ CFSG.pPrimeCore 3 Y ≃* alternatingGroup (Fin 7))) :
    CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 Y with hP
  set R := CFSG.pPrimeCore 3 Y with hR
  have hPR : P ≤ R := pCore_two_le_pPrimeCore_three
  set π := QuotientGroup.mk' P with hπ
  set Z := R.map π with hZ
  have hZn : Z.Normal := (CFSG.pPrimeCore_normal (p := 3) (G := Y)).map _
    (QuotientGroup.mk'_surjective _)
  have hR3 : Nat.Coprime 3 (Nat.card R) := CFSG.pPrimeCore_coprime_card (p := 3) (G := Y)
  have hZtop : Z ≠ ⊤ := by
    intro htop
    have hRtop : R = ⊤ := by
      have h1 : R ⊔ π.ker = ⊤ := by
        have hc := Subgroup.comap_map_eq π R
        rw [← hZ, htop, Subgroup.comap_top] at hc
        exact hc.symm
      rwa [QuotientGroup.ker_mk', sup_eq_left.mpr hPR] at h1
    rw [hRtop, Subgroup.card_top] at hR3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR3 h3
  have hZc : Z ≤ Subgroup.center (Y ⧸ P) :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
      ⟨hq.1.commutator_eq_top, hq.2.1⟩ Z hZtop
  have hZ3 : Nat.Coprime 3 (Nat.card Z) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hR3
  have hZ2 : Nat.Coprime 2 (Nat.card Z) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
    have hzc : (z : Y ⧸ P) ∈ Subgroup.center (Y ⧸ P) := hZc z.2
    have hzn : (Subgroup.zpowers (z : Y ⧸ P)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hzp : IsPGroup 2 (Subgroup.zpowers (z : Y ⧸ P)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hle : Subgroup.zpowers (z : Y ⧸ P) ≤ CFSG.pCore 2 (Y ⧸ P) := by
      exact CFSG.LieType.BorelTits.le_pCore 2 hzn hzp
    rw [Sec18.pCore_quotient_pCore_eq_bot 2] at hle
    have hz1 : (z : Y ⧸ P) = 1 := (Subgroup.mem_bot).mp (hle (Subgroup.mem_zpowers _))
    have : orderOf z = 1 := by
      rw [← Subgroup.orderOf_coe, hz1, orderOf_one]
    omega
  have hZ6 : Nat.Coprime 6 (Nat.card Z) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.coprime_mul_iff_left.mpr ⟨hZ2, hZ3⟩
  have e : (Y ⧸ P) ⧸ Z ≃* Y ⧸ R := QuotientGroup.quotientQuotientEquivQuotient P R hPR
  have hperf : Group.IsPerfect (Y ⧸ P) := hq.1
  have hZbot : Z = ⊥ := by
    rcases htype with ⟨p, f, _, hf, hL⟩ | ⟨⟨φ⟩⟩
    · exact eq_bot_of_isLThreeEpsAt (Y ⧸ P) Z hperf hZc hZ6 hf (IsLThreeEpsAt.of_mulEquiv e.symm hL)
    · exact KFacts.KS14.ks18Mult_sporadic (Y ⧸ P) Z hperf hZc hZ6 (Or.inr (Or.inl ⟨e.trans φ⟩))
  refine le_antisymm ?_ hPR
  have h1 : R ≤ π.ker := (Subgroup.map_eq_bot_iff R).mp hZbot
  rwa [QuotientGroup.ker_mk'] at h1

end Mult

section Dec

variable {G : Type} [Group G] [Finite G]

theorem factorization_three_mul' {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

theorem factorization_three_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    a.factorization 3 ≤ b.factorization 3 :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hb h) hb).mpr h 3

theorem factorization_three_card_le {X Y : Subgroup G} (h : X ≤ Y) :
    (Nat.card X).factorization 3 ≤ (Nat.card Y).factorization 3 :=
  factorization_three_le_of_dvd Nat.card_pos.ne' (Subgroup.card_dvd_of_le h)

theorem factorization_three_le_inf (h142 : Item142R) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {D : Subgroup G}
    (hDK : D ≤ k142 A (lB A) c) (hDH : D ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (Nat.card D).factorization 3 ≤ (Nat.card (D ⊓ L : Subgroup G)).factorization 3 := by
  have hD := h.toSec13Data
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set K := k142 A (lB A) c with hK
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h h3L
  obtain ⟨Q₀, -, hQ₀⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) (bot_mem_invariantPiSubgroups H A _)
  obtain ⟨-, hbr⟩ := h142 G A c L h Q₀ hQ₀
  rcases hbr with ⟨-, hQK, -, -⟩ | ⟨hKeq, -⟩
  ·
    have hK3 : ¬ 3 ∣ Nat.card K := by
      rw [hK, ← hQK]
      exact (isPiSubgroup_piCompl_iff Nat.prime_three Q₀).mp hQ₀.prop.2.1
    have hD3 : ¬ 3 ∣ Nat.card D := fun h3 => hK3 (h3.trans (Subgroup.card_dvd_of_le hDK))
    rw [Nat.factorization_eq_zero_of_not_dvd hD3]
    exact Nat.zero_le _
  ·
    set N₀ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ pPrimeCoreOf 3 H with hN₀
    have hKeq' : K = N₀ ⊔ L := by
      rw [hK, hKeq, hN₀, hH]
      ac_rfl
    have hCAH : Subgroup.centralizer (A : Set G) ≤ H :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A)).trans
        (centralizer_singleton_le_normalizer_zpowers c)
    have hON : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (pPrimeCoreOf_le 3 _).trans (hCAH.trans (le_normalizer_pPrimeCoreOf 3 H))
    have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
      intro h3
      have hdvd := h3.trans (card_sup_dvd_card_mul hON)
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h1 | h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
          (coprime_card_pPrimeCoreOf 3 _) h1
    have hN₀L : N₀ ≤ Subgroup.normalizer (L : Set G) :=
      sup_le ((pPrimeCoreOf_le 3 _).trans (hCAH.trans hHL)) ((pPrimeCoreOf_le 3 H).trans hHL)
    have hDL : D ≤ Subgroup.normalizer (L : Set G) := hDH.trans hHL
    have h1 := Sec6.card_sup_mul_card_inf hN₀L
    have h2 := Sec6.card_sup_mul_card_inf hDL
    have hDLK : D ⊔ L ≤ N₀ ⊔ L := sup_le (hKeq' ▸ hDK) le_sup_right
    have h3 := factorization_three_card_le hDLK
    have hN₀v : (Nat.card N₀).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hN₀3
    have e1 : (Nat.card (N₀ ⊔ L : Subgroup G)).factorization 3 +
        (Nat.card (N₀ ⊓ L : Subgroup G)).factorization 3 =
          (Nat.card N₀).factorization 3 + (Nat.card L).factorization 3 := by
      rw [← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne',
        ← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne', h1]
    have e2 : (Nat.card (D ⊔ L : Subgroup G)).factorization 3 +
        (Nat.card (D ⊓ L : Subgroup G)).factorization 3 =
          (Nat.card D).factorization 3 + (Nat.card L).factorization 3 := by
      rw [← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne',
        ← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne', h2]
    omega

theorem eq_inf_sup_of_dec (h142 : Item142R) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    (hdec : Y = pPrimeCoreOf 3 Y ⊔
      deltaZero A (lB A) (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    Y = (L ⊓ Y) ⊔ pPrimeCoreOf 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set D := deltaZero A (lB A) (Y ⊓ H) with hDdef
  set R := pPrimeCoreOf 3 Y with hR
  set M := (L ⊓ Y) ⊔ R with hM
  have hv : (Nat.card D).factorization 3 ≤ (Nat.card (D ⊓ L : Subgroup G)).factorization 3 :=
    factorization_three_le_inf h142 h h9
      (sSup_le fun Q hQ => le_delta hQ.1.1 (hQ.2.trans inf_le_right))
      ((deltaZero_le _).trans inf_le_right)
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    Sec17.Sec15R.normalizer_zpowers_le_normalizer_L h h3L
  have hDY : D ≤ Y := (deltaZero_le _).trans inf_le_left
  have hDL : D ≤ Subgroup.normalizer (L : Set G) :=
    ((deltaZero_le _).trans inf_le_right).trans hHL
  have hRY : R ≤ Y := pPrimeCoreOf_le 3 Y
  have hMY : M ≤ Y := sup_le inf_le_right hRY
  have hYR : Y ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pPrimeCoreOf 3 Y
  have hDLY : D ≤ Subgroup.normalizer ((L ⊓ Y : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hDL hx, Subgroup.le_normalizer (hDY hx)⟩
  have hDM : D ≤ Subgroup.normalizer (M : Set G) := le_normalizer_sup hDLY (hDY.trans hYR)
  have hYMD : Y = D ⊔ M := by
    refine le_antisymm ?_ (sup_le hDY hMY)
    conv_lhs => rw [hdec]
    exact sup_le (le_sup_right.trans le_sup_right) le_sup_left
  have hcardY := Sec6.card_sup_mul_card_inf hDM
  rw [← hYMD] at hcardY
  have hDLM : D ⊓ L ≤ D ⊓ M :=
    le_inf inf_le_left fun x hx => Subgroup.mem_sup_left ⟨hx.2, hDY hx.1⟩
  have e1 : (Nat.card Y).factorization 3 + (Nat.card (D ⊓ M : Subgroup G)).factorization 3 =
      (Nat.card D).factorization 3 + (Nat.card M).factorization 3 := by
    rw [← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne',
      ← factorization_three_mul' Nat.card_pos.ne' Nat.card_pos.ne', hcardY]
  have h4 := factorization_three_card_le hDLM
  have h5 := factorization_three_card_le hMY
  have hvYM : (Nat.card Y).factorization 3 = (Nat.card M).factorization 3 := by omega
  have hidx : ¬ 3 ∣ M.relIndex Y := Proof157.not_dvd_relIndex_of_factorization_three_eq hMY hvYM
  have hMn : Y ≤ Subgroup.normalizer (M : Set G) := by
    rw [hYMD]
    exact sup_le hDM Subgroup.le_normalizer
  have hres : oPrimeResidualOf 3 Y ≤ M := by
    rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hyY, k, hk⟩
    have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
      have hord : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨g, hgY, hle⟩ := exists_le_map_conj_of_not_dvd_relIndex hMY hidx
      (Subgroup.zpowers_le.mpr hyY) hyp
    have hMg : M.map (MulAut.conj g).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMn hgY)
    rw [hMg] at hle
    exact hle (Subgroup.mem_zpowers y)
  have hYres : Y = oPrimeResidualOf 3 Y := hY.1.2.1
  exact le_antisymm (hYres.le.trans hres) hMY

end Dec

end Proof1511Steps

open Proof1511Steps

theorem step1511List_of
    (hpt : Step1511Point) (h142 : Item142R) : Step1511List := by
  intro G _ _ A c L h p e _ he hL3 Y hY hmeet P hAP hP hprod hWH hΩ
  obtain ⟨hdec, htype⟩ := hpt G A c L h p e he hL3 Y hY hmeet P hAP hP hprod hWH hΩ
  have hD := h.toSec13Data
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_eq_nine hD (isPerfect_lBar hD) hprod.some
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hO2 : CFSG.pCore 2 ↥Y ≠ ⊤ := by
    intro htop
    have : Subsingleton (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [QuotientGroup.eq, htop]
          exact Subgroup.mem_top _
    have : Subsingleton ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
        Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) := QuotientGroup.mk_surjective.subsingleton
    obtain ⟨-, hS, -⟩ := hq
    exact not_nontrivial_iff_subsingleton.mpr this hS.toNontrivial
  have h3Y : 3 ∣ Nat.card ↥Y :=
    (three_dvd_card_quotient_of_eq_oPrimeResidualOf hY.1.2.1 (CFSG.pCore 2 ↥Y) hO2).trans
      (Subgroup.card_quotient_dvd_card _)
  have htype' : (∃ (p' f : ℕ) (_ : Fact p'.Prime), 1 ≤ f ∧
      IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p' f) ∨
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) := by
    rcases htype with ⟨n, f, hf, -, hL⟩ | hA7
    · exact Or.inl ⟨p, f, inferInstance, hf, hL⟩
    · exact Or.inr hA7
  have hcore := pPrimeCore_eq_pCore_of_quot hq h3Y htype'
  have hcoreG : pPrimeCoreOf 3 Y = CFSG.Open.pCoreOf 2 Y := by
    show (CFSG.pPrimeCore 3 ↥Y).map Y.subtype = (CFSG.Open.pCore 2 ↥Y).map Y.subtype
    rw [hcore]
  refine ⟨?_, ?_⟩
  · rw [← hcoreG]
    exact eq_inf_sup_of_dec h142 h h9 hY hdec
  · have e₀ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y :=
      QuotientGroup.quotientMulEquivOfEq hcore.symm
    rcases htype with ⟨n, f, hf, hnf, hL⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl ⟨n, f, hf, hnf, IsLThreeEpsAt.of_mulEquiv e₀.symm hL⟩
    · exact Or.inr ⟨e₀.trans φ⟩

end CFSG.RankThree.PartTwo.Sec15
