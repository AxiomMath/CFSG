module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelOvergroup
public import CFSG.GroupTheory.NormalizerLift
public import CFSG.GroupTheory.TwoPowOrderFactorization
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem519
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_of_isSylowOf_of_comm {A R : Subgroup G} {r : ℕ} [hr : Fact r.Prime]
    (hcomm : IsMulCommutative ↥A) (hR : IsSylowOf r R A) {x : G} (hxA : x ∈ A)
    (hx : x ^ r = 1) : x ∈ R := by
  obtain ⟨Q, rfl⟩ := hR
  let y : ↥A := ⟨x, hxA⟩
  have hy : y ^ r = 1 := Subtype.ext (by simpa using hx)
  have hzp : IsPGroup r (zpowers y) := by
    have hdvd : orderOf y ∣ r ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hy
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hr.out).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  obtain ⟨Q', hQ'⟩ := hzp.exists_le_sylow
  haveI : (Q : Subgroup ↥A).Normal := by
    haveI : IsMulCommutative ↥A := hcomm
    exact Subgroup.normal_of_isMulCommutative _
  have hQQ' : Q' = Q := by
    haveI := Sylow.unique_of_normal Q inferInstance
    exact Subsingleton.elim _ _
  refine ⟨y, ?_, rfl⟩
  rw [← hQQ']
  exact hQ' (mem_zpowers y)

theorem exists_isSylowOf_le_normalizer_torsion {M I A E : Subgroup G} {r : ℕ}
    [hr : Fact r.Prime] (hIM : I ≤ M) (hMI : M ≤ normalizer (I : Set G)) (hAI : A ≤ I)
    (hcomm : IsMulCommutative ↥A)
    (hrpart : (Nat.card A).factorization r = (Nat.card I).factorization r)
    (hE : ∀ x, x ∈ E ↔ x ∈ A ∧ x ^ r = 1) :
    ∃ P : Subgroup G, IsSylowOf r P M ∧ E ≤ P ∧ P ≤ normalizer (E : Set G) := by
  obtain ⟨R, hR⟩ := exists_isSylowOf r A
  have hRA : R ≤ A := hR.le
  have hRr : IsPGroup r R := hR.isPGroup
  have hRI : IsSylowOf r R I :=
    isSylowOf_of_card (hRA.trans hAI) (by rw [hR.card_eq, hrpart])
  have hER : E ≤ R := fun x hx =>
    mem_of_isSylowOf_of_comm hcomm hR ((hE x).mp hx).1 ((hE x).mp hx).2
  obtain ⟨Q, hQ⟩ := (hRr.comap_subtype (K := M)).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hPdef
  have hPsyl : IsSylowOf r P M := ⟨Q, rfl⟩
  have hPM : P ≤ M := hPsyl.le
  have hRP : R ≤ P := by
    intro x hx
    have hxM : x ∈ M := hIM (hAI (hRA hx))
    exact ⟨⟨x, hxM⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hPI : P ⊓ I = R :=
    hRI.eq_of_le (le_inf hRP hRI.le) inf_le_right (hPsyl.isPGroup.to_le inf_le_left)
  have hPN : P ≤ normalizer (R : Set G) := by
    intro g hg
    have := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hMI (hPM hg)⟩
    rwa [hPI] at this
  have hNRE : normalizer (R : Set G) ≤ normalizer (E : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    constructor
    · intro hx
      have hxR : x ∈ R := hER hx
      have hgx : g * x * g⁻¹ ∈ R := (hg x).mp hxR
      refine (hE _).mpr ⟨hRA hgx, ?_⟩
      rw [conj_pow, ((hE x).mp hx).2, mul_one, mul_inv_cancel]
    · intro hx
      have hgxR : g * x * g⁻¹ ∈ R := hER hx
      have hxR : x ∈ R := (hg x).mpr hgxR
      refine (hE x).mpr ⟨hRA hxR, ?_⟩
      have h1 : (g * x * g⁻¹) ^ r = 1 := ((hE _).mp hx).2
      rw [conj_pow] at h1
      have h2 : x ^ r = g⁻¹ * (g * x ^ r * g⁻¹) * g := by group
      rw [h2, h1]
      group
  exact ⟨P, hPsyl, hER.trans hRP, hPN.trans hNRE⟩

theorem permutes_torsion_of_le_normalizer_inf {M I A E T : Subgroup G} {r : ℕ}
    (hTM : T ≤ M) (hMI : M ≤ normalizer (I : Set G)) (hAI : A ≤ I)
    (hAT : Permutes A T) (hAN : A ≤ normalizer ((T ⊓ I : Subgroup G) : Set G))
    (hAT1 : A ⊓ T = ⊥) (hE : ∀ x, x ∈ E ↔ x ∈ A ∧ x ^ r = 1) : Permutes E T := by
  set R₂ : Subgroup G := T ⊓ I with hR₂
  have hEA : E ≤ A := fun x hx => ((hE x).mp hx).1
  have hR₂T : R₂ ≤ T := inf_le_left
  have hER₂ : E ≤ normalizer (R₂ : Set G) := hEA.trans hAN
  have hpow : ∀ a ∈ A, ∀ s ∈ R₂, ∀ k : ℕ, ∃ s' ∈ R₂, (a * s) ^ k = a ^ k * s' := by
    intro a ha s hs k
    induction k with
    | zero => exact ⟨1, R₂.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨s', hs', hk⟩ := ih
      refine ⟨(a⁻¹ * s' * a) * s, R₂.mul_mem ?_ hs, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) s').mp hs'
        simpa using this
      · rw [pow_succ, hk, pow_succ]
        group
  have hconj : ∀ t ∈ T, ∀ y ∈ E ⊔ R₂, t * y * t⁻¹ ∈ E ⊔ R₂ := by
    intro t ht y hy
    have hyset : y ∈ ((E ⊔ R₂ : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E R₂ hER₂] at hyset
    obtain ⟨x, hx, s, hs, rfl⟩ := hyset
    have htxs : t * (x * s) * t⁻¹ = (t * x * t⁻¹) * (t * s * t⁻¹) := by group
    rw [htxs]
    refine (E ⊔ R₂).mul_mem ?_ (Subgroup.mem_sup_right ?_)
    ·
      have hxA : x ∈ A := hEA hx
      have hmem : t * x ∈ (A : Set G) * (T : Set G) := by
        rw [show (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) from hAT]
        exact Set.mul_mem_mul ht hxA
      obtain ⟨a, ha, u₀, hu₀, hau₀⟩ := hmem
      have hau₀' : a * u₀ = t * x := hau₀
      set u : G := u₀ * t⁻¹ with hudef
      have hau : a * u = t * x * t⁻¹ := by rw [hudef, ← mul_assoc, hau₀']
      have hu : u ∈ T := T.mul_mem hu₀ (T.inv_mem ht)
      have hxI : t * x * t⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.mp (hMI (hTM ht)) x).mp (hAI hxA)
      have huI : u ∈ I := by
        have : u = a⁻¹ * (t * x * t⁻¹) := by rw [← hau]; group
        rw [this]
        exact I.mul_mem (I.inv_mem (hAI ha)) hxI
      have huR : u ∈ R₂ := ⟨hu, huI⟩
      obtain ⟨s', hs', hk⟩ := hpow a ha u huR r
      have hxr : (t * x * t⁻¹) ^ r = 1 := by
        rw [conj_pow, ((hE x).mp hx).2, mul_one, mul_inv_cancel]
      rw [← hau, hk] at hxr
      have har : a ^ r = s'⁻¹ := eq_inv_of_mul_eq_one_left hxr
      have harA : a ^ r ∈ A ⊓ T := ⟨A.pow_mem ha r, har ▸ T.inv_mem (hR₂T hs')⟩
      rw [hAT1] at harA
      have har1 : a ^ r = 1 := Subgroup.mem_bot.mp harA
      rw [← hau]
      exact (E ⊔ R₂).mul_mem (Subgroup.mem_sup_left ((hE a).mpr ⟨ha, har1⟩))
        (Subgroup.mem_sup_right huR)
    ·
      refine ⟨T.mul_mem (T.mul_mem ht (hR₂T hs)) (T.inv_mem ht), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMI (hTM ht)) s).mp hs.2
  have hTN : T ≤ normalizer ((E ⊔ R₂ : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj t ht y, fun hy => ?_⟩
    have := hconj t⁻¹ (T.inv_mem ht) _ hy
    simpa [mul_assoc] using this
  exact TwelveNineteen.permutes_of_le_normalizer_sup hR₂T hTN hER₂

theorem gap19_22_P_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hrpart : (Nat.card A).factorization r = (Nat.card (IOf D p L)).factorization r)
    (hAN : A ≤ normalizer ((D.T ⊓ IOf D p L : Subgroup G) : Set G))
    (E : Subgroup G) : Gap19_22_P D V₀ V p L A t B r h E := by
  intro hEA hEel hEcard
  have hr : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hr⟩
  haveI hcomm : IsMulCommutative ↥A := isMulCommutative_of_isZModSq h.hAcard
  have hEeq := eq_powTorsionSubgroup_of_isElemAbelian_card h.hAcard hr h.hr.2 hEA hEel hEcard
  have hE : ∀ x, x ∈ E ↔ x ∈ A ∧ x ^ r = 1 := by
    intro x
    rw [hEeq]
    exact mem_powTorsionSubgroup
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p h.hyp.hL.1.1.le
  have hMI : D.M ≤ normalizer (IOf D p L : Set G) := le_normalizer_IOf D h.hyp.hL.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hAT1 : A ⊓ D.T = ⊥ := by
    have hodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
    have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
    rw [eq_bot_iff]
    intro x hx
    have hx2 : IsPGroup 2 ↥(A ⊓ D.T) := hT2.to_le inf_le_right
    have hdvd : Nat.card ↥(A ⊓ D.T) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hx2.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ Nat.card A := by
        rw [hk] at hdvd
        exact (dvd_pow_self 2 hk0).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    rw [hk0, pow_zero] at hk
    have := (Subgroup.card_eq_one.mp hk)
    rw [this] at hx
    exact hx
  refine ⟨permutes_torsion_of_le_normalizer_inf hTM hMI h.hA h.hAT hAN hAT1 hE, Or.inr ?_⟩
  exact exists_isSylowOf_le_normalizer_torsion hIM hMI h.hA hcomm hrpart hE

theorem factorization_card_A_eq_card_IOf_of_hBar {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r)
    (hBar : (Nat.card (Bar2 (IOf D p L))).factorization r =
      2 * (2 ^ S17.nOf L - 1).factorization r) :
    (Nat.card A).factorization r = (Nat.card (IOf D p L)).factorization r := by
  classical
  have hr : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hr⟩
  set n := S17.nOf L with hn
  set I := IOf D p L with hI
  have hBar' : (Nat.card (Bar2 I)).factorization r = 2 * (2 ^ n - 1).factorization r := by
    rw [hn, hI]; exact hBar
  have hr2 : r ≠ 2 := by
    intro hr2'
    have hodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
    have : 2 ∣ Nat.card A := hr2' ▸ h.hr.2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hAcard : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) := by
    have h' := card_eq_of_isZModSq h.hAcard
    rw [← hn] at h'
    exact h'
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hAcard
    norm_num at hAcard
    exact Nat.card_pos.ne' hAcard
  have hIbar : (Nat.card I).factorization r = (Nat.card (Bar2 I)).factorization r := by
    have hcard : Nat.card I = Nat.card (Bar2 I) * Nat.card ↥(CFSG.pCore 2 ↥I) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    have hKzero : (Nat.card ↥(CFSG.pCore 2 ↥I)).factorization r = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd ?_
      rw [hk]
      intro hd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
    rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, hKzero, add_zero]
  rw [hAcard, show (2 ^ n - 1) * (2 ^ n - 1) = (2 ^ n - 1) ^ 2 by ring,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, hIbar, hBar']
  norm_num

theorem factorization_card_A_eq_card_IOf_of_shape
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
    {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L)) :
    (Nat.card A).factorization r = (Nat.card (IOf D p L)).factorization r := by
  classical
  have hr : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hr⟩
  set n := S17.nOf L with hn
  set I := IOf D p L with hI
  have hr2 : r ≠ 2 := by
    intro hr2'
    have hodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
    have : 2 ∣ Nat.card A := hr2' ▸ h.hr.2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hAcard : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) := by
    have h' := card_eq_of_isZModSq h.hAcard
    rw [← hn] at h'
    exact h'
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hAcard
    norm_num at hAcard
    exact Nat.card_pos.ne' hAcard
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  have h2q : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
  have hq1dvd : r ∣ 2 ^ n - 1 := by
    have hdvd : r ∣ (2 ^ n - 1) ^ 2 := by
      have hA : r ∣ Nat.card A := h.hr.2
      rw [hAcard, show (2 ^ n - 1) * (2 ^ n - 1) = (2 ^ n - 1) ^ 2 by ring] at hA
      exact hA
    exact hr.dvd_of_dvd_pow hdvd
  have hq : 2 ^ n ≡ 1 [MOD r] := by
    have h1 : (1 : ℕ) ≡ 2 ^ n [MOD r] :=
      Nat.modEq_of_dvd' Nat.one_le_two_pow hq1dvd
    exact h1.symm
  have hBar : (Nat.card (Bar2 I)).factorization r = 2 * (2 ^ n - 1).factorization r := by
    rcases hshape with hsp | hL2sq | hU3 | hSzsq
    · have hX : Nat.card (Bar2 I) = CFSG.Open.ordBC 2 (2 ^ n) :=
        (CFSG.Timmesfeld.card_statedClassicalModel_two
          (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by decide) hsp)).2.2.1
          rfl
      rw [hX, CFSG.Timmesfeld.Orders.ordBC_two_eq hn1,
        show (2 : ℕ) ^ (n * 4) = (2 ^ n) ^ 4 from pow_mul 2 n 4]
      exact CFSG.GroupTheory.factorization_card_Sp4 hr hr2 h2q hq
    · have hX : Nat.card (Bar2 I) = 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2 :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.card_of_isL2Square_eq hL2sq
      have hpow2 : (2 : ℕ) ^ (2 * n) = (2 ^ n) ^ 2 := by rw [mul_comm, pow_mul]
      rw [hX, hpow2]
      exact CFSG.GroupTheory.factorization_card_L2Square hr hr2 h2q hq
    · obtain ⟨A', B', gA, gB, ⟨e⟩, hL2A, hU3B⟩ := hU3
      haveI : Finite B' := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_PSU3 hU3B
      have hAfac : Nat.card A' = 2 ^ n * (4 ^ n - 1) :=
        CFSG.Quasithin.H13.card_of_lieModel_L2 hn1 hL2A
      have hc := CFSG.LocalAnalysis.EvenBN.GMSK.card_mul_gcd_of_lieModel_PSU3 hU3B
      have hg0 : Nat.gcd 3 (2 ^ n + 1) ≠ 0 := by positivity
      have hu0 : Nat.card B' ≠ 0 := Nat.card_pos.ne'
      have hgz : (Nat.gcd 3 (2 ^ n + 1)).factorization r = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (CFSG.GroupTheory.not_dvd_gcd_three_add_one hr h2q hq)
      have hufac : (Nat.card B').factorization r =
          (((2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 - 1))).factorization r := by
        have hm := congrArg (fun f : ℕ →₀ ℕ => f r) (Nat.factorization_mul hu0 hg0)
        simp only [Finsupp.add_apply] at hm
        rw [hgz, add_zero, hc] at hm
        exact hm.symm
      have hq2pos : 0 < (2 ^ n) ^ 2 - 1 := by
        have h1 : 1 < (2 ^ n) ^ 2 := by
          calc 1 < (2 : ℕ) ^ 2 := by norm_num
            _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2q 2
        omega
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, hAfac,
        show (4 : ℕ) ^ n = (2 ^ n) ^ 2 by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm],
        Nat.factorization_mul (by positivity) hu0, Finsupp.add_apply,
        hufac, CFSG.GroupTheory.factorization_card_U3 hr hr2 h2q hq,
        CFSG.GroupTheory.factorization_card_L2 hr hr2 h2q hq]
      ring
    · obtain ⟨A', B', gA, gB, ⟨e⟩, hSzA, hSzB⟩ := hSzsq
      have hAfac : Nat.card A' = (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
        have hs := (CFSG.Blueprint.LieModel.suzukiModel hSzA).2
        have hc := (CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_suzuki hs).2.2
        simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordSuzuki] using hc
      have hBfac : Nat.card B' = (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
        have hs := (CFSG.Blueprint.LieModel.suzukiModel hSzB).2
        have hc := (CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_suzuki hs).2.2
        simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordSuzuki] using hc
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, hAfac, hBfac, ← pow_two,
        Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
        CFSG.GroupTheory.factorization_card_Sz hr hr2 h2q hq]
      ring
  exact factorization_card_A_eq_card_IOf_of_hBar h (by rw [← hI, ← hn]; exact hBar)

theorem factorization_card_A_eq_card_IOf_of_case13
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G} {B : Subgroup G}
    {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hcase : (IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        S17.SwapsParabolics D.T (IOf D p L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      ((S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
          IsL2Square (Bar2 (IOf D p L)) (S17.nOf L)) ∧
        2 < S17.nOf L ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)])) :
    (Nat.card A).factorization r = (Nat.card (IOf D p L)).factorization r := by
  refine factorization_card_A_eq_card_IOf_of_shape h ?_
  rcases hcase with ⟨hsp, -⟩ | ⟨hprod, -, -, -⟩
  · exact Or.inl hsp
  · rcases hprod with hU3 | hL2
    · exact Or.inr (Or.inr (Or.inl hU3))
    · exact Or.inr (Or.inl hL2)

theorem A_le_normalizer_T_inf_IOf_of_shape {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L))
    (hn3 : 3 ≤ S17.nOf L) (hK : K_BorelOvergroup) :
    A ≤ normalizer ((D.T ⊓ IOf D p L : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := IOf D p L with hI
  set n := S17.nOf L with hn
  set V := D.T ⊓ I with hV
  have hIM : I ≤ D.M := IOf_le_M D p (S17.calLp_subset_calC D p h.hyp.hL).1.le
  have hMI : D.M ≤ normalizer (I : Set G) := le_normalizer_IOf D h.hyp.hL.1
  have hVI : V ≤ I := inf_le_right
  have hVsyl : IsSylowOf 2 V I :=
    D.sylowM.inf_of_le_normalizer hIM hMI
  have hAT1 : A ⊓ D.T = ⊥ := by
    have hodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
    have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
    rw [eq_bot_iff]
    intro x hx
    have hx2 : IsPGroup 2 ↥(A ⊓ D.T) := hT2.to_le inf_le_right
    have hdvd : Nat.card ↥(A ⊓ D.T) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk⟩ := hx2.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ Nat.card A := by
        rw [hk] at hdvd
        exact (dvd_pow_self 2 hk0).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    rw [hk0, pow_zero] at hk
    have := (Subgroup.card_eq_one.mp hk)
    rw [this] at hx
    exact hx
  have hAV : A ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ A ⊓ D.T := ⟨hx.1, hx.2.1⟩
    rw [hAT1] at hx'
    exact hx'

  let π : ↥I →* Bar2 I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = CFSG.pCore 2 ↥I := QuotientGroup.ker_mk' _
  have hVsubsyl : IsSylowOf 2 (V.subgroupOf I) ⊤ := by
    rw [← isSylowOf_map_subtype_iff I]
    have hmap : (⊤ : Subgroup ↥I).map I.subtype = I := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [hmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVI]
    exact hVsyl
  have hKle : (CFSG.pCore 2 ↥I).map I.subtype ≤ V := by
    obtain ⟨S, hS⟩ := hVsyl.exists_sylow_eq_subgroupOf
    have hp : CFSG.pCore 2 ↥I ≤ (S : Subgroup ↥I) :=
      (CFSG.pCore_isPGroup).le_sylow_of_normal S
    calc (CFSG.pCore 2 ↥I).map I.subtype ≤ (S : Subgroup ↥I).map I.subtype :=
          Subgroup.map_mono hp
      _ = (V.subgroupOf I).map I.subtype := by rw [hS]
      _ = V ⊓ I := Subgroup.subgroupOf_map_subtype V I
      _ = V := inf_eq_left.mpr hVI
  have hkerVs : π.ker ≤ V.subgroupOf I := by
    rw [hkerπ]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_map_of_mem I.subtype hx))
  set H : Subgroup G := (A ⊔ D.T) ⊓ I with hH
  have hAH : A ≤ H := fun a ha => ⟨Subgroup.mem_sup_left ha, h.hA ha⟩
  have hVH : V ≤ H := fun x hx =>
    ⟨Subgroup.mem_sup_right hx.1, hVI hx⟩
  have hHle : H ≤ I := inf_le_right
  set Y : Subgroup (Bar2 I) := (H.subgroupOf I).map π with hY
  set Abar : Subgroup (Bar2 I) := (A.subgroupOf I).map π with hAbar
  set Ubar : Subgroup (Bar2 I) := (V.subgroupOf I).map π with hUbar
  have hAbarY : Abar ≤ Y := Subgroup.map_mono (Subgroup.subgroupOf_mono I hAH)
  have hUbarY : Ubar ≤ Y := Subgroup.map_mono (Subgroup.subgroupOf_mono I hVH)
  have hHset : (H : Set G) = (A : Set G) * (V : Set G) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hx1' : x ∈ ((A ⊔ D.T : Subgroup G) : Set G) := hx1
      rw [CFSG.ABGTheoremB.V56.coe_sup_of_permutable h.hAT] at hx1'
      obtain ⟨a, ha, t, ht, rfl⟩ := hx1'
      have htI : t ∈ I := by
        have : t = a⁻¹ * (a * t) := by group
        rw [this]
        exact I.mul_mem (I.inv_mem (h.hA ha)) hx2
      exact ⟨a, ha, t, ⟨ht, htI⟩, rfl⟩
    · rintro ⟨a, ha, v, hv, rfl⟩
      exact ⟨Subgroup.mul_mem_sup ha hv.1, I.mul_mem (h.hA ha) hv.2⟩
  have hHcard : Nat.card H = Nat.card A * Nat.card V := by
    have hc := CFSG.GroupTheory.FT63ChII.card_setMul_mul_card_inf (G := G) A V
    have hbot : Nat.card ↥(A ⊓ V) = 1 := by rw [hAV, Subgroup.card_bot]
    rw [hbot, mul_one] at hc
    rw [← hc]
    exact Nat.card_congr (Set.equivOfEq hHset)
  have hKpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥I) := Nat.card_pos
  have hVcard : Nat.card V = Nat.card Ubar * Nat.card ↥(CFSG.pCore 2 ↥I) := by
    have hc := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf π (V.subgroupOf I)
    have hinf : π.ker ⊓ V.subgroupOf I = π.ker := inf_eq_left.mpr hkerVs
    rw [hinf, ← hUbar, hkerπ] at hc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv] at hc
    exact hc
  have hHimg : Nat.card H = Nat.card Y * Nat.card ↥(CFSG.pCore 2 ↥I) := by
    have hc := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf π (H.subgroupOf I)
    have hinf : π.ker ⊓ H.subgroupOf I = π.ker :=
      inf_eq_left.mpr (hkerVs.trans (Subgroup.subgroupOf_mono I hVH))
    rw [hinf, ← hY, hkerπ] at hc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv] at hc
    exact hc
  have hAbarCard : Nat.card Abar = Nat.card A := by
    have hc := CFSG.GroupTheory.FT63ChII.card_eq_card_map_mul_card_inf π (A.subgroupOf I)
    have hbot : π.ker ⊓ A.subgroupOf I = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxK : (x : ↥I) ∈ CFSG.pCore 2 ↥I := by
        rw [← hkerπ]; exact hx.1
      have hxV : x ∈ V.subgroupOf I :=
        Subgroup.mem_subgroupOf.mpr (hKle (Subgroup.mem_map_of_mem I.subtype hxK))
      have hxA : x ∈ A.subgroupOf I := hx.2
      have hmemA : ((x : ↥I) : G) ∈ A := hxA
      have hmemV : ((x : ↥I) : G) ∈ V := Subgroup.mem_subgroupOf.mp hxV
      have hbot' : ((x : ↥I) : G) ∈ (A ⊓ V : Subgroup G) := ⟨hmemA, hmemV⟩
      rw [hAV] at hbot'
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hbot'))
    rw [hbot, ← hAbar] at hc
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hA).toEquiv] at hc
    rw [hc, Subgroup.card_bot, mul_one]
  have hYU : Nat.card Y = Nat.card A * Nat.card Ubar := by
    apply Nat.mul_right_cancel hKpos
    calc Nat.card Y * Nat.card ↥(CFSG.pCore 2 ↥I) = Nat.card H := hHimg.symm
      _ = Nat.card A * Nat.card V := hHcard
      _ = Nat.card A * (Nat.card Ubar * Nat.card ↥(CFSG.pCore 2 ↥I)) := by rw [hVcard]
      _ = (Nat.card A * Nat.card Ubar) * Nat.card ↥(CFSG.pCore 2 ↥I) := by ring
  have hYdvd : Nat.card Y ∣ Nat.card Ubar * (2 ^ n - 1) ^ 2 := by
    have hA2 : Nat.card A = (2 ^ n - 1) ^ 2 := by
      have h' := card_eq_of_isZModSq h.hAcard
      rw [← hn] at h'
      rw [h']; ring
    rw [hYU, hA2]
    exact dvd_of_eq (mul_comm _ _)
  have hUbarsyl : IsSylowOf 2 Ubar ⊤ := by
    have hc := CFSG.LocalAnalysis.RankThreeTheoremC.isSylowOf_map_hom (p := 2) π hVsubsyl
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hπsurj, ← hUbar] at hc
    simpa using hc
  have hUbarCard : Nat.card Ubar = 2 ^ (Nat.card (Bar2 I)).factorization 2 := by
    rw [hUbarsyl.card_eq, Subgroup.card_top]
  let U : Sylow 2 (Bar2 I) := Sylow.ofCard Ubar hUbarCard
  have hUcoe : (U : Subgroup (Bar2 I)) = Ubar := Sylow.coe_ofCard Ubar hUbarCard
  have hUY : (U : Subgroup (Bar2 I)) ≤ Y := by rw [hUcoe]; exact hUbarY
  have hKN := hK (Bar2 I) n hn3 hshape U Y hUY hYdvd
  rw [hUcoe] at hKN
  have hAbarN : Abar ≤ Subgroup.normalizer (Ubar : Set (Bar2 I)) := hAbarY.trans hKN
  have hAs : A.subgroupOf I ≤ Subgroup.normalizer ((V.subgroupOf I) : Set ↥I) :=
    CFSG.GroupTheory.le_normalizer_of_map_le_normalizer_of_ker_le π hkerVs
      (by simpa [← hAbar, ← hUbar] using hAbarN)
  have hAs' : A.subgroupOf I ≤ (Subgroup.normalizer (V : Set G)).subgroupOf I := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVI] at hAs
    exact hAs
  intro a ha
  have hai : (⟨a, h.hA ha⟩ : ↥I) ∈ A.subgroupOf I := ha
  exact Subgroup.mem_subgroupOf.mp (hAs' hai)

theorem A_le_normalizer_T_inf_IOf {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hcase : (IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        S17.SwapsParabolics D.T (IOf D p L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      ((S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
          IsL2Square (Bar2 (IOf D p L)) (S17.nOf L)) ∧
        2 < S17.nOf L ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]))
    (hK : K_BorelOvergroup) :
    A ≤ normalizer ((D.T ⊓ IOf D p L : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := IOf D p L with hI
  set n := S17.nOf L with hn
  have hn3 : 3 ≤ n := by
    have hAcard : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) := by
      have h' := card_eq_of_isZModSq h.hAcard
      rwa [← hn] at h'
    have hrA : r ∣ Nat.card A := h.hr.2
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at hAcard
      norm_num at hAcard
      exact Nat.card_pos.ne' hAcard
    have hn1 : n ≠ 1 := by
      intro h1
      rw [h1] at hAcard
      norm_num at hAcard
      rw [hAcard, Subgroup.card_bot] at hrA
      exact h.hr.1.not_dvd_one hrA
    rcases hcase with ⟨-, hodd, -⟩ | ⟨-, h2n, -⟩
    · rcases hodd with ⟨k, hk⟩
      omega
    · omega
  have hshape : IsSp4 (Bar2 I) n ∨ IsL2Square (Bar2 I) n ∨
      S17.IsL2U3Product (Bar2 I) n ∨ IsSzSquare (Bar2 I) n := by
    rcases hcase with ⟨hsp, -⟩ | ⟨hprod, -⟩
    · exact Or.inl hsp
    · rcases hprod with hU3 | hL2
      · exact Or.inr (Or.inr (Or.inl hU3))
      · exact Or.inr (Or.inl hL2)
  exact A_le_normalizer_T_inf_IOf_of_shape h hshape hn3 hK

theorem gap19_22_P_of_case13 (D : Data G) {V₀ V : Subgroup G}
    {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hcase : (IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∧ Odd (S17.nOf L) ∧
        S17.SwapsParabolics D.T (IOf D p L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      ((S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
          IsL2Square (Bar2 (IOf D p L)) (S17.nOf L)) ∧
        2 < S17.nOf L ∧ IsPowTwo (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]))
    (hK : K_BorelOvergroup) (E : Subgroup G) :
    Gap19_22_P D V₀ V p L A t B r h E :=
  gap19_22_P_of D h (factorization_card_A_eq_card_IOf_of_case13 h hcase)
    (A_le_normalizer_T_inf_IOf h hcase hK) E

theorem isL2Square_bar2_conjClosure {D : Data G} {L : Subgroup G} {x : G} {n : ℕ}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L) (hL2 : IsL2 (Bar2 L) n) :
    IsL2Square (Bar2 (conjClosure D.M L)) n := by
  classical
  set I : Subgroup G := conjClosure D.M L with hI
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hK
  have hKcal := (conjSubgroup_mem_calC_and_ne hL hxM hXsup hne).1
  have hKne := (conjSubgroup_mem_calC_and_ne hL hxM hXsup hne).2
  have hLKne : L ≠ K := hKne.symm
  have hIeq : I = L ⊔ K := by rw [hI, hK]; exact hXsup
  have hIL : L ≤ I := by rw [hI]; exact TwelveTwentyThree.le_conjClosure D.M L
  have hIK : K ≤ I := by rw [hIeq]; exact le_sup_right
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hL
  have hLcalI : L ∈ calC I := hsubset L (self_mem_conjSetOf D.M L)
  have hKmem : K ∈ conjSetOf D.M L := ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hKcalI : K ∈ calC I := hsubset K hKmem
  let π : ↥I →* Bar2 I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Lbar : Subgroup (Bar2 I) := barImage I L
  let Kbar : Subgroup (Bar2 I) := barImage I K
  have hcomm : ⁅Lbar, Kbar⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (uc22p22l_barImage_commute hLcalI hKcalI hLKne a ha b hb).symm
  have hsup : Lbar ⊔ Kbar = ⊤ := by
    have h1 : (L.subgroupOf I) ⊔ (K.subgroupOf I) = ⊤ := by
      have h2 : (L ⊔ K).subgroupOf I = ⊤ := by rw [hIeq, Subgroup.subgroupOf_self]
      rwa [Subgroup.subgroupOf_sup hIL hIK] at h2
    have hmap : ((L.subgroupOf I) ⊔ (K.subgroupOf I)).map π = ⊤ := by
      rw [h1, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπsurj]
    rwa [Subgroup.map_sup] at hmap
  obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv (L := I) (K := L) hLcalI
  have hLbar2 : IsL2 ↥Lbar n := LieModel.of_mulEquiv eL hL2
  have hK2 : IsL2 (Bar2 K) n := by
    obtain ⟨eK⟩ := uc22p20d_bar2_conj x⁻¹ L
    exact LieModel.of_mulEquiv eK hL2
  obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv (L := I) (K := K) hKcalI
  have hKbar2 : IsL2 ↥Kbar n := LieModel.of_mulEquiv eK hK2
  have hLbarSimple : IsSimpleGroup ↥Lbar :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLbar2
  have hLbarPerf : ⁅Lbar, Lbar⁆ = Lbar := by
    have hp : ⁅(⊤ : Subgroup ↥Lbar), ⊤⁆ = ⊤ :=
      (uc22p22l_barImage_isComponent hLcalI).1.1.commutator_eq_top
    have hmap := congrArg (Subgroup.map Lbar.subtype) hp
    rw [Subgroup.map_commutator] at hmap
    simpa [Subgroup.map_top, Subgroup.range_subtype] using hmap
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_mulEquiv_sup_prod
    (V₁ := Lbar) (V₂ := Kbar) hLbarSimple hLbarPerf hcomm
  have hIso : Bar2 I ≃* ↥Lbar × ↥Kbar :=
    (Subgroup.topEquiv (G := Bar2 I)).symm.trans
      ((MulEquiv.subgroupCongr hsup).symm.trans e)
  exact ⟨↥Lbar, ↥Kbar, inferInstance, inferInstance, ⟨hIso⟩, hLbar2, hKbar2⟩

theorem isSzSquare_bar2_conjClosure {D : Data G} {L : Subgroup G} {x : G} {n : ℕ}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hne : conjClosure D.M L ≠ L) (hL2 : IsSz (Bar2 L) n) :
    IsSzSquare (Bar2 (conjClosure D.M L)) n := by
  classical
  set I : Subgroup G := conjClosure D.M L with hI
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hK
  have hKcal := (conjSubgroup_mem_calC_and_ne hL hxM hXsup hne).1
  have hKne := (conjSubgroup_mem_calC_and_ne hL hxM hXsup hne).2
  have hLKne : L ≠ K := hKne.symm
  have hIeq : I = L ⊔ K := by rw [hI, hK]; exact hXsup
  have hIL : L ≤ I := by rw [hI]; exact TwelveTwentyThree.le_conjClosure D.M L
  have hIK : K ≤ I := by rw [hIeq]; exact le_sup_right
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hL
  have hLcalI : L ∈ calC I := hsubset L (self_mem_conjSetOf D.M L)
  have hKmem : K ∈ conjSetOf D.M L := ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hKcalI : K ∈ calC I := hsubset K hKmem
  let π : ↥I →* Bar2 I := QuotientGroup.mk' (CFSG.pCore 2 ↥I)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Lbar : Subgroup (Bar2 I) := barImage I L
  let Kbar : Subgroup (Bar2 I) := barImage I K
  have hcomm : ⁅Lbar, Kbar⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (uc22p22l_barImage_commute hLcalI hKcalI hLKne a ha b hb).symm
  have hsup : Lbar ⊔ Kbar = ⊤ := by
    have h1 : (L.subgroupOf I) ⊔ (K.subgroupOf I) = ⊤ := by
      have h2 : (L ⊔ K).subgroupOf I = ⊤ := by rw [hIeq, Subgroup.subgroupOf_self]
      rwa [Subgroup.subgroupOf_sup hIL hIK] at h2
    have hmap : ((L.subgroupOf I) ⊔ (K.subgroupOf I)).map π = ⊤ := by
      rw [h1, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπsurj]
    rwa [Subgroup.map_sup] at hmap
  obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv (L := I) (K := L) hLcalI
  have hLbar2 : IsSz ↥Lbar n := LieModel.of_mulEquiv eL hL2
  have hK2 : IsSz (Bar2 K) n := by
    obtain ⟨eK⟩ := uc22p20d_bar2_conj x⁻¹ L
    exact LieModel.of_mulEquiv eK hL2
  obtain ⟨eK, -⟩ := uc22p22l_barImage_equiv (L := I) (K := K) hKcalI
  have hKbar2 : IsSz ↥Kbar n := LieModel.of_mulEquiv eK hK2
  have hLbarSimple : IsSimpleGroup ↥Lbar := uc22p22r_lieModel_isSimple_twistedB2 hLbar2
  have hLbarPerf : ⁅Lbar, Lbar⁆ = Lbar := by
    have hp : ⁅(⊤ : Subgroup ↥Lbar), ⊤⁆ = ⊤ :=
      (uc22p22l_barImage_isComponent hLcalI).1.1.commutator_eq_top
    have hmap := congrArg (Subgroup.map Lbar.subtype) hp
    rw [Subgroup.map_commutator] at hmap
    simpa [Subgroup.map_top, Subgroup.range_subtype] using hmap
  obtain ⟨e⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_mulEquiv_sup_prod
    (V₁ := Lbar) (V₂ := Kbar) hLbarSimple hLbarPerf hcomm
  have hIso : Bar2 I ≃* ↥Lbar × ↥Kbar :=
    (Subgroup.topEquiv (G := Bar2 I)).symm.trans
      ((MulEquiv.subgroupCongr hsup).symm.trans e)
  exact ⟨↥Lbar, ↥Kbar, inferInstance, inferInstance, ⟨hIso⟩, hLbar2, hKbar2⟩

theorem gap19_22_P_of_case2
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r)
    (hcase2 : IOf D p L = conjClosure D.M L ∧ conjClosure D.M L ≠ L ∧
      2 < S17.nOf L ∧
        ((IsL2 (Bar2 L) (S17.nOf L) ∧
            (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
          (IsSz (Bar2 L) (S17.nOf L) ∧
            (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)])))
    (h1742 : S17.R17_42At D V₀ V) (hK : K_BorelOvergroup) (E : Subgroup G) :
    Gap19_22_P D V₀ V p L A t B r h E := by
  have hL : L ∈ calC D.M := h.hyp.hL.1
  have hP : S17.P17_42_2 D L (conjClosure D.M L) p :=
    S17.p42_alt2_of_ne h1742 h.hyp.hp hL hcase2.2.1
  obtain ⟨-, x, hxM, hXsup, hne, -, -⟩ := hP
  have hn3 : 3 ≤ S17.nOf L := by omega
  have hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      S17.IsL2U3Product (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) := by
    rcases hcase2.2.2.2 with ⟨hL2, -⟩ | ⟨hSz, -⟩
    · have hsq := isL2Square_bar2_conjClosure hL hxM hXsup hne hL2
      rw [← hcase2.1] at hsq
      exact Or.inr (Or.inl hsq)
    · have hsq := isSzSquare_bar2_conjClosure hL hxM hXsup hne hSz
      rw [← hcase2.1] at hsq
      exact Or.inr (Or.inr (Or.inr hsq))
  exact gap19_22_P_of D h (factorization_card_A_eq_card_IOf_of_shape h hshape)
    (A_le_normalizer_T_inf_IOf_of_shape h hshape hn3 hK) E

theorem gap19_22_P
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h1742 : S17.R17_42At D V₀ V) (hK : K_BorelOvergroup) :
    ∀ E : Subgroup G, Gap19_22_P D V₀ V p L A t B r h E := by
  intro E
  have hset := h.h1910
  unfold Setting1910 at hset
  rcases hset.2 with h1 | h2 | h3
  · exact gap19_22_P_of_case13 D h (Or.inl h1) hK E
  · exact gap19_22_P_of_case2 D h h2 h1742 hK E
  · exact gap19_22_P_of_case13 D h (Or.inr h3) hK E

theorem nineteen_twentytwo_b
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h171 : S17.R17_1At D V₀ V h.hyp.hyp125)
    (h12 : R19_12At D V₀ V p L A t B r h)
    (h1742 : S17.R17_42At D V₀ V) (hK : K_BorelOvergroup)
    (hgap : Gap19_22 D V₀ V p L A t B r h) :
    R19_22At D V₀ V p L A t B r h :=
  nineteen_twentytwo D h h61 h127 h171 h12 (gap19_22_P D h h1742 hK) hgap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
