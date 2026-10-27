module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Skel
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Statements
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Cent
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Eight
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
import CFSG.Models.PGLSimple
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.GorensteinWalter
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem center_eq_bot_of_mulEquiv_tools {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hg' : e g ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg x]
  rw [h, Subgroup.mem_bot] at hg'
  rw [Subgroup.mem_bot]
  exact e.injective (hg'.trans (map_one e).symm)

private theorem false_of_orderOf_eq_three {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsPGroup 2 H) {y : G} (hy : y ∈ H) (h3 : orderOf y = 3) : False := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hH ⟨y, hy⟩
  rw [Subgroup.orderOf_mk, h3] at hk
  rcases k with _ | k
  · norm_num at hk
  · have h2 : 2 ∣ 3 := hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)
    omega

theorem isSimpleGroup_and_center_eq_bot_of_L2 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hq : 9 < p ^ f)
    (e : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p f)) :
    IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ∧
      Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hsimp := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField p f) le_rfl
    (Or.inr (by rw [hcard]; omega)) (Or.inr (by rw [hcard]; omega))
  exact ⟨e.isSimpleGroup, center_eq_bot_of_mulEquiv_tools
    (e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p f)))
    (psl2_center_eq_bot (GaloisField p f))⟩

theorem exists_conjAct_psl2 (h : Hyp1411 X L S) {F : Type} [Field F]
    (ε : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≃* PSL2 F)
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥) :
    ∃ Φ : X ⧸ CFSG.pPrimeCore 3 X →* MulAut (PSL2 F), Function.Injective Φ ∧
      ∀ (y : X ⧸ CFSG.pPrimeCore 3 X) (n : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))),
        ((ε.symm (Φ y (ε n)) : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
          X ⧸ CFSG.pPrimeCore 3 X) = y * n * y⁻¹ := by
  revert ε hZ
  set K := CFSG.pPrimeCore 3 X with hK
  set π := QuotientGroup.mk' K with hπ
  intro ε hZ
  haveI : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  have hF : CFSG.generalizedFitting (X ⧸ K) = L.map π := h.2.2.2.1
  let Φ : X ⧸ K →* MulAut (PSL2 F) := (MulAut.congr ε).toMonoidHom.comp MulAut.conjNormal
  have hΦ : ∀ (y : X ⧸ K) (n : ↥(L.map π)),
      ((ε.symm (Φ y (ε n)) : ↥(L.map π)) : X ⧸ K) = y * n * y⁻¹ := by
    intro y n
    have e1 : Φ y (ε n) = ε (MulAut.conjNormal y n) := by
      show (MulAut.congr ε (MulAut.conjNormal y)) (ε n) = _
      simp [MulAut.congr_apply]
    rw [e1, MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]
  refine ⟨Φ, ?_, hΦ⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  have hcent : y ∈ Subgroup.centralizer (L.map π : Set (X ⧸ K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := hΦ y ⟨n, hn⟩
    rw [hy, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    change n = y * n * y⁻¹ at h1
    rw [eq_mul_inv_iff_mul_eq] at h1
    exact h1
  have hyL : y ∈ L.map π := by
    rw [← hF]
    exact CFSG.centralizer_generalizedFitting_le _ (by rw [hF]; exact hcent)
  have hzc : (⟨y, hyL⟩ : ↥(L.map π)) ∈ Subgroup.center ↥(L.map π) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcent g g.2)
  rw [hZ, Subgroup.mem_bot] at hzc
  exact congrArg Subtype.val hzc

theorem orderOf_mk_eq_three_of_pPrimeCore_eq (hKQ : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {x : X}
    (hx : orderOf x = 3) : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) = 3 := by
  have hx3 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) ^ 3 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  refine orderOf_eq_prime hx3 fun h1 => ?_
  have hxK : x ∈ CFSG.pCore 2 X := by
    rw [← hKQ]
    exact (QuotientGroup.eq_one_iff x).mp h1
  exact false_of_orderOf_eq_three CFSG.pCore_isPGroup hxK hx

theorem mem_map_normalizer_of_mem_normalizer (hKQ : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X)
    {x : X} (hx : orderOf x = 3) {y : X}
    (hy : QuotientGroup.mk' (CFSG.pPrimeCore 3 X) y ∈ Subgroup.normalizer
      (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) :
        Set (X ⧸ CFSG.pPrimeCore 3 X))) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 X) y ∈
      (Subgroup.normalizer (Subgroup.zpowers x : Set X)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  have hx3 := orderOf_mk_eq_three_of_pPrimeCore_eq hKQ hx
  revert hKQ hx3 hy
  set K := CFSG.pPrimeCore 3 X with hK
  set π := QuotientGroup.mk' K with hπ
  intro hKQ hy hx3
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective K
  set P : Subgroup X := (zpowers (π x)).comap π with hP
  have hKP : K ≤ P := fun k hk => by
    have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [hP, mem_comap, hk1]
    exact one_mem _
  have hZP : zpowers x ≤ P := by
    rw [zpowers_le, hP, mem_comap]
    exact mem_zpowers _
  have hyP : y ∈ normalizer (P : Set X) := by
    rw [mem_normalizer_iff]
    intro g
    rw [hP, mem_comap, mem_comap, map_mul, map_mul, map_inv]
    exact mem_normalizer_iff.mp hy (π g)
  have hPcard : Nat.card P = 3 * Nat.card K := by
    have h1 : K.relIndex P = Nat.card (P.map π) := by
      rw [← relIndex_ker, QuotientGroup.ker_mk']
    have h2 : P.map π = zpowers (π x) := map_comap_eq_self_of_surjective hsurj _
    have := Subgroup.relIndex_mul_card (H := K) (K := P)
    rw [inf_eq_left.mpr hKP, h1, h2, Nat.card_zpowers, hx3] at this
    exact this.symm
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
    (show IsPGroup 2 ↥(CFSG.pPrimeCore 3 X) by rw [hKQ]; exact CFSG.pCore_isPGroup)
  have ha' : Nat.card K = 2 ^ a := ha
  have hfac : (Nat.card P).factorization 3 = 1 := by
    rw [hPcard, ha', Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (fun h3 => by
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
        omega)]
  have hS : Nat.card (zpowers x) = 3 ^ (Nat.card P).factorization 3 := by
    rw [Nat.card_zpowers, hx, hfac, pow_one]
  obtain ⟨g, hgP, hg⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1020_frattini_conj
    (p := 3) hZP hS hyP
  have hπg : π g ∈ (zpowers x).map π := by
    rw [MonoidHom.map_zpowers]
    exact hgP
  have h1 : π g ∈ (normalizer (zpowers x : Set X)).map π :=
    map_mono le_normalizer hπg
  have h2 : π (g⁻¹ * y) ∈ (normalizer (zpowers x : Set X)).map π := mem_map_of_mem π hg
  have := Subgroup.mul_mem _ h1 h2
  rwa [← map_mul, mul_inv_cancel_left] at this

theorem commute_mk_of_conj_mem_zpowers (hS2 : IsPGroup 2 S) {x : X}
    (hx3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) = 3)
    (hxS : x ∈ Subgroup.normalizer (S : Set X)) {s : X} (hs : s ∈ S)
    (hsx : QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s * QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s)⁻¹ ∈
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x)) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s * QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x * QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have hy3 : (π x) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (π x)
    rwa [hx3] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsx
  have hmod : (π x) ^ k = (π x) ^ (k % (3 : ℕ)) := zpow_eq_zpow_emod' k hy3
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  ·
    exfalso
    rw [hmod, show ((3 : ℕ) : ℤ) = 3 from rfl, h0, zpow_zero] at hk
    have h1 : π s * π x = π s := mul_inv_eq_one.mp hk.symm
    have : π x = 1 := (mul_eq_left.mp h1)
    rw [this, orderOf_one] at hx3
    omega
  · rw [hmod, show ((3 : ℕ) : ℤ) = 3 from rfl, h1, zpow_one] at hk
    exact mul_inv_eq_iff_eq_mul.mp hk.symm
  ·
    exfalso
    rw [hmod, show ((3 : ℕ) : ℤ) = 3 from rfl, h2, zpow_two] at hk
    have hcomm : π (s * (x * s⁻¹ * x⁻¹)) = π x := by
      have : π (s * (x * s⁻¹ * x⁻¹)) = (π s * π x * (π s)⁻¹) * (π x)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [this, ← hk]
      group
    have hmem : s * (x * s⁻¹ * x⁻¹) ∈ S :=
      S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp hxS s⁻¹).mp (S.inv_mem hs))
    exact false_of_orderOf_eq_three (hS2.map π) ⟨_, hmem, hcomm⟩ hx3

theorem relIndex_le_four_of_commute (h : Hyp1411 X L S)
    (hKQ : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {F : Type} [Field F] [Finite F]
    (hF2 : ringChar F ≠ 2) (hF3 : ringChar F ≠ 3)
    (ε : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≃* PSL2 F)
    (hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥)
    {x : X} (hxL : x ∈ L) (hx3 : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) = 3)
    (hcomm : ∀ s ∈ S, QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s *
        QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x * QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s)
    {A : Subgroup X} (hAS : A ≤ S) (hA : Sec3.IsElemTwo A) :
    (CFSG.pCore 2 X).relIndex A ≤ 4 ∧ ((CFSG.pCore 2 X).relIndex A = 4 →
      (∃ t ∈ A, t ∉ CFSG.pCore 2 X ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t ∈
        L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ∧
      ∃ σ : F ≃+* F, σ ≠ 1 ∧ σ * σ = 1) := by
  revert hKQ ε hZ hx3 hcomm
  set K := CFSG.pPrimeCore 3 X with hK
  set π := QuotientGroup.mk' K with hπ
  intro hKQ ε hZ hx3 hcomm
  obtain ⟨Φ, hΦinj, hΦ⟩ := exists_conjAct_psl2 h ε hZ
  set x₀ : ↥(L.map π) := ⟨π x, mem_map_of_mem π hxL⟩ with hx₀
  have hxh : orderOf (ε x₀) = 3 := by
    rw [MulEquiv.orderOf_eq, hx₀, Subgroup.orderOf_mk]
    exact hx3
  set E : Subgroup (MulAut (PSL2 F)) := (A.map π).map Φ with hE
  have hE2 : ∀ α ∈ E, α * α = 1 := by
    rintro α ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, hA.2 a ha, map_one, map_one]
  have hEx : ∀ α ∈ E, α (ε x₀) = ε x₀ := by
    rintro α ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have h1 := hΦ (π a) x₀
    have h2 : π a * (x₀ : X ⧸ K) * (π a)⁻¹ = π x :=
      mul_inv_eq_iff_eq_mul.mpr (hcomm a (hAS ha))
    rw [h2] at h1
    exact (MulEquiv.symm_apply_eq ε).mp (Subtype.ext h1)
  have hrel : (CFSG.pCore 2 X).relIndex A = Nat.card E := by
    rw [hE, Subgroup.card_map_of_injective hΦinj, ← hKQ, ← relIndex_ker, QuotientGroup.ker_mk']
  obtain ⟨hle, hfour⟩ := card_le_four_of_forall_apply_eq hF2 hF3 hxh E hE2 hEx
  rw [← hrel] at hle hfour
  refine ⟨hle, fun h4 => ?_⟩
  obtain ⟨⟨α, hαE, hα1, y, hαy⟩, σ, hσ1, hσ2⟩ := hfour h4
  refine ⟨?_, σ, hσ1, hσ2⟩
  obtain ⟨_, ⟨a, haA, rfl⟩, rfl⟩ := hαE
  have hΦℓ : Φ ((ε.symm y : ↥(L.map π)) : X ⧸ K) = MulAut.conj y := by
    ext z
    obtain ⟨n, rfl⟩ := ε.surjective z
    apply ε.symm.injective
    apply Subtype.ext
    rw [hΦ, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rfl
  have hπa : π a = ((ε.symm y : ↥(L.map π)) : X ⧸ K) := hΦinj (hαy.trans hΦℓ.symm)
  refine ⟨a, haA, fun haQ => hα1 ?_, hπa ▸ (ε.symm y).2⟩
  have haK : a ∈ K := by rw [hK, hKQ]; exact haQ
  have : π a = 1 := (QuotientGroup.eq_one_iff a).mpr haK
  rw [this, map_one]

theorem noSmallEight1412_of_inner (h : Hyp1411 X L S)
    (hKQ : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hq : 9 < p ^ f)
    (e : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p f))
    {σ : GaloisField p f ≃+* GaloisField p f} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    {t : X} (htt : t * t = 1) (htQ : t ∉ CFSG.pCore 2 X)
    (htL : QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t ∈
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) :
    NoSmallEight1412 X L t := by
  obtain ⟨hsimp, -⟩ := isSimpleGroup_and_center_eq_bot_of_L2 hp2 hq e
  have hp' : p.Prime := Fact.out
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  obtain ⟨m, hm⟩ := even_of_ringEquiv hp' hcard hσ1 hσ2
  have hm0 : m ≠ 0 := by omega
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp' (by norm_num)
    have := hp'.two_le
    omega
  have hpodd : Odd p := hp'.odd_of_ne_two hp2
  have hrodd : Odd (p ^ m) := hpodd.pow
  have hr5 : 5 ≤ p ^ m := hp5.trans (Nat.le_self_pow hm0 p)
  have hqr : p ^ f = (p ^ m) ^ 2 := by
    rw [hm, ← two_mul, pow_mul', sq]
  letI : Fintype (GaloisField p f) := Fintype.ofFinite _
  classical
  have hqc : Fintype.card (GaloisField p f) = (p ^ m) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard, hqr]
  have hchar : ringChar (GaloisField p f) = p := ringChar.eq _ p
  have hF2 : ringChar (GaloisField p f) ≠ 2 := by rw [hchar]; exact hp2
  have hsq : IsSquare (-1 : GaloisField p f) := by
    rw [FiniteField.isSquare_neg_one_iff, hqc]
    obtain ⟨k, hk⟩ := hrodd
    rw [hk]
    have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
    omega
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  set ε : ↥(L.map π) ≃* PSL2 (GaloisField p f) :=
    e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p f)) with hε
  set t₀ : ↥(L.map π) := ⟨π t, htL⟩ with ht₀
  have hπt1 : π t ≠ 1 := fun h1 => htQ (by
    rw [← hKQ]
    exact (QuotientGroup.eq_one_iff t).mp h1)
  have ht₀2 : orderOf t₀ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change π t ^ 2 = 1
      rw [pow_two, ← map_mul, htt, map_one]
    · intro h1
      exact hπt1 (congrArg Subtype.val h1)
  have hz : orderOf (ε t₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht₀2
  obtain ⟨g, hg⟩ := exists_orderOf_mul_conj_eq_of_orderOf_eq_two hF2
    (by rw [hqc]; nlinarith) hsq hz
  obtain ⟨ℓ, hℓ, hℓg⟩ := Subgroup.mem_map.mp (ε.symm g).2
  obtain ⟨r, k, hr, hr2, hk, hdvd, h6⟩ := exists_primePow_dvd_sq_add_one_div_two hrodd hr5
  refine noSmallEight1412_of_dvd_orderOf h hsimp htt hℓ hr hr2 hk h6 ?_
  have himg : π (t * (ℓ * t * ℓ⁻¹)) =
      ((ε.symm (ε t₀ * (g * ε t₀ * g⁻¹)) : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    rw [map_mul, map_mul, map_mul, map_inv, hℓg]
    simp [ht₀]
  rw [himg, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg, hqc]
  exact hdvd

end CFSG.RankThree.PartTwo.Sec20
