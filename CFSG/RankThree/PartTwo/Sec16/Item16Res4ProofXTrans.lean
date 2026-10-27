module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofGen
import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SL447
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofHess
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS163XTransInv : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 1 ≤ m → Sec4.IsoLThreePi X 2 m →
    ¬ (2 ^ m % 9 = 1 ∨ 2 ^ m % 9 = 8) →
    ∀ D : Subgroup X, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    ∀ T : Subgroup X, IsPGroup 2 T → D ≤ Subgroup.normalizer (T : Set X) → T = ⊥

namespace Proof163XTrans

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_le_L (hK : KS163XTransInv) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hD : Sec13Data G A c L) {n : ℕ} (hn1 : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (hmod : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) (hθ1 : aschbacherSolvableCore 3 ↥L = ⊥)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {U : Subgroup G} (hUL : U ≤ L)
    (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G)) : U = ⊥ := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ab := (A.subgroupOf L).map π with hAb
  have hAb9 : Nat.card Ab = 9 := by
    rw [hAb, hπ, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEab : CFSG.Assembly.IsElemAbelian 3 Ab :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
      (isElemAbelian_subgroupOf hD.isElemAbelian)
  set Ub := (U.subgroupOf L).map π with hUb
  have hUb2 : IsPGroup 2 Ub := (hU2.comap_subtype (K := L)).map π
  have hAbU : Ab ≤ Subgroup.normalizer (Ub : Set (↥L ⧸ θ)) := by
    rintro _ ⟨⟨b, hbL⟩, hbA, rfl⟩
    have hbA' : b ∈ A := Subgroup.mem_subgroupOf.mp hbA
    have hbN : (⟨b, hbL⟩ : ↥L) ∈
        Subgroup.normalizer ((U.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hAU hbA') y
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hbN)
  have hUb1 : Ub = ⊥ := hK _ n hn1 hiso hmod Ab hEab hAb9 Ub hUb2 hAbU
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    exact hθ1
  have hsub : U.subgroupOf L = ⊥ := by
    rw [hUb, Subgroup.map_eq_bot_iff_of_injective _ hπinj] at hUb1
    exact hUb1
  rw [eq_bot_iff]
  intro u hu
  have hmem : (⟨u, hUL hu⟩ : ↥L) ∈ U.subgroupOf L := Subgroup.mem_subgroupOf.mpr hu
  rw [hsub, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

theorem le_centralizer_A (hK : KS163XTransInv) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {n : ℕ} (hn1 : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (hmod : ¬ (2 ^ n % 9 = 1 ∨ 2 ^ n % 9 = 8)) (hθ1 : aschbacherSolvableCore 3 ↥L = ⊥)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    {S : Subgroup G} (hSc : S ≤ Subgroup.centralizer ({c} : Set G)) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.centralizer (A : Set G) := by
  have hD := h.toSec13Data
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA
  have hCL : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h.toSec14Std h3
  have hSL : S ⊓ L = ⊥ :=
    eq_bot_of_le_L hK hD hn1 hiso hmod hθ1 h9 inf_le_right (hS2.to_le inf_le_left)
      (Proof169.le_normalizer_inf hAS hD.le_normalizer)
  have hAC : A ≤ Subgroup.centralizer (S : Set G) := by
    rw [hAc]
    refine sup_le ?_ ?_
    · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hSc hs)
    · intro b hb
      obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.mp hb
      refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
      have hzL : s * b * s⁻¹ * b⁻¹ ∈ L :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hCL (hSc hs)) b).mp hbL) (inv_mem hbL)
      have hzS : s * b * s⁻¹ * b⁻¹ ∈ S := by
        have h1 : b * s⁻¹ * b⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.mp (hAS hbA) s⁻¹).mp (inv_mem hs)
        have e : s * b * s⁻¹ * b⁻¹ = s * (b * s⁻¹ * b⁻¹) := by group
        rw [e]
        exact mul_mem hs h1
      have hz : s * b * s⁻¹ * b⁻¹ ∈ S ⊓ L := ⟨hzS, hzL⟩
      rw [hSL, Subgroup.mem_bot] at hz
      calc s * b = s * b * s⁻¹ * b⁻¹ * (b * s) := by group
        _ = b * s := by rw [hz, one_mul]
  exact Subgroup.le_centralizer_iff.mp hAC

omit [Finite G] in
theorem map_subtype_map_conj (X : Subgroup G) (P : Subgroup X) (x : X) :
    (P.map (MulAut.conj x).toMonoidHom).map X.subtype =
      (P.map X.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_conj_of_max {X S T : Subgroup G} {p : ℕ} [Fact p.Prime] (hSX : S ≤ X)
    (hTX : T ≤ X) (hS : IsPGroup p S) (hT : IsPGroup p T)
    (hSmax : ∀ P : Subgroup G, IsPGroup p P → S ≤ P → P ≤ X → P = S)
    (hTmax : ∀ P : Subgroup G, IsPGroup p P → T ≤ P → P ≤ X → P = T) :
    ∃ x ∈ X, T = S.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨P, hSP⟩ := (hS.comap_subtype (K := X)).exists_le_sylow
  obtain ⟨Q, hTQ⟩ := (hT.comap_subtype (K := X)).exists_le_sylow
  have hPS : (P : Subgroup X).map X.subtype = S := by
    refine hSmax _ (P.isPGroup'.map _) ?_ (Subgroup.map_subtype_le _)
    intro s hs
    exact ⟨⟨s, hSX hs⟩, hSP (Subgroup.mem_comap.mpr hs), rfl⟩
  have hQT : (Q : Subgroup X).map X.subtype = T := by
    refine hTmax _ (Q.isPGroup'.map _) ?_ (Subgroup.map_subtype_le _)
    intro t ht
    exact ⟨⟨t, hTX ht⟩, hTQ (Subgroup.mem_comap.mpr ht), rfl⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨x, x.2, ?_⟩
  have hQ : (Q : Subgroup X) = (P : Subgroup X).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hQT, ← hPS, hQ, map_subtype_map_conj]

end Proof163XTrans

open Proof163XTrans Proof169Theta Proof1612Gen

theorem step163XTransH_of
    (h1514 : Item1514R) (hMeets : Step163Meets) (h135 : Item135Simple) (h138 : Item138N)
    (h142 : Concl142R) (hK : KS163XTransInv) : Step163XTransH := by
  intro G _ _ A c L h hL hO h32 hne hΩ a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  obtain ⟨Y, hY⟩ := hne
  obtain ⟨-, -, hprod⟩ := cover_of_isL3TwoPow h (h1514 G A c L h) hMeets h32 hY (hL Y hY)
  obtain ⟨n, hn1, hiso⟩ := h32
  have hz : IsZ3LThreeTwo A c L n := ⟨hn1, hiso, hprod⟩
  obtain ⟨-, h9, hAc⟩ := facts_of_isZ3LThreeTwo hD hz
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨2, n, inferInstance, hn1, hiso⟩
  have hθ := theta_eq_pCore_two_of_item135Simple h135 hD (Or.inl hL3)
  have hθ1 : aschbacherSolvableCore 3 ↥L = ⊥ := by
    rw [hθ]
    rw [CFSG.Open.pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hO
    exact hO
  have hmod := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hn1 hiso hprod
  have hac : Subgroup.zpowers a = Subgroup.zpowers c := by
    rw [hΩ] at ha
    exact ha
  rw [centralizer_singleton_eq_of_zpowers_eq hac]
  have hA3elts : ∀ y ∈ Subgroup.centralizer (A : Set G), y ^ 3 = 1 → y ∈ A := by
    intro y hy hy3
    exact Sec15.mem_of_mem_partTwoF hD.mem_partTwoF hy3 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hy x hx)
  obtain ⟨N, hNC, hCN, hN3, hNall⟩ := Sec4.Item4443SL.exists_normal_complement le_rfl hA3elts
  have hNX : N ≤ xA A :=
    le_pPrimeCoreOf hNC hCN ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
  have hXA : xA A ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  have hAc' : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A)
  have key : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({c} : Set G)) (piOf 2),
      S ≤ xA A ∧ IsPGroup 2 S ∧
        ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ xA A → P = S := by
    intro S hS
    have hSQ := hS.prop
    have hSc : S ≤ Subgroup.centralizer ({c} : Set G) := hSQ.1.2
    have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hSQ.2
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSQ.1.1.1.2.2
    have hSA := le_centralizer_A hK h hn1 hiso hmod hθ1 h9 hAc hSc hS2 hAS
    have hSX : S ≤ xA A := by
      intro s hs
      refine hNX (hNall s (hSA hs) ?_)
      obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
      have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      intro h3
      have h1 := orderOf_dvd_of_pow_eq_one hsk
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow (h3.trans h1))
      omega
    refine ⟨hSX, hS2, fun P hP2 hSP hPX => ?_⟩
    have hPA : P ≤ Subgroup.centralizer (A : Set G) := hPX.trans hXA
    have hPc : P ≤ Subgroup.centralizer ({c} : Set G) := hPA.trans hAc'
    have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
      (Subgroup.le_centralizer_iff.mp hPA).trans (Subgroup.centralizer_le_normalizer _)
    have hP3 : ¬ 3 ∣ Nat.card P := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
      rw [hk]
      intro h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    have hPQ : P ∈ scriptQ A (lB A) := mem_scriptQ_of_concl142 (h142 G A c L h)
      h.zpowers_mem_omegaA ⟨hPc.trans (centralizer_singleton_le_normalizer_zpowers c),
        (isPiSubgroup_piCompl_iff Nat.prime_three P).mpr hP3, hAP⟩
    have hPmem : P ∈ scriptQPi A (lB A) (Subgroup.centralizer ({c} : Set G)) (piOf 2) :=
      ⟨⟨hPQ, hPc⟩, (isPiSubgroup_piOf_iff Nat.prime_two P).mpr hP2⟩
    exact (hS.eq_of_le hPmem hSP).symm
  intro S hS T hT
  obtain ⟨hSX, hS2, hSmax⟩ := key S hS
  obtain ⟨hTX, hT2, hTmax⟩ := key T hT
  obtain ⟨x, hxX, hx⟩ := exists_conj_of_max hSX hTX hS2 hT2 hSmax hTmax
  exact ⟨x, ⟨hxX, (hXA.trans hAc') hxX⟩, hx⟩

namespace Proof163XInv

open CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.RankThree.PartTwo.Sec16.ProofHess
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] {π : Bool} {f : ℕ}

theorem eq_one_of_pow_two_pow_eq_one [CharP K 2] {a : K} {k : ℕ} (h : a ^ 2 ^ k = 1) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h0 : (a - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h0)

theorem charP_two (hK : PiField π 2 f K) : CharP K 2 := by
  have := hK.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Fintype.ofFinite K
  have hc := hK.card
  rw [Nat.card_eq_fintype_card] at hc
  cases π
  · exact charP_of_card_eq_prime_pow (f := 2 * f) (by
      rw [hc]
      change (2 ^ f) ^ 2 = 2 ^ (2 * f)
      rw [← pow_mul, mul_comm])
  · exact charP_of_card_eq_prime_pow (f := f) hc

theorem eq_one_of_commute_two (hK : PiField π 2 f K) (hq : ModThree π (2 ^ f))
    (h9 : ¬ 9 ∣ Nat.card K - 1) {w x : ProjGenLinGroup (Fin 3) K}
    (hwS : w ∈ projImage (slPi π 3 (2 ^ f) K)) (hxS : x ∈ projImage (slPi π 3 (2 ^ f) K))
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) {k : ℕ} (hxk : x ^ 2 ^ k = 1) (hwx : w * x = x * w) :
    x = 1 := by
  have := hK.finite
  have : CharP K 2 := charP_two hK
  have hπ : π = false → UnitaryFieldData 2 f K := fun h => by subst h; exact hK.unitary
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨a, ha⟩ : ∃ a, orderOf x = 2 ^ a :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxk) |>.imp fun _ h => h.2
  have hx3 : Nat.Coprime 3 (orderOf x) := by
    rw [ha]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨y, hyS, rfl⟩ := hwS
  obtain ⟨s, hsS, rfl, hsm⟩ := exists_lift_pow_eq_one hK hxS hx3
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_lift hK h9 hyS hw3
  have hdet : (y : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hyS).2
  have hys : ∀ c : K, (y : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c hc
    apply hw1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      rw [hc, det_zero] at hdet
      exact zero_ne_one hdet
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr (mem_statedScalars_of_eq_smul hc hc0)
  have hy3m : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy3, Units.val_one]
  have hsy : s * y = y * s :=
    commute_of_mk_commute hK hsS hyS hwx hx3.symm hsm
  obtain ⟨P, j, hP, hPD⟩ := exists_normal_form_det_one hτ hτ1 h3 hy3m hdet hys
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, τ ^ 2, 1] with hD
  set Y : Matrix (Fin 3) (Fin 3) K := τ ^ (j : ℕ) • (y : Matrix (Fin 3) (Fin 3) K) with hY
  set Q := P⁻¹ with hQ
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hPdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hsY : (s : Matrix (Fin 3) (Fin 3) K) * Y = Y * s := by
    have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hsy
    simp only [Units.val_mul] at h
    rw [hY, Matrix.mul_smul, Matrix.smul_mul, h]
  set M := Q * (s : Matrix (Fin 3) (Fin 3) K) * P with hM
  have hMD : M * D = D * M := conj_commute hPQ hQP hPD hsY
  have hMdiag := eq_diagonal_of_commute hτ hτ1 hMD
  have hMm : M ^ 2 ^ a = 1 := by
    rw [hM, conj_pow hPQ hQP, ← Units.val_pow_eq_pow_val, ← ha, hsm, Units.val_one,
      Matrix.mul_one, hQP]
  have hentry : ∀ i, M i i = 1 := by
    intro i
    have h := congrFun (congrFun hMm i) i
    rw [hMdiag, diagonal_pow, diagonal_apply_eq, Matrix.one_apply_eq] at h
    exact eq_one_of_pow_two_pow_eq_one h
  have hM1 : M = 1 := by
    rw [hMdiag]
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq, hentry, Matrix.one_apply_eq]
    · rw [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hs1 : (s : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h := unconj hPQ (s : Matrix (Fin 3) (Fin 3) K)
    rw [← hM, hM1, Matrix.mul_one, hPQ] at h
    exact h.symm
  have hs : s = 1 := Units.ext hs1
  rw [hs, map_one]

end Proof163XInv

open Proof163XInv in
theorem ks163XTransInv : KS163XTransInv := by
  intro X _ _ m hm1 hiso hmod D hDE hD9 T hT2 hDT
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model hm1 hiso
  have h9K := not_nine_dvd_card_sub_one hK hmod
  have key : ∀ e : X, e ^ 3 = 1 → e ≠ 1 → ∀ t : X, ∀ k : ℕ, t ^ 2 ^ k = 1 → e * t = t * e →
      t = 1 := by
    intro e he3 he1 t k htk het
    have h := eq_one_of_commute_two hK hq h9K (φ e).2 (φ t).2
      (by rw [← Subgroup.coe_pow, ← map_pow, he3, map_one, Subgroup.coe_one])
      (fun h1 => he1 (φ.injective (Subtype.ext (by rw [h1, map_one, Subgroup.coe_one]))))
      (by rw [← Subgroup.coe_pow, ← map_pow, htk, map_one, Subgroup.coe_one])
      (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, het])
    exact φ.injective (Subtype.ext (by rw [h, map_one, Subgroup.coe_one]))
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 3
    Nat.prime_three D T (fun d => Subtype.ext (by simpa using hDE.2 d.1 d.2))
    (by rw [hD9]; norm_num) hT3 hDT
  rw [hgen]
  refine iSup_eq_bot.mpr fun d => iSup_eq_bot.mpr fun hd1 => ?_
  rw [eq_bot_iff]
  rintro t ⟨htT, htC⟩
  obtain ⟨k, hk⟩ := hT2 ⟨t, htT⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine Subgroup.mem_bot.mpr (key d (hDE.2 d.1 d.2) (fun h => hd1 (Subtype.ext h)) t k htk ?_)
  exact (Subgroup.mem_centralizer_singleton_iff.mp htC).symm

theorem step163XTransH_of_kfact
    (h1514 : Item1514R) (hMeets : Step163Meets) (h135 : Item135Simple) (h138 : Item138N)
    (h142 : Concl142R) : Step163XTransH :=
  step163XTransH_of h1514 hMeets h135 h138 h142 ks163XTransInv

end CFSG.RankThree.PartTwo.Sec16
