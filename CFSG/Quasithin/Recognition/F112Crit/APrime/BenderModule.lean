module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.BenderVertex
public import CFSG.Quasithin.Recognition.F112Crit.APrime.NoSmallOffender
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Offenders
public import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

private theorem exists_odd_pow_isTwoElement [Finite G] (h : G) :
    ∃ e : ℕ, Odd e ∧ ∃ k : ℕ, (h ^ e) ^ 2 ^ k = 1 := by
  obtain ⟨k, e, he, hk⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.mp (orderOf_pos h))
  have hepos : 0 < e := by
    obtain ⟨t, ht⟩ := he
    omega
  refine ⟨e, he, k, ?_⟩
  have hord : orderOf (h ^ e) = 2 ^ k := by
    rw [orderOf_pow, hk, Nat.gcd_mul_left_left, Nat.mul_div_left _ hepos]
  rw [← hord]
  exact pow_orderOf_eq_one _

private theorem autOnK_central_quotient [Finite G] {H K V : Subgroup G}
    (hB : BenderVertex H K) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G)) :
    Group.IsPerfect ↥(autOn K V) ∧
      Odd (Nat.card (Subgroup.center ↥(autOn K V))) ∧
      ((∃ a : ℕ, 1 ≤ a ∧
          Nonempty (↥(autOn K V) ⧸ Subgroup.center ↥(autOn K V) ≃* CFSG.Open.Sz a)) ∨
        (∃ f : ℕ, 2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
          Nat.card F = (2 ^ f) ^ 2 ∧
            Nonempty (↥(autOn K V) ⧸ Subgroup.center ↥(autOn K V) ≃*
              CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ f) F)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := hB.le.trans hHV
  let ψ : ↥K →* ↥(autOn K V) :=
    ((conjAct V).comp (Subgroup.inclusion hKN)).codRestrict (autOn K V)
      (fun k => AutOn.conjAct_mem_autOn ((Subgroup.inclusion hKN) k) k.2)
  have hψs : Function.Surjective ψ := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hnK, rfl⟩ := AutOn.mem_autOn_iff.1 ha
    exact ⟨⟨n, hnK⟩, rfl⟩
  have hψker : ψ.ker = (K ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hk
      have hk' : conjAct V ((Subgroup.inclusion hKN) k) = 1 := congrArg Subtype.val hk
      refine ⟨k.2, ?_⟩
      simpa using (AutOn.conjAct_eq_one_iff ((Subgroup.inclusion hKN) k)).mp hk'
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      exact (AutOn.conjAct_eq_one_iff ((Subgroup.inclusion hKN) k)).mpr (by simpa using hc)
  have hcore_le : CFSG.pCore 2 ↥K ≤ ψ.ker := by
    intro k hk
    rw [hψker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨k.2, ?_⟩
    have hk' : k ∈ (pCoreOf 2 K).subgroupOf K := by
      rwa [CFSG.openPCoreOf_subgroupOf]
    have hkK : (k : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp hk'
    have hKH : pCoreOf 2 K ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hB.le)
        (hB.normalizes.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact hQV (hKH hkK)
  let φ : oTwoQuot ↥K →* ↥(autOn K V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ hcore_le
  have hφs : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective _ ψ hψs hcore_le
  have hLne : autOn K V ≠ ⊥ :=
    autOn_ne_bot_of_not_le_centralizer hKN hKV
  have hφker_ne : φ.ker ≠ ⊤ := by
    intro htop
    apply hLne
    rw [eq_bot_iff]
    intro a ha
    obtain ⟨x, hx⟩ := hφs ⟨a, ha⟩
    have hxker : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
    rw [MonoidHom.mem_ker] at hxker
    rw [Subgroup.mem_bot]
    have h1 : (⟨a, ha⟩ : ↥(autOn K V)) = 1 := by rw [← hx, hxker]
    exact congrArg Subtype.val h1
  have hφkerZ : φ.ker ≤ Subgroup.center (oTwoQuot ↥K) :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hB.quasisimple φ.normal_ker).resolve_left
      hφker_ne
  have hcomap := CFSG.LocalCores.comap_center_eq_of_perfect hB.quasisimple.1 φ hφs hφkerZ
  have hperf : Group.IsPerfect ↥(autOn K V) := by
    haveI : Group.IsPerfect (oTwoQuot ↥K) := hB.quasisimple.1
    exact Group.IsPerfect.ofSurjective (f := φ) hφs
  have hcenter : Subgroup.center ↥(autOn K V) =
      (Subgroup.center (oTwoQuot ↥K)).map φ := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hφs]
  have hodd : Odd (Nat.card (Subgroup.center ↥(autOn K V))) := by
    rw [hcenter]
    exact hB.odd_center.of_dvd_nat (Subgroup.card_map_dvd _ φ)
  have hc : Subgroup.center (oTwoQuot ↥K) =
      ((QuotientGroup.mk' (Subgroup.center ↥(autOn K V))).comp φ).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : (oTwoQuot ↥K) ⧸ Subgroup.center (oTwoQuot ↥K) ≃*
      ↥(autOn K V) ⧸ Subgroup.center ↥(autOn K V) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        ((QuotientGroup.mk' (Subgroup.center ↥(autOn K V))).comp φ)
        ((QuotientGroup.mk'_surjective _).comp hφs))
  refine ⟨hperf, hodd, ?_⟩
  rcases hB.type with ⟨a, ha, ⟨eK⟩⟩ | ⟨f, hf, F, hFld, hFin, hF, ⟨eK⟩⟩
  · exact Or.inl ⟨a, ha, ⟨e.symm.trans eK⟩⟩
  · exact Or.inr ⟨f, hf, F, hFld, hFin, hF, ⟨e.symm.trans eK⟩⟩

private theorem autOn_inf_centralizer_eq_one_of_two_pow [Finite G] {H K V : Subgroup G}
    (hB : BenderVertex H K) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H)
    {σ : MulAut V} (hσX : σ ∈ autOn H V)
    (hσC : σ ∈ Subgroup.centralizer (autOn K V : Set (MulAut V)))
    (hσ2 : ∃ m : ℕ, σ ^ 2 ^ m = 1) : σ = 1 := by
  classical
  obtain ⟨n, hnN, hnH, hnσ⟩ := AutOn.mem_autOn_iff_exists.mp hσX
  let n' : Subgroup.normalizer (V : Set G) := ⟨n, hnN⟩
  have hnσ' : conjAct V n' = σ := hnσ
  subst σ
  obtain ⟨e, he, k, hk⟩ := exists_odd_pow_isTwoElement n
  let x : G := n ^ e
  have hxH : x ∈ H := H.pow_mem hnH e
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := hHV hxH
  have hconj : (conjAct V n') ^ e = conjAct V ⟨x, hxN⟩ := by
    rw [← map_pow]
    exact congrArg (conjAct V) (Subtype.ext rfl)
  have hcomm : ∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro y hyK
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := (hB.le.trans hHV) hyK
    have hlL : conjAct V ⟨y, hyN⟩ ∈ autOn K V :=
      AutOn.conjAct_mem_autOn ⟨y, hyN⟩ hyK
    have hcomm_l : Commute (conjAct V ⟨y, hyN⟩) (conjAct V n') :=
      Subgroup.mem_centralizer_iff.mp hσC _ hlL
    have hcomm_e : Commute (conjAct V ⟨y, hyN⟩) ((conjAct V n') ^ e) :=
      hcomm_l.pow_right e
    let c : G := y * x * y⁻¹ * x⁻¹
    have hcN : c ∈ Subgroup.normalizer (V : Set G) := by
      dsimp [c]
      exact ((Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem
          ((Subgroup.normalizer (V : Set G)).mul_mem hyN hxN)
          ((Subgroup.normalizer (V : Set G)).inv_mem hyN))
        ((Subgroup.normalizer (V : Set G)).inv_mem hxN))
    have hmap : conjAct V ⟨c, hcN⟩ =
        conjAct V ⟨y, hyN⟩ * (conjAct V n') ^ e * (conjAct V ⟨y, hyN⟩)⁻¹ *
          ((conjAct V n') ^ e)⁻¹ := by
      rw [show (⟨c, hcN⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹ * ⟨x, hxN⟩⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hconj]
    have hone : conjAct V ⟨c, hcN⟩ = 1 := by
      rw [hmap, hcomm_e.eq]
      group
    have hcC : c ∈ Subgroup.centralizer (V : Set G) :=
      (AutOn.conjAct_eq_one_iff ⟨c, hcN⟩).mp hone
    simpa [c] using hcC
  have hxQ : x ∈ pCoreOf 2 H := hcore x hxH ⟨k, by simpa [x] using hk⟩ hcomm
  have hxCV : x ∈ Subgroup.centralizer (V : Set G) := hQV hxQ
  have hxconj : conjAct V ⟨x, hxN⟩ = 1 :=
    (AutOn.conjAct_eq_one_iff ⟨x, hxN⟩).mpr hxCV
  have hσe : (conjAct V n') ^ e = 1 := by rw [hconj, hxconj]
  obtain ⟨m, hm⟩ := hσ2
  have hdvd1 : orderOf (conjAct V n') ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hdvd2 : orderOf (conjAct V n') ∣ e := orderOf_dvd_of_pow_eq_one hσe
  have hcop : Nat.Coprime (2 ^ m) e :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr he)
  have hone : orderOf (conjAct V n') = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  exact orderOf_eq_one_iff.mp hone

private theorem autOn_inf_centralizer_le [Finite G] {H K V : Subgroup G}
    (hB : BenderVertex H K) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H) :
    autOn H V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut V)) ≤ autOn K V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup (MulAut V) :=
    autOn H V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut V))
  have hYodd : Odd (Nat.card ↥Y) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    obtain ⟨z, hzord⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.mp heven)
    have hzX : (z : MulAut V) ∈ autOn H V := z.2.1
    have hzC : (z : MulAut V) ∈
        Subgroup.centralizer (autOn K V : Set (MulAut V)) := z.2.2
    have hz2 : (z : MulAut V) ^ 2 ^ 1 = 1 := by
      have h := pow_orderOf_eq_one (z : MulAut V)
      rw [Subgroup.orderOf_coe, hzord] at h
      simpa using h
    have hz1 : (z : MulAut V) = 1 :=
      autOn_inf_centralizer_eq_one_of_two_pow hB hHV hQV hcore hzX hzC ⟨1, hz2⟩
    have hzord1 : orderOf z = 1 := by
      rw [← Subgroup.orderOf_coe z, hz1, orderOf_one]
    omega
  intro σ hσY
  have hσX : σ ∈ autOn H V := hσY.1
  have hσC : σ ∈ Subgroup.centralizer (autOn K V : Set (MulAut V)) := hσY.2
  have hσodd : Odd (orderOf σ) := by
    have h := hYodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Y hσY)
    simpa using h
  obtain ⟨n, hnN, hnH, hnσ⟩ := AutOn.mem_autOn_iff_exists.mp hσX
  let n' : Subgroup.normalizer (V : Set G) := ⟨n, hnN⟩
  have hnσ' : conjAct V n' = σ := hnσ
  subst σ
  obtain ⟨k, hk⟩ := hB.two_quot n hnH
  have hpowL : (conjAct V n') ^ 2 ^ k ∈ autOn K V := by
    rw [← map_pow]
    exact AutOn.conjAct_mem_autOn (n' ^ 2 ^ k) (by simpa using hk)
  have hmem : conjAct V n' ∈ Subgroup.zpowers ((conjAct V n') ^ 2 ^ k) :=
    mem_zpowers_pow_iff.mpr (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hσodd))
  exact Subgroup.zpowers_le.mpr hpowL hmem

private theorem isElemAbelian2_autOn_of_commutator_square {P V Q : Subgroup G}
    (hV : IsElemAbelian 2 V) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hQV : Q ≤ Subgroup.centralizer (V : Set G))
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Q)
    (hsq : ∀ x ∈ P, x ^ 2 ∈ Q) :
    @IsElemAbelian2 ↥V (commGroupOfElemAbelian hV) (autOn P V) := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  constructor
  · intro a ha b hb
    obtain ⟨x, hxN, hxP, rfl⟩ := AutOn.mem_autOn_iff_exists.mp ha
    obtain ⟨y, hyN, hyP, rfl⟩ := AutOn.mem_autOn_iff_exists.mp hb
    let c : G := x * y * x⁻¹ * y⁻¹
    have hcN : c ∈ Subgroup.normalizer (V : Set G) := by
      dsimp [c]
      exact ((Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem
          ((Subgroup.normalizer (V : Set G)).mul_mem hxN hyN)
          ((Subgroup.normalizer (V : Set G)).inv_mem hxN))
        ((Subgroup.normalizer (V : Set G)).inv_mem hyN))
    have hc1 : conjAct V ⟨c, hcN⟩ = 1 :=
      (AutOn.conjAct_eq_one_iff ⟨c, hcN⟩).mpr (hQV (hcomm x hxP y hyP))
    have heq : (⟨x, hxN⟩ * ⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨c, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩) := by
      apply Subtype.ext
      dsimp [c]
      group
    calc conjAct V ⟨x, hxN⟩ * conjAct V ⟨y, hyN⟩
        = conjAct V (⟨x, hxN⟩ * ⟨y, hyN⟩) := (map_mul _ _ _).symm
      _ = conjAct V (⟨c, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩)) := by rw [heq]
      _ = conjAct V ⟨y, hyN⟩ * conjAct V ⟨x, hxN⟩ := by
        rw [map_mul, hc1, one_mul, map_mul]
  · intro a ha
    obtain ⟨x, hxN, hxP, rfl⟩ := AutOn.mem_autOn_iff_exists.mp ha
    rw [← map_pow]
    have heq : (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 =
        ⟨x ^ 2, (Subgroup.normalizer (V : Set G)).pow_mem hxN 2⟩ := Subtype.ext rfl
    rw [heq]
    exact (AutOn.conjAct_eq_one_iff _).mpr (hQV (hsq x hxP))

private theorem inf_centralizer_eq_inf_pCoreOf [Finite G] {H K V P : Subgroup G}
    (hB : BenderVertex H K) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H)
    (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    P ⊓ Subgroup.centralizer (V : Set G) = P ⊓ pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · intro x hx
    refine ⟨hx.1, hcore x (hPH hx.1) ?_ ?_⟩
    · obtain ⟨k, hk⟩ := hP ⟨x, hx.1⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro y hy
      have hxCV : x ∈ Subgroup.centralizer (V : Set G) := hx.2
      have hzle : Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set G) :=
        Subgroup.zpowers_le.mpr hxCV
      have hyC : y * x * y⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
        CFSG.GroupTheory.conj_mem_centralizer_of_le_normalizer
          (A := Subgroup.zpowers x) (B := K) (K := V) (hB.le.trans hHV) hzle y hy x
          (Subgroup.mem_zpowers x)
      exact (Subgroup.centralizer (V : Set G)).mul_mem hyC
        ((Subgroup.centralizer (V : Set G)).inv_mem hxCV)
  · intro x hx
    exact ⟨hx.1, hQV hx.2⟩

theorem BenderVertex.two_mul_card_lt_index_fixV_of_core
    [Finite G] {H K V : Subgroup G} (hB : BenderVertex H K) (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H) :
    ∀ A : Subgroup (MulAut ↥V), A ≤ autOn H V → A ≠ ⊥ →
      @IsElemAbelian2 ↥V (commGroupOfElemAbelian hV) A →
      2 * Nat.card A < (@fixV ↥V (commGroupOfElemAbelian hV) A).index := by
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  intro A hAX hA hAe
  have hV' : ∀ v : ↥V, v * v = 1 := by
    intro v
    apply Subtype.ext
    have h := hV.2 v v.2
    simpa [pow_two] using h
  obtain ⟨hperf, hZ, hLZ⟩ := autOnK_central_quotient hB hHV hQV hKV
  have hC := autOn_inf_centralizer_le hB hHV hQV hcore
  have hLX : autOn K V ≤ autOn H V := AutOn.autOn_mono hB.le
  have hXL : autOn H V ≤ Subgroup.normalizer (autOn K V : Set (MulAut V)) :=
    AutOn.autOn_le_normalizer_autOn hB.normalizes
  exact two_mul_card_lt_index_fixV hV' hLX hXL hperf hZ hC hLZ hAX hA hAe

theorem BenderVertex.starBound_of_core
    [Finite G] {H K V : Subgroup G} (hB : BenderVertex H K) (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H) :
    StarBound V (pCoreOf 2 H) H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  intro P hPH hP hcomm hsq hPQ
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans hHV
  have hinf := inf_centralizer_eq_inf_pCoreOf hB hHV hQV hcore hPH hP
  have hA_ne : autOn P V ≠ ⊥ := by
    apply autOn_ne_bot_of_not_le_centralizer hPN
    intro hPC
    apply hPQ
    have hPeq : P ⊓ Subgroup.centralizer (V : Set G) = P := inf_eq_left.mpr hPC
    have hPeqQ : P ⊓ pCoreOf 2 H = P := by rw [← hinf, hPeq]
    exact inf_eq_left.mp hPeqQ
  have hAe : @IsElemAbelian2 ↥V (commGroupOfElemAbelian hV) (autOn P V) :=
    isElemAbelian2_autOn_of_commutator_square hV hPN hQV hcomm hsq
  have hlt := BenderVertex.two_mul_card_lt_index_fixV_of_core
    hB hV hHV hQV hKV hcore (autOn P V) (AutOn.autOn_mono hPH) hA_ne hAe
  have hcardA : Nat.card ↥(autOn P V) = (P ⊓ pCoreOf 2 H).relIndex P := by
    rw [card_autOn_eq_relIndex hPN, hinf]
  have hidx : (fixV (autOn P V)).index =
      (V ⊓ Subgroup.centralizer (P : Set G)).relIndex V := by
    have hfix : fixV (autOn P V) = (Subgroup.centralizer (P : Set G)).subgroupOf V :=
      AutOn.fixV_autOn_eq hPN
    have hsub : (Subgroup.centralizer (P : Set G)).subgroupOf V =
        (V ⊓ Subgroup.centralizer (P : Set G)).subgroupOf V := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    rw [hfix, hsub, Subgroup.relIndex]
  rw [hcardA, hidx] at hlt
  exact hlt

theorem BenderVertex.not_isFFModule_of_core
    [Finite G] {H K V : Subgroup G} (hB : BenderVertex H K) (hV : IsElemAbelian 2 V)
    (hHV : H ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hKV : ¬ K ≤ Subgroup.centralizer (V : Set G))
    (hcore : ∀ x ∈ H, (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (∀ y ∈ K, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) →
      x ∈ pCoreOf 2 H) :
    ¬ @IsFFModule ↥V (commGroupOfElemAbelian hV) (autOn H V) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  rintro ⟨A, hAX, hA, hAe, hle⟩
  have hApos : 0 < Nat.card A := by
    haveI : Nonempty ↥A := ⟨1, A.one_mem⟩
    exact Nat.card_pos
  have hlt := BenderVertex.two_mul_card_lt_index_fixV_of_core
    hB hV hHV hQV hKV hcore A hAX hA hAe
  haveI : Nonempty ↥(fixV A) := ⟨1, (fixV A).one_mem⟩
  have hcardpos : 0 < Nat.card ↥(fixV A) := Nat.card_pos
  have hidxle : (fixV A).index ≤ Nat.card A := by
    have h1 : (fixV A).index * Nat.card ↥(fixV A) = Nat.card ↥V :=
      Subgroup.index_mul_card _
    have h2 : (fixV A).index * Nat.card ↥(fixV A) ≤
        Nat.card A * Nat.card ↥(fixV A) := by
      rw [h1]
      exact hle
    exact Nat.le_of_mul_le_mul_right h2 hcardpos
  omega

end CFSG.Quasithin.F112Crit.APrime

end
