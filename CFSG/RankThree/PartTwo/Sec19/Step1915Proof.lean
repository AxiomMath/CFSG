module

public import CFSG.RankThree.PartTwo.Sec19.Step1915W
public import CFSG.RankThree.PartTwo.Sec19.Step1916Proof2
public import CFSG.RankThree.PartTwo.Sec19.Step198Proof
import CFSG.RankThree.PartTwo.Sec19.Step1918ProofInner
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.T444.Step452
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.AutTrialityOrderThree
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Step1915Proof

section Orders

theorem le_mul_of_four_le {q : ℕ} (hq : 4 ≤ q) :
    64 * (15 * 63) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h1 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ q ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul (by omega) (by omega))

theorem le_card_of_isoLThreePi {Y : Type} [Group Y] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi Y p e) (hq2 : p ^ e ≠ 2) : 20160 ≤ Nat.card Y := by
  have hp : p.Prime := Fact.out
  have h2 : 2 ≤ p ^ e := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hq4 : 4 ≤ p ^ e := by
    rcases h with ⟨h3, -⟩ | ⟨h3, -⟩ <;> omega
  have key := le_mul_of_four_le hq4
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hle : Nat.card Y * Nat.gcd 3 (p ^ e - 1) ≤ Nat.card Y * 3 := Nat.mul_le_mul_left _ hg
    have h3 : 64 * (15 * 63) ≤ Nat.card Y * 3 := (key.trans hc.symm.le).trans hle
    omega
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hg : Nat.gcd 3 (p ^ e + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
    have hle : Nat.card Y * Nat.gcd 3 (p ^ e + 1) ≤ Nat.card Y * 3 := Nat.mul_le_mul_left _ hg
    have hmono : (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1)) ≤
        (p ^ e) ^ 3 * (((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : 64 * (15 * 63) ≤ Nat.card Y * 3 := ((key.trans hmono).trans hc.symm.le).trans hle
    omega

variable {G : Type} [Group G] [Finite G] {A L E M : Subgroup G} {c : G}

theorem le_card_quot_center
    (h1913 : Step1913) (hctx : Ctx1912 G A c L E M) :
    20160 ≤ Nat.card ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
  obtain ⟨hθ, hZ, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  have eL : (L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* L ⧸ CFSG.pCore 2 L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
      (QuotientGroup.quotientMulEquivOfEq hθ)
  rw [Nat.card_congr eL.toEquiv]
  rcases h1913 G A c L E M hctx with ⟨p, e, hp, he, hiso⟩ | hM12
  · obtain ⟨-, hq2⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi he hiso
    exact le_card_of_isoLThreePi he hiso hq2
  · obtain ⟨φ⟩ := hM12
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num

end Orders

section Components

variable {G : Type} [Group G] [Finite G]

theorem mem_oTwoComponentsIn_of_card (hG : TheoremFourHyp G)
    {M K L F : Subgroup G} (hM2 : CFSG.Assembly.IsTwoLocal M) (hMtop : M ≠ ⊤)
    (hK : K ∈ thetaComponentsIn M) (hLK : L ≤ K)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L))
    (hcard : Nat.card ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 2520 ∨
      20160 ≤ Nat.card ((L ⧸ aschbacherSolvableCore 3 L) ⧸
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)))
    (hFL : F ≤ L) (hF9 : Nat.card F = 9) (hF3 : ∀ x ∈ F, x ^ 3 = 1) :
    K ∈ oTwoComponentsIn M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKM, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have hsn : (K.subgroupOf M).IsSubnormal := hK'.2.1
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hKtop : K ≠ ⊤ := fun h => hMtop (top_le_iff.mp (h ▸ hKM))
  have hK4 : SectionFourHyp K := hG.sectionFourHyp hKtop
  have hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
    set e := Subgroup.subgroupOfEquivOfLe hKM
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e
      (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hK'.2.2
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := LocalCores.isQuasisimple_nontrivial hLq
    obtain ⟨u, v, huv⟩ := exists_pair_ne (L ⧸ aschbacherSolvableCore 3 L)
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    have : Subsingleton L := by
      rw [h]
      infer_instance
    rw [Subsingleton.elim u v]
  have hK1 : K ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLK))
  have hO2 : CFSG.pCore 2 K ≠ ⊥ :=
    Step198Proof.pCore_two_ne_bot hG.charTwoType hM2 hKM hsn hKp hK1
  have := hKp
  set θK := aschbacherSolvableCore 3 K with hθK
  set N : Subgroup K := (Subgroup.center (K ⧸ θK)).comap (QuotientGroup.mk' θK) with hN
  have : N.Normal := Subgroup.Normal.comap inferInstance _
  have hNs : Group.IsSolvable N :=
    Sec4.isSolvable_comap_mk' (solvable_prime_complement_core_characterization (H := K)
      Nat.prime_three).1 inferInstance
  have : IsSimpleGroup ((K ⧸ θK) ⧸ Subgroup.center (K ⧸ θK)) := hKq.2.1
  have : IsSimpleGroup (K ⧸ N) :=
    (Sec4.Census.quotientComapEquiv θK (Subgroup.center (K ⧸ θK))).isSimpleGroup
  have hPN : CFSG.pCore 2 K ≤ N := by
    intro x hx
    have hxθ : x ∈ θK := (solvable_prime_complement_core_characterization (H := K)
      Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num) hx
    rw [hN, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hxθ]
    exact Subgroup.one_mem _
  have h3 : ¬ Subgroup.centralizer (CFSG.pCore 3 (K ⧸ CFSG.pCore 2 K) :
      Set (K ⧸ CFSG.pCore 2 K)) ≤ N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := by
    intro hle
    have hcen := Step198Proof.pCore_three_le_center hKq
    have htop : N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊤ := by
      refine eq_top_iff.mpr (le_trans ?_ hle)
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (hcen hx) g).symm
    have hNtop : N = ⊤ := by
      refine eq_top_iff.mpr fun x _ => ?_
      have hx : QuotientGroup.mk' (CFSG.pCore 2 K) x ∈
          N.map (QuotientGroup.mk' (CFSG.pCore 2 K)) := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have h1 : n⁻¹ * x ∈ CFSG.pCore 2 K := QuotientGroup.eq.mp hnx
      have := N.mul_mem hn (hPN h1)
      simpa using this
    have : Nontrivial (K ⧸ N) := IsSimpleGroup.toNontrivial
    exact (QuotientGroup.nontrivial_iff.mp this) hNtop
  rcases Step198Proof.quasisimple_or_linear hK4 hNs hO2 h3 with
    hq | ⟨⟨e2⟩⟩ | ⟨p, hp, hp3, ⟨e3⟩⟩ | ⟨⟨e4⟩⟩
  · exact Sec18.mem_oTwoComponentsIn_of_quasisimple hKM hsn (Subgroup.isPerfect_iff.mp hKp) hq
  · exfalso
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hdvd := Step198Proof.card_quot_center_dvd hLK hLq (Sec4.oTwoFitting K)
      Sec4.isSolvable_oTwoFitting
    rw [Nat.card_congr e2.toEquiv, Sec4.Census.card_SL2] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases hcard with h | h <;> omega
  · exact (Step198Proof.false_of_sl2 (hFL.trans hLK) hF9 hF3 hp hp3 e3).elim
  · exfalso
    have hdvd := Step198Proof.card_quot_center_dvd hLK hLq (Sec4.oTwoP 3 K)
      (Sec4.isSolvable_oTwoP 3)
    rw [Nat.card_congr e4.toEquiv, Sec4.Census.card_SL3_three] at hdvd
    rcases hcard with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · have := Nat.le_of_dvd (by norm_num) hdvd
      omega

end Components

section Central

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_of_central_of_mem_normalizer {K L : Subgroup G} {c : G}
    (hKq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) (hLK : L ≤ K)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : orderOf c = 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G))
    (hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal)
    (hLp : Group.IsPerfect L) (hL1 : L ≠ ⊥)
    (hcen : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    K = L ⊔ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 2 K with hP
  set π := QuotientGroup.mk' P with hπ
  set O := CFSG.Open.pCoreOf 2 K with hO
  have hOK : O ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hB3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc3, pow_one])
  have hBO : Subgroup.zpowers c ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcK)
  have hρ : Step199Proof.pCoreAct K ⟨c, hcK⟩ = 1 :=
    (Step1918Proof.pCoreAct_eq_one_iff hcK).mpr hcen
  have hBK : ∀ b ∈ Subgroup.zpowers c, ∀ k ∈ K, k⁻¹ * (b * k * b⁻¹) ∈ O := by
    rintro _ ⟨n, rfl⟩ k hk
    have hbN : c ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.zpow_mem _ hcK n
    have h1 : Step199Proof.pCoreAct K ⟨c ^ n, hbN⟩ = 1 := by
      have e : (⟨c ^ n, hbN⟩ : Subgroup.normalizer (K : Set G)) = ⟨c, hcK⟩ ^ n := by
        ext
        simp
      rw [e, map_zpow, hρ, one_zpow]
    have h2 := (Step1918Proof.pCoreAct_eq_one_iff hbN).mp h1 k hk
    have h3 : k⁻¹ * (c ^ n * k * (c ^ n)⁻¹ * k⁻¹) * k⁻¹⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem hk)) _).mp h2
    rwa [show k⁻¹ * (c ^ n * k * (c ^ n)⁻¹ * k⁻¹) * k⁻¹⁻¹ = k⁻¹ * (c ^ n * k * (c ^ n)⁻¹) by
      group] at h3
  have hsurj : ∀ q : K ⧸ P, ∃ x : K, (x : G) ∈ Subgroup.centralizer ({c} : Set G) ∧ π x = q := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective P q
    obtain ⟨y, hy, hyB⟩ :=
      Step199Proof.exists_fixed_mem_coset hB3 hO3 hBO fun b hb => hBK b hb k k.2
    have hyK : y ∈ K := by
      have := K.mul_mem k.2 (hOK hy)
      simpa using this
    refine ⟨⟨y, hyK⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hyB c (Subgroup.mem_zpowers c)).symm
    · apply QuotientGroup.eq.mpr
      rw [Sec18.mem_pCore_iff_mem_pCoreOf]
      have h1 := O.inv_mem hy
      rwa [mul_inv_rev, inv_inv] at h1
  set C' : Subgroup K := (Subgroup.centralizer ({c} : Set G)).subgroupOf K with hC'
  set L' : Subgroup K := L.subgroupOf K with hL'
  have hL'C' : L' ≤ C' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hLc (Subgroup.mem_subgroupOf.mp hx))
  set ι : C' →* Subgroup.centralizer ({c} : Set G) :=
    MonoidHom.codRestrict (K.subtype.comp C'.subtype) _
      (fun x => Subgroup.mem_subgroupOf.mp x.2) with hι
  have hsn' : (L'.subgroupOf C').IsSubnormal := by
    have h := hLsn.comap ι
    convert h using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  set φ : C' →* K ⧸ P := π.comp C'.subtype with hφ
  have hφs : Function.Surjective φ := fun q => by
    obtain ⟨x, hx, hxq⟩ := hsurj q
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mpr hx⟩, hxq⟩
  have heq : (L'.subgroupOf C').map φ = L'.map π := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hL'C' hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hsn'' : (L'.map π).IsSubnormal := heq ▸ hsn'.map hφs
  have hL'p : Group.IsPerfect L' := by
    have := hLp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom) (MulEquiv.surjective _)
  have hperf : Group.IsPerfect (L'.map π) :=
    Group.IsPerfect.ofSurjective (f := π.subgroupMap L') (π.subgroupMap_surjective L')
  have hne : L'.map π ≠ ⊥ := by
    intro h
    have hL'P : L' ≤ P := by
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
      exact h
    have hL2 : IsPGroup 2 L' := (CFSG.pCore_isPGroup (p := 2) (G := K)).to_le hL'P
    have : Group.IsSolvable L' := by
      have := hL2.isNilpotent
      infer_instance
    have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
    have : Nontrivial L' := (Subgroup.subgroupOfEquivOfLe hLK).toEquiv.nontrivial
    exact Group.IsPerfect.not_isSolvable L' inferInstance
  have htop := Sec4.Item426.eq_top_of_isPerfect_of_isSubnormal hKq hperf hsn'' hne
  apply le_antisymm
  · intro k hk
    have hq : π ⟨k, hk⟩ ∈ L'.map π := htop ▸ Subgroup.mem_top _
    obtain ⟨l, hl, hlk⟩ := hq
    have h1 : l⁻¹ * ⟨k, hk⟩ ∈ P := QuotientGroup.eq.mp hlk
    have h2 : ((l⁻¹ * ⟨k, hk⟩ : K) : G) ∈ CFSG.Open.pCoreOf 2 K :=
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
    have e : k = (l : G) * ((l⁻¹ * ⟨k, hk⟩ : K) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) h2
  · exact sup_le hLK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)

end Central

end Step1915Proof

open Step1915Proof

@[expose] def Census1915 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L A : Subgroup G) (c : G),
    SectionFourHyp ↥(K ⊔ A) → CFSG.Open.pCoreOf 2 K ≠ ⊥ → Group.IsPerfect K →
    IsQuasisimple (K ⧸ CFSG.pCore 2 K) → A ≤ Subgroup.normalizer (K : Set G) →
    CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → c ∈ A → orderOf c = 3 →
    ¬ (∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) →
    L ≤ K → L ≤ Subgroup.centralizer ({c} : Set G) →
    (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal → Group.IsPerfect L →
    A ≤ Subgroup.normalizer (L : Set G) →
    (∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      a ∈ Subgroup.zpowers c) →
    (IsLThreePi (L ⧸ CFSG.pCore 2 L) ∨
      Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)) →
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
        Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧ KFacts.InducesStdKind K c .field) ∨
      ∃ (n : ℕ) (_ : 1 ≤ n) (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (2 ^ n) ^ 3 ∧ ∃ σ : F ≃+* F, (∀ x, σ x = x ^ 2 ^ n) ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃*
            CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 F
              σ.toRingHom) ∧
          Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 n ∧
          CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 2 n ∧
          Sec4.InducesOuterTheta c K

theorem step1915W_of
    (h1913 : Step1913) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hC : Census1915) :
    Step1915W := by
  intro G _ _ A c L E M hctx hLM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hL : L ∈ thetaComponentsAt 3 c := hctx.mem_lA.1
  have hE := Step1916Proof2.isE27_E hctx
  have hA := Step1916Proof2.isE27_A hctx
  have hc3 := Step1916Proof2.orderOf_eq hctx
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc3
    norm_num at hc3
  have hcA := Step1916Proof2.mem_A hctx
  have hcE := Step1916Proof2.mem_E hctx
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hLq := Sec12.isQuasisimple_thetaQuot_of_mem hL
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hL
  have hLsn : (L.subgroupOf (Subgroup.centralizer ({c} : Set G))).IsSubnormal :=
    PartOne.isSubnormal_of_mem_thetaComponentsAt hL
  obtain ⟨hθ, -, -⟩ := Step1916Proof2.lBar_facts h1913 hctx
  obtain ⟨F, hFL, hF, hF9⟩ := Step1918Proof.exists_elemAbelian_nine h1913 hctx
  have hL1 : L ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card F ≤ Nat.card (⊥ : Subgroup G) := Subgroup.card_le_of_le hFL
    rw [Subgroup.card_bot] at h1
    omega
  have hEM : E ≤ M := hE.le_gamma.trans hctx.mem_scriptM.2
  have hAM : A ≤ M := by
    have hD9 : Nat.card (A ⊓ E : Subgroup G) = 9 := step1916D_of h1913 G A c L E M hctx
    have hND : Subgroup.normalizer ((A ⊓ E : Subgroup G) : Set G) ≤ M :=
      (normalizer_le_gamma inf_le_right (two_le_pRank_of_elemAbelian
        (isElemAbelian_of_le hA.1 inf_le_left) hD9.ge)).trans hctx.mem_scriptM.2
    intro a ha
    refine hND ((Subgroup.centralizer_le_normalizer _) (Subgroup.mem_centralizer_iff.mpr ?_))
    intro d hd
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨d, hd.1⟩ ⟨a, ha⟩)
  have hcM : c ∈ M := hEM hcE
  have hM2 : CFSG.Assembly.IsTwoLocal M := hctx.mem_scriptM.1.1
  have hMtop : M ≠ ⊤ := by
    have : IsSimpleGroup G := hst.isSimpleGroup
    exact ne_top_of_pCoreOf_ne_bot hst.nonabelian
      (pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1)
  have hM4 : SectionFourHyp M := hst.toTheoremFourHyp.sectionFourHyp hMtop
  obtain ⟨L', hL', hLL'⟩ := h48 M hM4 (E.subgroupOf M)
    (Step198DProof.isElemAbelian_subgroupOf hE.1 M)
    ⟨3, le_rfl, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE.2]; norm_num⟩
    ⟨c, hcM⟩ (Subgroup.mem_subgroupOf.mpr hcE) (fun h => hc1 (congrArg Subtype.val h))
    (L.subgroupOf M) (Step198Proof.subgroupOf_mem_thetaComponentsAt hL hLM hcM)
  set K := L'.map M.subtype with hKdef
  have hKθ : K ∈ thetaComponentsIn M := ⟨L', hL', rfl⟩
  have hLK : L ≤ K := fun l hl =>
    ⟨⟨l, hLM hl⟩, hLL' (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  have hEK : E ≤ Subgroup.normalizer (K : Set G) :=
    Step198Proof.le_normalizer_map_of_isE27 h45 hM4 hE hEM hL'
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Step198Proof.le_normalizer_map_of_isE27 h45 hM4 hA hAM hL'
  have hK : K ∈ oTwoComponentsIn M :=
    mem_oTwoComponentsIn_of_card hst.toTheoremFourHyp hM2 hMtop hKθ hLK hLq
      (Or.inr (le_card_quot_center h1913 hctx)) hFL hF9 hF.2
  refine ⟨K, hK, hLK, ?_⟩
  by_cases hcen : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K
  ·
    left
    exact eq_sup_of_central_of_mem_normalizer (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
      hLK (hEK hcE) hc3 hLc hLsn hLp hL1 hcen
  ·
    right
    have hKA : K ⊔ A ≤ M := sup_le (le_of_mem_oTwoComponentsIn hK) hAM
    have hKA4 : SectionFourHyp ↥(K ⊔ A) :=
      hst.toTheoremFourHyp.sectionFourHyp (fun h => hMtop (top_le_iff.mp (h ▸ hKA)))
    have hOeq : (CFSG.pCore 2 L).map L.subtype = CFSG.Open.pCoreOf 2 L := by
      rfl
    have hsec : ∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
        a ∈ Subgroup.zpowers c := by
      intro a ha h
      have hmem : a ∈ Late.sectionCentralizer A L
          ((aschbacherSolvableCore 3 L).map L.subtype) := by
        refine ⟨ha, fun l hl => ?_⟩
        rw [hθ, hOeq]
        exact h l hl
      have := hctx.mem_lA.2.2.1
      rw [this] at hmem
      exact hmem
    rcases hC G K L A c hKA4 (pCoreOf_ne_bot_of_mem_oTwoComponentsIn hst.charTwoType hM2 hK)
        (isPerfect_of_mem_oTwoComponentsIn hK) (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK)
        hAK hA.1 hA.2 hcA hc3 hcen hLK hLc (Sec18.isSubnormal_subgroupOf_of_le hLsn inf_le_right)
        hLp hctx.mem_lA.2.1 hsec (h1913 G A c L E M hctx) with
      h2 | ⟨n, hn, F', _, _, hF', σ, hσ, ⟨iso⟩, hLiso, hmodel, hout⟩
    · exact Or.inl h2
    ·
      exact Or.inr ⟨n, hn, hLiso, hmodel, KFacts.InducesStdKind.triality n hn F' hF' σ hσ
        (KFacts.inducesKindTriality_graphField hn hF' hσ K (hA.1.2 c hcA) hout iso)⟩

end CFSG.RankThree.PartTwo.Sec19
