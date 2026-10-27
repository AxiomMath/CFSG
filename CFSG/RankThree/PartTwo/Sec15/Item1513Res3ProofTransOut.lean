module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTrans
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec17.Item17ParaS
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofEven

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

@[expose] def KS1513CentOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (m : ℕ), 1 ≤ m → Sec4.IsoLThreePi X 2 m →
    Group.IsPerfect X → ∀ σ : X ≃* X, (∀ g, σ (σ (σ g)) = g) →
    ∀ R : Subgroup X, (∀ r ∈ R, σ r = r) →
      (∀ g : X, σ g = g → ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
      Group.IsSolvable R → ¬ 3 ∣ Nat.card R → ¬ 2 ∣ Nat.card R

namespace Proof1513Res3

section Theta

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem le_normalizer_inSubgroup_theta {Y : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (Y : Set Γ)) :
    g ∈ Subgroup.normalizer ((inSubgroup (aschbacherSolvableCore 3) Y : Subgroup Γ) : Set Γ) := by
  have : (aschbacherSolvableCore 3 ↥Y).Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three).2.1
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _ hg

theorem odd_card_theta (hKf : KS1513CentOdd) {K L X : Subgroup Γ} (hLK : L ≤ K)
    (hKL : K ≤ Subgroup.normalizer (L : Set Γ)) (hXL : X ≤ Subgroup.normalizer (L : Set Γ))
    (hX : ¬ 2 ∣ Nat.card X) (hKLX : K ≤ L ⊔ X) {x : Γ}
    (hxL : x ∈ Subgroup.normalizer (L : Set Γ)) (hx3 : x ^ 3 = 1) {Λ : Type} [Group Λ]
    [Finite Λ] (e : ↥L ≃* Λ) {m : ℕ} (hm : 1 ≤ m)
    (hiso : Sec4.IsoLThreePi Λ 2 m) (hperf : Group.IsPerfect Λ) :
    ¬ 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (K ⊓ Subgroup.centralizer ({x} : Set Γ))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K ⊓ Subgroup.centralizer ({x} : Set Γ) with hY
  set θ₁ := inSubgroup (aschbacherSolvableCore 3) Y with hθ₁
  obtain ⟨hθsolv, hθchar, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  have hθY : θ₁ ≤ Y := Subgroup.map_subtype_le _
  have hYθ : Y ≤ Subgroup.normalizer (θ₁ : Set Γ) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨z', hz', rfl⟩ := hz
    have hθn : (aschbacherSolvableCore 3 ↥Y).Normal := by
      have := hθchar
      infer_instance
    have : (⟨y, hy⟩ : ↥Y) * z' * (⟨y, hy⟩ : ↥Y)⁻¹ ∈ aschbacherSolvableCore 3 ↥Y :=
      hθn.conj_mem z' hz' ⟨y, hy⟩
    exact ⟨_, this, rfl⟩
  set R := θ₁ ⊓ L with hR
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hθ3 (by
    have h1 : Nat.card R ∣ Nat.card θ₁ := Subgroup.card_dvd_of_le inf_le_left
    rw [hθ₁, inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective] at h1
    exact h3.trans h1)
  have hRsolv : Group.IsSolvable R := by
    have : Group.IsSolvable θ₁ := by
      rw [hθ₁, inSubgroup]
      exact Group.isSolvable_of_surjective ((Y.subtype).subgroupMap_surjective _)
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (show R ≤ θ₁ from inf_le_left))
  set σ : MulAut ↥L := L.normalizerMonoidHom ⟨x, hxL⟩ with hσ
  set σ' : Λ ≃* Λ := e.symm.trans (σ.trans e) with hσ'
  have hσv : ∀ l : ↥L, ((σ l : ↥L) : Γ) = x * l * x⁻¹ := fun l => rfl
  have hσ'3 : ∀ g, σ' (σ' (σ' g)) = g := by
    intro g
    apply e.symm.injective
    apply Subtype.ext
    simp only [hσ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hσv, hσv, hσv]
    have hx3' : x * x * x = 1 := by
      have h := hx3
      rw [pow_succ, pow_succ, pow_one] at h
      exact h
    calc x * (x * (x * ((e.symm g : ↥L) : Γ) * x⁻¹) * x⁻¹) * x⁻¹ =
        (x * x * x) * ((e.symm g : ↥L) : Γ) * (x * x * x)⁻¹ := by group
      _ = _ := by rw [hx3']; group
  set R' : Subgroup Λ := (R.subgroupOf L).map e.toMonoidHom with hR'
  have hcardR' : Nat.card R' = Nat.card R := by
    rw [hR', Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ L)).toEquiv]
  have hfix : ∀ r ∈ R', σ' r = r := by
    rintro _ ⟨r, hr, rfl⟩
    simp only [hσ', MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hσv]
    have hrx : (r : Γ) ∈ Subgroup.centralizer ({x} : Set Γ) :=
      (hθY (Subgroup.mem_subgroupOf.mp hr).1).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hrx
    calc x * (r : Γ) * x⁻¹ = (r : Γ) * x * x⁻¹ := by rw [hrx]
      _ = r := by group
  have hnorm : ∀ g : Λ, σ' g = g → ∀ r ∈ R', g * r * g⁻¹ ∈ R' := by
    intro g hg r hr
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    set g₀ := e.symm g with hg₀
    have hgg : g = e g₀ := by rw [hg₀, MulEquiv.apply_symm_apply]
    have hg₀x : x * (g₀ : Γ) * x⁻¹ = g₀ := by
      have h1 : σ g₀ = g₀ := by
        apply e.injective
        have := hg
        simp only [hσ', MulEquiv.trans_apply] at this
        rw [← hg₀] at this
        exact this.trans hgg
      rw [← hσv, h1]
    have hg₀Y : (g₀ : Γ) ∈ Y := by
      refine Subgroup.mem_inf.mpr ⟨hLK g₀.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g₀ : Γ) * x = x * (g₀ : Γ) * x⁻¹ * x := by rw [hg₀x]
        _ = x * g₀ := by group
    refine ⟨g₀ * r₀ * g₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have hr₀' := Subgroup.mem_subgroupOf.mp hr₀
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hYθ hg₀Y) r₀).mp hr₀'.1
        simpa using this
      · exact (g₀ * r₀ * g₀⁻¹).2
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [hgg]
  have hR'solv : Group.IsSolvable R' := by
    have : Group.IsSolvable (R.subgroupOf L) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ L)).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ L)).symm.surjective
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  have hR'odd := hKf Λ m hm hiso hperf σ' hσ'3 R' hfix hnorm hR'solv (hcardR' ▸ hR3)
  rw [hcardR'] at hR'odd
  intro h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := θ₁) 2 h2
  have htK : (t : Γ) ∈ K := (hθY t.2).1
  have hzt : Subgroup.zpowers (t : Γ) ≤ L := by
    have hp : IsPGroup 2 (Subgroup.zpowers (t : Γ)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht, pow_one])
    exact le_of_le_sup_of_odd hp hX (Subgroup.zpowers_le.mpr (hKL htK)) hXL
      (Subgroup.zpowers_le.mpr (hKLX htK))
  have htR : (t : Γ) ∈ R := ⟨t.2, hzt (Subgroup.mem_zpowers _)⟩
  apply hR'odd
  have : orderOf (⟨t, htR⟩ : R) = 2 :=
    (Subgroup.orderOf_coe (⟨(t : Γ), htR⟩ : R)).symm.trans ((Subgroup.orderOf_coe t).trans ht)
  exact this ▸ orderOf_dvd_natCard _

end Theta

section Img

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

variable {G : Type} [Group G] {A : Subgroup G} {LB : Subgroup G → Subgroup G} {b : G}
  [(ker142 A LB b).Normal]

theorem img142_mono {X Y : Subgroup G} (h : X ≤ Y) : img142 A LB b X ≤ img142 A LB b Y :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem mk_mem_img142 {X : Subgroup G} {g : ↥(kA142 A LB b)} (hg : (g : G) ∈ X) :
    QuotientGroup.mk' (ker142 A LB b) g ∈ img142 A LB b X :=
  ⟨g, Subgroup.mem_subgroupOf.mpr hg, rfl⟩

theorem img142_eq_bot {X : Subgroup G}
    (hX : X ≤ pPrimeCoreOf 3 (k142 A LB b) ⊔ Subgroup.zpowers b) : img142 A LB b X = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker142,
    Subgroup.mem_subgroupOf]
  exact hX (Subgroup.mem_subgroupOf.mp hg)

theorem mk_mem_normalizer_img142 [Finite G] {X : Subgroup G} {g : ↥(kA142 A LB b)}
    (hg : (g : G) ∈ Subgroup.normalizer (X : Set G)) :
    QuotientGroup.mk' (ker142 A LB b) g ∈ Subgroup.normalizer (img142 A LB b X : Set _) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hk, rfl⟩ := hn
  have hk' : (g : G) * k * (g : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hg k).mp (Subgroup.mem_subgroupOf.mp hk)
  refine ⟨g * k * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
  simpa using hk'

theorem card_img142_dvd {X : Subgroup G} (hX : X ≤ kA142 A LB b) :
    Nat.card (img142 A LB b X) ∣ Nat.card X := by
  refine (Subgroup.card_map_dvd _ _).trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

theorem img142_sup {X Y : Subgroup G} (hX : X ≤ kA142 A LB b) (hY : Y ≤ kA142 A LB b) :
    img142 A LB b (X ⊔ Y) = img142 A LB b X ⊔ img142 A LB b Y := by
  rw [img142, Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]
  rfl

end Img

section All

variable {G : Type} [Group G] [Finite G]

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

theorem le_of_le_sup_zpowers {S M : Subgroup G} {b : G} (hS2 : IsPGroup 2 S)
    (hSM : S ≤ Subgroup.normalizer (M : Set G)) (hbM : b ∈ Subgroup.normalizer (M : Set G))
    (hb3 : b ^ 3 = 1) (hSb : S ≤ M ⊔ Subgroup.zpowers b) : S ≤ M := by
  refine le_of_le_sup_of_odd hS2 ?_ hSM (Subgroup.zpowers_le.mpr hbM) hSb
  rw [Nat.card_zpowers]
  intro h2
  have h3 : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have := Nat.le_of_dvd (by norm_num) (h2.trans h3)
  have h1 : orderOf b ≠ 1 := by
    intro h1
    rw [h1] at h2
    norm_num at h2
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact h1 h
  · rw [h] at h2
    norm_num at h2

theorem le_pPrimeCore_of_mem_star (h142 : Item142R) (hbot : Item145BotS14)
    (hKf : KS1513CentOdd) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hX : ¬ 2 ∣ Nat.card (xA A)) {b : G} {Lb : Subgroup G}
    (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b) {m : ℕ} (hm : 1 ≤ m)
    (hiso : Sec4.IsoLThreePi (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) 2 m)
    {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2)) :
    S ≤ pPrimeCoreOf 3 (k142 A (lB A) b) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb' : Sec15R G A b Lb := Proof1511.sec15R_point h hb hLb
  have hD := hb'.toSec13Data
  have hA := hD.isElemAbelian
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hH
  set K := k142 A (lB A) b with hKdef
  set M := pPrimeCoreOf 3 K with hMdef
  have hM3 : ¬ 3 ∣ Nat.card M :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hKH : K ≤ H := delta_le H
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec14.le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := le_normalizer_pPrimeCoreOf 3 K
  have hCbH : Subgroup.centralizer ({b} : Set G) ≤ H :=
    centralizer_singleton_le_normalizer_zpowers b
  have h142b := h142 G A b Lb hb'
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
  have hSC : S ≤ Subgroup.centralizer ({b} : Set G) := hS.prop.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSQ.1.2.2
  have hSinv : S ∈ invariantPiSubgroups H A (piCompl 3) := ⟨hSC.trans hCbH, hSQ.1.2.1, hAS⟩
  obtain ⟨Q, hSQle, hQ⟩ :=
    Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hSinv
  obtain ⟨hQQ, hcase⟩ := h142b Q hQ
  have hQK : Q ≤ K := le_delta hQQ.1 (hQQ.2.trans hCbH)
  have hSK : S ≤ K := hSQle.trans hQK
  rcases hcase with ⟨-, hQK', -, -⟩ | ⟨hK, htypes⟩
  ·
    have hKQ : K = Q := hQK'.symm
    have hK3 : ¬ 3 ∣ Nat.card K := by
      rw [hKQ]
      exact (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.prop.2.1
    exact hSK.trans (le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3))
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  obtain ⟨e⟩ := Sec14.Item148PtRes2.nonempty_img142_equiv sporadicModels131 hb'.toSec14Std hK
  have hperf : Group.IsPerfect (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb) := by
    have : Group.IsPerfect Lb := Sec6.isPerfect_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨a, ha, ha1, hQα⟩ : ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) b a ha ≠ 1 ∧
      img142 A (lB A) b Q = thetaC142 A (lB A) b (alpha142 A (lB A) b a ha) ⊔
        thetaCA142 A (lB A) b := by
    rcases htypes with ⟨-, hex⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact hex
    · exfalso
      refine KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_nativeM22
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_m22)
        (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_m22)
        2 m ?_
      have ψ := φ.symm.trans e
      rcases hiso with ⟨hq, ⟨χ⟩⟩ | ⟨hq, ⟨χ⟩⟩
      · exact Or.inl ⟨hq, ⟨ψ.trans χ⟩⟩
      · exact Or.inr ⟨hq, ⟨ψ.trans χ⟩⟩
    · exfalso
      refine Sec14.Item148PtRes2.not_isoLThreePi_J2 2 m ?_
      have ψ := φ.symm.trans e
      rcases hiso with ⟨hq, ⟨χ⟩⟩ | ⟨hq, ⟨χ⟩⟩
      · exact Or.inl ⟨hq, ⟨ψ.trans χ⟩⟩
      · exact Or.inr ⟨hq, ⟨ψ.trans χ⟩⟩
  set KA := kA142 A (lB A) b with hKA
  set π := QuotientGroup.mk' (ker142 A (lB A) b) with hπ
  set x := alpha142 A (lB A) b a ha with hx
  have hKeq : K = Lb ⊔ pPrimeCoreOf 3 H ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) :=
    hK
  have hLbK : Lb ≤ K := by rw [hKeq]; exact le_sup_left.trans le_sup_left
  have hOK : pPrimeCoreOf 3 H ≤ K := by rw [hKeq]; exact le_sup_right.trans le_sup_left
  have hXK : xA A ≤ K := by rw [hKeq]; exact le_sup_right
  have hKKA : K ≤ KA := le_sup_left
  have h3Lb : 3 ∣ Nat.card Lb := three_dvd_card_of_types148
    (hb'.chosen136.2 b hD.zpowers_mem_omegaA Lb hD.mem_lA).1
  have hHLb : H ≤ Subgroup.normalizer (Lb : Set G) :=
    Sec17.Sec15R.normalizer_zpowers_le_normalizer_L hb' h3Lb
  have hKLb : K ≤ Subgroup.normalizer (Lb : Set G) := hKH.trans hHLb
  have hOM : pPrimeCoreOf 3 H ≤ M := le_pPrimeCoreOf hOK
    (hKH.trans (le_normalizer_pPrimeCoreOf 3 H)) (coprime_card_pPrimeCoreOf 3 H)
  have hLα : img142 A (lB A) b Lb ≤ img142 A (lB A) b K := img142_mono hLbK
  have hKαL : img142 A (lB A) b K ≤
      Subgroup.normalizer (img142 A (lB A) b Lb : Set (↥KA ⧸ ker142 A (lB A) b)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact mk_mem_normalizer_img142 (hKLb (Subgroup.mem_subgroupOf.mp hk))
  have hXαL : img142 A (lB A) b (xA A) ≤
      Subgroup.normalizer (img142 A (lB A) b Lb : Set (↥KA ⧸ ker142 A (lB A) b)) :=
    (img142_mono hXK).trans hKαL
  have hXα2 : ¬ 2 ∣ Nat.card (img142 A (lB A) b (xA A)) := fun h2 =>
    hX (h2.trans (card_img142_dvd (hXK.trans hKKA)))
  have hKαLX : img142 A (lB A) b K ≤
      img142 A (lB A) b Lb ⊔ img142 A (lB A) b (xA A) := by
    rw [hKeq, img142_sup ((sup_le hLbK hOK).trans hKKA) (hXK.trans hKKA),
      img142_sup (hLbK.trans hKKA) (hOK.trans hKKA),
      img142_eq_bot (hOM.trans le_sup_left), sup_bot_eq]
  have hAKA : ∀ a' ∈ A, a' ∈ KA := fun a' ha' => Subgroup.mem_sup_right ha'
  have hxA : ∀ a' (ha' : a' ∈ A), π ⟨a', hAKA a' ha'⟩ ∈ img142 A (lB A) b A := fun a' ha' =>
    mk_mem_img142 (X := A) (g := ⟨a', hAKA a' ha'⟩) ha'
  have hxL : x ∈ Subgroup.normalizer (img142 A (lB A) b Lb : Set (↥KA ⧸ ker142 A (lB A) b)) :=
    mk_mem_normalizer_img142 (X := Lb) (g := ⟨a, hAKA a ha⟩) (hD.le_normalizer ha)
  have hx3 : x ^ 3 = 1 := by
    rw [hx, alpha142, ← map_pow]
    have : (⟨a, hAKA a ha⟩ : ↥KA) ^ 3 = 1 := Subtype.ext (by simpa using hA.2 a ha)
    rw [this, map_one]
  have hθ1 : ¬ 2 ∣ Nat.card (thetaC142 A (lB A) b x) :=
    odd_card_theta hKf hLα hKαL hXαL hXα2 hKαLX hxL hx3 e hm hiso hperf
  have hθ2C : thetaCA142 A (lB A) b ≤
      Subgroup.centralizer (img142 A (lB A) b A : Set (↥KA ⧸ ker142 A (lB A) b)) :=
    (Subgroup.map_subtype_le _).trans inf_le_right
  have hxAα : x ∈ img142 A (lB A) b A := hxA a ha
  have hAαcomm : ∀ y ∈ img142 A (lB A) b A, ∀ z ∈ img142 A (lB A) b A, y * z = z * y := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hz))
  have hθ2N : thetaCA142 A (lB A) b ≤ Subgroup.normalizer
      (thetaC142 A (lB A) b x : Set (↥KA ⧸ ker142 A (lB A) b)) := by
    intro t ht
    refine le_normalizer_inSubgroup_theta (Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
    · exact ((Subgroup.map_subtype_le _).trans inf_le_left) ht
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hθ2C ht) x hxAα).symm
  have hyθ1 : ∀ y ∈ img142 A (lB A) b A, y ∈ Subgroup.normalizer
      (thetaC142 A (lB A) b x : Set (↥KA ⧸ ker142 A (lB A) b)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine le_normalizer_inSubgroup_theta (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨mk_mem_normalizer_img142 (hAK (Subgroup.mem_subgroupOf.mp hy)), ?_⟩)
    refine Subgroup.le_normalizer ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAαcomm _ (mk_mem_img142 (Subgroup.mem_subgroupOf.mp hy)) x hxAα
  have hSKA : S ≤ KA := hSK.trans hKKA
  have hSα2 : IsPGroup 2 (img142 A (lB A) b S) :=
    (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSKA).symm).map _
  have hcomm : ∀ s ∈ S, ∀ a' ∈ A, s * a' * s⁻¹ * a'⁻¹ ∈ M := by
    intro s hs a' ha'
    set ŝ : ↥KA := ⟨s, hSKA hs⟩
    set â : ↥KA := ⟨a', hAKA a' ha'⟩
    have hσs : π ŝ ∈ img142 A (lB A) b Q := img142_mono hSQle (mk_mem_img142 hs)
    rw [hQα, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hθ2N] at hσs
    obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := hσs
    have hyt₂ : π â * t₂ = t₂ * π â :=
      (Subgroup.mem_centralizer_iff.mp (hθ2C ht₂) _ (hxA a' ha'))
    have hw1 : π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ ∈ thetaC142 A (lB A) b x := by
      have h1 : π â * t₁⁻¹ * (π â)⁻¹ ∈ thetaC142 A (lB A) b x :=
        (Subgroup.mem_normalizer_iff.mp (hyθ1 _ (hxA a' ha')) _).mp (inv_mem ht₁)
      have h2 : π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ = t₁ * (π â * t₁⁻¹ * (π â)⁻¹) := by
        rw [← ht]
        calc t₁ * t₂ * π â * (t₁ * t₂)⁻¹ * (π â)⁻¹ = t₁ * (t₂ * π â) * t₂⁻¹ * t₁⁻¹ * (π â)⁻¹ := by
              group
          _ = t₁ * (π â * t₂) * t₂⁻¹ * t₁⁻¹ * (π â)⁻¹ := by rw [hyt₂]
          _ = t₁ * (π â * t₁⁻¹ * (π â)⁻¹) := by group
      rw [h2]
      exact mul_mem ht₁ h1
    have hw2 : π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ ∈ img142 A (lB A) b S := by
      have h1 : π â * (π ŝ)⁻¹ * (π â)⁻¹ ∈ img142 A (lB A) b S :=
        (Subgroup.mem_normalizer_iff.mp (mk_mem_normalizer_img142 (hAS ha')) _).mp
          (inv_mem (mk_mem_img142 hs))
      have h2 : π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ = π ŝ * (π â * (π ŝ)⁻¹ * (π â)⁻¹) := by group
      rw [h2]
      exact mul_mem (mk_mem_img142 hs) h1
    have hw : π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ = 1 := by
      set w := π ŝ * π â * (π ŝ)⁻¹ * (π â)⁻¹ with hwdef
      obtain ⟨k, hk⟩ := hSα2 ⟨w, hw2⟩
      have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have ho1 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have ho2 : orderOf w ∣ Nat.card (thetaC142 A (lB A) b x) := by
        have := orderOf_dvd_natCard (⟨w, hw1⟩ : thetaC142 A (lB A) b x)
        rwa [Subgroup.orderOf_mk] at this
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr (Nat.odd_iff.mpr
          (Nat.two_dvd_ne_zero.mp hθ1)))) ho1 ho2)
    have hker : ŝ * â * ŝ⁻¹ * â⁻¹ ∈ ker142 A (lB A) b := by
      rw [← QuotientGroup.eq_one_iff (N := ker142 A (lB A) b)]
      simpa [hπ] using hw
    have hMb : s * a' * s⁻¹ * a'⁻¹ ∈ M ⊔ Subgroup.zpowers b := by
      have := Subgroup.mem_subgroupOf.mp hker
      simpa using this
    have hgS : s * a' * s⁻¹ * a'⁻¹ ∈ S := by
      have h1 : a' * s⁻¹ * a'⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hAS ha') s⁻¹).mp (inv_mem hs)
      have h2 : s * a' * s⁻¹ * a'⁻¹ = s * (a' * s⁻¹ * a'⁻¹) := by group
      rw [h2]
      exact mul_mem hs h1
    have hz : Subgroup.zpowers (s * a' * s⁻¹ * a'⁻¹) ≤ M := by
      refine le_of_le_sup_zpowers (hS2.to_le (Subgroup.zpowers_le.mpr hgS))
        (Subgroup.zpowers_le.mpr (hKM (hSK hgS))) (hAM hD.mem_A)
        (hA.2 b hD.mem_A) (Subgroup.zpowers_le.mpr hMb)
    exact hz (Subgroup.mem_zpowers _)
  have hSAM : ⁅S, A⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro s hs a' ha'
    rw [commutatorElement_def]
    exact hcomm s hs a' ha'
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1
  have hCSA : S ⊓ Subgroup.centralizer (A : Set G) ≤ M := by
    have hAN : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :
        Set G) := fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAS hg, (hAC.trans Subgroup.le_normalizer) hg⟩
    have hle : S ⊓ Subgroup.centralizer (A : Set G) ≤ xA A :=
      le_pPrimeCoreOf_centralizer (hbot G A b Lb hb'.toSec14Std)
        (mem_scriptQ_of_le hSQ inf_le_left hAN) inf_le_right
    have hbot' : S ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hS2.to_le inf_le_left)
      have hd : Nat.card (S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ∣
          Nat.card (xA A) := Subgroup.card_dvd_of_le hle
      rcases n with _ | n
      · simpa using hn
      · exfalso
        apply hX
        rw [hn] at hd
        exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hd
    rw [hbot']
    exact bot_le
  have hcopS : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A S hA3 hAS hcopS
  rw [← hfac]
  exact sup_le hSAM hCSA

theorem transOn_of_forall_le (h142 : Item142R) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) {b : G} {Lb : Subgroup G}
    (hb : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hSM : ∀ S ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2),
      S ≤ pPrimeCoreOf 3 (k142 A (lB A) b)) :
    TransOn A (lB A) (xA A) (Subgroup.centralizer ({b} : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb' : Sec15R G A b Lb := Proof1511.sec15R_point h hb hLb
  have hD := hb'.toSec13Data
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hH
  set K := k142 A (lB A) b with hKdef
  set M := pPrimeCoreOf 3 K with hMdef
  have hM3 : ¬ 3 ∣ Nat.card M :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hKH : K ≤ H := delta_le H
  have hAK : A ≤ Subgroup.normalizer (K : Set G) :=
    Sec14.le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hAM : A ≤ Subgroup.normalizer (M : Set G) :=
    hAK.trans (normalizer_le_normalizer_pPrimeCoreOf 3 K)
  have hCbH : Subgroup.centralizer ({b} : Set G) ≤ H :=
    centralizer_singleton_le_normalizer_zpowers b
  have hMinv : M ∈ invariantPiSubgroups H A (piCompl 3) :=
    ⟨(pPrimeCoreOf_le 3 K).trans hKH, (isPiSubgroup_piCompl_iff Nat.prime_three M).mpr hM3, hAM⟩
  obtain ⟨Q₀, hMQ₀, hQ₀⟩ :=
    Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups H A (piCompl 3))) hMinv
  obtain ⟨hQ₀Q, -⟩ := h142 G A b Lb hb' Q₀ hQ₀
  have hMQ : M ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ₀Q.1 hMQ₀ hAM
  have hMC : M ≤ Subgroup.centralizer ({b} : Set G) := hMQ₀.trans hQ₀Q.2
  have hsyl : ∀ R ∈ scriptQPiStar A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2),
      CFSG.Open.fusionIsSylowIn 2 R M ∧ A ≤ Subgroup.normalizer (R : Set G) := by
    intro R hR
    have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR.prop
    have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR.prop.1.1.1.2.2
    obtain ⟨R', hR', hRR', hAR'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hM3 hAM (hSM R hR) hR2 hAR
    have hR'mem : R' ∈ scriptQPi A (lB A) (Subgroup.centralizer ({b} : Set G)) (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hMQ hR'.1 hAR', hR'.1.trans hMC⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two R').mpr hR'.2.1⟩
    have := hR.eq_of_le hR'mem hRR'
    exact ⟨this ▸ hR', hAR⟩
  have hCAb : Subgroup.centralizer (A : Set G) ≤ H :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hD.mem_A)).trans hCbH
  have hCMX : M ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    refine le_pPrimeCoreOf inf_le_right (fun g hg => ?_)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (coprime_card_pPrimeCoreOf 3 K))
    have hgA : g ∈ Subgroup.normalizer (A : Set G) := Subgroup.centralizer_le_normalizer _ hg
    have hgH : H.map (MulAut.conj g).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hCAb hg))
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := by
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      have h1 := Sec17.HeadProof.map_conj_delta hgA H
      rw [hgH] at h1
      exact h1
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_le_normalizer_pPrimeCoreOf 3 K hgK, Subgroup.le_normalizer hg⟩
  intro S hS T hT
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hM3 hAM hSs hTs hAS hAT
  exact ⟨x, ⟨hCMX hx, hMC hx.1⟩, hxT⟩

end All

end Proof1513Res3

open CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem step1513EvenTrans_of_kfact
    (h142 : Item142R)
    (hbot : Item145BotS14) (hKf : KS1513CentOdd) : Step1513EvenTrans := by
  intro G _ _ A c L h hX b Lb hb hLb hm
  obtain ⟨m, hm1, hiso⟩ := hm
  exact Proof1513Res3.transOn_of_forall_le h142 h hb hLb fun S hS =>
    Proof1513Res3.le_pPrimeCore_of_mem_star h142 hbot hKf h hX hb hLb hm1 hiso hS

end CFSG.RankThree.PartTwo.Sec15
