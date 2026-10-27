module

public import CFSG.RankThree.PartTwo.KFacts.KS18MultProof
public import CFSG.RankThree.PartOne.S11c.Sec68
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1915Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Theta

variable {K : Type} [Group K] [Finite K]

theorem pCore_two_le_theta : CFSG.pCore 2 K ≤ aschbacherSolvableCore 3 K :=
  (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.2.2.2.2 2
    Nat.prime_two (by norm_num)

theorem nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hq : IsQuasisimple Q) :
    Nontrivial Q := by
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.1.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem exists_ne_comm_of_isQuasisimple {Q : Type*} [Group Q] (hq : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) b
  exact ⟨a, b, fun h => hab (by rw [← map_mul, ← map_mul, h])⟩

theorem center_eq_bot_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : Subgroup.center Q = ⊥) : Subgroup.center P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [h, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.mpr ((map_eq_one_iff e e.injective).mp hex)

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hq : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have := nontrivial_of_isQuasisimple hq
  have := hq.1
  exact Group.IsPerfect.not_isSolvable Q

theorem theta_map_le_center (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) :
    (aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
  have hZn : ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases LocalCores.quasisimple_normal_subgroups hq hZn with htop | hcen
  · exfalso
    have hθs : Group.IsSolvable (aschbacherSolvableCore 3 K) :=
      (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).1
    have hZs : Group.IsSolvable
        ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))) :=
      Group.isSolvable_of_surjective
        ((QuotientGroup.mk' (CFSG.pCore 2 K)).subgroupMap_surjective _)
    rw [htop] at hZs
    exact not_isSolvable_of_isQuasisimple hq (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv (G := K ⧸ CFSG.pCore 2 K)).toMonoidHom)
      (Subgroup.topEquiv (G := K ⧸ CFSG.pCore 2 K)).surjective)
  · exact hcen

theorem isQuasisimple_theta_quot (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) :
    IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) := by
  have hZ := theta_map_le_center hq
  have : ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have h1 := LocalCores.isQuasisimple_of_surjective hq
    (QuotientGroup.mk' ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hZ)
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K) (aschbacherSolvableCore 3 K)
      pCore_two_le_theta) h1

theorem theta_eq_pCore_of_map_eq_bot
    (h : (aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) = ⊥) :
    aschbacherSolvableCore 3 K = CFSG.pCore 2 K := by
  refine le_antisymm (fun x hx => ?_) pCore_two_le_theta
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 K) x ∈
      (aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) := ⟨x, hx, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact hx'

theorem coprime_six_card_theta_map (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K)) :
    Nat.Coprime 6
      (Nat.card ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := (aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) with hZdef
  have hZc : Z ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := theta_map_le_center hq
  have h3 : ¬ 3 ∣ Nat.card Z := fun h =>
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
      (h.trans (Subgroup.card_map_dvd _ _))
  have h2 : ¬ 2 ∣ Nat.card Z := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h
    have hzc : (z : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := hZc z.2
    have hN : (Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hz2 : orderOf (z : K ⧸ CFSG.pCore 2 K) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hz
    have hP : IsPGroup 2 (Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
    have hle : Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K) ≤
        CFSG.pCore 2 (K ⧸ CFSG.pCore 2 K) := le_sSup ⟨hN, hP⟩
    rw [ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
    have h1 : (z : K ⧸ CFSG.pCore 2 K) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    rw [h1, orderOf_one] at hz2
    norm_num at hz2
  have hc2 : Nat.Coprime 2 (Nat.card Z) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
  have hc3 : Nat.Coprime 3 (Nat.card Z) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  exact (Nat.coprime_mul_iff_left (m := 2) (n := 3)).mpr ⟨hc2, hc3⟩

theorem theta_eq_pCore_of_isLThreePi
    (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hS : Sec13.IsLThreePi (K ⧸ aschbacherSolvableCore 3 K)) :
    aschbacherSolvableCore 3 K = CFSG.pCore 2 K := by
  apply theta_eq_pCore_of_map_eq_bot
  have : ((aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  refine KFacts.KS14.ks18Mult_lThreePi (K ⧸ CFSG.pCore 2 K) _ hq.1 (theta_map_le_center hq)
    (coprime_six_card_theta_map hq) ?_
  obtain ⟨p, e, hp, he, hiso⟩ := hS
  exact ⟨p, e, hp, he, Sec21.Item211Proof.isoLThreePi_of_mulEquiv
    (QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K) (aschbacherSolvableCore 3 K)
      pCore_two_le_theta).symm hiso⟩

theorem theta_eq_pCore_of_exceptional (hExc : PartOne.ExceptionalCenterSmallPrimes)
    (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hZ1 : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ aschbacherSolvableCore 3 K) t p f) :
    aschbacherSolvableCore 3 K = CFSG.pCore 2 K := by
  apply theta_eq_pCore_of_map_eq_bot
  set Z := (aschbacherSolvableCore 3 K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) with hZdef
  have : Z.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hZc : Z ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := theta_map_le_center hq
  set e : (K ⧸ CFSG.pCore 2 K) ⧸ Z ≃* K ⧸ aschbacherSolvableCore 3 K :=
    QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 K) (aschbacherSolvableCore 3 K)
      pCore_two_le_theta with he
  have hZ1' : Subgroup.center ((K ⧸ CFSG.pCore 2 K) ⧸ Z) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rw [hZ1, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact (map_eq_one_iff e e.injective).mp hex
  obtain ⟨-, hcomap, -⟩ := LocalCores.quasisimple_central_quotient hq Z hZc
  have hcen : Subgroup.center (K ⧸ CFSG.pCore 2 K) = Z := by
    rw [← hcomap, hZ1', MonoidHom.comap_bot, QuotientGroup.ker_mk']
  have hrep : CFSG.Blueprint.ExceptionalRep
      ((K ⧸ CFSG.pCore 2 K) ⧸ Subgroup.center (K ⧸ CFSG.pCore 2 K)) :=
    Or.inl ⟨t, p, f, ht, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans e) hM⟩
  have hsmall := hExc _ hq hrep
  rw [hcen] at hsmall
  have hcop := coprime_six_card_theta_map hq
  refine Subgroup.eq_bot_of_card_eq _ (by_contra fun h1 => ?_)
  obtain ⟨r, hr, hrZ⟩ := Nat.exists_prime_and_dvd h1
  have hr6 : Nat.Coprime 6 r := Nat.Coprime.coprime_dvd_right hrZ hcop
  have h2 : r ≠ 2 := by
    rintro rfl
    norm_num at hr6
  have h3 : r ≠ 3 := by
    rintro rfl
    norm_num at hr6
  have := hr.two_le
  exact hsmall r hr (by omega) hrZ

end Theta

section Central

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_mem_theta {K : Subgroup G} {c : G}
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (hKp : Group.IsPerfect K)
    (hq : IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (h : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  have hmem : ∀ k : K, c * (k : G) * c⁻¹ * (k : G)⁻¹ ∈ K := fun k =>
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hcK k).mp k.2) (K.inv_mem k.2)
  have hθ : ∀ k : K, (⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hmem k⟩ : K) ∈
      aschbacherSolvableCore 3 K := fun k => by
    obtain ⟨y, hy, hyk⟩ := h k k.2
    have : y = ⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hmem k⟩ := Subtype.ext hyk
    rwa [← this]
  have hZc := theta_map_le_center hq
  have hcen : ∀ k : K, QuotientGroup.mk' (CFSG.pCore 2 K)
      (⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hmem k⟩ : K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) :=
    fun k => hZc ⟨_, hθ k, rfl⟩
  let δ : K →* K ⧸ CFSG.pCore 2 K :=
    { toFun := fun k => QuotientGroup.mk' (CFSG.pCore 2 K) ⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hmem k⟩
      map_one' := by
        have e1 : (⟨c * ((1 : K) : G) * c⁻¹ * ((1 : K) : G)⁻¹, hmem 1⟩ : K) = 1 := by
          apply Subtype.ext
          simp
        rw [e1, map_one]
      map_mul' := fun k l => by
        have e1 : (⟨c * ((k * l : K) : G) * c⁻¹ * ((k * l : K) : G)⁻¹, hmem (k * l)⟩ : K) =
            ⟨c * (k : G) * c⁻¹ * (k : G)⁻¹, hmem k⟩ *
              (k * ⟨c * (l : G) * c⁻¹ * (l : G)⁻¹, hmem l⟩ * k⁻¹) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        simp only [e1, map_mul, map_inv]
        rw [Subgroup.mem_center_iff.mp (hcen l) (QuotientGroup.mk' (CFSG.pCore 2 K) k),
          mul_inv_cancel_right] }
  have hker : commutator K ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hcen y) (δ x)
  intro k hk
  have hk1 : δ ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker]
    exact hker (hKp.commutator_eq_top ▸ Subgroup.mem_top _)
  change QuotientGroup.mk' (CFSG.pCore 2 K) ⟨c * k * c⁻¹ * k⁻¹, hmem ⟨k, hk⟩⟩ = 1 at hk1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp hk1

end Central

section Types

theorem isSimpleGroup_of_type1915 {Y : Type} [Group Y]
    (hY : Group.IsPerfect Y)
    (h : Sec13.IsLThreePi Y ∨ Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    IsSimpleGroup Y := by
  rcases h with ⟨p, e, hp, he, ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩
  · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p e)
    exact MulEquiv.isSimpleGroup φ
  · by_cases hq : p ^ e = 2
    · exfalso
      have hpd : p ∣ 2 := hq ▸ dvd_pow_self p (by omega : e ≠ 0)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hpd
      subst hp2
      have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (hq.trans (pow_one 2).symm)
      subst he1
      have hsU := Sec13.isSolvable_projSU_two
      have hsol : Group.IsSolvable Y :=
        Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have hcard := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
      norm_num at hcard
      have hcY : Nat.card Y = 72 := by
        rw [Nat.card_congr φ.toEquiv]
        omega
      have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
      have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      exact Group.IsPerfect.not_isSolvable Y hsol
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p e he hq
      exact MulEquiv.isSimpleGroup φ
  · have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    exact MulEquiv.isSimpleGroup φ

theorem le_card_of_type1915 {Y : Type} [Group Y] (hY : Group.IsPerfect Y)
    (h : Sec13.IsLThreePi Y ∨ Nonempty (Y ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    20160 ≤ Nat.card Y := by
  rcases h with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩
  · by_cases hq : p ^ e = 2
    · exfalso
      have hpd : p ∣ 2 := hq ▸ dvd_pow_self p (by omega : e ≠ 0)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp hpd
      subst hp2
      have he1 : e = 1 := Nat.pow_right_injective (le_refl 2) (hq.trans (pow_one 2).symm)
      subst he1
      rcases hiso with ⟨h1, -⟩ | ⟨-, ⟨φ⟩⟩
      · norm_num at h1
      · have hsU := Sec13.isSolvable_projSU_two
        have hsol : Group.IsSolvable Y :=
          Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
        have hcard := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
        norm_num at hcard
        have hcY : Nat.card Y = 72 := by
          rw [Nat.card_congr φ.toEquiv]
          omega
        have : Finite Y := Nat.finite_of_card_ne_zero (by omega)
        have : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by omega)
        exact Group.IsPerfect.not_isSolvable Y hsol
    · exact Sec19.Step1915Proof.le_card_of_isoLThreePi he hiso hq
  · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
    norm_num

end Types

section Surj

variable {L J : Type} [Group L] [Group J] [Finite L] [Finite J]

theorem isSolvable_of_isPGroup_two {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) :
    Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hP.isNilpotent
  infer_instance

omit [Finite L] in
theorem comap_pCore_eq_of_surjective (ψ : L →* J) (hψ : Function.Surjective ψ)
    (hJ : IsQuasisimple J) (hL : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) :
    (CFSG.pCore 2 J).comap ψ = CFSG.pCore 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (CFSG.pCore 2 J).comap ψ with hMdef
  have hle : CFSG.pCore 2 L ≤ M := by
    rw [hMdef, ← Subgroup.map_le_iff_le_comap]
    have hN : ((CFSG.pCore 2 L).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hP : IsPGroup 2 ((CFSG.pCore 2 L).map ψ) := CFSG.pCore_isPGroup.map ψ
    exact le_sSup ⟨hN, hP⟩
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance ψ
  have hMm : (M.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
    Subgroup.Normal.map hMn _ (QuotientGroup.mk'_surjective _)
  rcases hL.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (CFSG.pCore 2 L))) with h | h
  · refine le_antisymm (fun x hx => ?_) hle
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 L) x ∈
        M.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    have hMtop : M = ⊤ := by
      have h1 := QuotientGroup.comap_map_mk' (CFSG.pCore 2 L) M
      rw [h, Subgroup.comap_top, sup_eq_right.mpr hle] at h1
      exact h1.symm
    have hJtop : CFSG.pCore 2 J = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := hψ y
      have hx : x ∈ M := hMtop ▸ Subgroup.mem_top x
      exact hx
    have hJ2 : IsPGroup 2 J := by
      intro y
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)) ⟨y, hJtop ▸ Subgroup.mem_top y⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    exact not_isSolvable_of_isQuasisimple hJ (isSolvable_of_isPGroup_two hJ2)

noncomputable def quotientPCoreEquiv (ψ : L →* J) (hψ : Function.Surjective ψ)
    (hJ : IsQuasisimple J) (hL : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) :
    L ⧸ CFSG.pCore 2 L ≃* J ⧸ CFSG.pCore 2 J :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← comap_pCore_eq_of_surjective ψ hψ hJ hL, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk'])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (CFSG.pCore 2 J)).comp ψ)
      ((QuotientGroup.mk'_surjective _).comp hψ))

theorem pCore_eq_bot_of_isSimpleGroup {Y : Type*} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hY : ∃ a b : Y, a * b ≠ b * a) : CFSG.pCore 2 Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 Y) with h | h
  · exact h
  · exfalso
    have hY2 : IsPGroup 2 Y := by
      intro y
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)) ⟨y, h ▸ Subgroup.mem_top y⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    exact not_isSolvable_of_isQuasisimple (LocalCores.isQuasisimple_of_isSimpleGroup hY).1
      (isSolvable_of_isPGroup_two hY2)

end Surj

end CFSG.RankThree.PartTwo.Sec19.Item19Res7Proof
