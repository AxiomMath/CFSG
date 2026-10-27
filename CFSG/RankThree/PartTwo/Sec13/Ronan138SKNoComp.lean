module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwo
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKCase2
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofCent
import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinM12
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step138CentPGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e → e ∉ F →
      E ⊓ L ≤ K → Sec8.IsZ3PGLThreePi (lBarA e K E) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G),
        Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
          (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K)))

@[expose] def Step138CentL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e → e ∉ F →
      E ⊓ L ≤ K → IsLThreePi (K ⧸ aschbacherSolvableCore 3 K) →
      Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × Sec12.lBar e K) →
      Sec21.IsIrreducibleOn (Sec4.autIn (K ⊓ Subgroup.normalizer (E : Set G)) (E ⊓ K)) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G),
        Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
          (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K)))

@[expose] def Step138CentJ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) → ∀ F : Subgroup G, IsF138N L E F →
    ∀ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E → K ∈ lA E e → e ∉ F →
      E ⊓ L ≤ K →
      Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2) →
      ∀ hcN : c ∈ Subgroup.normalizer (K : Set G),
        Group.IsSolvable ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
          (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K)))

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

section Fix

variable {X : Type} [Group X] [Finite X]

theorem isSolvable_eqLocus_of_inner (hZ : Subgroup.center X = ⊥)
    (hinn : ∀ σ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → ∃ x : X, σ = MulAut.conj x)
    (hcent : ∀ x : X, x ^ 3 = 1 → x ≠ 1 →
      Group.IsSolvable (Subgroup.centralizer ({x} : Set X)))
    {τ : MulAut X} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Group.IsSolvable (τ.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨x, rfl⟩ := hinn τ ⟨1, by rw [pow_one]; exact hτ3⟩
  have hx1 : x ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hx3 : x ^ 3 = 1 := by
    have h2 : x ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun σ : MulAut X => σ g)
        (show MulAut.conj (x ^ 3) = 1 by rw [map_pow]; exact hτ3)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * x ^ 3 = x ^ 3 * g * (x ^ 3)⁻¹ * x ^ 3 := by rw [h3]
        _ = x ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have heq : (MulAut.conj x).toMonoidHom.eqLocus (MonoidHom.id X) =
      Subgroup.centralizer ({x} : Set X) := by
    ext z
    show (MulAut.conj x).toMonoidHom z = MonoidHom.id X z ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    constructor
    · intro h
      calc z * x = x * z * x⁻¹ * x := by rw [h]
        _ = x * z := by group
    · intro h
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [h]
        _ = z := by group
  rw [heq]
  exact hcent x hx3 hx1

theorem isSolvable_eqLocus_alt7
    (ψ : X ≃* alternatingGroup (Fin 7)) {τ : MulAut X} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Group.IsSolvable (τ.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨-, hZ, hinn, -, -⟩ := KFacts.KS14.ks18A7M22 X (Or.inl ⟨ψ⟩)
  refine isSolvable_eqLocus_of_inner hZ hinn (fun x hx3 hx1 => ?_) hτ3 hτ1
  exact Sec16.Res162.isSolvable_of_forall_commute ψ hx3 hx1 _
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp hk)

theorem isSolvable_eqLocus_m22
    (ψ : X ≃* CFSG.Blueprint.NativeSporadic.M22) {τ : MulAut X} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) : Group.IsSolvable (τ.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨-, hZ, hinn, -, -⟩ := KFacts.KS14.ks18A7M22 X (Or.inr ⟨ψ⟩)
  refine isSolvable_eqLocus_of_inner hZ hinn (fun x hx3 hx1 => ?_) hτ3 hτ1
  have hcard := (KFacts.KP4.m22_centralizer_facts_of_orderOf ⟨ψ⟩ (orderOf_eq_prime hx3 hx1)).1
  exact Sec4.Census.isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 2) (b := 2)
    (by rw [hcard]; norm_num)

theorem isSolvable_eqLocus_m12
    (ψ : X ≃* CFSG.Blueprint.NativeSporadic.M12) {τ : MulAut X} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) : Group.IsSolvable (τ.toMonoidHom.eqLocus (MonoidHom.id X)) := by
  obtain ⟨-, hZ, hinn, -⟩ := KFacts.ks18M12 X ⟨ψ⟩
  refine isSolvable_eqLocus_of_inner hZ hinn (fun x hx3 hx1 => ?_) hτ3 hτ1
  have hord : orderOf (ψ x) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hx3 hx1
  have hS := GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinM12.isSolvable_centralizer Nat.prime_three
    (by norm_num) (ψ x) hord
  have hmap : (Subgroup.centralizer ({x} : Set X)).map ψ.toMonoidHom =
      Subgroup.centralizer ({ψ x} : Set CFSG.Blueprint.NativeSporadic.M12) :=
    CFSG.RankThree.PartTwo.map_centralizer_singleton ψ x
  let e1 : Subgroup.centralizer ({x} : Set X) ≃*
      Subgroup.centralizer ({ψ x} : Set CFSG.Blueprint.NativeSporadic.M12) :=
    ((Subgroup.centralizer ({x} : Set X)).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective

end Fix

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem thetaComponents_eq_empty_of_isSolvable {K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (K : Set G)) (hc3 : c ^ 3 = 1)
    (hsolv : Group.IsSolvable
      ((Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (K ⧸ aschbacherSolvableCore 3 K)))) :
    thetaComponents 3 ↥(K ⊓ Subgroup.centralizer ({c} : Set G)) = ∅ := by
  ext T
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hT
  exact Sec11.fieldCent_false_of_isSolvable hcN hc3 ⟨T, hT, rfl⟩ hsolv

theorem residual_le_of_not_mem (h48 : Sec4.Item4_8) (hKF : KF138TypeTwo)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t) {e : G}
    {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∉ F) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) ≤ K := by
  have hH := hfr.hH
  have hD := hH.1
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hfr.hE3 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    have := (zpowers_mem_omegaA_iff.mp heΩ).2.1
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
    norm_num at this
  have hcLF : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ F := by
    refine sup_le (Subgroup.zpowers_le.mpr hfr.hcF) ?_
    rw [hfr.hEL]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2
  obtain ⟨hdJ, hJq⟩ := hKF G A c L E hH hfr.hPGL e heE (fun h => heF (hcLF h))
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hJdef
  have hdJ' : ⁅x, y⁆ ∈ J := hdJ (hfr.hEL ▸ Subgroup.mem_zpowers _)
  have hL := hD.mem_thetaComponentsAt
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({e} : Set G)) :=
    hD.toPartTwoStanding.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one hD.toPartTwoStanding.toTheoremFourHyp he1)
  have hE27' : Late.IsE27 E := ⟨hH.2.2.2.1, hfr.hE27⟩
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27' hfr.hcE
    heE hfr.hc1 hL hJq
  have hKK' : K' = K := by
    by_contra hne
    have hK'K : K' ≤ Sec4.thetaQuotCentralizer K := by
      rw [thetaComponentsAt_eq_thetaComponentsIn] at hK'
      have hK1 := hK.1
      rw [thetaComponentsAt_eq_thetaComponentsIn] at hK1
      exact Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in hK' hK1 hne
    have hdC : ⁅x, y⁆ ∈ Sec4.thetaQuotCentralizer K := hK'K (hJK' hdJ')
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hd' : ⁅x, y⁆ ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hfr.hdE, hdC⟩
    rw [← hCE] at hd'
    have heq := zpowers_eq_of_mem hfr.hd3 hfr.hd1 he3 he1 hd'
    apply heF
    have he : e ∈ Subgroup.zpowers ⁅x, y⁆ := heq ▸ Subgroup.mem_zpowers e
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2 he
  subst hKK'
  exact hJK'

theorem inf_le_of_not_mem (h48 : Sec4.Item4_8) (hKF : KF138TypeTwo)
    {A L E F : Subgroup G} {c x y t : G} (hfr : Frame138 A L E F c x y t) {e : G}
    {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∉ F) :
    E ⊓ L ≤ K := by
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have hcLF : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ F := by
    refine sup_le (Subgroup.zpowers_le.mpr hfr.hcF) ?_
    rw [hfr.hEL]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2
  exact (hKF G A c L E hfr.hH hfr.hPGL e heE (fun h => heF (hcLF h))).1.trans
    (residual_le_of_not_mem h48 hKF hfr heΩ hK heF)

theorem step138NoCompF_of_cent
    (hspor : SporadicModels131) (h48 : Sec4.Item4_8) (hsetAt : Item13SetupAt) (h133 : Item133)
    (hENeD : Step138ENeD) (hPGLc : Step138CentPGL) (hL3c : Step138CentL3)
    (hJ2c : Step138CentJ2) : Step138NoCompF := by
  intro G _ _ A c L E hH hPGL F hF e K heΩ hK heF
  obtain ⟨x, y, t, hfr⟩ := exists_frame138_t hH hF hPGL
  have hcΩ := zpowers_not_mem_omegaA hsetAt hH hfr.hdE hfr.hdL hfr.hdc
  have hdΩ := hENeD G A c L E hH hPGL
  have hEL := inf_le_of_not_mem h48 Ronan138S.kf138TypeTwo hfr heΩ hK heF
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, -, -, -, hST, -⟩ := hH'
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hK.2.1 hcE
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  refine thetaComponents_eq_empty_of_isSolvable hcN hc3 ?_
  have hτ3 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one, map_one]
  have hτ1 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) ≠ 1 := by
    intro h1
    have hcC : c ∈ Sec4.thetaQuotCentralizer K :=
      Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mpr ⟨hcN, h1⟩
    have hCE := sectionCentralizer_eq_inf hK.2.1
    rw [hK.2.2.1] at hCE
    have hc' : c ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hcE, hcC⟩
    rw [← hCE] at hc'
    have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
    have he1 : e ≠ 1 := by
      rintro rfl
      have := (zpowers_mem_omegaA_iff.mp heΩ).2.1
      rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at this
      norm_num at this
    have heq := zpowers_eq_of_mem hc3 hfr.hc1 (hfr.hE3 e heE) he1 hc'
    apply heF
    have he : e ∈ Subgroup.zpowers c := heq ▸ Subgroup.mem_zpowers e
    exact Subgroup.zpowers_le.mpr hfr.hcF he
  rcases h133 G E e K hD hST with h1 | ⟨-, hφ, -⟩ | ⟨hirr, -, -, -, -, -, -, hφ3, hK3⟩ |
      hPGLK | hφ | hHJ
  · exact (false_of_case1 hfr hcΩ hdΩ heΩ h1).elim
  · obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv hD isPerfect_center_alt7.1 φ
    exact isSolvable_eqLocus_alt7 ψ hτ3 hτ1
  · rcases hK3 with hL3 | hψ | hψ
    · exact hL3c G A c L E hH hPGL F hF e K heΩ hK heF hEL hL3 hφ3 hirr hcN
    · obtain ⟨ψ⟩ := hψ
      exact isSolvable_eqLocus_alt7 ψ hτ3 hτ1
    · obtain ⟨ψ⟩ := hψ
      exact isSolvable_eqLocus_m22 ψ hτ3 hτ1
  · exact hPGLc G A c L E hH hPGL F hF e K heΩ hK heF hEL hPGLK hcN
  · obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv hD hspor.2.1.1 φ
    exact isSolvable_eqLocus_m12 ψ hτ3 hτ1
  · exact hJ2c G A c L E hH hPGL F hF e K heΩ hK heF hEL hHJ hcN

end Reduction

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
