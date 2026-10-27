module

public import CFSG.Quasithin.Background.C41PfDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearInvolutions
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace C41Pf

section General

@[expose] noncomputable def quotMulAutHom {L : Type*} [Group L] (N : Subgroup L)
    [N.Characteristic] : MulAut L →* MulAut (L ⧸ N) where
  toFun φ := QuotientGroup.congr N N φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] {A : Subgroup X}
    (hA : ⁅A, A⁆ = A) (hs : Group.IsSolvable ↥A) : A = ⊥ := by
  have htop : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = (⊤ : Subgroup ↥A) := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hA]
  have hds : ∀ n : ℕ, derivedSeries ↥A n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, htop]
  obtain ⟨n, hn⟩ := hs.solvable
  rw [hds n] at hn
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  have : (⟨a, ha⟩ : ↥A) ∈ (⊥ : Subgroup ↥A) := hn ▸ Subgroup.mem_top _
  exact congrArg Subtype.val (Subgroup.mem_bot.mp this)

theorem isSolvable_normalizer_of_odd_index {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) :
    Group.IsSolvable ↥(Subgroup.normalizer (P : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (P : Set X) with hN
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hTn : (P.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hS : Group.IsSolvable ↥P := by
    have := hP.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥(P.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hPN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPN).injective
  have hodd' : Odd (Nat.card (↥N ⧸ P.subgroupOf N)) := by
    change Odd (P.relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => hodd ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (Subgroup.relIndex_dvd_index_of_le hPN)
  have hQ : Group.IsSolvable (↥N ⧸ P.subgroupOf N) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  exact Group.isSolvable_of_ker_le_range (P.subgroupOf N).subtype
    (QuotientGroup.mk' (P.subgroupOf N))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end General

section Core

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def quotConjHom (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (quotMulAutHom (CFSG.pCore 2 ↥K)).comp (Subgroup.normalizerMonoidHom K)

omit [Finite G] in
theorem quotConjHom_mk (K : Subgroup G) (g : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    quotConjHom K g (k : ↥K ⧸ CFSG.pCore 2 ↥K) =
      (((Subgroup.normalizerMonoidHom K g) k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) :=
  rfl

theorem commutator_le_pCoreOf_of_outSolvable {K D S : Subgroup G}
    (hOut : OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hD : ⁅D, D⁆ = D) (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hS : IsSylowTwoOf S K)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) : ⁅D, K⁆ ≤ pCoreOf 2 K := by
  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hX
  set π : ↥K →* X := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set ψ : ↥D →* MulAut X := (quotConjHom K).comp (Subgroup.inclusion hDK) with hψ
  have htop : ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ = (⊤ : Subgroup ↥D) := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hD]
  have hDp : Group.IsPerfect ↥D := Group.isPerfect_def.mpr htop
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [← hZ, Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hx)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hrange : ∀ d : ↥D, ψ d ∈ (MulAut.conj : X →* MulAut X).range := by
    intro d
    obtain ⟨x, hx⟩ := A38.exists_inner_of_outSolvable hOut hDp ψ d
    exact ⟨x, hx.symm⟩
  set e := MonoidHom.ofInjective hinj with he
  set χ : ↥D →* X := e.symm.toMonoidHom.comp (ψ.codRestrict _ hrange) with hχdef
  have hχ : ∀ d : ↥D, MulAut.conj (χ d) = ψ d := by
    intro d
    have h1 : e (χ d) = ψ.codRestrict _ hrange d := e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  set S' := S.subgroupOf K with hS'
  set Sb := S'.map π with hSb
  have hS'p : IsPGroup 2 ↥S' := hS.2.1.comap_subtype
  have hSbp : IsPGroup 2 ↥Sb := hS'p.map π
  have hSbodd : ¬ 2 ∣ Sb.index := fun h =>
    hS.2.2 (h.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))
  have hψS : ∀ (d : ↥D) (s : ↥K), (s : G) ∈ S → ψ d (π s) ∈ Sb := by
    intro d s hs
    refine ⟨(Subgroup.normalizerMonoidHom K ⟨d, hDK d.2⟩) s, ?_, rfl⟩
    show _ ∈ S.subgroupOf K
    rw [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (hDS d.2) s).mp hs
  have hχN : χ.range ≤ Subgroup.normalizer (Sb : Set X) := by
    rintro _ ⟨d, rfl⟩
    have hle : ∀ d : ↥D, ∀ y ∈ Sb, χ d * y * (χ d)⁻¹ ∈ Sb := by
      intro d y hy
      obtain ⟨s, hs, rfl⟩ := hy
      have h1 := congrArg (fun φ : MulAut X => φ (π s)) (hχ d)
      simp only [MulAut.conj_apply] at h1
      rw [h1]
      exact hψS d s hs
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨hle d y, fun hy => ?_⟩
    have h2 := hle d⁻¹ _ hy
    rw [map_inv, inv_inv] at h2
    simpa [mul_assoc] using h2
  have hsol : Group.IsSolvable ↥χ.range :=
    have := isSolvable_normalizer_of_odd_index hSbp hSbodd
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hχN)
      (Subgroup.inclusion_injective hχN)
  have hperf : ⁅χ.range, χ.range⁆ = χ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  have hχ1 := eq_bot_of_perfect_of_isSolvable hperf hsol
  rw [Subgroup.commutator_le]
  intro d hd k hk
  have h1 : χ ⟨d, hd⟩ = 1 := by
    have : χ ⟨d, hd⟩ ∈ χ.range := ⟨⟨d, hd⟩, rfl⟩
    rw [hχ1] at this
    exact Subgroup.mem_bot.mp this
  have h2 : ψ ⟨d, hd⟩ = 1 := by rw [← hχ, h1, map_one]
  have h3 := congrArg (fun φ : MulAut X => φ (π ⟨k, hk⟩)) h2
  simp only [MulAut.one_apply] at h3
  rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, quotConjHom_mk] at h3
  have h4 := QuotientGroup.eq.mp h3
  set y : ↥K := (Subgroup.normalizerMonoidHom K (Subgroup.inclusion hDK ⟨d, hd⟩)) ⟨k, hk⟩ with hy
  have hyv : (y : G) = d * k * d⁻¹ := Subgroup.normalizerMonoidHom_apply_apply_coe K _ _
  have hz : y * (y⁻¹ * ⟨k, hk⟩)⁻¹ * y⁻¹ ∈ CFSG.pCore 2 ↥K :=
    (inferInstance : (CFSG.pCore 2 ↥K).Normal).conj_mem _ (inv_mem h4) y
  have hz' : ((y * (y⁻¹ * ⟨k, hk⟩)⁻¹ * y⁻¹ : ↥K) : G) = ⁅d, k⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyv, commutatorElement_def]
    group
  rw [← hz']
  exact ⟨_, by assumption, rfl⟩

omit [Finite G] in
@[expose] noncomputable def modO2Equiv {K : Subgroup G} {X : Type*} [Group X] (α : ↥K →* X)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

omit [Finite G] in
theorem outSolvable_center_of_sl2 {K : Subgroup G} {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (α : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) ∧ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  set e := modO2Equiv α hα hker with he
  refine ⟨?_, ?_⟩
  · have hc : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (CFSG.GorensteinWalter.PSL2 F)) :=
      Group.isSolvable_of_comm
        (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm F)
    have := CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv
      (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.psl2CharTwoEquivSL.trans e.symm)
    exact CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer this
  · rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.sl2_charTwo_center_eq_bot,
      Subgroup.map_bot]

omit [Finite G] in
theorem outSolvable_center_of_alt5 {K : Subgroup G} (α : ↥K →* alternatingGroup (Fin 5))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) ∧ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  set e := modO2Equiv α hα hker with he
  refine ⟨⟨1, fun φ hφ => ?_⟩, ?_⟩
  · set A := CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm e with hA
    have h1 : A φ ∈ alternatingGroup (Fin 5) := by
      have hc : φ ∈ commutator (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        rwa [derivedSeries_one] at hφ
      have h2 := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp A.toMonoidHom) hc
      exact h2
    refine ⟨e.symm ⟨A φ, h1⟩, ?_⟩
    rw [← CFSG.LieType.SteinbergBR.AltFiveGL3.autEquivPerm_symm_eq_conj e h1,
      MulEquiv.symm_apply_apply]
  · rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
      alternatingGroup.center_eq_bot (by simp), Subgroup.map_bot]

end Core

theorem c41KGBorel_holds : C41KGBorel := by
  intro G _ _ K D S hq htype hD hDK hS hDS
  rcases htype with ⟨n, -, F, _, _, hF, α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩ | ⟨α, hα, hker, -⟩
  · obtain ⟨hOut, hZ⟩ := C41Pf.outSolvable_center_of_sl2 hF α hα hker
    exact C41Pf.commutator_le_pCoreOf_of_outSolvable hOut hZ hD hDK hS hDS
  · exfalso
    set e := C41Pf.modO2Equiv α hα hker with he
    have hcomm3 : ∀ a b : alternatingGroup (Fin 3), a * b = b * a := by decide
    have hcomm : ∀ x y : ↥K ⧸ CFSG.pCore 2 ↥K, x * y = y * x := fun x y =>
      e.injective (by rw [map_mul, map_mul, hcomm3])
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm])
  · obtain ⟨hOut, hZ⟩ := C41Pf.outSolvable_center_of_alt5 α hα hker
    exact C41Pf.commutator_le_pCoreOf_of_outSolvable hOut hZ hD hDK hS hDS

end C41Pf

end CFSG.Quasithin
