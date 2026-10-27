module

public import CFSG.LocalAnalysis.ComponentInitial.CLSSmallReeModelInvolutionsInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.Walter.Ree.Model.Fusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.Sporadic.Schreier.TitsInner
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.LocalAnalysis.SteinbergCCCentralQuotientComponentLift

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

section Transport

variable {G H : Type*} [Group G] [Group H]

@[expose] def HasNormalSimpleSL2 (X : Type*) [Group X] (K : Type*) [Field K] : Prop :=
  ∃ S : Subgroup X, S.Normal ∧ IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)

theorem HasNormalSimpleSL2.of_mulEquiv {K : Type*} [Field K] (e : G ≃* H)
    (h : HasNormalSimpleSL2 G K) : HasNormalSimpleSL2 H K := by
  obtain ⟨S, hSn, hSs, ⟨a, b, hab⟩, ⟨φ⟩⟩ := h
  let eS : S ≃* S.map e.toMonoidHom := S.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨S.map e.toMonoidHom, hSn.map _ e.surjective, eS.symm.isSimpleGroup,
    ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩, ⟨eS.symm.trans φ⟩⟩

theorem isComponent_of_hasNormalSimpleSL2 {K : Type*} [Field K] (h : HasNormalSimpleSL2 G K) :
    ∃ L : Subgroup G, CFSG.IsComponent L ∧ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨S, hSn, hSs, hSnab, hφ⟩ := h
  exact ⟨S, ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1, hSn.isSubnormal⟩, hφ⟩

theorem eqLocus_conj_eq_centralizer (x : G) :
    (MulAut.conj x).toMonoidHom.eqLocus (MonoidHom.id G) = Subgroup.centralizer {x} := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  change x * y * x⁻¹ = y ↔ y * x = x * y
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
      _ = y := by group

theorem map_centralizer_singleton (e : G ≃* H) (x : G) :
    (Subgroup.centralizer {x}).map e.toMonoidHom = Subgroup.centralizer {e x} := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  · intro h
    apply e.injective
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply]

theorem HasNormalSimpleSL2.centralizer_of_mulEquiv {K : Type*} [Field K] (e : G ≃* H) (x : G)
    (h : HasNormalSimpleSL2 (Subgroup.centralizer {x}) K) :
    HasNormalSimpleSL2 (Subgroup.centralizer {e x}) K :=
  h.of_mulEquiv (((Subgroup.centralizer {x}).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton e x)))

theorem map_subtype_centralizer_singleton {M : Type*} [Group M] (Γ : Subgroup M) (z : Γ) :
    (Subgroup.centralizer {z}).map Γ.subtype = Γ ⊓ Subgroup.centralizer {(z : M)} := by
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hw))⟩
  · rintro ⟨hyΓ, hy⟩
    exact ⟨⟨y, hyΓ⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy)), rfl⟩

theorem exists_involution_of_inner {A : Type*} [Group A] {K : Type*} [Field K]
    (hZ : Subgroup.center A = ⊥) {α : MulAut A} (hα1 : α ≠ 1) (hα2 : α ^ 2 = 1)
    (hinner : α ∈ inner A) (h : HasNormalSimpleSL2 (α.toMonoidHom.eqLocus (MonoidHom.id A)) K) :
    ∃ x : A, orderOf x = 2 ∧ HasNormalSimpleSL2 (Subgroup.centralizer {x}) K := by
  obtain ⟨x, rfl⟩ := hinner
  have hx2 : x ^ 2 = 1 := by
    have hc : x ^ 2 ∈ Subgroup.center A := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun β : MulAut A => β y) hα2
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * x ^ 2 = x ^ 2 * y * (x ^ 2)⁻¹ * x ^ 2 := by rw [hy]
        _ = x ^ 2 * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  refine ⟨x, orderOf_eq_prime hx2 hx1, h.of_mulEquiv (MulEquiv.subgroupCongr ?_)⟩
  exact eqLocus_conj_eq_centralizer x

end Transport

theorem two_mul_card_SL_two_pow_ne (n a : ℕ) (hn : 2 ≤ n) (ha : 1 ≤ a) :
    2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) ≠ 3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
  intro h
  set s := 3 ^ (2 * a + 1) with hsdef
  have hs2 : s ^ 2 = 9 * 81 ^ a := by
    rw [hsdef, ← pow_mul, show (2 * a + 1) * 2 = 2 + 4 * a by ring, pow_add, pow_mul]
    norm_num
  have h81 : 81 ^ a % 16 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have hs2mod : s ^ 2 % 16 = 9 := by
    rw [hs2, Nat.mul_mod, h81]
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
  have hs27 : 27 ≤ s := by
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hu : (s ^ 2 - 1) % 16 = 8 := by
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hR : s * (s ^ 2 - 1) % 16 = 8 := by
    rw [Nat.mul_mod, hu]
    have hr : s % 16 % 2 = 1 := by omega
    have hr16 : s % 16 < 16 := Nat.mod_lt _ (by norm_num)
    generalize s % 16 = r at hr hr16
    interval_cases r <;> simp_all
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have h729 : 729 ≤ s ^ 2 := by nlinarith
    have : 27 * 728 ≤ s * (s ^ 2 - 1) := Nat.mul_le_mul hs27 (by omega)
    norm_num at h
    omega
  · have h8 : 8 ∣ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ∣ 2 ^ n := pow_dvd_pow 2 hn3
    obtain ⟨c, hc⟩ := h8
    have hL : 2 * (2 ^ n * ((2 ^ n) ^ 2 - 1)) % 16 = 0 := by
      rw [hc]
      apply Nat.mod_eq_zero_of_dvd
      exact ⟨c * ((8 * c) ^ 2 - 1), by ring⟩
    omega

theorem large_Ree_case
    {A : Type} [Group A] {p f : ℕ}
    (h : ReeTitsModel A .twistedF4 p f) (K : Type*) [Field K] {x : A} (hx : orderOf x = 2) :
    ¬ HasNormalSimpleSL2 (Subgroup.centralizer {x}) K := by
  intro hS
  obtain ⟨-, -, -, hp, -, hiso⟩ := ReeTag.large_Ree_model_Schreier A p f h
  obtain ⟨hadm, a, hfa, F, _, _, hF, hw⟩ := h
  subst hp
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have : CharP F ReeTag.F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  obtain ⟨E⟩ := hiso a F hfa hF hw
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  obtain ⟨L, hL, -⟩ := isComponent_of_hasNormalSimpleSL2 (hS.centralizer_of_mulEquiv E x)
  exact (LargeReeInvolution.large_Ree_involution_centralizers_component_free a ha F hF').1 (E x)
    (by rw [MulEquiv.orderOf_eq]; exact hx) L hL

theorem tits_case
    {A : Type} [Group A] {p f : ℕ}
    (h : ReeTitsModel A .Tits p f) (K : Type*) [Field K] {x : A} (hx : orderOf x = 2) :
    ¬ HasNormalSimpleSL2 (Subgroup.centralizer {x}) K := by
  intro hS
  obtain ⟨E⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv A p f h
  obtain ⟨L, hL, -⟩ := isComponent_of_hasNormalSimpleSL2 (hS.centralizer_of_mulEquiv E x)
  exact CFSG.Sporadic.Schreier.Tits.titsD_involution_centralizer_component_free (E x)
    (by rw [MulEquiv.orderOf_eq]; exact hx) L hL

theorem small_Ree_case
    {A : Type} [Group A] {p f : ℕ}
    (h : ReeTitsModel A .twistedG2 p f) (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {x : A} (hx : orderOf x = 2) :
    ¬ HasNormalSimpleSL2 (Subgroup.centralizer {x}) K := by
  intro hS
  obtain ⟨-, -, hp, -, hiso⟩ := small_Ree_model_Schreier A p f h
  obtain ⟨hadm, a, hfa, F, _, _, hF, hw⟩ := h
  subst hp
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have : CharP F ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      (by omega) hF
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  obtain ⟨E⟩ := hiso a F hfa hF hw
  have hF' : Nat.card F = 3 ^ (2 * a + 1) := by rw [hF, hfa]
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion a F hF' w₀ hw₀
  obtain ⟨ψ, hψC, -, -, -, hψ1, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a F hF' w₀ hw₀
  set Γ := ReeTag.G2.reeGamma F a with hΓ
  set t := smallReeH a F (-1) with ht
  set C := smallReeInvCentralizer a F with hCdef
  have hz2 : orderOf ((E x : Γ) : ModGL ReeTag.G2.tag F) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hx
  obtain ⟨g, hgΓ, hgz⟩ := hfus _ (E x).2 hz2
  set gΓ : Γ := ⟨g, hgΓ⟩
  have hz' : ((MulAut.conj gΓ (E x) : Γ) : ModGL ReeTag.G2.tag F) = t := hgz
  have hCeq : Γ ⊓ Subgroup.centralizer {((MulAut.conj gΓ (E x) : Γ) : ModGL ReeTag.G2.tag F)} =
      C := by
    rw [hz', hCdef, smallReeInvCentralizer]
  have hSC : HasNormalSimpleSL2 C K :=
    ((((hS.centralizer_of_mulEquiv E x).centralizer_of_mulEquiv (MulAut.conj gΓ) (E x)).of_mulEquiv
      ((Subgroup.centralizer {MulAut.conj gΓ (E x)}).equivMapOfInjective Γ.subtype
        Γ.subtype_injective)).of_mulEquiv
      (MulEquiv.subgroupCongr (map_subtype_centralizer_singleton Γ _))).of_mulEquiv
      (MulEquiv.subgroupCongr hCeq)
  obtain ⟨S, hSn, hSs, hSnab, ⟨φ⟩⟩ := hSC
  have hScomp : CFSG.IsComponent S :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1, hSn.isSubnormal⟩
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨u, rfl⟩
    exact hψC u
  have htC : t ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨t, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨y, hy, m, hm, rfl⟩ := hc
    refine ⟨⟨y, hy⟩, ?_⟩
    have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).2 hm
    change QuotientGroup.mk' N y = QuotientGroup.mk' N (y * m)
    rw [map_mul, hm1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have hsolv : Group.IsSolvable (C ⧸ N) :=
    CFSG.ComponentClassification.CatalogueBSmallRee.isSolvable_of_isCyclic
  have hF27 : 27 ≤ Nat.card F := by
    rw [hF']
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF2 : Nat.card F ≠ 2 := by omega
  have hF3 : Nat.card F ≠ 3 := by omega
  let e' : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 F le_rfl
      (Or.inr hF2) (Or.inr hF3)
  have : IsSimpleGroup N := e'.isSimpleGroup
  have hNnab : ∃ y z : N, y * z ≠ z * y := by
    obtain ⟨y, z, hyz⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian F
        hF2 hF3
    refine ⟨e'.symm y, e'.symm z, fun h' => hyz ?_⟩
    simpa using congrArg e' h'
  have hSN : S = N :=
    CentralQuotientLift.component_eq_of_quasisimple_normal N
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hNnab).1 hsolv hScomp
  have hcardS : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card ψ.range := by
    rw [← Nat.card_congr φ.toEquiv, hSN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv]
  have hne : (1 : Matrix.SpecialLinearGroup (Fin 2) F) ≠ -1 := by
    intro h1
    have h2 := congrArg (fun u : Matrix.SpecialLinearGroup (Fin 2) F =>
      (u : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.one_apply_eq, Matrix.neg_apply] at h2
    have h3 : ((2 : ℕ) : F) = 0 := by
      push_cast
      linear_combination h2
    rw [CharP.cast_eq_zero_iff F 3] at h3
    omega
  have hker : Nat.card ψ.ker = 2 := by
    have hset : (ψ.ker : Set (Matrix.SpecialLinearGroup (Fin 2) F)) = {1, -1} := Set.ext fun u => by
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hψ1 u
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_pair hne]
  have hmul : Nat.card ψ.ker * Nat.card ψ.range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hSLF : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), hF']
    simp
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hSLK : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), hK]
    simp
  apply two_mul_card_SL_two_pow_ne n a hn ha
  rw [← hSLK, hcardS, ← hSLF, ← hmul, hker]

theorem Ree_Tits_involution_fixed_groups_have_no_normal_even_SL2
    (A : Type) [Group A] (hAs : IsSimpleGroup A)
    (hAnab : ∃ a b : A, a * b ≠ b * a) (K : Type*) [Field K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (τ : StatedLieTag) (p f : ℕ) (hmodel : ReeTitsModel A τ p f)
    (α : MulAut A) (hα1 : α ≠ 1) (hα2 : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id A))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    IsEmpty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  refine ⟨fun φ => ?_⟩
  have hS : HasNormalSimpleSL2 (α.toMonoidHom.eqLocus (MonoidHom.id A)) K :=
    ⟨S, hSn, hSs, hSnab, ⟨φ⟩⟩
  have hZ : Subgroup.center A = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hAnab).2
  cases τ
  case twistedG2 =>
    obtain ⟨x, hx, hSx⟩ := exists_involution_of_inner hZ hα1 hα2
      (CFSG.LocalAnalysis.ComponentInitial.small_Ree_model_involutions_inner A p f hmodel α hα2) hS
    exact small_Ree_case hmodel K hn hK hx hSx
  case twistedF4 =>
    obtain ⟨x, hx, hSx⟩ := exists_involution_of_inner hZ hα1 hα2
      ((large_Ree_model_field_outer_group_and_inner_involutions A p f hmodel).2.2.2.2.2.1 α hα2)
      hS
    exact large_Ree_case hmodel K hx hSx
  case Tits =>
    obtain ⟨E⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv A p f hmodel
    obtain ⟨x, hx, hSx⟩ := exists_involution_of_inner hZ hα1 hα2
      (CFSG.Sporadic.Schreier.Tits.mem_inner_of_congr E
        (CFSG.Sporadic.Schreier.Tits.titsD_mem_inner_of_sq_eq_one
          (by rw [← map_pow, hα2, map_one]))) hS
    exact tits_case hmodel K hx hSx
  all_goals exact hmodel.2.choose_spec.2.elim

end CFSG.LocalAnalysis.SymplecticFourStandard
