module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowAut
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsAutL3
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLinAlg
public import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieTools
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GH74.GLS.IVK (fixedField)
open scoped commutatorElement

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul]
  norm_num [Nat.pow_mod]

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

theorem three_ne_zero_of_charTwo (F : Type) [Field F] [CharP F 2] : (3 : F) ≠ 0 := by
  intro h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) = 1 + 2 := by norm_num
  rw [h3, h2, add_zero] at h
  exact one_ne_zero h

theorem two_dvd_card_of_isTypeEpsCube {X : Type} [Group X] (h : IsTypeEpsCube X) :
    2 ∣ Nat.card X := by
  obtain ⟨p, g, -, -, -, hcase⟩ := card_of_isTypeEpsCube_prime h
  have key : 2 ∣ p ^ g ∨ 2 ∣ (p ^ g) ^ 6 - 1 := by
    rcases Nat.even_or_odd (p ^ g) with he | ho
    · exact Or.inl (even_iff_two_dvd.mp he)
    · exact Or.inr (even_iff_two_dvd.mp (Nat.Odd.sub_odd ho.pow odd_one))
  rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩ <;> rw [hc]
  · rcases key with h2 | h2
    · exact dvd_mul_of_dvd_left (dvd_pow h2 (by norm_num)) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 _) _
  · rcases key with h2 | h2
    · exact dvd_mul_of_dvd_left (dvd_pow h2 (by norm_num)) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 _) _

theorem exists_omega_of_card {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : Even n) : ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have := two_pow_mod_three_of_even hn
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx3 : (x : F) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    have := congrArg (fun y : Fˣ => (y : F)) h
    simpa using this
  have hx1 : (x : F) ≠ 1 := by
    intro h
    have hx' : x = 1 := Units.ext h
    rw [hx', orderOf_one] at hx
    norm_num at hx
  refine ⟨x, ?_⟩
  have h : ((x : F) - 1) * ((x : F) ^ 2 + x + 1) = 0 := by linear_combination hx3
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hx1
  · exact h

theorem false_of_fieldCase {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn2 : 2 ≤ n)
    {A : Subgroup (MulAut (projectiveSL 3 F))} {α : MulAut (projectiveSL 3 F)}
    {K : Subgroup (projectiveSL 3 F)} (hc : CfgSEps (projectiveSL 3 F) A α K)
    (hD : α ∉ linearAutGroup 3 F) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hc.isPerfect
  have hα3 : α ^ 3 = 1 := hc.pow_three
  obtain ⟨φ, hφ, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
  have hr : MulAut.congr (MulEquiv.refl (projectiveSL 3 F)) α = α := MulEquiv.ext fun x => rfl
  have hστ : MulAut.congr ((MulEquiv.refl (projectiveSL 3 F)).trans (conjAut 3 F H)⁻¹) α =
      fieldAut 3 F φ := by
    rw [congr_trans_mulAut, hr, hαH]
    group
  have h3dvd : 3 ∣ Nat.card ↥K :=
    (three_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)).trans
      (Subgroup.card_quotient_dvd_card _)
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hk3 : k ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k
    rwa [hk] at h
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    norm_num at hk
  have hkP : (k : projectiveSL 3 F) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have h3 : ∃ k' ∈ K, k' ≠ 1 ∧ k' ^ 3 = 1 :=
    ⟨k, k.2, hkP, by
      have := congrArg Subtype.val hk3
      simpa using this⟩
  have hnt : K ≠ ⊥ := by
    intro hb
    have hmem : (k : projectiveSL 3 F) ∈ (⊥ : Subgroup (projectiveSL 3 F)) := by
      rw [← hb]
      exact k.2
    exact hkP (Subgroup.mem_bot.mp hmem)
  obtain ⟨⟨eK⟩, -⟩ := fieldCase_linear _ hστ (fun x => mem_autFix) hc.le_autFix hnt
    hc.isSubnormal h3
  obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
  obtain ⟨m, rfl⟩ := h3n
  have hm : 1 ≤ m := by omega
  have hcube : Nat.card F = (2 ^ m) ^ 3 := by rw [hF, ← pow_mul, mul_comm]
  have hK₀ : Nat.card (fixedField φ) = 2 ^ m := card_fixedField_of_orderOf_eq_three hφ hcube
  have hmod : 2 ^ m % 3 = 1 := by
    have h1 := two_pow_mod_three_of_even hn
    rw [show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm], cube_mod_three] at h1
    exact h1
  have ψ : fixedField φ ≃+* GaloisField 2 m :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 m (by omega) hK₀
  obtain ⟨φ₁⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 m)
  haveI := isSimpleGroup_projectiveSL_three (fixedField φ)
  haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hpc : CFSG.pCore 2 ↥K = ⊥ := by
    haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥K) with h | h
    · exact h
    · exfalso
      have hidx : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
        show (CFSG.pCore 2 ↥K).index = 1
        rw [h, Subgroup.index_top]
      have h3' := three_dvd_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
      rw [hidx] at h3'
      norm_num at h3'
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  have eQ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
  have hiso : IsoLThreePi (↥K ⧸ CFSG.pCore 2 ↥K) 2 m :=
    Or.inl ⟨hmod, ⟨((eQ.trans eK).trans
      (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr ψ)).trans φ₁.symm⟩⟩
  exact false_of_isTypeEps_of_isoLThreePi hc.isType hm hiso

theorem finite_projectiveSL_three (F : Type) [Field F] [Finite F] :
    Finite (projectiveSL 3 F) :=
  Finite.of_surjective (LinearFlag.proj 3 F) (LinearFlag.proj_surjective 3 F)

attribute [local instance] finite_projectiveSL_three

noncomputable abbrev slConj {F : Type} [Field F] (g : GL (Fin 3) F) : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F g

abbrev C0 {F : Type} [Field F] (g : GL (Fin 3) F) : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
  (Subgroup.centralizer ({g} : Set (GL (Fin 3) F))).comap Matrix.SpecialLinearGroup.toGL

theorem slPi_true_eq_range (F : Type) [Field F] (q : ℕ) :
    slPi true 3 q F = Matrix.SpecialLinearGroup.toGL.range :=
  CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 F

theorem scalar_mem_center {F : Type} [Field F] (v : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) v ∈ Subgroup.center (GL (Fin 3) F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨v, rfl⟩

theorem mem_C0 {F : Type} [Field F] {g : GL (Fin 3) F} {x : Matrix.SpecialLinearGroup (Fin 3) F} :
    x ∈ C0 g ↔ Matrix.SpecialLinearGroup.toGL x * g = g * Matrix.SpecialLinearGroup.toGL x :=
  Subgroup.mem_comap.trans Subgroup.mem_centralizer_singleton_iff

theorem toGL_slConj {F : Type} [Field F] (g : GL (Fin 3) F) (x : Matrix.SpecialLinearGroup (Fin 3) F) :
    Matrix.SpecialLinearGroup.toGL (slConj g x) = g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ := by
  apply Units.ext
  exact coe_slConjugation g x

theorem slConj_eq_of_comm {F : Type} [Field F] {g : GL (Fin 3) F}
    {x : Matrix.SpecialLinearGroup (Fin 3) F}
    (hx : Matrix.SpecialLinearGroup.toGL x * g = g * Matrix.SpecialLinearGroup.toGL x) :
    slConj g x = x := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConj]
  calc g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ = (Matrix.SpecialLinearGroup.toGL x * g) * g⁻¹ := by
        rw [hx]
    _ = Matrix.SpecialLinearGroup.toGL x := by group

theorem comm_of_slConj_eq {F : Type} [Field F] {g : GL (Fin 3) F}
    {x : Matrix.SpecialLinearGroup (Fin 3) F} (h : slConj g x = x) :
    Matrix.SpecialLinearGroup.toGL x * g = g * Matrix.SpecialLinearGroup.toGL x := by
  have h1 : Matrix.SpecialLinearGroup.toGL x = g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ := by
    rw [← toGL_slConj, h]
  calc Matrix.SpecialLinearGroup.toGL x * g = (g * Matrix.SpecialLinearGroup.toGL x * g⁻¹) * g := by
        rw [← h1]
    _ = g * Matrix.SpecialLinearGroup.toGL x := by group

theorem conjAut_proj_eq_self_of_comm {F : Type} [Field F] (g : GL (Fin 3) F)
    (x : Matrix.SpecialLinearGroup (Fin 3) F)
    (hx : Matrix.SpecialLinearGroup.toGL x * g = g * Matrix.SpecialLinearGroup.toGL x) :
    conjAut 3 F g (LinearFlag.proj 3 F x) = LinearFlag.proj 3 F x := by
  rw [conjAut_proj, slConj_eq_of_comm hx]

theorem commutatorElement_mul_central_eq {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  have hzx : ∀ x : G, z * x * z⁻¹ = x := fun x => by
    rw [(hz' x).symm, mul_assoc, mul_inv_cancel, mul_one]
  have hwx : ∀ x : G, w * x * w⁻¹ = x := fun x => by
    rw [(hw' x).symm, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w) * z⁻¹) * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * (b * w) * a⁻¹ * (b * w)⁻¹ := by rw [hzx]
    _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwx]

theorem map_proj_commutator_comap {F : Type} [Field F] [Finite F]
    (K : Subgroup (projectiveSL 3 F)) [Group.IsPerfect ↥K] :
    Subgroup.map (LinearFlag.proj 3 F) ⁅K.comap (LinearFlag.proj 3 F),
      K.comap (LinearFlag.proj 3 F)⁆ = K := by
  rw [Subgroup.map_commutator]
  have hm : Subgroup.map (LinearFlag.proj 3 F) (K.comap (LinearFlag.proj 3 F)) = K := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (LinearFlag.proj_surjective 3 F),
      top_inf_eq]
  rw [hm]
  have h1 : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ := by
    rw [← commutator_def ↥K]
    exact Group.isPerfect_def.mp inferInstance
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) (⊤ : Subgroup ↥K) K.subtype
  rw [h1] at h2
  have hT : Subgroup.map K.subtype (⊤ : Subgroup ↥K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hT] at h2
  exact h2.symm

theorem isPerfect_commutator_comap {F : Type} [Field F] [Finite F]
    (K : Subgroup (projectiveSL 3 F)) [Group.IsPerfect ↥K] :
    Group.IsPerfect ↥(⁅K.comap (LinearFlag.proj 3 F), K.comap (LinearFlag.proj 3 F)⁆ :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  set Kt := K.comap (LinearFlag.proj 3 F) with hKt
  set K₁ := ⁅Kt, Kt⁆ with hK₁
  have hK₁K : K₁.map (LinearFlag.proj 3 F) = K := map_proj_commutator_comap K
  have hdec : ∀ a ∈ Kt, ∃ a' ∈ K₁, ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F),
      a = a' * z := by
    intro a ha
    have hpa : LinearFlag.proj 3 F a ∈ K := ha
    rw [← hK₁K] at hpa
    obtain ⟨a', ha', hpa'⟩ := Subgroup.mem_map.mp hpa
    have hz : a'⁻¹ * a ∈ scalars 3 F := LinearFlag.proj_eq_proj_iff.mp hpa'
    exact ⟨a', ha', a'⁻¹ * a, scalars_le_center 3 F hz, (mul_inv_cancel_left a' a).symm⟩
  have hle : K₁ ≤ ⁅K₁, K₁⁆ := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨a', ha', z, hz, rfl⟩ := hdec a ha
    obtain ⟨b', hb', w, hw, rfl⟩ := hdec b hb
    rw [commutatorElement_mul_central_eq hz hw]
    exact Subgroup.commutator_mem_commutator ha' hb'
  have hperf : (⁅(⊤ : Subgroup ↥K₁), ⊤⁆ : Subgroup ↥K₁) = ⊤ := by
    have hT : (⊤ : Subgroup ↥K₁).map K₁.subtype = K₁ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmap : (⁅(⊤ : Subgroup ↥K₁), ⊤⁆ : Subgroup ↥K₁).map K₁.subtype = ⁅K₁, K₁⁆ := by
      rw [Subgroup.map_commutator, hT]
    rw [eq_top_iff]
    intro x _
    have h1 : (x : Matrix.SpecialLinearGroup (Fin 3) F) ∈
        (⁅(⊤ : Subgroup ↥K₁), ⊤⁆ : Subgroup ↥K₁).map K₁.subtype := by
      rw [hmap]
      exact hle x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
    have hxy : y = x := Subtype.ext hyx
    rw [← hxy]
    exact hy
  exact Group.isPerfect_def.mpr (by rw [commutator_def]; exact hperf)

theorem commutator_comap_le_C0 {F : Type} [Field F] [Finite F] (K : Subgroup (projectiveSL 3 F))
    {g : GL (Fin 3) F} (hfix : ∀ k ∈ K, conjAut 3 F g k = k) :
    ⁅K.comap (LinearFlag.proj 3 F), K.comap (LinearFlag.proj 3 F)⁆ ≤ C0 g := by
  have hdec : ∀ a ∈ K.comap (LinearFlag.proj 3 F),
      ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F), slConj g a = a * z := by
    intro a ha
    have hfa : conjAut 3 F g (LinearFlag.proj 3 F a) = LinearFlag.proj 3 F a :=
      hfix _ (Subgroup.mem_comap.mp ha)
    rw [conjAut_proj] at hfa
    have hz : a⁻¹ * slConj g a ∈ scalars 3 F := LinearFlag.proj_eq_proj_iff.mp hfa.symm
    exact ⟨a⁻¹ * slConj g a, scalars_le_center 3 F hz, (mul_inv_cancel_left a _).symm⟩
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  obtain ⟨za, hza, hθa⟩ := hdec a ha
  obtain ⟨zb, hzb, hθb⟩ := hdec b hb
  have hθ : slConj g ⁅a, b⁆ = ⁅a, b⁆ := by
    rw [map_commutatorElement, hθa, hθb, commutatorElement_mul_central_eq hza hzb]
  exact mem_C0.mpr (comm_of_slConj_eq hθ)

theorem not_odd_card_C0 {F : Type} [Field F] [Finite F] [CharP F 2] (g : GL (Fin 3) F)
    (K : Subgroup (projectiveSL 3 F)) (K₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
    (h1 : K₁.map (LinearFlag.proj 3 F) = K) (h2 : K₁ ≤ C0 g)
    (h3 : IsTypeEpsCube (↥K ⧸ CFSG.pCore 2 ↥K)) : ¬ Odd (Nat.card ↥(C0 g)) := by
  intro hodd
  have hK : Nat.card ↥K ∣ Nat.card ↥K₁ := by
    rw [← h1]
    exact Subgroup.card_map_dvd K₁ (LinearFlag.proj 3 F)
  have hK₁ : Nat.card ↥K₁ ∣ Nat.card ↥(C0 g) := Subgroup.card_dvd_of_le h2
  have hQ : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ∣ Nat.card ↥K := Subgroup.card_quotient_dvd_card _
  have h2' : 2 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := two_dvd_card_of_isTypeEpsCube h3
  have h4 : 2 ∣ Nat.card ↥(C0 g) := h2'.trans (hQ.trans (hK.trans hK₁))
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h4)

theorem card_C0_eq {F : Type} [Field F] (g : GL (Fin 3) F) (q : ℕ) :
    Nat.card ↥(C0 g) = Nat.card ↥(slPi true 3 q F ⊓ Subgroup.centralizer ({g} : Set (GL (Fin 3) F))) := by
  calc Nat.card ↥(C0 g)
      = Nat.card ↥((C0 g).map Matrix.SpecialLinearGroup.toGL) :=
        (Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective).symm
    _ = Nat.card ↥(Matrix.SpecialLinearGroup.toGL.range ⊓
          Subgroup.centralizer ({g} : Set (GL (Fin 3) F))) := by
        rw [C0, Subgroup.map_comap_eq]
    _ = Nat.card ↥(slPi true 3 q F ⊓ Subgroup.centralizer ({g} : Set (GL (Fin 3) F))) := by
        rw [slPi_true_eq_range]

theorem odd_card_C0_of_no_cube_root {F : Type} [Field F] [Finite F] [CharP F 2]
    {g : GL (Fin 3) F} {c : F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hno : ¬ ∃ μ : F, μ ^ 3 = c) : Odd (Nat.card ↥(C0 g)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht] at h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  set x : Matrix.SpecialLinearGroup (Fin 3) F := (t : Matrix.SpecialLinearGroup (Fin 3) F) with hx
  set T : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hT
  have hx2 : x ^ 2 = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have hTT : T * T = 1 := by
    have h := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) hx2
    simpa [sq, hT] using h
  have hT1 : T ≠ 1 := by
    intro h
    apply ht1
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrFun (congrFun h i) j
    simpa [hT] using this
  have h2 : ∀ M : Matrix (Fin 3) (Fin 3) F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  have hN : T - 1 ≠ 0 := sub_ne_zero.mpr hT1
  have hNN : (T - 1) * (T - 1) = 0 := by
    calc (T - 1) * (T - 1) = T * T - (T + T) + 1 := by noncomm_ring
      _ = 0 := by rw [hTT, h2 T, sub_zero, h2 1]
  have hcomm : T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T :=
    congrArg Units.val (mem_C0.mp t.2)
  have hgN : (g : Matrix (Fin 3) (Fin 3) F) * (T - 1) = (T - 1) * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hcomm]
  obtain ⟨v, μ, hv, hgv⟩ := exists_eigenvector_of_commute_sq_zero hN hNN hgN
  exact hno ⟨μ, pow_three_eq_of_eigenvector hg hv hgv⟩

theorem exists_scalar_of_conjAut_pow_three {F : Type} [Field F] [Finite F] {g : GL (Fin 3) F}
    {α : MulAut (projectiveSL 3 F)} (hg : conjAut 3 F g = α) (hα3 : α ^ 3 = 1) :
    ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c = g ^ 3 := by
  have hg3 : conjAut 3 F (g ^ 3) = 1 := by rw [map_pow, hg, hα3]
  have h := mk_eq_one_iff_mem_statedScalars.mp
    ((RonanK432.L3Outer.conjAut_eq_one_iff (g ^ 3)).mp hg3)
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp
    (show g ^ 3 ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F).range from h)
  exact ⟨c, hc⟩

theorem pow_three_matrix_eq_scalar {F : Type} [Field F] {g : GL (Fin 3) F} {c : Fˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c = g ^ 3) :
    (g : Matrix (Fin 3) (Fin 3) F) ^ 3 = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h := congrArg (fun y : GL (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at h
  rw [← h, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

theorem exists_scalar_diagUnits_eq {F : Type} [Field F] {ω : F} (hω0 : ω ≠ 0)
    (a : Fin 3 → ZMod 3) (h x : GL (Fin 3) F)
    (hd : ((h * x * h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun i => ω ^ (a i).val)) :
    ∃ (E s t : Fˣ), h * x * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) E * diagUnits 1 s t := by
  have hne : ω ^ (a 0).val ≠ 0 := pow_ne_zero _ hω0
  refine ⟨Units.mk0 (ω ^ (a 0).val) hne,
    Units.mk0 (ω ^ (a 1).val / ω ^ (a 0).val) (div_ne_zero (pow_ne_zero _ hω0) hne),
    Units.mk0 (ω ^ (a 2).val / ω ^ (a 0).val) (div_ne_zero (pow_ne_zero _ hω0) hne), ?_⟩
  apply Units.ext
  rw [hd, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, coe_diagUnits, Matrix.scalar_apply,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp [hne]
    field_simp
  · simp [hne]
    field_simp

theorem false_of_sl2_residual {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn1 : 1 ≤ n) (h4 : 4 ≤ Nat.card F)
    {A : Subgroup (MulAut (projectiveSL 3 F))} {α : MulAut (projectiveSL 3 F)}
    {K : Subgroup (projectiveSL 3 F)} (hc : CfgSEps (projectiveSL 3 F) A α K)
    (g : GL (Fin 3) F) (hgα : conjAut 3 F g = α)
    (K₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) [Group.IsPerfect ↥K₁]
    (h1 : K₁.map (LinearFlag.proj 3 F) = K) (h2 : K₁ ≤ C0 g)
    (ψR : ↥(inSubgroup perfectResidual
      (slPi true 3 (2 ^ n) F ⊓ Subgroup.centralizer ({g} : Set (GL (Fin 3) F)))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup (GL (Fin 3) F) :=
    slPi true 3 (2 ^ n) F ⊓ Subgroup.centralizer ({g} : Set (GL (Fin 3) F)) with hX
  set R : Subgroup (GL (Fin 3) F) := inSubgroup perfectResidual X with hR
  set R' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    R.comap Matrix.SpecialLinearGroup.toGL with hR'
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hXrange : X ≤ Matrix.SpecialLinearGroup.toGL.range := by
    rw [← slPi_true_eq_range F (2 ^ n)]
    exact inf_le_left
  have hR'comm : ∀ x ∈ R', Matrix.SpecialLinearGroup.toGL x * g =
      g * Matrix.SpecialLinearGroup.toGL x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hRX (Subgroup.mem_comap.mp hx))).2
  have hK₁R' : ∀ x ∈ K₁, x ∈ R' := by
    intro x hx
    have hP : Subgroup.map Matrix.SpecialLinearGroup.toGL K₁ ≤ R := by
      apply le_inSubgroup_perfectResidual (Group.IsPerfect.map Matrix.SpecialLinearGroup.toGL)
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (mem_slPi_true (2 ^ n) (A := Matrix.SpecialLinearGroup.toGL z)).mpr z.2
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mem_C0.mp (h2 hz))
    exact Subgroup.mem_comap.mpr (hP (Subgroup.mem_map_of_mem _ hx))
  have hRrange : ∀ r ∈ R, ∃ x : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL x = r := fun r hr =>
    MonoidHom.mem_range.mp (hXrange (hRX hr))
  let Ein : ↥R' →* ↥R := MonoidHom.codRestrict
    (Matrix.SpecialLinearGroup.toGL.comp R'.subtype) R (fun x => Subgroup.mem_comap.mp x.2)
  have hEin : Function.Bijective Ein := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.toGL_injective
      exact congrArg Subtype.val hxy
    · intro r
      obtain ⟨x, hx⟩ := hRrange r.1 r.2
      exact ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact r.2)⟩, Subtype.ext hx⟩
  have eR' : ↥R' ≃* ↥R := MulEquiv.ofBijective Ein hEin
  have e : ↥R' ≃* Matrix.SpecialLinearGroup (Fin 2) F := eR'.trans ψR
  have hZR' : Subgroup.center ↥R' = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv e Sec19.Item19Res2Proof.center_sl2_eq_bot
  set f : ↥R' →* LinearFlag.projectiveSL 3 F := (LinearFlag.proj 3 F).comp R'.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : LinearFlag.proj 3 F (x : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := hx
    have hxs : (x : Matrix.SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F :=
      LinearFlag.proj_eq_one_iff.mp hx'
    have hxc : x ∈ Subgroup.center ↥R' := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (scalars_le_center 3 F hxs) y.1
    rw [hZR', Subgroup.mem_bot] at hxc
    exact hxc
  set N : Subgroup (LinearFlag.projectiveSL 3 F) := f.range with hN
  have ιN : ↥N ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective hinj).symm.trans e
  have hZN : Subgroup.center ↥N = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv ιN Sec19.Item19Res2Proof.center_sl2_eq_bot
  have hNq : IsQuasisimple ↥N :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ιN.symm (RonanKChevTwo.SpFour.isQuasisimple_sl2 h4)
  have hKN : K ≤ N := by
    intro y hy
    rw [← h1] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact MonoidHom.mem_range.mpr ⟨⟨x, hK₁R' x hx⟩, rfl⟩
  have hNC : N ≤ autFix α := by
    intro y hy
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [mem_autFix, ← hgα]
    exact conjAut_proj_eq_self_of_comm g z.1 (hR'comm z.1 z.2)
  have hcube : IsTypeEpsCube ↥N := hc.isTypeEpsCube_of_le hKN hNC hNq hZN
  have hcard : Nat.card ↥N = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr ιN.toEquiv, card_SL_two F, hF]
  exact not_isTypeEpsCube_of_card_sl2_even hn1 hcard hcube

theorem false_of_linearCase {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn2 : 2 ≤ n)
    {A : Subgroup (MulAut (projectiveSL 3 F))} {α : MulAut (projectiveSL 3 F)}
    {K : Subgroup (projectiveSL 3 F)} (hc : CfgSEps (projectiveSL 3 F) A α K)
    (g : GL (Fin 3) F) (hg : conjAut 3 F g = α) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hc.isPerfect
  have hn1 : 1 ≤ n := by omega
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hfix : ∀ k ∈ K, conjAut 3 F g k = k := fun k hk => by
    rw [hg]
    exact mem_autFix.mp (hc.le_autFix hk)
  obtain ⟨c, hc3⟩ := exists_scalar_of_conjAut_pow_three hg hc.pow_three
  have hgM := pow_three_matrix_eq_scalar hc3
  by_cases hμ : ∃ μ : F, μ ^ 3 = (c : F)
  swap
  · exact not_odd_card_C0 g K _ (map_proj_commutator_comap K) (commutator_comap_le_C0 K hfix)
      (isTypeEpsCube_of_cfgSEps hc) (odd_card_C0_of_no_cube_root hgM hμ)
  obtain ⟨μ, hμc⟩ := hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply Units.ne_zero c
    rw [← hμc, h0]
    norm_num
  set u : Fˣ := Units.mk0 μ hμ0 with hu
  have hu3 : u ^ 3 = c := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hμc)
  have hscal : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ : GL (Fin 3) F) g :=
    (Subgroup.mem_center_iff.mp (scalar_mem_center (F := F) u⁻¹) g).symm
  set gp : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g with hgp
  have hg_eq : g = Matrix.GeneralLinearGroup.scalar (Fin 3) u * gp := by
    rw [hgp, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hgp3 : gp ^ 3 = 1 := by
    rw [hgp, Commute.mul_pow hscal, ← map_pow, ← hc3, ← map_mul, inv_pow, hu3, inv_mul_cancel,
      map_one]
  obtain ⟨ω, hω⟩ := exists_omega_of_card hF hn
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  obtain ⟨h, a, hdiag⟩ :=
    RonanK432.exists_conj_diagonal_of_pow_three hω (three_ne_zero_of_charTwo F) hgp3
  obtain ⟨E0, s1, t2, hD⟩ := exists_scalar_diagUnits_eq hω0 a h gp hdiag
  have hcen_u : h * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u * h :=
    Subgroup.mem_center_iff.mp (scalar_mem_center (F := F) u) h
  have hy : (h⁻¹)⁻¹ * g * h⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (u * E0) * diagUnits 1 s1 t2 := by
    rw [inv_inv, hg_eq]
    calc h * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * gp) * h⁻¹
        = (h * Matrix.GeneralLinearGroup.scalar (Fin 3) u) * gp * h⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (h * gp * h⁻¹) := by
          rw [hcen_u]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) E0 * diagUnits 1 s1 t2) := by rw [hD]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (u * E0) * diagUnits 1 s1 t2 := by
          rw [map_mul, mul_assoc]
  have hnc : ∃ M ∈ slPi true 3 (2 ^ n) F, M * g ≠ g * M := by
    by_contra hcon
    push Not at hcon
    apply hc.ne_one
    rw [← hg]
    apply MulEquiv.ext
    intro p
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective 3 F p
    exact conjAut_proj_eq_self_of_comm g x
      (hcon (Matrix.SpecialLinearGroup.toGL x) ((mem_slPi_true (2 ^ n)).mpr x.2))
  have hPi : PiField true 2 n F := ⟨Nat.prime_two, hn1, by rw [hF]; rfl⟩
  by_cases hodd : Odd (Nat.card ↥(slPi true 3 (2 ^ n) F ⊓
      Subgroup.centralizer ({g} : Set (GL (Fin 3) F))))
  · have hodd' : Odd (Nat.card ↥(C0 g)) := by
      rw [card_C0_eq g (2 ^ n)]
      exact hodd
    exact not_odd_card_C0 g K _ (map_proj_commutator_comap K) (commutator_comap_le_C0 K hfix)
      (isTypeEpsCube_of_cfgSEps hc) hodd'
  have hev : Even (Nat.card ↥(slPi true 3 (2 ^ n) F ⊓
      Subgroup.centralizer ({g} : Set (GL (Fin 3) F)))) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨ψR⟩ := Sec21.SL3Lines.perfectResidual_centralizer_of_conj (y := g) (g := h⁻¹) (l := u * E0)
    (s := s1) (t := t2) hPi h4 hy hnc hev
  haveI := isPerfect_commutator_comap K
  exact false_of_sl2_residual hF hn1 h4 hc g hg
    (⁅K.comap (LinearFlag.proj 3 F), K.comap (LinearFlag.proj 3 F)⁆) (map_proj_commutator_comap K)
    (commutator_comap_le_C0 K hfix) ψR

theorem noCfgSEps_projectiveSL_three_even {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn2 : 2 ≤ n) : NoCfgSEps (projectiveSL 3 F) := by
  intro A α K hc
  by_cases hD : α ∈ linearAutGroup 3 F
  · rw [linearAutGroup_eq_range] at hD
    obtain ⟨g, hg⟩ := hD
    exact false_of_linearCase hF hn hn2 hc g hg
  · exact false_of_fieldCase hF hn hn2 hc hD

theorem rowSEpsOf_seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSEpsOf (projSL 3 (GaloisField 2 n)) := by
  intro n hn S _ _ _ _ ⟨eS⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
  rcases Nat.even_or_odd n with he | ho
  · have hn2 : 2 ≤ n := by
      obtain ⟨k, rfl⟩ := he
      omega
    exact (noCfgSEps_projectiveSL_three_even hF he hn2).of_mulEquiv (eS.trans φ₀)
  · exact (noCfgSEps_of_autNoE27
      (autNoE27_projectiveSL_three_of_mod_two Nat.prime_two hn hF
        (two_pow_mod_three_of_odd ho))).of_mulEquiv (eS.trans φ₀)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
