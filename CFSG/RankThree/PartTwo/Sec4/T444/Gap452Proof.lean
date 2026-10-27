module

public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.OddKernel.EvenMinimalCover
public import CFSG.RankThree.OddKernel.FrattiniLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverMatrices
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Residual452

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.OddKernel Module
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev L34 : Type := LinearFlag.projectiveSL 3 (GaloisField 2 2)

theorem card_L34 : Nat.card L34 = 20160 :=
  KFacts.L34.card_projectiveSL KFacts.L34.card_galoisField_two_two

instance isSimpleGroup_L34 : IsSimpleGroup L34 := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 2) (n := 3)
    (by norm_num) (Or.inl le_rfl)).2.1
  exact (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 _)).isSimpleGroup

theorem center_L34 : Subgroup.center L34 = ⊥ :=
  LinearThreeFourOuter.center_projectiveSL_three_eq_bot KFacts.L34.card_galoisField_two_two

theorem exists_mul_ne_L34 : ∃ a b : L34, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have htop : Subgroup.center L34 = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => h y x
  have : Nontrivial L34 := IsSimpleGroup.toNontrivial
  rw [center_L34] at htop
  exact bot_ne_top htop

theorem layer_L34 : CFSG.layer L34 = ⊤ :=
  CFSG.LocalCores.layer_eq_top_of_mulEquiv_pi (ι := Unit) (S := fun _ => L34)
    (fun _ => exists_mul_ne_L34) (MulEquiv.funUnique Unit L34).symm

theorem exists_elementary_sixteen_L34 : ∃ E : Subgroup L34, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
    (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 :=
  ⟨FieldFourCover.projRad (GaloisField 2 2) 0,
    fun _ hx _ hy => FieldFourCover.commute_of_mem_projRad 0 hx hy,
    fun _ hx => FieldFourCover.sq_eq_one_of_mem_projRad KFacts.L34.card_galoisField_two_two 0 hx,
    by rw [FieldFourCover.card_projRad, KFacts.L34.card_galoisField_two_two]⟩

theorem exists_exponent_three_card_nine_L34 :
    ∃ E : Subgroup L34, Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  have hk := KFacts.L34.card_galoisField_two_two
  have := KFacts.L34.isElementaryAbelian_eZero hk
  exact ⟨KFacts.L34.eZero _, CFSG.IsElementaryAbelian.exponent_dvd_p 3 _,
    KFacts.L34.card_eZero hk⟩

theorem map_eq_one_of_commute {G M : Type*} [Group G] [Group.IsPerfect G] [Monoid M]
    (f : G →* M) (hf : ∀ a b, f a * f b = f b * f a) (g : G) : f g = 1 := by
  have hc : ∀ a b : G, f ⁅a, b⁆ = 1 := by
    intro a b
    have h1 : f a * f a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : f b * f b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [commutatorElement_def, map_mul, map_mul, map_mul, mul_assoc (f a), hf b a⁻¹,
      ← mul_assoc, h1, one_mul, h2]
  have hle : commutator G ≤ f.toHomUnits.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [MonoidHom.coe_toHomUnits, hc, Units.val_one])
  rw [Group.IsPerfect.commutator_eq_top] at hle
  have := congrArg Units.val (MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g)))
  rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this

theorem eq_one_of_isSolvable_range {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) (hs : Group.IsSolvable f.range) (g : G) : f g = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  rcases subsingleton_or_nontrivial f.range with h | h
  · exact congrArg Subtype.val (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)
  · exact absurd hs (Group.IsPerfect.not_isSolvable f.range)

structure IsL34Cover {G : Type*} [Group G] (π : G →* L34) : Prop where
  surjective : Function.Surjective π
  solvable : Group.IsSolvable π.ker

section Cover

variable {G : Type*} [Group G] [Group.IsPerfect G] {π : G →* L34}

theorem IsL34Cover.eq_one_or_ker_le (hπ : IsL34Cover π) {H : Type*} [Group H] (f : G →* H) :
    (∀ g, f g = 1) ∨ f.ker ≤ π.ker := by
  have : (f.ker.map π).Normal := (f.normal_ker).map π hπ.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map π) with h | h
  · right
    intro x hx
    have hx' : π x ∈ f.ker.map π := ⟨x, hx, rfl⟩
    rwa [h, Subgroup.mem_bot] at hx'
  · left
    have := hπ.solvable
    let ψ : π.ker →* f.range := (f.comp π.ker.subtype).codRestrict f.range fun k => ⟨k, rfl⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨_, g, rfl⟩
      have hg : π g ∈ f.ker.map π := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨⟨k⁻¹ * g, ?_⟩, Subtype.ext ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
      · change f (k⁻¹ * g) = f g
        rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    exact eq_one_of_isSolvable_range f (Group.isSolvable_of_surjective hψ)

theorem IsL34Cover.eq_one_or_ker_le' (hπ : IsL34Cover π) {M : Type*} [Monoid M] (f : G →* M) :
    (∀ g, f g = 1) ∨ ∀ g, f g = 1 → π g = 1 := by
  rcases hπ.eq_one_or_ker_le f.toHomUnits with h | h
  · exact Or.inl fun g => by simpa using congrArg Units.val (h g)
  · refine Or.inr fun g hg => h (MonoidHom.mem_ker.mpr (Units.ext ?_))
    rw [MonoidHom.coe_toHomUnits, hg, Units.val_one]

theorem IsL34Cover.eq_one_of_card_lt [Finite G] (hπ : IsL34Cover π) {H : Type*} [Group H]
    [Finite H] (f : G →* H) (hH : Nat.card H < 20160) (g : G) : f g = 1 := by
  rcases hπ.eq_one_or_ker_le f with h | h
  · exact h g
  · exfalso
    let π' : G ⧸ f.ker →* L34 := QuotientGroup.lift f.ker π h
    have hπ' : Function.Surjective π' := by
      intro y
      obtain ⟨x, rfl⟩ := hπ.surjective y
      exact ⟨x, rfl⟩
    have h1 : Nat.card L34 ≤ Nat.card (G ⧸ f.ker) := Nat.card_le_card_of_surjective _ hπ'
    have h2 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.range ≤ Nat.card H := Subgroup.card_le_card_group _
    rw [card_L34] at h1
    omega

theorem card_mulAut_le {H : Type*} [Group H] [Finite H] :
    Nat.card (MulAut H) ≤ (Nat.card H - 1).factorial := by
  classical
  let f : MulAut H → Equiv.Perm {x : H // x ≠ 1} := fun σ =>
    σ.toEquiv.subtypeEquiv fun x => (map_ne_one_iff σ σ.injective).symm
  have hf : Function.Injective f := by
    intro σ τ h
    ext x
    by_cases hx : x = 1
    · rw [hx, map_one, map_one]
    · exact congrArg (fun e : Equiv.Perm {x : H // x ≠ 1} => (e ⟨x, hx⟩ : H)) h
  calc Nat.card (MulAut H) ≤ Nat.card (Equiv.Perm {x : H // x ≠ 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = (Nat.card {x : H // x ≠ 1}).factorial := Nat.card_perm
    _ ≤ (Nat.card H - 1).factorial := by
        refine Nat.factorial_le ?_
        have := Finite.card_subtype_lt (p := fun x : H => x ≠ 1) (x := 1) (fun h => h rfl)
        omega

theorem IsL34Cover.le_center_of_card_le [Finite G] (hπ : IsL34Cover π) (R : Subgroup G)
    [R.Normal] (hR : Nat.card R ≤ 8) : R ≤ Subgroup.center G := by
  have hcard : Nat.card (MulAut R) < 20160 :=
    calc Nat.card (MulAut R) ≤ (Nat.card R - 1).factorial := card_mulAut_le
      _ ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
      _ < 20160 := by decide
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun σ : MulAut R => ((σ ⟨r, hr⟩ : R) : G))
    (hπ.eq_one_of_card_lt (MulAut.conjNormal (H := R)) hcard g)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc g * r = g * r * g⁻¹ * g := by group
    _ = r * g := by rw [h1]

theorem false_of_surjective_of_isCyclic_sylow {X Y : Type*} [Group X] [Finite X] [Group Y]
    [Finite Y] (F : X →* Y) (hF : Function.Surjective F) (hcyc : ∀ S : Sylow 3 X, IsCyclic S)
    {E : Subgroup Y} (hexp : Monoid.exponent E ∣ 3) (hcard : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := E.comap F with hW
  set ψ : W →* E := (F.comp W.subtype).codRestrict E (fun w => w.2) with hψ
  have hψs : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hF e
    exact ⟨⟨x, show F x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 W) := inferInstance
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have htop : ((T.mapSurjective hψs : Sylow 3 E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψs).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hT'p : IsPGroup 3 T' := T.isPGroup'.map _
  obtain ⟨S, hS⟩ := hT'p.exists_le_sylow
  have : IsCyclic S := hcyc S
  have hT'c : IsCyclic T' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom (MulEquiv.surjective _)
  have hTc : IsCyclic T :=
    isCyclic_of_surjective
      ((T : Subgroup W).equivMapOfInjective W.subtype W.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hEc : IsCyclic E := by
    refine isCyclic_of_surjective (ψ.comp (T : Subgroup W).subtype) ?_
    intro e
    have he : e ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top e
    obtain ⟨t, ht, rfl⟩ := he
    exact ⟨⟨t, ht⟩, rfl⟩
  have hexp' := IsCyclic.exponent_eq_card (α := E)
  rw [hcard] at hexp'
  rw [hexp'] at hexp
  norm_num at hexp

theorem commute_of_finrank_le_one {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (h : finrank K U ≤ 1) (a b : Module.End K U) : a * b = b * a := by
  classical
  let bs := Module.finBasis K U
  have hs : Subsingleton (Fin (finrank K U)) := ⟨fun i j => Fin.ext (by omega)⟩
  apply (LinearMap.toMatrix bs bs).injective
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_subsingleton _ i,
    Fintype.sum_subsingleton _ i, Subsingleton.elim j i, mul_comm]

theorem isCyclic_sylow_three_of_le_SL2 {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (S : Sylow 3 H) : IsCyclic S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S' := (S : Subgroup H).map H.subtype with hS'
  have hS'p : IsPGroup 3 S' := S.isPGroup'.map _
  obtain ⟨Q, hQ⟩ := hS'p.exists_le_sylow
  have : IsCyclic Q := Census.isCyclic_sylow_SL2 (by norm_num) (by omega) Q
  have hS'c : IsCyclic S' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom (MulEquiv.surjective _)
  exact isCyclic_of_surjective
    ((S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem IsL34Cover.rep_eq_one_of_finrank_le_two [Finite G]
    (hπ : IsL34Cover π) {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U] [FiniteDimensional (ZMod p) U] (hU : finrank (ZMod p) U ≤ 2)
    (ρ : G →* Module.End (ZMod p) U) (g : G) : ρ g = 1 := by
  classical
  rcases Nat.lt_or_ge (finrank (ZMod p) U) 2 with h1 | h2
  · exact map_eq_one_of_commute ρ (fun a b => commute_of_finrank_le_one (by omega) _ _) g
  have h2' : finrank (ZMod p) U = 2 := le_antisymm hU h2
  rcases hπ.eq_one_or_ker_le' ρ with h | hker
  · exact h g
  exfalso
  let bs := Module.finBasisOfFinrankEq (ZMod p) U h2'
  have hdet : ∀ x, LinearMap.det (ρ x) = 1 := fun x =>
    map_eq_one_of_commute ((LinearMap.det : Module.End (ZMod p) U →* ZMod p).comp ρ)
      (fun _ _ => mul_comm _ _) x
  let ψ : G →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    { toFun := fun x => ⟨LinearMap.toMatrix bs bs (ρ x), by rw [LinearMap.det_toMatrix, hdet]⟩
      map_one' := Subtype.ext (by
        change LinearMap.toMatrix bs bs (ρ 1) = 1
        rw [map_one, LinearMap.toMatrix_one])
      map_mul' := fun x y => Subtype.ext (by
        change LinearMap.toMatrix bs bs (ρ (x * y)) =
          LinearMap.toMatrix bs bs (ρ x) * LinearMap.toMatrix bs bs (ρ y)
        rw [map_mul, LinearMap.toMatrix_mul]) }
  have hψker : ψ.ker ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    apply hker
    have hx' : LinearMap.toMatrix bs bs (ρ x) = 1 := congrArg Subtype.val hx
    apply (LinearMap.toMatrix bs bs).injective
    rw [hx', LinearMap.toMatrix_one]
  let F : ψ.range →* L34 := (QuotientGroup.lift ψ.ker π hψker).comp
    (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hπ.surjective y
    refine ⟨⟨ψ x, x, rfl⟩, ?_⟩
    have : (QuotientGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩ = (x : G ⧸ ψ.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    change QuotientGroup.lift ψ.ker π hψker
      ((QuotientGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩) = π x
    rw [this, QuotientGroup.lift_mk]
  obtain ⟨E, hEexp, hEcard⟩ := exists_exponent_three_card_nine_L34
  exact false_of_surjective_of_isCyclic_sylow F hF (isCyclic_sylow_three_of_le_SL2 hp5 ψ.range)
    hEexp hEcard

@[expose] def restrictRep {K U H : Type*} [Field K] [AddCommGroup U] [Module K U] [Monoid H]
    (ρ : H →* Module.End K U) (S : Submodule K U) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    H →* Module.End K S where
  toFun g := (ρ g).restrict (hS g)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

theorem restrictRep_apply {K U H : Type*} [Field K] [AddCommGroup U] [Module K U] [Monoid H]
    (ρ : H →* Module.End K U) (S : Submodule K U) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : H)
    (v : S) : ((restrictRep ρ S hS g v : S) : U) = ρ g v :=
  rfl

theorem exists_cube_root_galoisField (p : ℕ) [hp : Fact p.Prime] (hp3 : p ≠ 3) :
    ∃ ω : GaloisField p 2, ω * ω + ω + 1 = 0 := by
  classical
  have hcard : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have : Fintype (GaloisField p 2) := Fintype.ofFinite _
  have h3 : 3 ∣ Nat.card (GaloisField p 2)ˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard]
    have hp3' : ¬ 3 ∣ p := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h).symm
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
    have hp2 : p ^ 2 % 3 = 1 := by rcases hmod with h | h <;> simp [Nat.pow_mod, h]
    have hpos : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField p 2)ˣ) 3 h3
  refine ⟨(u : GaloisField p 2), ?_⟩
  have hu3 : (u : GaloisField p 2) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : GaloisField p 2) ≠ 1 := by
    intro h
    have h' : u = 1 := Units.ext h
    rw [h', orderOf_one] at hu
    norm_num at hu
  have hmul : ((u : GaloisField p 2) - 1) * ((u : GaloisField p 2) * u + u + 1) = 0 := by
    linear_combination hu3
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd (sub_eq_zero.mp h) hu1
  · exact h

theorem three_dvd_finrank_of_central_fpf {p : ℕ} [hp : Fact p.Prime] (hp3 : p ≠ 3)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (ρ : G →* Module.End (ZMod p) U) (c : G) (hc : ∀ g, ρ c * ρ g = ρ g * ρ c)
    (hc3 : ρ c ^ 3 = 1) (hfix : fixSpace (ρ c) = ⊥) : 3 ∣ finrank (ZMod p) U := by
  classical
  set m := finrank (ZMod p) U with hm
  let bs := Module.finBasis (ZMod p) U
  let Φ : Module.End (ZMod p) U →+* Module.End (GaloisField p 2) (Fin m → GaloisField p 2) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) (GaloisField p 2) ≃ₐ[GaloisField p 2]
        Module.End (GaloisField p 2) (Fin m → GaloisField p 2)).toRingEquiv.toRingHom.comp
      ((RingHom.mapMatrix (algebraMap (ZMod p) (GaloisField p 2))).comp
        (LinearMap.toMatrixAlgEquiv bs).toRingEquiv.toRingHom)
  let L : G →* Module.End (GaloisField p 2) (Fin m → GaloisField p 2) := Φ.toMonoidHom.comp ρ
  have hLc : ∀ g, L c * L g = L g * L c := fun g => by
    change Φ (ρ c) * Φ (ρ g) = Φ (ρ g) * Φ (ρ c)
    rw [← map_mul Φ, ← map_mul Φ, hc]
  have hq : ρ c * ρ c + ρ c + 1 = 0 := by
    apply LinearMap.ext
    intro v
    have hrel : (ρ c - 1) * (ρ c * ρ c + ρ c + 1) = ρ c ^ 3 - 1 := by noncomm_ring
    have h0 : ((ρ c - 1) * (ρ c * ρ c + ρ c + 1)) v = 0 := by
      rw [hrel, hc3, sub_self, LinearMap.zero_apply]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0
    have hmem : (ρ c * ρ c + ρ c + 1) v ∈ fixSpace (ρ c) := mem_fixSpace.mpr h0
    rw [hfix, Submodule.mem_bot] at hmem
    rw [hmem, LinearMap.zero_apply]
  have hqL : L c * L c + L c + 1 = 0 := by
    change Φ (ρ c) * Φ (ρ c) + Φ (ρ c) + 1 = 0
    rw [← map_mul, ← map_add, ← map_one Φ, ← map_add, hq, map_zero]
  obtain ⟨ω, hω⟩ := exists_cube_root_galoisField p hp3
  set ω' : GaloisField p 2 := -1 - ω with hω'def
  have hω'q : ω' * ω' + ω' + 1 = 0 := by rw [hω'def]; linear_combination hω
  have h3F : (3 : GaloisField p 2) ≠ 0 := by
    intro h
    have h3 : ((3 : ℕ) : GaloisField p 2) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (GaloisField p 2) p] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h3)
  have hcube : ∀ μ : GaloisField p 2, μ * μ + μ + 1 = 0 → μ ^ 3 = 1 ∧ μ ≠ 1 := by
    intro μ hμ
    refine ⟨by linear_combination (μ - 1) * hμ, fun h1 => h3F ?_⟩
    rw [h1] at hμ
    linear_combination hμ
  have hne : ω - ω' ≠ 0 := by
    intro h
    apply h3F
    have : (ω - ω') * (ω - ω') = 0 := by rw [h, mul_zero]
    linear_combination (-1 : GaloisField p 2) * this + 4 * hω
  have hinv : ∀ (μ : GaloisField p 2) (g : G), ∀ v ∈ LinearMap.ker (L c - μ • 1),
      L g v ∈ LinearMap.ker (L c - μ • 1) := by
    intro μ g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [← Module.End.mul_apply, hLc g, Module.End.mul_apply, sub_eq_zero.mp hv, map_smul,
      sub_self]
  have hdvd : ∀ μ : GaloisField p 2, μ * μ + μ + 1 = 0 →
      3 ∣ finrank (GaloisField p 2) (LinearMap.ker (L c - μ • 1)) := by
    intro μ hμ
    obtain ⟨hμ3, hμ1⟩ := hcube μ hμ
    set S := LinearMap.ker (L c - μ • 1)
    let L1 := restrictRep L S (hinv μ)
    have hdet1 : LinearMap.det (L1 c) = 1 :=
      map_eq_one_of_commute
        ((LinearMap.det : Module.End (GaloisField p 2) S →* GaloisField p 2).comp L1)
        (fun _ _ => mul_comm _ _) c
    have hL1c : L1 c = μ • 1 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have hv := v.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at hv
      rw [restrictRep_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_smul, hv]
    rw [hL1c, LinearMap.det_smul, map_one, mul_one] at hdet1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf μ = 3 := orderOf_eq_prime hμ3 hμ1
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hdet1
  set E1 := LinearMap.ker (L c - ω • 1) with hE1
  set E2 := LinearMap.ker (L c - ω' • 1) with hE2
  have hinf : E1 ⊓ E2 = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero] at hv1 hv2
    rw [Submodule.mem_bot]
    have h0 : (ω - ω') • v = 0 := by rw [sub_smul, ← hv1, ← hv2, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left hne
  have hw : ∀ w, L c (L c w) + L c w + w = 0 := by
    intro w
    have := congrArg (fun f => f w) hqL
    simpa [Module.End.mul_apply] using this
  have hprod : ∀ μ ν : GaloisField p 2, μ + ν = -1 → μ * ν = 1 →
      ∀ w, (L c - μ • 1) ((L c - ν • 1) w) = 0 := by
    intro μ ν hs hp' w
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      map_smul]
    linear_combination (norm := module) hw w - hs • L c w + hp' • w
  have hs1 : ω + ω' = -1 := by rw [hω'def]; ring
  have hp1 : ω * ω' = 1 := by rw [hω'def]; linear_combination -hω
  have hsup : E1 ⊔ E2 = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv1 : (L c - ω' • 1) v ∈ E1 := LinearMap.mem_ker.mpr (hprod ω ω' hs1 hp1 v)
    have hv2 : (L c - ω • 1) v ∈ E2 :=
      LinearMap.mem_ker.mpr (hprod ω' ω (by rw [add_comm, hs1]) (by rw [mul_comm, hp1]) v)
    have hdec : v = (ω - ω')⁻¹ • ((L c - ω' • 1) v) - (ω - ω')⁻¹ • ((L c - ω • 1) v) := by
      rw [← smul_sub]
      have : (L c - ω' • 1) v - (L c - ω • 1) v = (ω - ω') • v := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
        abel
      rw [this, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hdec]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ hv1))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv2))
  have hsum : finrank (GaloisField p 2) E1 + finrank (GaloisField p 2) E2 = m := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq E1 E2
    rw [hsup, hinf, finrank_bot, add_zero, finrank_top, Module.finrank_fin_fun] at h
    exact h.symm
  have h1 : 3 ∣ finrank (GaloisField p 2) E1 := hdvd ω hω
  have h2 : 3 ∣ finrank (GaloisField p 2) E2 := hdvd ω' hω'q
  omega

section Nine

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

@[expose] def cubeSpace (σ : Module.End K U) : Submodule K U := LinearMap.ker (σ * σ + σ + 1)

theorem mem_cubeSpace {σ : Module.End K U} {v : U} : v ∈ cubeSpace σ ↔ σ (σ v) + σ v + v = 0 := by
  rw [cubeSpace, LinearMap.mem_ker]
  rfl

theorem apply_three_eq {σ : Module.End K U} (hσ : σ ^ 3 = 1) (v : U) : σ (σ (σ v)) = v := by
  have := LinearMap.congr_fun hσ v
  rwa [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.one_apply] at this

theorem injective_of_pow_three {σ : Module.End K U} (hσ : σ ^ 3 = 1) {v w : U}
    (h : σ v = σ w) : v = w := by
  rw [← apply_three_eq hσ v, ← apply_three_eq hσ w, h]

theorem finrank_eq_fix_add_cube [FiniteDimensional K U] (h3 : (3 : K) ≠ 0)
    (σ : Module.End K U) (hσ : σ ^ 3 = 1) (X : Submodule K U) (hX : ∀ x ∈ X, σ x ∈ X) :
    finrank K X = finrank K ↥(X ⊓ fixSpace σ) + finrank K ↥(X ⊓ cubeSpace σ) := by
  set A' := X ⊓ fixSpace σ with hA'
  set B' := X ⊓ cubeSpace σ with hB'
  have hAB : A' ⊓ B' = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, hv1⟩, ⟨-, hv2⟩⟩
    rw [SetLike.mem_coe, mem_fixSpace] at hv1
    rw [SetLike.mem_coe, mem_cubeSpace, hv1, hv1] at hv2
    rw [Submodule.mem_bot]
    have h3v : (3 : K) • v = 0 := by
      rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
      exact hv2
    exact (smul_eq_zero.1 h3v).resolve_left h3
  have hsup : A' ⊔ B' = X := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro x hx
    have hσx := hX x hx
    have hσσx := hX _ hσx
    set P := (3 : K)⁻¹ • (σ (σ x) + σ x + x) with hP
    have hPA : P ∈ A' := by
      refine ⟨X.smul_mem _ (X.add_mem (X.add_mem hσσx hσx) hx), ?_⟩
      rw [SetLike.mem_coe, mem_fixSpace, hP, map_smul, map_add, map_add, apply_three_eq hσ]
      congr 1
      abel
    have hPB : x - P ∈ B' := by
      refine ⟨X.sub_mem hx (X.smul_mem _ (X.add_mem (X.add_mem hσσx hσx) hx)), ?_⟩
      rw [SetLike.mem_coe, mem_cubeSpace]
      have hPfix : σ P = P := by
        rw [hP, map_smul, map_add, map_add, apply_three_eq hσ]
        congr 1
        abel
      have h3P : (3 : K) • P = σ (σ x) + σ x + x := by
        rw [hP, smul_smul, mul_inv_cancel₀ h3, one_smul]
      rw [map_sub, map_sub, hPfix, hPfix]
      linear_combination (norm := module) -h3P
    have hx' : x = P + (x - P) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hPA hPB
  have := Submodule.finrank_sup_add_finrank_inf_eq A' B'
  rw [hsup, hAB, finrank_bot, add_zero] at this
  exact this

theorem fixSpace_invariant {σ τ : Module.End K U} (h : ∀ v, σ (τ v) = τ (σ v)) :
    ∀ v ∈ fixSpace σ, τ v ∈ fixSpace σ := fun v hv => by
  rw [mem_fixSpace] at hv ⊢
  rw [h, hv]

theorem cubeSpace_invariant {σ τ : Module.End K U} (h : ∀ v, σ (τ v) = τ (σ v)) :
    ∀ v ∈ cubeSpace σ, τ v ∈ cubeSpace σ := fun v hv => by
  rw [mem_cubeSpace] at hv ⊢
  rw [h, h, ← map_add, ← map_add, hv, map_zero]

theorem eq_of_mem_cube_three {A B : Module.End K U} (h3 : (3 : K) ≠ 0) (hA : A ^ 3 = 1)
    (hc : ∀ v, A (B v) = B (A v)) (hB3 : ∀ v, B (B (B v)) = v) {v : U}
    (ha : A (A v) + A v + v = 0) (hb : B (B v) + B v + v = 0)
    (hab : A (B (A (B v))) + A (B v) + v = 0) : A v = B v := by
  have ha' : A (A v) = -A v - v := by linear_combination (norm := module) ha
  have hb' : B (B v) = -B v - v := by linear_combination (norm := module) hb
  have e2 : A (A (B v)) = -A (B v) - B v := by
    calc A (A (B v)) = B (A (A v)) := by rw [hc v, hc (A v)]
      _ = B (-A v - v) := by rw [ha']
      _ = -A (B v) - B v := by rw [map_sub, map_neg, hc v]
  have e3 : A (B (A (B v))) = A (B v) + B v + (A v + v) := by
    calc A (B (A (B v))) = A (A (B (B v))) := by rw [← hc (B v)]
      _ = A (A (-B v - v)) := by rw [hb']
      _ = -A (A (B v)) - A (A v) := by rw [map_sub, map_neg, map_sub, map_neg]
      _ = A (B v) + B v + (A v + v) := by rw [e2, ha']; abel
  have e4 : (2 : K) • A (B v) + A v + B v + (2 : K) • v = 0 := by
    linear_combination (norm := module) hab - e3
  set u := A v - B v with hu
  have hBv : B v = A v - u := by rw [hu]; abel
  have hBu : B u = A u := by
    rw [hu, map_sub, map_sub, ← hc v, ha', hb']
    linear_combination (norm := module) e4
  have s1 : B (B v) = A (A v) - (2 : K) • A u := by
    calc B (B v) = B (A v - u) := by rw [← hBv]
      _ = B (A v) - B u := map_sub _ _ _
      _ = A (B v) - A u := by rw [← hc v, hBu]
      _ = A (A v - u) - A u := by rw [← hBv]
      _ = A (A v) - (2 : K) • A u := by rw [map_sub]; module
  have s2 : B (B (B v)) = A (A (A v)) - (3 : K) • A (A u) := by
    calc B (B (B v)) = B (A (A v) - (2 : K) • A u) := by rw [s1]
      _ = B (A (A v)) - (2 : K) • B (A u) := by rw [map_sub, map_smul]
      _ = A (A (B v)) - (2 : K) • A (B u) := by rw [← hc (A v), ← hc v, ← hc u]
      _ = A (A (A v - u)) - (2 : K) • A (A u) := by rw [← hBv, hBu]
      _ = A (A (A v)) - (3 : K) • A (A u) := by rw [map_sub, map_sub]; module
  rw [hB3, apply_three_eq hA] at s2
  have h0 : (3 : K) • A (A u) = 0 := by linear_combination (norm := module) s2
  have hAAu : A (A u) = A (A 0) := by
    rw [map_zero, map_zero]
    exact (smul_eq_zero.mp h0).resolve_left h3
  have hu0 : u = 0 := injective_of_pow_three hA (injective_of_pow_three hA hAAu)
  rw [hu] at hu0
  exact sub_eq_zero.mp hu0

theorem sum_finrank_fixSpace_nine [FiniteDimensional K U] (h3 : (3 : K) ≠ 0)
    (A B : Module.End K U) (hAB : A * B = B * A) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) :
    finrank K (fixSpace A) + finrank K (fixSpace B) + finrank K (fixSpace (A * B)) +
      finrank K (fixSpace (A * B * B)) =
        finrank K U + 3 * finrank K ↥(fixSpace A ⊓ fixSpace B) := by
  have hc : ∀ v, A (B v) = B (A v) := fun v => by
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
  have hA3 := apply_three_eq hA
  have hB3 := apply_three_eq hB
  have hAB3 : (A * B) ^ 3 = 1 := by
    rw [(show Commute A B from hAB).mul_pow, hA, hB, one_mul]
  have cA1 : ∀ v, (A * B) (A v) = A ((A * B) v) := fun v => by
    simp only [Module.End.mul_apply, hc]
  have cB1 : ∀ v, (A * B) (B v) = B ((A * B) v) := fun v => by
    simp only [Module.End.mul_apply, hc]
  have cA2 : ∀ v, (A * B * B) (A v) = A ((A * B * B) v) := fun v => by
    simp only [Module.End.mul_apply, hc]
  have cB2 : ∀ v, (A * B * B) (B v) = B ((A * B * B) v) := fun v => by
    simp only [Module.End.mul_apply, hc]
  have cBA : ∀ v, B (A v) = A (B v) := fun v => (hc v).symm
  have cAAB : ∀ v, A ((A * B) v) = (A * B) (A v) := fun v => (cA1 v).symm
  have cBAB : ∀ v, B ((A * B) v) = (A * B) (B v) := fun v => (cB1 v).symm
  have inf_inv : ∀ {S T : Submodule K U} {τ : Module.End K U}, (∀ v ∈ S, τ v ∈ S) →
      (∀ v ∈ T, τ v ∈ T) → ∀ v ∈ S ⊓ T, τ v ∈ S ⊓ T :=
    fun hS hT v hv => ⟨hS v hv.1, hT v hv.2⟩
  have hfix3 : ∀ v, v ∈ fixSpace A → v ∈ cubeSpace A → v = 0 := by
    intro v hv1 hv2
    rw [mem_fixSpace] at hv1
    rw [mem_cubeSpace, hv1, hv1] at hv2
    have h3v : (3 : K) • v = 0 := by
      rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
      exact hv2
    exact (smul_eq_zero.1 h3v).resolve_left h3
  have e1 := finrank_eq_fix_add_cube h3 A hA ⊤ fun _ _ => Submodule.mem_top
  rw [top_inf_eq, top_inf_eq, finrank_top] at e1
  have e2 := finrank_eq_fix_add_cube h3 B hB (fixSpace A) (fixSpace_invariant hc)
  have e3 := finrank_eq_fix_add_cube h3 B hB (cubeSpace A) (cubeSpace_invariant hc)
  have e4 := finrank_eq_fix_add_cube h3 A hA (fixSpace B) (fixSpace_invariant cBA)
  rw [inf_comm (fixSpace B), inf_comm (fixSpace B)] at e4
  have e5 := finrank_eq_fix_add_cube h3 A hA (fixSpace (A * B)) (fixSpace_invariant cA1)
  have e5a : fixSpace (A * B) ⊓ fixSpace A = fixSpace A ⊓ fixSpace B := by
    ext v
    simp only [Submodule.mem_inf, mem_fixSpace, Module.End.mul_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, injective_of_pow_three hA (h1.trans h2.symm)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2, h1], h1⟩
  have e5b := finrank_eq_fix_add_cube h3 B hB (fixSpace (A * B) ⊓ cubeSpace A)
    (inf_inv (fixSpace_invariant cB1) (cubeSpace_invariant hc))
  have e5c : fixSpace (A * B) ⊓ cubeSpace A ⊓ fixSpace B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨h1, h2⟩, h3'⟩
    rw [SetLike.mem_coe, mem_fixSpace, Module.End.mul_apply] at h1
    rw [SetLike.mem_coe, mem_fixSpace] at h3'
    rw [h3'] at h1
    exact (Submodule.mem_bot K).mpr (hfix3 v (mem_fixSpace.mpr h1) h2)
  have e5d : fixSpace (A * B) ⊓ cubeSpace A ⊓ cubeSpace B =
      cubeSpace A ⊓ cubeSpace B ⊓ fixSpace (A * B) := by
    ext v
    simp only [Submodule.mem_inf]
    tauto
  rw [e5a] at e5
  rw [e5c, finrank_bot, zero_add, e5d] at e5b
  have e6 := finrank_eq_fix_add_cube h3 A hA (fixSpace (A * B * B))
    (fixSpace_invariant cA2)
  have e6a : fixSpace (A * B * B) ⊓ fixSpace A = fixSpace A ⊓ fixSpace B := by
    ext v
    simp only [Submodule.mem_inf, mem_fixSpace, Module.End.mul_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have hBB : B (B v) = v := injective_of_pow_three hA (h1.trans h2.symm)
      refine ⟨h2, ?_⟩
      calc B v = B (B (B v)) := by rw [hBB]
        _ = v := hB3 v
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2, h2, h1], h1⟩
  have e6b := finrank_eq_fix_add_cube h3 B hB (fixSpace (A * B * B) ⊓ cubeSpace A)
    (inf_inv (fixSpace_invariant cB2) (cubeSpace_invariant hc))
  have e6c : fixSpace (A * B * B) ⊓ cubeSpace A ⊓ fixSpace B = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨h1, h2⟩, h3'⟩
    rw [SetLike.mem_coe, mem_fixSpace, Module.End.mul_apply, Module.End.mul_apply] at h1
    rw [SetLike.mem_coe, mem_fixSpace] at h3'
    rw [h3', h3'] at h1
    exact (Submodule.mem_bot K).mpr (hfix3 v (mem_fixSpace.mpr h1) h2)
  have e6d : fixSpace (A * B * B) ⊓ cubeSpace A ⊓ cubeSpace B =
      cubeSpace A ⊓ cubeSpace B ⊓ fixSpace (A * B * B) := by
    ext v
    simp only [Submodule.mem_inf]
    tauto
  rw [e6a] at e6
  rw [e6c, finrank_bot, zero_add, e6d] at e6b
  have e7 := finrank_eq_fix_add_cube h3 (A * B) hAB3 (cubeSpace A ⊓ cubeSpace B)
    (inf_inv (cubeSpace_invariant cAAB) (cubeSpace_invariant cBAB))
  have e7a : cubeSpace A ⊓ cubeSpace B ⊓ cubeSpace (A * B) =
      cubeSpace A ⊓ cubeSpace B ⊓ fixSpace (A * B * B) := by
    ext v
    simp only [Submodule.mem_inf, mem_cubeSpace, mem_fixSpace, Module.End.mul_apply]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      have hAv := eq_of_mem_cube_three h3 hA hc hB3 ha hb hab
      refine ⟨⟨ha, hb⟩, ?_⟩
      rw [hc, hc, hAv]
      exact hB3 v
    · rintro ⟨⟨ha, hb⟩, habb⟩
      refine ⟨⟨ha, hb⟩, ?_⟩
      have hAv : A v = B v := by
        have := congrArg B habb
        rw [cBA, hB3] at this
        exact this
      rw [hc v, hAv, hB3, hAv]
      linear_combination (norm := module) hb
  rw [e7a] at e7
  omega

theorem false_of_nine_dim_four [FiniteDimensional K U] (h3 : (3 : K) ≠ 0)
    (hU : finrank K U = 4) (A B S Si : Module.End K U) (hAB : A * B = B * A) (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hSi : Si * S = 1) (hSA : S * A = A * A * S) (hSB : S * B = B * B * S)
    (hfB : finrank K (fixSpace B) = finrank K (fixSpace A))
    (hfAB : finrank K (fixSpace (A * B)) = finrank K (fixSpace A))
    (hfABB : finrank K (fixSpace (A * B * B)) = finrank K (fixSpace A))
    (hA1 : fixSpace A ≠ ⊤) : False := by
  have hid := sum_finrank_fixSpace_nine h3 A B hAB hA hB
  rw [hfB, hfAB, hfABB, hU] at hid
  have hle : finrank K ↥(fixSpace A ⊓ fixSpace B) ≤ finrank K (fixSpace A) :=
    Submodule.finrank_mono inf_le_left
  have hlt : finrank K (fixSpace A) < 4 := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hA1)
    rwa [finrank_top, hU] at this
  have hf1 : finrank K (fixSpace A) = 1 := by omega
  have hf0 : finrank K ↥(fixSpace A ⊓ fixSpace B) = 0 := by omega
  have hc : ∀ x, A (B x) = B (A x) := fun x => by
    rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
  obtain ⟨v, hvA, hv0⟩ : ∃ v ∈ fixSpace A, v ≠ 0 := by
    by_contra h
    push Not at h
    have hbot : fixSpace A = ⊥ := eq_bot_iff.mpr fun w hw => (Submodule.mem_bot K).mpr (h w hw)
    rw [hbot, finrank_bot] at hf1
    exact zero_ne_one hf1
  have hspan : ∀ w ∈ fixSpace A, ∃ c : K, c • v = w := by
    intro w hw
    obtain ⟨c, hcw⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hvA⟩ : fixSpace A)
      (fun h => hv0 (congrArg Subtype.val h))).mp hf1 ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hcw⟩
  have hBv : B v ∈ fixSpace A := fixSpace_invariant hc v hvA
  have hSv : S v ∈ fixSpace A := by
    have hvA' := mem_fixSpace.mp hvA
    have h1 : S v = A (A (S v)) := by
      have := LinearMap.congr_fun hSA v
      rwa [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hvA'] at this
    rw [mem_fixSpace]
    calc A (S v) = A (A (A (S v))) := by rw [← h1]
      _ = S v := apply_three_eq hA _
  obtain ⟨l, hl⟩ := hspan _ hBv
  obtain ⟨m, hm⟩ := hspan _ hSv
  have hBc : ∀ c : K, B (c • v) = (c * l) • v := fun c => by
    rw [map_smul, ← hl, smul_smul]
  have hB2 : B (B v) = (l * l) • v := by rw [← hl, hBc]
  have hB3' : B (B (B v)) = (l * l * l) • v := by rw [hB2, hBc]
  have hSB' := LinearMap.congr_fun hSB v
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, ← hl, map_smul, ← hm,
    smul_smul, hBc, hBc] at hSB'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hm
    apply hv0
    have := LinearMap.congr_fun hSi v
    rwa [Module.End.mul_apply, ← hm, map_zero, Module.End.one_apply, eq_comm] at this
  have hl3 : l * l * l = 1 := by
    have h1 := apply_three_eq hB v
    rw [hB3'] at h1
    have h2 : (l * l * l - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  have hlm : l * m = m * l * l := by
    have h2 : (l * m - m * l * l) • v = 0 := by rw [sub_smul, hSB', sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  have hl1 : l = 1 := by
    have hl0 : l ≠ 0 := by
      rintro rfl
      simp at hl3
    have : m * l * (l - 1) = 0 := by linear_combination -hlm
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hm0 hl0)
    · exact sub_eq_zero.mp h
  have hvB : v ∈ fixSpace B := by
    rw [mem_fixSpace, ← hl, hl1, one_smul]
  have hbot : fixSpace A ⊓ fixSpace B = ⊥ := Submodule.finrank_eq_zero.mp hf0
  have : v ∈ fixSpace A ⊓ fixSpace B := ⟨hvA, hvB⟩
  rw [hbot, Submodule.mem_bot] at this
  exact hv0 this

end Nine

theorem exists_mul_mem_normalizer {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (T : Sylow p H) {W : Subgroup H} (hTW : (T : Subgroup H) ≤ W) (h : H)
    (hh : ((h • T : Sylow p H) : Subgroup H) ≤ W) :
    ∃ w ∈ W, w * h ∈ Subgroup.normalizer ((T : Subgroup H) : Set H) := by
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W ((h • T).subtype hh) (T.subtype hTW)
  refine ⟨w, w.2, ?_⟩
  rw [Sylow.smul_subtype] at hw
  have h1 := Sylow.subtype_injective hw
  have h2 : ((w : H) * h) • T = T := by rw [mul_smul]; exact h1
  exact Sylow.smul_eq_iff_mem_normalizer.mp h2

theorem finrank_fixSpace_conj {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (A S Si : Module.End K U) (h1 : Si * S = 1) (h2 : S * Si = 1) :
    finrank K (fixSpace (S * A * Si)) = finrank K (fixSpace A) := by
  let e : U ≃ₗ[K] U := LinearEquiv.ofLinearMap S Si h2 h1
  have hmap : (fixSpace A).map (e : U →ₗ[K] U) = fixSpace (S * A * Si) := by
    ext v
    simp only [Submodule.mem_map, mem_fixSpace, Module.End.mul_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change S (A (Si (S x))) = S x
      rw [← Module.End.mul_apply Si S, h1, Module.End.one_apply, hx]
    · intro hv
      refine ⟨Si v, ?_, ?_⟩
      · have := congrArg Si hv
        rwa [← Module.End.mul_apply Si S, h1, Module.End.one_apply] at this
      · change S (Si v) = v
        rw [← Module.End.mul_apply, h2, Module.End.one_apply]
  rw [← hmap, LinearEquiv.finrank_map_eq]

theorem neg_one_ne_one_end {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (h2 : (2 : K) ≠ 0) (hU : 0 < finrank K U) :
    (-1 : Module.End K U) ≠ 1 := by
  intro h
  have : Nontrivial U := Module.finrank_pos_iff.mp hU
  obtain ⟨v, hv⟩ := exists_ne (0 : U)
  have h1 := LinearMap.congr_fun h v
  rw [LinearMap.neg_apply, Module.End.one_apply, neg_eq_iff_add_eq_zero, ← two_smul K] at h1
  exact hv ((smul_eq_zero.mp h1).resolve_left h2)

theorem det_eq_one_of_isPerfect {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (σ : G →* Module.End K V) (g : G) : LinearMap.det (σ g) = 1 :=
  map_eq_one_of_commute ((LinearMap.det : Module.End K V →* K).comp σ) (fun _ _ => mul_comm _ _) g

theorem even_finrank_of_eq_neg_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hm1 : (-1 : K) ≠ 1) (σ : G →* Module.End K V) {z : G}
    (hz : σ z = -1) : Even (finrank K V) := by
  have h := det_eq_one_of_isPerfect σ z
  rw [hz, show (-1 : Module.End K V) = (-1 : K) • 1 by rw [neg_one_smul], LinearMap.det_smul,
    map_one, mul_one] at h
  exact (neg_one_pow_eq_one_iff_even hm1).mp h

theorem factorization_card_L34_three : (Nat.card L34).factorization 3 = 2 := by
  rw [card_L34, show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem IsL34Cover.false_of_rep [Finite G] (hπ : IsL34Cover π)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (h3c : ∀ c : G, π c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → c ∈ Subgroup.center G)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U] [FiniteDimensional (ZMod p) U]
    (hU0 : 0 < finrank (ZMod p) U) (hU4 : finrank (ZMod p) U ≤ 4)
    (ρ : G →* Module.End (ZMod p) U) {z : G} (hz : ρ z = -1) : False := by
  classical
  have hcast : ∀ n : ℕ, n < p → 0 < n → ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n hn hn0 h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hn0 h) (by omega)
  have h2p : (2 : ZMod p) ≠ 0 := by exact_mod_cast hcast 2 (by omega) (by norm_num)
  have h3p : (3 : ZMod p) ≠ 0 := by exact_mod_cast hcast 3 (by omega) (by norm_num)
  have hm1 : (-1 : ZMod p) ≠ 1 := fun h => h2p (by linear_combination -h)
  have hz1 : ρ z ≠ 1 := hz ▸ neg_one_ne_one_end h2p hU0
  have hker : ∀ g, ρ g = 1 → π g = 1 :=
    (hπ.eq_one_or_ker_le' ρ).resolve_left fun h => hz1 (h z)
  have h4 : finrank (ZMod p) U = 4 := by
    obtain ⟨r, hr⟩ := even_finrank_of_eq_neg_one hm1 ρ hz
    by_contra h4
    exact hz1 (hπ.rep_eq_one_of_finrank_le_two hp5 (by omega) ρ z)
  have h3triv : ∀ c : G, π c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → ρ c = 1 := by
    rintro c hc ⟨k, hk⟩
    by_contra hne
    have hord : orderOf (ρ c) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero, orderOf_eq_one_iff] at hj
        exact absurd hj hne
      · exact h0
    set c' := c ^ 3 ^ (j - 1) with hc'
    have hc'3 : ρ c' ^ 3 = 1 := by
      rw [hc', map_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hj1, ← hj,
        pow_orderOf_eq_one]
    have hc'1 : ρ c' ≠ 1 := by
      intro h
      rw [hc', map_pow] at h
      have h' := orderOf_dvd_of_pow_eq_one h
      rw [hj] at h'
      have h1 := Nat.le_of_dvd (by positivity) h'
      have h2 : 3 ^ (j - 1) < 3 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hc'c : c' ∈ Subgroup.center G := h3c c' (by rw [hc', map_pow, hc, one_pow])
      ⟨k, by rw [hc', ← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
    have hcomm : ∀ g, ρ c' * ρ g = ρ g * ρ c' := fun g => by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc'c g)]
    have hinv1 : ∀ g, ∀ v ∈ fixSpace (ρ c'), ρ g v ∈ fixSpace (ρ c') := fun g =>
      fixSpace_invariant fun v => by rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
    let ρ1 := restrictRep ρ (fixSpace (ρ c')) hinv1
    have hz1' : ρ1 z = -1 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      rw [restrictRep_apply, hz]
      rfl
    have hlt1 : finrank (ZMod p) (fixSpace (ρ c')) < 4 := by
      have hne' : fixSpace (ρ c') ≠ ⊤ := by
        intro htop
        apply hc'1
        apply LinearMap.ext
        intro v
        have hv : v ∈ fixSpace (ρ c') := htop ▸ Submodule.mem_top
        rw [mem_fixSpace.mp hv, Module.End.one_apply]
      have := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne')
      rwa [finrank_top, h4] at this
    obtain ⟨r, hr⟩ := even_finrank_of_eq_neg_one hm1 ρ1 hz1'
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
    · have hbot : fixSpace (ρ c') = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
      have h3d := three_dvd_finrank_of_central_fpf (by omega) ρ c' hcomm hc'3 hbot
      rw [h4] at h3d
      norm_num at h3d
    · have h1 := hπ.rep_eq_one_of_finrank_le_two hp5 (by omega) ρ1 z
      rw [hz1'] at h1
      exact neg_one_ne_one_end h2p (by omega) h1
  have hk := KFacts.L34.card_galoisField_two_two
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 G) := inferInstance
  set E : Subgroup L34 := (T : Subgroup G).map π with hEdef
  have hE9 : Nat.card E = 9 := by
    have h := (T.mapSurjective hπ.surjective).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective, factorization_card_L34_three] at h
    rw [hEdef, h]
    norm_num
  have hEel := KFacts.L34.isElementaryAbelian_of_card_eq_nine hk hE9
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hρeq : ∀ x y : G, x * y⁻¹ ∈ (T : Subgroup G) → π x = π y → ρ x = ρ y := by
    intro x y hxy hxy'
    have h1 : ρ (x * y⁻¹) = 1 := by
      refine h3triv _ (by rw [map_mul, map_inv, hxy', mul_inv_cancel]) ?_
      obtain ⟨k, hk'⟩ := T.isPGroup' ⟨_, hxy⟩
      exact ⟨k, congrArg Subtype.val hk'⟩
    calc ρ x = ρ (x * y⁻¹ * y) := by rw [inv_mul_cancel_right]
      _ = ρ (x * y⁻¹) * ρ y := map_mul _ _ _
      _ = ρ y := by rw [h1, one_mul]
  obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [hbot, Subgroup.card_bot] at hE9
    norm_num at hE9
  have hza : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hE3 a haE) ha1
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers a := fun x hx => h x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hab1 : a * b ≠ 1 := fun h => hba (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
  have habb1 : a * b * b ≠ 1 := fun h => hba (by
    have hbb : b * b = a⁻¹ := by
      rw [mul_assoc] at h
      exact eq_inv_of_mul_eq_one_right h
    have : b = a⁻¹ * a⁻¹ := by
      calc b = b ^ 3 * b := by rw [hE3 b hbE, one_mul]
        _ = (b * b) * (b * b) := by rw [pow_succ, sq, mul_assoc (b * b) b b]
        _ = a⁻¹ * a⁻¹ := by rw [hbb]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
  obtain ⟨a', haT, rfl⟩ := haE
  obtain ⟨b', hbT, rfl⟩ := hbE
  set A := ρ a' with hA
  set B := ρ b' with hB
  have hAB : A * B = B * A := by
    rw [hA, hB, ← map_mul, ← map_mul]
    refine hρeq _ _ ?_ ?_
    · exact T.mul_mem (T.mul_mem haT hbT) (T.inv_mem (T.mul_mem hbT haT))
    · rw [map_mul, map_mul]
      exact hEc _ ⟨a', haT, rfl⟩ _ ⟨b', hbT, rfl⟩
  have hpow3 : ∀ x ∈ (T : Subgroup G), ρ x ^ 3 = 1 := by
    intro x hx
    rw [← map_pow, ← map_one ρ]
    refine hρeq _ _ (by rw [inv_one, mul_one]; exact T.pow_mem hx 3) ?_
    rw [map_pow, map_one]
    exact hE3 _ ⟨x, hx, rfl⟩
  have hA1 : fixSpace A ≠ ⊤ := by
    intro htop
    apply ha1
    apply hker
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixSpace A := htop ▸ Submodule.mem_top
    rw [mem_fixSpace.mp hv, Module.End.one_apply]
  have hTW : (T : Subgroup G) ≤ E.comap π := Subgroup.le_comap_map π _
  have hlift : ∀ n ∈ Subgroup.normalizer (E : Set L34), ∃ g : G,
      g ∈ Subgroup.normalizer ((T : Subgroup G) : Set G) ∧ ∃ e ∈ E, π g = e * n := by
    intro n hn
    obtain ⟨h, rfl⟩ := hπ.surjective n
    have hh : ((h • T : Sylow 3 G) : Subgroup G) ≤ E.comap π := by
      intro x hx
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨t, htT, rfl⟩ := hx
      rw [Subgroup.mem_comap, MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp ⟨t, htT, rfl⟩
    obtain ⟨w, hwW, hwN⟩ := exists_mul_mem_normalizer T hTW h hh
    exact ⟨w * h, hwN, π w, hwW, map_mul _ _ _⟩
  have hconjT : ∀ g ∈ Subgroup.normalizer ((T : Subgroup G) : Set G), ∀ x ∈ (T : Subgroup G),
      g * x * g⁻¹ ∈ (T : Subgroup G) := fun g hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hfix : ∀ y' ∈ (T : Subgroup G), π y' ≠ 1 →
      finrank (ZMod p) (fixSpace (ρ y')) = finrank (ZMod p) (fixSpace A) := by
    intro y' hyT hy1
    obtain ⟨n, hnN, hn⟩ := KFacts.L34.exists_mem_normalizer_conj_eq_of_card_eq_nine hk hE9
      ⟨a', haT, rfl⟩ ha1 ⟨y', hyT, rfl⟩ hy1
    obtain ⟨g, hgN, e, heE, hge⟩ := hlift n hnN
    have hρ : ρ (g * a' * g⁻¹) = ρ y' := by
      refine hρeq _ _ (T.mul_mem (hconjT g hgN a' haT) (T.inv_mem hyT)) ?_
      rw [map_mul, map_mul, map_inv, hge]
      calc e * n * π a' * (e * n)⁻¹ = e * (n * π a' * n⁻¹) * e⁻¹ := by group
        _ = e * π y' * e⁻¹ := by rw [hn]
        _ = π y' := by rw [hEc e heE _ ⟨y', hyT, rfl⟩, mul_inv_cancel_right]
    rw [← hρ, map_mul, map_mul]
    exact finrank_fixSpace_conj A (ρ g) (ρ g⁻¹) (by rw [← map_mul, inv_mul_cancel, map_one])
      (by rw [← map_mul, mul_inv_cancel, map_one])
  obtain ⟨s, hss, -, hsinv⟩ := KFacts.L34.exists_involution_inverting hk hE9
  have hsN : s ∈ Subgroup.normalizer (E : Set L34) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hsinv x hx]
      exact E.inv_mem hx
    · intro hx
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
      have hx' : x = s * (s * x * s⁻¹) * s⁻¹ := by
        rw [hsi]
        calc x = (s * s) * x * (s * s) := by rw [hss, one_mul, mul_one]
          _ = s * (s * x * s) * s := by group
      rw [hx', hsinv _ hx]
      exact E.inv_mem hx
  obtain ⟨gs, hgsN, es, hesE, hgs⟩ := hlift s hsN
  have hS : ∀ x ∈ (T : Subgroup G), ρ gs * ρ x = ρ x * ρ x * ρ gs := by
    intro x hx
    have hπx : π x ∈ E := ⟨x, hx, rfl⟩
    have hinvx : (π x)⁻¹ = π x * π x := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_two, ← pow_succ, hE3 _ hπx]
    have hconj' : ρ (gs * x * gs⁻¹) = ρ (x * x) := by
      refine hρeq _ _ (T.mul_mem (hconjT gs hgsN x hx) (T.inv_mem (T.mul_mem hx hx))) ?_
      rw [map_mul, map_mul, map_inv, hgs, map_mul, ← hinvx]
      calc es * s * π x * (es * s)⁻¹ = es * (s * π x * s⁻¹) * es⁻¹ := by group
        _ = es * (π x)⁻¹ * es⁻¹ := by rw [hsinv _ hπx]
        _ = (π x)⁻¹ := by
          rw [hEc es hesE _ (E.inv_mem hπx), mul_inv_cancel_right]
    calc ρ gs * ρ x = ρ (gs * x * gs⁻¹) * ρ gs := by
          rw [map_mul, map_mul, mul_assoc (ρ gs * ρ x), ← map_mul ρ gs⁻¹ gs, inv_mul_cancel,
            map_one, mul_one]
      _ = ρ (x * x) * ρ gs := by rw [hconj']
      _ = ρ x * ρ x * ρ gs := by rw [map_mul]
  exact false_of_nine_dim_four h3p h4 A B (ρ gs) (ρ gs⁻¹) hAB (hpow3 a' haT) (hpow3 b' hbT)
    (by rw [← map_mul, inv_mul_cancel, map_one]) (hS a' haT) (hS b' hbT) (hfix b' hbT hb1)
    (by rw [hA, hB, ← map_mul]; exact hfix _ (T.mul_mem haT hbT) (by rwa [map_mul]))
    (by
      rw [hA, hB, ← map_mul, ← map_mul]
      exact hfix _ (T.mul_mem (T.mul_mem haT hbT) hbT) (by rwa [map_mul, map_mul]))
    hA1

end Cover

theorem exists_isPGroup_map_eq {H K : Type*} [Group H] [Group K] [Finite H] {q : ℕ}
    [Fact q.Prime] {f : H →* K} (hf : Function.Surjective f) {E : Subgroup K}
    (hE : IsPGroup q E) : ∃ P : Subgroup H, IsPGroup q P ∧ P.map f = E := by
  set W := E.comap f with hW
  let ψ : W →* E := (f.comp W.subtype).codRestrict E fun w => w.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hf e
    exact ⟨⟨x, show f x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow q W) := inferInstance
  have htop : ((T.mapSurjective hψ : Sylow q E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hE.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro e he
    have : (⟨e, he⟩ : E) ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwe⟩ := this
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩

theorem frattiniAction_conjNormal_eq_one {X : Type*} [Group X] {R : Subgroup X} [R.Normal]
    {D : Subgroup R} [D.Characteristic] {a : X}
    (ha : ∀ d ∈ D, a * ((d : R) : X) * a⁻¹ = d) :
    (SectionRank.Ccomm.frattiniAction D).comp (MulAut.conjNormal (H := R)) a = 1 := by
  ext w
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective w
  rw [MulAut.one_apply, MonoidHom.comp_apply, SectionRank.Ccomm.frattiniAction_mk]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact ha d d.2

theorem card_le_four_of_quaternion {n : ℕ} (hn : 0 < n) {M : Type*} [Group M] [Finite M]
    (f : QuaternionGroup n →* M) (hf : Function.Surjective f) (h2 : ∀ x : M, x ^ 2 = 1) :
    Nat.card M ≤ 4 := by
  have : NeZero (2 * n) := ⟨by omega⟩
  have hβ : ∀ m : ℕ, f (QuaternionGroup.a 1) ^ m = 1 ∨
      f (QuaternionGroup.a 1) ^ m = f (QuaternionGroup.a 1) := by
    intro m
    induction m with
    | zero => exact Or.inl (pow_zero _)
    | succ k ih =>
      rcases ih with h | h
      · right
        rw [pow_succ, h, one_mul]
      · left
        rw [pow_succ, h, ← sq, h2]
  let g : Bool × Bool → M := fun ij =>
    (if ij.1 then f (QuaternionGroup.xa 0) else 1) * (if ij.2 then f (QuaternionGroup.a 1) else 1)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨q, rfl⟩ := hf y
    rcases q with i | i
    · have hai : f (QuaternionGroup.a i) = f (QuaternionGroup.a 1) ^ i.val := by
        rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rcases hβ i.val with h | h
      · exact ⟨(false, false), by rw [hai, h]; simp [g]⟩
      · exact ⟨(false, true), by rw [hai, h]; simp [g]⟩
    · have hxi : f (QuaternionGroup.xa i) =
          f (QuaternionGroup.xa 0) * f (QuaternionGroup.a 1) ^ i.val := by
        rw [← map_pow, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, ← map_mul,
          QuaternionGroup.xa_mul_a, zero_add]
      rcases hβ i.val with h | h
      · exact ⟨(true, false), by rw [hxi, h]; simp [g]⟩
      · exact ⟨(true, true), by rw [hxi, h]; simp [g]⟩
  calc Nat.card M ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_surjective g hg
    _ = 4 := by simp

theorem le_center_of_isPGroup {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] {π : X →* L34} (hπ : IsL34Cover π) (h9 : ¬ 9 ∣ Nat.card π.ker)
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p X ≤ 2)
    (R : Subgroup X) [R.Normal] (hR : IsPGroup p R) : R ≤ Subgroup.center X := by
  classical
  by_contra hRZ
  have hcomm : ⁅(⊤ : Subgroup X), R⁆ ≠ ⊥ := by
    intro h
    apply hRZ
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hx
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hR1 : R ≠ ⊥ := fun h => hRZ (h ▸ bot_le)
  obtain ⟨D, hDc, -, hDexp, -, -, hclass, hrange, -, hdet, hfixD⟩ :=
    odd_prime_kernel_critical_involution_fixed_spaces (by omega) R hR hR1 hcomm hloc
  set α := (SectionRank.Ccomm.frattiniAction D).comp (MulAut.conjNormal (H := R)) with hα
  have hDp : IsPGroup p D := hR.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hWp : IsPGroup p (D ⧸ frattini D) := fun x => ⟨1, by rw [pow_one, hWpow]⟩
  obtain ⟨n, hn⟩ := hWp.exists_card_eq
  obtain ⟨e⟩ := SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWcomm hWpow hn
  let φ : X →* Module.End (ZMod p) (Fin n → ZMod p) :=
    { toFun := fun x => coordLin e (α x)
      map_one' := by rw [map_one, coordLin_one]; rfl
      map_mul' := fun x y => by rw [map_mul, coordLin_mul]; rfl }
  have hφ : ∀ x, φ x = coordLin e (α x) := fun _ => rfl
  have hφα : ∀ x, φ x = 1 → α x = 1 := fun x h =>
    coordLin_injective e (by rw [← hφ, h, coordLin_one]; rfl)
  have hfixdim : ∀ t : X, orderOf t = 2 → finrank (ZMod p) (fixSpace (φ t)) ≤ 2 := by
    intro t ht
    have h := (hfixD t ht).2
    rw [card_fixed_eq_pow e] at h
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 h
  by_cases hcase : ∃ t : X, orderOf t = 2 ∧ α t = 1
  ·
    obtain ⟨t, ht, hαt⟩ := hcase
    have hn2 : n ≤ 2 := by
      have h := hfixdim t ht
      have htop : fixSpace (φ t) = ⊤ := by
        rw [eq_top_iff]
        intro v _
        rw [mem_fixSpace, hφ, hαt, coordLin_one, LinearMap.id_apply]
      rwa [htop, finrank_top, Module.finrank_fin_fun] at h
    apply hrange
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot]
    exact hφα x (hπ.rep_eq_one_of_finrank_le_two hp5 (by rwa [Module.finrank_fin_fun]) φ x)
  push Not at hcase
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
  obtain ⟨Y, -, hYmin⟩ := Finite.exists_le_minimal (p := fun Y : Subgroup X => Y.map π = ⊤)
    (show (⊤ : Subgroup X).map π = ⊤ from Subgroup.map_top_of_surjective π hπ.surjective)
  have hYS : Y.map π = ⊤ := hYmin.prop
  have hYmin' : ∀ U < Y, U.map π ≠ ⊤ := fun U hUY hU => hUY.not_ge (hYmin.2 hU hUY.le)
  obtain ⟨hYp, hCnil, hsyl⟩ := minimal_cover_facts layer_L34 π Y hYS hYmin'
  have := hYp
  set πY : Y →* L34 := π.comp Y.subtype with hπYdef
  set C : Subgroup Y := (Subgroup.center L34).comap πY with hCdef
  have hCmem : ∀ c : Y, c ∈ C ↔ πY c = 1 := fun c => by
    rw [hCdef, Subgroup.mem_comap, center_L34, Subgroup.mem_bot]
  have hπYs : Function.Surjective πY := by
    intro y
    have hy : y ∈ Y.map π := hYS ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hCker : C = πY.ker := by
    ext c
    rw [hCmem, MonoidHom.mem_ker]
  have hπY : IsL34Cover πY := ⟨hπYs, by rw [← hCker]; have := hCnil; infer_instance⟩
  have hCdvd : Nat.card C ∣ Nat.card π.ker := by
    have hle : C.map Y.subtype ≤ π.ker := by
      rintro _ ⟨c, hc, rfl⟩
      exact (hCmem c).mp hc
    rw [Nat.card_congr (C.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv]
    exact Subgroup.card_dvd_of_le hle
  have hfaith : ∀ a : X, a ^ 2 = 1 → (∀ d ∈ D, a * ((d : R) : X) * a⁻¹ = d) → a = 1 := by
    intro a ha2 hcent
    by_contra ha1
    exact hcase a (orderOf_eq_prime ha2 ha1) (frattiniAction_conjNormal_eq_one hcent)
  have hE16 : ∀ A : Subgroup X, (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 2 = 1) →
      Nat.card A = 16 → False := fun A hAc hA2 hA16 =>
    false_of_elementary_sixteen (by omega) hR hDexp hclass (fun t ht => (hfixD t ht).1) A hAc
      hA2 hA16 fun a ha hcent => hfaith a (hA2 a ha) hcent
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E16, hE16c, hE16sq, hE16card⟩ := exists_elementary_sixteen_L34
  have hE16p : IsPGroup 2 E16 := IsPGroup.of_card (n := 4) (by rw [hE16card]; norm_num)
  obtain ⟨P, hP2, hPE⟩ := exists_isPGroup_map_eq hπYs hE16p
  by_cases hCodd : Odd (Nat.card C)
  ·
    have hPC : ∀ x ∈ P, πY x = 1 → x = 1 := by
      intro x hx hx1
      have hxC : x ∈ C := (hCmem x).mpr hx1
      obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
      have h1 : orderOf x ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have h2 : orderOf x ∣ Nat.card C := by
        rw [← Subgroup.orderOf_mk x hxC]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime (2 ^ k) (Nat.card C) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hCodd)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    have hinj : Function.Injective (πY.comp P.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact Subtype.ext (hPC x x.2 hx)
    obtain ⟨hPc, hPsq, hPcard⟩ := props_of_injective_map πY hinj hPE hE16c hE16sq
    refine hE16 (P.map Y.subtype) ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hPc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hPsq x hx)
    · rw [← hE16card, ← hPcard]
      exact Nat.card_congr (P.equivMapOfInjective Y.subtype Y.subtype_injective).toEquiv.symm
  have hCeven : 2 ∣ Nat.card C := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hCodd)
  obtain ⟨S2⟩ : Nonempty (Sylow 2 C) := inferInstance
  set S : Subgroup Y := (S2 : Subgroup C).map C.subtype with hSdef
  have hSn : S.Normal := hsyl 2 S2
  have hS2 : IsPGroup 2 S := S2.isPGroup'.map _
  have hS1 : S ≠ ⊥ := by
    rw [hSdef, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact S2.ne_bot_of_dvd_card hCeven
  set Z : Subgroup Y := S ⊓ Subgroup.centralizer (S : Set Y) with hZdef
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  let Ω : Subgroup Y :=
    { carrier := {x | x ∈ Z ∧ x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => ⟨Z.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hZc x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨Z.one_mem, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨Z.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hΩmem : ∀ x, x ∈ Ω ↔ x ∈ Z ∧ x ^ 2 = 1 := fun x => Iff.rfl
  have hZn : Z.Normal := inferInstance
  have hΩn : Ω.Normal := ⟨fun x hx g => (hΩmem _).mpr ⟨hZn.conj_mem x ((hΩmem x).mp hx).1 g, by
    rw [conj_pow, ((hΩmem x).mp hx).2, mul_one, mul_inv_cancel]⟩⟩
  have hΩ8 : Nat.card Ω ≤ 8 := by
    have hΩ2 : IsPGroup 2 Ω := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow]
      exact ((hΩmem _).mp x.2).2)⟩
    obtain ⟨m, hm⟩ := hΩ2.exists_card_eq
    by_contra h8
    have hm4 : 4 ≤ m := by
      by_contra h
      have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := Ω) 2 (n := 4)
      (by rw [hm]; exact pow_dvd_pow 2 hm4)
    refine hE16 ((Q.map Ω.subtype).map Y.subtype) ?_ ?_ ?_
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩ _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
      exact congrArg Subtype.val (hZc _ ((hΩmem _).mp x.2).1 _ ((hΩmem _).mp y.2).1)
    · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
      exact congrArg Subtype.val ((hΩmem _).mp x.2).2
    · rw [← Nat.card_congr ((Q.map Ω.subtype).equivMapOfInjective Y.subtype
        Y.subtype_injective).toEquiv, ← Nat.card_congr (Q.equivMapOfInjective Ω.subtype
        Ω.subtype_injective).toEquiv, hQ]
      norm_num
  have hΩZ := hπY.le_center_of_card_le Ω hΩ8
  obtain ⟨z, hzΩ, hz2⟩ : ∃ z ∈ Ω, orderOf z = 2 := by
    have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hS1
    have hZS : Nontrivial (Subgroup.center S) := hS2.center_nontrivial
    have h2c : 2 ∣ Nat.card (Subgroup.center S) := by
      rcases (hS2.to_subgroup (Subgroup.center S)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hZS).ne'
      · exact h
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center S) 2 h2c
    have hz0' : orderOf ((z0 : S) : Y) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz0]
    refine ⟨((z0 : S) : Y), (hΩmem _).mpr ⟨Subgroup.mem_inf.mpr ⟨(z0 : S).2, ?_⟩, ?_⟩, hz0'⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z0.2 ⟨s, hs⟩)
    · rw [← hz0', pow_orderOf_eq_one]
  have hzc : z ∈ Subgroup.center Y := hΩZ hzΩ
  obtain ⟨t, ht2, htz⟩ : ∃ t : Y, orderOf t = 2 ∧ t ≠ z := by
    by_contra hnone
    push Not at hnone
    have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions P := by
      intro t1 t2 _
      apply Subtype.ext
      apply Subtype.ext
      rw [hnone ((t1 : P) : Y) (by rw [Subgroup.orderOf_coe]; exact t1.2),
        hnone ((t2 : P) : Y) (by rw [Subgroup.orderOf_coe]; exact t2.2)]
    let f : P →* E16 := (πY.comp P.subtype).codRestrict E16
      (fun x => hPE ▸ Subgroup.mem_map_of_mem πY x.2)
    have hf : Function.Surjective f := by
      intro e
      have he : (e : L34) ∈ P.map πY := hPE.symm ▸ e.2
      obtain ⟨x, hx, hxe⟩ := he
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have hE2 : ∀ x : E16, x ^ 2 = 1 := fun x => Subtype.ext (hE16sq x x.2)
    rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hP2 hrank with
      hcyc | ⟨k, -, ⟨eQ⟩⟩
    · have : IsCyclic E16 := isCyclic_of_surjective f hf
      have hexp := IsCyclic.exponent_eq_card (α := E16)
      have hdvd : Monoid.exponent E16 ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hE2
      rw [hexp, hE16card] at hdvd
      norm_num at hdvd
    · have h4 := card_le_four_of_quaternion (by positivity) (f.comp eQ.toMonoidHom)
        (hf.comp eQ.surjective) hE2
      rw [hE16card] at h4
      norm_num at h4
  set zX : X := (z : X) with hzX
  set tX : X := (t : X) with htX
  have hzX2 : orderOf zX = 2 := by rw [hzX, Subgroup.orderOf_coe, hz2]
  have htX2 : orderOf tX = 2 := by rw [htX, Subgroup.orderOf_coe, ht2]
  have hcz : ∀ y : Y, (y : X) * zX = zX * (y : X) := fun y =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzc) y)
  have hzX1 : zX ^ 2 = 1 := by rw [← hzX2]; exact pow_orderOf_eq_one zX
  have htX1 : tX ^ 2 = 1 := by rw [← htX2]; exact pow_orderOf_eq_one tX
  have htzX : tX * zX ≠ 1 := by
    intro h
    apply htz
    apply Subtype.ext
    have hzinv : zX⁻¹ = zX := inv_eq_of_mul_eq_one_right (by rw [← sq, hzX1])
    change tX = zX
    rw [← hzinv]
    exact eq_inv_of_mul_eq_one_left h
  have htzX2 : orderOf (tX * zX) = 2 := by
    refine orderOf_eq_prime ?_ htzX
    rw [(show Commute tX zX from hcz t).mul_pow, htX1, hzX1, one_mul]
  have hinvol : ∀ x : X, orderOf x = 2 → ∀ w, φ x (φ x w) = w := by
    intro x hx w
    rw [← Module.End.mul_apply, ← map_mul, ← sq, ← hx, pow_orderOf_eq_one, map_one,
      Module.End.one_apply]
  have hcommφ : ∀ w, φ tX (φ zX w) = φ zX (φ tX w) := by
    intro w
    rw [← Module.End.mul_apply, ← map_mul, hcz t, map_mul, Module.End.mul_apply]
  have h4 := finrank_four_group h2p (φ tX) (φ zX) (hinvol tX htX2) (hinvol zX hzX2) hcommφ ⊤
    (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
  have hdec := finrank_eq_fix_add_neg h2p (φ zX) (hinvol zX hzX2) ⊤
    (fun _ _ => Submodule.mem_top)
  repeat rw [top_inf_eq] at h4
  repeat rw [top_inf_eq] at hdec
  rw [finrank_top] at hdec h4
  have hft := hfixdim tX htX2
  have hftz := hfixdim (tX * zX) htzX2
  rw [map_mul, Module.End.mul_eq_comp] at hftz
  obtain ⟨h4a, h4b, h4c, h4d⟩ := h4
  have hU4 : finrank (ZMod p) (negSpace (φ zX)) ≤ 4 := by omega
  have hU0 : 0 < finrank (ZMod p) (negSpace (φ zX)) := by
    by_contra h0
    have hfix : fixSpace (φ zX) = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    apply hcase zX hzX2
    apply hφα
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    exact mem_fixSpace.mp (hfix ▸ Submodule.mem_top)
  have hinvU : ∀ y : Y, ∀ v ∈ negSpace (φ zX), (φ.comp Y.subtype) y v ∈ negSpace (φ zX) := by
    intro y v hv
    rw [mem_negSpace] at hv ⊢
    change φ zX (φ (y : X) v) = -φ (y : X) v
    rw [← Module.End.mul_apply, ← map_mul, ← hcz y, map_mul, Module.End.mul_apply, hv, map_neg]
  let ρ := restrictRep (φ.comp Y.subtype) (negSpace (φ zX)) hinvU
  have hρz : ρ z = -1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [restrictRep_apply, LinearMap.neg_apply, Module.End.one_apply, Submodule.coe_neg]
    exact mem_negSpace.mp v.2
  have h3c : ∀ c : Y, πY c = 1 → (∃ k : ℕ, c ^ 3 ^ k = 1) → c ∈ Subgroup.center Y := by
    rintro c hc ⟨k, hk⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q3⟩ : Nonempty (Sylow 3 C) := inferInstance
    set T3 : Subgroup Y := (Q3 : Subgroup C).map C.subtype with hT3
    have hT3n : T3.Normal := hsyl 3 Q3
    have hcC : c ∈ C := (hCmem c).mpr hc
    have hQ3n : (Q3 : Subgroup C).Normal := by
      have h := hT3n.subgroupOf C
      have heq : T3.subgroupOf C = (Q3 : Subgroup C) := by
        rw [hT3, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      rwa [heq] at h
    have hcT : c ∈ T3 := by
      have hord : orderOf (⟨c, hcC⟩ : C) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow]; exact hk))
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
      have hzp : IsPGroup 3 (Subgroup.zpowers (⟨c, hcC⟩ : C)) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
      obtain ⟨S3, hS3⟩ := hzp.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q3 S3
      have hQS : S3 = Q3 := by rw [← hg]; exact Sylow.smul_eq_of_normal
      have hmem : (⟨c, hcC⟩ : C) ∈ (Q3 : Subgroup C) := hQS ▸ hS3 (Subgroup.mem_zpowers _)
      exact ⟨⟨c, hcC⟩, hmem, rfl⟩
    have hT3card : Nat.card T3 ≤ 3 := by
      have hdvd : Nat.card T3 ∣ Nat.card π.ker := by
        rw [hT3, Subgroup.card_map_of_injective C.subtype_injective]
        exact (Subgroup.card_subgroup_dvd_card _).trans hCdvd
      obtain ⟨m, hm⟩ := (Q3.isPGroup'.map C.subtype : IsPGroup 3 T3).exists_card_eq
      rw [hm] at hdvd ⊢
      by_contra h3
      have hm2 : 2 ≤ m := by
        by_contra h
        have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact h9 ((pow_dvd_pow 3 hm2).trans hdvd)
    exact hπY.le_center_of_card_le T3 (by omega) hcT
  exact hπY.false_of_rep hp5 h3c hU0 hU4 ρ hρz

end CFSG.RankThree.PartTwo.Sec4.Residual452

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG Residual452

theorem rank3II_4_52_residual : Item4_52Residual := by
  intro X _ _ hX hXp hO2 K _ hK h9 hψ
  obtain ⟨ψ⟩ := hψ
  classical
  let π : X →* L34 := (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).toMonoidHom.comp
    (ψ.toMonoidHom.comp (QuotientGroup.mk' K))
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := ψ.surjective ((KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨x, ?_⟩
    change (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) (ψ (x : X ⧸ K)) = y
    rw [show ((x : X ⧸ K)) = QuotientGroup.mk' K x from rfl, hq, MulEquiv.apply_symm_apply]
  have hπker : π.ker = K := by
    ext x
    rw [MonoidHom.mem_ker]
    change (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) (ψ (x : X ⧸ K)) = 1 ↔ x ∈ K
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hπ : IsL34Cover π := ⟨hπs, by rw [hπker]; exact hK⟩
  have h9' : ¬ 9 ∣ Nat.card π.ker := by rw [hπker]; exact h9
  have hcore : ∀ (q : ℕ) [Fact q.Prime] (N : Subgroup X) [N.Normal], IsPGroup q N → N ≤ K →
      N ≤ Subgroup.center X := by
    intro q hq N _ hN hNK
    by_cases hq2 : q = 2
    · subst hq2
      have hle : N ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, hN⟩
      rw [hO2, le_bot_iff] at hle
      rw [hle]
      exact bot_le
    by_cases hq3 : q = 3
    · subst hq3
      refine hπ.le_center_of_card_le N ?_
      obtain ⟨m, hm⟩ := hN.exists_card_eq
      have hdvd : Nat.card N ∣ Nat.card K := Subgroup.card_dvd_of_le hNK
      rw [hm] at hdvd ⊢
      by_contra h8
      have hm2 : 2 ≤ m := by
        by_contra h
        have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact h9 ((pow_dvd_pow 3 hm2).trans hdvd)
    have hq5 : 5 ≤ q := by
      have h2 := hq.out.two_le
      have h4 : q ≠ 4 := by
        rintro rfl
        exact absurd hq.out (by norm_num)
      omega
    exact le_center_of_isPGroup hπ h9' hq5
      (Nat.lt_succ_iff.mp (hX.localRank_lt q hq.out (by omega))) N hN
  have hpc : ∀ q : (Nat.card K).primeFactors.attach,
      (CFSG.pCore q.1.1 K).map K.subtype ≤ Subgroup.center X := fun q =>
    hcore q.1.1 _ (CFSG.pCore_isPGroup.map _) (Subgroup.map_subtype_le _)
  have hFX : (CFSG.fittingSubgroup K).map K.subtype ≤ Subgroup.center X := by
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact iSup_le hpc
  have hFc : CFSG.fittingSubgroup K ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hFX ⟨x, hx, rfl⟩)) y)
  have htop : CFSG.fittingSubgroup K = ⊤ := by
    have hc : Subgroup.centralizer (CFSG.fittingSubgroup K : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_center_iff.mp (hFc hx) y).symm
    have h := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hK
    rw [hc] at h
    exact top_le_iff.mp h
  have hKZ : K ≤ Subgroup.center X := by
    intro x hx
    exact hFX ⟨⟨x, hx⟩, htop ▸ Subgroup.mem_top _, rfl⟩
  have hZK : Subgroup.center X = π.ker := by
    rw [hπker]
    refine le_antisymm ?_ hKZ
    intro x hx
    rw [← hπker, MonoidHom.mem_ker]
    have hxc : π x ∈ Subgroup.center L34 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := hπs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx g]
    rwa [center_L34, Subgroup.mem_bot] at hxc
  let e : X ⧸ Subgroup.center X ≃* L34 := (QuotientGroup.quotientMulEquivOfEq hZK).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  refine ⟨hXp, e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_L34
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

end CFSG.RankThree.PartTwo.Sec4
