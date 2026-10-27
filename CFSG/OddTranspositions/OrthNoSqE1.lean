module

public import CFSG.OddTranspositions.SymNoSqE1
public import CFSG.Fischer.Classification.Recognition.SymOOrth
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.OddTranspositions

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open QuadraticMap

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem bilinIsometryGroup_map_generalLinearEquiv {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] (B : LinearMap.BilinForm (ZMod 2) M) :
    (bilinIsometryGroup B).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).toMonoidHom =
      TauCeti.BilinForm.isometryGroup B := by
  ext e
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [TauCeti.BilinForm.mem_isometryGroup_iff]
    exact (mem_bilinIsometryGroup.mp hg)
  · intro he
    refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).symm e, ?_, ?_⟩
    · refine mem_bilinIsometryGroup.mpr ?_
      rw [TauCeti.BilinForm.mem_isometryGroup_iff] at he
      change ∀ x y, B (e x) (e y) = B x y
      exact he
    · exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).apply_symm_apply e


noncomputable def bilinIsometryGroupEquivIsometryGroup {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] (B : LinearMap.BilinForm (ZMod 2) M) :
    bilinIsometryGroup B ≃* TauCeti.BilinForm.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).subgroupMap
      (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (bilinIsometryGroup_map_generalLinearEquiv B))

@[simp]
theorem bilinIsometryGroupEquivIsometryGroup_symm_apply {M : Type*} [AddCommGroup M]
    [Module (ZMod 2) M] (B : LinearMap.BilinForm (ZMod 2) M)
    (x : TauCeti.BilinForm.isometryGroup B) (w : M) :
    (((bilinIsometryGroupEquivIsometryGroup B).symm x :
        LinearMap.GeneralLinearGroup (ZMod 2) M) : M → M) w =
      (x : M ≃ₗ[ZMod 2] M) w := by
  rfl

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Alternating

theorem pCore_two_eq_bot_of_faithful_pretransitive_odd {G X : Type*} [Group G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hX : ¬ 2 ∣ Nat.card X) : CFSG.pCore 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀⟩ :=
    (CFSG.pCore_isPGroup (p := 2) (G := G)).nonempty_fixed_point_of_prime_not_dvd_card X hX
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ x
  rw [one_smul]
  have hm : g⁻¹ * n * g ∈ CFSG.pCore 2 G := by
    have := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem n hn g⁻¹
    rwa [inv_inv] at this
  have h1 : (g⁻¹ * n * g) • x₀ = x₀ := hx₀ ⟨_, hm⟩
  have e : n * g = g * (g⁻¹ * n * g) := by group
  calc n • g • x₀ = (n * g) • x₀ := (mul_smul n g x₀).symm
    _ = (g * (g⁻¹ * n * g)) • x₀ := by rw [e]
    _ = g • (g⁻¹ * n * g) • x₀ := mul_smul _ _ _
    _ = g • x₀ := by rw [h1]

theorem odd_card_ne_zero_vectors {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Finite W] (hW : 1 ≤ Module.finrank (ZMod 2) W) :
    ¬ 2 ∣ Nat.card {w : W // w ≠ 0} := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]
  have hcardX : Nat.card {w : W // w ≠ 0} = Nat.card W - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have h := Fintype.card_subtype_compl (fun w : W => w = 0)
    simpa using h
  rw [hcardX, hcardW]
  intro hdvd
  have h2n : 2 ∣ 2 ^ Module.finrank (ZMod 2) W :=
    dvd_pow_self 2 (by omega)
  have h1 : 2 ∣ 2 ^ Module.finrank (ZMod 2) W - (2 ^ Module.finrank (ZMod 2) W - 1) :=
    Nat.dvd_sub h2n hdvd
  have hpos : 1 ≤ 2 ^ Module.finrank (ZMod 2) W := Nat.one_le_two_pow
  rw [Nat.sub_sub_self hpos] at h1
  omega

theorem pCore_bilinIsometryGroup_eq_bot {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Finite W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 2) W) :
    CFSG.pCore 2 (bilinIsometryGroup B) = ⊥ := by
  classical
  let G := bilinIsometryGroup B
  let X := {w : W // w ≠ 0}
  have hgen : bilinIsometryGroup B = Subgroup.closure
      {g : LinearMap.GeneralLinearGroup (ZMod 2) W |
        ∃ a c, g = symplecticTransvection B hB a c} :=
    alternating_transvection_generation hB hnd
  have htr : ∀ u v : W, u ≠ 0 → v ≠ 0 →
      ∃ g : G, ((g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) u = v := by
    intro u v hu hv
    obtain ⟨g, hg, hgu⟩ := (alternating_transvection_vector_transitivity hB hnd).2 u v hu hv
    refine ⟨⟨g, ?_⟩, hgu⟩
    show g ∈ bilinIsometryGroup B
    rw [hgen]
    exact hg
  have hfaith : FaithfulSMul G X := by
    refine ⟨fun {g h} hgh => ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    by_cases hw : w = 0
    · simpa [hw]
    · have h1 := congrArg Subtype.val (hgh ⟨w, hw⟩)
      have h2 : ((g • (⟨w, hw⟩ : X) : X) : W) =
          ((g : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w := rfl
      have h3 : ((h • (⟨w, hw⟩ : X) : X) : W) =
          ((h : LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w := rfl
      rw [h2, h3] at h1
      exact h1
  letI : FaithfulSMul G X := hfaith
  have hpre : MulAction.IsPretransitive G X := by
    refine ⟨fun u v => ?_⟩
    obtain ⟨g, hg⟩ := htr u.1 v.1 u.2 v.2
    exact ⟨g, Subtype.ext hg⟩
  letI : MulAction.IsPretransitive G X := hpre
  have hodd : ¬ 2 ∣ Nat.card X :=
    odd_card_ne_zero_vectors (W := W) (by omega)
  exact pCore_two_eq_bot_of_faithful_pretransitive_odd hodd

end CFSG.OddTranspositions

namespace CFSG.Fischer.Classification.Recognition.SymO

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal


noncomputable def rhoB {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hnd : (polarBilin Q).Nondegenerate) {v y : V} (hv : Q v = 1)
    (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v) :
    Subgroup.centralizer {t} →*
      CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
        (LinearMap.BilinForm.restrict (polarBilin Q) (perp Q v y)) :=
  (CFSG.OddTranspositions.bilinIsometryGroupEquivIsometryGroup
      (LinearMap.BilinForm.restrict (polarBilin Q) (perp Q v y))).symm.toMonoidHom.comp
    (rho hnd hv hyv t ht)

theorem rhoB_apply {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hnd : (polarBilin Q).Nondegenerate) {v y : V} (hv : Q v = 1)
    (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)
    (c : Subgroup.centralizer {t}) (w : perp Q v y) :
    (((rhoB hnd hv hyv t ht c :
        CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup
          (LinearMap.BilinForm.restrict (polarBilin Q) (perp Q v y))) :
        LinearMap.GeneralLinearGroup (ZMod 2) (perp Q v y)) : perp Q v y → perp Q v y) w =
      restr hyv ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) w := by
  rw [rhoB, MonoidHom.comp_apply]
  change (((CFSG.OddTranspositions.bilinIsometryGroupEquivIsometryGroup
      (LinearMap.BilinForm.restrict (polarBilin Q) (perp Q v y))).symm (rho hnd hv hyv t ht c) :
        LinearMap.GeneralLinearGroup (ZMod 2) (perp Q v y)) : perp Q v y → perp Q v y) w = _
  rw [CFSG.OddTranspositions.bilinIsometryGroupEquivIsometryGroup_symm_apply]
  exact rho_apply hnd hv hyv t ht c w



theorem rhoB_eq_one_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hnd : (polarBilin Q).Nondegenerate) {v y : V} (hv : Q v = 1)
    (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)
    (c : Subgroup.centralizer {t}) :
    rhoB hnd hv hyv t ht c = 1 ↔ rho hnd hv hyv t ht c = 1 := by
  constructor
  · intro h
    have h' := congrArg
      (CFSG.OddTranspositions.bilinIsometryGroupEquivIsometryGroup
        (LinearMap.BilinForm.restrict (polarBilin Q) (perp Q v y))) h
    simpa [rhoB] using h'
  · intro h
    simp [rhoB, h]

def cenT {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (t : TauCeti.QuadraticMap.orthogonalGroup Q) :
    Subgroup.centralizer ({t} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem rho_ker_eq_zpowers {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hnd : (polarBilin Q).Nondegenerate) {v y : V} (hv : Q v = 1)
    (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v) :
    (rho hnd hv hyv t ht).ker = Subgroup.zpowers (cenT t) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hself : polar Q v v = 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  have hrefl : (bil Q).IsRefl := fun x z h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [QuadraticMap.polar_comm]
  refine le_antisymm ?_ ?_
  · intro c hc
    have hfix : ∀ w : perp Q v y,
        restr hyv ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) w = w := by
      intro w
      rw [← rho_apply hnd hv hyv t ht c w, MonoidHom.mem_ker.mp hc]
      rfl
    have hcv : ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) v = v :=
      apply_eq_self_of_mem_centralizer hnd hv t ht c.2
    have hform := apply_eq_of_restr_eq_id hv hyv
      (c : TauCeti.QuadraticMap.orthogonalGroup Q).2 hcv hfix
    let z : V := ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) y - y
    have hzW : z ∈ (bil Q).orthogonal (perp Q v y) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have hwv : polar Q v (w : V) = 0 := by
        rw [QuadraticMap.polar_comm]
        exact polar_perp_left (⟨w, hw⟩ : perp Q v y)
      have hcw : ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) (w : V) = w := by
        rw [hform (w : V), hwv, zero_smul, sub_zero]
      have hiso := polar_map_of_mem (c : TauCeti.QuadraticMap.orthogonalGroup Q).2 (w : V) y
      rw [hcw] at hiso
      change polar Q (w : V) (((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) y - y) = 0
      rw [polar_sub_right, hiso, sub_self]
    have hzspan : z ∈ Submodule.span (ZMod 2) ({v, y} : Set V) := by
      have horth : (bil Q).orthogonal (perp Q v y) =
          Submodule.span (ZMod 2) ({v, y} : Set V) := by
        rw [perp, LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
      exact horth ▸ hzW
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hzspan
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by revert x; decide
    have hb0 : b = 0 := by
      by_contra hb
      have hb1 : b = 1 := (h01 b).resolve_left hb
      have hcy : ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) y =
          a • v := by
        rw [hform y, QuadraticMap.polar_comm Q v y, hyv, one_smul]
        change y - z = a • v
        rw [← hab]
        change y - (a • v + b • y) = a • v
        rw [hb1, one_smul]
        simp [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
        rw [← neg_smul, ZMod.neg_eq_self_mod_two]
      have hcav : ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) (a • v) =
          a • v := by
        rw [map_smul, hcv]
      have hyv' : y = a • v :=
        ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V).injective
          (hcy.trans hcav.symm)
      have hzero : polar Q y v = 0 := by
        rw [hyv', polar_smul_left, hself, smul_zero]
      rw [hyv] at hzero
      exact one_ne_zero hzero
    have hz : z = a • v := by
      have h : a • v + b • y = z := hab
      rw [hb0, zero_smul, add_zero] at h
      exact h.symm
    rcases h01 a with ha | ha
    · have hc1 : c = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [hform x]
        change x - polar Q v x • z = x
        rw [hz, ha, zero_smul, smul_zero, sub_zero]
      rw [hc1]
      exact Subgroup.one_mem _
    · have hct : c = cenT t := by
        apply Subtype.ext
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        rw [hform x]
        change x - polar Q v x • z = (t : V ≃ₗ[ZMod 2] V) x
        rw [hz, ha, one_smul]
        rw [ht, QuadraticMap.polar_comm Q x v]
        rw [sub_eq_add_neg, ← neg_smul, ZMod.neg_eq_self_mod_two]
      rw [hct]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    rw [rho_apply hnd hv hyv t ht]
    change restr hyv ((t : V ≃ₗ[ZMod 2] V)) w = w
    rw [restr_apply]
    have hwv : polar Q (w : V) v = 0 := polar_perp_left w
    change proj hyv ((t : V ≃ₗ[ZMod 2] V) (w : V)) = w
    rw [ht, hwv, zero_smul, add_zero]
    exact proj_coe hyv w

end CFSG.Fischer.Classification.Recognition.SymO




namespace CFSG.OddTranspositions

open CFSG.Fischer.Classification.Recognition.SymO
open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.Alternating
open CFSG.LocalAnalysis.ComponentInitial
open QuadraticMap

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def orthReflections {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  {g | ∃ v, Q v = 1 ∧ (g : V ≃ₗ[ZMod 2] V) = reflect Q v}

theorem noSqE1_orthReflections {m : ℕ} (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 (orthReflections Q) := by
  classical
  have hB : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [QuadraticMap.polar_comm]; simpa using hy x⟩
  intro d hd
  obtain ⟨v, hv, hdv⟩ := hd
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hB hv
  let W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2) := perp Q v y
  let B' : LinearMap.BilinForm (ZMod 2) W :=
    LinearMap.BilinForm.restrict (polarBilin Q) W
  have hB'alt : B'.IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting (bil_isAlt Q) hB hv0
  have hBvy : (bil Q) v y = 1 := by
    rw [bil_apply, QuadraticMap.polar_comm, hyv]
  obtain ⟨-, -, -, -, hndW, hdimW⟩ := hsplit y hBvy
  have hndW' : B'.Nondegenerate := by simpa [B', W, perp] using hndW
  have hdimW' : Module.finrank (ZMod 2) W = 2 * m - 2 := by
    simpa [W, perp, Module.finrank_fin_fun] using hdimW
  have h2W : 2 ≤ Module.finrank (ZMod 2) W := by omega
  have ht : ∀ x, (((d : TauCeti.QuadraticMap.orthogonalGroup Q).1) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x =
      x + QuadraticMap.polar Q x v • v := by
    intro x
    rw [hdv, reflect_apply_of_map_eq_one hv]
  let K : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.RankThree.GF2n.Tim79a.cenGen (orthReflections Q) d
  have hKleC : K ≤ Subgroup.centralizer ({d} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    dsimp only [K]
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen, Subgroup.closure_le]
    exact Set.inter_subset_right
  let rhoK : K →* bilinIsometryGroup B' :=
    (rhoB hB hv hyv d ht).comp (Subgroup.inclusion hKleC)
  have hsurj : Function.Surjective rhoK := by
    have hgen : bilinIsometryGroup B' = Subgroup.closure
        {g : LinearMap.GeneralLinearGroup (ZMod 2) W |
          ∃ a c, g = symplecticTransvection B' hB'alt a c} :=
      alternating_transvection_generation hB'alt hndW'
    have hle : Subgroup.closure
        {g : LinearMap.GeneralLinearGroup (ZMod 2) W |
          ∃ a c, g = symplecticTransvection B' hB'alt a c} ≤
        (rhoK.range).map (bilinIsometryGroup B').subtype := by
      rw [Subgroup.closure_le]
      rintro g ⟨a, c, rfl⟩
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := fun x => by revert x; decide
      rcases h01 c with rfl | rfl
      · rw [symplecticTransvection_zero]
        exact Subgroup.mem_map_of_mem (bilinIsometryGroup B').subtype
          (Subgroup.one_mem (rhoK.range))
      · let u : Fin (2 * m) → ZMod 2 := lift Q v a
        have hQu : Q u = 1 := map_lift hv a
        let c0 : Subgroup.centralizer ({d} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
          ⟨⟨reflect Q u, reflect_mem_orthogonalGroup Q u⟩,
            Subgroup.mem_centralizer_singleton_iff.mpr
              (Subtype.ext (reflect_lift_commute hv ht a))⟩
        have hc0D : (c0 : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ orthReflections Q :=
          ⟨u, hQu, rfl⟩
        have hc0K : (c0 : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ K := by
          dsimp only [K]
          rw [CFSG.RankThree.GF2n.Tim79a.cenGen]
          exact Subgroup.subset_closure ⟨hc0D, c0.2⟩
        let T : bilinIsometryGroup B' :=
          ⟨symplecticTransvection B' hB'alt a 1,
            symplecticTransvection_mem_bilinIsometryGroup hB'alt a 1⟩
        refine Subgroup.mem_map_of_mem (f := (bilinIsometryGroup B').subtype)
          (show T ∈ rhoK.range from ?_)
        refine MonoidHom.mem_range.mpr ⟨(⟨(c0 : TauCeti.QuadraticMap.orthogonalGroup Q), hc0K⟩ : K), ?_⟩
        apply Subtype.ext
        apply Units.ext
        apply LinearMap.ext
        intro x
        rw [MonoidHom.comp_apply, rhoB_apply]
        simp only [Subgroup.coe_inclusion]
        change restr hyv (reflect Q u) x =
          (symplecticTransvection B' hB'alt a 1 : W →ₗ[ZMod 2] W) x
        rw [restr_reflect_lift hv hyv a x, symplecticTransvection_apply]
        simp [B', LinearMap.BilinForm.restrict_apply]
    intro g
    have hg : (g : LinearMap.GeneralLinearGroup (ZMod 2) W) ∈
        Subgroup.closure {h : LinearMap.GeneralLinearGroup (ZMod 2) W |
          ∃ a c, h = symplecticTransvection B' hB'alt a c} :=
      hgen ▸ g.2
    rcases hle hg with ⟨r, hr, hrg⟩
    obtain ⟨x, hx⟩ := hr
    refine ⟨x, ?_⟩
    rw [hx]
    exact Subtype.ext hrg
  have hpcW : CFSG.pCore 2 (bilinIsometryGroup B') = ⊥ :=
    pCore_bilinIsometryGroup_eq_bot B' hB'alt hndW' h2W
  have hpcK : CFSG.inSubgroup (CFSG.pCore 2) K ≤ Subgroup.zpowers d := by
    intro z hz
    rw [CFSG.inSubgroup, Subgroup.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxcomap : x ∈ (Subgroup.zpowers d).comap K.subtype := by
      have hNnorm : (CFSG.pCore 2 K).Normal := CFSG.pCore_normal
      have hmapnorm : ((CFSG.pCore 2 K).map rhoK).Normal := hNnorm.map rhoK hsurj
      have hmapP : IsPGroup 2 ((CFSG.pCore 2 K).map rhoK) :=
        (CFSG.pCore_isPGroup (p := 2) (G := K)).map rhoK
      have hle : (CFSG.pCore 2 K).map rhoK ≤ CFSG.pCore 2 (bilinIsometryGroup B') :=
        le_sSup ⟨hmapnorm, hmapP⟩
      rw [hpcW] at hle
      have hmapbot : (CFSG.pCore 2 K).map rhoK = ⊥ := le_bot_iff.mp hle
      have hxmap : rhoK x ∈ (CFSG.pCore 2 K).map rhoK := Subgroup.mem_map_of_mem rhoK hx
      rw [hmapbot] at hxmap
      have hxker : rhoK x = 1 := by simpa using hxmap
      have hxkerB : rhoB hB hv hyv d ht
          (Subgroup.inclusion hKleC x) = 1 := by
        simpa only [rhoK, MonoidHom.comp_apply] using hxker
      have hxkerR : rho hB hv hyv d ht (Subgroup.inclusion hKleC x) = 1 :=
        (rhoB_eq_one_iff hB hv hyv d ht (Subgroup.inclusion hKleC x)).mp hxkerB
      have hxker' : (Subgroup.inclusion hKleC x) ∈ (rho hB hv hyv d ht).ker := hxkerR
      rw [rho_ker_eq_zpowers] at hxker'
      rw [Subgroup.mem_zpowers_iff] at hxker'
      obtain ⟨n, hn⟩ := hxker'
      rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
      refine ⟨n, ?_⟩
      have := congrArg
        (fun q : Subgroup.centralizer ({d} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) =>
          (q : TauCeti.QuadraticMap.orthogonalGroup Q)) hn
      simpa [cenT, Subgroup.coe_inclusion] using this
    exact Subgroup.mem_subgroupOf.mp hxcomap
  exact hpcK.trans le_sup_left

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.Fischer.Classification
open CFSG.Fischer.Classification.Recognition.SymO
open QuadraticMap Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem noSqE1_of_orth {G : Type} [Group G] {D : Set G}
    (hP : CFSG.Blueprint.Fischer.Pair G D) (hZ : Subgroup.center G = ⊥)
    {m : ℕ} (hm : 2 ≤ m)
    (Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hex : m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (hM : CFSG.Open.fischerLinearModel D
      (CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
        ∀ x, Q (A *ᵥ x) = Q x)
      (CFSG.Open.fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  classical
  set H : Subgroup (GL (Fin (2 * m)) (ZMod 2)) :=
    CFSG.Open.fischerMatrixGroup fun A : Matrix (Fin (2 * m)) (Fin (2 * m)) (ZMod 2) =>
      ∀ x, Q (A *ᵥ x) = Q x with hH
  set T : Set (GL (Fin (2 * m)) (ZMod 2)) :=
    CFSG.Open.fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1 with hT
  rcases hM with ⟨φ, hφ⟩
  have hφ' : ∀ g : G, g ∈ D ↔ ((φ g : H) : GL (Fin (2 * m)) (ZMod 2)) ∈ T := hφ
  have hHmap : H.map (toLinEquiv (Fin (2 * m)) (ZMod 2)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hH, CFSG.Fischer.Classification.fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective
      (toLinEquiv (Fin (2 * m)) (ZMod 2)).surjective _
  let eH : H ≃* TauCeti.QuadraticMap.orthogonalGroup Q :=
    ((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap H).trans
      (MulEquiv.subgroupCongr hHmap)
  let Φ : G ≃* TauCeti.QuadraticMap.orthogonalGroup Q := φ.trans eH
  have hΦ_apply : ∀ g : G,
      ((Φ g : TauCeti.QuadraticMap.orthogonalGroup Q) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) =
      toLinEquiv (Fin (2 * m)) (ZMod 2) ((φ g : H) : GL (Fin (2 * m)) (ZMod 2)) := by
    intro g
    rfl
  have hD : orthReflections Q = Φ '' D := by
    ext g
    constructor
    · rintro ⟨v, hv, hgv⟩
      let A : GL (Fin (2 * m)) (ZMod 2) := orthTransvectionGL Q v
      have hAT : A ∈ T := orthTransvectionGL_mem_fischerTransvections hv
      have hAH : A ∈ H := by
        rw [hH]
        exact fischerTransvections_polar_subset hAT
      let g0 : G := φ.symm ⟨A, hAH⟩
      have hφg0 : φ g0 = ⟨A, hAH⟩ := φ.apply_symm_apply _
      have hg0D : g0 ∈ D := by
        refine (hφ' g0).2 ?_
        show ((φ g0 : H) : GL (Fin (2 * m)) (ZMod 2)) ∈ T
        rw [hφg0]
        exact hAT
      refine ⟨g0, hg0D, ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      rw [hΦ_apply, hφg0]
      change (toLinEquiv (Fin (2 * m)) (ZMod 2) A : (Fin (2 * m) → ZMod 2) →ₗ[ZMod 2] _) x =
        (g : (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) x
      rw [toLinEquiv_orthTransvectionGL, hgv]
      rfl
    · rintro ⟨g0, hg0D, rfl⟩
      have hg0T : ((φ g0 : H) : GL (Fin (2 * m)) (ZMod 2)) ∈ T := by
        refine (hφ' g0).1 hg0D
      obtain ⟨v, hv, hgv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections hg0T
      refine ⟨v, hv, ?_⟩
      rw [hΦ_apply]
      change (toLinEquiv (Fin (2 * m)) (ZMod 2)
        ((φ g0 : H) : GL (Fin (2 * m)) (ZMod 2)) :
        (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) = reflect Q v
      rw [hgv, toLinEquiv_orthTransvectionGL]
  exact noSqE1_of_map_mulEquiv Φ hD (noSqE1_orthReflections hm Q hnd)

end CFSG.OddTranspositions
