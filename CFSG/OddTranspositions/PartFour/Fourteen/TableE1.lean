module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthQuotient

public noncomputable section

namespace CFSG.OddTranspositions.PartFour

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply
  symplecticTransvection_zero alternating_transvection_generation
  alternating_transvection_vector_transitivity)

theorem noSqE1_of_pCore_centralizer_le {G : Type} [Group G] {D : Set G}
    (hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D)
    (hC : ∀ d ∈ D,
      (CFSG.pCore 2 (Subgroup.centralizer ({d} : Set G))).map
        (Subgroup.centralizer ({d} : Set G)).subtype ≤ Subgroup.zpowers d) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  intro d hd
  let C : Subgroup G := Subgroup.centralizer ({d} : Set G)
  let K : Subgroup G := CFSG.RankThree.GF2n.Tim79a.cenGen D d
  have hKC : K ≤ C := by
    change CFSG.RankThree.GF2n.Tim79a.cenGen D d ≤ C
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen, Subgroup.closure_le]
    intro x hx
    exact hx.2
  have hconj : ∀ x ∈ D ∩ (C : Set G), ∀ c ∈ C, c * x * c⁻¹ ∈ D ∩ (C : Set G) := by
    intro x hx c hc
    obtain ⟨hxD, hxC⟩ := hx
    refine ⟨hN c x hxD, ?_⟩
    change c * x * c⁻¹ ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxd : x * d = d * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (show x ∈ Subgroup.centralizer {d} from hxC)
    have hcd : c * d = d * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (show c ∈ Subgroup.centralizer {d} from hc)
    have hc'd : c⁻¹ * d = d * c⁻¹ := by
      calc c⁻¹ * d = c⁻¹ * (d * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * d) * c⁻¹ := by rw [← hcd]
        _ = d * c⁻¹ := by group
    calc c * x * c⁻¹ * d = c * x * (c⁻¹ * d) := by group
      _ = c * (x * d) * c⁻¹ := by rw [hc'd]; group
      _ = (c * d) * x * c⁻¹ := by rw [hxd]; group
      _ = d * (c * x * c⁻¹) := by rw [hcd]; group
  have hconj_mem : ∀ x ∈ K, ∀ c ∈ C, c * x * c⁻¹ ∈ K := by
    intro x hx c hc
    change x ∈ CFSG.RankThree.GF2n.Tim79a.cenGen D d at hx
    change c * x * c⁻¹ ∈ CFSG.RankThree.GF2n.Tim79a.cenGen D d
    rw [CFSG.RankThree.GF2n.Tim79a.cenGen] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact Subgroup.subset_closure (hconj y hy c hc)
    | one => simp
    | mul a b ha hb iha ihb =>
        rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group]
        exact Subgroup.mul_mem _ iha ihb
    | inv a ha iha =>
        rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ iha
  have hKnormal : (K.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro h k hh hk
    exact hconj_mem h hh k hk
  let KC : Subgroup C := K.subgroupOf C
  have : KC.Normal := hKnormal
  let e : KC ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  have hpc : (CFSG.pCore 2 KC).map e.toMonoidHom = CFSG.pCore 2 K :=
    CFSG.pCore_map_iso 2 e
  let PC : Subgroup C := (CFSG.pCore 2 KC).map KC.subtype
  have hPCnormal : PC.Normal := ConjAct.normal_of_characteristic_of_normal
  have hPCp : IsPGroup 2 PC := CFSG.pCore_isPGroup.map KC.subtype
  have hPCle : PC ≤ CFSG.pCore 2 C :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hPCnormal hPCp
  have hcomp : C.subtype.comp KC.subtype = K.subtype.comp e.toMonoidHom := by
    ext z
    rfl
  have hmap : CFSG.inSubgroup (CFSG.pCore 2) K = PC.map C.subtype := by
    change (CFSG.pCore 2 K).map K.subtype = ((CFSG.pCore 2 KC).map KC.subtype).map C.subtype
    rw [← hpc, Subgroup.map_map, Subgroup.map_map, hcomp]
  change CFSG.inSubgroup (CFSG.pCore 2) K ≤ Subgroup.zpowers d ⊔ Subgroup.center G
  rw [hmap]
  exact (Subgroup.map_mono (f := C.subtype) hPCle).trans ((hC d hd).trans le_sup_left)

theorem pCore_two_eq_bot_of_faithful_pretransitive_of_not_two_dvd {G X : Type*} [Group G]
    [Finite X] [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
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
  calc n • g • x₀ = (g * (g⁻¹ * n * g)) • x₀ := by rw [← mul_smul]; group
    _ = g • (g⁻¹ * n * g) • x₀ := mul_smul _ _ _
    _ = g • x₀ := by rw [h1]

theorem not_two_dvd_card_ne_zero_of_charTwo {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (hW : 1 ≤ Module.finrank K W) :
    ¬ 2 ∣ Nat.card {w : W // w ≠ 0} := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype W := Module.fintypeOfFintype (Module.finBasis K W)
  have h2K : 2 ∣ Nat.card K := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.pos.ne'
  have hcardW : Nat.card W = Nat.card K ^ Module.finrank K W := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_fintype
      (Module.finBasis K W), Fintype.card_fin]
  have hcardX : Nat.card {w : W // w ≠ 0} = Nat.card W - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp
  have h2W : 2 ∣ Nat.card W := by
    rw [hcardW]
    exact h2K.trans (dvd_pow_self _ (by omega))
  have hpos : 1 ≤ Nat.card W := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [hcardX]
  intro hdvd
  have h1 : 2 ∣ Nat.card W - (Nat.card W - 1) := Nat.dvd_sub h2W hdvd
  rw [Nat.sub_sub_self hpos] at h1
  omega

theorem pCore_bilinIsometryGroup_eq_bot_of_charTwo {K W : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (B : LinearMap.BilinForm K W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (h1 : 1 ≤ Module.finrank K W) :
    CFSG.pCore 2 (bilinIsometryGroup B) = ⊥ := by
  classical
  have : Finite W := Module.finite_of_finite K
  let G := bilinIsometryGroup B
  let X := {w : W // w ≠ 0}
  have hgen : bilinIsometryGroup B = Subgroup.closure
      {g : LinearMap.GeneralLinearGroup K W | ∃ a c, g = symplecticTransvection B hB a c} :=
    alternating_transvection_generation hB hnd
  have htr : ∀ u v : W, u ≠ 0 → v ≠ 0 →
      ∃ g : G, ((g : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) u = v := by
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
    · simp [hw]
    · have h1 := congrArg Subtype.val (hgh ⟨w, hw⟩)
      have h2 : ((g • (⟨w, hw⟩ : X) : X) : W) =
          ((g : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) w := rfl
      have h3 : ((h • (⟨w, hw⟩ : X) : X) : W) =
          ((h : LinearMap.GeneralLinearGroup K W) : W →ₗ[K] W) w := rfl
      rw [h2, h3] at h1
      exact h1
  have hpre : MulAction.IsPretransitive G X := by
    refine ⟨fun u v => ?_⟩
    obtain ⟨g, hg⟩ := htr u.1 v.1 u.2 v.2
    exact ⟨g, Subtype.ext hg⟩
  exact pCore_two_eq_bot_of_faithful_pretransitive_of_not_two_dvd
    (not_two_dvd_card_ne_zero_of_charTwo (K := K) (W := W) h1)


section Centralizer

variable {K : Type} [Field K] [CharP K 2] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}
  (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1)
include hQ hv

private theorem exists_lift_transvection_of_charTwo [Finite K] (u : vPerp Q v) (c : K) :
    ∃ g : symmetryCentralizer Q v,
      symmetryRestrict hQ hv g = symplecticTransvection (vQuotForm Q v) (vQuotForm_isAlt Q v)
        (Submodule.Quotient.mk u) c := by
  by_cases hc : c = 0
  · refine ⟨1, ?_⟩
    rw [map_one, hc, symplecticTransvection_zero]
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c⁻¹ + Q u)
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have huv : polar Q (u : Fin d → K) v = 0 := by
    rw [polar_comm]
    exact u.2
  have hvv : polar Q v v = 0 := by rw [polar_self, hv, two_nsmul, CharTwo.add_self_eq_zero]
  set z₀ : Fin d → K := (u : Fin d → K) + b • v with hz₀def
  set z : Fin d → K := l • z₀ with hzdef
  have hz₀ : Q z₀ = c⁻¹ := by
    rw [hz₀def, QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, polar_smul_right, huv,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_one]
    linear_combination hb.symm + Q u * h22
  have hz : Q z = 1 := by
    rw [hzdef, QuadraticMap.map_smul, hz₀, smul_eq_mul, ← hl, mul_inv_cancel₀ hc]
  have hzv : polar Q z v = 0 := by
    rw [hzdef, hz₀def, polar_smul_left, polar_add_left, polar_smul_left, huv, hvv, smul_zero,
      add_zero, smul_zero]
  have hsz : symmetryGL Q z ∈ symmetryCentralizer Q v := by
    refine ⟨symmetryGL_mem Q z,
      (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q z)).mpr ?_⟩
    rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero]
  refine ⟨⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [symmetryRestrict_mk, symplecticTransvection_apply, vQuotForm_mk,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
      Submodule.mem_comap]
    have hx : polar Q v (x : Fin d → K) = 0 := x.2
    have hxz₀ : polar Q z₀ (x : Fin d → K) = polar Q (x : Fin d → K) u := by
      rw [hz₀def, polar_add_left, polar_smul_left, hx, smul_zero, add_zero, polar_comm]
    have hact : ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
        symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) =
        (x : Fin d → K) + (c * polar Q (x : Fin d → K) u) • (u : Fin d → K) +
          (c * polar Q (x : Fin d → K) u * b) • v := by
      rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        symmetryGL_mulVec_of_charTwo hv, hx, zero_smul, add_zero,
        symmetryGL_mulVec_of_charTwo hz, hzdef, polar_smul_left, hxz₀, hl, hz₀def]
      module
    refine Submodule.mem_span_singleton.mpr ⟨c * polar Q (x : Fin d → K) u * b, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_add,
      Submodule.coe_smul]
    change _ = ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
        symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) - _
    rw [hact]
    abel

private theorem range_symmetryRestrict_of_charTwo [Finite K] :
    (symmetryRestrict hQ hv).range = bilinIsometryGroup (vQuotForm Q v) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact symmetryRestrict_mem hQ hv g
  · rw [alternating_transvection_generation (vQuotForm_isAlt Q v)
      (vQuotForm_nondegenerate hQ hv0), Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨g, hg⟩ := exists_lift_transvection_of_charTwo hQ hv u c
    exact ⟨g, hg⟩

private theorem pCore_symmetryCentralizer_le [Finite K] (hd : 4 ≤ d) :
    CFSG.pCore 2 (symmetryCentralizer Q v) ≤
      Subgroup.zpowers ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  set S : Subgroup (LinearMap.GeneralLinearGroup K (vQuot Q v)) :=
    bilinIsometryGroup (vQuotForm Q v) with hS
  let ρ := (symmetryRestrict hQ hv).codRestrict S (fun g => symmetryRestrict_mem hQ hv g)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨g, hg⟩ : y ∈ (symmetryRestrict hQ hv).range := by
      rw [range_symmetryRestrict_of_charTwo hQ hv]
      exact hy
    exact ⟨g, Subtype.ext hg⟩
  have hdim : 1 ≤ Module.finrank K (vQuot Q v) := by
    have := finrank_vQuot hQ hv
    omega
  have hSbot : CFSG.pCore 2 S = ⊥ :=
    pCore_bilinIsometryGroup_eq_bot_of_charTwo (vQuotForm Q v) (vQuotForm_isAlt Q v)
      (vQuotForm_nondegenerate hQ hv0) hdim
  have hnormal : ((CFSG.pCore 2 (symmetryCentralizer Q v)).map ρ).Normal :=
    (CFSG.pCore_normal (p := 2)).map ρ hρ
  have hp : IsPGroup 2 ((CFSG.pCore 2 (symmetryCentralizer Q v)).map ρ) :=
    CFSG.pCore_isPGroup.map ρ
  have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hnormal hp
  rw [hSbot, le_bot_iff, Subgroup.map_eq_bot_iff, MonoidHom.ker_codRestrict,
    ker_symmetryRestrict hQ hv] at hle
  exact hle

end Centralizer

private theorem mul_self_eq_one_of_rank_eq_one {K : Type} [Field K] [CharP K 2] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : Q.polarBilin.Nondegenerate) {s : GL (Fin d) K}
    (hs : s ∈ matrixIsometries Q) (hr : ((s : Matrix (Fin d) (Fin d) K) - 1).rank = 1) :
    s * s = 1 := by
  set S : Matrix (Fin d) (Fin d) K := (s : Matrix (Fin d) (Fin d) K) with hSdef
  have hiso : ∀ x, Q (S *ᵥ x) = Q x := (mem_matrixIsometries_iff Q s).mp hs
  have hpol : ∀ x y, polar Q (S *ᵥ x) (S *ᵥ y) = polar Q x y := fun x y => by
    rw [polar, polar, ← Matrix.mulVec_add, hiso, hiso, hiso]
  rw [Matrix.rank] at hr
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp hr
  set w' : Fin d → K := (w : Fin d → K) with hw'def
  have hw'0 : w' ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hc : ∀ x, ∃ a : K, S *ᵥ x = x + a • w' := by
    intro x
    obtain ⟨a, ha⟩ := hw ⟨_, LinearMap.mem_range_self (S - 1).mulVecLin x⟩
    refine ⟨a, ?_⟩
    have h : a • w' = (S - 1) *ᵥ x := congrArg Subtype.val ha
    rw [h, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hww : polar Q w' w' = 0 := by rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]
  obtain ⟨μ, hμ⟩ := hc w'
  have hkey : ∀ y, μ * polar Q y w' = 0 := by
    intro y
    obtain ⟨a, ha⟩ := hc y
    have h := hpol y w'
    rw [ha, hμ] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hww,
      smul_eq_mul] at h
    linear_combination h
  have hSw : S *ᵥ w' = w' := by
    by_cases hμ0 : μ = 0
    · rw [hμ, hμ0, zero_smul, add_zero]
    · exfalso
      apply hw'0
      apply hQ.1
      intro y
      rw [polarBilin_apply_apply, polar_comm]
      exact (mul_eq_zero.mp (hkey y)).resolve_left hμ0
  have hSS : ∀ x, S *ᵥ (S *ᵥ x) = x := by
    intro x
    obtain ⟨a, ha⟩ := hc x
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hSw, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  exact hSS x

private theorem pCore_centralizer_le_of_injective {G M : Type} [Group G] [Group M]
    {φ : G →* M} (hφ : Function.Injective φ) {X : Subgroup M} (hX : φ.range = X) {x : G}
    {y : M} (hy : φ x = y) (hyX : y ∈ X ⊓ Subgroup.centralizer ({y} : Set M))
    (h : CFSG.pCore 2 ↥(X ⊓ Subgroup.centralizer ({y} : Set M)) ≤ Subgroup.zpowers ⟨y, hyX⟩) :
    (CFSG.pCore 2 (Subgroup.centralizer ({x} : Set G))).map
      (Subgroup.centralizer ({x} : Set G)).subtype ≤ Subgroup.zpowers x := by
  subst hy hX
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  have hmap : C.map φ = φ.range ⊓ Subgroup.centralizer ({φ x} : Set M) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]
    · intro hz
      obtain ⟨⟨g, rfl⟩, hz⟩ := Subgroup.mem_inf.mp hz
      refine ⟨g, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply hφ
      rw [map_mul, map_mul, hz]
  let ψ : C ≃* ↥(φ.range ⊓ Subgroup.centralizer ({φ x} : Set M)) :=
    (C.equivMapOfInjective φ hφ).trans (MulEquiv.subgroupCongr hmap)
  have hψ : (CFSG.pCore 2 C).map ψ.toMonoidHom = CFSG.pCore 2 _ := CFSG.pCore_map_iso 2 ψ
  rintro _ ⟨c, hc, rfl⟩
  have hc' : ψ c ∈ CFSG.pCore 2 ↥(φ.range ⊓ Subgroup.centralizer ({φ x} : Set M)) := by
    rw [← hψ]
    exact Subgroup.mem_map_of_mem _ hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (h hc')
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, hφ ?_⟩
  have hval := congrArg Subtype.val hn
  rw [Subgroup.coe_zpow] at hval
  rw [map_zpow]
  exact hval

private theorem nondegenerate_reindexQuadraticForm {ι K : Type} [Field K] {d : ℕ}
    (e : ι ≃ Fin d) {Q₀ : QuadraticForm K (ι → K)} (hQ₀ : Q₀.polarBilin.Nondegenerate) :
    (reindexQuadraticForm e Q₀).polarBilin.Nondegenerate := by
  have hpol : ∀ y z, polar (reindexQuadraticForm e Q₀) y z =
      polar Q₀ ((reindexVectorEquiv (K := K) e).symm y)
        ((reindexVectorEquiv (K := K) e).symm z) := by
    intro y z
    simp only [polar, reindexQuadraticForm, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      map_add]
  have hsep : ∀ x : Fin d → K, (∀ y, polar (reindexQuadraticForm e Q₀) x y = 0) → x = 0 := by
    intro x hx
    have h0 : (reindexVectorEquiv (K := K) e).symm x = 0 := by
      apply hQ₀.1
      intro y
      have h := hx (reindexVectorEquiv e y)
      rwa [hpol, LinearEquiv.symm_apply_apply, ← polarBilin_apply_apply] at h
    exact ((reindexVectorEquiv (K := K) e).symm.map_eq_zero_iff).mp h0
  refine ⟨fun x hx => hsep x fun y => ?_, fun x hx => hsep x fun y => ?_⟩
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hx y

private theorem noSqE1_of_rankOne_model {G ι F : Type} [Group G] [Fintype ι] [DecidableEq ι]
    [Field F] [Finite F] [CharP F 2] {D : Set G} (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hZ : Subgroup.center G = ⊥) {s : G} (hs : s ∈ D) {Q₀ : QuadraticForm F (ι → F)}
    (hQ₀ : Q₀.polarBilin.Nondegenerate) (hι : 4 ≤ Fintype.card ι) {O : Subgroup (GL ι F)}
    (hO : O = (TauCeti.QuadraticMap.orthogonalGroup Q₀).comap (toLinEquiv ι F).toMonoidHom)
    (e : G ⧸ Subgroup.center G ≃* O)
    (hr : CFSG.LocalAnalysis.WeakClosure81.IsRankOneIn
      ((e (QuotientGroup.mk s) : O) : GL ι F)) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  obtain ⟨d₀, rfl⟩ := hcls
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set Q := reindexQuadraticForm σ Q₀ with hQdef
  have hQ : Q.polarBilin.Nondegenerate := nondegenerate_reindexQuadraticForm σ hQ₀
  let φ : G →* GL (Fin (Fintype.card ι)) F := (reindexMatrixEquiv σ).toMonoidHom.comp
    (O.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))))
  have hmk : Function.Injective (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hZ]
  have hφ : Function.Injective φ :=
    (reindexMatrixEquiv σ).injective.comp (O.subtype_injective.comp (e.injective.comp hmk))
  have hmem : ∀ A : GL ι F, reindexMatrixEquiv σ A ∈ matrixIsometries Q ↔ A ∈ O := by
    intro A
    rw [hO]
    exact reindexMatrixEquiv_mem_isometries σ Q₀ A
  have hrange : φ.range = matrixIsometries Q := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      exact (hmem _).mpr (e _).2
    · intro hA
      obtain ⟨B, rfl⟩ := (reindexMatrixEquiv σ).surjective A
      obtain ⟨q, hq⟩ := e.surjective ⟨B, (hmem B).mp hA⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
      refine ⟨g, ?_⟩
      show reindexMatrixEquiv σ ((e (QuotientGroup.mk' (Subgroup.center G) g) : O) : GL ι F) = _
      rw [hq]
  have hφmem : ∀ g, φ g ∈ matrixIsometries Q := fun g => by
    rw [← hrange]
    exact ⟨g, rfl⟩
  have hrs : (((φ s : GL (Fin (Fintype.card ι)) F) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) F) - 1).rank = 1 := by
    have h : ((φ s : GL (Fin (Fintype.card ι)) F) :
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) F) - 1 =
        Matrix.reindex σ σ ((((e (QuotientGroup.mk s) : O) : GL ι F) : Matrix ι ι F) - 1) := by
      show Matrix.reindex σ σ ((((e (QuotientGroup.mk s) : O) : GL ι F) : Matrix ι ι F)) - 1 = _
      simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
        Matrix.submatrix_one_equiv]
    rw [h, Matrix.rank_reindex]
    exact hr
  have hs2 : φ s * φ s = 1 := mul_self_eq_one_of_rank_eq_one hQ (hφmem s) hrs
  have hs1 : φ s ≠ 1 := by
    intro h
    rw [h, Units.val_one, sub_self, Matrix.rank_zero] at hrs
    exact zero_ne_one hrs
  obtain ⟨w, hw, hsw⟩ := OmegaRadical.exists_symmetry_of_rank_le_one hQ (hφmem s) hs2 hs1 hrs.le
  have hN : ∀ g x : G, x ∈ {g | IsConj d₀ g} → g * x * g⁻¹ ∈ {g | IsConj d₀ g} :=
    fun g x hx => (show IsConj d₀ x from hx).trans (isConj_iff.mpr ⟨g, rfl⟩)
  refine noSqE1_of_pCore_centralizer_le hN fun x hx => ?_
  obtain ⟨g, rfl⟩ := isConj_iff.mp ((show IsConj d₀ s from hs).symm.trans hx)
  have hw' : Q (((φ g : GL (Fin (Fintype.card ι)) F) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) F) *ᵥ w) = 1 := by
    rw [← hw]
    exact (mem_matrixIsometries_iff Q _).mp (hφmem g) w
  have hφx : φ (g * s * g⁻¹) = symmetryGL Q (((φ g : GL (Fin (Fintype.card ι)) F) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) F) *ᵥ w) := by
    rw [map_mul, map_mul, map_inv, hsw, conj_symmetryGL (hφmem g)]
  exact pCore_centralizer_le_of_injective hφ hrange hφx symmetryGL_mem_symmetryCentralizer
    (pCore_symmetryCentralizer_le hQ hw' hι)

theorem noSqE1_of_isOrthReflection {G : Type} [Group G] [Finite G] {D : Set G}
    (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hZ : Subgroup.center G = ⊥) {s : G} (hs : s ∈ D)
    {m f : ℕ} (ho : CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection G m f s) :
    CFSG.RankThree.GF2n.Tim79a.NoSqE1 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases ho with ⟨k, hk, -, F, hF, hFin, hcard, e, hr⟩ |
    ⟨k, hk, -, F, hF, hFin, hcard, b, c, hbc, e, hr⟩
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have hcoeq : ⇑(CFSG.LieType.Universal.Spin.quadPlus k F) =
        CFSG.PGLModel.plusQuadForm k (K := F) := by
      funext v
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      rfl
    have hO : CFSG.PGLModel.orthogonalPlus k F =
        (TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus k F)).comap
          (toLinEquiv (Fin k ⊕ Fin k) F).toMonoidHom := by
      have h := closure_isometries_eq_comap (ι := Fin k ⊕ Fin k) (K := F) hcoeq
      simpa [CFSG.PGLModel.orthogonalPlus, CFSG.PGLModel.orthogonalGroup,
        CFSG.MatrixModel.isometryCore] using h
    exact noSqE1_of_rankOne_model hcls hZ hs
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus k F)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hO e hr
  · let _ : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (by rwa [Nat.card_eq_fintype_card] at hcard)
    have hcoeq : ⇑(CFSG.LieType.Universal.Spin.quadMinus (k + 1) F b c) =
        CFSG.PGLModel.minusQuadForm k (K := F) b c := by
      funext v
      rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
      rfl
    have hO : CFSG.PGLModel.orthogonalMinus k F b c =
        (TauCeti.QuadraticMap.orthogonalGroup
          (CFSG.LieType.Universal.Spin.quadMinus (k + 1) F b c)).comap
          (toLinEquiv (Fin k ⊕ Fin k ⊕ Fin 2) F).toMonoidHom := by
      have h := closure_isometries_eq_comap (ι := Fin k ⊕ Fin k ⊕ Fin 2) (K := F) hcoeq
      simpa [CFSG.PGLModel.orthogonalMinus, CFSG.PGLModel.orthogonalGroup,
        CFSG.MatrixModel.isometryCore] using h
    exact noSqE1_of_rankOne_model hcls hZ hs
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := k + 1)
        (K := F) hbc)
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hO e hr

end CFSG.OddTranspositions.PartFour

end
