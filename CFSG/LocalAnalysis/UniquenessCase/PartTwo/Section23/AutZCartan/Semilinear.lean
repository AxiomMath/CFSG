module

public import CFSG.Open.LocalVocabulary
import CFSG.Milestones.ASVolI.A1
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelSemilinear
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open
open CFSG.ShultStronglyClosedTI.CyclicSemiregular
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

private lemma existsUnique_of_commutative_transitive {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃! x : X, (x : V ≃ₗ[ZMod 2] V) v = w := by
  intro v w hv hw
  obtain ⟨x, hx, hxw⟩ := htrans v w hv hw
  refine ⟨⟨x, hx⟩, hxw, ?_⟩
  rintro ⟨y, hy⟩ hyw
  have hfix : ∀ s : X, ((s : V ≃ₗ[ZMod 2] V) v = v) → s = 1 := by
    intro s hs
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    by_cases hu : u = 0
    · rw [hu, map_zero]; rfl
    · obtain ⟨t, ht, htv⟩ := htrans v u hv hu
      have hst : ((s : V ≃ₗ[ZMod 2] V) * (t : V ≃ₗ[ZMod 2] V)) =
          ((t : V ≃ₗ[ZMod 2] V) * (s : V ≃ₗ[ZMod 2] V)) :=
        hcomm s.1 s.2 t ht
      calc (s : V ≃ₗ[ZMod 2] V) u
          = (s : V ≃ₗ[ZMod 2] V) ((t : V ≃ₗ[ZMod 2] V) v) := by rw [htv]
        _ = ((s : V ≃ₗ[ZMod 2] V) * (t : V ≃ₗ[ZMod 2] V)) v := rfl
        _ = ((t : V ≃ₗ[ZMod 2] V) * (s : V ≃ₗ[ZMod 2] V)) v := by rw [hst]
        _ = (t : V ≃ₗ[ZMod 2] V) ((s : V ≃ₗ[ZMod 2] V) v) := rfl
        _ = (t : V ≃ₗ[ZMod 2] V) v := by rw [hs]
        _ = u := htv
  have hfixxy : ((((⟨x, hx⟩ : X)⁻¹ * ⟨y, hy⟩ : X) : V ≃ₗ[ZMod 2] V)) v = v := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply, hyw, ← hxw]
    change ((⟨x, hx⟩ : X) : V ≃ₗ[ZMod 2] V).symm
      (((⟨x, hx⟩ : X) : V ≃ₗ[ZMod 2] V) v) = v
    exact LinearEquiv.symm_apply_apply _ v
  have h2 := hfix (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) hfixxy
  have h3 : (⟨y, hy⟩ : X) = ⟨x, hx⟩ := by
    calc (⟨y, hy⟩ : X) = ⟨x, hx⟩ * (⟨x, hx⟩⁻¹ * ⟨y, hy⟩) := by group
      _ = ⟨x, hx⟩ * 1 := by rw [h2]
      _ = ⟨x, hx⟩ := mul_one _
  exact h3

private lemma card_of_regular {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} {v₀ : V} (hv₀ : v₀ ≠ 0)
    (hreg : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃! x : X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    Nat.card X = Nat.card V - 1 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype {v : V // v ≠ 0} := Fintype.ofFinite _
  let f : X → {v : V // v ≠ 0} := fun x =>
    ⟨(x : V ≃ₗ[ZMod 2] V) v₀, fun h => hv₀ ((x : V ≃ₗ[ZMod 2] V).injective (by
      rw [h, map_zero]))⟩
  have hfb : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hxy' : (x : V ≃ₗ[ZMod 2] V) v₀ = (y : V ≃ₗ[ZMod 2] V) v₀ :=
        congrArg Subtype.val hxy
      obtain ⟨z, -, huniq⟩ := hreg v₀ ((x : V ≃ₗ[ZMod 2] V) v₀) hv₀ (f x).2
      have h1 : x = z := huniq x rfl
      have h2 : y = z := huniq y hxy'.symm
      exact h1.trans h2.symm
    · rintro ⟨w, hw⟩
      obtain ⟨x, hxw⟩ := (hreg v₀ w hv₀ hw).exists
      exact ⟨x, Subtype.ext hxw⟩
  rw [Nat.card_congr (Equiv.ofBijective f hfb), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl (p := fun v : V => v = 0)]
  simp

private lemma generalLinearEquiv_symm_coe {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : V ≃ₗ[ZMod 2] V) (v : V) :
    (((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm f :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) v = f v := by
  rw [show ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm f :
      LinearMap.GeneralLinearGroup (ZMod 2) V) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv f from rfl]
  rfl

private lemma regular_of_cyclic_transitive {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hXcyc : IsCyclic X)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃! x : X, (x : V ≃ₗ[ZMod 2] V) v = w := by
  haveI := hXcyc
  exact existsUnique_of_commutative_transitive
    (fun a ha b hb => congrArg Subtype.val
      ((IsCyclic.commGroup (α := X)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩)) htrans

private lemma card_of_cyclic_transitive {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Nontrivial V] {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hXcyc : IsCyclic X)
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    Nat.card X = Nat.card V - 1 := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  exact card_of_regular hv₀ (regular_of_cyclic_transitive hXcyc htrans)

private lemma normal_of_cyclic_transitive_of_odd {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] [Nontrivial V] {X Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hXcyc : IsCyclic X) (hXY : X ≤ Y) (hodd : Odd (Nat.card Y))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    (X.subgroupOf Y).Normal := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  exact CFSG.ASVolI.as_A_1_12 V X Y hXcyc
    (regular_of_cyclic_transitive hXcyc htrans) hXY hodd

private lemma exists_semilinear_hom_ker {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Nontrivial V] {X Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hXcyc : IsCyclic X)
    (hXY : X ≤ Y) (hodd : Odd (Nat.card Y))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), IsCyclic (RingAut k₀) ∧
      ∃ ι : Y →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀,
        ι.ker = ⊥ ∧ (X.subgroupOf Y).map ι =
          (SemidirectProduct.inl : k₀ˣ →* _).range := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : (X.subgroupOf Y).Normal :=
    normal_of_cyclic_transitive_of_odd hXcyc hXY hodd htrans
  let X' : Subgroup Y := X.subgroupOf Y
  have hX'card : Nat.card X' = 2 ^ Module.finrank (ZMod 2) V - 1 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv,
      card_of_cyclic_transitive hXcyc htrans,
      FiniteField.pow_finrank_eq_natCard 2 V]
  have he : 1 ≤ Module.finrank (ZMod 2) V := by
    have hgt : 1 < Nat.card V := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    by_contra h
    have h0 : Module.finrank (ZMod 2) V = 0 := by omega
    rw [← FiniteField.pow_finrank_eq_natCard 2 V, h0, pow_zero] at hgt
    omega
  have hX'comm : ∀ a ∈ X', ∀ b ∈ X', a * b = b * a := by
    intro a ha b hb
    exact Subtype.ext (congrArg (fun x : X => (x : V ≃ₗ[ZMod 2] V))
      ((IsCyclic.commGroup (α := X)).mul_comm
        ⟨(a : V ≃ₗ[ZMod 2] V), Subgroup.mem_subgroupOf.mp ha⟩
        ⟨(b : V ≃ₗ[ZMod 2] V), Subgroup.mem_subgroupOf.mp hb⟩))
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  let ρB : Y →* LinearMap.GeneralLinearGroup (ZMod 2) V := e.symm.toMonoidHom.comp Y.subtype
  have hρBinj : Function.Injective ρB := by
    intro a b h
    exact Subtype.ext (e.symm.injective (by simpa [ρB] using h))
  have htrans' : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ g ∈ X',
      (((ρB g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        Module.End (ZMod 2) V) v) = w := by
    intro v w hv hw
    obtain ⟨g, hg, hgv⟩ := htrans v w hv hw
    refine ⟨⟨g, hXY hg⟩, Subgroup.mem_subgroupOf.mpr hg, ?_⟩
    exact (generalLinearEquiv_symm_coe g v).trans hgv
  have hX'inj : ∀ g ∈ X', ρB g = 1 → g = 1 := by
    intro g hg h1
    exact hρBinj (by simpa [ρB] using h1)
  obtain ⟨k₀, hF, hFin, hkcard, ev, ι, hιker, hιcompat, hιimage⟩ :=
    CFSG.ShultStronglyClosedTI.LinearChain.semilinear_of_transitive_commutative
      (B := Y) (V := V) (e := Module.finrank (ZMod 2) V) he rfl ρB
      (X := X') hX'comm htrans' hX'inj hX'card
  refine ⟨k₀, hF, hFin, (card_ringAut_and_isCyclic Nat.prime_two k₀ hkcard).2, ι, ?_, hιimage⟩
  rw [hιker]
  exact (MonoidHom.ker_eq_bot_iff ρB).mpr hρBinj

private lemma exists_ringAut_hom_ker {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [Nontrivial V] {X Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hXcyc : IsCyclic X)
    (hXY : X ≤ Y) (hodd : Odd (Nat.card Y))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    ∃ (k₀ : Type) (_ : Field k₀) (_ : Finite k₀), IsCyclic (RingAut k₀) ∧
      ∃ τ : Y →* RingAut k₀, τ.ker = X.subgroupOf Y := by
  obtain ⟨k₀, hF, hFin, hcyc, ι, hιker, hιimage⟩ :=
    exists_semilinear_hom_ker hXcyc hXY hodd htrans
  letI : Field k₀ := hF
  letI : Finite k₀ := hFin
  letI : IsCyclic (RingAut k₀) := hcyc
  let τ : Y →* RingAut k₀ := SemidirectProduct.rightHom.comp ι
  have hιinj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).mp hιker
  refine ⟨k₀, hF, hFin, hcyc, τ, ?_⟩
  ext y
  rw [MonoidHom.mem_ker]
  change SemidirectProduct.rightHom (ι y) = 1 ↔ y ∈ X.subgroupOf Y
  constructor
  · intro h
    have h1 : ι y ∈ (SemidirectProduct.inl :
        k₀ˣ →* k₀ˣ ⋊[ringAutUnits k₀] RingAut k₀).range := by
      rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
      exact h
    rw [← hιimage] at h1
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp h1
    rw [← hιinj hxy]
    exact hx
  · intro hy
    have h1 : ι y ∈ (X.subgroupOf Y).map ι := Subgroup.mem_map_of_mem ι hy
    rw [hιimage] at h1
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at h1
    exact h1

theorem exists_cyclic_quotient_of_regular_cyclic {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] [Nontrivial V] {X Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hXcyc : IsCyclic X) (hXY : X ≤ Y) (hodd : Odd (Nat.card Y))
    (htrans : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ x ∈ X, (x : V ≃ₗ[ZMod 2] V) v = w) :
    (X.subgroupOf Y).Normal ∧
      ∃ y₀ : Y, ∀ y : Y, ∃ k : ℤ, y * (y₀ ^ k)⁻¹ ∈ X.subgroupOf Y := by
  obtain ⟨k₀, hF, hFin, hcyc, τ, hτker⟩ :=
    exists_ringAut_hom_ker hXcyc hXY hodd htrans
  letI : Field k₀ := hF
  letI : Finite k₀ := hFin
  letI : IsCyclic (RingAut k₀) := hcyc
  haveI : IsCyclic τ.range := Subgroup.isCyclic τ.range
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite Y := inferInstance
  obtain ⟨u, -, hu⟩ :=
    CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.exists_cover_of_cyclic_image τ
      (E := ⊤) (by rw [← MonoidHom.range_eq_map]; exact (inferInstance : IsCyclic τ.range))
  refine ⟨normal_of_cyclic_transitive_of_odd hXcyc hXY hodd htrans, u, ?_⟩
  intro y
  obtain ⟨k, hk⟩ := hu y (Subgroup.mem_top y)
  rw [hτker] at hk
  exact ⟨(k : ℤ), by simpa [zpow_natCast] using hk⟩

private def conjRep {M Z : Subgroup G} [IsMulCommutative Z] [Module (ZMod 2) (Additive Z)]
    (hMZ : M ≤ Subgroup.normalizer (Z : Set G)) :
    M →* (Additive Z ≃ₗ[ZMod 2] Additive Z) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive Z)).toMonoidHom.comp
    (((mulAutGL 2 Z).comp Z.normalizerMonoidHom).comp (Subgroup.inclusion hMZ))

private lemma conjRep_apply {M Z : Subgroup G} [IsMulCommutative Z]
    [Module (ZMod 2) (Additive Z)] (hMZ : M ≤ Subgroup.normalizer (Z : Set G)) (b : M)
    (v : Additive Z) :
    ((conjRep (M := M) (Z := Z) hMZ b : Additive Z ≃ₗ[ZMod 2] Additive Z) v).toMul =
      (b : G) * (v.toMul : G) * (b : G)⁻¹ := by
  let ρ₀ : M →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z) :=
    ((mulAutGL 2 Z).comp Z.normalizerMonoidHom).comp (Subgroup.inclusion hMZ)
  have hρ₀ : ∀ (b : M) (v : Additive Z),
      (((ρ₀ b : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Z)) :
        Module.End (ZMod 2) (Additive Z)) v).toMul =
        (b : G) * (v.toMul : G) * (b : G)⁻¹ := fun _ _ => rfl
  have hfun : (conjRep (M := M) (Z := Z) hMZ b : Additive Z → Additive Z) =
      (ρ₀ b : Additive Z → Additive Z) :=
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv (R := ZMod 2) (M := Additive Z)
      (ρ₀ b)
  change ((conjRep (M := M) (Z := Z) hMZ b : Additive Z → Additive Z) v).toMul =
    (b : G) * (v.toMul : G) * (b : G)⁻¹
  rw [hfun]
  exact hρ₀ b v

private lemma conjRep_eq_one_iff {M Z : Subgroup G} [IsMulCommutative Z]
    [Module (ZMod 2) (Additive Z)] (hMZ : M ≤ Subgroup.normalizer (Z : Set G)) (b : M) :
    conjRep (M := M) (Z := Z) hMZ b = 1 ↔
      (b : G) ∈ Subgroup.centralizer (Z : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro hb x hx
    have h1 := congrArg (fun g : Additive Z ≃ₗ[ZMod 2] Additive Z =>
      (((g : Additive Z → Additive Z) (Additive.ofMul ⟨x, hx⟩)).toMul : G)) hb
    have h2 := conjRep_apply (M := M) (Z := Z) hMZ b (Additive.ofMul ⟨x, hx⟩)
    rw [h2] at h1
    simp only [toMul_ofMul, LinearEquiv.coe_one, id_eq] at h1
    calc x * (b : G) = (b : G) * x * (b : G)⁻¹ * b := by rw [h1]
      _ = b * x := by group
  · intro hb
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (b : G) * (v.toMul : G) * (b : G)⁻¹ = (v.toMul : G)
    rw [← hb _ v.toMul.2, mul_inv_cancel_right]

private lemma conjRep_ker {M Z : Subgroup G} [IsMulCommutative Z]
    [Module (ZMod 2) (Additive Z)] (hMZ : M ≤ Subgroup.normalizer (Z : Set G)) :
    (conjRep (M := M) (Z := Z) hMZ).ker =
      (M ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf M := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨b.2, (conjRep_eq_one_iff hMZ b).mp h⟩,
    fun h => (conjRep_eq_one_iff hMZ b).mpr h.2⟩

private lemma conjRep_range_odd {M Z : Subgroup G} [IsMulCommutative Z]
    [Module (ZMod 2) (Additive Z)] (hMZ : M ≤ Subgroup.normalizer (Z : Set G))
    (hodd : Odd ((M ⊓ Subgroup.centralizer (Z : Set G)).relIndex M)) :
    Odd (Nat.card (conjRep (M := M) (Z := Z) hMZ).range) := by
  rw [← Subgroup.index_ker (conjRep (M := M) (Z := Z) hMZ), conjRep_ker hMZ]
  simpa [Subgroup.relIndex] using hodd

private lemma exists_cyclic_transitive {M Z : Subgroup G} [IsMulCommutative Z]
    [Module (ZMod 2) (Additive Z)] (hMZ : M ≤ Subgroup.normalizer (Z : Set G))
    (hZ1 : Z ≠ ⊥) {x : G} (hxM : x ∈ M)
    (htr : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ 1 → w ≠ 1 → ∃ k : ℤ, x ^ k * z * (x ^ k)⁻¹ = w) :
    ∃ X₀ : Subgroup (Additive Z ≃ₗ[ZMod 2] Additive Z), IsCyclic X₀ ∧
      X₀ ≤ (conjRep (M := M) (Z := Z) hMZ).range ∧
      (∀ v w : Additive Z, v ≠ 0 → w ≠ 0 →
        ∃ g ∈ X₀, (g : Additive Z ≃ₗ[ZMod 2] Additive Z) v = w) ∧
      Nat.card X₀ = Nat.card Z - 1 := by
  classical
  let xM : M := ⟨x, hxM⟩
  let X₀ : Subgroup (Additive Z ≃ₗ[ZMod 2] Additive Z) :=
    Subgroup.zpowers (conjRep (M := M) (Z := Z) hMZ xM)
  have hX₀le : X₀ ≤ (conjRep (M := M) (Z := Z) hMZ).range :=
    Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨xM, rfl⟩)
  haveI hX₀cyc : IsCyclic X₀ := Subgroup.isCyclic_zpowers _
  have htrans₀ : ∀ v w : Additive Z, v ≠ 0 → w ≠ 0 →
      ∃ g ∈ X₀, (g : Additive Z ≃ₗ[ZMod 2] Additive Z) v = w := by
    intro v w hv hw
    have hv' : (v.toMul : G) ∈ (Z : Set G) \ {1} :=
      ⟨v.toMul.2, fun h => hv (by
        have h1 : v.toMul = 1 := Subtype.ext h
        simpa using congrArg Additive.ofMul h1)⟩
    have hw' : (w.toMul : G) ∈ (Z : Set G) \ {1} :=
      ⟨w.toMul.2, fun h => hw (by
        have h1 : w.toMul = 1 := Subtype.ext h
        simpa using congrArg Additive.ofMul h1)⟩
    obtain ⟨k, hk⟩ := htr (v.toMul : G) hv'.1 (w.toMul : G) hw'.1 hv'.2 hw'.2
    refine ⟨conjRep (M := M) (Z := Z) hMZ xM ^ k,
      Subgroup.zpow_mem_zpowers _ k, ?_⟩
    have h2 := conjRep_apply hMZ (xM ^ k) v
    rw [map_zpow, Subgroup.coe_zpow] at h2
    refine Additive.toMul.injective ?_
    refine Subtype.ext ?_
    simpa [xM, hk] using h2
  have hreg₀ := regular_of_cyclic_transitive hX₀cyc htrans₀
  obtain ⟨z₀, hz₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have hv₀ : Additive.ofMul z₀ ≠ 0 := by
    intro h
    exact hz₀ (by simpa using congrArg Additive.toMul h)
  refine ⟨X₀, hX₀cyc, hX₀le, htrans₀, ?_⟩
  have h := card_of_regular (X := X₀) hv₀ hreg₀
  rwa [show Nat.card (Additive Z) = Nat.card Z from rfl] at h

private def preimageSubgroup {Y : Type*} [Group Y] {M : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y) : Subgroup G :=
  (X.comap ρ).map M.subtype

private lemma preimageSubgroup_le {Y : Type*} [Group Y] {M : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y) : preimageSubgroup ρ X ≤ M :=
  Subgroup.map_subtype_le _

private lemma preimageSubgroup_subgroupOf {Y : Type*} [Group Y] {M : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y) :
    (preimageSubgroup ρ X).subgroupOf M = X.comap ρ := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (preimageSubgroup_le ρ X)]
  rfl

private lemma preimageSubgroup_normal {Y : Type*} [Group Y] {M : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y) [X.Normal] :
    ((preimageSubgroup ρ X).subgroupOf M).Normal := by
  rw [preimageSubgroup_subgroupOf]
  exact Subgroup.Normal.comap (inferInstance : X.Normal) ρ

private lemma centralizer_le_preimageSubgroup {Y : Type*} [Group Y] {M Z : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y)
    (hker : ρ.ker = (M ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf M) :
    M ⊓ Subgroup.centralizer (Z : Set G) ≤ preimageSubgroup ρ X := by
  intro y hy
  have hy1 : (⟨y, hy.1⟩ : M) ∈ ρ.ker := by
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hy.1, hy.2⟩
  have hyK : (⟨y, hy.1⟩ : M) ∈ X.comap ρ := by
    show ρ (⟨y, hy.1⟩ : M) ∈ X
    rw [MonoidHom.mem_ker.mp hy1]
    exact X.one_mem
  exact Subgroup.mem_map_of_mem M.subtype hyK

private lemma preimageSubgroup_relIndex {Y : Type*} [Group Y] {M Z : Subgroup G}
    {ρ : M →* Y} {X : Subgroup Y} [X.Normal]
    (hker : ρ.ker = (M ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf M)
    (hXle : X ≤ ρ.range) :
    (M ⊓ Subgroup.centralizer (Z : Set G)).relIndex (preimageSubgroup ρ X) = Nat.card X := by
  let C := preimageSubgroup ρ X
  have hCM : C ≤ M := preimageSubgroup_le ρ X
  let ψ : C →* Y := ρ.comp (Subgroup.inclusion hCM)
  have hψker : ψ.ker = (M ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hc
      have h1 : Subgroup.inclusion hCM c ∈ ρ.ker := MonoidHom.mem_ker.mpr hc
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h1
      exact ⟨hCM c.2, h1.2⟩
    · intro hc
      have h1 : Subgroup.inclusion hCM c ∈ ρ.ker := by
        rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨(Subgroup.inclusion hCM c).2, hc.2⟩
      exact MonoidHom.mem_ker.mp h1
  have hψrange : ψ.range = X := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      obtain ⟨k, hkK, hkc⟩ := Subgroup.mem_map.mp c.2
      have hck : Subgroup.inclusion hCM c = k := Subtype.ext hkc.symm
      rw [show ψ c = ρ (Subgroup.inclusion hCM c) from rfl, hck]
      exact hkK
    · intro x hx
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hXle hx)
      have hmK : m ∈ X.comap ρ := by
        show ρ m ∈ X
        rw [hm]
        exact hx
      refine ⟨⟨(m : G), Subgroup.mem_map.mpr ⟨m, hmK, rfl⟩⟩, ?_⟩
      have hincl : Subgroup.inclusion hCM
          ⟨(m : G), Subgroup.mem_map.mpr ⟨m, hmK, rfl⟩⟩ = m := Subtype.ext rfl
      rw [show ψ ⟨(m : G), Subgroup.mem_map.mpr ⟨m, hmK, rfl⟩⟩ =
        ρ (Subgroup.inclusion hCM
          ⟨(m : G), Subgroup.mem_map.mpr ⟨m, hmK, rfl⟩⟩) from rfl, hincl]
      exact hm
  rw [Subgroup.relIndex, ← hψker, Subgroup.index_ker, hψrange]

private lemma preimageSubgroup_generator {Y : Type*} [Group Y] {M : Subgroup G}
    {ρ : M →* Y} {X : Subgroup Y}
    (hquot : ∃ y₀ ∈ ρ.range, ∀ y ∈ ρ.range, ∃ k : ℤ, y * (y₀ ^ k)⁻¹ ∈ X) :
    ∃ m ∈ M, ∀ y ∈ M, ∃ k : ℤ, y * (m ^ k)⁻¹ ∈ preimageSubgroup ρ X := by
  obtain ⟨y₀, hy₀, hquot⟩ := hquot
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hy₀
  refine ⟨m, m.2, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := hquot (ρ ⟨y, hy⟩) (MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩)
  refine ⟨k, ?_⟩
  have hmem : (⟨y, hy⟩ : M) * m ^ (-k) ∈ X.comap ρ := by
    show ρ ((⟨y, hy⟩ : M) * m ^ (-k)) ∈ X
    rw [map_mul, map_zpow, hm]
    simpa [zpow_neg] using hk
  have hzc : (((⟨y, hy⟩ : M) * m ^ (-k) : M) : G) ∈ preimageSubgroup ρ X :=
    Subgroup.mem_map_of_mem M.subtype hmem
  simpa [zpow_neg] using hzc

private lemma exists_preimage_cartan {Y : Type*} [Group Y] {M Z : Subgroup G}
    (ρ : M →* Y) (X : Subgroup Y) [X.Normal]
    (hker : ρ.ker = (M ⊓ Subgroup.centralizer (Z : Set G)).subgroupOf M)
    (hXle : X ≤ ρ.range)
    (hquot : ∃ y₀ ∈ ρ.range, ∀ y ∈ ρ.range, ∃ k : ℤ, y * (y₀ ^ k)⁻¹ ∈ X) :
    ∃ C : Subgroup G, M ⊓ Subgroup.centralizer (Z : Set G) ≤ C ∧ C ≤ M ∧
      (C.subgroupOf M).Normal ∧
      (M ⊓ Subgroup.centralizer (Z : Set G)).relIndex C = Nat.card X ∧
      ∃ m ∈ M, ∀ y ∈ M, ∃ k : ℤ, y * (m ^ k)⁻¹ ∈ C := by
  refine ⟨preimageSubgroup ρ X, centralizer_le_preimageSubgroup ρ X hker,
    preimageSubgroup_le ρ X, preimageSubgroup_normal ρ X,
    preimageSubgroup_relIndex hker hXle, ?_⟩
  exact preimageSubgroup_generator hquot

theorem exists_cartan_of_zpowers_transitive {M Z : Subgroup G} (hZ : IsElemAbelian 2 Z)
    (hZ1 : Z ≠ ⊥) (hMZ : M ≤ Subgroup.normalizer (Z : Set G))
    (hodd : Odd ((M ⊓ Subgroup.centralizer (Z : Set G)).relIndex M)) {x : G} (hxM : x ∈ M)
    (htr : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ 1 → w ≠ 1 → ∃ k : ℤ, x ^ k * z * (x ^ k)⁻¹ = w) :
    ∃ C : Subgroup G, M ⊓ Subgroup.centralizer (Z : Set G) ≤ C ∧ C ≤ M ∧
      (C.subgroupOf M).Normal ∧
      (M ⊓ Subgroup.centralizer (Z : Set G)).relIndex C = Nat.card Z - 1 ∧
      ∃ m ∈ M, ∀ y ∈ M, ∃ k : ℤ, y * (m ^ k)⁻¹ ∈ C := by
  classical
  haveI : IsMulCommutative Z := hZ.1
  letI : Module (ZMod 2) (Additive Z) :=
    AddCommGroup.zmodModule (n := 2) fun v => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact Subtype.ext (hZ.2 _ v.toMul.2)
  haveI : Finite (Additive Z) := inferInstanceAs (Finite Z)
  haveI : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ1
  haveI : Nontrivial (Additive Z) := inferInstance
  let ρ := conjRep (M := M) (Z := Z) hMZ
  obtain ⟨X₀, hX₀cyc, hX₀le, htrans₀, hX₀card⟩ :=
    exists_cyclic_transitive (M := M) (Z := Z) hMZ hZ1 hxM htr
  obtain ⟨hnorm, u, hu⟩ :=
    exists_cyclic_quotient_of_regular_cyclic (X := X₀) (Y := ρ.range)
      hX₀cyc hX₀le (conjRep_range_odd hMZ hodd) htrans₀
  haveI : (X₀.subgroupOf ρ.range).Normal := hnorm
  have hrange : ρ.rangeRestrict.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MonoidHom.rangeRestrict_surjective ρ)
  have hquot : ∃ y₀ ∈ ρ.rangeRestrict.range,
      ∀ y ∈ ρ.rangeRestrict.range, ∃ k : ℤ, y * (y₀ ^ k)⁻¹ ∈ X₀.subgroupOf ρ.range :=
    ⟨u, by rw [hrange]; exact Subgroup.mem_top u, fun y _ => hu y⟩
  obtain ⟨C, hC1, hCM, hCnorm, hCcard, hCgen⟩ :=
    exists_preimage_cartan (M := M) (Z := Z) ρ.rangeRestrict (X₀.subgroupOf ρ.range)
      (by rw [MonoidHom.ker_rangeRestrict]; exact conjRep_ker (M := M) (Z := Z) hMZ)
      (by rw [hrange]; exact le_top) hquot
  refine ⟨C, hC1, hCM, hCnorm, ?_, hCgen⟩
  rw [hCcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₀le).toEquiv, hX₀card]

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
