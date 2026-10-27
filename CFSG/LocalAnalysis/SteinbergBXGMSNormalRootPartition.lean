module

public import CFSG.LocalAnalysis.SteinbergBVGMSNormalRootFamily
public import CFSG.LocalAnalysis.SteinbergCCRegularSubspacePartition

public section

namespace CFSG.LocalAnalysis.SteinbergBX

open Subgroup CFSG CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV
open CFSG.LocalAnalysis.SteinbergBT (linAut)
open scoped IsMulCommutative Pointwise

namespace GMSPartition

section Generic

variable {A : Type*} [Group A] [IsElementaryAbelian 2 A]

noncomputable def subspaceOrderIso : Subgroup A ≃o Submodule (ZMod 2) (Additive A) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

theorem mem_subspaceOrderIso {S : Subgroup A} {w : Additive A} :
    w ∈ subspaceOrderIso S ↔ Additive.toMul w ∈ S :=
  Iff.rfl

theorem map_linAut_subspaceOrderIso (α : MulAut A) (S : Subgroup A) :
    (subspaceOrderIso S).map (linAut α : Additive A →ₗ[ZMod 2] Additive A) =
      subspaceOrderIso (S.map α.toMonoidHom) := by
  ext w
  rw [Submodule.mem_map, mem_subspaceOrderIso, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Additive.toMul y, hy, rfl⟩
  · rintro ⟨x, hx, hxw⟩
    exact ⟨Additive.ofMul x, hx, congrArg Additive.ofMul hxw⟩

theorem card_subspaceOrderIso (S : Subgroup A) :
    Nat.card (subspaceOrderIso S) = Nat.card S :=
  Nat.card_congr
    { toFun := fun w => ⟨Additive.toMul w.1, w.2⟩
      invFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem linAut_injective : Function.Injective (linAut (A := A)) := by
  intro α β hαβ
  ext x
  exact congrArg Additive.toMul
    (congrArg (fun f : Additive A ≃ₗ[ZMod 2] Additive A => f (Additive.ofMul x)) hαβ)

end Generic

section Subspaces

variable {D : Type*} [Group D]

theorem map_conj_le_of_le {V Q : Subgroup D} (hQ : Q ≤ V) (l : normalizer (V : Set D)) :
    Q.map (MulAut.conj (l : D)).toMonoidHom ≤ V := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_normalizer_iff.1 l.2 x).1 (hQ hx)

noncomputable def subspace (V : Subgroup D) [IsElementaryAbelian 2 V] (Q : Subgroup D) :
    Submodule (ZMod 2) (Additive V) :=
  subspaceOrderIso (Q.subgroupOf V)

variable {V : Subgroup D} [IsElementaryAbelian 2 V]

theorem subspace_inj {Q Z : Subgroup D} (hQ : Q ≤ V) (hZ : Z ≤ V) :
    subspace V Q = subspace V Z ↔ Q = Z := by
  rw [subspace, subspace, EmbeddingLike.apply_eq_iff_eq, subgroupOf_inj, inf_of_le_left hQ,
    inf_of_le_left hZ]

theorem subspace_inf (Q Z : Subgroup D) :
    subspace V (Q ⊓ Z) = subspace V Q ⊓ subspace V Z := by
  ext w
  exact Iff.rfl

theorem subspace_bot : subspace V (⊥ : Subgroup D) = ⊥ := by
  rw [subspace, bot_subgroupOf, OrderIso.map_bot]

theorem card_subspace {Q : Subgroup D} (hQ : Q ≤ V) :
    Nat.card (subspace V Q) = Nat.card Q := by
  rw [subspace, card_subspaceOrderIso]
  exact Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv

theorem finrank_subspace [Finite D] {Q : Subgroup D} (hQ : Q ≤ V) {k : ℕ}
    (hk : Nat.card Q = 2 ^ k) : Module.finrank (ZMod 2) (subspace V Q) = k := by
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : FiniteDimensional (ZMod 2) (Additive V) := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspace V Q)
  rw [Nat.card_zmod, card_subspace hQ, hk] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

theorem map_linAut_rho_subspace {Q : Subgroup D} (hQ : Q ≤ V) (l : normalizer (V : Set D)) :
    (subspace V Q).map
        (linAut (V.normalizerMonoidHom l) : Additive V →ₗ[ZMod 2] Additive V) =
      subspace V (Q.map (MulAut.conj (l : D)).toMonoidHom) := by
  rw [subspace, map_linAut_subspaceOrderIso, subspace, ← gms_map_rho hQ l]
  congr 1
  exact (comap_map_eq_self_of_injective V.subtype_injective _).symm

theorem map_linAut_subspace_eq_iff (β : MulAut V) (Q Z : Subgroup D) :
    (subspace V Q).map (linAut β : Additive V →ₗ[ZMod 2] Additive V) = subspace V Z ↔
      β • Q.subgroupOf V = Z.subgroupOf V := by
  rw [subspace, map_linAut_subspaceOrderIso, subspace, EmbeddingLike.apply_eq_iff_eq]
  exact Iff.rfl

end Subspaces

section Native

variable {D : Type*} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_native_partition [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤ normalizer (U : Set D) ∧
    (gmsRootConjugates (U ⊔ R) R).ncard = 2 ^ n ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R, ∀ v ∈ Q, v ≠ 1 → v ∉ U) ∧
    (∀ v ∈ U ⊔ R, v ∉ U → ∃! Q, Q ∈ gmsRootConjugates (U ⊔ R) R ∧ v ∈ Q) ∧
    (∀ α ∈ gmsSingerImage X U (U ⊔ R), ∀ Q ∈ gmsRootConjugates (U ⊔ R) R \ {R},
      ∃ Z ∈ gmsRootConjugates (U ⊔ R) R \ {R},
        α • Q.subgroupOf (U ⊔ R) = Z.subgroupOf (U ⊔ R)) ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R \ {R}, ∀ Z ∈ gmsRootConjugates (U ⊔ R) R \ {R},
      ∃! α : gmsSingerImage X U (U ⊔ R),
        (α : MulAut ↥(U ⊔ R)) • Q.subgroupOf (U ⊔ R) = Z.subgroupOf (U ⊔ R)) ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (U ⊔ R) R, Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) := by
  classical
  have hUR : U ⊓ R = ⊥ := by
    obtain ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, hUR, -, -⟩⟩ := h
    exact hUR
  obtain ⟨hVel, hUcard, hn3, m, hm1, hRcard, hQ, hdisj, htr, -, hstab, -, -, -, hHle, hHn, hHR,
    hHU, -, -, hreg, -⟩ := gms_normal_root_actual_linear_family_and_kernels h
  have : Finite (Additive ↥(U ⊔ R)) := inferInstanceAs (Finite ↥(U ⊔ R))
  have : FiniteDimensional (ZMod 2) (Additive ↥(U ⊔ R)) := Module.Finite.of_finite
  have hleV : ∀ Q ∈ gmsRootConjugates (U ⊔ R) R, Q ≤ U ⊔ R := fun Q hQΔ => (hQ Q hQΔ).1
  have hinj : Set.InjOn (subspace (U ⊔ R)) (gmsRootConjugates (U ⊔ R) R) :=
    fun Q hQΔ Z hZΔ hQZ => (subspace_inj (hleV Q hQΔ) (hleV Z hZΔ)).1 hQZ
  have hUR' : IsCompl (subspace (U ⊔ R) U) (subspace (U ⊔ R) R) := by
    constructor
    · rw [disjoint_iff, ← subspace_inf, hUR, subspace_bot]
    · rw [codisjoint_iff, subspace, subspace, ← OrderIso.map_sup,
        ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self, OrderIso.map_top]
  have hn' : 3 ≤ Module.finrank (ZMod 2) (subspace (U ⊔ R) U) := by
    rw [finrank_subspace le_sup_left hUcard]
    exact hn3
  have hm' : 1 ≤ Module.finrank (ZMod 2) (subspace (U ⊔ R) R) := by
    rw [finrank_subspace le_sup_right hRcard]
    exact hm1
  have hRΔ : subspace (U ⊔ R) R ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R :=
    ⟨R, gms_R_mem, rfl⟩
  have hdimΔ : ∀ Q ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R,
      Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) (subspace (U ⊔ R) R) := by
    rintro _ ⟨Q, hQΔ, rfl⟩
    rw [finrank_subspace (hleV Q hQΔ) (hQ Q hQΔ).2, finrank_subspace le_sup_right hRcard]
  have hdisj' : ∀ Q ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R,
      ∀ Z ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R, Q ≠ Z → Q ⊓ Z = ⊥ := by
    rintro _ ⟨Q, hQΔ, rfl⟩ _ ⟨Z, hZΔ, rfl⟩ hne
    rw [← subspace_inf, hdisj Q hQΔ Z hZΔ (fun hQZ => hne (by rw [hQZ])), subspace_bot]
  have h3' : 3 ≤ (subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R).ncard := by
    rw [hinj.ncard_image]
    exact h3
  set M' : Subgroup (Additive ↥(U ⊔ R) ≃ₗ[ZMod 2] Additive ↥(U ⊔ R)) :=
    (linAut.comp (U ⊔ R).normalizerMonoidHom).range with hM'
  set H' : Subgroup (Additive ↥(U ⊔ R) ≃ₗ[ZMod 2] Additive ↥(U ⊔ R)) :=
    (gmsSingerImage X U (U ⊔ R)).map linAut with hH'
  have hMΔ : ∀ g ∈ M', ∀ Q ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R,
      Q.map (g : Additive ↥(U ⊔ R) →ₗ[ZMod 2] Additive ↥(U ⊔ R)) ∈
        subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R := by
    rintro _ ⟨l, rfl⟩ _ ⟨Q, hQΔ, rfl⟩
    exact ⟨Q.map (MulAut.conj (l : D)).toMonoidHom, map_conj_mem_gmsRootConjugates hQΔ l.2,
      (map_linAut_rho_subspace (hleV Q hQΔ) l).symm⟩
  have hMtr : ∀ Q ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R,
      ∀ Z ∈ subspace (U ⊔ R) '' gmsRootConjugates (U ⊔ R) R,
        ∃ g ∈ M', Q.map (g : Additive ↥(U ⊔ R) →ₗ[ZMod 2] Additive ↥(U ⊔ R)) = Z := by
    rintro _ ⟨Q, hQΔ, rfl⟩ _ ⟨Z, hZΔ, rfl⟩
    obtain ⟨l, hl⟩ := htr.exists_smul_eq ⟨Q, hQΔ⟩ ⟨Z, hZΔ⟩
    refine ⟨linAut ((U ⊔ R).normalizerMonoidHom l), ⟨l, rfl⟩, ?_⟩
    rw [map_linAut_rho_subspace (hleV Q hQΔ) l]
    exact congrArg (subspace (U ⊔ R)) (congrArg Subtype.val hl)
  have hHM : H' ≤ M' := by
    rintro _ ⟨_, ⟨l, -, rfl⟩, rfl⟩
    exact ⟨l, rfl⟩
  have hHnormal : ∀ a ∈ M',
      (subspace (U ⊔ R) R).map (a : Additive ↥(U ⊔ R) →ₗ[ZMod 2] Additive ↥(U ⊔ R)) =
        subspace (U ⊔ R) R → ∀ g ∈ H', a * g * a⁻¹ ∈ H' := by
    rintro _ ⟨l, rfl⟩ hlR _ ⟨β, hβ, rfl⟩
    have h1 : subspace (U ⊔ R) (R.map (MulAut.conj (l : D)).toMonoidHom) =
        subspace (U ⊔ R) R := by
      rw [← map_linAut_rho_subspace le_sup_right l]
      exact hlR
    rw [subspace_inj (map_conj_le_of_le le_sup_right l) le_sup_right] at h1
    have hlMR : l ∈ (gmsRootStabilizer (U ⊔ R) R).comap (U ⊔ R).normalizerMonoidHom := by
      rw [hstab, mem_subgroupOf]
      exact map_conj_eq_self_iff.1 h1
    have hconj := hHn.conj_mem ⟨β, hHle hβ⟩ (mem_subgroupOf.2 hβ) ⟨_, hlMR⟩
    rw [mem_subgroupOf] at hconj
    refine ⟨_, hconj, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, MonoidHom.comp_apply]
  have hHU' : ∀ g ∈ H',
      (subspace (U ⊔ R) U).map (g : Additive ↥(U ⊔ R) →ₗ[ZMod 2] Additive ↥(U ⊔ R)) =
        subspace (U ⊔ R) U := by
    rintro _ ⟨β, hβ, rfl⟩
    exact (map_linAut_subspace_eq_iff β U U).2 (hHU β hβ)
  have hHR' : ∀ g ∈ H', ∀ r ∈ subspace (U ⊔ R) R, g r = r := by
    rintro _ ⟨β, hβ, rfl⟩ r hr
    exact congrArg Additive.ofMul (hHR β hβ (Additive.toMul r) hr)
  have hreg' : ∀ u ∈ subspace (U ⊔ R) U, ∀ v ∈ subspace (U ⊔ R) U, u ≠ 0 → v ≠ 0 →
      ∃! g, g ∈ H' ∧ g u = v := by
    intro u hu v hv hu0 hv0
    obtain ⟨α, hα, hαu⟩ := hreg (Additive.toMul u) (Additive.toMul v) hu hv
      (fun h1 => hu0 (toMul_eq_one.1 h1)) (fun h1 => hv0 (toMul_eq_one.1 h1))
    refine ⟨linAut (α : MulAut ↥(U ⊔ R)), ⟨⟨α, α.2, rfl⟩, congrArg Additive.ofMul hα⟩, ?_⟩
    rintro _ ⟨⟨β, hβ, rfl⟩, hβu⟩
    rw [show β = (α : MulAut ↥(U ⊔ R)) from
      congrArg Subtype.val (hαu ⟨β, hβ⟩ (congrArg Additive.toMul hβu))]
  obtain ⟨hMU, hΔcard, hnz, hpart, hHΔ, hHreg, h2tr⟩ :=
    binary_regular_subspace_family_partition (subspace (U ⊔ R) U) (subspace (U ⊔ R) R) hUR' hn'
      hm' _ hRΔ hdimΔ hdisj' h3' M' hMΔ hMtr H' hHM hHnormal hHU' hHR' hreg'
  have hRne : ∀ Q ∈ gmsRootConjugates (U ⊔ R) R, Q ∉ ({R} : Set (Subgroup D)) →
      subspace (U ⊔ R) Q ∉ ({subspace (U ⊔ R) R} : Set (Submodule (ZMod 2) _)) :=
    fun Q hQΔ hQR hQR' => hQR ((subspace_inj (hleV Q hQΔ) le_sup_right).1 hQR')
  refine ⟨fun l hl => ?_, ?_, fun Q hQΔ v hv hv1 hvU => ?_, fun v hvV hvU => ?_,
    fun α hα Q hQ' => ?_, fun Q hQ' Z hZ' => ?_, ?_⟩
  ·
    have h1 : subspace (U ⊔ R) (U.map (MulAut.conj l).toMonoidHom) = subspace (U ⊔ R) U := by
      rw [← map_linAut_rho_subspace le_sup_left ⟨l, hl⟩]
      exact hMU _ ⟨⟨l, hl⟩, rfl⟩
    rw [subspace_inj (map_conj_le_of_le le_sup_left ⟨l, hl⟩) le_sup_left] at h1
    exact map_conj_eq_self_iff.1 h1
  ·
    rw [hinj.ncard_image, finrank_subspace le_sup_left hUcard] at hΔcard
    exact hΔcard
  ·
    refine hnz _ ⟨Q, hQΔ, rfl⟩ (Additive.ofMul ⟨v, hleV Q hQΔ hv⟩) hv (fun h0 => hv1 ?_) hvU
    exact congrArg Subtype.val (toMul_eq_one.2 h0)
  ·
    obtain ⟨_, ⟨⟨Q, hQΔ, rfl⟩, hvQ⟩, huniq⟩ := hpart (Additive.ofMul ⟨v, hvV⟩) hvU
    refine ⟨Q, ⟨hQΔ, hvQ⟩, fun Z hZ => ?_⟩
    exact (subspace_inj (hleV Z hZ.1) (hleV Q hQΔ)).1 (huniq _ ⟨⟨Z, hZ.1, rfl⟩, hZ.2⟩)
  ·
    obtain ⟨⟨Z, hZΔ, hZ⟩, hZR⟩ :=
      hHΔ (linAut α) ⟨α, hα, rfl⟩ _ ⟨⟨Q, hQ'.1, rfl⟩, hRne Q hQ'.1 hQ'.2⟩
    refine ⟨Z, ⟨hZΔ, fun hZR' => hZR ?_⟩, ((map_linAut_subspace_eq_iff α Q Z).1 hZ.symm)⟩
    rw [← hZ, show Z = R from hZR']
    rfl
  ·
    obtain ⟨_, ⟨⟨α, hα, rfl⟩, hαQ⟩, hαuniq⟩ :=
      hHreg _ ⟨⟨Q, hQ'.1, rfl⟩, hRne Q hQ'.1 hQ'.2⟩ _ ⟨⟨Z, hZ'.1, rfl⟩, hRne Z hZ'.1 hZ'.2⟩
    refine ⟨⟨α, hα⟩, (map_linAut_subspace_eq_iff α Q Z).1 hαQ, fun β hβ => ?_⟩
    exact Subtype.ext (linAut_injective
      (hαuniq _ ⟨⟨β, β.2, rfl⟩,
        (map_linAut_subspace_eq_iff (V := U ⊔ R) (β : MulAut ↥(U ⊔ R)) Q Z).2 hβ⟩))
  ·
    rintro ⟨Q₁, hQ₁⟩ ⟨Q₂, hQ₂⟩ ⟨Z₁, hZ₁⟩ ⟨Z₂, hZ₂⟩ hQ12 hZ12
    have hQ12' : subspace (U ⊔ R) Q₁ ≠ subspace (U ⊔ R) Q₂ := fun h12 =>
      hQ12 (Subtype.ext (hinj hQ₁ hQ₂ h12))
    have hZ12' : subspace (U ⊔ R) Z₁ ≠ subspace (U ⊔ R) Z₂ := fun h12 =>
      hZ12 (Subtype.ext (hinj hZ₁ hZ₂ h12))
    obtain ⟨_, ⟨l, rfl⟩, h1, h2⟩ := h2tr _ ⟨Q₁, hQ₁, rfl⟩ _ ⟨Q₂, hQ₂, rfl⟩ _ ⟨Z₁, hZ₁, rfl⟩ _
      ⟨Z₂, hZ₂, rfl⟩ hQ12' hZ12'
    refine ⟨gmsRootConjugateAction (U ⊔ R) R l, ⟨l, rfl⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [gmsRootConjugateAction_apply]
      rw [MonoidHom.comp_apply, map_linAut_rho_subspace (hleV _ hQ₁) l] at h1
      exact (subspace_inj (map_conj_le_of_le (hleV _ hQ₁) l) (hleV _ hZ₁)).1 h1
    · rw [gmsRootConjugateAction_apply]
      rw [MonoidHom.comp_apply, map_linAut_rho_subspace (hleV _ hQ₂) l] at h2
      exact (subspace_inj (map_conj_le_of_le (hleV _ hQ₂) l) (hleV _ hZ₂)).1 h2

end Native

end GMSPartition

open GMSPartition

variable {D : Type*} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_partition_and_two_transitivity [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    normalizer ((U ⊔ R : Subgroup D) : Set D) ≤ normalizer (U : Set D) ∧
    (gmsRootConjugates (U ⊔ R) R).ncard = 2 ^ n ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R, ∀ v ∈ Q, v ≠ 1 → v ∉ U) ∧
    (∀ v ∈ U ⊔ R, v ∉ U → ∃! Q, Q ∈ gmsRootConjugates (U ⊔ R) R ∧ v ∈ Q) ∧
    (∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (U ⊔ R) R, Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, σ Q₁ = Z₁ ∧ σ Q₂ = Z₂) ∧
    gmsSingerImage X U (U ⊔ R) ≤ gmsRootStabilizer (U ⊔ R) R ∧
    ((gmsSingerImage X U (U ⊔ R)).subgroupOf (gmsRootStabilizer (U ⊔ R) R)).Normal ∧
    (∀ α ∈ gmsSingerImage X U (U ⊔ R), ∀ Q ∈ gmsRootConjugates (U ⊔ R) R \ {R},
      ∃ Z ∈ gmsRootConjugates (U ⊔ R) R \ {R},
        α • Q.subgroupOf (U ⊔ R) = Z.subgroupOf (U ⊔ R)) ∧
    (∀ Q ∈ gmsRootConjugates (U ⊔ R) R \ {R}, ∀ Z ∈ gmsRootConjugates (U ⊔ R) R \ {R},
      ∃! α : gmsSingerImage X U (U ⊔ R),
        (α : MulAut ↥(U ⊔ R)) • Q.subgroupOf (U ⊔ R) = Z.subgroupOf (U ⊔ R)) ∧
    (U ⊔ R).normalizerMonoidHom.ker = (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    (gmsRootConjugateAction (U ⊔ R) R).ker = gmsRootKernel (U ⊔ R) R ∧
    (∃ π' : (U ⊔ R).normalizerMonoidHom.range →* Equiv.Perm (gmsRootConjugates (U ⊔ R) R),
      (∀ l, π' ((U ⊔ R).normalizerMonoidHom.rangeRestrict l) =
        gmsRootConjugateAction (U ⊔ R) R l) ∧
      π'.ker = (gmsRootKernel (U ⊔ R) R).map (U ⊔ R).normalizerMonoidHom.rangeRestrict) ∧
    Nonempty (↥((gmsRootKernel (U ⊔ R) R).map (U ⊔ R).normalizerMonoidHom) ≃*
      ↥(gmsRootKernel (U ⊔ R) R) ⧸
        ((U ⊔ R).normalizerMonoidHom.comp (gmsRootKernel (U ⊔ R) R).subtype).ker) ∧
    ((U ⊔ R).normalizerMonoidHom.comp (gmsRootKernel (U ⊔ R) R).subtype).ker =
      ((centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
        (normalizer ((U ⊔ R : Subgroup D) : Set D))).subgroupOf (gmsRootKernel (U ⊔ R) R) ∧
    (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ≤ gmsRootKernel (U ⊔ R) R ∧
    (∀ g (hg : g ∈ X ⊓ normalizer (U : Set D)),
      gmsRootConjugateAction (U ⊔ R) R ⟨g, gms_NXU_le_L h hg⟩ = 1 ↔
        g ∈ X ⊓ centralizer (U : Set D)) ∧
    (∀ g (hg : g ∈ X ⊓ normalizer (U : Set D)),
      (U ⊔ R).normalizerMonoidHom ⟨g, gms_NXU_le_L h hg⟩ = 1 ↔
        g ∈ X ⊓ centralizer (U : Set D)) := by
  obtain ⟨-, -, -, m, -, -, hQ, -, -, hρker, -, -, -, -, hHle, hHn, -, -, -, -, -, hNXker,
    hπker, hCK, hπ', hiso, hkerK⟩ := gms_normal_root_actual_linear_family_and_kernels h
  obtain ⟨hLU, hΔcard, hnz, hpart, hHΔ, hHreg, h2tr⟩ := gms_native_partition h h3
  refine ⟨hLU, hΔcard, hnz, hpart, h2tr, hHle, hHn, hHΔ, hHreg, hρker, hπker, hπ', hiso, hkerK,
    hCK, fun g hg => ?_, hNXker⟩
  rw [← hNXker g hg]
  constructor
  · intro hπ1
    obtain ⟨Q, hQΔ, hQR⟩ :=
      Set.exists_ne_of_one_lt_ncard (s := gmsRootConjugates (U ⊔ R) R) (by omega) R
    have hQ' : Q ∈ gmsRootConjugates (U ⊔ R) R \ {R} := ⟨hQΔ, hQR⟩
    have hgH : (U ⊔ R).normalizerMonoidHom ⟨g, gms_NXU_le_L h hg⟩ ∈
        gmsSingerImage X U (U ⊔ R) :=
      ⟨⟨g, gms_NXU_le_L h hg⟩, mem_subgroupOf.2 hg, rfl⟩
    have hfix : (U ⊔ R).normalizerMonoidHom ⟨g, gms_NXU_le_L h hg⟩ • Q.subgroupOf (U ⊔ R) =
        Q.subgroupOf (U ⊔ R) := by
      rw [gms_rho_smul_eq_iff (hQ Q hQΔ).1, ← map_conj_eq_self_iff]
      exact congrArg Subtype.val (Equiv.ext_iff.1 hπ1 ⟨Q, hQΔ⟩)
    obtain ⟨α, -, huniq⟩ := hHreg Q hQ' Q hQ'
    exact congrArg Subtype.val ((huniq ⟨_, hgH⟩ hfix).trans (huniq 1 (one_smul _ _)).symm)
  · intro hρ1
    have h1 : (⟨g, gms_NXU_le_L h hg⟩ : normalizer ((U ⊔ R : Subgroup D) : Set D)) ∈
        (U ⊔ R).normalizerMonoidHom.ker := hρ1
    rw [hρker] at h1
    have h2 := hCK h1
    rw [← hπker] at h2
    exact h2

end CFSG.LocalAnalysis.SteinbergBX
