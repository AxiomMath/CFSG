module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.Quasithin.Background.F8Basic

public section

namespace CFSG.Quasithin.H13.A6.G52

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement IsMulCommutative

variable {X : Type} [Group X] {A B Y : Subgroup X}

theorem isChiefFactorUnder_two (hAB : A ≤ normalizer (B : Set X))
    (hsq : ∀ a ∈ A, a * a ∈ B) (hcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' * a⁻¹ * a'⁻¹ ∈ B)
    (hYA : Y ≤ normalizer (A : Set X)) (hYB : Y ≤ normalizer (B : Set X)) (hlt : B < A)
    (hirr : ∀ W : Subgroup X, B ≤ W → W ≤ A → Y ≤ normalizer (W : Set X) → W = B ∨ W = A) :
    IsChiefFactorUnder 2 Y A B :=
  ⟨hlt, hYA, hYB, fun x hx y hy => (mem_normalizer_iff.mp (hAB hx) y).mp hy,
    fun x hx y hy => hcomm x hx y hy, fun x hx => by rw [pow_two]; exact hsq x hx, hirr⟩

theorem isIrreducible_of_forall_submodule {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [Nontrivial V] (τ : Representation k G V)
    (h : ∀ U : Submodule k V, (∀ g, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Representation.IsIrreducible τ := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
  · have := congrArg Subrepresentation.toSubmodule hbt
    exact bot_ne_top this
  · rcases h P.toSubmodule (fun g v hv => P.apply_mem_toSubmodule g hv) with hP | hP
    · exact Or.inl (Subrepresentation.toSubmodule_injective hP)
    · exact Or.inr (Subrepresentation.toSubmodule_injective hP)

section Rep

variable [(B.subgroupOf A).Normal] [IsElementaryAbelian 2 (↥A ⧸ B.subgroupOf A)]

noncomputable def yRep (hch : IsChiefFactorUnder 2 Y A B) :
    Representation (ZMod 2) ↥Y (Additive (↥A ⧸ B.subgroupOf A)) :=
  (Units.coeHom _).comp (chiefRep (p := 2) hch.2.1 hch.2.2.1)

theorem yRep_apply_mk (hch : IsChiefFactorUnder 2 Y A B) (y : ↥Y) (a : ↥A) :
    yRep hch y (Additive.ofMul (a : ↥A ⧸ B.subgroupOf A)) =
      Additive.ofMul ((chiefConj hch.2.1 y a : ↥A) : ↥A ⧸ B.subgroupOf A) :=
  chiefRep_apply_mk (p := 2) hch.2.1 hch.2.2.1 y a

theorem chiefRep_eq_one_of (hch : IsChiefFactorUnder 2 Y A B) (y : ↥Y)
    (h : ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) :
    chiefRep (p := 2) hch.2.1 hch.2.2.1 y = 1 := by
  rw [chiefRep_eq_one_iff]
  intro w hw
  have h2 := B.inv_mem (h w hw)
  have e : ((y : X) * w * (y : X)⁻¹ * w⁻¹)⁻¹ = ⁅w, (y : X)⁆ := by
    rw [commutatorElement_def]
    group
  rwa [e] at h2

theorem nontrivial_sec (hlt : B < A) : Nontrivial (Additive (↥A ⧸ B.subgroupOf A)) := by
  obtain ⟨a, haA, haB⟩ := Set.exists_of_ssubset hlt
  refine ⟨⟨0, Additive.ofMul ((⟨a, haA⟩ : ↥A) : ↥A ⧸ B.subgroupOf A), fun h => haB ?_⟩⟩
  have h1 : ((⟨a, haA⟩ : ↥A) : ↥A ⧸ B.subgroupOf A) = 1 := (congrArg Additive.toMul h).symm
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

noncomputable def sRepGL (hch : IsChiefFactorUnder 2 Y A B) (ρ : ↥Y →* Equiv.Perm (Fin 6))
    (hs : Function.Surjective ρ)
    (hk : ∀ y : ↥Y, ρ y = 1 → ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) :
    Equiv.Perm (Fin 6) →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (↥A ⧸ B.subgroupOf A)) :=
  MonoidHom.liftOfRightInverse ρ (Function.surjInv hs) (Function.rightInverse_surjInv hs)
    ⟨chiefRep (p := 2) hch.2.1 hch.2.2.1, fun y hy => chiefRep_eq_one_of hch y (hk y hy)⟩

noncomputable def sRep (hch : IsChiefFactorUnder 2 Y A B) (ρ : ↥Y →* Equiv.Perm (Fin 6))
    (hs : Function.Surjective ρ)
    (hk : ∀ y : ↥Y, ρ y = 1 → ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) :
    Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive (↥A ⧸ B.subgroupOf A)) :=
  (Units.coeHom _).comp (sRepGL hch ρ hs hk)

theorem sRep_apply (hch : IsChiefFactorUnder 2 Y A B) (ρ : ↥Y →* Equiv.Perm (Fin 6))
    (hs : Function.Surjective ρ)
    (hk : ∀ y : ↥Y, ρ y = 1 → ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) (y : ↥Y) :
    sRep hch ρ hs hk (ρ y) = yRep hch y := by
  show Units.coeHom _ (sRepGL hch ρ hs hk (ρ y)) =
    Units.coeHom _ (chiefRep (p := 2) hch.2.1 hch.2.2.1 y)
  rw [sRepGL, MonoidHom.liftOfRightInverse_comp_apply]

theorem sRep_isIrreducible (hch : IsChiefFactorUnder 2 Y A B) (ρ : ↥Y →* Equiv.Perm (Fin 6))
    (hs : Function.Surjective ρ)
    (hk : ∀ y : ↥Y, ρ y = 1 → ∀ a ∈ A, (y : X) * a * (y : X)⁻¹ * a⁻¹ ∈ B) :
    Representation.IsIrreducible (sRep hch ρ hs hk) := by
  have := nontrivial_sec hch.1
  refine isIrreducible_of_forall_submodule _ fun U hU => ?_
  exact chiefRep_irreducible hch U fun n v hv => by
    have h := hU (ρ n) v hv
    rw [sRep_apply] at h
    exact h

omit [(B.subgroupOf A).Normal] [IsElementaryAbelian 2 (↥A ⧸ B.subgroupOf A)] in
theorem relIndex_eq_natCard :
    B.relIndex A = Nat.card (Additive (↥A ⧸ B.subgroupOf A)) :=
  (Nat.card_congr (Additive.toMul : Additive (↥A ⧸ B.subgroupOf A) ≃ _)).symm

noncomputable def subm (S : Subgroup (↥A ⧸ B.subgroupOf A)) :
    Submodule (ZMod 2) (Additive (↥A ⧸ B.subgroupOf A)) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup S)

theorem natCard_subm (S : Subgroup (↥A ⧸ B.subgroupOf A)) : Nat.card (subm S) = Nat.card S :=
  Nat.card_congr ((Additive.toMul : Additive (↥A ⧸ B.subgroupOf A) ≃ _).subtypeEquiv
    fun _ => Iff.rfl)

variable (A B) in
@[expose] def imgSub (W : Subgroup X) : Subgroup (↥A ⧸ B.subgroupOf A) :=
  (W.subgroupOf A).map (QuotientGroup.mk' (B.subgroupOf A))

omit [IsElementaryAbelian 2 (↥A ⧸ B.subgroupOf A)] in
theorem natCard_imgSub {W : Subgroup X} (hWA : W ≤ A) :
    Nat.card (imgSub A B W) = B.relIndex W := by
  let g : ↥(W.subgroupOf A) →* (↥A ⧸ B.subgroupOf A) :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp (W.subgroupOf A).subtype
  have hrange : g.range = imgSub A B W := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : g.ker = (B.subgroupOf A).subgroupOf (W.subgroupOf A) := by
    ext w
    simp [g, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have h := Subgroup.index_ker g
  rw [hker, hrange] at h
  rw [← h, ← Subgroup.relIndex_subgroupOf hWA]
  rfl

theorem yRep_mem_subm_imgSub (hch : IsChiefFactorUnder 2 Y A B) {W : Subgroup X}
    (y : ↥Y) (hy : (y : X) ∈ normalizer (W : Set X))
    {v : Additive (↥A ⧸ B.subgroupOf A)} (hv : v ∈ subm (imgSub A B W)) :
    yRep hch y v ∈ subm (imgSub A B W) := by
  obtain ⟨w, hw, hwv⟩ := hv
  have hv' : v = Additive.ofMul (w : ↥A ⧸ B.subgroupOf A) := congrArg Additive.ofMul hwv.symm
  rw [hv', yRep_apply_mk]
  refine ⟨chiefConj hch.2.1 y w, ?_, rfl⟩
  have h1 := chiefConj_apply_coe hch.2.1 y w
  have h2 : ((chiefConj hch.2.1 y w : ↥A) : X) ∈ W := by
    rw [h1]
    exact (mem_normalizer_iff.mp hy w).mp hw
  exact h2

theorem fix_zpow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V)
    (h : (g : Module.End (ZMod 2) V) v = v) (k : ℤ) :
    ((g ^ k : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) v = v := by
  have hinv : ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : Module.End (ZMod 2) V) v = v := by
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, Module.End.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, Module.End.mul_apply, hinv, ih]

theorem fix_iff_comm (hch : IsChiefFactorUnder 2 Y A B) (hAB : A ≤ normalizer (B : Set X))
    (u : ↥Y) (a : ↥A) :
    yRep hch u (Additive.ofMul (a : ↥A ⧸ B.subgroupOf A)) =
        Additive.ofMul (a : ↥A ⧸ B.subgroupOf A) ↔
      (a : X) * (u : X) * (a : X)⁻¹ * (u : X)⁻¹ ∈ B := by
  rw [yRep_apply_mk]
  have h1 : Additive.ofMul ((chiefConj hch.2.1 u a : ↥A) : ↥A ⧸ B.subgroupOf A) =
      Additive.ofMul (a : ↥A ⧸ B.subgroupOf A) ↔
      (u : X) * (a : X)⁻¹ * (u : X)⁻¹ * (a : X) ∈ B := by
    rw [Equiv.apply_eq_iff_eq, QuotientGroup.eq, mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv, chiefConj_apply_coe]
    have e : ((u : X) * (a : X) * (u : X)⁻¹)⁻¹ * (a : X) =
        (u : X) * (a : X)⁻¹ * (u : X)⁻¹ * (a : X) := by group
    rw [e]
  rw [h1]
  have hmem := (mem_normalizer_iff.mp (hAB a.2) ((u : X) * (a : X)⁻¹ * (u : X)⁻¹ * (a : X)))
  rw [hmem]
  have e : (a : X) * ((u : X) * (a : X)⁻¹ * (u : X)⁻¹ * (a : X)) * (a : X)⁻¹ =
      (a : X) * (u : X) * (a : X)⁻¹ * (u : X)⁻¹ := by group
  rw [e]

theorem mem_centralizerMod_iff (hch : IsChiefFactorUnder 2 Y A B)
    (hAB : A ≤ normalizer (B : Set X)) (y : ↥Y) (a : ↥A) :
    (a : X) ∈ centralizerMod B A (zpowers (y : X)) ↔
      yRep hch y (Additive.ofMul (a : ↥A ⧸ B.subgroupOf A)) =
        Additive.ofMul (a : ↥A ⧸ B.subgroupOf A) := by
  rw [mem_centralizerMod]
  constructor
  · rintro ⟨-, -, h⟩
    exact (fix_iff_comm hch hAB y a).mpr (h (y : X) (mem_zpowers _))
  · intro hfix
    refine ⟨a.2, hAB a.2, fun u hu => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have hY : ((y ^ k : ↥Y) : X) = (y : X) ^ k := by simp
    rw [← hY]
    refine (fix_iff_comm hch hAB (y ^ k) a).mp ?_
    have h1 : yRep hch (y ^ k) =
        ((chiefRep (p := 2) hch.2.1 hch.2.2.1 y ^ k : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (↥A ⧸ B.subgroupOf A))) : Module.End (ZMod 2)
          (Additive (↥A ⧸ B.subgroupOf A))) := by
      show Units.coeHom _ (chiefRep (p := 2) hch.2.1 hch.2.2.1 (y ^ k)) = _
      rw [map_zpow]
      rfl
    rw [h1]
    exact fix_zpow _ _ hfix k

theorem relIndex_centralizerMod (hch : IsChiefFactorUnder 2 Y A B)
    (hAB : A ≤ normalizer (B : Set X)) (y : ↥Y) :
    (centralizerMod B A (zpowers (y : X))).relIndex A =
      Nat.card (LinearMap.range (yRep hch y - 1)) := by
  let f : Additive (↥A ⧸ B.subgroupOf A) →ₗ[ZMod 2] Additive (↥A ⧸ B.subgroupOf A) :=
    yRep hch y - 1
  let δ : (↥A ⧸ B.subgroupOf A) →* (↥A ⧸ B.subgroupOf A) :=
    MonoidHom.toAdditive.symm f.toAddMonoidHom
  have hδ : ∀ q, δ q = Additive.toMul (f (Additive.ofMul q)) := fun q => rfl
  have hC : (centralizerMod B A (zpowers (y : X))).subgroupOf A =
      δ.ker.comap (QuotientGroup.mk' (B.subgroupOf A)) := by
    ext a
    rw [mem_subgroupOf, mem_comap, MonoidHom.mem_ker, mem_centralizerMod_iff hch hAB y a, hδ,
      toMul_eq_one]
    show _ ↔ yRep hch y (Additive.ofMul (a : ↥A ⧸ B.subgroupOf A)) -
      Additive.ofMul (a : ↥A ⧸ B.subgroupOf A) = 0
    rw [sub_eq_zero]
  show ((centralizerMod B A (zpowers (y : X))).subgroupOf A).index = _
  rw [hC, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.index_ker]
  refine Nat.card_congr (Additive.ofMul.subtypeEquiv fun q => ?_)
  rw [MonoidHom.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨q₀, rfl⟩
    exact ⟨Additive.ofMul q₀, rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨Additive.toMul v, by rw [hδ]; exact congrArg Additive.toMul hv⟩

end Rep

end CFSG.Quasithin.H13.A6.G52
