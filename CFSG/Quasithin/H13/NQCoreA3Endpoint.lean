module

public import CFSG.Quasithin.H13.NQCoreA3Actor
public import CFSG.Quasithin.SteinbergBNA7ThreeRankClosure

public section

namespace CFSG.Quasithin.H13.NQCore

open Module Subgroup Equiv CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight)
open CFSG.LocalAnalysis.SteinbergBV (IsBinaryTransvection)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transvection

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem isBinaryTransvection_of_mul_self_eq_one {g : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (hg : g * g = 1)
    (hrank : finrank (ZMod 2) (LinearMap.range ((g : W →ₗ[ZMod 2] W) - 1)) = 1) :
    IsBinaryTransvection g := by
  classical
  set φ : W →ₗ[ZMod 2] W := (g : W →ₗ[ZMod 2] W) - 1 with hφ
  obtain ⟨⟨u, hu⟩, hu0, hspan⟩ := finrank_eq_one_iff'.mp hrank
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hrange : ∀ x, φ x ∈ Submodule.span (ZMod 2) {u} := by
    intro x
    obtain ⟨c, hc⟩ := hspan ⟨φ x, LinearMap.mem_range_self φ x⟩
    have h1 : c • u = φ x := congrArg Subtype.val hc
    rw [← h1]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self u)
  set e := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) W u hu0' with he
  set f : Module.Dual (ZMod 2) W := e.symm.toLinearMap.comp (φ.codRestrict _ hrange) with hf
  have hφf : ∀ x, φ x = f x • u := by
    intro x
    have h1 : e (f x) = ⟨φ x, hrange x⟩ := by
      rw [hf, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rfl
    have h2 := congrArg Subtype.val h1
    rw [he, LinearEquiv.toSpanNonzeroSingleton_apply] at h2
    exact h2.symm
  have h2 : ∀ y : W, y + y = 0 := fun y => by
    rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hgg : ∀ x, (g : W →ₗ[ZMod 2] W) ((g : W →ₗ[ZMod 2] W) x) = x := fun x => by
    rw [← Module.End.mul_apply, ← Units.val_mul, hg, Units.val_one, Module.End.one_apply]
  have hφφ : ∀ x, φ (φ x) = 0 := by
    intro x
    simp only [hφ, LinearMap.sub_apply, Module.End.one_apply, map_sub, hgg]
    calc x - (g : W →ₗ[ZMod 2] W) x - ((g : W →ₗ[ZMod 2] W) x - x) =
        (x + x) - ((g : W →ₗ[ZMod 2] W) x + (g : W →ₗ[ZMod 2] W) x) := by abel
      _ = 0 := by rw [h2, h2, sub_zero]
  obtain ⟨x₀, hx₀⟩ := LinearMap.mem_range.mp hu
  have hfx₀ : f x₀ ≠ 0 := fun h => hu0' (by rw [← hx₀, hφf, h, zero_smul])
  refine ⟨u, f, hu0', fun h => hfx₀ (by rw [h]; rfl), ?_, ?_⟩
  · have h3 := hφφ x₀
    rw [hx₀, hφf] at h3
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h hu0'
  · ext x
    have h4 := hφf x
    simp only [hφ, LinearMap.sub_apply, Module.End.one_apply] at h4
    simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
    rw [← h4]
    abel

theorem isBinaryTransvection_conj {n : LinearMap.GeneralLinearGroup (ZMod 2) W}
    (hn : IsBinaryTransvection n) (a : LinearMap.GeneralLinearGroup (ZMod 2) W) :
    IsBinaryTransvection (a * n * a⁻¹) := by
  obtain ⟨u, f, hu, hf, hfu, hn⟩ := hn
  refine ⟨(a : Module.End (ZMod 2) W) u,
    f.comp ((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) : Module.End (ZMod 2) W),
    fun h => hu ?_, fun h => hf ?_, ?_, ?_⟩
  · have h1 := congrArg (((a⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) W) :
      Module.End (ZMod 2) W)) h
    rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, map_zero] at h1
  · ext x
    have h1 := LinearMap.congr_fun h ((a : Module.End (ZMod 2) W) x)
    rwa [LinearMap.comp_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply] at h1
  · rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply, hfu]
  · rw [Units.val_mul, Units.val_mul, hn]
    exact CFSG.LocalAnalysis.SteinbergBV.BinaryTransvection.conj_id_add_smulRight a u f

end Transvection

theorem isSylowOf_map_range {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q] {p : ℕ}
    [Fact p.Prime] (φ : P →* Q) {S : Subgroup P} (hS : IsPGroup p S) (hSi : ¬ p ∣ S.index) :
    ABGLocalTools.IsSylowOf p (S.map φ) φ.range := by
  refine ABGLocalTools.isSylowOf_iff.mpr ⟨map_le_range _ _, hS.map φ, fun hd => hSi ?_⟩
  rw [MonoidHom.range_eq_map, relIndex_map_map, top_sup_eq, relIndex_top_right] at hd
  exact hd.trans (index_dvd_of_le le_sup_left)

variable {G : Type} [Group G] [Finite G] {X T K A U V : Subgroup G}

theorem actual_A3_reduced_actor_S3_or_S7_normalizer_endpoint (hX : CharTwo X)
    (hT : IsSylowTwoOf T X) (hKX : K ≤ X) (hK : IsShort2 K)
    (hK3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) (hTK : T ≤ normalizer (K : Set G))
    (hAT : A ≤ T) (hAn : T ≤ normalizer (A : Set G)) (hU : U = blockQ K) (hAU : ⁅A, U⁆ ≠ ⊥)
    (hE2 : Nat.card ↥(A ⊓ centralizer (U : Set G)) = 2)
    (h3 : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9)
    (hV : V = conjJoin X U) :
    IsElemAbelian 2 V ∧
    (∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (ι : V ≃* Multiplicative M)
      (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M), ∀ (x : X) (v w : V),
        (w : G) = x * v * x⁻¹ →
          (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) ∧
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod 2) M] (ι : V ≃* Multiplicative M)
      (ρ : X →* LinearMap.GeneralLinearGroup (ZMod 2) M),
      (∀ (x : X) (v w : V), (w : G) = x * v * x⁻¹ →
        (ρ x : M →ₗ[ZMod 2] M) (Multiplicative.toAdd (ι v)) = Multiplicative.toAdd (ι w)) →
      ∃ τ : ρ.range,
        (A.subgroupOf X).map ρ = zpowers (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) ∧
        Nat.card ((A.subgroupOf X).map ρ) = 2 ∧
        (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ (T.subgroupOf X).map ρ ⊓
          centralizer (((T.subgroupOf X).map ρ :
            Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) : Set _) ∧
        finrank (ZMod 2) (LinearMap.range
          (((τ : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) - 1)) = 1 ∧
        (∀ b ∈ (K.subgroupOf X).map ρ, (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * b *
          (τ : LinearMap.GeneralLinearGroup (ZMod 2) M)⁻¹ = b⁻¹) ∧
        ∀ (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) M)) (C : Submodule (ZMod 2) M),
          N = Subgroup.closure {x | ∃ h ∈ ρ.range,
            x = h * (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * h⁻¹} →
          (∀ v, v ∈ C ↔ ∀ n ∈ N, (n : M →ₗ[ZMod 2] M) v = v) →
          ∃ ρW : ρ.range →* LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C),
            (∀ (h : ρ.range) (v : M), (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) (C.mkQ v) =
              C.mkQ (((h : LinearMap.GeneralLinearGroup (ZMod 2) M) : M →ₗ[ZMod 2] M) v)) ∧
            Function.Injective ρW ∧
            (∀ W : Submodule (ZMod 2) (M ⧸ C), (∀ h : ρ.range, ∀ w ∈ W,
              (ρW h : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
            N = ρ.range ∧
            ((Nonempty (ρ.range ≃* Perm (Fin 3)) ∧ finrank (ZMod 2) (M ⧸ C) = 2) ∨
              (finrank (ZMod 2) (M ⧸ C) = 6 ∧ ∃ ψ : Perm (Fin 7) ≃* ρ.range,
                ∃ f : (M ⧸ C) ≃ₗ[ZMod 2] evenWeight (Fin 7), ∀ σ w i,
                  (f ((ρW (ψ σ) : (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) w) : Fin 7 → ZMod 2) i =
                    (f w : Fin 7 → ZMod 2) (σ⁻¹ i))) ∧
            normalizer (((T.subgroupOf X).map ρ : Subgroup (LinearMap.GeneralLinearGroup
              (ZMod 2) M)) : Set _) ⊓ ρ.range = (T.subgroupOf X).map ρ ∧
            normalizer ((T ⊔ ρ.ker.map X.subtype : Subgroup G) : Set G) ⊓ X =
              T ⊔ ρ.ker.map X.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hexist, hall⟩ :=
    SteinbergBN.actual_A3_three_rank_irreducible_transvection_normal_closure hX hT hKX hK hK3 hTK
      hAT hAn hU hAU hE2 h3 hV
  have hVea : IsElemAbelian 2 V := by
    obtain ⟨M, _, _, ι, -, -⟩ := hexist
    refine ⟨⟨⟨fun a b => ι.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)⟩⟩,
      fun v hv => ?_⟩
    have h1 : ι (⟨v, hv⟩ ^ 2) = ι 1 := by
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, ← two_smul (ZMod 2),
        show (2 : ZMod 2) = 0 from rfl, zero_smul]
    have h2 := congrArg Subtype.val (ι.injective h1)
    simpa using h2
  refine ⟨hVea, hexist, fun M _ _ ι ρ hρ => ?_⟩
  obtain ⟨τ, hτA, hτ2, hτZ, hτrank, hτinv, hB3, hTB, -, hrest, -⟩ := hall M ι ρ hρ
  refine ⟨τ, hτA, hτ2, hτZ, hτrank, hτinv, fun N C hN hC => ?_⟩
  obtain ⟨hNH, ρW, hρW, hinj, -, hirrH, hirrN, hBN, hτW, hbW⟩ := hrest N C hN hC
  refine ⟨ρW, hρW, hinj, hirrH, ?_⟩
  set B := (K.subgroupOf X).map ρ with hBdef
  set Ts := (T.subgroupOf X).map ρ with hTsdef
  have hFinM : Finite M := Finite.of_equiv V (ι.toEquiv.trans Multiplicative.toAdd)
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have : Finite (M ≃ₗ[ZMod 2] M) := SteinbergBS.RankTwoThree.finite_linearEquiv _
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) M) :=
    Finite.of_injective _ (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) M).injective
  have : Finite (M ⧸ C) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective C)
  have : FiniteDimensional (ZMod 2) (M ⧸ C) := Module.Finite.of_finite
  have : Finite ((M ⧸ C) ≃ₗ[ZMod 2] (M ⧸ C)) := SteinbergBS.RankTwoThree.finite_linearEquiv _
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C)) :=
    Finite.of_injective _ (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (M ⧸ C)).injective
  have hττ : τ * τ = 1 := by
    have h1 : (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ (A.subgroupOf X).map ρ :=
      hτA ▸ mem_zpowers _
    have h2 := Subgroup.orderOf_dvd_natCard _ h1
    rw [hτ2] at h2
    apply Subtype.ext
    rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have hτtr : IsBinaryTransvection (ρW τ) :=
    isBinaryTransvection_of_mul_self_eq_one (by rw [← map_mul, hττ, map_one]) hτW
  set S : Set (LinearMap.GeneralLinearGroup (ZMod 2) M) :=
    {x | ∃ h ∈ ρ.range, x = h * (τ : LinearMap.GeneralLinearGroup (ZMod 2) M) * h⁻¹} with hSdef
  have hSR : S ⊆ ρ.range := by
    rintro _ ⟨h, hh, rfl⟩
    exact mul_mem (mul_mem hh τ.2) (inv_mem hh)
  set S' : Set ↥ρ.range := {r | (r : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ S} with hS'def
  have hNR : N.subgroupOf ρ.range = closure S' := by
    have h1 : (closure S').map ρ.range.subtype = N := by
      rw [MonoidHom.map_closure, hN]
      congr 1
      ext x
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact hr
      · intro hx
        exact ⟨⟨x, hSR hx⟩, hx, rfl⟩
    rw [← h1]
    exact comap_map_eq_self_of_injective ρ.range.subtype_injective _
  have hNn : (N.subgroupOf ρ.range).Normal := by
    rw [hNR]
    refine ⟨fun n hn g => ?_⟩
    have hle : (closure S').map (MulAut.conj g).toMonoidHom ≤ closure S' := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨r, ⟨h, hh, hrh⟩, rfl⟩
      refine subset_closure ?_
      refine ⟨(g : LinearMap.GeneralLinearGroup (ZMod 2) M) * h, mul_mem g.2 hh, ?_⟩
      change ((g * r * g⁻¹ : ↥ρ.range) : LinearMap.GeneralLinearGroup (ZMod 2) M) = _
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrh]
      group
    exact hle ⟨n, hn, rfl⟩
  set σ : ↥X →* LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C) := ρW.comp ρ.rangeRestrict with hσ
  have hσrange : σ.range = ρW.range := by
    rw [hσ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
      ← MonoidHom.range_eq_map]
  set NA := (N.subgroupOf ρ.range).map ρW with hNA
  set TA := (T.subgroupOf X).map σ with hTA
  set e : ↥ρ.range ≃* ↥σ.range := (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr hσrange.symm) with he
  have he_coe : ∀ r : ↥ρ.range, ((e r : ↥σ.range) : LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C)) =
      ρW r := fun r => rfl
  have hBR : B ≤ ρ.range := map_le_range _ _
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    rcases B.bot_or_exists_ne_one with h | h
    · rw [h, Subgroup.card_bot] at hB3
      norm_num at hB3
    · exact h
  have hxo : orderOf x = 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hxB
    rw [hB3] at h1
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  set b' : ↥ρ.range := ⟨x, hBR hxB⟩ with hb'
  have hb'1 : b' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hzB : zpowers x = B := by
    refine Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hxB) ?_
    rw [Nat.card_zpowers, hxo, hB3]
  have hmemB : ∀ g : ↥ρ.range, g ∈ zpowers b' ↔
      (g : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ B := by
    intro g
    rw [← hzB, ← mem_map_iff_mem ρ.range.subtype_injective, MonoidHom.map_zpowers]
    rfl
  have hmemTA : ∀ r : ↥ρ.range, ρW r ∈ TA ↔ (r : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ Ts := by
    intro r
    rw [hTA, hσ, ← map_map, mem_map_iff_mem hinj]
    constructor
    · rintro ⟨y, hy, hyr⟩
      exact ⟨y, hy, congrArg Subtype.val hyr⟩
    · rintro ⟨y, hy, hyr⟩
      exact ⟨y, hy, Subtype.ext hyr⟩
  have hGX : ∀ E : Subgroup ↥X, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := hE
    have h := h3 (E.map X.subtype) (map_subtype_le E) (IsElementaryAbelian.map X.subtype)
    rwa [card_map_of_injective X.subtype_injective] at h
  have hrankb := (hbW b' hxB hb'1).2.2
  have hdim : 2 ≤ finrank (ZMod 2) (M ⧸ C) := hrankb.symm.trans_le (Submodule.finrank_le _)
  set ρA : (⊤ : Subgroup ↥X) →* ↥σ.range := σ.rangeRestrict.comp (⊤ : Subgroup ↥X).subtype
    with hρA
  have hρAsurj : Function.Surjective ρA := by
    rintro ⟨_, y, rfl⟩
    exact ⟨⟨y, mem_top y⟩, rfl⟩
  have hNAH : NA ≤ σ.range := by rw [hσrange]; exact map_le_range _ _
  have hNAn : (NA.subgroupOf σ.range).Normal := by
    have h1 : NA.subgroupOf σ.range = (N.subgroupOf ρ.range).map e.toMonoidHom := by
      ext y
      rw [mem_subgroupOf]
      constructor
      · rintro ⟨r, hr, hry⟩
        exact ⟨r, hr, Subtype.ext hry⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, hr, rfl⟩
    rw [h1]
    exact hNn.map _ e.surjective
  have hirrA : ∀ W : Submodule (ZMod 2) (M ⧸ C),
      (∀ n ∈ NA, ∀ u ∈ W, (n : Module.End (ZMod 2) (M ⧸ C)) u ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirrN W fun h hhN w hw => hW (ρW h) ⟨h, hhN, rfl⟩ w hw
  have hgenA : NA = closure {n | n ∈ NA ∧ IsBinaryTransvection n} := by
    refine le_antisymm ?_ ((closure_le _).mpr fun n hn => hn.1)
    have h1 : NA = closure (ρW '' S') := by rw [hNA, hNR, MonoidHom.map_closure]
    calc NA = closure (ρW '' S') := h1
      _ ≤ _ := closure_mono ?_
    rintro _ ⟨r, ⟨h, hh, hrh⟩, rfl⟩
    refine ⟨⟨r, by rw [hNR]; exact subset_closure ⟨h, hh, hrh⟩, rfl⟩, ?_⟩
    have hr : r = ⟨h, hh⟩ * τ * ⟨h, hh⟩⁻¹ := Subtype.ext hrh
    rw [hr, map_mul, map_mul, map_inv]
    exact isBinaryTransvection_conj hτtr _
  have hTAsyl : ABGLocalTools.IsSylowOf 2 TA σ.range :=
    isSylowOf_map_range σ (hT.2.1.of_equiv (subgroupOfEquivOfLe hT.1).symm) hT.2.2
  have hbN : ρW b' ∈ NA := ⟨b', show (b' : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ N from
    hBN hxB, rfl⟩
  have hb3 : orderOf (ρW b') = 3 := by
    rw [orderOf_injective ρW hinj b', ← Subgroup.orderOf_coe]
    exact hxo
  have hTb : TA ≤ normalizer (zpowers (ρW b') :
      Set (LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C))) := by
    rw [← MonoidHom.map_zpowers, hTA, hσ, ← map_map]
    refine (map_mono ?_).trans (le_normalizer_map ρW)
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_normalizer_iff]
    intro g
    rw [hmemB, hmemB]
    have hyT : ρ y ∈ Ts := ⟨y, hy, rfl⟩
    exact mem_normalizer_iff.mp (hTB hyT) (g : LinearMap.GeneralLinearGroup (ZMod 2) M)
  have hrankA : finrank (ZMod 2) (LinearMap.range
      (((ρW b' : LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C)) :
        (M ⧸ C) →ₗ[ZMod 2] (M ⧸ C)) - LinearMap.id)) = 2 := by
    rw [← Module.End.one_eq_id]
    exact hrankb
  obtain ⟨hHN, hcase, hnorm⟩ := three_rank_irreducible_normal_transvection_actor_forces_S3_or_S7
    hGX hdim ⊤ ρA hρAsurj hNAH hNAn hirrA hgenA hTAsyl hbN hb3 hTb hrankA
  have hNtop : N.subgroupOf ρ.range = ⊤ := by
    apply map_injective hinj
    rw [← hNA, ← hHN, hσrange, MonoidHom.range_eq_map]
  have hNeq : N = ρ.range := by
    refine le_antisymm hNH fun r hr => ?_
    have h1 : (⟨r, hr⟩ : ↥ρ.range) ∈ N.subgroupOf ρ.range := hNtop ▸ mem_top _
    exact h1
  have hnormTs :
      normalizer (Ts : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) ⊓ ρ.range = Ts := by
    refine le_antisymm (fun g hg => ?_) (le_inf le_normalizer (map_le_range _ _))
    obtain ⟨hgN, hgR⟩ := mem_inf.mp hg
    set g' : ↥ρ.range := ⟨g, hgR⟩ with hg'
    have hcj : ∀ r : ↥ρ.range, (r : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ Ts ↔
        ((g' * r * g'⁻¹ : ↥ρ.range) : LinearMap.GeneralLinearGroup (ZMod 2) M) ∈ Ts := fun r =>
      mem_normalizer_iff.mp hgN r
    have hgA : ρW g' ∈ normalizer (TA : Set (LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C))) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨r, hr⟩ : y ∈ ρW.range := hσrange ▸ (map_le_range _ _ hy)
        rw [← hr] at hy ⊢
        rw [hmemTA, hcj] at hy
        rw [← map_mul, ← map_inv, ← map_mul, hmemTA]
        exact hy
      · intro hy
        obtain ⟨r, hr⟩ : ρW g' * y * (ρW g')⁻¹ ∈ ρW.range :=
          hσrange ▸ (map_le_range _ _ hy)
        have hy' : y = ρW (g'⁻¹ * r * g') := by
          have h2 : y = (ρW g')⁻¹ * (ρW g' * y * (ρW g')⁻¹) * ρW g' := by group
          rw [h2, ← hr, map_mul, map_mul, map_inv]
        rw [hy'] at hy ⊢
        rw [hmemTA]
        rw [← map_mul, ← map_inv, ← map_mul, hmemTA] at hy
        rw [hcj]
        have h3 : g' * (g'⁻¹ * r * g') * g'⁻¹ = r := by group
        rw [h3]
        rwa [h3] at hy
    have h1 : ρW g' ∈ TA := by
      rw [← hnorm]
      exact mem_inf.mpr ⟨hgA, hσrange ▸ ⟨g', rfl⟩⟩
    exact (hmemTA g').mp h1
  refine ⟨hNeq, ?_, hnormTs, ?_⟩
  ·
    rcases hcase with ⟨⟨χ⟩, h2⟩ | ⟨h6, ψ, f, hf⟩
    · exact Or.inl ⟨⟨e.trans χ⟩, h2⟩
    · refine Or.inr ⟨h6, ψ.trans e.symm, f, fun σ' w i => ?_⟩
      have h1 : ρW ((ψ.trans e.symm) σ') = ((ψ σ' : ↥σ.range) :
          LinearMap.GeneralLinearGroup (ZMod 2) (M ⧸ C)) := by
        change ρW (e.symm (ψ σ')) = _
        rw [← he_coe, e.apply_symm_apply]
      rw [h1]
      exact hf σ' w i
  ·
    set K₀ := ρ.ker.map X.subtype with hK₀
    have hK₀X : K₀ ≤ X := map_subtype_le _
    have hTK₀ : T ≤ normalizer (K₀ : Set G) := by
      intro t ht
      rw [mem_normalizer_iff]
      intro k
      constructor
      · rintro ⟨k', hk', rfl⟩
        refine ⟨⟨t, hT.1 ht⟩ * k' * ⟨t, hT.1 ht⟩⁻¹, ?_, rfl⟩
        exact (MonoidHom.normal_ker ρ).conj_mem _ hk' _
      · intro hk
        obtain ⟨k', hk', hkk⟩ := hk
        refine ⟨⟨t, hT.1 ht⟩⁻¹ * k' * ⟨t, hT.1 ht⟩, ?_, ?_⟩
        · have := (MonoidHom.normal_ker ρ).conj_mem _ hk' ⟨t, hT.1 ht⟩⁻¹
          rwa [inv_inv] at this
        · change t⁻¹ * (k' : G) * t = k
          rw [show (k' : G) = t * k * t⁻¹ from hkk]
          group
    have hconjT : ∀ z : ↥X, (z : G) ∈ normalizer ((T ⊔ K₀ : Subgroup G) : Set G) →
        ∀ y ∈ Ts, ρ z * y * (ρ z)⁻¹ ∈ Ts := by
      rintro z hz _ ⟨t, ht, rfl⟩
      have h1 : (z * t * z⁻¹ : ↥X) ∈ (T ⊔ K₀).subgroupOf X := by
        rw [mem_subgroupOf]
        exact (mem_normalizer_iff.mp hz t).mp (mem_sup_left ht)
      rw [mem_subgroupOf] at h1
      have h2 : ((z * t * z⁻¹ : ↥X) : G) ∈ (T : Set G) * (K₀ : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right T K₀ hTK₀]
        exact h1
      obtain ⟨t₁, ht₁, k, ⟨k', hk', rfl⟩, htk⟩ := h2
      have h3 : z * t * z⁻¹ = ⟨t₁, hT.1 ht₁⟩ * k' := Subtype.ext htk.symm
      refine ⟨⟨t₁, hT.1 ht₁⟩, ht₁, ?_⟩
      rw [← map_mul, ← map_inv, ← map_mul, h3, map_mul, MonoidHom.mem_ker.mp hk', mul_one]
    refine le_antisymm (fun x hx => ?_) (le_inf le_normalizer (sup_le hT.1 hK₀X))
    obtain ⟨hxN, hxX⟩ := mem_inf.mp hx
    set x' : ↥X := ⟨x, hxX⟩ with hx'
    have hρx :
        ρ x' ∈ normalizer (Ts : Set (LinearMap.GeneralLinearGroup (ZMod 2) M)) ⊓ ρ.range := by
      refine mem_inf.mpr ⟨mem_normalizer_iff.mpr fun y => ⟨hconjT x' hxN y, fun hy => ?_⟩,
        ⟨x', rfl⟩⟩
      have hx'N : ((x'⁻¹ : ↥X) : G) ∈ normalizer ((T ⊔ K₀ : Subgroup G) : Set G) :=
        inv_mem hxN
      have h1 := hconjT x'⁻¹ hx'N _ hy
      rwa [map_inv, inv_inv, show (ρ x')⁻¹ * (ρ x' * y * (ρ x')⁻¹) * ρ x' = y by group] at h1
    rw [hnormTs] at hρx
    obtain ⟨t, ht, hte⟩ := hρx
    have hker : t⁻¹ * x' ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
    have h1 : x = (t : G) * ((t⁻¹ * x' : ↥X) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h1]
    exact mul_mem (mem_sup_left ht) (mem_sup_right ⟨_, hker, rfl⟩)

end CFSG.Quasithin.H13.NQCore
