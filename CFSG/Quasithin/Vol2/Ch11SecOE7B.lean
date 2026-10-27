module

public import CFSG.Quasithin.Vol2.Ch11SecE3LieL2Up
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.Quasithin.Background.E3ClosedTwo
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isE_sup_tauOf_of_sl2 {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {T A L₀ : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (eL : ↥L₀ ≃* SL(2, F)) (hF : Nat.card F = 2 ^ n) (hF4 : 4 ≤ Nat.card F)
    (hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G))
    (hL : IsSylowIn 2 (T ⊓ L₀) L₀) (hAC : ¬ A ≤ Subgroup.centralizer (L₀ : Set G)) :
    E1.IsE n ⊤ T A (L₀ ⊔ E1.tauOf ⊤ T A) := by
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  have hs : IsSimpleGroup ↥L₀ := eL.isSimpleGroup
  have hnab : ∃ x y : ↥L₀, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SecE3.sl2_nonabelian (K := F)
    exact ⟨eL.symm x, eL.symm y, fun h => hxy (eL.symm.injective (by
      rw [map_mul, map_mul, h]))⟩
  set τ := E1.tauOf ⊤ T A with hτdef
  have hτT : τ ≤ T := E1.tauOf_le _ _ _
  have hT2 : IsPGroup 2 T := hT.2.1
  have hAτ : A ≤ τ := le_sup_left.trans (E1.le_tauOf hT hAT hA)
  set K := L₀ ⊔ τ with hKdef
  have hLK : L₀ ≤ K := le_sup_left
  have hτK : τ ≤ K := le_sup_right
  have hAK : A ≤ K := hAτ.trans hτK
  have hKN : K ≤ Subgroup.normalizer (L₀ : Set G) := sup_le Subgroup.le_normalizer hτN
  have hSyl : IsSylowIn 2 (T ⊓ K) K := SecU1.Comp.isSylowIn_sup hT2 hτT hτN hL
  refine ⟨le_top, le_inf hτT hτK, hSyl, Or.inr ?_⟩
  set L := L₀.subgroupOf K with hLdef
  set C := (Subgroup.centralizer (L₀ : Set G)).subgroupOf K with hCdef
  have hLn : L.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLK).mpr hKN
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    have hg : (g : G)⁻¹ ∈ Subgroup.normalizer (L₀ : Set G) := hKN (K.inv_mem g.2)
    have hh' : (g : G)⁻¹ * h * (g : G)⁻¹⁻¹ ∈ L₀ := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have h1 := hc _ hh'
    rw [inv_inv] at h1
    push_cast
    calc h * ((g : G) * c * (g : G)⁻¹) = g * ((g : G)⁻¹ * h * g * c) * (g : G)⁻¹ := by group
      _ = g * (c * ((g : G)⁻¹ * h * g)) * (g : G)⁻¹ := by rw [h1]
      _ = g * c * (g : G)⁻¹ * h := by group
  have : IsSimpleGroup ↥L := (Subgroup.subgroupOfEquivOfLe hLK).isSimpleGroup
  have hnabL : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    let e := (Subgroup.subgroupOfEquivOfLe hLK).symm
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hZ := SecE3.center_eq_bot_of_simple hnab
  have hLC : L ⊓ C = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    rw [hLdef, Subgroup.mem_subgroupOf] at hxL
    rw [hCdef, Subgroup.mem_subgroupOf] at hxC
    have hc : (⟨x, hxL⟩ : ↥L₀) ∈ Subgroup.center ↥L₀ := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hc
    have h1 : (x : G) = 1 := by simpa using congrArg Subtype.val hc
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hcent : ∀ q : ↥K, (∀ l ∈ L, l * q = q * l) → q ∈ C := fun q h => by
    rw [hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (h ⟨y, hLK hy⟩ (by rw [hLdef, Subgroup.mem_subgroupOf]; exact hy))
  have hτ' : IsPGroup 2 ↥(τ.subgroupOf K) :=
    (hT2.to_le hτT).comap_of_injective K.subtype K.subtype_injective
  have hsup : L ⊔ τ.subgroupOf K = ⊤ := (Subgroup.codisjoint_subgroupOf_sup L₀ τ).eq_top
  have htwo : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ L := fun q => by
    have hq : q ∈ L ⊔ τ.subgroupOf K := hsup ▸ Subgroup.mem_top q
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
    obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
      show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]
  have hAS := SecU1.Comp.almostSimple_map hnabL hLC hcent htwo
  have hC2 : IsPGroup 2 C := SecU1.Comp.isPGroup_two hLC htwo
  set φ := QuotientGroup.mk' C with hφdef
  have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective C
  have hker : φ.ker = C := QuotientGroup.ker_mk' C
  have hO2 : CFSG.Open.pCore 2 (↥K ⧸ C) = ⊥ :=
    le_bot_iff.mp (E3.pCore_two_le_solvableRadical.trans hAS.solvableRadical_eq_bot.le)
  have hZC : E1.IsTwoClosed ((CFSG.Open.pCore 2 (↥K ⧸ C)).comap φ) := by
    rw [hO2, MonoidHom.comap_bot, hker]
    exact ⟨C, ⟨le_rfl, hC2, by rw [Subgroup.relIndex_self]; norm_num⟩,
      by rw [Subgroup.subgroupOf_self]; infer_instance⟩
  have hSylQ : IsSylowIn 2 ((T ⊓ K).subgroupOf K) ⊤ := by
    have h := (E1.isSylowIn_subgroupOf_iff (H := K) inf_le_right le_rfl).mpr hSyl
    rwa [Subgroup.subgroupOf_self] at h
  have hBS : A.subgroupOf K ≤ (T ⊓ K).subgroupOf K := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hAT hx, hAK hx⟩
  have hB : (A.subgroupOf K).map φ ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, hker] at h
    exact hAC fun a ha => h (show (⟨a, hAK ha⟩ : ↥K) ∈ A.subgroupOf K from ha)
  have hCS : C ≤ (T ⊓ K).subgroupOf K := by
    have h2 := B6.pCoreOf_two_le_of_isSylowTwoOf hSylQ
    rw [E1.pCoreOf_top_eq] at h2
    exact (CFSG.LieType.BorelTits.le_pCore 2 hCn hC2).trans h2
  have hres : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    E1.twoResidual_eq_perfectCore_of_surjective φ hφ hSylQ
      (fun M hSM hM => by rwa [hker, sup_eq_left.mpr (hCS.trans hSM)] at hM)
      (by rw [hAS.twoResidual_eq, hAS.perfectCore_eq])
  refine ⟨E1.eTwo_of_surjective φ hφ hZC hSylQ.2.1 hBS hres (hAS.eTwo hB), ?_⟩
  rw [← E1.card_barRad_eq_of_surjective φ hφ (E1.isSolvable_ker_of_isTwoClosed φ hZC)]
  unfold E1.barRad
  rw [Subgroup.card_map_of_injective (by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hAS.solvableRadical_eq_bot])]
  have hinj : Function.Injective (φ.comp L.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h : (x : ↥K) ∈ L ⊓ C := ⟨x.2, hx⟩
    rw [hLC, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hrange : (φ.comp L.subtype).range = L.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e₁ : ↥(L.map φ) ≃* SL(2, F) :=
    ((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans
      ((Subgroup.subgroupOfEquivOfLe hLK).trans eL)
  have hAφ : IsElemAbelian 2 ((A.subgroupOf K).map φ) := by
    refine E1.isElemAbelian_map' φ ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := E1.commute_of_isElemAbelian hA (Subgroup.mem_subgroupOf.mp x.2)
        (Subgroup.mem_subgroupOf.mp y.2)
      simpa using this
    · have := hA.2 _ (Subgroup.mem_subgroupOf.mp hx)
      exact Subtype.ext (by simpa using this)
  exact SecE3.card_le_of_isElemAbelian_sl2 hAS e₁ hF hAφ

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
