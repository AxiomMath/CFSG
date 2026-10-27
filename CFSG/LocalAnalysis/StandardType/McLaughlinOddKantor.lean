module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorComp
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def IsSLOrSpOn (D : Set (V ≃ₗ[ZMod p] V)) : Prop :=
  (∀ g : cenSpan D ≃ₗ[ZMod p] cenSpan D,
      (∃ h ∈ Subgroup.closure D, ∀ x : cenSpan D, h x = g x) ↔
        LinearMap.det (g : cenSpan D →ₗ[ZMod p] cenSpan D) = 1) ∨
    ∃ B : LinearMap.BilinForm (ZMod p) (cenSpan D), B.IsAlt ∧ B.Nondegenerate ∧
      ∀ g : cenSpan D ≃ₗ[ZMod p] cenSpan D,
        (∃ h ∈ Subgroup.closure D, ∀ x : cenSpan D, h x = g x) ↔ ∀ x y, B (g x) (g y) = B x y

structure KantorDecomp (S : Set (V ≃ₗ[ZMod p] V)) (𝒟 : Set (Set (V ≃ₗ[ZMod p] V))) : Prop where
  nonempty : ∀ D ∈ 𝒟, D.Nonempty
  subset : ∀ D ∈ 𝒟, D ⊆ S
  conn : ∀ D ∈ 𝒟, IsConnTr D
  cover : ∀ t ∈ S, ∃ D ∈ 𝒟, t ∈ D
  disjoint : ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, D ≠ D' → Disjoint D D'
  commute : ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, D ≠ D' → ∀ t ∈ D, ∀ s ∈ D', Commute t s
  closure_eq : Subgroup.closure S = ⨆ D : 𝒟, Subgroup.closure (D : Set (V ≃ₗ[ZMod p] V))
  isCompl : IsCompl (cenSpan S) (fixSub (Subgroup.closure S))
  indep : iSupIndep fun D : 𝒟 => cenSpan (D : Set (V ≃ₗ[ZMod p] V))
  iSup_eq : ⨆ D : 𝒟, cenSpan (D : Set (V ≃ₗ[ZMod p] V)) = cenSpan S
  fixSub_le : ∀ D ∈ 𝒟, fixSub (Subgroup.closure S) ≤ fixSub (Subgroup.closure D)
  cenSpan_le : ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, D ≠ D' → cenSpan D' ≤ fixSub (Subgroup.closure D)
  isCompl_comp : ∀ D ∈ 𝒟, IsCompl (cenSpan D) (fixSub (Subgroup.closure D))
  slsp : ∀ D ∈ 𝒟, IsSLOrSpOn D

variable {S : Set (V ≃ₗ[ZMod p] V)}

theorem iSup_cenSpan_trComps : ⨆ D : trComps S, cenSpan (D : Set (V ≃ₗ[ZMod p] V)) = cenSpan S := by
  refine le_antisymm (iSup_le fun D => Submodule.span_mono ?_) ?_
  · rintro v ⟨t, ht, f, h⟩
    exact ⟨t, subset_of_mem_trComps D.2 ht, f, h⟩
  · rw [cenSpan, Submodule.span_le]
    rintro v ⟨t, ht, f, h⟩
    exact le_iSup (fun D : trComps S => cenSpan (D : Set (V ≃ₗ[ZMod p] V)))
      ⟨trComp S t, mem_trComps ht⟩ (center_mem_cenSpan (mem_trComp_self ht) h)

theorem kantor_reduction (hp : p ≠ 2) [Module.Finite (ZMod p) V] (S : Set (V ≃ₗ[ZMod p] V))
    (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) (hT : NoNormalExpP (Subgroup.closure S)) :
    KantorDecomp S (trComps S) := by
  classical
  have hcomp : ∀ D ∈ trComps S, IsCompl (cenSpan D) (fixSub (Subgroup.closure D)) ∧
      IsSLOrSpOn D := fun D hD =>
    kantor_connected hp D (tr_of_mem_trComps hS hD) (isConnTr_of_mem_trComps hD)
      (noNormalExpP_of_mem_trComps hT hD)
  have hfixle : ∀ D ∈ trComps S, fixSub (Subgroup.closure S) ≤ fixSub (Subgroup.closure D) :=
    fun D hD x hx g hg => hx g (Subgroup.closure_mono (subset_of_mem_trComps hD) hg)
  have hcenle : ∀ D ∈ trComps S, ∀ D' ∈ trComps S, D ≠ D' →
      cenSpan D' ≤ fixSub (Subgroup.closure D) := fun D hD D' hD' hne =>
    cenSpan_le_fixSub_of_commute (tr_of_mem_trComps hS hD)
      fun t ht s hs => commute_of_mem_trComps hD hD' hne ht hs
  refine ⟨fun D hD => nonempty_of_mem_trComps hD, fun D hD => subset_of_mem_trComps hD,
    fun D hD => isConnTr_of_mem_trComps hD, fun t ht => exists_mem_trComps ht,
    fun D hD D' hD' hne => disjoint_of_mem_trComps hD hD' hne,
    fun D hD D' hD' hne t ht s hs => commute_of_mem_trComps hD hD' hne ht hs, ?_, ?_, ?_,
    iSup_cenSpan_trComps, hfixle, hcenle, fun D hD => (hcomp D hD).1, fun D hD => (hcomp D hD).2⟩
  · rw [← Subgroup.closure_iUnion]
    congr 1
    ext t
    simp only [Set.mem_iUnion]
    constructor
    · intro ht
      exact ⟨⟨trComp S t, mem_trComps ht⟩, mem_trComp_self ht⟩
    · rintro ⟨D, hD⟩
      exact subset_of_mem_trComps D.2 hD
  · set 𝒜 := (trComps_finite S).toFinset with h𝒜
    have h := isCompl_finset_trComps hp hS hT 𝒜 fun D hD => (trComps_finite S).mem_toFinset.mp hD
    have hsup : 𝒜.sup cenSpan = cenSpan S := by
      rw [← iSup_cenSpan_trComps]
      refine le_antisymm (Finset.sup_le fun D hD => ?_) (iSup_le fun D => ?_)
      · exact le_iSup (fun D : trComps S => cenSpan (D : Set (V ≃ₗ[ZMod p] V)))
          ⟨D, (trComps_finite S).mem_toFinset.mp hD⟩
      · exact Finset.le_sup (f := cenSpan) ((trComps_finite S).mem_toFinset.mpr D.2)
    have hinf : (𝒜.inf fun D => fixSub (Subgroup.closure D)) = fixSub (Subgroup.closure S) := by
      refine le_antisymm (fun x hx => ?_) (Finset.le_inf fun D hD =>
        hfixle D ((trComps_finite S).mem_toFinset.mp hD))
      refine mem_fixSub_closure_of_forall fun s hs => ?_
      have hle := Finset.inf_le (f := fun D => fixSub (Subgroup.closure D))
        ((trComps_finite S).mem_toFinset.mpr (mem_trComps hs))
      exact hle hx s (Subgroup.subset_closure (mem_trComp_self hs))
    rw [hsup, hinf] at h
    exact h
  · rw [iSupIndep_def]
    rintro ⟨D, hD⟩
    refine (hcomp D hD).1.disjoint.mono_right (iSup₂_le fun D' hD'ne => ?_)
    exact hcenle D hD D' D'.2 fun h => hD'ne (Subtype.ext h.symm)

theorem noNormalExpP_of_normal {A T : Subgroup (V ≃ₗ[ZMod p] V)} (hTA : T ≤ A)
    (hnorm : ∀ a ∈ A, ∀ t ∈ T, a * t * a⁻¹ ∈ T)
    (hA : ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥) : NoNormalExpP T := by
  intro N hNT hNnorm hexp
  have hPbot : (CFSG.pCore p T).map T.subtype = ⊥ := by
    refine hA _ ((Subgroup.map_subtype_le _).trans hTA) (fun a ha n hn => ?_)
      (CFSG.pCore_isPGroup.map T.subtype)
    obtain ⟨m, hm, rfl⟩ := hn
    let φ : T ≃* T :=
      { toFun := fun t => ⟨a * t * a⁻¹, hnorm a ha t t.2⟩
        invFun := fun t => ⟨a⁻¹ * t * a⁻¹⁻¹, hnorm a⁻¹ (A.inv_mem ha) t t.2⟩
        left_inv := fun t => Subtype.ext (by simp only; group)
        right_inv := fun t => Subtype.ext (by simp only; group)
        map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    have hchar := Subgroup.characteristic_iff_map_eq.mp
      (CFSG.pCore_characteristic (p := p) (G := T)) φ
    have hφm : φ m ∈ CFSG.pCore p T := by
      rw [← hchar]
      exact ⟨m, hm, rfl⟩
    exact ⟨φ m, hφm, rfl⟩
  rw [eq_bot_iff, ← hPbot]
  intro n hn
  refine ⟨⟨n, hNT hn⟩, ?_, rfl⟩
  have hK : N.subgroupOf T ∈ {K : Subgroup T | K.Normal ∧ IsPGroup p K} := by
    refine ⟨⟨fun x hx g => hNnorm g g.2 x hx⟩, fun x => ⟨1, ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hexp _ x.2
  exact Subgroup.mem_sSup_of_mem hK (show (⟨n, hNT hn⟩ : T) ∈ N.subgroupOf T from hn)

theorem conj_mem_closure_of_normalizes {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hSA : ∀ a ∈ A, ∀ t ∈ S, a * t * a⁻¹ ∈ S) {a : V ≃ₗ[ZMod p] V} (ha : a ∈ A)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Subgroup.closure S) : a * g * a⁻¹ ∈ Subgroup.closure S := by
  refine Subgroup.closure_induction (p := fun g _ => a * g * a⁻¹ ∈ Subgroup.closure S)
    (fun t ht => Subgroup.subset_closure (hSA a ha t ht)) (by simp) (fun x y _ _ hx hy => ?_)
    (fun x _ hx => ?_) hg
  · rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  · rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

theorem kantor_reduction_of_normalizes (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥)
    (hSsub : S ⊆ A) (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f)
    (hSA : ∀ a ∈ A, ∀ t ∈ S, a * t * a⁻¹ ∈ S) : KantorDecomp S (trComps S) :=
  kantor_reduction hp S hS (noNormalExpP_of_normal ((Subgroup.closure_le A).mpr hSsub)
    (fun _ ha _ ht => conj_mem_closure_of_normalizes hSA ha ht) hA)

end CFSG.StandardType.McLaughlinOdd
