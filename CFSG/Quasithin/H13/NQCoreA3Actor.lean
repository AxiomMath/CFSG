module

public import CFSG.Quasithin.SteinbergBNA7NoThreeS3
public import CFSG.Quasithin.SteinbergCGA7ListedActor

public section

namespace CFSG.Quasithin.H13.NQCore

open Module Subgroup Equiv
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight)
open CFSG.LocalAnalysis.SteinbergBV (IsBinaryTransvection)
open CFSG.Quasithin.SteinbergBN (deletedW deltaSub radSub wRep onesV)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Deleted

variable (m : ℕ)

theorem deltaSub_eq_evenWeight :
    (deltaSub m : Set (Fin m → ZMod 2)) = (evenWeight (Fin m) : Set (Fin m → ZMod 2)) := by
  ext x
  change x ∈ deltaSub m ↔ x ∈ evenWeight (Fin m)
  rw [SteinbergBN.mem_deltaSub]
  rfl

@[expose] noncomputable def deltaEquiv : ↥(deltaSub m) ≃ₗ[ZMod 2] ↥(evenWeight (Fin m)) :=
  LinearEquiv.ofEq _ _ (SetLike.coe_injective (deltaSub_eq_evenWeight m))

theorem radSub_eq_bot_of_odd (hm : Odd m) : radSub m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : Fin m → ZMod 2) ∈ Submodule.span (ZMod 2) {onesV m} := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx'
  have hsum := (SteinbergBN.mem_deltaSub m).mp x.2
  rw [← hc] at hsum
  simp only [Pi.smul_apply, onesV, smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm1 : ((m : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_iff]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by rw [hk, ZMod.val_one]; ring⟩
  rw [hm1, one_mul] at hsum
  rw [Submodule.mem_bot]
  apply Subtype.ext
  rw [← hc, hsum, zero_smul]
  rfl

@[expose] noncomputable def deletedEquivOdd (hm : Odd m) :
    deletedW m ≃ₗ[ZMod 2] ↥(evenWeight (Fin m)) :=
  ((radSub m).quotEquivOfEqBot (radSub_eq_bot_of_odd m hm)).trans (deltaEquiv m)

theorem map_radSub_deltaEquiv :
    (radSub m).map (deltaEquiv m : ↥(deltaSub m) →ₗ[ZMod 2] ↥(evenWeight (Fin m))) =
      (Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)}).comap (evenWeight (Fin m)).subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨(deltaEquiv m).symm x, hx, ?_⟩
    simp

@[expose] noncomputable def deletedEquivEven :
    deletedW m ≃ₗ[ZMod 2] (↥(evenWeight (Fin m)) ⧸
      (Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)}).comap (evenWeight (Fin m)).subtype) :=
  Submodule.Quotient.equiv _ _ (deltaEquiv m) (map_radSub_deltaEquiv m)

end Deleted

variable {G : Type*} [Group G] [Finite G]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem isEmpty_mulEquiv_three_S3_of_section
    (hG : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9) {Q : Type*} [Group Q]
    (Y : Subgroup G) {H L : Subgroup Q} (ρ : Y →* H) (hρ : Function.Surjective ρ) (hLH : L ≤ H) :
    IsEmpty (L ≃* (Fin 3 → Perm (Fin 3))) := by
  refine ⟨fun χ => ?_⟩
  let κ : (Fin 3 → Perm (Fin 3)) →* H := (inclusion hLH).comp χ.symm.toMonoidHom
  have hκ : Function.Injective κ := (inclusion_injective hLH).comp χ.symm.injective
  let θ₀ : (κ.range.comap ρ) →* (Fin 3 → Perm (Fin 3)) :=
    (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp (ρ.subgroupComap κ.range)
  have hθ₀ : Function.Surjective θ₀ :=
    (MonoidHom.ofInjective hκ).symm.surjective.comp (ρ.subgroupComap_surjective κ.range hρ)
  let θ : ((κ.range.comap ρ).map Y.subtype) →* (Fin 3 → Perm (Fin 3)) :=
    θ₀.comp ((κ.range.comap ρ).equivMapOfInjective Y.subtype Y.subtype_injective).symm.toMonoidHom
  have hθ : Function.Surjective θ := hθ₀.comp (MulEquiv.surjective _)
  have h3 := QuasithinUnique.Setup.Lift.sym_three_pow_section_forces_three_rank 3 _ θ hθ
  obtain ⟨A, hA, hcard⟩ := SteinbergCG.exists_isElementaryAbelian_card_pRank Nat.prime_three G
  have h9 := hG A hA
  rw [hcard] at h9
  have h27 : 3 ^ 3 ≤ 3 ^ CFSG.pRank 3 G := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem three_rank_irreducible_normal_transvection_actor_forces_S3_or_S7
    (hG : ∀ E : Subgroup G, CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9)
    (hV : 2 ≤ finrank (ZMod 2) V) (Y : Subgroup G)
    {H N T : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} (ρ : Y →* H)
    (hρ : Function.Surjective ρ) (hNH : N ≤ H) (hNn : (N.subgroupOf H).Normal)
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = closure {n | n ∈ N ∧ IsBinaryTransvection n})
    (hT : ABGLocalTools.IsSylowOf 2 T H) {b : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hbN : b ∈ N) (hb : orderOf b = 3)
    (hTb : T ≤ normalizer (zpowers b : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)))
    (hrank : finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2) :
    H = N ∧
      ((Nonempty (H ≃* Perm (Fin 3)) ∧ finrank (ZMod 2) V = 2) ∨
        (finrank (ZMod 2) V = 6 ∧ ∃ ψ : Perm (Fin 7) ≃* H,
          ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin 7), ∀ σ v i,
            (f (((ψ σ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) :
              Fin 7 → ZMod 2) i = (f v : Fin 7 → ZMod 2) (σ⁻¹ i))) ∧
      normalizer (T : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) ⊓ H = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite (V ≃ₗ[ZMod 2] V) := SteinbergBS.RankTwoThree.finite_linearEquiv V
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Finite.of_injective _ (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective
  have hS3 : ∀ L ≤ N, IsEmpty (L ≃* (Fin 3 → Perm (Fin 3))) := fun L hLN =>
    isEmpty_mulEquiv_three_S3_of_section hG Y ρ hρ (hLN.trans hNH)
  have hrec := SteinbergBN.no_three_S3_binary_transvection_group_linear_or_deleted_symmetric hV N
    hirr hgen hS3
  set e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V with he
  have hecoe : ∀ g : LinearMap.GeneralLinearGroup (ZMod 2) V,
      ((e g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = (g : V →ₗ[ZMod 2] V) := fun g =>
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap g
  set H' := H.map e.toMonoidHom with hH'
  set N' := N.map e.toMonoidHom with hN'
  set T' := T.map e.toMonoidHom with hT'
  set eH : ↥H ≃* ↥H' := H.equivMapOfInjective _ e.injective with heH
  set eN : ↥N ≃* ↥N' := N.equivMapOfInjective _ e.injective with heN
  have hN'H' : N' ≤ H' := map_mono hNH
  have hN'n : (N'.subgroupOf H').Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hN'H', hH', hN', ← map_equiv_normalizer_eq]
    exact map_mono ((normal_subgroupOf_iff_le_normalizer hNH).mp hNn)
  have hT'syl : ABGLocalTools.IsSylowOf 2 T' H' := by
    obtain ⟨hTH, hT2, hTi⟩ := ABGLocalTools.isSylowOf_iff.mp hT
    refine ABGLocalTools.isSylowOf_iff.mpr ⟨map_mono hTH, hT2.map _, ?_⟩
    rw [hT', hH', relIndex_map_map_of_injective _ _ e.injective]
    exact hTi
  have hb'N : e b ∈ N' := mem_map_of_mem _ hbN
  have hb' : orderOf (e b) = 3 := (orderOf_injective e.toMonoidHom e.injective b).trans hb
  have hT'b : T' ≤ normalizer (zpowers (e b) : Set (V ≃ₗ[ZMod 2] V)) := by
    have hz : zpowers (e b) = (zpowers b).map e.toMonoidHom :=
      (MonoidHom.map_zpowers e.toMonoidHom b).symm
    rw [hT', hz, ← map_equiv_normalizer_eq]
    exact map_mono hTb
  have hrank' : finrank (ZMod 2) (LinearMap.range
      (((e b : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id)) = 2 := by
    rw [hecoe]
    exact hrank
  set ρ' : Y →* H' := eH.toMonoidHom.comp ρ with hρ'
  have hρ'surj : Function.Surjective ρ' := eH.surjective.comp hρ
  have halt : N' = ⊤ ∨
      (∃ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
        N' = TauCeti.BilinForm.isometryGroup β) ∨
      (∃ q : QuadraticForm (ZMod 2) V, (QuadraticMap.polarBilin q).Nondegenerate ∧
        N' = TauCeti.QuadraticMap.orthogonalGroup q) ∨
      ∃ m : ℕ, 3 ≤ m ∧ ∃ ψ : Perm (Fin m) ≃* N',
        (Odd m ∧ ∃ f : V ≃ₗ[ZMod 2] evenWeight (Fin m), ∀ σ v i,
          (f ((ψ σ : V ≃ₗ[ZMod 2] V) v) : Fin m → ZMod 2) i = (f v : Fin m → ZMod 2) (σ⁻¹ i)) ∨
        (Even m ∧ ∃ f : V ≃ₗ[ZMod 2] (evenWeight (Fin m) ⧸
            (Submodule.span (ZMod 2) {fun _ => 1}).comap (evenWeight (Fin m)).subtype),
          ∀ σ v (x y : evenWeight (Fin m)), f v = Submodule.Quotient.mk x →
            (∀ i, (y : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i)) →
            f ((ψ σ : V ≃ₗ[ZMod 2] V) v) = Submodule.Quotient.mk y) := by
    rcases hrec with ⟨hNtop, -, -⟩ | ⟨m, hm, ψ, f, hf, -⟩
    · left
      rw [hN', hNtop]
      exact map_top_of_surjective _ e.surjective
    · right; right; right
      have hm3 : 3 ≤ m := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        omega
      refine ⟨m, hm3, ψ.trans eN, ?_⟩
      have hψ : ∀ σ v, ((ψ.trans eN σ : ↥N') : V ≃ₗ[ZMod 2] V) v =
          ((ψ σ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v := fun σ v => by
        rw [← hecoe]
        rfl
      rcases Nat.even_or_odd m with hev | hodd
      · right
        refine ⟨hev, f.trans (deletedEquivEven m), fun σ v x y hx hy => ?_⟩
        rw [hψ, LinearEquiv.trans_apply, hf σ v]
        obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (f v)
        rw [LinearEquiv.trans_apply, ← hx₀] at hx
        rw [← hx₀, SteinbergBN.wRep_apply_mk]
        change Submodule.Quotient.mk (deltaEquiv m _) = _
        change Submodule.Quotient.mk (deltaEquiv m x₀) = Submodule.Quotient.mk x at hx
        rw [Submodule.Quotient.eq] at hx ⊢
        have hx' : ((deltaEquiv m x₀ - x : ↥(evenWeight (Fin m))) : Fin m → ZMod 2) ∈
            Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx'
        change ((deltaEquiv m (SteinbergBN.deltaEnd m σ x₀) - y : ↥(evenWeight (Fin m))) :
          Fin m → ZMod 2) ∈ Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)}
        refine Submodule.mem_span_singleton.mpr ⟨c, funext fun i => ?_⟩
        have hci := congrFun hc (σ⁻¹ i)
        simp only [Pi.smul_apply, smul_eq_mul, mul_one, Submodule.coe_sub, Pi.sub_apply] at hci ⊢
        rw [hy i]
        exact hci
      · left
        refine ⟨hodd, f.trans (deletedEquivOdd m hodd), fun σ v i => ?_⟩
        rw [hψ, LinearEquiv.trans_apply, hf σ v, LinearEquiv.trans_apply]
        obtain ⟨x₀, hx₀⟩ := Submodule.Quotient.mk_surjective _ (f v)
        rw [← hx₀, SteinbergBN.wRep_apply_mk]
        rfl
  obtain ⟨hHN', hcase, hnorm⟩ := SteinbergCG.listed_binary_normal_actor_forces_S3_or_S7 hG Y ρ'
    hρ'surj hN'H' hN'n hT'syl hb'N hb' hT'b hrank' halt
  have hHN : H = N := map_injective (f := e.toMonoidHom) e.injective hHN'
  refine ⟨hHN, ?_, ?_⟩
  · rcases hcase with ⟨⟨χ⟩, h2⟩ | ⟨h6, ψ, f, hf⟩
    · exact Or.inl ⟨⟨eH.trans χ⟩, h2⟩
    · refine Or.inr ⟨h6, ψ.trans eH.symm, f, fun σ v i => ?_⟩
      have h1 := hf σ v i
      have h2 : ((ψ σ : ↥H') : V ≃ₗ[ZMod 2] V) =
          e ((ψ.trans eH.symm σ : ↥H) : LinearMap.GeneralLinearGroup (ZMod 2) V) := by
        change ((ψ σ : ↥H') : V ≃ₗ[ZMod 2] V) = ((eH ((eH.symm) (ψ σ)) : ↥H') : _)
        rw [eH.apply_symm_apply]
      rw [h2] at h1
      change (f (((e ((ψ.trans eH.symm σ : ↥H) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) v) : Fin 7 → ZMod 2) i = _
      rw [hecoe]
      exact h1
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_inf_eq _ _ e.toMonoidHom e.injective, map_equiv_normalizer_eq]
    exact hnorm

end CFSG.Quasithin.H13.NQCore
