module

public import CFSG.Quasithin.Background.F918V0
public import CFSG.Quasithin.Background.F918T5
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B4ModelsAction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Matrix

section OffenderModel

variable {X : Type} [CommGroup X] {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}

private def natMulEquiv (γ : ↥Γ) : Multiplicative (Fin 3 → K) ≃* Multiplicative (Fin 3 → K) where
  toFun := natAct Γ γ
  invFun := natAct Γ γ⁻¹
  left_inv x := by rw [← natAct_mul_act, inv_mul_cancel, natAct_one]
  right_inv x := by rw [← natAct_mul_act, mul_inv_cancel, natAct_one]
  map_mul' := natAct_mul Γ γ

private theorem natMulEquiv_apply (γ : ↥Γ) (x : Multiplicative (Fin 3 → K)) :
    natMulEquiv γ x = natAct Γ γ x := rfl

variable (Γ) in
private def transAct {V : Subgroup X} (Θ : ↥V ≃* Multiplicative (Fin 3 → K)) : ↥Γ →* MulAut ↥V where
  toFun γ := Θ.trans ((natMulEquiv γ).trans Θ.symm)
  map_one' := MulEquiv.ext fun v => by simp [natMulEquiv_apply, natAct_one]
  map_mul' γ δ := MulEquiv.ext fun v => by simp [natMulEquiv_apply, natAct_mul_act]

private theorem transAct_apply {V : Subgroup X} (Θ : ↥V ≃* Multiplicative (Fin 3 → K)) (γ : ↥Γ) (v : ↥V) :
    Θ (transAct Γ Θ γ v) = natAct Γ γ (Θ v) :=
  Θ.apply_symm_apply (natAct Γ γ (Θ v))

private theorem transAct_theta {Lb : Subgroup (MulAut X)} {V : Subgroup X} (hLV : Lb ≤ stabSub V)
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V ≃* Multiplicative (Fin 3 → K))
    (hΘ : ∀ (l : ↥Lb) (v : ↥V), Θ ((resHomOn V hLV l : MulAut ↥V) v) = natAct Γ (θ l) (Θ v)) (l : ↥Lb) :
    transAct Γ Θ (θ l) = resHomOn V hLV l :=
  MulEquiv.ext fun v => Θ.injective (by rw [transAct_apply, hΘ])

private theorem transAct_injective {Lb : Subgroup (MulAut X)} {V : Subgroup X} (hLV : Lb ≤ stabSub V)
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V ≃* Multiplicative (Fin 3 → K)) (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V), Θ ((resHomOn V hLV l : MulAut ↥V) v) = natAct Γ (θ l) (Θ v)) :
    Function.Injective (transAct Γ Θ) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨l, rfl⟩ := hθs γ
  rw [transAct_theta hLV θ Θ hΘ] at hγ
  apply natAct_faithful Γ (θ l)
  intro m
  obtain ⟨v, rfl⟩ := Θ.surjective m
  rw [← hΘ, hγ, MulAut.one_apply, mul_inv_cancel]

private theorem mem_fixV_map_transAct {V : Subgroup X} (Θ : ↥V ≃* Multiplicative (Fin 3 → K))
    (B : Subgroup ↥Γ) (v : ↥V) :
    v ∈ fixV (B.map (transAct Γ Θ)) ↔ Multiplicative.toAdd (Θ v) ∈ fixNat Γ B := by
  constructor
  · intro h γ hγ
    have h1 : transAct Γ Θ γ v = v := mem_fixV.mp h _ (Subgroup.mem_map_of_mem _ hγ)
    have h2 : natAct Γ γ (Θ v) = Θ v := by rw [← transAct_apply, h1]
    exact congrArg Multiplicative.toAdd h2
  · rintro h _ ⟨γ, hγ, rfl⟩
    apply Θ.injective
    rw [transAct_apply]
    have h1 := h γ hγ
    show Multiplicative.ofAdd (_ *ᵥ Multiplicative.toAdd (Θ v)) = Θ v
    rw [h1, ofAdd_toAdd]

private theorem card_fixV_map_transAct {V : Subgroup X} (Θ : ↥V ≃* Multiplicative (Fin 3 → K))
    (B : Subgroup ↥Γ) : Nat.card ↥(fixV (B.map (transAct Γ Θ))) = Nat.card ↥(fixNat Γ B) :=
  Nat.card_congr ((Θ.toEquiv.trans Multiplicative.toAdd).subtypeEquiv
    (p := fun v => v ∈ fixV (B.map (transAct Γ Θ))) (q := fun w => w ∈ fixNat Γ B)
    (mem_fixV_map_transAct Θ B))

private theorem agree_of_offender {Lb N A : Subgroup (MulAut X)} {V : Subgroup X} (hN : N ≤ stabSub V)
    (hAN : A ≤ N) (hffJ : ffJ (autSub (Lb ⊔ N) V) = autSub Lb V)
    (hoff : IsFFStarOffender (autSub (Lb ⊔ N) V) (autSub A V)) :
    ∀ a ∈ A, ∃ l ∈ Lb, ∀ v ∈ V, a v = l v := by
  intro a ha
  have haV : a ∈ stabSub V := hN (hAN ha)
  have hle : autSub A V ≤ autSub Lb V :=
    (le_iSup₂ (f := fun (B : Subgroup (MulAut ↥V)) (_ : IsFFStarOffender (autSub (Lb ⊔ N) V) B) => B)
      _ hoff).trans hffJ.le
  obtain ⟨g, hg, hgn⟩ := mem_autSub.mp (hle (mem_autSub.mpr ⟨⟨a, haV⟩, ha, rfl⟩))
  refine ⟨(g : MulAut X), hg, fun v hv => ?_⟩
  exact (congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : X)) hgn).symm

private theorem autSub_eq_map_agreeSub {Lb A : Subgroup (MulAut X)} {V : Subgroup X} (hLV : Lb ≤ stabSub V)
    (hA : A ≤ stabSub V) (hagree : ∀ a ∈ A, ∃ l ∈ Lb, ∀ v ∈ V, a v = l v) :
    autSub A V = (agreeSub Lb A V hLV).map (resHomOn V hLV) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨l, hl, hag⟩ := hagree (g : MulAut X) hg
    refine ⟨⟨l, hl⟩, ⟨g, hg, hag⟩, ?_⟩
    ext v
    exact (hag v v.2).symm
  · rintro ⟨l, ⟨a, ha, hag⟩, rfl⟩
    refine mem_autSub.mpr ⟨⟨a, hA ha⟩, ha, ?_⟩
    ext v
    exact hag v v.2

end OffenderModel

theorem offender_model {X : Type} [CommGroup X] [Finite X] {Lb N A : Subgroup (MulAut X)}
    {V : Subgroup X} (hLV : Lb ≤ stabSub V) (hN : N ≤ stabSub V) (hAN : A ≤ N)
    {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
    (θ : ↥Lb →* ↥Γ) (Θ : ↥V ≃* Multiplicative (Fin 3 → K)) (hθs : Function.Surjective θ)
    (hΘ : ∀ (l : ↥Lb) (v : ↥V),
      Θ ((resHomOn V hLV l : MulAut ↥V) v) = natAct Γ (θ l) (Θ v))
    (hffJ : ffJ (autSub (Lb ⊔ N) V) = autSub Lb V)
    (hoff : IsFFStarOffender (autSub (Lb ⊔ N) V) (autSub A V)) :
    (∀ a ∈ A, ∃ l ∈ Lb, ∀ v ∈ V, a v = l v) ∧
      OffNat Γ ((agreeSub Lb A V hLV).map θ) := by
  have hagree := agree_of_offender hN hAN hffJ hoff
  refine ⟨hagree, ?_⟩
  have hinj := transAct_injective hLV θ Θ hθs hΘ
  have hE : ((agreeSub Lb A V hLV).map θ).map (transAct Γ Θ) = autSub A V := by
    have hcomp : (transAct Γ Θ).comp θ = resHomOn V hLV := MonoidHom.ext (transAct_theta hLV θ Θ hΘ)
    rw [Subgroup.map_map, hcomp, ← autSub_eq_map_agreeSub hLV (hAN.trans hN) hagree]
  have hmem : ∀ γ ∈ (agreeSub Lb A V hLV).map θ, transAct Γ Θ γ ∈ autSub A V := fun γ hγ => by
    rw [← hE]
    exact Subgroup.mem_map_of_mem _ hγ
  refine ⟨fun h => hoff.2.1 ?_, fun a ha b hb => hinj ?_, fun a ha => hinj ?_, fun B hB => ?_⟩
  · rw [← hE, h, Subgroup.map_bot]
  · rw [map_mul, map_mul]
    exact hoff.2.2.1.1 _ (hmem a ha) _ (hmem b hb)
  · rw [map_pow, map_one]
    exact hoff.2.2.1.2 _ (hmem a ha)
  · have h := hoff.2.2.2 (B.map (transAct Γ Θ)) ((Subgroup.map_mono hB).trans hE.le)
    rw [← hE, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj,
      card_fixV_map_transAct, card_fixV_map_transAct] at h
    exact h

end CFSG.Quasithin
