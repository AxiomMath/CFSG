module

public import CFSG.Quasithin.Vol2.Ch10SecC3G
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13 (tensorPairModel)
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply)
open scoped Matrix

variable {K : Type} [Field K]

variable (K) in
@[expose] def tau : MulAut (WM K) where
  toFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  invFun X := Multiplicative.ofAdd (Multiplicative.toAdd X)ᵀ
  left_inv X := by simp
  right_inv X := by simp
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    simp [Matrix.transpose_add]

theorem toAdd_tau (X : WM K) : Multiplicative.toAdd (tau K X) = (Multiplicative.toAdd X)ᵀ := rfl

theorem tau_mul_self : tau K * tau K = 1 := MulEquiv.ext fun X => by
  apply Multiplicative.toAdd.injective
  change ((Multiplicative.toAdd X)ᵀ)ᵀ = Multiplicative.toAdd X
  rw [Matrix.transpose_transpose]

theorem tau_inv : (tau K)⁻¹ = tau K := inv_eq_of_mul_eq_one_right tau_mul_self

theorem tau_conj_rho (g : SL K × SL K) : tau K * rho K g * (tau K)⁻¹ = rho K g.swap := by
  rw [tau_inv]
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change ((g.1 : Matrix (Fin 2) (Fin 2) K) * (Multiplicative.toAdd X)ᵀ *
    (g.2 : Matrix (Fin 2) (Fin 2) K)ᵀ)ᵀ = (g.2 : Matrix (Fin 2) (Fin 2) K) *
      Multiplicative.toAdd X * (g.1 : Matrix (Fin 2) (Fin 2) K)ᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem tau_mul_rho (g : SL K × SL K) : tau K * rho K g = rho K g.swap * tau K := by
  rw [← tau_conj_rho, inv_mul_cancel_right]

@[expose] def sc (y : Kˣ) : MulAut (WM K) where
  toFun X := Multiplicative.ofAdd ((y : K) • Multiplicative.toAdd X)
  invFun X := Multiplicative.ofAdd (((y⁻¹ : Kˣ) : K) • Multiplicative.toAdd X)
  left_inv X := by simp [smul_smul]
  right_inv X := by simp [smul_smul]
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    simp [smul_add]

theorem toAdd_sc (y : Kˣ) (X : WM K) :
    Multiplicative.toAdd (sc y X) = (y : K) • Multiplicative.toAdd X := rfl

@[expose] def fa (σ : K ≃+* K) : MulAut (WM K) where
  toFun X := Multiplicative.ofAdd ((Multiplicative.toAdd X).map σ)
  invFun X := Multiplicative.ofAdd ((Multiplicative.toAdd X).map σ.symm)
  left_inv X := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp
  right_inv X := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp
  map_mul' X Y := by
    apply Multiplicative.toAdd.injective
    ext i j
    simp

theorem toAdd_fa (σ : K ≃+* K) (X : WM K) :
    Multiplicative.toAdd (fa σ X) = (Multiplicative.toAdd X).map σ := rfl

variable (K) in
@[expose] def img : Subgroup (MulAut (WM K)) := (rho K).range

variable (K) in
@[expose] def norm : Subgroup (MulAut (WM K)) :=
  Subgroup.normalizer (img K : Set (MulAut (WM K)))

theorem rho_mem_img (g : SL K × SL K) : rho K g ∈ img K := ⟨g, rfl⟩

@[expose] noncomputable def pairOf (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) : SL K × SL K :=
  ((slEquiv K).symm γ.1, (slEquiv K).symm γ.2)

theorem tensorPairModel_act (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (X : WM K) :
    (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).act γ X = rho K (pairOf γ) X := by
  apply Multiplicative.toAdd.injective
  change ((γ.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
      ((γ.2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ =
    (((slEquiv K).symm γ.1 : SL K) : Matrix (Fin 2) (Fin 2) K) * Multiplicative.toAdd X *
      (((slEquiv K).symm γ.2 : SL K) : Matrix (Fin 2) (Fin 2) K)ᵀ
  rw [coe_slEquiv_symm, coe_slEquiv_symm]

theorem exists_model {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : (tensorPairModel (StatedSL 2 K) (StatedSL 2 K)).RealizesMod H) :
    ∃ e : V ≃* WM K, H.map (congrHom e) = img K := by
  obtain ⟨π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(⊤ : Subgroup (WM K)) ⧸ (⊥ : Subgroup (WM K)).subgroupOf (⊤ : Subgroup (WM K)) ≃*
      WM K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let e : V ≃* WM K :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.ofBijective β ⟨hβi, hβs⟩)).trans q
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (WM K)) ⧸
      (⊥ : Subgroup (WM K)).subgroupOf (⊤ : Subgroup (WM K))) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have he : ∀ (γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (v : V),
      e (((π γ : ↥H) : MulAut V) v) = rho K (pairOf γ) (e v) := by
    intro γ v
    have h1 : β ⟨v, trivial⟩ = QuotientGroup.mk ⟨e v, trivial⟩ := hqs _
    have h2 := hβe γ ⟨v, trivial⟩ ⟨e v, trivial⟩ trivial trivial h1
    rw [← tensorPairModel_act]
    exact congrArg q h2
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥(StatedSL 2 K) × ↥(StatedSL 2 K),
      congrHom e ((π γ : ↥H) : MulAut V) = rho K (pairOf γ) := by
    intro γ
    refine MulEquiv.ext fun w => ?_
    show e (((π γ : ↥H) : MulAut V) (e.symm w)) = rho K (pairOf γ) w
    rw [he, MulEquiv.apply_symm_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
    have hx' : ((π γ : ↥H) : MulAut V) = x := by rw [hγ]
    have h1 := hpair γ
    rw [hx'] at h1
    rw [h1]
    exact rho_mem_img _
  · rintro ⟨g, rfl⟩
    refine ⟨_, (π (slEquiv K g.1, slEquiv K g.2)).2, ?_⟩
    rw [hpair]
    congr 1
    exact Prod.ext ((slEquiv K).symm_apply_apply g.1) ((slEquiv K).symm_apply_apply g.2)

end CFSG.Quasithin.Vol2.Ch10.C3.Om
