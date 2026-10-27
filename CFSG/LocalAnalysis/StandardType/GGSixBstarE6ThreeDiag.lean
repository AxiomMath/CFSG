module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Hyp
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeToral
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoOffE6Three

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def zetaHom (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* (Fin Tag.E6.rank → Kˣ) where
  toFun x := TableBExc.E6Three.zetaVec ζ hζ (Multiplicative.toAdd x)
  map_one' := by
    funext i
    simp [TableBExc.E6Three.zetaVec]
  map_mul' x y := by
    funext i
    simp only [TableBExc.E6Three.zetaVec, toAdd_mul, Pi.add_apply, Pi.mul_apply]
    exact map_mul (zmodPowHom ζ hζ) (Multiplicative.ofAdd (Multiplicative.toAdd x i))
      (Multiplicative.ofAdd (Multiplicative.toAdd y i))

theorem zetaHom_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3) :
    zetaHom ζ hζ (Multiplicative.ofAdd x) = TableBExc.E6Three.zetaVec ζ hζ x :=
  rfl

@[expose] noncomputable def diag3 (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin Tag.E6.rank → ZMod 3) →* MulAut (adjointGroup .E6 K) :=
  (rootDiagAutHom .E6 K).comp (zetaHom ζ hζ)

theorem diag3_apply (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (x : Fin Tag.E6.rank → ZMod 3)
    (h : adjointGroup .E6 K) :
    ((diag3 ζ hζ (Multiplicative.ofAdd x) h : adjointGroup .E6 K) : ModGL .E6 K) =
      rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x) * (h : ModGL .E6 K) *
        (rootDiagUnit .E6 (TableBExc.E6Three.zetaVec ζ hζ x))⁻¹ :=
  rfl

@[expose] noncomputable def vAd (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (MulAut (adjointGroup .E6 K)) :=
  (diag3 ζ hζ).range

@[expose] noncomputable def hypIncl : Multiplicative (NoOffRest.hypE6) →* Multiplicative (Fin Tag.E6.rank → ZMod 3) :=
  AddMonoidHom.toMultiplicative (NoOffRest.hypE6).subtype

@[expose] noncomputable def diag3Hyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    Multiplicative (NoOffRest.hypE6) →* MulAut (adjointGroup .E6 K) :=
  (diag3 ζ hζ).comp hypIncl

@[expose] noncomputable def vHyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : Subgroup (MulAut (adjointGroup .E6 K)) :=
  (diag3Hyp ζ hζ).range

end Defs

section Facts

variable {K : Type} [Field K]

theorem zetaHom_injective {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (zetaHom (K := K) ζ hζ) := by
  intro x y h
  exact Multiplicative.toAdd.injective
    (TableBExc.E6Three.zetaVec_injective hζo hζ h)

theorem diag3_injective {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (diag3 (K := K) ζ hζ) :=
  (rootDiagAutHom_injective (τ := .E6) (K := K)).comp (zetaHom_injective hζo hζ)

theorem diag3Hyp_injective {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Function.Injective (diag3Hyp (K := K) ζ hζ) := by
  refine (diag3_injective hζo hζ).comp ?_
  intro x y h
  exact Multiplicative.toAdd.injective (Subtype.ext (Multiplicative.toAdd.injective h))

theorem card_multiplicative_pi_zmod :
    Nat.card (Multiplicative (Fin Tag.E6.rank → ZMod 3)) = 3 ^ 6 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin Tag.E6.rank → ZMod 3) ≃ _),
    Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rfl

theorem card_vAd {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Nat.card (vAd (K := K) ζ hζ) = 3 ^ 6 := by
  unfold vAd
  rw [← Nat.card_congr (MonoidHom.ofInjective (diag3_injective hζo hζ)).toEquiv,
    card_multiplicative_pi_zmod]

theorem card_vHyp {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) :
    Nat.card (vHyp (K := K) ζ hζ) = 3 ^ 5 := by
  unfold vHyp
  rw [← Nat.card_congr (MonoidHom.ofInjective (diag3Hyp_injective hζo hζ)).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (NoOffRest.hypE6) ≃ _)]
  exact NoOffRest.card_hypE6

theorem pow_three_eq_one (a : Multiplicative (Fin Tag.E6.rank → ZMod 3)) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext j
  simp only [Pi.smul_apply, Pi.zero_apply]
  generalize (Multiplicative.toAdd a) j = z
  revert z
  decide

theorem isElemAbelian_vAd (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : IsElemAbelian 3 (vAd (K := K) ζ hζ) :=
  isElemAbelian_range (fun a b => mul_comm a b) pow_three_eq_one (diag3 ζ hζ)

theorem hypIncl_injective : Function.Injective hypIncl := fun x y h =>
  Multiplicative.toAdd.injective (Subtype.ext (Multiplicative.toAdd.injective h))

theorem pow_three_eq_one_hyp (a : Multiplicative NoOffRest.hypE6) : a ^ 3 = 1 :=
  hypIncl_injective (by rw [map_pow, pow_three_eq_one, map_one])

theorem isElemAbelian_vHyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : IsElemAbelian 3 (vHyp (K := K) ζ hζ) :=
  isElemAbelian_range (fun a b => mul_comm a b) pow_three_eq_one_hyp (diag3Hyp ζ hζ)

theorem vHyp_le_vAd (ζ : Kˣ) (hζ : ζ ^ 3 = 1) : vHyp (K := K) ζ hζ ≤ vAd ζ hζ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨hypIncl x, rfl⟩

end Facts

section Aut

open TableBExc.E6Three

variable {K : Type} [Field K]

theorem rootDiagAutHom_mem_hatAut_range (a : Fin Tag.E6.rank → Kˣ) :
    rootDiagAutHom .E6 K a ∈ (hatAut .E6 K).range :=
  ⟨⟨rootDiagUnit .E6 a, rootDiagUnit_mem_hatGroup a⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩

theorem vAd_le_hatAut_range (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    vAd (K := K) ζ hζ ≤ (hatAut .E6 K).range := by
  rintro _ ⟨x, rfl⟩
  exact rootDiagAutHom_mem_hatAut_range _

end Aut

section Inner

variable {K : Type} [Field K]

@[expose] def cartanSection : Fin Tag.E6.rank → Fin Tag.E6.rank → ZMod 3 :=
  ![![0, 2, 2, 1, 1, 1], ![0, 2, 0, 0, 1, 2], ![0, 1, 0, 2, 0, 1], ![0, 0, 0, 0, 2, 1],
    ![0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0]]

theorem cartan_mul_cartanSection :
    ∀ x : Fin Tag.E6.rank → ZMod 3, NoOffRest.kDotP 3 x = 0 → ∀ l : Fin Tag.E6.rank,
      ∑ j, ((Tag.E6.cartan j l : ℤ) : ZMod 3) * (∑ m, cartanSection j m * x m) = x l := by
  decide +kernel

theorem zetaVec_eq_cartanChar_of_mem_hyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ NoOffRest.hypE6) :
    ∃ y : Fin Tag.E6.rank → ZMod 3,
      TableBExc.E6Three.zetaVec ζ hζ x = cartanChar (TableBExc.E6Three.zetaVec ζ hζ y) := by
  refine ⟨fun j => ∑ m, cartanSection j m * x m, ?_⟩
  funext l
  have h := cartan_mul_cartanSection x hx l
  simp only [cartanChar, TableBExc.E6Three.zetaVec]
  rw [← h, ofAdd_sum, map_prod]
  refine (Finset.prod_congr rfl fun j _ => ?_)
  rw [TableBExc.E6Three.zmodPowHom_zpow]

theorem diag3_mem_innerAut_of_mem_hyp (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ NoOffRest.hypE6) :
    diag3 (K := K) ζ hζ (Multiplicative.ofAdd x) ∈
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  obtain ⟨y, hy⟩ := zetaVec_eq_cartanChar_of_mem_hyp ζ hζ hx
  have h := rootDiagAut_cartanChar_mem_inner (τ := .E6) (K := K)
    (TableBExc.E6Three.zetaVec ζ hζ y)
  have e : diag3 (K := K) ζ hζ (Multiplicative.ofAdd x) =
      rootDiagAut .E6 K (cartanChar (TableBExc.E6Three.zetaVec ζ hζ y)) := by
    rw [← hy]
    rfl
  rw [e]
  exact h

theorem vHyp_le_innerAut (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    vHyp (K := K) ζ hζ ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  rintro _ ⟨x, rfl⟩
  exact diag3_mem_innerAut_of_mem_hyp ζ hζ (Multiplicative.toAdd x).2

end Inner

section TwoLocal

variable {K : Type} [Field K]

theorem twoLocal_vAd [CharP K 2] (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    ∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ vAd (K := K) ζ hζ, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨U₀, hU₀, hU₀2, hU₀n⟩ :=
    TableBExc.E6Three.exists_rootGroup_normalized_diag (τ := .E6) (K := K) ⟨0, by decide⟩
  refine ⟨U₀, hU₀, hU₀2, ?_⟩
  rintro _ ⟨x, rfl⟩ u hu
  obtain ⟨v, hv, hveq⟩ := hU₀n (TableBExc.E6Three.zetaVec ζ hζ (Multiplicative.toAdd x)) u hu
  have h1 : (diag3 ζ hζ x) u = v := Subtype.ext (by
    rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl, diag3_apply]
    exact hveq.symm)
  rw [h1]
  exact hv

theorem twoLocal_vHyp [CharP K 2] (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    ∃ U : Subgroup (adjointGroup .E6 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ φ ∈ vHyp (K := K) ζ hζ, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨U, hU, hU2, hUn⟩ := twoLocal_vAd (K := K) ζ hζ
  exact ⟨U, hU, hU2, fun φ hφ => hUn φ (vHyp_le_vAd ζ hζ hφ)⟩

end TwoLocal

end NoOffE6Three

end CFSG.StandardType
