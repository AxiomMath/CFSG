module

public import CFSG.Quasithin.Background.RonanH15Model
public import CFSG.Quasithin.Background.RonanH15Pair
public import CFSG.Quasithin.Background.RonanH15Perm22

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {V : Type*} [CommGroup V] {Γ : Subgroup (Equiv.Perm (Fin 24))} {ρ : ↥Γ →* MulAut V}

theorem vecOf_act_pair {numer denom : Subgroup (G6.PermMod 24)}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (h : RealizesBy (FFModel.golaySec Γ numer denom) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    {i j : Fin 24} {v : V} (hv : VecOf (FFModel.golaySec Γ numer denom) β (pairVec i j) v)
    (γ : ↥Γ) :
    VecOf (FFModel.golaySec Γ numer denom) β
      (pairVec ((γ : Equiv.Perm (Fin 24)) i) ((γ : Equiv.Perm (Fin 24)) j)) (ρ γ v) := by
  have h1 := VecOf.act h hv γ
  have h2 : (FFModel.golaySec Γ numer denom).act γ (pairVec i j) =
      pairVec ((γ : Equiv.Perm (Fin 24)) i) ((γ : Equiv.Perm (Fin 24)) j) :=
    permAct_pairVec (γ : Equiv.Perm (Fin 24)) i j
  rw [h2] at h1
  exact h1

theorem vecOf_pair_eq_iff_golay {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      golayC.subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) golayC) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    {i j k l : Fin 24} (hij : i ≠ j) (hkl : k ≠ l) {v w : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) golayC) β (pairVec i j) v)
    (hw : VecOf (FFModel.golaySec Γ (G6.coreMod 24) golayC) β (pairVec k l) w) :
    v = w ↔ ({i, j} : Finset (Fin 24)) = {k, l} :=
  (VecOf.eq_iff h hv hw).trans (pairVec_inv_mul_mem_golayC_iff hij hkl)

theorem vecOf_pair_eq_iff_sup {a b : Fin 24}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) (hab : a ≠ b)
    {i j k l : Fin 24} (hij : i ≠ j) (hkl : k ≠ l) {v w : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      β (pairVec i j) v)
    (hw : VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      β (pairVec k l) w) :
    v = w ↔ ({i, j} : Finset (Fin 24)) = {k, l} ∨
      symmDiff ({i, j} : Finset (Fin 24)) {k, l} = {a, b} :=
  (VecOf.eq_iff h hv hw).trans (pairVec_inv_mul_mem_sup_iff hab hij hkl)

theorem vecOf_pair_ne_one_golay {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      golayC.subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) golayC) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    {i j : Fin 24} (hij : i ≠ j) {v : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) golayC) β (pairVec i j) v) : v ≠ 1 :=
  fun h1 => pairVec_not_mem_golayC hij ((VecOf.eq_one_iff h hv).1 h1)

theorem vecOf_pair_ne_one_sup {a b : Fin 24}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) (hab : a ≠ b)
    {i j : Fin 24} (hij : i ≠ j) (hne : ({i, j} : Finset (Fin 24)) ≠ {a, b}) {v : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      β (pairVec i j) v) : v ≠ 1 :=
  fun h1 => hne ((pairVec_mem_sup_iff hab hij).1 ((VecOf.eq_one_iff h hv).1 h1))

theorem rho_eq_self_iff_golay {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      golayC.subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) golayC) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    {i j : Fin 24} (hij : i ≠ j) {v : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) golayC) β (pairVec i j) v) (γ : ↥Γ) :
    ρ γ v = v ↔
      ({(γ : Equiv.Perm (Fin 24)) i, (γ : Equiv.Perm (Fin 24)) j} : Finset (Fin 24)) = {i, j} :=
  vecOf_pair_eq_iff_golay h ((γ : Equiv.Perm (Fin 24)).injective.ne hij) hij
    (vecOf_act_pair h hv γ) hv

theorem rho_eq_self_iff_22 {a b j : Fin 24}
    {β : ↥(⊤ : Subgroup V) →* ↥(G6.coreMod 24) ⧸
      (golayC ⊔ Subgroup.zpowers (pairVec a b)).subgroupOf (G6.coreMod 24)}
    (h : RealizesBy (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      ρ.range ⊤ ⊥ ρ.rangeRestrict β) (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) {v : V}
    (hv : VecOf (FFModel.golaySec Γ (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec a b)))
      β (pairVec a j) v) (γ : ↥Γ)
    (hγ : ((γ : Equiv.Perm (Fin 24)) a = a ∧ (γ : Equiv.Perm (Fin 24)) b = b) ∨
      ((γ : Equiv.Perm (Fin 24)) a = b ∧ (γ : Equiv.Perm (Fin 24)) b = a)) :
    ρ γ v = v ↔ (γ : Equiv.Perm (Fin 24)) j = j := by
  have hne : a ≠ j := Ne.symm hja
  have hne' : (γ : Equiv.Perm (Fin 24)) a ≠ (γ : Equiv.Perm (Fin 24)) j :=
    (γ : Equiv.Perm (Fin 24)).injective.ne hne
  rw [eq_comm, vecOf_pair_eq_iff_sup h hab hne hne' hv (vecOf_act_pair h hv γ)]
  exact perm_pair_iff_22 hab hja hjb hγ

end CFSG.Quasithin.RonanH15
