module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] {H M S : Subgroup G}

@[expose] def Wcomm (α : Geo H M) : Subgroup G := ⁅Wn α, stab α⁆

@[expose] def Estar (α : Geo H M) : Subgroup G := fixSecIn (stab α) (Zv α) (Wn α)

structure Hyp18 (α β : Geo H M) : Prop where
  card_Vn : Nat.card (Vn β) = 2 ^ 6
  comm_Wn_Qv : ⁅Wn α, Qv α⁆ ≤ Zv α
  sec : IsOrthSec (stab α) (Zv α) (Wcomm α)
  sup_eq : Estar α ⊔ Wcomm α = Wn α
  inf_eq : Estar α ⊓ Wcomm α = Zv α
  Vn_inf_Estar : Vn β ⊓ Estar α = Zv α
  proj : (Vn β ⊔ Estar α) ⊓ Wcomm α = fixSecIn (Qst β) (Zv α) (Wcomm α)
  Vst_normal : Mab α β ≤ Subgroup.normalizer (Vst β : Set G)

@[expose] def Mcent (α : Geo H M) : Subgroup G := Qv α ⊓ Subgroup.centralizer (Wcomm α : Set G)

@[expose] def Qgrp (α β : Geo H M) : Subgroup G := cSecIn (stab α ⊓ stab β) (Zv β) (Vst β)

@[expose] def Xgrp (α β : Geo H M) : Subgroup G := Mab α β ⊔ stab β

structure Out19 (α β : Geo H M) : Prop where
  C_eq : stab α ⊓ stab β ⊓ Subgroup.centralizer (Vst β : Set G) = Cst β
  M_le_C : Mcent α ≤ Cst β
  M_le_centralizer : Mcent α ≤ Subgroup.centralizer (Wn α : Set G)

structure Out20bc (α β : Geo H M) : Prop where
  C_normal : Xgrp α β ≤ Subgroup.normalizer (Cst β : Set G)
  Q_normal : Xgrp α β ≤ Subgroup.normalizer (Qgrp α β : Set G)
  relIndex_C_Q : (Cst β).relIndex (Qgrp α β) = 8
  relIndex_Q_P : (Qgrp α β).relIndex (stab α ⊓ stab β) = 8

structure Out20 (α β : Geo H M) : Prop extends Out20bc α β where
  Q_sup : Qgrp α β ⊔ Qv α = pCoreOf 2 (Mab α β)
  relIndex_inf : (Cst β).relIndex (Qgrp α β ⊓ Qv α) = 2
  comm_le : ⁅Qgrp α β ⊓ Qv α, Mab α β⁆ ≤ Cst β
  relIndex_W : (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) = 2
  not_C_le_M : ¬ Cst β ≤ Mcent α

@[expose] def Claim14 (α : Geo H M) : Prop :=
  ∀ {α' ν ρ : Geo H M}, IsCritPair₁ α α' → ν ∈ nbrs α' → dist α ν = bMin H M - 1 →
    ρ ∈ nbrs ν → dist α ρ = bMin H M - 2 →
    Wn α ≤ stab ρ ∧ (Wn α ⊓ stab ν).relIndex (Wn α) ≤ 2 ∧
      stab ρ ⊓ Subgroup.centralizer (Yv ν : Set G) ≤ stab ν ∧
      Wn α ⊓ Mab ρ ν ≤ Subgroup.centralizer (Yv ν : Set G) ∧ Wn α ⊓ Mab ρ ν ≤ stab ν

@[expose] def Claim15 (α : Geo H M) : Prop :=
  ∀ {α' : Geo H M}, IsCritPair₁ α α' →
    ∃ x ∈ Zv α', x ∉ Qv α ∧ ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α

@[expose] def Claim17 (α : Geo H M) : Prop :=
  ∃ x ∈ stab α, x ∉ Qv α ∧ IsTransvec 1 x (Zv α) (Wn α)

end CFSG.Quasithin.F53.Stellmacher.S43.Even
