module

public import CFSG.Monster.Existence.TwoPoint.LeechFourA

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Generated CFSG.Monster.B.Short CFSG.Monster.B Subgroup

section Generic

variable {G : Type*} [Group G]

theorem leech_mul_self_of_comm {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b) * b := by rw [hab]
    _ = (a * a) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [ha, hb, mul_one]

theorem leech_comm_iff_of_prod {g α β γ x : G} (hx : α * β * γ = x) (hα : α * α = 1)
    (hβ : β * β = 1) :
    (g * α = α * g ∧ g * β = β * g ∧ g * γ = γ * g) ↔
      (g * α = α * g ∧ g * β = β * g ∧ g * x = x * g) := by
  have hγ : γ = β * α * x := by
    calc γ = (β * β) * γ := by rw [hβ, one_mul]
      _ = β * ((α * α) * (β * γ)) := by rw [hα, one_mul, mul_assoc]
      _ = β * α * x := by rw [← hx]; simp only [mul_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← hx]
    exact (Commute.mul_right (Commute.mul_right (show Commute g α from h1)
      (show Commute g β from h2)) (show Commute g γ from h3)).eq
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [hγ]
    exact (Commute.mul_right (Commute.mul_right (show Commute g β from h2)
      (show Commute g α from h1)) (show Commute g x from h3)).eq

theorem leech_zQ_ne_one' {z : G} (hz : z ≠ 1) (r : G) : z * r ≠ r := fun h =>
  hz (mul_eq_right.1 h)

theorem leech_trans_mul_mul {a b c d x : G} (h : a * b = d) (h2 : d * c = x) : a * b * c = x := by
  rw [h, h2]

theorem leech_mul_mul_cancel_of_sq (z : G) {a : G} (h : a * a = 1) : z * a * a = z := by
  rw [mul_assoc, h, mul_one]

end Generic

section PointStab

variable {G : Type} [Group G]

theorem leech_mem_pointStab_triple {α β γ g : G} :
    g ∈ pointStab ({α, β, γ} : Set G) ↔ g * α = α * g ∧ g * β = β * g ∧ g * γ = γ * g := by
  simp only [pointStab, Subgroup.mem_iInf, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, mem_centralizer_singleton_iff]

theorem leech_pointStab_le_cent_prod (α β γ : G) :
    pointStab ({α, β, γ} : Set G) ≤ cent (α * β * γ) := fun g hg => by
  obtain ⟨h1, h2, h3⟩ := leech_mem_pointStab_triple.1 hg
  exact mem_centralizer_singleton_iff.2
    (Commute.mul_right (Commute.mul_right (show Commute g α from h1) (show Commute g β from h2))
      (show Commute g γ from h3)).eq

end PointStab

theorem leech_zQ_ne_one : zQ ≠ 1 := fun h => by
  have := orderOf_zQ
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem leech_add_add_left {a b : L2} : a + b + a = b := by
  rw [add_comm a b, add_assoc, ZModModule.add_self, add_zero]

theorem leech_add_add_right {a b : L2} : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, ZModModule.add_self, zero_add]

theorem leech_add_add_self {a b : L2} : a + b + b = a := by
  rw [add_assoc, ZModModule.add_self, add_zero]

theorem leech_add_self_add {a b : L2} : b + (b + a) = a := by
  rw [← add_assoc, ZModModule.add_self, zero_add]

theorem leech_qL_eq_zero_of_mem_shortSet {v : L2} (h : v ∈ shortSet) : qL v = 0 :=
  h.elim fun _ hu => hu.2 ▸ qL_classOf_minVecs hu.1

theorem leech_isConj_mul
    {q₁ q₂ : Q} (h : phi0 (coordOf (q₂ * q₁)) ∈ shortSet) :
    IsConj tGriess (rhoGriess q₁ * rhoGriess q₂) :=
  (rhoGriess_mul q₂ q₁) ▸ leech_isConj_tGriess_rhoGriess h

theorem leech_phi0_zQ_mul (q : Q) : phi0 (coordOf (zQ * q)) = phi0 (coordOf q) :=
  congrArg phi0 (coordOf_zQ_mul q)

theorem leech_ne_zero_of_mem_shortSet {v : L2} (h : v ∈ shortSet) : v ≠ 0 :=
  h.elim fun _ hu h0 => classOf_ne_zero_of_mem_minVecs hu.1 (hu.2.trans h0)

theorem leech_mem_shortSet_of_eq {a b : L2} (h : a = b) (hb : b ∈ shortSet) : a ∈ shortSet :=
  h ▸ hb

theorem leech_isShortCoord_of_eq {q : Q} {v : L2} (h : phi0 (coordOf q) = v) (hv : v ∈ shortSet) :
    IsShortCoord (coordOf q) :=
  hv.elim fun u hu => ⟨u, hu.1, hu.2.trans h.symm⟩

theorem leech_isLongTriangle_rho
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (hne : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂))
    (hs : phi0 (coordOf r₁) + phi0 (coordOf r₂) ∈ shortSet) :
    IsLongTriangle tGriess
      {rhoGriess r₁, rhoGriess r₂, rhoGriess (zQ * (r₂ * r₁))} := by
  have hv₁ := leech_phi0_ne_zero hr₁
  have hv₂ := leech_phi0_ne_zero hr₂
  have hr₁' : phi0 (coordOf r₁) ∈ shortSet := hr₁
  have hr₂' : phi0 (coordOf r₂) ∈ shortSet := hr₂
  have hs' : phi0 (coordOf r₂) + phi0 (coordOf r₁) ∈ shortSet := by
    rw [add_comm]
    exact hs
  have e21 : phi0 (coordOf (r₂ * r₁)) = phi0 (coordOf r₂) + phi0 (coordOf r₁) :=
    phi0_coordOf_mul r₂ r₁
  have e12 : phi0 (coordOf (r₁ * r₂)) = phi0 (coordOf r₁) + phi0 (coordOf r₂) :=
    phi0_coordOf_mul r₁ r₂
  have es : phi0 (coordOf (zQ * (r₂ * r₁))) = phi0 (coordOf r₂) + phi0 (coordOf r₁) :=
    (leech_phi0_zQ_mul _).trans e21
  have hab : rhoGriess r₁ * rhoGriess r₂ = rhoGriess (r₂ * r₁) := (rhoGriess_mul r₂ r₁).symm
  have p₃ : phi0 (coordOf (zQ * (r₂ * r₁) * r₁)) = phi0 (coordOf r₂) :=
    (phi0_coordOf_mul _ r₁).trans ((congrArg (· + phi0 (coordOf r₁)) es).trans leech_add_add_self)
  have p₄ : phi0 (coordOf (r₁ * (zQ * (r₂ * r₁)))) = phi0 (coordOf r₂) :=
    (phi0_coordOf_mul r₁ _).trans ((congrArg (phi0 (coordOf r₁) + ·) es).trans leech_add_add_right)
  have p₅ : phi0 (coordOf (zQ * (r₂ * r₁) * r₂)) = phi0 (coordOf r₁) :=
    (phi0_coordOf_mul _ r₂).trans ((congrArg (· + phi0 (coordOf r₂)) es).trans leech_add_add_left)
  have p₆ : phi0 (coordOf (r₂ * (zQ * (r₂ * r₁)))) = phi0 (coordOf r₁) :=
    (phi0_coordOf_mul r₂ _).trans ((congrArg (phi0 (coordOf r₂) + ·) es).trans leech_add_self_add)
  refine leech_isLongTriangle (leech_isConj_tGriess_rhoGriess hr₁)
    (leech_isConj_tGriess_rhoGriess hr₂)
    (leech_isConj_tGriess_rhoGriess (r := zQ * (r₂ * r₁)) (leech_isShortCoord_of_eq es hs'))
    (fun h => hne (congrArg (fun q => phi0 (coordOf q)) (rhoGriess_injective h)))
    (fun h => hv₂ (by
      have h1 := congrArg (fun q => phi0 (coordOf q)) (rhoGriess_injective h)
      have h2 : phi0 (coordOf r₁) = phi0 (coordOf r₂) + phi0 (coordOf r₁) := h1.trans es
      exact right_eq_add.1 h2))
    (fun h => hv₁ (by
      have h1 := congrArg (fun q => phi0 (coordOf q)) (rhoGriess_injective h)
      have h2 : phi0 (coordOf r₂) = phi0 (coordOf r₂) + phi0 (coordOf r₁) := h1.trans es
      exact left_eq_add.1 h2))
    (leech_isConj_mul (q₁ := r₁) (q₂ := r₂) (leech_mem_shortSet_of_eq e21 hs'))
    (leech_isConj_mul (q₁ := r₂) (q₂ := r₁) (leech_mem_shortSet_of_eq e12 hs))
    (leech_isConj_mul (q₁ := r₁) (q₂ := zQ * (r₂ * r₁)) (leech_mem_shortSet_of_eq p₃ hr₂'))
    (leech_isConj_mul (q₁ := zQ * (r₂ * r₁)) (q₂ := r₁) (leech_mem_shortSet_of_eq p₄ hr₂'))
    (leech_isConj_mul (q₁ := r₂) (q₂ := zQ * (r₂ * r₁)) (leech_mem_shortSet_of_eq p₅ hr₁'))
    (leech_isConj_mul (q₁ := zQ * (r₂ * r₁)) (q₂ := r₂) (leech_mem_shortSet_of_eq p₆ hr₁'))
    (fun h => hv₂ (by
      have h1 := congrArg (fun q => phi0 (coordOf q)) (rhoGriess_injective (hab.symm.trans h))
      have h2 : phi0 (coordOf r₂) + phi0 (coordOf r₁) = phi0 (coordOf r₁) := e21.symm.trans h1
      exact add_eq_right.1 h2))
    (fun h => hv₁ (by
      have h1 := congrArg (fun q => phi0 (coordOf q)) (rhoGriess_injective (hab.symm.trans h))
      have h2 : phi0 (coordOf r₂) + phi0 (coordOf r₁) = phi0 (coordOf r₂) := e21.symm.trans h1
      exact add_eq_left.1 h2))
    (fun h => leech_zQ_ne_one' leech_zQ_ne_one (r₂ * r₁)
      (rhoGriess_injective (hab.symm.trans h)).symm)


theorem leech_mul_self_of_isShortCoord {r : Q} (h : IsShortCoord (coordOf r)) : r * r = 1 :=
  (mul_self_eq_one_iff_qL r).2 (leech_qL_phi0_eq_zero h)

theorem leech_prod_rho_aux (c r₁ r₂ : Q) (hq₁ : r₁ * r₁ = 1) (hq₂ : r₂ * r₂ = 1)
    (hcomm : r₁ * r₂ = r₂ * r₁) :
    rhoGriess r₁ * rhoGriess r₂ * rhoGriess (c * (r₂ * r₁)) = rhoGriess c := by
  have hc' : r₂ * r₁ = r₁ * r₂ := hcomm.symm
  have hsq := leech_mul_self_of_comm (G := Q) hq₂ hq₁ hc'
  have e := leech_mul_mul_cancel_of_sq (G := Q) c hsq
  exact leech_trans_mul_mul (G := MGriess) (rhoGriess_mul r₂ r₁).symm
    ((rhoGriess_mul (c * (r₂ * r₁)) (r₂ * r₁)).symm.trans (congrArg rhoGriess e))

theorem leech_prod_rho_triangle {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (hcomm : r₁ * r₂ = r₂ * r₁) :
    rhoGriess r₁ * rhoGriess r₂ * rhoGriess (zQ * (r₂ * r₁)) = xGriess :=
  (leech_prod_rho_aux zQ r₁ r₂ (leech_mul_self_of_isShortCoord hr₁)
    (leech_mul_self_of_isShortCoord hr₂) hcomm).trans rhoGriess_zQ

theorem leech_mem_pointStab_iff {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (hcomm : r₁ * r₂ = r₂ * r₁) (g : MGriess) :
    g ∈ pointStab ({rhoGriess r₁, rhoGriess r₂, rhoGriess (zQ * (r₂ * r₁))} : Set MGriess) ↔
      g * rhoGriess r₁ = rhoGriess r₁ * g ∧ g * rhoGriess r₂ = rhoGriess r₂ * g ∧
        g * xGriess = xGriess * g := by
  have hα : rhoGriess r₁ * rhoGriess r₁ = 1 :=
    leech_rhoGriess_mul_self (leech_mul_self_of_isShortCoord hr₁)
  have hβ : rhoGriess r₂ * rhoGriess r₂ = 1 :=
    leech_rhoGriess_mul_self (leech_mul_self_of_isShortCoord hr₂)
  have hx : rhoGriess r₁ * rhoGriess r₂ * rhoGriess (zQ * (r₂ * r₁)) = xGriess :=
    leech_prod_rho_triangle hr₁ hr₂ hcomm
  exact (leech_mem_pointStab_triple (G := MGriess)).trans
    (leech_comm_iff_of_prod (G := MGriess) hx hα hβ)

theorem leech_longTriangle_shape_of_rep
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂)) (hne : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂))
    (hs : phi0 (coordOf r₁) + phi0 (coordOf r₂) ∈ shortSet) :
    IsLongTriangle tGriess
        {rhoGriess r₁, rhoGriess r₂, rhoGriess (zQ * (r₂ * r₁))} ∧
      rhoGriess r₁ * rhoGriess r₂ * rhoGriess (zQ * (r₂ * r₁)) = xGriess ∧
      HasLayeredTwoShape
        (pointStab ({rhoGriess r₁, rhoGriess r₂, rhoGriess (zQ * (r₂ * r₁))} : Set MGriess)) 3 20
        fun X _ => Nonempty (X ≃* ↥(Kstab (phi0 (coordOf r₁)) ⊓ Kstab (phi0 (coordOf r₂)))) := by
  have hbL : bL (phi0 (coordOf r₁)) (phi0 (coordOf r₂)) = 0 :=
    (bL_eq_qL_add_of_short hr₁ hr₂).trans (leech_qL_eq_zero_of_mem_shortSet hs)
  have hcomm : r₁ * r₂ = r₂ * r₁ := (commute_iff_bL r₁ r₂).2 hbL
  refine ⟨leech_isLongTriangle_rho hr₁ hr₂ hne hs, leech_prod_rho_triangle hr₁ hr₂ hcomm, ?_⟩
  exact HasLayeredTwoShape.of_mulEquiv (H := leechJ r₁ r₂)
    (H' := pointStab ({rhoGriess r₁, rhoGriess r₂, rhoGriess (zQ * (r₂ * r₁))} : Set MGriess))
    (equivLeechJ (leech_mem_pointStab_iff hr₁ hr₂ hcomm)).symm
    (fun _ _ _ _ e ⟨e'⟩ => ⟨e.symm.trans e'⟩) (leechJ_layered_shape hr₁ hr₂ hne hbL)

theorem leech_longTriangle_shape_gen
    {v₁ v₂ : L2} (h₁ : v₁ ∈ shortSet) (h₂ : v₂ ∈ shortSet)
    (h12 : v₁ + v₂ ∈ shortSet) :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab v₁ ⊓ Kstab v₂)) := by
  obtain ⟨r₁, hr₁, rfl⟩ := leech_exists_short_rep h₁
  obtain ⟨r₂, hr₂, rfl⟩ := leech_exists_short_rep h₂
  have hne : phi0 (coordOf r₁) ≠ phi0 (coordOf r₂) := fun h =>
    leech_ne_zero_of_mem_shortSet h12 (by rw [← h]; exact ZModModule.add_self _)
  obtain ⟨hT, hx, hS⟩ := leech_longTriangle_shape_of_rep hr₁ hr₂ hne h12
  exact ⟨_, _, _, hT, hx, hS⟩

theorem leech_longTriangle_shape
    (v₂ : L2) (h₂ : v₂ ∈ shortSet) (h12 : Co2.v0 + v₂ ∈ shortSet) :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab v₂)) :=
  leech_longTriangle_shape_gen classOf_vMinus_mem_shortSet h₂ h12

theorem pCore_eq_of_quotient {G X : Type*} [Group G] [Group X] (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 N) (e : G ⧸ N ≃* X)
    (hX : ∀ P : Subgroup X, P.Normal → IsPGroup 2 P → P = ⊥) : pCore 2 G = N := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hN⟩)
  let f : G →* X := (e : G ⧸ N →* X).comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hn : ((pCore 2 G).map f).Normal := Subgroup.Normal.map pCore_normal f hf
  have hp : IsPGroup 2 ((pCore 2 G).map f) := IsPGroup.map pCore_isPGroup f
  have hbot := hX _ hn hp
  intro g hg
  have h1 : f g ∈ (pCore 2 G).map f := ⟨g, hg, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (QuotientGroup.mk' N) g = 1 := e.injective (h1.trans (map_one e).symm)
  exact (QuotientGroup.eq_one_iff g).1 h2

theorem leech_longTriangle_pCore_gen
    {v₁ v₂ : L2} (h₁ : v₁ ∈ shortSet) (h₂ : v₂ ∈ shortSet)
    (h12 : v₁ + v₂ ∈ shortSet)
    (hX : ∀ P : Subgroup ↥(Kstab v₁ ⊓ Kstab v₂), P.Normal → IsPGroup 2 P → P = ⊥) :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab v₁ ⊓ Kstab v₂)) ∧
        pCore 2 ↥(pointStab ({α, β, γ} : Set MGriess)) = N := by
  obtain ⟨α, β, γ, hT, hx, N, hN, N₀, hN₀, hle, hE, hc₀, hQ, hc, ⟨e⟩⟩ :=
    leech_longTriangle_shape_gen h₁ h₂ h12
  have : N.Normal := hN
  exact ⟨α, β, γ, hT, hx, N, hN, N₀, hN₀, hle, hE, hc₀, hQ, hc, ⟨e⟩,
    pCore_eq_of_quotient N (IsPGroup.of_card hc) e hX⟩

theorem leech_longTriangle_pCore
    (v₂ : L2) (h₂ : v₂ ∈ shortSet) (h12 : Co2.v0 + v₂ ∈ shortSet)
    (hX : ∀ P : Subgroup ↥(Kstab Co2.v0 ⊓ Kstab v₂), P.Normal → IsPGroup 2 P → P = ⊥) :
    ∃ α β γ : MGriess, IsLongTriangle tGriess {α, β, γ} ∧ α * β * γ = xGriess ∧
      ∃ (N : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N.Normal)
        (N₀ : Subgroup ↥(pointStab ({α, β, γ} : Set MGriess))) (_ : N₀.Normal), N₀ ≤ N ∧
        IsElementaryAbelian 2 N₀ ∧ Nat.card N₀ = 2 ^ 3 ∧
        IsElementaryAbelian 2 (N ⧸ N₀.subgroupOf N) ∧ Nat.card N = 2 ^ (3 + 20) ∧
        Nonempty (↥(pointStab ({α, β, γ} : Set MGriess)) ⧸ N ≃* ↥(Kstab Co2.v0 ⊓ Kstab v₂)) ∧
        pCore 2 ↥(pointStab ({α, β, γ} : Set MGriess)) = N :=
  leech_longTriangle_pCore_gen classOf_vMinus_mem_shortSet h₂ h12 hX

theorem exists_leech_longTriangle_class :
    ∃ v₂ : L2, v₂ ∈ shortSet ∧ Co2.v0 + v₂ ∈ shortSet := by
  have h : phi0 (coordOf rOneTwo) = Co2.v0 + phi0 (coordOf rTwo) :=
    (congrArg (fun r => phi0 (coordOf r)) rStar_mul_rTwo.symm).trans
      ((phi0_coordOf_mul rStar rTwo).trans (congrArg (· + phi0 (coordOf rTwo))
        phi0_coordOf_rStar))
  exact ⟨phi0 (coordOf rTwo), isShortCoord_rTwo,
    leech_mem_shortSet_of_eq h.symm isShortCoord_rOneTwo⟩

end CFSG.Monster.Existence
