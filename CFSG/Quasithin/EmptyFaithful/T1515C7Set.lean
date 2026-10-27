module

public import CFSG.Quasithin.EmptyFaithful.T1515C7Tb
public import CFSG.Quasithin.EmptyFaithful.T1515C6Gl
public import CFSG.Quasithin.EmptyFaithful.T1515A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure Seven7Data (V M T : Subgroup G) (hVe : IsElemAbelian 2 V) where
  hMN : M ≤ Subgroup.normalizer (V : Set G)
  hsyl : IsSylowTwoOf T M
  τ : MulAut ↥V
  x : MulAut ↥V
  y : MulAut ↥V
  z : MulAut ↥V
  tt : MulAut ↥V
  p : MulAut ↥V
  ctx : @SevenCtx ↥V (commGroupOfElemAbelian hVe) (autOn M V) (autOn T V) tt
  gen : @SevenGen ↥V (commGroupOfElemAbelian hVe) (autOn M V) (autOn T V) τ x y z
  hp : p ∈ oTwoUpper (autOn M V)
  htp : tt = p * τ

namespace Seven7Data

variable {V M T : Subgroup G} {hVe : IsElemAbelian 2 V} (d : Seven7Data V M T hVe)
include d

@[expose] noncomputable def Z₁' : Subgroup V := @fixOf ↥V (commGroupOfElemAbelian hVe) d.y

@[expose] noncomputable def Z₂' : Subgroup V := @fixOf ↥V (commGroupOfElemAbelian hVe) d.x

@[expose] noncomputable def Z₁ : Subgroup G := d.Z₁'.map V.subtype

@[expose] noncomputable def Z₂ : Subgroup G := d.Z₂'.map V.subtype

@[expose] noncomputable def V₂' : Subgroup V := (@normOf ↥V (commGroupOfElemAbelian hVe) d.y).ker

@[expose] noncomputable def V₂ : Subgroup G := d.V₂'.map V.subtype

theorem hTN : T ≤ Subgroup.normalizer (V : Set G) := d.hsyl.1.trans d.hMN

theorem Z₁_le_V : d.Z₁ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem Z₂_le_V : d.Z₂ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem V₂_le_V : d.V₂ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem card_Z₁ [Finite G] : Nat.card d.Z₁ = 4 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₁
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact (SevenGen.card_fix_y' d.ctx d.gen).1

theorem card_Z₂ [Finite G] : Nat.card d.Z₂ = 4 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₂
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact SevenGen.card_fix_x d.ctx d.gen

theorem Z₁_ne_bot [Finite G] : d.Z₁ ≠ ⊥ := fun hb => by
  have := d.card_Z₁
  rw [hb, Subgroup.card_bot] at this
  omega

theorem Z₁_inf_Z₂ [Finite G] : d.Z₁ ⊓ d.Z₂ = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₁ Z₂
  rw [← Subgroup.map_inf _ _ _ V.subtype_injective]
  have : d.Z₁' ⊓ d.Z₂' = ⊥ := SevenGen.fix_y_inf_fix_x d.ctx d.gen
  rw [this, Subgroup.map_bot]

theorem card_Z₁_sup_Z₂ [Finite G] : Nat.card (d.Z₁ ⊔ d.Z₂ : Subgroup G) = 16 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₁ Z₂
  rw [← Subgroup.map_sup, Subgroup.card_map_of_injective V.subtype_injective]
  exact SevenGen.card_fix_y_sup_fix_x d.ctx d.gen

theorem card_V₂ [Finite G] : Nat.card d.V₂ = 16 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold V₂
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  have h1 := card_eq_fixOf_mul_ker (SevenGen.y3 d.ctx d.gen) d.ctx.sq
  rw [d.ctx.card_V, (SevenGen.card_fix_y' d.ctx d.gen).1] at h1
  exact (show Nat.card (normOf d.y).ker = 16 by omega)

theorem Z₁'_inf_V₂' [Finite G] : d.Z₁' ⊓ d.V₂' = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact fixOf_inf_ker d.ctx.sq

theorem Z₁'_sup_V₂' [Finite G] : d.Z₁' ⊔ d.V₂' = ⊤ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact fixOf_sup_ker (SevenGen.y3 d.ctx d.gen) d.ctx.sq

theorem Z₁_inf_V₂ [Finite G] : d.Z₁ ⊓ d.V₂ = ⊥ := by
  unfold Z₁ V₂
  rw [← Subgroup.map_inf _ _ _ V.subtype_injective, d.Z₁'_inf_V₂', Subgroup.map_bot]

theorem Z₁_sup_V₂ [Finite G] : d.Z₁ ⊔ d.V₂ = V := by
  unfold Z₁ V₂
  rw [← Subgroup.map_sup, d.Z₁'_sup_V₂', ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem inf_centralizer_Z₁_eq [Finite G] :
    M ⊓ Subgroup.centralizer (d.Z₁ : Set G) = preOn M V (fixingV (d.Z₁' : Set V)) :=
  inf_centralizer_eq_preOn d.hMN d.Z₁'

theorem T_inf_centralizer_Z₁_eq [Finite G] :
    T ⊓ Subgroup.centralizer (d.Z₁ : Set G) = preOn T V (fixingV (d.Z₁' : Set V)) :=
  inf_centralizer_eq_preOn d.hTN d.Z₁'

theorem autOn_X [Finite G] :
    autOn (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V =
      @sixCbar ↥V (commGroupOfElemAbelian hVe) (autOn M V) d.Z₁' := by
  rw [d.inf_centralizer_Z₁_eq, autOn_preOn_inf, inf_comm]
  rfl

theorem autOn_S [Finite G] :
    autOn (T ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V = Subgroup.zpowers d.τ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [d.T_inf_centralizer_Z₁_eq, autOn_preOn_inf, inf_comm]
  exact SevenGen.T0_eq d.ctx d.gen

theorem centralizer_V_le_X : M ⊓ Subgroup.centralizer (V : Set G) ≤
    M ⊓ Subgroup.centralizer (d.Z₁ : Set G) :=
  inf_le_inf_left M (Subgroup.centralizer_le d.Z₁_le_V)

theorem caseI [Finite G] : (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ⊔ T = M := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hX : M ⊓ Subgroup.centralizer (d.Z₁ : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans d.hMN
  have hle : (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ⊔ T ≤ M := sup_le inf_le_left d.hsyl.1
  have hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ⊔ T :=
    d.centralizer_V_le_X.trans le_sup_left
  have h1 := preOn_autOn_eq d.hMN hle hC
  have h2 : autOn ((M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ⊔ T) V = autOn M V := by
    have hTN := d.hTN
    have : autOn ((M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ⊔ T) V =
        autOn (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V ⊔ autOn T V := by
      unfold autOn
      rw [Subgroup.subgroupOf_sup hX hTN, Subgroup.map_sup]
    rw [this, d.autOn_X]
    exact SevenGen.Cbar_sup_T d.ctx d.gen
  rw [h2] at h1
  exact h1.symm.trans (preOn_autOn_eq d.hMN le_rfl inf_le_left)

theorem hMN_N : M ≤ Subgroup.normalizer (M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  intro x hx
  exact le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) d.hMN hx

theorem mem_S_iff [Finite G] {x : G} (hx : x ∈ T) :
    x ∈ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) ↔
      conjAct V ⟨x, d.hTN hx⟩ ∈ Subgroup.zpowers d.τ := by
  constructor
  · intro h
    rw [← d.autOn_S]
    exact mem_autOn_of_mem (d.hTN hx) h
  · intro h
    rw [← d.autOn_S] at h
    have hC : T ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) :=
      inf_le_inf_left T (Subgroup.centralizer_le d.Z₁_le_V)
    exact mem_of_conjAct_mem_autOn d.hTN inf_le_left hC hx h

theorem sylow [Finite G] :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer (d.Z₁ : Set G))
      (Subgroup.centralizer (d.Z₁ : Set G) ⊓ M) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [inf_comm (Subgroup.centralizer (d.Z₁ : Set G)) M]
  set S : Subgroup G := T ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hS
  set X : Subgroup G := M ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hX
  set N : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hN
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hTN
  have hSX : S ≤ X := le_inf (inf_le_left.trans d.hsyl.1) inf_le_right
  have hCV : Subgroup.centralizer (V : Set G) ≤ Subgroup.centralizer (d.Z₁ : Set G) :=
    Subgroup.centralizer_le d.Z₁_le_V
  have hNsyl : IsSylowTwoOf (T ⊓ N) N :=
    A4.isSylowTwoOf_inf_normal d.hsyl inf_le_left d.hMN_N
  have hXC : X ⊓ Subgroup.centralizer (V : Set G) = N := by
    ext x
    simp only [hX, hN, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCV h.2⟩, h.2⟩⟩
  have hSC : S ⊓ Subgroup.centralizer (V : Set G) = T ⊓ N := by
    ext x
    simp only [hS, hN, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.1, d.hsyl.1 h.1.1, h.2⟩, fun h => ⟨⟨h.1, hCV h.2.2⟩, h.2.2⟩⟩
  have hcX : Nat.card X = Nat.card N * 6 := by
    rw [card_eq_card_inf_mul_card_autOn hXN, hXC, d.autOn_X]
    congr 1
    exact SevenGen.card_Cbar d.ctx d.gen
  have hcS : Nat.card S = Nat.card (T ⊓ N : Subgroup G) * 2 := by
    rw [card_eq_card_inf_mul_card_autOn hSN, hSC, d.autOn_S]
    congr 1
    exact SevenGen.card_zpowers_tau d.gen
  have hN1 : (T ⊓ N).relIndex N * Nat.card (T ⊓ N : Subgroup G) = Nat.card N := by
    have := Subgroup.relIndex_mul_card (T ⊓ N) N
    rwa [inf_of_le_left inf_le_right] at this
  have hS1 : S.relIndex X * Nat.card S = Nat.card X := by
    have := Subgroup.relIndex_mul_card S X
    rwa [inf_of_le_left hSX] at this
  rw [hcX, hcS, ← hN1] at hS1
  have hpos : 0 < Nat.card (T ⊓ N : Subgroup G) := Nat.card_pos
  have hodd : ¬ 2 ∣ (T ⊓ N).relIndex N := hNsyl.2.2
  have hr : S.relIndex X = 3 * (T ⊓ N).relIndex N := by
    have h1 : S.relIndex X * 2 * Nat.card (T ⊓ N : Subgroup G) =
        3 * (T ⊓ N).relIndex N * 2 * Nat.card (T ⊓ N : Subgroup G) := by
      calc S.relIndex X * 2 * Nat.card (T ⊓ N : Subgroup G)
          = S.relIndex X * (Nat.card (T ⊓ N : Subgroup G) * 2) := by ring
        _ = (T ⊓ N).relIndex N * Nat.card (T ⊓ N : Subgroup G) * 6 := hS1
        _ = 3 * (T ⊓ N).relIndex N * 2 * Nat.card (T ⊓ N : Subgroup G) := by ring
    have h2 := Nat.eq_of_mul_eq_mul_right hpos h1
    omega
  refine ⟨hSX, d.hsyl.2.1.to_le inf_le_left, ?_⟩
  show ¬ 2 ∣ S.relIndex X
  rw [hr]
  intro h2
  exact hodd ((Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2))

theorem s_normal [Finite G] : T ≤ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (d.Z₁ : Set G) : Subgroup G) : Set G) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have key : ∀ x ∈ T, ∀ y : G, y ∈ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) →
      x * y * x⁻¹ ∈ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) := by
    intro x hx y hy
    have hxy : x * y * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hx hy.1) (T.inv_mem hx)
    refine (d.mem_S_iff hxy).mpr ?_
    have hyT := (d.mem_S_iff hy.1).mp hy
    have h1 : conjAct V ⟨x * y * x⁻¹, d.hTN hxy⟩ =
        conjAct V ⟨x, d.hTN hx⟩ * conjAct V ⟨y, d.hTN hy.1⟩ * (conjAct V ⟨x, d.hTN hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    rw [h1]
    have hxT : conjAct V ⟨x, d.hTN hx⟩ ∈ autOn T V := mem_autOn_of_mem (d.hTN hx) hx
    have hc : Commute (conjAct V ⟨x, d.hTN hx⟩) d.τ :=
      SevenGen.tau_central d.ctx d.gen _ hxT
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyT
    have hcomm : conjAct V ⟨x, d.hTN hx⟩ * conjAct V ⟨y, d.hTN hy.1⟩ =
        conjAct V ⟨y, d.hTN hy.1⟩ * conjAct V ⟨x, d.hTN hx⟩ := by
      rw [← hm]
      exact (hc.zpow_right m).eq
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hyT
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (T.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem prime_o2 [Finite G] :
    (Nat.card (oTwoUpper (autOn (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V))).Prime := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [d.autOn_X]
  show (Nat.card (oTwoUpper (sixCbar (autOn M V) (fixOf d.y)))).Prime
  rw [SevenGen.oTwoUpper_Cbar d.ctx d.gen,
    card_pow_gen (SevenGen.y3 d.ctx d.gen) (SevenGen.y_ne_one d.gen)]
  exact Nat.prime_three

theorem conj_mem_map [Finite G] {X : Subgroup G} (hXM : X ≤ M) {W : Subgroup V}
    (hW : ∀ a ∈ autOn X V, ∀ w ∈ W, a w ∈ W) {x : G} (hx : x ∈ X) {v : G}
    (hv : v ∈ W.map V.subtype) : x * v * x⁻¹ ∈ W.map V.subtype := by
  have hxN := d.hMN (hXM hx)
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨conjAct V ⟨x, hxN⟩ w, hW _ (mem_autOn_of_mem hxN hx) w hw, ?_⟩
  show ((conjAct V ⟨x, hxN⟩ w : V) : G) = x * (w : G) * x⁻¹
  rw [conj_coe_apply]

theorem le_normalizer_map [Finite G] {X : Subgroup G} (hXM : X ≤ M) {W : Subgroup V}
    (hW : ∀ a ∈ autOn X V, ∀ w ∈ W, a w ∈ W) :
    X ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => d.conj_mem_map hXM hW hx hy
  · intro hy
    have := d.conj_mem_map hXM hW (X.inv_mem hx) hy
    simpa [mul_assoc] using this

theorem commutator_map_eq [Finite G] {X : Subgroup G} (hXM : X ≤ M) {W : Subgroup V} {c : MulAut V}
    (hcW : ∀ w ∈ W, c w ∈ W) (hfix : ∀ w ∈ W, c w = w → w = 1)
    (hX : autOn X V = Subgroup.zpowers c) (hW : ∀ a ∈ autOn X V, ∀ w ∈ W, a w ∈ W) :
    ⁅W.map V.subtype, X⁆ = W.map V.subtype := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv x hx
    have h1 := d.conj_mem_map hXM hW hx hv
    have h2 : (v : G) * (x * v * x⁻¹)⁻¹ ∈ W.map V.subtype :=
      (W.map V.subtype).mul_mem hv ((W.map V.subtype).inv_mem h1)
    have : ⁅v, x⁆ = v * (x * v * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact h2
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨w', hw', hww'⟩ := exists_comm_rep hcW hfix w hw
    have hcX : c ∈ autOn X V := by rw [hX]; exact Subgroup.mem_zpowers c
    obtain ⟨x, hxN, hxX, hxc⟩ := mem_autOn_iff_exists.mp hcX
    have hw'W : (w' : G) ∈ W.map V.subtype := ⟨w', hw', rfl⟩
    have hcomm : ⁅x, (w' : G)⁆ = (V.subtype w : G) := by
      have h1 : ((c w' : V) : G) = x * (w' : G) * x⁻¹ := by
        rw [← hxc, conj_coe_apply]
      have h2 : (V.subtype w : G) = (c w' : G) * (w' : G)⁻¹ := by
        have := congrArg (fun z : V => (z : G)) hww'
        simpa using this.symm
      rw [h2, h1, commutatorElement_def]
    rw [← hcomm, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hxX hw'W

theorem hyord : orderOf d.y = 3 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (SevenGen.y3 d.ctx d.gen) (SevenGen.y_ne_one d.gen)

theorem hY_zpowers_V₂' [Finite G] {a : MulAut V} (ha : a ∈ Subgroup.zpowers d.y) {w : V}
    (hw : w ∈ d.V₂') : a w ∈ d.V₂' := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact apply_mem_ker_normOf (Commute.zpow_self d.y m).eq hw

theorem y_fpf_V₂' [Finite G] {w : V} (hw : w ∈ d.V₂') (hyw : d.y w = w) : w = 1 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have : w ∈ d.Z₁' ⊓ d.V₂' := ⟨hyw, hw⟩
  rw [d.Z₁'_inf_V₂', Subgroup.mem_bot] at this
  exact this

theorem v2_comm [Finite G] :
    ⁅d.V₂, oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))⁆ = d.V₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hXN : (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans d.hMN
  have hX : autOn (oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V =
      Subgroup.zpowers d.y := by
    rw [← A4.oTwoUpper_autOn hXN, d.autOn_X]
    exact SevenGen.oTwoUpper_Cbar d.ctx d.gen
  have hXM : oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ M :=
    (oTwoUpper_le _).trans inf_le_left
  refine d.commutator_map_eq hXM (W := d.V₂') (c := d.y) ?_ ?_ hX ?_
  · exact fun w hw => d.hY_zpowers_V₂' (Subgroup.mem_zpowers _) hw
  · exact fun w hw hgw => d.y_fpf_V₂' hw hgw
  · intro a ha w hw
    rw [hX] at ha
    exact d.hY_zpowers_V₂' ha hw

theorem autOn_Y [Finite G] :
    autOn (oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V =
      Subgroup.zpowers d.y := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  set X' : Subgroup G := M ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hX'
  have hX'N : X' ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hO : oTwoUpper (autOn X' V) = Subgroup.zpowers d.y := by
    rw [d.autOn_X]
    exact SevenGen.oTwoUpper_Cbar d.ctx d.gen
  apply le_antisymm
  ·
    have hYle : oPrimeResidualOf 3 X' ≤ preOn X' V (Subgroup.zpowers d.y) := by
      rw [oPrimeResidualOf, Subgroup.closure_le]
      rintro x ⟨hxX, k, hk⟩
      have hxodd : Odd (orderOf x) := by
        rw [hk]
        exact Odd.pow (by decide)
      have h1 := conjAct_mem_oTwoUpper_autOn hX'N hxX hxodd
      rw [hO] at h1
      exact mem_preOn.mpr ⟨hxX, hX'N hxX, h1⟩
    have h2 : autOn (oPrimeResidualOf 3 X') V ≤ autOn (preOn X' V (Subgroup.zpowers d.y)) V :=
      autOn_le_autOn V hYle
    rw [autOn_preOn_inf] at h2
    exact h2.trans inf_le_left
  ·
    have hcX : d.y ∈ autOn X' V := by
      rw [d.autOn_X]
      exact SevenGen.y_mem_Cbar d.gen
    obtain ⟨x, hxN, hxX, hxc⟩ := mem_autOn_iff_exists.mp hcX
    have hn : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hn
      simpa using hnm
    have hyo : orderOf (x ^ m) = 3 ^ e := by
      rw [orderOf_pow' _ hm0, hnm]
      have : Nat.gcd (3 ^ e * m) m = m := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
      rw [this]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
    have hyY : x ^ m ∈ oPrimeResidualOf 3 X' :=
      Subgroup.subset_closure ⟨X'.pow_mem hxX m, e, hyo⟩
    have hρ : conjAct V ⟨x ^ m, hX'N (X'.pow_mem hxX m)⟩ = d.y ^ m := by
      have : (⟨x ^ m, hX'N (X'.pow_mem hxX m)⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) ^ m := rfl
      rw [this, map_pow, hxc]
    have hmem : d.y ^ m ∈ autOn (oPrimeResidualOf 3 X') V := by
      rw [← hρ]
      exact mem_autOn_of_mem _ hyY
    have hcop : Nat.Coprime m (orderOf d.y) := by
      rw [d.hyord]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm))
    have h3 := A4.mem_zpowers_pow_of_coprime hcop
    exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr hmem) h3)

theorem not_Y_le_mZ [Finite G] {Mc : Subgroup G} (hCV : Subgroup.centralizer (V : Set G) ≤ Mc)
    (hTMc : T ≤ Mc) (hMne : ¬ M ≤ Mc) :
    ¬ oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ mZ1516 Mc d.Z₁ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  intro hY
  set X' : Subgroup G := M ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hX'
  set S : Subgroup G := T ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hS
  set Y : Subgroup G := oPrimeResidualOf 3 X' with hYdef
  have hYMc : Y ≤ Mc := hY.trans (mZ1516_le_mc _ _)
  set K₀ : Subgroup G := (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ S ⊔ Y with hK₀
  have hX'N : X' ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hSX : S ≤ X' := le_inf (inf_le_left.trans d.hsyl.1) inf_le_right
  have hYX : Y ≤ X' := by
    rw [hYdef, oPrimeResidualOf, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hK₀X : K₀ ≤ X' := sup_le (sup_le d.centralizer_V_le_X hSX) hYX
  have hK₀M : K₀ ≤ M := hK₀X.trans inf_le_left
  have hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ K₀ := le_sup_left.trans le_sup_left
  have hY' : autOn Y V = Subgroup.zpowers d.y := d.autOn_Y
  have hTo : Subgroup.zpowers d.τ ≤ autOn K₀ V := by
    rw [← d.autOn_S]
    exact autOn_le_autOn V (le_sup_right.trans le_sup_left)
  have hOo : Subgroup.zpowers d.y ≤ autOn K₀ V := by
    rw [← hY']
    exact autOn_le_autOn V le_sup_right
  have hCb : autOn X' V ≤ autOn K₀ V := by
    have hCe : @sixCbar ↥V (commGroupOfElemAbelian hVe) (autOn M V) d.Z₁' =
        Subgroup.zpowers d.y ⊔ Subgroup.zpowers d.τ := SevenGen.Cbar_eq d.ctx d.gen
    rw [d.autOn_X, hCe]
    exact sup_le hOo hTo
  have h1 := preOn_autOn_eq d.hMN hK₀M hC
  have hX'K : X' ≤ K₀ := by
    intro x hx
    rw [← h1]
    exact mem_preOn.mpr ⟨hx.1, hX'N hx, hCb (mem_autOn_of_mem (hX'N hx) hx)⟩
  have hK₀Mc : K₀ ≤ Mc := by
    refine sup_le (sup_le ?_ ?_) hYMc
    · exact inf_le_right.trans hCV
    · exact inf_le_left.trans hTMc
  have hMMc : M ≤ Mc := by
    have : X' ⊔ T ≤ Mc := sup_le (hX'K.trans hK₀Mc) hTMc
    rw [d.caseI] at this
    exact this
  exact hMne hMMc

theorem card_autOn_Y [Finite G] :
    Nat.card (autOn (oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V) = 3 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [d.autOn_Y]
  exact card_pow_gen (SevenGen.y3 d.ctx d.gen) (SevenGen.y_ne_one d.gen)

theorem Y_facts [Finite G] :
    ⁅d.V₂, oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))⁆ = d.V₂ ∧
      oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤
        Subgroup.normalizer (d.V₂ : Set G) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hYM : oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ M := by
    rw [oPrimeResidualOf, Subgroup.closure_le]
    exact fun x hx => hx.1.1
  have hY := d.autOn_Y
  have hinv : ∀ a ∈ autOn (oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V,
      ∀ w ∈ d.V₂', a w ∈ d.V₂' := by
    intro a ha w hw
    rw [hY] at ha
    exact d.hY_zpowers_V₂' ha hw
  exact ⟨d.commutator_map_eq hYM (W := d.V₂') (c := d.y)
    (fun w hw => d.hY_zpowers_V₂' (Subgroup.mem_zpowers _) hw)
    (fun w hw hgw => d.y_fpf_V₂' hw hgw) hY hinv,
    d.le_normalizer_map hYM hinv⟩

theorem vE_eq [Finite G] (hJ : autOn (thompsonJi T 1) V = Subgroup.zpowers d.τ) :
    V ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) = d.Z₁ ⊔ d.Z₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hJT : thompsonJi T 1 ≤ T := iSup₂_le fun _ hA => hA.1
  have hJN : thompsonJi T 1 ≤ Subgroup.normalizer (V : Set G) := hJT.trans d.hTN
  rw [← S152N2.map_fixV_autOn hVe hJN, hJ, SevenGen.fixV_zpowers_tau,
    SevenGen.fixOf_tau_eq d.ctx d.gen, Subgroup.map_sup]
  rfl

theorem setting_of [Finite G] {Mc : Subgroup G} (h7 : Ce15Seven T Mc M) (hVeq : V = V154 T Mc M)
    (hVZ : V154 T Mc M = VZ T M) (hCV : Subgroup.centralizer (V : Set G) ≤ Mc) (hTMc : T ≤ Mc)
    (hMne : ¬ M ≤ Mc) (hJ : autOn (thompsonJi T 1) V = Subgroup.zpowers d.τ)
    (hpsub : ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ∃ Y' : Subgroup G,
      Y' ≤ M ⊓ g1_1516 d.Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧ IsPGroup p Y' ∧
        ((s1516 T d.Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T d.Z₁ : Set G)) ∧
        ⁅d.V₂, Y'⁆ = d.V₂)
    (hP : Seven1516P T Mc M d.Z₁ d.Z₂ d.V₂) :
    Setting1516X T Mc M d.Z₁ d.Z₂ ⊥ d.V₂ := by
  subst hVeq
  have hvE : vE1516 T Mc M = d.Z₁ ⊔ d.Z₂ := d.vE_eq hJ
  have hV64 : Nat.card (V154 T Mc M) = 64 := h7.card_eq
  refine
    { ce15 := Or.inr (Or.inr h7)
      hV := hVZ
      z1_ne := d.Z₁_ne_bot
      z1_le := hvE ▸ le_sup_left
      z2_le := hvE ▸ le_sup_right
      vE_sup := ⟨hvE.ge, (Setting1516.z_le_vE_of_hV hVZ).trans hvE.le⟩
      vE_sup_small := fun _ => hvE.symm
      vE_inf := d.Z₁_inf_Z₂
      caseI := fun hle => hMne (d.caseI.symm.le.trans (sup_le hle hTMc))
      caseI_small := fun _ => d.caseI
      sylow := d.sylow
      extra_small := fun _ => ⟨d.s_normal, d.prime_o2⟩
      s_normal := d.s_normal
      prime_o2 := d.prime_o2
      v2_le := d.V₂_le_V
      v2_comm := d.v2_comm
      z2_le_v2 := fun h => absurd h7 h
      decomp_seven := fun _ => ⟨d.Z₁_sup_V₂, d.Z₁_inf_V₂⟩
      decomp_other := fun h => absurd h7 h
      swap_small := fun _ h => absurd h7 h
      ranks_four := fun h4 => absurd (h4.card_eq.symm.trans hV64) (by norm_num)
      ranks_six := fun ⟨p, _, h6⟩ => absurd (h6.card_eq.symm.trans hV64) (by norm_num)
      ranks_seven := fun _ => ⟨d.card_Z₁, d.card_Z₂, d.card_V₂, by rw [hvE]; exact d.card_Z₁_sup_Z₂⟩
      seven_P := fun _ => hP
      index_two := fun _ h => absurd h7 h
      diagonal := fun _ h => absurd h7 h
      index_v1 := fun _ h => absurd h7 h
      y_facts := fun _ => ⟨⟨d.card_autOn_Y, d.not_Y_le_mZ hCV hTMc hMne, (d.Y_facts).1,
        (d.Y_facts).2⟩, fun h => absurd h7 h⟩
      p_sub := hpsub }

end Seven7Data

end CFSG.Quasithin
