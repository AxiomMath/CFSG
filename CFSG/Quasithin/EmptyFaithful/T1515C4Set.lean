module

public import CFSG.Quasithin.EmptyFaithful.T1515C4Grp
public import CFSG.Quasithin.EmptyFaithful.T1515C6Gl
public import CFSG.Quasithin.EmptyFaithful.T1515A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure Four4Data (V M T : Subgroup G) (hVe : IsElemAbelian 2 V) where
  hMN : M ≤ Subgroup.normalizer (V : Set G)
  hsyl : IsSylowTwoOf T M
  τ : MulAut ↥V
  tt : MulAut ↥V
  g : MulAut ↥V
  ctx : @FourCtx ↥V (commGroupOfElemAbelian hVe) (autOn M V) τ tt
  gen : @FourGen ↥V (commGroupOfElemAbelian hVe) (autOn M V) τ g
  hT : autOn T V = Subgroup.zpowers τ

namespace Four4Data

variable {V M T : Subgroup G} {hVe : IsElemAbelian 2 V} (d : Four4Data V M T hVe)
include d

@[expose] noncomputable def Z₁' : Subgroup V := @zOne ↥V (commGroupOfElemAbelian hVe) d.τ d.g

@[expose] noncomputable def Z₂' : Subgroup V := @zTwo ↥V (commGroupOfElemAbelian hVe) d.τ d.g

@[expose] noncomputable def Z₁ : Subgroup G := d.Z₁'.map V.subtype

@[expose] noncomputable def Z₂ : Subgroup G := d.Z₂'.map V.subtype

@[expose] noncomputable def V₁' : Subgroup V := @fixOf ↥V (commGroupOfElemAbelian hVe) d.g

@[expose] noncomputable def V₂' : Subgroup V :=
  @fixOf ↥V (commGroupOfElemAbelian hVe) (@hOf ↥V (commGroupOfElemAbelian hVe) d.τ d.g)

@[expose] noncomputable def V₁ : Subgroup G := d.V₁'.map V.subtype

@[expose] noncomputable def V₂ : Subgroup G := d.V₂'.map V.subtype

theorem hTN : T ≤ Subgroup.normalizer (V : Set G) := d.hsyl.1.trans d.hMN

theorem Z₁_le_V : d.Z₁ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem Z₂_le_V : d.Z₂ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem V₁_le_V : d.V₁ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem V₂_le_V : d.V₂ ≤ V := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem card_Z₁ [Finite G] : Nat.card d.Z₁ = 2 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₁
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact FourGen.card_zOne d.ctx d.gen

theorem card_Z₂ [Finite G] : Nat.card d.Z₂ = 2 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold Z₂
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact FourGen.card_zTwo d.ctx d.gen

theorem Z₁_ne_bot [Finite G] : d.Z₁ ≠ ⊥ := fun hb => by
  have := d.card_Z₁
  rw [hb, Subgroup.card_bot] at this
  omega

theorem Z₁'_inf_Z₂' [Finite G] : d.Z₁' ⊓ d.Z₂' = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact FourGen.zOne_inf_zTwo d.gen

theorem Z₁_inf_Z₂ [Finite G] : d.Z₁ ⊓ d.Z₂ = ⊥ := by
  unfold Z₁ Z₂
  rw [← Subgroup.map_inf _ _ _ V.subtype_injective, d.Z₁'_inf_Z₂', Subgroup.map_bot]

theorem card_V₁ [Finite G] : Nat.card d.V₁ = 4 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold V₁
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact d.gen.card_U₁

theorem card_V₂ [Finite G] : Nat.card d.V₂ = 4 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  unfold V₂
  rw [Subgroup.card_map_of_injective V.subtype_injective]
  exact d.gen.card_U₂

theorem V₁'_inf_V₂' [Finite G] : d.V₁' ⊓ d.V₂' = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact d.gen.inf

theorem V₁'_sup_V₂' [Finite G] : d.V₁' ⊔ d.V₂' = ⊤ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact d.gen.sup

theorem V₁_inf_V₂ [Finite G] : d.V₁ ⊓ d.V₂ = ⊥ := by
  unfold V₁ V₂
  rw [← Subgroup.map_inf _ _ _ V.subtype_injective, d.V₁'_inf_V₂', Subgroup.map_bot]

theorem V₁_sup_V₂ [Finite G] : d.V₁ ⊔ d.V₂ = V := by
  unfold V₁ V₂
  rw [← Subgroup.map_sup, d.V₁'_sup_V₂', ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem Z₁_le_V₁ [Finite G] : d.Z₁ ≤ d.V₁ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact Subgroup.map_mono inf_le_right

theorem Z₂_le_V₂ [Finite G] : d.Z₂ ≤ d.V₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact Subgroup.map_mono inf_le_right

theorem Z₁_eq : d.Z₁ = d.Z₁'.map V.subtype := rfl

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
    autOn (T ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V = Subgroup.zpowers (d.τ * d.τ) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [d.T_inf_centralizer_Z₁_eq, autOn_preOn_inf, inf_comm, d.hT]
  exact FourGen.T0_eq d.ctx d.gen

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
    rw [this, d.autOn_X, d.hT]
    exact FourGen.Cbar_sup_T d.ctx d.gen
  rw [h2] at h1
  exact h1.symm.trans (preOn_autOn_eq d.hMN le_rfl inf_le_left)

theorem hMN_N : M ≤ Subgroup.normalizer (M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
  intro x hx
  exact le_normalizer_inf_centralizer' (fun y hy => Subgroup.le_normalizer hy) d.hMN hx

theorem mem_S_iff [Finite G] {x : G} (hx : x ∈ T) :
    x ∈ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) ↔
      conjAct V ⟨x, d.hTN hx⟩ ∈ Subgroup.zpowers (d.τ * d.τ) := by
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
    exact FourGen.card_Cbar d.ctx d.gen
  have hcS : Nat.card S = Nat.card (T ⊓ N : Subgroup G) * 2 := by
    rw [card_eq_card_inf_mul_card_autOn hSN, hSC, d.autOn_S]
    congr 1
    exact FourGen.card_zpowers_s d.ctx
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
    have hxT : conjAct V ⟨x, d.hTN hx⟩ ∈ Subgroup.zpowers d.τ := by
      rw [← d.hT]
      exact mem_autOn_of_mem (d.hTN hx) hx
    have hyT' : conjAct V ⟨y, d.hTN hy.1⟩ ∈ Subgroup.zpowers d.τ :=
      (FourGen.zpowers_s_le d.τ) hyT
    rw [zpowers_comm hxT hyT', mul_assoc, mul_inv_cancel, mul_one]
    exact hyT
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (T.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem index_two [Finite G] : (T ⊓ Subgroup.centralizer (d.Z₁ : Set G)).relIndex T = 2 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hST : T ⊓ Subgroup.centralizer (d.Z₁ : Set G) ≤ T := inf_le_left
  have hC : T ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer (d.Z₁ : Set G) :=
    inf_le_inf_left T (Subgroup.centralizer_le d.Z₁_le_V)
  have h1 := relIndex_autOn hST d.hTN hC
  rw [d.autOn_S, d.hT] at h1
  rw [← h1]
  exact FourGen.index_T0 d.ctx

theorem index_v1 [Finite G] :
    (Subgroup.centralizer (d.V₁ : Set G) ⊓ (T ⊓ Subgroup.centralizer (d.Z₁ : Set G))).relIndex
      (T ⊓ Subgroup.centralizer (d.Z₁ : Set G)) = 2 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  set S : Subgroup G := T ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hS
  have hSN : S ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hTN
  set B : Subgroup G := Subgroup.centralizer (d.V₁ : Set G) ⊓ S with hB
  have hBS : B ≤ S := inf_le_right
  have hC : S ⊓ Subgroup.centralizer (V : Set G) ≤ B := by
    intro x hx
    exact ⟨Subgroup.centralizer_le d.V₁_le_V hx.2, hx.1⟩
  have h1 := relIndex_autOn hBS hSN hC
  have hB'' : B = preOn S V (fixingV (d.V₁' : Set V)) := by
    rw [hB, inf_comm]
    exact inf_centralizer_eq_preOn hSN d.V₁'
  have hautB : autOn B V = ⊥ := by
    rw [hB'', autOn_preOn_inf, inf_comm, d.autOn_S]
    exact FourGen.zpowers_s_inf_fixingV d.ctx d.gen
  rw [hautB, d.autOn_S, Subgroup.relIndex_bot_left] at h1
  rw [← h1]
  exact FourGen.card_zpowers_s d.ctx

theorem prime_o2 [Finite G] :
    (Nat.card (oTwoUpper (autOn (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) V))).Prime := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  rw [d.autOn_X]
  show (Nat.card (oTwoUpper (sixCbar (autOn M V) (zOne d.τ d.g)))).Prime
  rw [FourGen.oTwoUpper_Cbar d.ctx d.gen, card_pow_gen d.gen.g3 d.gen.g1]
  exact Nat.prime_three

theorem swap_small [Finite G] {x : G} (hx : x ∈ T)
    (hxS : x ∉ T ⊓ Subgroup.centralizer (d.Z₁ : Set G)) : conjByElt x d.V₂ = d.V₁ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := d.hTN hx
  set a : MulAut V := conjAct V ⟨x, hxN⟩ with ha
  have haT : a ∈ Subgroup.zpowers d.τ := by
    rw [← d.hT]
    exact mem_autOn_of_mem hxN hx
  have hna : a ∉ Subgroup.zpowers (d.τ * d.τ) := fun hs => hxS ((d.mem_S_iff hx).mpr hs)
  have hle : conjByElt x d.V₂ ≤ d.V₁ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨a w, FourGen.swap_mem d.ctx d.gen haT hna hw, ?_⟩
    show ((a w : V) : G) = (MulAut.conj x).toMonoidHom (w : G)
    rw [ha, conj_coe_apply]
    rfl
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  unfold conjByElt
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, d.card_V₁, d.card_V₂]

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

theorem commutator_map_eq_bot [Finite G] {X : Subgroup G} (hXM : X ≤ M) {W : Subgroup V}
    (hX : ∀ a ∈ autOn X V, ∀ w ∈ W, a w = w) : ⁅W.map V.subtype, X⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := d.hMN (hXM hx)
  obtain ⟨w, hw, rfl⟩ := hv
  have h1 : conjAct V ⟨x, hxN⟩ w = w := hX _ (mem_autOn_of_mem hxN hx) w hw
  have h2 : x * (w : G) * x⁻¹ = w := by
    have := congrArg (fun z : V => (z : G)) h1
    simpa [conj_coe_apply] using this
  rw [Subgroup.mem_bot, commutatorElement_def]
  show (w : G) * x * (w : G)⁻¹ * x⁻¹ = 1
  have h3 : (w : G) * x = x * w := by
    calc (w : G) * x = (x * (w : G) * x⁻¹) * x := by rw [h2]
      _ = x * w := by group
  rw [h3]
  group

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

theorem hgord : orderOf d.g = 3 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime d.gen.g3 d.gen.g1

theorem hY_zpowers_U₂ [Finite G] {a : MulAut V} (ha : a ∈ Subgroup.zpowers d.g) {w : V}
    (hw : w ∈ d.V₂') : a w ∈ d.V₂' := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  exact FourGen.zpowers_g_U₂ d.ctx d.gen ha hw

theorem v2_comm [Finite G] :
    ⁅d.V₂, oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))⁆ = d.V₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hXN : (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans d.hMN
  have hX : autOn (oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V =
      Subgroup.zpowers d.g := by
    rw [← A4.oTwoUpper_autOn hXN, d.autOn_X]
    exact FourGen.oTwoUpper_Cbar d.ctx d.gen
  have hXM : oTwoUpper (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ M :=
    (oTwoUpper_le _).trans inf_le_left
  refine d.commutator_map_eq hXM (W := d.V₂') (c := d.g) ?_ ?_ hX ?_
  · exact fun w hw => d.hY_zpowers_U₂ (Subgroup.mem_zpowers _) hw
  · exact fun w hw hgw => FourGen.g_fpf_U₂ d.gen hw hgw
  · intro a ha w hw
    rw [hX] at ha
    exact d.hY_zpowers_U₂ ha hw

theorem autOn_Y [Finite G] :
    autOn (oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V =
      Subgroup.zpowers d.g := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  set X' : Subgroup G := M ⊓ Subgroup.centralizer (d.Z₁ : Set G) with hX'
  have hX'N : X' ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans d.hMN
  have hO : oTwoUpper (autOn X' V) = Subgroup.zpowers d.g := by
    rw [d.autOn_X]
    exact FourGen.oTwoUpper_Cbar d.ctx d.gen
  apply le_antisymm
  ·
    have hYle : oPrimeResidualOf 3 X' ≤ preOn X' V (Subgroup.zpowers d.g) := by
      rw [oPrimeResidualOf, Subgroup.closure_le]
      rintro x ⟨hxX, k, hk⟩
      have hxodd : Odd (orderOf x) := by
        rw [hk]
        exact Odd.pow (by decide)
      have h1 := conjAct_mem_oTwoUpper_autOn hX'N hxX hxodd
      rw [hO] at h1
      exact mem_preOn.mpr ⟨hxX, hX'N hxX, h1⟩
    have h2 : autOn (oPrimeResidualOf 3 X') V ≤ autOn (preOn X' V (Subgroup.zpowers d.g)) V :=
      autOn_le_autOn V hYle
    rw [autOn_preOn_inf] at h2
    exact h2.trans inf_le_left
  ·
    have hcX : d.g ∈ autOn X' V := by
      rw [d.autOn_X]
      exact FourGen.g_mem_Cbar d.ctx d.gen
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
    have hρ : conjAct V ⟨x ^ m, hX'N (X'.pow_mem hxX m)⟩ = d.g ^ m := by
      have : (⟨x ^ m, hX'N (X'.pow_mem hxX m)⟩ : Subgroup.normalizer (V : Set G)) =
          (⟨x, hxN⟩ : Subgroup.normalizer (V : Set G)) ^ m := rfl
      rw [this, map_pow, hxc]
    have hmem : d.g ^ m ∈ autOn (oPrimeResidualOf 3 X') V := by
      rw [← hρ]
      exact mem_autOn_of_mem _ hyY
    have hcop : Nat.Coprime m (orderOf d.g) := by
      rw [d.hgord]
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
  have hY' : autOn Y V = Subgroup.zpowers d.g := d.autOn_Y
  have hTo : Subgroup.zpowers (d.τ * d.τ) ≤ autOn K₀ V := by
    rw [← d.autOn_S]
    exact autOn_le_autOn V (le_sup_right.trans le_sup_left)
  have hOo : Subgroup.zpowers d.g ≤ autOn K₀ V := by
    rw [← hY']
    exact autOn_le_autOn V le_sup_right
  have hCb : autOn X' V ≤ autOn K₀ V := by
    have hCe : @sixCbar ↥V (commGroupOfElemAbelian hVe) (autOn M V) d.Z₁' =
        Subgroup.zpowers d.g ⊔ Subgroup.zpowers (d.τ * d.τ) := FourGen.Cbar_eq d.ctx d.gen
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
  exact card_pow_gen d.gen.g3 d.gen.g1

theorem Y_facts [Finite G] :
    ⁅d.V₂, oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))⁆ = d.V₂ ∧
      oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤
        Subgroup.normalizer (d.V₂ : Set G) ∧
      ⁅d.V₁, oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))⁆ = ⊥ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hYM : oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G)) ≤ M := by
    rw [oPrimeResidualOf, Subgroup.closure_le]
    exact fun x hx => hx.1.1
  have hY := d.autOn_Y
  have hinv : ∀ a ∈ autOn (oPrimeResidualOf 3 (M ⊓ Subgroup.centralizer (d.Z₁ : Set G))) V,
      ∀ w ∈ d.V₂', a w ∈ d.V₂' := by
    intro a ha w hw
    rw [hY] at ha
    exact d.hY_zpowers_U₂ ha hw
  refine ⟨d.commutator_map_eq hYM (W := d.V₂') (c := d.g)
    (fun w hw => d.hY_zpowers_U₂ (Subgroup.mem_zpowers _) hw)
    (fun w hw hgw => FourGen.g_fpf_U₂ d.gen hw hgw) hY hinv,
    d.le_normalizer_map hYM hinv, ?_⟩
  refine d.commutator_map_eq_bot hYM (W := d.V₁') ?_
  intro a ha w hw
  rw [hY] at ha
  exact apply_eq_of_mem_zpowers (show d.g w = w from hw) ha

theorem mem_S₂_iff [Finite G] {x : G} (hx : x ∈ T) :
    x ∈ T ⊓ Subgroup.centralizer (d.Z₂ : Set G) ↔
      conjAct V ⟨x, d.hTN hx⟩ ∈ Subgroup.zpowers (d.τ * d.τ) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hxN := d.hTN hx
  constructor
  · intro h
    have h1 : conjAct V ⟨x, hxN⟩ ∈ fixingV (d.Z₂' : Set V) :=
      (mem_centralizer_map_iff hxN).mp h.2
    by_contra hnot
    have haT : conjAct V ⟨x, hxN⟩ ∈ Subgroup.zpowers d.τ := by
      rw [← d.hT]
      exact mem_autOn_of_mem hxN hx
    obtain ⟨z, hz, hz1⟩ := FourGen.exists_ne_one_zTwo d.ctx d.gen
    have h2 : conjAct V ⟨x, hxN⟩ z = z := h1 z hz
    have h3 := FourGen.swap_mem d.ctx d.gen haT hnot hz.2
    rw [h2] at h3
    exact hz1 (FourGen.g_fpf_U₂ d.gen hz.2 h3)
  · intro h
    refine ⟨hx, ?_⟩
    exact (mem_centralizer_map_iff (Z := d.Z₂') hxN).mpr
      (fun z hz => apply_eq_of_mem_zpowers (show (d.τ * d.τ) z = z from hz.1) h)

omit d in
theorem omegaOneCenter_eq_inf {V T : Subgroup G} (hVT : V ≤ T) (hVe : IsElemAbelian 2 V)
    (hZV : quasithinOmegaOneCenter T ≤ V) :
    quasithinOmegaOneCenter T = V ⊓ Subgroup.centralizer (T : Set G) := by
  apply le_antisymm
  · refine le_inf hZV ?_
    intro z hz
    exact (quasithinOmegaOneCenter_le_center T hz).2
  · intro v hv
    refine Subgroup.subset_closure ⟨⟨hVT hv.1, hv.2⟩, hVe.2 v hv.1⟩

theorem diagonal [Finite G] (hVT : V ≤ T) (hZV : quasithinOmegaOneCenter T ≤ V) :
    Subgroup.centralizer (d.Z₁ : Set G) ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
        Subgroup.centralizer (d.Z₁ : Set G) ⊓ Subgroup.centralizer (d.Z₂ : Set G) ∧
      T ⊓ Subgroup.centralizer (d.Z₁ : Set G) = T ⊓ Subgroup.centralizer (d.Z₂ : Set G) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  refine ⟨?_, ?_⟩
  · have hZc : quasithinOmegaOneCenter T =
        (@fixV ↥V _ (autOn T V)).map V.subtype := by
      rw [omegaOneCenter_eq_inf hVT hVe hZV, S152N2.map_fixV_autOn hVe d.hTN]
    ext k
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hk1, hkZ⟩
      refine ⟨hk1, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hk1 hkZ ⊢
      rintro _ ⟨w₂, hw₂, rfl⟩
      have hw₁ : d.τ w₂ ∈ d.Z₁' := FourGen.tau_zTwo d.gen hw₂
      have hfix : d.τ w₂ * w₂ ∈ fixV (autOn T V) := by
        rw [d.hT]
        exact FourGen.diag_fix hw₂
      set w₁ := d.τ w₂ with hw₁def
      have hc1 : ((V.subtype w₁ : G)) * k = k * (V.subtype w₁ : G) :=
        hk1 _ ⟨w₁, hw₁, rfl⟩
      have hmem : (V.subtype (w₁ * w₂) : G) ∈ (quasithinOmegaOneCenter T : Set G) := by
        rw [SetLike.mem_coe, hZc]
        exact ⟨w₁ * w₂, hfix, rfl⟩
      have hc2 : ((V.subtype (w₁ * w₂) : G)) * k = k * (V.subtype (w₁ * w₂) : G) := hkZ _ hmem
      have hcom1 : Commute (V.subtype w₁ : G) k := hc1
      have hcom2 : Commute (V.subtype (w₁ * w₂) : G) k := hc2
      have hcom3 : Commute ((V.subtype w₁ : G)⁻¹ * (V.subtype (w₁ * w₂) : G)) k :=
        hcom1.inv_left.mul_left hcom2
      have heq : (V.subtype w₁ : G)⁻¹ * (V.subtype (w₁ * w₂) : G) = (V.subtype w₂ : G) := by
        simp
      rw [heq] at hcom3
      exact hcom3
    · rintro ⟨hk1, hk2⟩
      refine ⟨hk1, ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hk1 hk2 ⊢
      intro z hz
      rw [SetLike.mem_coe, hZc] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hw' : w ∈ fixV (Subgroup.zpowers d.τ) := by
        rw [← d.hT]
        exact hw
      obtain ⟨y, hy, z', hz', hyz⟩ := Subgroup.mem_sup.mp (FourGen.fixV_tau_le d.gen hw')
      have hcy : Commute (V.subtype y : G) k := hk1 _ ⟨y, hy, rfl⟩
      have hcz : Commute (V.subtype z' : G) k := hk2 _ ⟨z', hz', rfl⟩
      have : (V.subtype w : G) = (V.subtype y : G) * (V.subtype z' : G) := by
        rw [← hyz]
        simp
      rw [this]
      exact hcy.mul_left hcz
  · ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxT, hxc⟩
      exact ⟨hxT, ((d.mem_S₂_iff hxT).mpr ((d.mem_S_iff hxT).mp ⟨hxT, hxc⟩)).2⟩
    · rintro ⟨hxT, hxc⟩
      exact ⟨hxT, ((d.mem_S_iff hxT).mpr ((d.mem_S₂_iff hxT).mp ⟨hxT, hxc⟩)).2⟩

theorem vE_eq [Finite G] (hJ : autOn (thompsonJi T 1) V = Subgroup.zpowers (d.τ * d.τ)) :
    V ⊓ Subgroup.centralizer (thompsonJi T 1 : Set G) = d.Z₁ ⊔ d.Z₂ := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hJT : thompsonJi T 1 ≤ T := iSup₂_le fun _ hA => hA.1
  have hJN : thompsonJi T 1 ≤ Subgroup.normalizer (V : Set G) := hJT.trans d.hTN
  rw [← S152N2.map_fixV_autOn hVe hJN, hJ, FourGen.fixV_zpowers_s d.gen, Subgroup.map_sup]
  rfl

theorem setting_of [Finite G] {Mc : Subgroup G} (h4 : Ce15Four T Mc M) (hVeq : V = V154 T Mc M)
    (hVZ : V154 T Mc M = VZ T M) (hCV : Subgroup.centralizer (V : Set G) ≤ Mc) (hTMc : T ≤ Mc)
    (hMne : ¬ M ≤ Mc)
    (hJ : autOn (thompsonJi T 1) V = Subgroup.zpowers (d.τ * d.τ))
    (hVT : V ≤ T) (hZV : quasithinOmegaOneCenter T ≤ V)
    (hpsub : ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ∃ Y' : Subgroup G,
      Y' ≤ M ⊓ g1_1516 d.Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧ IsPGroup p Y' ∧
        ((s1516 T d.Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T d.Z₁ : Set G)) ∧
        ⁅d.V₂, Y'⁆ = d.V₂) :
    Setting1516X T Mc M d.Z₁ d.Z₂ d.V₁ d.V₂ := by
  subst hVeq
  have hvE : vE1516 T Mc M = d.Z₁ ⊔ d.Z₂ := d.vE_eq hJ
  have hnot7 : ¬ Ce15Seven T Mc M := h4.not_seven
  have hV16 : Nat.card (V154 T Mc M) = 16 := h4.card_eq
  refine
    { ce15 := Or.inl h4
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
      z2_le_v2 := fun _ => d.Z₂_le_V₂
      decomp_seven := fun h7 => absurd h7 hnot7
      decomp_other := fun _ => ⟨d.V₁_le_V, d.Z₁_le_V₁, d.V₁_sup_V₂, d.V₁_inf_V₂⟩
      swap_small := fun _ _ t ht htS => d.swap_small ht htS
      ranks_four := fun _ => ⟨d.card_V₁, d.card_V₂, d.card_Z₁, d.card_Z₂⟩
      ranks_six := fun ⟨p, _, h6⟩ => absurd (h6.card_eq.symm.trans hV16) (by norm_num)
      ranks_seven := fun h7 => absurd h7 hnot7
      seven_P := fun h7 => absurd h7 hnot7
      index_two := fun _ _ => d.index_two
      diagonal := fun _ _ => d.diagonal hVT hZV
      index_v1 := fun _ _ => d.index_v1
      y_facts := fun _ => ⟨⟨d.card_autOn_Y, d.not_Y_le_mZ hCV hTMc hMne, (d.Y_facts).1,
        (d.Y_facts).2.1⟩, fun _ => (d.Y_facts).2.2⟩
      p_sub := hpsub }

end Four4Data

end CFSG.Quasithin
