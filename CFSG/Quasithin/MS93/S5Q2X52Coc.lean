module

public import CFSG.Quasithin.MS93.S5A53
public import CFSG.Quasithin.MS93.S33XKF

public noncomputable section

namespace CFSG.Quasithin.MS93.S5Q2.X52

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Coord

variable (h : PUHyp M T L) (nv : S5.NatVec M T L a)

omit [Fintype F] in
include h in
theorem uCoord_mul_of_mem {n₁ n₂ : G} (hn₁ : n₁ ∈ Uq M T L ⊔ S5.cXL M L)
    (hn₂ : n₂ ∈ Uq M T L ⊔ S5.cXL M L) :
    S5.uCoord nv (n₁ * n₂) = S5.uCoord nv n₁ + S5.uCoord nv n₂ := by
  obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := (S5.mem_Uq_sup_cXL h).1 hn₁
  obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := (S5.mem_Uq_sup_cXL h).1 hn₂
  have hcomm : c₁ * u₂ = u₂ * c₁ := S5.commute_of_mem_Xq (S5.cXL_le hc₁) (h.Uq_le_Xq hu₂)
  have e : u₁ * c₁ * (u₂ * c₂) = (u₁ * u₂) * (c₁ * c₂) := by
    calc u₁ * c₁ * (u₂ * c₂) = u₁ * (c₁ * u₂) * c₂ := by group
      _ = u₁ * (u₂ * c₁) * c₂ := by rw [hcomm]
      _ = _ := by group
  rw [e, S5.uCoord_mul nv ((Uq M T L).mul_mem hu₁ hu₂) ((S5.cXL M L).mul_mem hc₁ hc₂),
    S5.uCoord_mul nv hu₁ hc₁, S5.uCoord_mul nv hu₂ hc₂]
  exact nv.vec_mul ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩

omit [Fintype F] in
include h in
theorem mem_cXL_of_uCoord_eq_zero {n : G} (hn : n ∈ Uq M T L ⊔ S5.cXL M L)
    (h0 : S5.uCoord nv n = 0) : n ∈ S5.cXL M L := by
  obtain ⟨u, hu, c, hc, rfl⟩ := (S5.mem_Uq_sup_cXL h).1 hn
  rw [S5.uCoord_mul nv hu hc] at h0
  have huL := (nv.vec_eq_zero_iff ⟨u, hu⟩).1 h0
  exact (S5.cXL M L).mul_mem ⟨h.Uq_le_Xq hu, huL⟩ hc

omit [Fintype F] in
include h in
theorem uCoord_comm_uq {m : G} (hm : m ∈ M) (u : ↥(Uq M T L)) :
    S5.uCoord nv ⁅m, (u : G)⁆ = MSP.mat (a ⟨m, hm⟩) *ᵥ nv.vec u - nv.vec u := by
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hmu : m * u * m⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hm) u).1 u.2
  have hc : ⁅m, (u : G)⁆ ∈ Uq M T L := by
    rw [commutatorElement_def]
    exact (Uq M T L).mul_mem hmu ((Uq M T L).inv_mem u.2)
  have e : ⁅m, (u : G)⁆ = ⁅m, (u : G)⁆ * 1 := (mul_one _).symm
  rw [e, S5.uCoord_mul nv hc (S5.cXL M L).one_mem]
  have e2 : (⟨⁅m, (u : G)⁆, hc⟩ : ↥(Uq M T L)) = ⟨m * u * m⁻¹, hmu⟩ * u⁻¹ :=
    Subtype.ext (commutatorElement_def _ _)
  rw [e2, nv.vec_mul, nv.vec_inv, nv.vec_conj ⟨m, hm⟩ u hmu, sub_eq_add_neg]

end Coord

section XFix

omit [Finite G] in
theorem comm_mul_eq {m y₁ y₂ : G} (hy₁ : y₁ ∈ Xq M) (hy₂ : ⁅m, y₂⁆ ∈ Xq M) :
    ⁅m, y₁ * y₂⁆ = ⁅m, y₁⁆ * ⁅m, y₂⁆ := by
  have e : ⁅m, y₁ * y₂⁆ = ⁅m, y₁⁆ * (y₁ * ⁅m, y₂⁆ * y₁⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, S5.commute_of_mem_Xq hy₁ hy₂, mul_inv_cancel_right]

variable (h : PUHyp M T L)

include h in
theorem le_normalizer_uq_sup_cXL :
    M ≤ Subgroup.normalizer ((Uq M T L ⊔ S5.cXL M L : Subgroup G) : Set G) :=
  le_normalizer_sup (le_normalizer_Uq h.le_normalizer) (S5.le_normalizer_cXL h)

include h in
theorem uq_sup_cXL_le_xq : Uq M T L ⊔ S5.cXL M L ≤ Xq M := sup_le h.Uq_le_Xq S5.cXL_le

@[expose] def xFix : Subgroup G where
  carrier := {y | y ∈ Xq M ∧ ∀ m ∈ M, ⁅m, y⁆ ∈ Uq M T L ⊔ S5.cXL M L}
  mul_mem' := fun {y₁ y₂} h₁ h₂ => ⟨(Xq M).mul_mem h₁.1 h₂.1, fun m hm => by
    rw [comm_mul_eq h₁.1 (uq_sup_cXL_le_xq h (h₂.2 m hm))]
    exact (Uq M T L ⊔ S5.cXL M L).mul_mem (h₁.2 m hm) (h₂.2 m hm)⟩
  one_mem' := ⟨(Xq M).one_mem, fun m _ => by
    rw [commutatorElement_one_right]
    exact (Uq M T L ⊔ S5.cXL M L).one_mem⟩
  inv_mem' := fun {y} hy => ⟨(Xq M).inv_mem hy.1, fun m hm => by
    have e : ⁅m, y⁻¹⁆ = y⁻¹ * ⁅m, y⁆⁻¹ * y := by
      simp only [commutatorElement_def]
      group
    have hX := uq_sup_cXL_le_xq h ((Uq M T L ⊔ S5.cXL M L).inv_mem (hy.2 m hm))
    rw [e, S5.commute_of_mem_Xq ((Xq M).inv_mem hy.1) hX, inv_mul_cancel_right]
    exact (Uq M T L ⊔ S5.cXL M L).inv_mem (hy.2 m hm)⟩

theorem xFix_le : xFix h ≤ Xq M := fun _ hy => hy.1

theorem uq_le_xFix : Uq M T L ≤ xFix h := fun u hu => ⟨h.Uq_le_Xq hu, fun m hm => by
  have hmu := (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer hm) u).1 hu
  rw [commutatorElement_def]
  exact Subgroup.mem_sup_left ((Uq M T L).mul_mem hmu ((Uq M T L).inv_mem hu))⟩

theorem cXL_le_xFix : S5.cXL M L ≤ xFix h := fun c hc => ⟨S5.cXL_le hc, fun m hm => by
  have hmc := (Subgroup.mem_normalizer_iff.1 (S5.le_normalizer_cXL h hm) c).1 hc
  rw [commutatorElement_def]
  exact Subgroup.mem_sup_right ((S5.cXL M L).mul_mem hmc ((S5.cXL M L).inv_mem hc))⟩

include h in
theorem forall_mem_of_L_T {x : G} (hL : ∀ l ∈ L, ⁅l, x⁆ ∈ Uq M T L ⊔ S5.cXL M L)
    (hT : ∀ t ∈ T, ⁅t, x⁆ ∈ Uq M T L ⊔ S5.cXL M L) :
    ∀ m ∈ M, ⁅m, x⁆ ∈ Uq M T L ⊔ S5.cXL M L := by
  have hNn := le_normalizer_uq_sup_cXL h
  let S : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ⁅m, x⁆ ∈ Uq M T L ⊔ S5.cXL M L}
      mul_mem' := fun {m₁ m₂} h₁ h₂ => ⟨M.mul_mem h₁.1 h₂.1, by
        rw [S5.commutatorElement_mul_left']
        exact (Uq M T L ⊔ S5.cXL M L).mul_mem
          ((Subgroup.mem_normalizer_iff.1 (hNn h₁.1) _).1 h₂.2) h₁.2⟩
      one_mem' := ⟨M.one_mem, by
        rw [commutatorElement_one_left]
        exact (Uq M T L ⊔ S5.cXL M L).one_mem⟩
      inv_mem' := fun {m} hm => ⟨M.inv_mem hm.1, by
        have e : ⁅m⁻¹, x⁆ = m⁻¹ * ⁅m, x⁆⁻¹ * m⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hNn (M.inv_mem hm.1)) _).1
          ((Uq M T L ⊔ S5.cXL M L).inv_mem hm.2)⟩ }
  have hMS : M ≤ S := by
    rw [h.eq_sup]
    exact sup_le (fun l hl => ⟨h.L_le hl, hL l hl⟩) (fun t ht => ⟨h.le ht, hT t ht⟩)
  exact fun m hm => (hMS hm).2

include h in
theorem exists_mem_xFix_not_mem (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hne : Xq M ≠ Uq M T L ⊔ Zq M L) : ∃ x ∈ xFix h, x ∉ Uq M T L ⊔ Zq M L := by
  have hNn := le_normalizer_uq_sup_cXL h
  have hNX := uq_sup_cXL_le_xq h
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := h.isPGroup.to_le h.pCore_le
  have hY : ¬ Xq M ≤ Uq M T L ⊔ S5.cXL M L := fun hle => hne (le_antisymm hle hNX)
  obtain ⟨x, hxX, hxN, hxT⟩ := S5.exists_fixed_mod_of_isPGroup h.isPGroup
    (hQ2.to_le ((sup_le le_rfl hNX).trans (Xq_le_pCoreOf M)))
    (h.le.trans (le_normalizer_Xq M)) (h.le.trans hNn) ((Xq_le M).trans hNn)
    (S5.le_normalizer_of_commute fun n hn y hy => S5.commute_of_mem_Xq (hNX hn) hy) hY
  refine ⟨x, ⟨hxX, forall_mem_of_L_T h (fun l hl => ?_) hxT⟩, hxN⟩
  have := hXL (Subgroup.commutator_mem_commutator hxX hl)
  rw [← commutatorElement_inv]
  exact Subgroup.mem_sup_left ((Uq M T L).inv_mem this)

omit [Fintype F] in
include h in
theorem mem_of_cob (nv : S5.NatVec M T L a) {x : G} (hx : x ∈ xFix h) {m₀ : MSP.V4 F}
    (hcob : ∀ l (hl : l ∈ L), S5.uCoord nv ⁅l, x⁆ =
      MSP.mat (a ⟨l, h.L_le hl⟩) *ᵥ m₀ - m₀) :
    x ∈ Uq M T L ⊔ S5.cXL M L := by
  obtain ⟨u₀, hu₀⟩ := nv.surj (Multiplicative.ofAdd (-m₀))
  have hvu₀ : nv.vec u₀ = -m₀ := by rw [S5.NatVec.vec, hu₀]; rfl
  have hx'X : x * (u₀ : G) ∈ Xq M := (Xq M).mul_mem hx.1 (h.Uq_le_Xq u₀.2)
  have hcomm : ∀ l ∈ L, ⁅l, x * (u₀ : G)⁆ ∈ S5.cXL M L := by
    intro l hl
    have hlM := h.L_le hl
    have hu := (uq_le_xFix h u₀.2).2 l hlM
    rw [comm_mul_eq hx.1 (uq_sup_cXL_le_xq h hu)]
    refine mem_cXL_of_uCoord_eq_zero h nv
      ((Uq M T L ⊔ S5.cXL M L).mul_mem (hx.2 l hlM) hu) ?_
    rw [uCoord_mul_of_mem h nv (hx.2 l hlM) hu, hcob l hl, uCoord_comm_uq h nv hlM u₀, hvu₀,
      Matrix.mulVec_neg]
    abel
  have hL : x * (u₀ : G) ∈ Subgroup.centralizer (L : Set G) :=
    S33.mem_centralizer_of_perfect h.perfect
      (fun b hb b' hb' => S5.commute_of_mem_Xq (S5.cXL_le hb) (S5.cXL_le hb')) inf_le_right
      fun l hl => by
        have := hcomm l hl
        rwa [commutatorElement_def] at this
  have e : x = (x * (u₀ : G)) * (u₀ : G)⁻¹ := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup ⟨hx'X, hL⟩ ((Uq M T L).inv_mem u₀.2)

end XFix

section Count

omit [Finite G] [Fintype F] in
theorem uCoord_of_mem_cXL (nv : S5.NatVec M T L a) {c : G} (hc : c ∈ S5.cXL M L) :
    S5.uCoord nv c = 0 := by
  have := S5.uCoord_mul nv (Uq M T L).one_mem hc
  rw [one_mul] at this
  rw [this]
  exact nv.vec_one

variable (h : PUHyp M T L) (nv : S5.NatVec M T L a) {K : Subgroup G} (hKM : K ≤ M)

@[expose] def phiK : ↥(xFix h) →* Multiplicative (↥K → MSP.V4 F) where
  toFun y := Multiplicative.ofAdd fun κ => S5.uCoord nv ⁅(κ : G), (y : G)⁆
  map_one' := by
    simp only [OneMemClass.coe_one, commutatorElement_one_right, S5.uCoord_one]
    rfl
  map_mul' y₁ y₂ := by
    simp only [Subgroup.coe_mul]
    rw [← ofAdd_add]
    congr 1
    funext κ
    have hκ := hKM κ.2
    rw [Pi.add_apply, comm_mul_eq y₁.2.1 (uq_sup_cXL_le_xq h (y₂.2.2 _ hκ)),
      uCoord_mul_of_mem h nv (y₁.2.2 _ hκ) (y₂.2.2 _ hκ)]

omit [Fintype F] in
theorem phiK_apply (y : ↥(xFix h)) (κ : ↥K) :
    Multiplicative.toAdd (phiK h nv hKM y) κ = S5.uCoord nv ⁅(κ : G), (y : G)⁆ := rfl

omit [Fintype F] in
theorem relIndex_mul_card_range_le :
    (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) *
      Nat.card (Set.range (phiK h nv hKM)) ≤
      (Subgroup.centralizer (K : Set G)).relIndex (Xq M) := by
  set H := (Subgroup.centralizer (K : Set G)).subgroupOf (xFix h) with hH
  set N := (phiK h nv hKM).ker with hN
  have hHN : H ≤ N := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext κ
    rw [phiK_apply]
    have hc : ⁅(κ : G), (y : G)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hy) κ κ.2
    rw [hc, S5.uCoord_one]
    rfl
  have hZN : (Zq M L).subgroupOf (xFix h) ≤ N := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext κ
    rw [phiK_apply]
    have hyZ : (y : G) ∈ S5.cXL M L := Subgroup.mem_subgroupOf.1 hy
    have hκy := (Subgroup.mem_normalizer_iff.1 (S5.le_normalizer_cXL h (hKM κ.2)) _).1 hyZ
    have hc : ⁅(κ : G), (y : G)⁆ ∈ S5.cXL M L := by
      rw [commutatorElement_def]
      exact (S5.cXL M L).mul_mem hκy ((S5.cXL M L).inv_mem hyZ)
    rw [uCoord_of_mem_cXL nv hc]
    rfl
  have h2 : H.relIndex N * N.index = H.index := Subgroup.relIndex_mul_index hHN
  have h3 : N.index = Nat.card (Set.range (phiK h nv hKM)) := Subgroup.index_ker _
  have h4 : H.relIndex ((Zq M L).subgroupOf (xFix h)) ≤ H.relIndex N :=
    Subgroup.relIndex_le_of_le_right hZN Subgroup.index_ne_zero_of_finite
  have h5 : H.relIndex ((Zq M L).subgroupOf (xFix h)) =
      (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) :=
    Subgroup.relIndex_subgroupOf (cXL_le_xFix h)
  have h6 : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) ≤
      (Subgroup.centralizer (K : Set G)).relIndex (Xq M) :=
    Subgroup.relIndex_le_of_le_right (xFix_le h) Subgroup.index_ne_zero_of_finite
  have h1 : (Subgroup.centralizer (K : Set G)).relIndex (xFix h) = H.index := rfl
  calc (Subgroup.centralizer (K : Set G)).relIndex (Zq M L) *
        Nat.card (Set.range (phiK h nv hKM))
      ≤ H.relIndex N * N.index := by rw [← h5, h3]; exact Nat.mul_le_mul_right _ h4
    _ = (Subgroup.centralizer (K : Set G)).relIndex (xFix h) := by rw [h2, h1]
    _ ≤ _ := h6

@[expose] def dK : MSP.V4 F →+ (↥K → MSP.V4 F) where
  toFun v κ := MSP.mat (a ⟨κ, hKM κ.2⟩) *ᵥ v - v
  map_zero' := by
    funext κ
    simp
  map_add' v w := by
    funext κ
    simp only [Pi.add_apply, Matrix.mulVec_add]
    abel

omit [Finite G] [Fintype F] in
theorem mem_ker_dK_iff (v : MSP.V4 F) :
    v ∈ (dK (a := a) hKM).ker ↔ v ∈ MSP.fixSp (S5.imSp a K) := by
  rw [AddMonoidHom.mem_ker, MSP.mem_fixSp]
  constructor
  · rintro hv _ ⟨m, hm, rfl⟩
    have := congrFun hv ⟨m, Subgroup.mem_subgroupOf.1 hm⟩
    exact sub_eq_zero.1 this
  · intro hv
    funext κ
    have := hv (a ⟨κ, hKM κ.2⟩) ⟨⟨κ, hKM κ.2⟩, Subgroup.mem_subgroupOf.2 κ.2, rfl⟩
    show MSP.mat (a ⟨κ, hKM κ.2⟩) *ᵥ v - v = 0
    rw [this, sub_self]

omit [Finite G] [Fintype F] in
theorem card_fixSp_mul_card_range_dK :
    Nat.card (MSP.fixSp (S5.imSp a K)) * Nat.card (Set.range (dK (a := a) hKM)) =
      Nat.card (MSP.V4 F) := by
  have hmul := AddSubgroup.card_mul_index (dK (a := a) hKM).ker
  rw [AddSubgroup.index_ker] at hmul
  rw [← hmul]
  congr 1
  exact (Nat.card_congr (Equiv.subtypeEquivRight (mem_ker_dK_iff hKM))).symm

omit [Fintype F] in
theorem ofAdd_image_range_dK_subset :
    Multiplicative.ofAdd '' Set.range (dK (a := a) hKM) ⊆ Set.range (phiK h nv hKM) := by
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd v)
  refine ⟨⟨u, uq_le_xFix h u.2⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext κ
  rw [phiK_apply, uCoord_comm_uq h nv (hKM κ.2) u]
  have : nv.vec u = v := by rw [S5.NatVec.vec, hu]; rfl
  rw [this]
  rfl

omit [Fintype F] in
theorem card_le_card_fixSp_mul_card_range :
    Nat.card (MSP.V4 F) ≤
      Nat.card (MSP.fixSp (S5.imSp a K)) * Nat.card (Set.range (phiK h nv hKM)) := by
  rw [← card_fixSp_mul_card_range_dK hKM]
  refine Nat.mul_le_mul_left _ ?_
  rw [← Nat.card_image_of_injective Multiplicative.ofAdd.injective]
  exact Nat.card_mono (Set.toFinite _) (ofAdd_image_range_dK_subset h nv hKM)

theorem two_mul_card_le_card_fixSp_mul_card_range {x : G} (hx : x ∈ xFix h)
    (hnc : ∀ v : MSP.V4 F, ∃ κ : ↥K, S5.uCoord nv ⁅(κ : G), x⁆ ≠
      MSP.mat (a ⟨κ, hKM κ.2⟩) *ᵥ v - v) :
    2 * Nat.card (MSP.V4 F) ≤
      Nat.card (MSP.fixSp (S5.imSp a K)) * Nat.card (Set.range (phiK h nv hKM)) := by
  set S₁ := Multiplicative.ofAdd '' Set.range (dK (a := a) hKM) with hS₁
  set w := phiK h nv hKM ⟨x, hx⟩ with hw
  set S₂ := (w * ·) '' S₁ with hS₂
  have h1 : S₁ ⊆ Set.range (phiK h nv hKM) := ofAdd_image_range_dK_subset h nv hKM
  have h2 : S₂ ⊆ Set.range (phiK h nv hKM) := by
    rintro _ ⟨_, hz, rfl⟩
    obtain ⟨y, hy⟩ := h1 hz
    exact ⟨⟨x, hx⟩ * y, by rw [map_mul, hy]⟩
  have hdisj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩ ⟨_, ⟨_, ⟨v', rfl⟩, rfl⟩, he⟩
    obtain ⟨κ, hκ⟩ := hnc (v - v')
    apply hκ
    have := congrFun (congrArg Multiplicative.toAdd he) κ
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, hw, phiK_apply] at this
    change S5.uCoord nv ⁅(κ : G), x⁆ + (MSP.mat (a ⟨κ, hKM κ.2⟩) *ᵥ v' - v') =
      MSP.mat (a ⟨κ, hKM κ.2⟩) *ᵥ v - v at this
    rw [Matrix.mulVec_sub]
    linear_combination this
  have hc₂ : S₂.ncard = S₁.ncard := Set.ncard_image_of_injective _ (mul_right_injective w)
  have hc₁ : S₁.ncard = Nat.card (Set.range (dK (a := a) hKM)) := by
    rw [← Nat.card_coe_set_eq, Nat.card_image_of_injective Multiplicative.ofAdd.injective]
  have hU : (S₁ ∪ S₂).ncard ≤ (Set.range (phiK h nv hKM)).ncard :=
    Set.ncard_le_ncard (Set.union_subset h1 h2)
  rw [Set.ncard_union_eq hdisj, hc₂, hc₁, ← Nat.card_coe_set_eq] at hU
  rw [← card_fixSp_mul_card_range_dK hKM]
  calc 2 * (Nat.card (MSP.fixSp (S5.imSp a K)) * Nat.card (Set.range (dK (a := a) hKM)))
      = Nat.card (MSP.fixSp (S5.imSp a K)) * (Nat.card (Set.range (dK (a := a) hKM)) +
          Nat.card (Set.range (dK (a := a) hKM))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hU

end Count

section Form

variable [CharP F 2]

theorem exists_cform_of_mem_xFix (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    (nv : S5.NatVec M T L a) {x : G} (hx : x ∈ xFix h) (hxN : x ∉ Uq M T L ⊔ Zq M L) :
    ∃ (B : F) (m₀ : MSP.V4 F), B ≠ 0 ∧ ∀ g, S5.cocSp hd nv x g = S5.cform B m₀ g := by
  have hφ := S5.cocSp_mul hd h nv hx.1 hx.2
  obtain ⟨B, m₀, hBm⟩ := S5.exists_eq_sqf hd.card_eq hd.one_le hφ
  refine ⟨B, m₀, fun hB => hxN ?_, hBm⟩
  refine mem_of_cob h nv hx (m₀ := m₀) fun l hl => ?_
  rw [← S5.cocSp_a hd h nv hx.1 hx.2 (h.L_le hl), hBm, hB, zero_smul, zero_add]

end Form

end CFSG.Quasithin.MS93.S5Q2.X52
