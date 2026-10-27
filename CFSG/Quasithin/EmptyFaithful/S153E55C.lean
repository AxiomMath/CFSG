module

public import CFSG.Quasithin.EmptyFaithful.S153E55A
public import CFSG.Quasithin.EmptyFaithful.S153E55B
public import CFSG.Quasithin.EmptyFaithful.S153E53C
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E55

open CFSG.Quasithin.S153E

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem U_le_normalizer_Y (cx : Ctx15350 T Mc M V₁ V₂ t) :
    UH153 T M V₁ Mc ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
  ((U_le_T cx).trans (T_le_M cx)).trans (le_normalizer_Y153 Mc M)

theorem T_le_normalizer_Y (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (Y153 Mc M : Set G) :=
  (T_le_M cx).trans (le_normalizer_Y153 Mc M)

theorem T_le_normalizer_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (UH153 T M V₁ Mc : Set G) :=
  (T_le_Mc cx).trans (le_normalizer_conjClosure _ _)

theorem T_le_normalizer_YU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer ((Y153 Mc M ⊔ UH153 T M V₁ Mc : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨T_le_normalizer_Y cx hx, T_le_normalizer_U cx hx⟩

theorem YU_le_normalizer_V (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) :=
  sup_le ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx)

theorem YU_le_M (cx : Ctx15350 T Mc M V₁ V₂ t) : Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ M :=
  sup_le (Y153_le Mc M) ((U_le_T cx).trans (T_le_M cx))

omit [Finite G] in
theorem U_le_YU : UH153 T M V₁ Mc ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := le_sup_right

omit [Finite G] in
theorem Y_le_YU : Y153 Mc M ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := le_sup_left

section PGroup

variable {g : G} (hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc)
include hI

omit [Finite G] in
theorem P_eq : Pgp153 T M V₁ Mc g = pCoreOf 2 (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
  unfold Pgp153
  rw [hI]

omit [Finite G] in
theorem P_le_YU : Pgp153 T M V₁ Mc g ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := by
  rw [P_eq hI]
  exact pCoreOf_le 2 _

theorem P_isPGroup : IsPGroup 2 (Pgp153 T M V₁ Mc g) := by
  rw [P_eq hI]
  exact pCoreOf_isPGroup 2 _

omit [Finite G] in
theorem YU_le_normalizer_P :
    Y153 Mc M ⊔ UH153 T M V₁ Mc ≤ Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) := by
  rw [P_eq hI]
  exact le_normalizer_pCoreOf 2 _

theorem T_le_normalizer_P (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ≤ Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) := by
  rw [P_eq hI]
  exact (T_le_normalizer_YU cx).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem P_le_T (cx : Ctx15350 T Mc M V₁ V₂ t) : Pgp153 T M V₁ Mc g ≤ T := by
  have hK : (Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊔ T ≤ M := sup_le (YU_le_M cx) (T_le_M cx)
  have hsyl : IsSylowTwoOf T ((Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊔ T) :=
    F7.isSylowTwoOf_mono_right cx.c.hyp.isSylowTwoOf le_sup_right hK
  have hnorm : (Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊔ T ≤
      Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) :=
    sup_le (YU_le_normalizer_P hI) (T_le_normalizer_P hI cx)
  have h1 : Pgp153 T M V₁ Mc g ≤ pCoreOf 2 ((Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((P_le_YU hI).trans le_sup_left) hnorm (P_isPGroup hI)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl)

theorem centralizer_le_P (cx : Ctx15350 T Mc M V₁ V₂ t) :
    (Y153 Mc M ⊔ UH153 T M V₁ Mc) ⊓ Subgroup.centralizer (VZ T M : Set G) ≤
      Pgp153 T M V₁ Mc g := by
  have hU2 : IsPGroup 2 (UH153 T M V₁ Mc) := cx.hF.isPGroup_conjClosure
  have hYC : IsPGroup 2 ↥(Y153 Mc M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
    have h0 := cx.r49.case_one.1
    have h1 : IsPGroup 2 ↥(pCoreOf 2 (Y153 Mc M)) := pCoreOf_isPGroup 2 _
    rw [h0] at h1
    exact h1
  rw [P_eq hI]
  exact inf_centralizer_le_pCoreOf (U_le_normalizer_Y cx) hU2 hYC (YU_le_normalizer_V cx)

end PGroup

end Basic

section NData

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem sup_le_normalizer_left {X : Type*} [Group X] {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ⊔ B ≤ Subgroup.normalizer (A : Set X) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  have key : ∀ b ∈ B, ∀ x ∈ A, b * x * b⁻¹ ∈ A := by
    intro b hb x hx
    have : b * x * b⁻¹ = x := by
      rw [← h x hx b hb]
      group
    rw [this]
    exact hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b hb x, fun hx => ?_⟩
  have := key b⁻¹ (B.inv_mem hb) _ hx
  simpa [mul_assoc] using this

theorem autI_YU_eq (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}
    (h53 : Concl15353One cx N₁ N₂) :
    autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) = N₁ ⊔ N₂ := by
  obtain ⟨Ω, -, hsup, hΩ⟩ := h53.omega
  rw [autI_sup _ ((Y153_le Mc M).trans cx.c.hyp.le_normalizer) (U_le_N cx), sup_comm]
  exact hsup.trans hΩ.symm

theorem Ni_norm (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hN : autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤
      Subgroup.normalizer (N : Set (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))))
    {i n : G} (hi : i ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hn : n ∈ Ni153 T Mc M V₁ N) :
    i * n * i⁻¹ ∈ Ni153 T Mc M V₁ N := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨hnI, hnN, hnc⟩ := mem_preAut153.1 hn
  have hiN : i ∈ Subgroup.normalizer (VZ T M : Set G) := YU_le_normalizer_V cx hi
  refine mem_preAut153.2 ⟨(Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem
    ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem hi hnI) ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hi),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hiN hnN) (Subgroup.inv_mem _ hiN), ?_⟩
  have e : (⟨i * n * i⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hiN hnN)
      (Subgroup.inv_mem _ hiN)⟩ : Subgroup.normalizer (VZ T M : Set G)) =
      ⟨i, hiN⟩ * ⟨n, hnN⟩ * ⟨i, hiN⟩⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]
  have h1 : conjAct (VZ T M) ⟨i, hiN⟩ ∈ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) :=
    convI_mem_autI hV hi hiN
  exact (Subgroup.mem_normalizer_iff.mp (hN h1) _).mp hnc

theorem pdecomp (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
    (c : Chain15354 cx N₁ N₂ g s) :
    PDecomp (Y153 Mc M ⊔ UH153 T M V₁ Mc) (Pgp153 T M V₁ Mc g) (VZ T M)
      (Ni153 T Mc M V₁ N₁) (Ni153 T Mc M V₁ N₂) (Pi153 T Mc M V₁ N₁ g) (Pi153 T Mc M V₁ N₂ g) := by
  have hI := c.h54.one
  have hΩ := autI_YU_eq cx c.h53one
  have hcomm := c.h53one.comm
  have hcomm' : ∀ a ∈ N₂, ∀ b ∈ N₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hN₁ : autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤
      Subgroup.normalizer (N₁ : Set (MulAut ↥(VZ T M))) := by
    rw [hΩ]
    exact sup_le_normalizer_left hcomm
  have hN₂ : autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc) ≤
      Subgroup.normalizer (N₂ : Set (MulAut ↥(VZ T M))) := by
    rw [hΩ, sup_comm]
    exact sup_le_normalizer_left hcomm'
  exact
    { PI := YU_le_normalizer_P hI
      P_le_I := P_le_YU hI
      VI := YU_le_normalizer_V cx
      V_le_P := c.h54.two_center.trans inf_le_left
      V_central := fun v hv p hp =>
        (Subgroup.mem_centralizer_iff.mp (c.h54.two_center hv).2 p hp).symm
      N₁_le_I := preAut153_le
      N₂_le_I := preAut153_le
      N₁_norm := fun i hi n hn => Ni_norm cx hN₁ hi hn
      N₂_norm := fun i hi n hn => Ni_norm cx hN₂ hi hn
      sup := c.h54.four_sup
      inf := c.h54.four_inf
      cent₁ := c.h54.four_cent₁
      cent₂ := c.h54.four_cent₂ }

theorem exists_pow_two_pow_odd {X : Type*} [Group X] [Finite X] (y : X) :
    ∃ k : ℕ, Odd (orderOf (y ^ 2 ^ k)) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  refine ⟨k, ?_⟩
  rw [orderOf_pow' y (pow_ne_zero k two_ne_zero), hn]
  have h1 : (2 ^ k * m).gcd (2 ^ k) = 2 ^ k := Nat.gcd_eq_right (dvd_mul_right _ _)
  rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem commV_eq_top (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hNY : N ≤ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (h : ⁅VZ T M, Ni153 T Mc M V₁ N⁆ = VZ T M) : commV N = ⊤ := by
  have hV := cx.c.hyp.elemAbelian
  have hNi : Ni153 T Mc M V₁ N ≤ Subgroup.normalizer (VZ T M : Set G) :=
    preAut153_le.trans (YU_le_normalizer_V cx)
  rw [commutator_eq_map_commV hV hNi] at h
  have hA : autI hV (Ni153 T Mc M V₁ N) = N := by
    show autI hV (preAut153 (VZ T M) (Y153 Mc M ⊔ UH153 T M V₁ Mc) N) = N
    rw [autI_preAut153, inf_eq_right.2 hNY]
  rw [hA] at h
  have h2 : (commV N).map (inclMod hV) = (⊤ : Subgroup (IntMod (VZ T M) hV)).map (inclMod hV) := by
    rw [h, map_inclMod_top]
  exact Subgroup.map_injective (inclMod_injective hV) h2

theorem exists_lift (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hNM : N ≤ autI cx.c.hyp.elemAbelian M)
    (e : ↥N ≃* Equiv.Perm (Fin 3)) (hcomm : commV N = ⊤) :
    ∃ y : G, y ∈ Y153 Mc M ∧ Odd (orderOf y) ∧ y ∈ Ni153 T Mc M V₁ N ∧
      ∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  let a₀ : ↥N := e.symm (finRotate 3)
  have ha₀3 : a₀ ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simp only [a₀, MulEquiv.apply_symm_apply]
    decide
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    have h1 := congrArg e h
    simp only [a₀, MulEquiv.apply_symm_apply, map_one] at h1
    exact absurd h1 (by decide)
  have hodd₀ : Odd (orderOf (a₀ : MulAut (IntMod (VZ T M) hV))) := by
    have h1 : orderOf a₀ ∣ 3 := orderOf_dvd_of_pow_eq_one ha₀3
    rw [Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h <;> rw [h] <;> decide
  have ha₀Y : (a₀ : MulAut (IntMod (VZ T M) hV)) ∈ autI hV (Y153 Mc M) := by
    rw [hYbar]
    exact Subgroup.subset_closure ⟨hNM a₀.2, hodd₀⟩
  obtain ⟨y', hy'Y, hy'⟩ := (mem_autI hV).1 ha₀Y
  obtain ⟨k, hk⟩ := exists_pow_two_pow_odd (y' : G)
  have hyN : (y' : G) ^ 2 ^ k ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.pow_mem _ y'.2 _
  have hyY : (y' : G) ^ 2 ^ k ∈ Y153 Mc M := Subgroup.pow_mem _ hy'Y _
  have hconv : convI hV ⟨(y' : G) ^ 2 ^ k, hyN⟩ = (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k := by
    have h1 : (⟨(y' : G) ^ 2 ^ k, hyN⟩ : Subgroup.normalizer (VZ T M : Set G)) = y' ^ 2 ^ k :=
      Subtype.ext rfl
    rw [h1, map_pow, hy']
  have ha_N : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k ∈ N := Subgroup.pow_mem _ a₀.2 _
  have ha3 : ((a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have h1 : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 3 = 1 := by
      have := congrArg Subtype.val ha₀3
      simpa using this
    rw [h1, one_pow]
  have ha1 : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k ≠ 1 := by
    intro h
    have h1 : a₀ ^ 2 ^ k = 1 := Subtype.ext (by simpa using h)
    have h2 : a₀ ^ Nat.gcd (2 ^ k) 3 = 1 := pow_gcd_eq_one.2 ⟨h1, ha₀3⟩
    have h3 : Nat.gcd (2 ^ k) 3 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rw [h3, pow_one] at h2
    exact ha₀1 h2
  refine ⟨(y' : G) ^ 2 ^ k, hyY, hk, ?_, ?_⟩
  · refine mem_preAut153.2 ⟨Y_le_YU hyY, hyN, ?_⟩
    show convI hV ⟨(y' : G) ^ 2 ^ k, hyN⟩ ∈ N
    rw [hconv]
    exact ha_N
  · intro v hv hvy
    have hfix := fixV_eq_bot_of_perm (W := IntMod (VZ T M) hV) IntMod.sq_eq_one e hcomm ha_N ha3 ha1
    have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (Subgroup.zpowers ((a₀ : MulAut (IntMod (VZ T M) hV)) ^ 2 ^ k)) := by
      rw [mem_fixV_zpowers_iff, ← hconv]
      refine IntMod.val_injective ?_
      rw [convI_apply_val]
      exact hvy
    rw [hfix, Subgroup.mem_bot] at hw
    have := congrArg IntMod.val hw
    exact this

end NData

section Commute

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

@[expose] noncomputable def bar (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G}
    (hy : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) :
    MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) :=
  convI cx.c.hyp.elemAbelian ⟨y, YU_le_normalizer_V cx hy⟩

theorem bar_apply_val (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G} (hy : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (w : IntMod (VZ T M) cx.c.hyp.elemAbelian) : (bar cx hy w).val = y * w.val * y⁻¹ :=
  convI_apply_val _ _ _

theorem bar_mem_of_mem_Ni (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N : Subgroup (MulAut ↥(VZ T M))} {y : G} (hy : y ∈ Ni153 T Mc M V₁ N)
    (hyYU : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) : bar cx hyYU ∈ N :=
  (mem_preAut153.1 hy).2.choose_spec

theorem bar_mem_autI (cx : Ctx15350 T Mc M V₁ V₂ t) {y : G} (hy : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    {K : Subgroup G} (hyK : y ∈ K) : bar cx hy ∈ autI cx.c.hyp.elemAbelian K :=
  convI_mem_autI _ hyK _

theorem commutator_mem_centralizer {X : Type*} [Group X] {V : Subgroup X} {y y' : X}
    (hy : y ∈ Subgroup.normalizer (V : Set X)) (hy' : y' ∈ Subgroup.normalizer (V : Set X))
    (hc : ∀ v ∈ V, y * (y' * v * y'⁻¹) * y⁻¹ = y' * (y * v * y⁻¹) * y'⁻¹) :
    y * y' * y⁻¹ * y'⁻¹ ∈ Subgroup.centralizer (V : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : y'⁻¹ * (y⁻¹ * v * y) * y'⁻¹⁻¹ ∈ V := by
    have h1 : y⁻¹ * v * y ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set X)).inv_mem hy) v).mp hv
      simpa using this
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set X)).inv_mem hy') _).mp h1
    exact this
  have h2 := hc _ hv'
  have e1 : y * (y' * (y'⁻¹ * (y⁻¹ * v * y) * y'⁻¹⁻¹) * y'⁻¹) * y⁻¹ = v := by group
  have e2 : y' * (y * (y'⁻¹ * (y⁻¹ * v * y) * y'⁻¹⁻¹) * y⁻¹) * y'⁻¹ =
      (y * y' * y⁻¹ * y'⁻¹)⁻¹ * v * (y * y' * y⁻¹ * y'⁻¹) := by group
  rw [e1, e2] at h2
  have e3 : v * (y * y' * y⁻¹ * y'⁻¹) = (y * y' * y⁻¹ * y'⁻¹) * v := by
    calc v * (y * y' * y⁻¹ * y'⁻¹) = (y * y' * y⁻¹ * y'⁻¹) * ((y * y' * y⁻¹ * y'⁻¹)⁻¹ * v *
        (y * y' * y⁻¹ * y'⁻¹)) := by group
      _ = (y * y' * y⁻¹ * y'⁻¹) * v := by rw [← h2]
  exact e3

theorem comm_mem_P (cx : Ctx15350 T Mc M V₁ V₂ t) {g : G}
    (hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc) {y y' : G}
    (hy : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hy' : y' ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (hc : bar cx hy * bar cx hy' = bar cx hy' * bar cx hy) :
    y * y' * y⁻¹ * y'⁻¹ ∈ Pgp153 T M V₁ Mc g := by
  have hyN := YU_le_normalizer_V cx hy
  have hy'N := YU_le_normalizer_V cx hy'
  refine centralizer_le_P hI cx ⟨(Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem
    ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem hy hy')
      ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hy)) ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem hy'),
    commutator_mem_centralizer hyN hy'N fun v hv => ?_⟩
  have h1 := congrArg (fun φ : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian) =>
    (φ (IntMod.mk cx.c.hyp.elemAbelian ⟨v, hv⟩)).val) hc
  simp only [MulAut.mul_apply, bar_apply_val] at h1
  exact h1

theorem autI_Y_comm (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {a b : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (ha : a ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M)) (hb : b ∈ autI cx.c.hyp.elemAbelian (Y153 Mc M)) :
    a * b = b * a := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 3 ^ 2 := by
    rw [hYbar]
    exact hS.card_oTwoUpper hT
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hY9).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val hcomm

end Commute


end S153E55

end CFSG.Quasithin
