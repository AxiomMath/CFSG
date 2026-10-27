module

public import CFSG.Quasithin.H13.L32A722b
public import CFSG.Quasithin.Background.F9Dual

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

omit [Finite G] in
theorem comm_mem_of_mem_o2z {Y : Subgroup G} {x : G} (hx : x ∈ L32A.o2z Y) {y : G}
    (hy : y ∈ Y) : y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 Y := by
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  have hz : QuotientGroup.mk' ((pCoreOf 2 Y).subgroupOf Y) x' ∈
      Subgroup.center (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y) := hx'
  have h1 := Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' _ ⟨y, hy⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h2 : ((⟨y, hy⟩ * x' : ↥Y) : G)⁻¹ * ((x' * ⟨y, hy⟩ : ↥Y) : G) ∈ pCoreOf 2 Y := h1
  have h3 := (Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf (r := 2) Y (Y.mul_mem hy x'.2)) _).mp h2
  have e2 : y * (x' : G) * (((⟨y, hy⟩ * x' : ↥Y) : G)⁻¹ * ((x' * ⟨y, hy⟩ : ↥Y) : G)) *
      (y * (x' : G))⁻¹ = (y * x' * y⁻¹ * (x' : G)⁻¹)⁻¹ := by
    push_cast
    group
  rw [e2] at h3
  simpa using inv_mem h3

omit [Finite G] in
theorem o2z_le (Y : Subgroup G) : L32A.o2z Y ≤ Y := Subgroup.map_subtype_le _

omit [Finite G] in
theorem eq_one_of_isPGroup {X : Subgroup G} (hX : IsPGroup 2 ↥X) {x : G} (hx : x ∈ X)
    (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := hX ⟨x, hx⟩
  have h2n : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)) (orderOf_dvd_of_pow_eq_one hx3)
    (orderOf_dvd_of_pow_eq_one h2n)
  exact orderOf_eq_one_iff.mp h1

omit [Finite G] in
theorem eq_or_eq_of_fpf_four {Y M X : Subgroup G} (hYM : Y ≤ M) (hMX : M ≤ X)
    (h4 : Y.relIndex X = 4) (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hcM : ∀ m ∈ M, c * m * c⁻¹ ∈ M) (hcY : ∀ y ∈ Y, c⁻¹ * y * c ∈ Y)
    (hfpf : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y → x ∈ Y) : M = Y ∨ M = X := by
  have hmul := Subgroup.relIndex_mul_relIndex Y M X hYM hMX
  rw [h4] at hmul
  by_cases h1 : Y.relIndex M = 1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hYM)
  by_cases h2 : M.relIndex X = 1
  · exact Or.inr (le_antisymm hMX (Subgroup.relIndex_eq_one.mp h2))
  exfalso
  have hdvd : Y.relIndex M ∣ 4 := ⟨_, hmul.symm⟩
  have hidx : Y.relIndex M = 2 := by
    have hle : Y.relIndex M ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Y.relIndex M
    · exact absurd (Nat.zero_dvd.mp hdvd) (by norm_num)
    · exact absurd rfl h1
    · rfl
    · exact absurd hdvd (by norm_num)
    · exfalso
      apply h2
      omega
  obtain ⟨m, hmM, hmY⟩ : ∃ m ∈ M, m ∉ Y := by
    by_contra hall
    push Not at hall
    exact h1 (Subgroup.relIndex_eq_one.mpr hall)
  have hcm : c * m * c⁻¹ ∈ M := hcM m hmM
  have hcmY : c * m * c⁻¹ ∉ Y := by
    intro h
    apply hmY
    have := hcY _ h
    simpa [mul_assoc] using this
  have hidx' : (Y.subgroupOf M).index = 2 := hidx
  have key : ((⟨m, hmM⟩ : ↥M)⁻¹ * ⟨c * m * c⁻¹, hcm⟩ : ↥M) ∈ Y.subgroupOf M := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx']
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inv]
    constructor
    · intro h
      exact absurd (by simpa using Y.inv_mem h) hmY
    · intro h
      exact absurd h hcmY
  rw [Subgroup.mem_subgroupOf] at key
  have hk : m⁻¹ * (c * m * c⁻¹) ∈ Y := by simpa using key
  apply hmY
  refine hfpf m (hMX hmM) ?_
  have e : c * m * c⁻¹ * m⁻¹ = m * (m⁻¹ * (c * m * c⁻¹)) * m⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hXY (hMX hmM)) _).mp hk

omit [Finite G] in
theorem le_normalizer_p : H ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
  F7.le_normalizer_pCoreOf_of_le_normalizer (le_normalizer_oTwoUpper H)

theorem p_le_qh : pCoreOf 2 (oTwoUpper H) ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 _).trans (oTwoUpper_le H)) le_normalizer_p
    (pCoreOf_isPGroup 2 _)

theorem fsuU_eq_h (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    fsuU T V = conjClosure V H := by
  rw [C.eq_hz]
  exact fsuU_eq_conjClosure_hz D.mod C.setting.hyp

theorem le_normalizer_u (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    H ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  rw [fsuU_eq_h C D]
  exact le_normalizer_conjClosure V H

omit [Finite G] in
theorem v1_le_u : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)

theorem u_comm (C : Ctx722 G T L V H γ γ' g k) {a b : G} (ha : a ∈ fsuU T V)
    (hb : b ∈ fsuU T V) : a * b = b * a :=
  fsuU_comm C.setting.hyp ha hb

theorem v1_comm (C : Ctx722 G T L V H γ γ' g k) {h v : G} (hh : h ∈ H)
    (hv : v ∈ fsuV1 T V) : h * v = v * h := by
  have hh' : h ∈ L32A.hz T V := C.eq_hz ▸ hh
  exact (Subgroup.mem_centralizer_iff.mp hh' v hv).symm

theorem conj_v1 (C : Ctx722 G T L V H γ γ' g k) {h v : G} (hh : h ∈ H)
    (hv : v ∈ fsuV1 T V) : h * v * h⁻¹ = v := by
  rw [v1_comm C hh hv, mul_inv_cancel_right]

theorem u_le_h (C : Ctx722 G T L V H γ γ' g k) : fsuU T V ≤ H := fun u hu => by
  rw [C.eq_hz]
  exact Subgroup.mem_centralizer_iff.mpr fun v hv => u_comm C (v1_le_u hv) hu

theorem comm_mem_v1 (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {x u : G}
    (hx : x ∈ pCoreOf 2 H) (hu : u ∈ fsuU T V) : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V :=
  C.hypF98.toHypF91.commutator_mem_V₁ hx (fsuU_eq_h C D ▸ hu)

theorem c_mem_o2z (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    c ∈ L32A.o2z (oTwoUpper H) := by
  have := D.c_mem
  rw [C.l1_eq] at this
  exact oTwoUpper_le _ this

theorem l1_le_k (C : Ctx722 G T L V H γ γ' g k) : L32A.l1 T L V ≤ oTwoUpper H := by
  rw [C.l1_eq]
  exact (oTwoUpper_le _).trans (o2z_le _)

theorem l1_le_h (C : Ctx722 G T L V H γ γ' g k) : L32A.l1 T L V ≤ H :=
  (l1_le_k C).trans (oTwoUpper_le H)

theorem c_mem_k (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) : c ∈ oTwoUpper H :=
  l1_le_k C D.c_mem

theorem c_mem_h (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) : c ∈ H :=
  oTwoUpper_le H (c_mem_k C D)

theorem comm_c_mem_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {y : G}
    (hy : y ∈ oTwoUpper H) : y * c * y⁻¹ * c⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
  comm_mem_of_mem_o2z (c_mem_o2z C D) hy

theorem c_not_mem_p (D : Data T L V θ c) : c ∉ pCoreOf 2 (oTwoUpper H) := fun h => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact D.c_ne (eq_one_of_isPGroup (pCoreOf_isPGroup 2 _) h D.c3)

theorem fpf_u (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∀ u ∈ fsuU T V, c * u * c⁻¹ * u⁻¹ ∈ fsuV1 T V → u ∈ fsuV1 T V := by
  have hcH := c_mem_h C D
  have hHU := le_normalizer_u C D
  have hV3 : ¬ 3 ∣ Nat.card ↥(fsuV1 T V) := by rw [D.card_v1]; norm_num
  have hcV : ∀ v ∈ fsuV1 T V, c * v * c⁻¹ ∈ fsuV1 T V := fun v hv => by
    rw [conj_v1 C hcH hv]; exact hv
  have hUV : fsuU T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := fun u hu =>
    mem_normalizer_of_forall_conj (Q := fsuU T V) (fun q hq v hv => by
      rw [conj_v1 C (u_le_h C hq) hv]; exact hv) hu
  have hF := mem_cfix_sup_iff D.c3 v1_le_u hV3 hcV hUV
  have hKF : oTwoUpper H ≤ Subgroup.normalizer
      ((cfix c (fsuU T V) ⊔ fsuV1 T V : Subgroup G) : Set G) := by
    intro y hy
    refine mem_normalizer_of_forall_conj (Q := oTwoUpper H) (fun y hy u hu => ?_) hy
    obtain ⟨huU, hcu⟩ := (hF u).mp hu
    have hyH : y ∈ H := oTwoUpper_le H hy
    rw [hF]
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hHU hyH) u).mp huU, ?_⟩
    set p := y⁻¹ * c * y * c⁻¹ with hp
    have hpP : p ∈ pCoreOf 2 (oTwoUpper H) := by
      have := comm_c_mem_p C D (inv_mem hy)
      simpa [hp] using this
    have hpH : p ∈ H := (pCoreOf_le 2 _).trans (oTwoUpper_le H) hpP
    have e : c * (y * u * y⁻¹) * c⁻¹ * (y * u * y⁻¹)⁻¹ =
        y * ((p * (c * u * c⁻¹ * u⁻¹) * p⁻¹) * (p * u * p⁻¹ * u⁻¹)) * y⁻¹ := by
      rw [hp]; group
    rw [e, conj_v1 C hyH (mul_mem ?_ (comm_mem_v1 C D (p_le_qh hpP) huU))]
    · exact mul_mem (by rw [conj_v1 C hpH hcu]; exact hcu) (comm_mem_v1 C D (p_le_qh hpP) huU)
    · rw [conj_v1 C hpH hcu]; exact hcu
  rcases C.irred_u _ le_sup_right (sup_le (fun x hx => (mem_cfix.mp hx).1) v1_le_u) hKF with
    hF1 | hF1
  · intro u hu h
    have := (hF u).mpr ⟨hu, h⟩
    rwa [hF1] at this
  · exfalso
    refine c_not_mem_p D (C.faithful_u c (c_mem_k C D) fun u hu => ?_)
    have : u ∈ cfix c (fsuU T V) ⊔ fsuV1 T V := by rw [hF1]; exact hu
    exact ((hF u).mp this).2

theorem conj_c_mem_u (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {u : G}
    (hu : u ∈ fsuU T V) : c * u * c⁻¹ ∈ fsuU T V :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D (c_mem_h C D)) u).mp hu

theorem norm_mem_v1 (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {u : G}
    (hu : u ∈ fsuU T V) :
    u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ∈ fsuV1 T V := by
  have hu₁ := conj_c_mem_u C D hu
  have hu₂ := conj_c_mem_u C D hu₁
  have hc3 : c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = u := by
    have : c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * u * (c * c * c)⁻¹ := by group
    rw [this, ← pow_three', D.c3, one_mul, inv_one, mul_one]
  refine fpf_u C D _ (mul_mem (mul_mem hu hu₁) hu₂) ?_
  have e : c * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * c⁻¹ =
      (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * (c * (c * (c * u * c⁻¹) * c⁻¹) * c⁻¹) := by
    group
  rw [e, hc3]
  have e2 : c * u * c⁻¹ * (c * (c * u * c⁻¹) * c⁻¹) * u =
      u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) := by
    exact (u_comm C (mul_mem hu₁ hu₂) hu).trans (mul_assoc _ _ _).symm
  rw [e2, mul_inv_cancel]
  exact one_mem _

theorem mem_of_comm_mem (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {X : Subgroup G}
    (hV₁X : fsuV1 T V ≤ X) (hXU : X ≤ fsuU T V) (hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) {u : G}
    (hu : u ∈ fsuU T V) (h : c * u * c⁻¹ * u⁻¹ ∈ X) : u ∈ X := by
  have : IsMulCommutative ↥(fsuU T V) := C.setting.hyp.abelian
  set x := c * u * c⁻¹ * u⁻¹ with hx
  have hx' : c * x * c⁻¹ ∈ X := hcX x h
  have hN := hV₁X (norm_mem_v1 C D hu)
  have e1 : c * u * c⁻¹ = x * u := by rw [hx]; group
  have e2 : c * (c * u * c⁻¹) * c⁻¹ = (c * x * c⁻¹) * x * u := by rw [hx]; group
  have hxU : x ∈ fsuU T V := hXU h
  have hx'U : c * x * c⁻¹ ∈ fsuU T V := hXU hx'
  have hu2 : u ^ 2 = 1 := F7.isElemAbelian_pow_eq_one D.elem_u hu
  have hx2 : x ^ 2 = 1 := F7.isElemAbelian_pow_eq_one D.elem_u hxU
  have key : u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) = (c * x * c⁻¹) * u := by
    rw [e2, e1]
    have := congrArg Subtype.val (show (⟨u, hu⟩ : ↥(fsuU T V)) * (⟨x, hxU⟩ * ⟨u, hu⟩) *
        (⟨c * x * c⁻¹, hx'U⟩ * ⟨x, hxU⟩ * ⟨u, hu⟩) = ⟨c * x * c⁻¹, hx'U⟩ * ⟨u, hu⟩ by
      have hu2' : (⟨u, hu⟩ : ↥(fsuU T V)) ^ 2 = 1 := Subtype.ext (by simpa using hu2)
      have hx2' : (⟨x, hxU⟩ : ↥(fsuU T V)) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      calc (⟨u, hu⟩ : ↥(fsuU T V)) * (⟨x, hxU⟩ * ⟨u, hu⟩) *
            (⟨c * x * c⁻¹, hx'U⟩ * ⟨x, hxU⟩ * ⟨u, hu⟩)
          = ⟨c * x * c⁻¹, hx'U⟩ * (⟨u, hu⟩ ^ 2 * ⟨x, hxU⟩ ^ 2) * ⟨u, hu⟩ := by
            rw [sq, sq]; ac_rfl
        _ = ⟨c * x * c⁻¹, hx'U⟩ * ⟨u, hu⟩ := by rw [hu2', hx2', mul_one, mul_one])
    simpa [mul_assoc] using this
  rw [key] at hN
  have e3 : u = (c * x * c⁻¹)⁻¹ * ((c * x * c⁻¹) * u) := by group
  rw [e3]
  exact mul_mem (inv_mem hx') hN

theorem v1_le_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    fsuV1 T V ≤ pCoreOf 2 (oTwoUpper H) := by
  obtain ⟨x, hx, u, hu, hne⟩ : ∃ x ∈ pCoreOf 2 (oTwoUpper H), ∃ u ∈ fsuU T V,
      x * u * x⁻¹ * u⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have heq : pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) =
        pCoreOf 2 (oTwoUpper H) := by
      refine le_antisymm inf_le_left fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr
        fun u hu => ?_⟩
      have h1 := hall x hx u hu
      calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * x * u := by group
        _ = x * u := by rw [h1, inv_one, one_mul]
    have h := C.relIndex_pc
    rw [heq, Subgroup.relIndex_self] at h
    norm_num at h
  have hv : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := comm_mem_v1 C D (p_le_qh hx) hu
  have hp : x * u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 (oTwoUpper H) := by
    have h1 : u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 (oTwoUpper H) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_p (u_le_h C hu)) _).mp (inv_mem hx)
    have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem hx h1
  refine le_of_card_eq_two_of_inf_ne_bot D.card_v1 fun hb => hne ?_
  have : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V ⊓ pCoreOf 2 (oTwoUpper H) := ⟨hv, hp⟩
  rwa [hb, Subgroup.mem_bot] at this

theorem u_le_p (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    fsuU T V ≤ pCoreOf 2 (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUL : fsuU T V ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) :=
    (u_le_h C).trans C.l1_normal
  have hLU : L32A.l1 T L V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    (l1_le_h C).trans (le_normalizer_u C D)
  have h1 : ⁅fsuU T V, L32A.l1 T L V⁆ ≤ fsuU T V ⊓ L32A.l1 T L V :=
    F7.commutator_le_inf_of_normalizes hUL hLU
  have h2 : fsuU T V ⊓ L32A.l1 T L V ≤ pCoreOf 2 (L32A.l1 T L V) := by
    refine le_pCoreOf_of_le_normalizer inf_le_right
      (F7.le_normalizer_inf hLU Subgroup.le_normalizer) fun x => ⟨1, Subtype.ext ?_⟩
    simpa using F7.isElemAbelian_pow_eq_one D.elem_u x.2.1
  rw [C.o2_l1] at h2
  rw [← C.u_comm]
  exact sup_le (h1.trans h2) (v1_le_p C D)

omit [Finite G] in
theorem le_normalizer_r :
    L ≤ Subgroup.normalizer
      ((conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L : Subgroup G) : Set G) :=
  le_normalizer_conjClosure _ L

omit [Finite G] in
theorem u_le_s : fsuU T V ≤ L32A.sL T L V := le_conjClosure _ L

theorem r_le_centralizer_u (C : Ctx722 G T L V H γ γ' g k) :
    conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L ≤ Subgroup.centralizer (fsuU T V : Set G) :=
  fun _ hr => Subgroup.mem_centralizer_iff.mpr fun u hu =>
    (Subgroup.mem_centralizer_iff.mp (C.r_center hr).2 u (u_le_s hu))

theorem u_not_le_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ¬ fsuU T V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L := by
  intro hUR
  have hSR : L32A.sL T L V ≤ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L :=
    conjClosure_le fun l hl u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_r hl) u).mp (hUR hu)
  have hcomm : ⁅L32A.sL T L V, L32A.sL T L V⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have h1 := Subgroup.mem_centralizer_iff.mp (C.r_center (hSR ha)).2 b hb
    rw [Subgroup.mem_bot, commutatorElement_def, ← h1]
    group
  have h8 := D.card_v
  rw [← C.frattini.2, hcomm, Subgroup.card_bot] at h8
  norm_num at h8

omit [Finite G] in
theorem conj_c_mem_e (D : Data T L V θ c) {e : G} (he : e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) :
    c * e * c⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_e ⟨D.c_L, D.c_N⟩) e).mp he

omit [Finite G] in
theorem conj_c_inv_mem_e (D : Data T L V θ c) {e : G}
    (he : e ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) : c⁻¹ * e * c ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have := (Subgroup.mem_normalizer_iff.mp
    (inv_mem (le_normalizer_e (T := T) (V := V) ⟨D.c_L, D.c_N⟩)) e).mp he
  simpa using this

theorem v1_le_e (C : Ctx722 G T L V H γ γ' g k) : fsuV1 T V ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
  inf_le_left.trans C.v_le_e

theorem fpf_ue (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {u : G}
    (hu : u ∈ fsuU T V) (h : c * u * c⁻¹ * u⁻¹ ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆) :
    u ∈ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
  mem_of_comm_mem C D (v1_le_e C) (e_le_u C D) (fun _ he => conj_c_mem_e D he) hu h

omit [Finite G] in
theorem le_normalizer_of_comm {X Y : Subgroup G} (hYX : Y ≤ X)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) : X ≤ Subgroup.normalizer (Y : Set G) :=
  fun _ hx => mem_normalizer_of_forall_conj (Q := X) (fun q hq y hy => by
    rw [hX q hq y (hYX hy), mul_inv_cancel_right]; exact hy) hx

theorem u_inf_r (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    fsuU T V ⊓ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L = ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have hEU := e_le_u C D
  rcases eq_or_eq_of_fpf_four (c := c) (Y := ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆)
      (M := fsuU T V ⊓ conjClosure ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ L) (X := fsuU T V)
      (fun e he => ⟨hEU he, le_conjClosure _ L he⟩) inf_le_left
      C.relIndex_eu (le_normalizer_of_comm hEU fun a ha b hb => u_comm C ha hb)
      (fun m hm => ⟨conj_c_mem_u C D hm.1,
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_r D.c_L) m).mp hm.2⟩)
      (fun e he => conj_c_inv_mem_e D he) (fun u hu h => fpf_ue C D hu h) with h | h
  · exact h
  · exact absurd (fun u hu => ((h.symm ▸ hu : u ∈ fsuU T V ⊓ _)).2) (u_not_le_r C D)

omit [Finite G] in
theorem mem_normalizer_centralizer' {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ n ∈ Subgroup.centralizer (X : Set G),
      g * n * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg n hn
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    have h1 := Subgroup.mem_centralizer_iff.mp hn _ hx'
    calc x * (g * n * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * n * g⁻¹ * x := by group
  exact mem_normalizer_of_forall_conj (Q := Subgroup.normalizer (X : Set G)) key hg

theorem fpf_pc (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {x : G}
    (hx : x ∈ pCoreOf 2 (oTwoUpper H))
    (h : c * x * c⁻¹ * x⁻¹ ∈ Subgroup.centralizer (fsuU T V : Set G)) :
    x ∈ Subgroup.centralizer (fsuU T V : Set G) := by
  have hF := C.hypF98.toHypF91
  have hxQ := p_le_qh hx
  have hxH : x ∈ H := pCoreOf_le 2 H hxQ
  have hcH := c_mem_h C D
  have hf : ∀ u ∈ fsuU T V, x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := fun u hu => comm_mem_v1 C D hxQ hu
  have hmul : ∀ u₁ ∈ fsuU T V, ∀ u₂ ∈ fsuU T V, x * (u₁ * u₂) * x⁻¹ * (u₁ * u₂)⁻¹ =
      (x * u₁ * x⁻¹ * u₁⁻¹) * (x * u₂ * x⁻¹ * u₂⁻¹) := fun u₁ hu₁ u₂ hu₂ =>
    hF.commutator_mul_right hxQ (fsuU_eq_h C D ▸ hu₁) (fsuU_eq_h C D ▸ hu₂)
  have hinv : ∀ u ∈ fsuU T V,
      x * (c * u * c⁻¹) * x⁻¹ * (c * u * c⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by
    intro u hu
    have hu' := conj_c_mem_u C D hu
    set z := c * x * c⁻¹ * x⁻¹ with hz
    have hzu : z * (c * u * c⁻¹) = (c * u * c⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.mp h _ hu').symm
    have hzf : z * (x * (c * u * c⁻¹) * x⁻¹ * (c * u * c⁻¹)⁻¹) =
        (x * (c * u * c⁻¹) * x⁻¹ * (c * u * c⁻¹)⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.mp h _ (v1_le_u (hf _ hu'))).symm
    have e3 : (z * x) * (c * u * c⁻¹) * (z * x)⁻¹ * (c * u * c⁻¹)⁻¹ =
        z * (x * (c * u * c⁻¹) * x⁻¹ * (c * u * c⁻¹)⁻¹) * ((c * u * c⁻¹) * z⁻¹ *
          (c * u * c⁻¹)⁻¹) := by group
    have e4 : (c * u * c⁻¹) * z⁻¹ * (c * u * c⁻¹)⁻¹ = z⁻¹ := by
      rw [← (Commute.inv_left (show Commute z (c * u * c⁻¹) from hzu)).eq, mul_inv_cancel_right]
    have e5 : z * x = c * x * c⁻¹ := by rw [hz]; group
    have e6 : (c * x * c⁻¹) * (c * u * c⁻¹) * (c * x * c⁻¹)⁻¹ * (c * u * c⁻¹)⁻¹ =
        c * (x * u * x⁻¹ * u⁻¹) * c⁻¹ := by group
    rw [conj_v1 C hcH (hf u hu)] at e6
    rw [← e6, ← e5, e3, e4, hzf, mul_inv_cancel_right]
  refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
  have hu₁ := conj_c_mem_u C D hu
  have hu₂ := conj_c_mem_u C D hu₁
  have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by
    have hN := norm_mem_v1 C D hu
    have hfN : x * (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) * x⁻¹ *
        (u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹))⁻¹ = 1 := by
      rw [conj_v1 C hxH hN, mul_inv_cancel]
    rw [hmul _ (mul_mem hu hu₁) _ hu₂, hmul _ hu _ hu₁, hinv _ hu₁, hinv _ hu] at hfN
    have hsq : (x * u * x⁻¹ * u⁻¹) ^ 2 = 1 :=
      F7.isElemAbelian_pow_eq_one D.elem_v (Subgroup.mem_inf.mp (hf u hu)).1
    calc x * u * x⁻¹ * u⁻¹ = (x * u * x⁻¹ * u⁻¹) ^ 2 * (x * u * x⁻¹ * u⁻¹) := by
          rw [hsq, one_mul]
      _ = 1 := by rw [sq]; exact hfN
  calc u * x = (x * u * x⁻¹ * u⁻¹)⁻¹ * x * u := by group
    _ = x * u := by rw [h1, inv_one, one_mul]

end CFSG.Quasithin.H13.S4
