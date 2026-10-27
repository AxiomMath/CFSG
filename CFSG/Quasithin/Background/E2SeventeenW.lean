module

public import CFSG.Quasithin.Background.E2SeventeenDecomp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F
open scoped Pointwise

namespace E2

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_bot_of_le_commutator {H K : Subgroup G} (hsolv : Group.IsSolvable H) (hKH : K ≤ H)
    (hK : K ≤ ⁅K, K⁆) : K = ⊥ := by
  by_contra hne
  set K' := K.subgroupOf H with hK'
  have hmap : K'.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hK'ne : K' ≠ ⊥ := fun h => hne (by rw [← hmap, h, Subgroup.map_bot])
  have := hsolv
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hK'ne
  have hlt' : (⁅K', K'⁆).map H.subtype < K'.map H.subtype :=
    (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).2 hlt
  rw [Subgroup.map_commutator, hmap] at hlt'
  exact hlt'.not_ge hK

namespace Setting17

variable {H T M V U : Subgroup G} {x z : G}

@[expose] def W (_s : Setting17 H T M V U x z) : Subgroup G :=
  Subgroup.closure {y | ∃ k ∈ twoResidual H, y ∈ cjSub k U}

theorem gen_mem_W (s : Setting17 H T M V U x z) {k y : G} (hk : k ∈ twoResidual H)
    (hy : y ∈ cjSub k U) : y ∈ s.W :=
  Subgroup.subset_closure ⟨k, hk, hy⟩

theorem U_le_W (s : Setting17 H T M V U x z) : U ≤ s.W := fun u hu =>
  s.gen_mem_W (twoResidual H).one_mem (by rw [cjSub_one]; exact hu)

theorem W_le_Q (s : Setting17 H T M V U x z) : s.W ≤ pCoreOf 2 H := by
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨k, hk, hy⟩
  have h1 : cjSub k U ≤ cjSub k (pCoreOf 2 H) := cjSub_mono s.UQ
  rw [cjSub_eq_of_mem_normalizer (s.QN (twoResidual_le H hk))] at h1
  exact h1 hy

theorem W_le_H (s : Setting17 H T M V U x z) : s.W ≤ H := s.W_le_Q.trans (pCoreOf_le 2 H)

theorem mem_T_mul_K (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) :
    ∃ t ∈ T, ∃ k ∈ twoResidual H, t * k = g := by
  have hTK : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    s.dp.TH.trans (le_normalizer_twoResidual H)
  have h1 : g ∈ ((T ⊔ twoResidual H : Subgroup G) : Set G) := by
    rw [sup_twoResidual_eq s.mp.isSylow]
    exact hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTK] at h1
  obtain ⟨t, ht, k, hk, e⟩ := h1
  exact ⟨t, ht, k, hk, e⟩

theorem conj_mem_W (s : Setting17 H T M V U x z) {g : G} (hg : g ∈ H) {y : G} (hy : y ∈ s.W) :
    g * y * g⁻¹ ∈ s.W := by
  obtain ⟨t, ht, k₀, hk₀, rfl⟩ := s.mem_T_mul_K hg
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hyk⟩ := hy
    have hk' : t * (k₀ * k) * t⁻¹ ∈ twoResidual H :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (s.dp.TH ht)) _).mp
        ((twoResidual H).mul_mem hk₀ hk)
    refine s.gen_mem_W hk' ?_
    rw [mem_cjSub] at hyk ⊢
    have htU := (Subgroup.mem_normalizer_iff.mp (s.TU ht) _).mp hyk
    have e : (t * (k₀ * k) * t⁻¹)⁻¹ * (t * k₀ * y * (t * k₀)⁻¹) * (t * (k₀ * k) * t⁻¹) =
        t * (k⁻¹ * y * k) * t⁻¹ := by group
    rw [e]
    exact htU
  | one => simp
  | mul a b _ _ ha hb =>
    have e : t * k₀ * (a * b) * (t * k₀)⁻¹ =
        (t * k₀ * a * (t * k₀)⁻¹) * (t * k₀ * b * (t * k₀)⁻¹) := by group
    rw [e]
    exact s.W.mul_mem ha hb
  | inv a _ ha =>
    have e : t * k₀ * a⁻¹ * (t * k₀)⁻¹ = (t * k₀ * a * (t * k₀)⁻¹)⁻¹ := by group
    rw [e]
    exact s.W.inv_mem ha

theorem Z0_le_U (s : Setting17 H T M V U x z) : Z0 H V ≤ U := by
  rw [← s.Zeq]
  exact s.dp.ZU

theorem W_comm (s : Setting17 H T M V U x z) {a b : G} (ha : a ∈ s.W) (hb : b ∈ s.W) :
    a * b * a⁻¹ * b⁻¹ ∈ Z0 H V := by
  have hWH := s.W_le_H
  have key : ∀ a, (∃ k ∈ twoResidual H, a ∈ cjSub k U) → ∀ b ∈ s.W,
      a * b * a⁻¹ * b⁻¹ ∈ Z0 H V := by
    rintro a ⟨k, hk, hak⟩ b hb
    have haW : a ∈ s.W := s.gen_mem_W hk hak
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      obtain ⟨l, hl, hbl⟩ := hb
      exact s.comm_mem hk hl hak hbl
    | one => simp
    | mul b₁ b₂ hb₁ hb₂ h₁ h₂ =>
      have e : a * (b₁ * b₂) * a⁻¹ * (b₁ * b₂)⁻¹ =
          (a * b₁ * a⁻¹ * b₁⁻¹) * (b₁ * (a * b₂ * a⁻¹ * b₂⁻¹) * b₁⁻¹) := by group
      rw [e, s.le_center (hWH hb₁) h₂]
      exact (Z0 H V).mul_mem h₁ h₂
    | inv b hb h =>
      have e : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b⁻¹⁻¹ := by group
      rw [e, s.le_center (hWH (s.W.inv_mem hb)) ((Z0 H V).inv_mem h)]
      exact (Z0 H V).inv_mem h
  induction ha using Subgroup.closure_induction with
  | mem a ha => exact key a ha b hb
  | one => simp
  | mul a₁ a₂ ha₁ ha₂ h₁ h₂ =>
    have e : a₁ * a₂ * b * (a₁ * a₂)⁻¹ * b⁻¹ =
        (a₁ * (a₂ * b * a₂⁻¹ * b⁻¹) * a₁⁻¹) * (a₁ * b * a₁⁻¹ * b⁻¹) := by group
    rw [e, s.le_center (hWH ha₁) h₂]
    exact (Z0 H V).mul_mem h₂ h₁
  | inv a ha h =>
    have e : a⁻¹ * b * a⁻¹⁻¹ * b⁻¹ = a⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, s.le_center (hWH (s.W.inv_mem ha)) ((Z0 H V).inv_mem h)]
    exact (Z0 H V).inv_mem h

theorem x_comm_mem (s : Setting17 H T M V U x z) {y : G} (hy : y ∈ s.W) :
    x * y * x⁻¹ * y⁻¹ ∈ U := by
  have hQU : pCoreOf 2 H ≤ Subgroup.normalizer (U : Set G) := s.dp.QU
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hyk⟩ := hy
    obtain ⟨i, hi, hki⟩ := s.conjV hk
    have hUk : cjSub k U = cjSub i U := by
      rcases hi with rfl | hi
      · rw [s.conj_U (twoResidual_le H hk), hki, cjSub_one, cjSub_one, ← s.U_eq]
      · rw [s.conj_U (twoResidual_le H hk), s.conj_U hi.1, hki]
    rw [hUk] at hyk
    rcases hi with rfl | hi
    · rw [cjSub_one] at hyk
      rw [isElemAbelian_comm s.dp.elem s.dp.xV (s.dp.UV hyk)]
      have : y * x * x⁻¹ * y⁻¹ = 1 := by group
      rw [this]
      exact U.one_mem
    · have d := s.dpw hi
      rw [← d.Aeq] at hyk
      have := Subgroup.commutator_mem_commutator s.dp.xV hyk
      rw [commutatorElement_def] at this
      exact d.comm1 this
  | one => simp
  | mul a b ha hb h₁ h₂ =>
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact U.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hQU (s.W_le_Q ha)) _).mp h₂)
  | inv a ha h =>
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hQU (s.W_le_Q (s.W.inv_mem ha))) _).mp (U.inv_mem h)

theorem comm_VQ (s : Setting17 H T M V U x z) {v q : G} (hv : v ∈ V) (hq : q ∈ pCoreOf 2 H) :
    v * q * v⁻¹ * q⁻¹ ∈ U := by
  rw [s.U_eq]
  refine ⟨?_, ?_⟩
  · have h1 : q * v⁻¹ * q⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (s.dp.TV (s.dp.QT hq)) _).mp (V.inv_mem hv)
    have e : v * q * v⁻¹ * q⁻¹ = v * (q * v⁻¹ * q⁻¹) := by group
    rw [e]
    exact V.mul_mem hv h1
  · have h1 : v * q * v⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (s.QN (s.dp.VH hv)) _).mp hq
    exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hq)

theorem mem_Q_of_mem_T (s : Setting17 H T M V U x z) {t q k : G} (ht : t ∈ T)
    (hq : q ∈ pCoreOf 2 H) (hk : k ∈ twoResidual H) (e : t = q * k) : t ∈ pCoreOf 2 H := by
  have hkT : k ∈ T := by
    have : k = q⁻¹ * t := by rw [e]; group
    rw [this]
    exact T.mul_mem (T.inv_mem (s.dp.QT hq)) ht
  obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one s.dp.T2 hkT
  rw [e]
  exact (pCoreOf 2 H).mul_mem hq (s.two_mem hk hm)

theorem le_sup_Q (s : Setting17 H T M V U x z) {X : Subgroup G} (hXK : X ≤ twoResidual H)
    (hXN : H ≤ Subgroup.normalizer (X : Set G))
    (hR : (X ⊔ pCoreOf 2 H) ⊔ T = H) : twoResidual H ≤ X ⊔ pCoreOf 2 H := by
  intro k hk
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (hXK.trans (twoResidual_le H)).trans s.QN
  have hT : T ≤ Subgroup.normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    B2F.le_normalizer_sup (s.dp.TH.trans hXN) (s.dp.TH.trans s.QN)
  have hkR : k ∈ (((X ⊔ pCoreOf 2 H) ⊔ T : Subgroup G) : Set G) := by
    rw [hR]
    exact twoResidual_le H hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT] at hkR
  obtain ⟨r, hr, t, ht, rfl⟩ := hkR
  have hr' : r ∈ ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hr
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXQ] at hr'
  obtain ⟨y, hy, q, hq, hyq⟩ := hr'
  have hr2 : r = y * q := hyq.symm
  have hyX : y ∈ X := hy
  have hqQ : q ∈ pCoreOf 2 H := hq
  rw [hr2] at hk ⊢
  have hyk : y⁻¹ * (y * q * t) ∈ twoResidual H :=
    (twoResidual H).mul_mem ((twoResidual H).inv_mem (hXK hyX)) hk
  have htQ : t ∈ pCoreOf 2 H := s.mem_Q_of_mem_T ht ((pCoreOf 2 H).inv_mem hqQ) hyk
    (by group)
  exact (X ⊔ pCoreOf 2 H).mul_mem ((X ⊔ pCoreOf 2 H).mul_mem (Subgroup.mem_sup_left hyX)
    (Subgroup.mem_sup_right hqQ)) (Subgroup.mem_sup_right htQ)

theorem le_of_le_sup_Q (s : Setting17 H T M V U x z) {X : Subgroup G}
    (hXK : X ≤ twoResidual H) (hXN : twoResidual H ≤ Subgroup.normalizer (X : Set G))
    (hle : twoResidual H ≤ X ⊔ pCoreOf 2 H) : twoResidual H ≤ X := by
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (hXK.trans (twoResidual_le H)).trans s.QN
  have h2 : ∀ y ∈ twoResidual H, ∃ m : ℕ, y ^ 2 ^ m ∈ X := by
    intro y hy
    have hy' : y ∈ ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) := hle hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXQ] at hy'
    obtain ⟨l, hl, q, hq, hlq⟩ := hy'
    have hy2 : y = l * q := hlq.symm
    have hl : l ∈ X := hl
    have hq : q ∈ pCoreOf 2 H := hq
    rw [hy2] at hy ⊢
    have hqK : q ∈ twoResidual H := by
      have : q = l⁻¹ * (l * q) := by group
      rw [this]
      exact (twoResidual H).mul_mem ((twoResidual H).inv_mem (hXK hl)) hy
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one s.dp.T2 (s.dp.QT hq)
    have key : ∀ n : ℕ, (l * q) ^ n * (q ^ n)⁻¹ ∈ X := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hc : q ^ n * l * (q ^ n)⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp
            (hXN ((twoResidual H).pow_mem hqK n)) l).mp hl
        have e : (l * q) ^ (n + 1) * (q ^ (n + 1))⁻¹ =
            ((l * q) ^ n * (q ^ n)⁻¹) * (q ^ n * l * (q ^ n)⁻¹) := by
          rw [pow_succ, pow_succ]
          group
        rw [e]
        exact X.mul_mem ih hc
    refine ⟨m, ?_⟩
    have := key (2 ^ m)
    rwa [hm, inv_one, mul_one] at this
  have h := twoResidual_le_of_isTwoQuotient hXK hXN h2
  rwa [twoResidual_twoResidual] at h

theorem le_M_of_ne (s : Setting17 H T M V U x z) {X : Subgroup G} (hXH : X ≤ H)
    (hR : (X ⊔ pCoreOf 2 H) ⊔ T ≠ H) : X ≤ M := by
  have hle : (X ⊔ pCoreOf 2 H) ⊔ T ≤ H := sup_le (sup_le hXH (pCoreOf_le 2 H)) s.dp.TH
  exact le_sup_left.trans (le_sup_left.trans
    (s.mp.le_of_lt le_sup_right (lt_of_le_of_ne hle hR)))

theorem L_le_K (s : Setting17 H T M V U x z) : ⁅twoResidual H, V⁆ ≤ twoResidual H := by
  rw [Subgroup.commutator_le]
  intro k hk v hv
  rw [commutatorElement_def]
  have h1 : v * k⁻¹ * v⁻¹ ∈ twoResidual H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (s.dp.VH hv)) _).mp
      ((twoResidual H).inv_mem hk)
  have e : k * v * k⁻¹ * v⁻¹ = k * (v * k⁻¹ * v⁻¹) := by group
  rw [e]
  exact (twoResidual H).mul_mem hk h1

theorem H_le_normalizer_L (s : Setting17 H T M V U x z) :
    H ≤ Subgroup.normalizer ((⁅twoResidual H, V⁆ : Subgroup G) : Set G) := by
  have hT : ∀ t ∈ T, ∀ y ∈ ⁅twoResidual H, V⁆, t * y * t⁻¹ ∈ ⁅twoResidual H, V⁆ := by
    intro t ht y hy
    rw [Subgroup.commutator_def] at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨t * k * t⁻¹, ?_, t * v * t⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H (s.dp.TH ht)) k).mp hk
      · exact (Subgroup.mem_normalizer_iff.mp (s.dp.TV ht) v).mp hv
      · simp only [commutatorElement_def]
        group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hK : ∀ g ∈ twoResidual H, ∀ y ∈ ⁅twoResidual H, V⁆, g * y * g⁻¹ ∈ ⁅twoResidual H, V⁆ := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, v, hv, rfl⟩ := hy
      have h1 := Subgroup.commutator_mem_commutator ((twoResidual H).mul_mem hg hk) hv
      have h2 := Subgroup.commutator_mem_commutator hg hv
      have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      rw [commutatorElement_def, commutatorElement_def] at h3
      rw [commutatorElement_def]
      have e : g * (k * v * k⁻¹ * v⁻¹) * g⁻¹ =
          g * k * v * (g * k)⁻¹ * v⁻¹ * (g * v * g⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact h3
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  have hTN : T ≤ Subgroup.normalizer ((⁅twoResidual H, V⁆ : Subgroup G) : Set G) := fun t ht =>
    B6.mem_normalizer_of_forall_mem (hT t ht)
      (fun y hy => by simpa using hT t⁻¹ (T.inv_mem ht) y hy)
  have hKN : twoResidual H ≤
      Subgroup.normalizer ((⁅twoResidual H, V⁆ : Subgroup G) : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (hK g hg)
      (fun y hy => by simpa using hK g⁻¹ ((twoResidual H).inv_mem hg) y hy)
  exact (sup_twoResidual_eq s.mp.isSylow).symm.le.trans (sup_le hTN hKN)

theorem z_mem_L (s : Setting17 H T M V U x z) : z ∈ ⁅twoResidual H, V⁆ := by
  have hzK : z ∈ twoResidual H := mem_twoResidual_of_odd' s.dp.zH s.dp.zodd
  have h1 := Subgroup.commutator_mem_commutator hzK s.dp.xV
  rw [commutatorElement_def] at h1
  have hxz' : x * z⁻¹ * x⁻¹ = z := by
    calc x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
      _ = z := by rw [s.dp.xz, inv_inv]
  have hz3' : z ^ 3 = 1 := by rw [← s.z3]; exact pow_orderOf_eq_one z
  have e : z * x * z⁻¹ * x⁻¹ = z⁻¹ := by
    calc z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) := by group
      _ = z * z := by rw [hxz']
      _ = z⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, show z * z * z = z ^ 3 by rw [pow_three, mul_assoc]]
        exact hz3'
  rw [e] at h1
  simpa using Subgroup.inv_mem _ h1

theorem K_le_L (s : Setting17 H T M V U x z) : twoResidual H ≤ ⁅twoResidual H, V⁆ := by
  have hLH : ⁅twoResidual H, V⁆ ≤ H := s.L_le_K.trans (twoResidual_le H)
  have hR : (⁅twoResidual H, V⁆ ⊔ pCoreOf 2 H) ⊔ T = H := by
    by_contra hne
    have hzM : z ∈ M := s.le_M_of_ne hLH hne s.z_mem_L
    have hzC := s.odd_mem_centralizer hzM s.dp.zodd
    exact s.conj_ne s.isInv_z (cjSub_eq_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ hzC))
  exact s.le_of_le_sup_Q s.L_le_K (fun g hg => s.H_le_normalizer_L (twoResidual_le H hg))
    (s.le_sup_Q s.L_le_K s.H_le_normalizer_L hR)

theorem comm_comm_mem (s : Setting17 H T M V U x z) {k v q : G} (hk : k ∈ twoResidual H)
    (hv : v ∈ V) (hq : q ∈ pCoreOf 2 H) :
    (k * v * k⁻¹ * v⁻¹) * q * (k * v * k⁻¹ * v⁻¹)⁻¹ * q⁻¹ ∈ s.W := by
  have hkH : k ∈ H := twoResidual_le H hk
  have hvH : v ∈ H := s.dp.VH hv
  have hqH : q ∈ H := pCoreOf_le 2 H hq
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = q⁻¹ * k⁻¹ * q * k := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂, c₂ = v⁻¹ * q * v * q⁻¹ := ⟨_, rfl⟩
  have e : (k * v * k⁻¹ * v⁻¹) * q * (k * v * k⁻¹ * v⁻¹)⁻¹ * q⁻¹ =
      ((k * q) * (v * c₁ * v⁻¹ * c₁⁻¹)⁻¹ * (k * q)⁻¹ *
        ((k * v) * (k⁻¹ * c₂ * k * c₂⁻¹)⁻¹ * (k * v)⁻¹))⁻¹ := by
    rw [hc₁, hc₂]
    group
  have hc₁Q : c₁ ∈ pCoreOf 2 H := by
    have h1 : k⁻¹ * q * k ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (s.QN (H.inv_mem hkH)) q).mp hq
      simpa using this
    have e1 : c₁ = q⁻¹ * (k⁻¹ * q * k) := by rw [hc₁]; group
    rw [e1]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem hq) h1
  have hX : v * c₁ * v⁻¹ * c₁⁻¹ ∈ s.W := s.U_le_W (s.comm_VQ hv hc₁Q)
  have hc₂U : c₂ ∈ U := by
    have := s.comm_VQ (V.inv_mem hv) hq
    rw [hc₂]
    simpa using this
  have hY : k⁻¹ * c₂ * k * c₂⁻¹ ∈ s.W := by
    have h1 : k⁻¹ * c₂ * k ∈ cjSub k⁻¹ U := by
      rw [mem_cjSub]
      simpa [mul_assoc] using hc₂U
    exact s.W.mul_mem (s.gen_mem_W ((twoResidual H).inv_mem hk) h1)
      (s.W.inv_mem (s.U_le_W hc₂U))
  rw [e]
  exact s.W.inv_mem (s.W.mul_mem (s.conj_mem_W (H.mul_mem hkH hqH) (s.W.inv_mem hX))
    (s.conj_mem_W (H.mul_mem hkH hvH) (s.W.inv_mem hY)))

theorem comm_Q_mem (s : Setting17 H T M V U x z) {k q : G} (hk : k ∈ twoResidual H)
    (hq : q ∈ pCoreOf 2 H) : k * q * k⁻¹ * q⁻¹ ∈ s.W := by
  have hLH : ⁅twoResidual H, V⁆ ≤ H := s.L_le_K.trans (twoResidual_le H)
  have key : ∀ y ∈ ⁅twoResidual H, V⁆, ∀ q ∈ pCoreOf 2 H, y * q * y⁻¹ * q⁻¹ ∈ s.W := by
    intro y hy
    have hyH : y ∈ H := hLH hy
    rw [Subgroup.commutator_def] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k₀, hk₀, v, hv, rfl⟩ := hy
      intro q hq
      rw [commutatorElement_def]
      exact s.comm_comm_mem hk₀ hv hq
    | one => intro q _; simp
    | mul a b ha hb h₁ h₂ =>
      intro q hq
      have haH : a ∈ H := hLH (by rw [Subgroup.commutator_def]; exact ha)
      have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
          a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ * (a * q * a⁻¹ * q⁻¹) := by group
      rw [e]
      exact s.W.mul_mem (s.conj_mem_W haH (h₂ (hLH (by rw [Subgroup.commutator_def]; exact hb))
        q hq)) (h₁ haH q hq)
    | inv a ha h =>
      intro q hq
      have haH : a ∈ H := hLH (by rw [Subgroup.commutator_def]; exact ha)
      have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = a⁻¹ * (a * q * a⁻¹ * q⁻¹)⁻¹ * a⁻¹⁻¹ := by group
      rw [e]
      exact s.conj_mem_W (H.inv_mem haH) (s.W.inv_mem (h haH q hq))
  exact key k (s.K_le_L hk) q hq

theorem H_le_normalizer_W (s : Setting17 H T M V U x z) :
    H ≤ Subgroup.normalizer (s.W : Set G) := fun g hg =>
  B6.mem_normalizer_of_forall_mem (fun y hy => s.conj_mem_W hg hy)
    (fun y hy => by simpa using s.conj_mem_W (H.inv_mem hg) hy)

theorem inf_le_W (s : Setting17 H T M V U x z) : twoResidual H ⊓ pCoreOf 2 H ≤ s.W := by
  have hKH : twoResidual H ≤ H := twoResidual_le H
  set N : Subgroup ↥(twoResidual H) := (pCoreOf 2 H).subgroupOf (twoResidual H) with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (s.QN (hKH g.2)) _).mp hn⟩
  have hN2 : IsPGroup 2 N := fun n => by
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one s.dp.T2
      (s.dp.QT (Subgroup.mem_subgroupOf.1 n.2))
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hQ3 : IsPGroup 3 (↥(twoResidual H) ⧸ N) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H g =>
    obtain ⟨a, ha⟩ := s.three_pow_mem g g.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    simpa using ha
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨α, hα⟩ := IsPGroup.iff_card.1 hN2
    obtain ⟨β, hβ⟩ := IsPGroup.iff_card.1 hQ3
    rw [hα]
    show Nat.Coprime (2 ^ α) (Nat.card (↥(twoResidual H) ⧸ N))
    rw [hβ]
    exact Nat.Coprime.pow α β (by norm_num)
  obtain ⟨S', hS'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set S : Subgroup G := S'.map (twoResidual H).subtype with hS
  have hSK : S ≤ twoResidual H := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hSQ : ∀ t ∈ S, t ∈ pCoreOf 2 H → t = 1 := by
    rintro _ ⟨t, ht, rfl⟩ htQ
    have h1 : t ∈ N := Subgroup.mem_subgroupOf.2 htQ
    have := Subgroup.disjoint_def.1 hS'.disjoint h1 ht
    simp [this]
  have hdec : ∀ k ∈ twoResidual H, ∃ n ∈ twoResidual H ⊓ pCoreOf 2 H, ∃ t ∈ S, k = n * t := by
    intro k hk
    obtain ⟨⟨⟨n, hn⟩, ⟨t, ht⟩⟩, h⟩ := hS'.2 ⟨k, hk⟩
    refine ⟨n, ⟨n.2, Subgroup.mem_subgroupOf.1 hn⟩, t, ⟨t, ht, rfl⟩, ?_⟩
    have := congrArg Subtype.val h
    simpa using this.symm
  set B := twoResidual H ⊓ pCoreOf 2 H ⊓ s.W with hB
  have hBn : H ≤ Subgroup.normalizer (B : Set G) :=
    B2F.le_normalizer_inf (B2F.le_normalizer_inf (le_normalizer_twoResidual H) s.QN)
      s.H_le_normalizer_W
  set N₁ := S ⊔ B with hN₁
  have hN₁K : N₁ ≤ twoResidual H := sup_le hSK (inf_le_left.trans inf_le_left)
  have hSN : S ≤ Subgroup.normalizer (B : Set G) := fun t ht => hBn (hKH (hSK ht))
  have hcoe : ((N₁ : Subgroup G) : Set G) = (S : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S B hSN
  have hkey : ∀ n ∈ twoResidual H ⊓ pCoreOf 2 H, cjSub n N₁ ≤ N₁ := by
    intro n hn
    rw [hN₁, cjSub_sup, cjSub_eq_of_mem_normalizer (hBn (hKH hn.1))]
    refine sup_le (fun y hy => ?_) le_sup_right
    rw [mem_cjSub] at hy
    obtain ⟨t, ht, hty⟩ : ∃ t ∈ S, t = n⁻¹ * y * n := ⟨_, hy, rfl⟩
    have htK : t ∈ twoResidual H := hSK ht
    have hc : n * t * n⁻¹ * t⁻¹ ∈ B := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact (twoResidual H).mul_mem ((twoResidual H).mul_mem ((twoResidual H).mul_mem hn.1 htK)
          ((twoResidual H).inv_mem hn.1)) ((twoResidual H).inv_mem htK)
      · have h1 : t * n⁻¹ * t⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (s.QN (hKH htK)) _).mp ((pCoreOf 2 H).inv_mem hn.2)
        have e : n * t * n⁻¹ * t⁻¹ = n * (t * n⁻¹ * t⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 H).mul_mem hn.2 h1
      · have h1 := s.comm_Q_mem htK hn.2
        have e : n * t * n⁻¹ * t⁻¹ = (t * n * t⁻¹ * n⁻¹)⁻¹ := by group
        rw [e]
        exact s.W.inv_mem h1
    have e : y = (n * t * n⁻¹ * t⁻¹) * t := by rw [hty]; group
    rw [e]
    exact N₁.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left ht)
  have hnN : ∀ n ∈ twoResidual H ⊓ pCoreOf 2 H, n ∈ Subgroup.normalizer (N₁ : Set G) :=
    fun n hn => le_normalizer_of_cjSub_le (hkey n hn)
      (hkey n⁻¹ ((twoResidual H ⊓ pCoreOf 2 H).inv_mem hn))
  have htN : ∀ t ∈ S, t ∈ Subgroup.normalizer (N₁ : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_cjSub_eq, hN₁, cjSub_sup, cjSub_eq_of_mem_normalizer
      (Subgroup.le_normalizer ht), cjSub_eq_of_mem_normalizer (hBn (hKH (hSK ht)))]
  have hKN : twoResidual H ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro k hk
    obtain ⟨n, hn, t, ht, rfl⟩ := hdec k hk
    exact Subgroup.mul_mem _ (hnN n hn) (htN t ht)
  have h2 : ∀ y ∈ twoResidual H, ∃ m : ℕ, y ^ 2 ^ m ∈ N₁ := by
    intro y hy
    obtain ⟨n, hn, t, ht, rfl⟩ := hdec y hy
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one s.dp.T2 (s.dp.QT hn.2)
    have key : ∀ j : ℕ, (n * t) ^ j * (n ^ j)⁻¹ ∈ N₁ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hc : n ^ (j + 1) * t * (n ^ (j + 1))⁻¹ ∈ N₁ :=
          (Subgroup.mem_normalizer_iff.mp
            (hnN _ ((twoResidual H ⊓ pCoreOf 2 H).pow_mem hn (j + 1))) t).mp
            (Subgroup.mem_sup_left ht)
        have e : (n * t) ^ (j + 1) * (n ^ (j + 1))⁻¹ =
            ((n * t) ^ j * (n ^ j)⁻¹) * (n ^ (j + 1) * t * (n ^ (j + 1))⁻¹) := by
          rw [pow_succ, pow_succ]
          group
        rw [e]
        exact N₁.mul_mem ih hc
    refine ⟨m, ?_⟩
    have := key (2 ^ m)
    rwa [hm, inv_one, mul_one] at this
  have hKle : twoResidual H ≤ N₁ := by
    have h := twoResidual_le_of_isTwoQuotient hN₁K hKN h2
    rwa [twoResidual_twoResidual] at h
  intro a ha
  have haN : a ∈ ((N₁ : Subgroup G) : Set G) := hKle ha.1
  rw [hcoe] at haN
  obtain ⟨t, ht, b, hb, htb⟩ := haN
  have htb' : t * b = a := htb
  have htQ : t ∈ pCoreOf 2 H := by
    have : t = a * b⁻¹ := by rw [← htb']; group
    rw [this]
    exact (pCoreOf 2 H).mul_mem ha.2 ((pCoreOf 2 H).inv_mem hb.1.2)
  rw [← htb', hSQ t ht htQ, one_mul]
  exact hb.2

theorem Kc_le_K (_s : Setting17 H T M V U x z) :
    ⁅twoResidual H, twoResidual H⁆ ≤ twoResidual H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem H_le_normalizer_Kc (_s : Setting17 H T M V U x z) :
    H ≤ Subgroup.normalizer
      ((⁅twoResidual H, twoResidual H⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, ∀ y ∈ ⁅twoResidual H, twoResidual H⁆,
      g * y * g⁻¹ ∈ ⁅twoResidual H, twoResidual H⁆ := by
    intro g hg y hy
    rw [Subgroup.commutator_def] at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      refine Subgroup.subset_closure ⟨g * a * g⁻¹, ?_, g * b * g⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H hg) a).mp ha
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual H hg) b).mp hb
      · simp only [commutatorElement_def]
        group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ ha
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (key g hg)
    (fun y hy => by simpa using key g⁻¹ (H.inv_mem hg) y hy)

theorem commutator_le_M (s : Setting17 H T M V U x z) :
    ⁅twoResidual H, twoResidual H⁆ ≤ M := by
  have hKcH : ⁅twoResidual H, twoResidual H⁆ ≤ H := s.Kc_le_K.trans (twoResidual_le H)
  by_contra hne
  have hR : (⁅twoResidual H, twoResidual H⁆ ⊔ pCoreOf 2 H) ⊔ T = H := by
    by_contra hR
    exact hne (s.le_M_of_ne hKcH hR)
  have hle := s.le_of_le_sup_Q s.Kc_le_K
    (fun g hg => s.H_le_normalizer_Kc (twoResidual_le H hg))
    (s.le_sup_Q s.Kc_le_K s.H_le_normalizer_Kc hR)
  have hbot := eq_bot_of_le_commutator s.solv (twoResidual_le H) hle
  have hzK : z ∈ twoResidual H := mem_twoResidual_of_odd' s.dp.zH s.dp.zodd
  rw [hbot, Subgroup.mem_bot] at hzK
  exact s.dp.z1 hzK

theorem Kc_comm_U (s : Setting17 H T M V U x z) {c : G}
    (hc : c ∈ ⁅twoResidual H, twoResidual H⁆) {u : G} (hu : u ∈ U) :
    c * u * c⁻¹ * u⁻¹ ∈ Z0 H V := by
  have hcK := s.Kc_le_K hc
  have hcM := s.commutator_le_M hc
  obtain ⟨a, b, rfl, ha, hb, ⟨m, hm⟩, hbo⟩ := exists_two_part_odd_part c
  have hzK : Subgroup.zpowers (b * a) ≤ twoResidual H := Subgroup.zpowers_le.2 hcK
  have hzM : Subgroup.zpowers (b * a) ≤ M := Subgroup.zpowers_le.2 hcM
  have haW : a ∈ s.W := s.inf_le_W ⟨hzK ha, s.two_mem (hzK ha) hm⟩
  have hbC : b ∈ Subgroup.centralizer (V : Set G) := s.odd_mem_centralizer (hzM hb) hbo
  have hζ := s.W_comm haW (s.U_le_W hu)
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = a * u * a⁻¹ * u⁻¹ := ⟨_, rfl⟩
  rw [← hζdef] at hζ
  have hau : a * u * a⁻¹ = ζ * u := by rw [hζdef]; group
  have hζV : ζ * u ∈ V := V.mul_mem hζ.1 (s.dp.UV hu)
  have hb' : b * (ζ * u) * b⁻¹ = ζ * u := by
    rw [← Subgroup.mem_centralizer_iff.1 hbC _ hζV]
    group
  have e : b * a * u * (b * a)⁻¹ * u⁻¹ = ζ := by
    calc b * a * u * (b * a)⁻¹ * u⁻¹ = b * (a * u * a⁻¹) * b⁻¹ * u⁻¹ := by group
      _ = ζ := by rw [hau, hb']; group
  rw [e]
  exact hζ

theorem Kc_comm_W (s : Setting17 H T M V U x z) {c : G}
    (hc : c ∈ ⁅twoResidual H, twoResidual H⁆) {y : G} (hy : y ∈ s.W) :
    c * y * c⁻¹ * y⁻¹ ∈ Z0 H V := by
  have hWH := s.W_le_H
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, hyk⟩ := hy
    rw [mem_cjSub] at hyk
    have hkH : k ∈ H := twoResidual_le H hk
    have hc' : k⁻¹ * c * k⁻¹⁻¹ ∈ ⁅twoResidual H, twoResidual H⁆ :=
      (Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_Kc (H.inv_mem hkH)) c).mp hc
    have h1 := s.Kc_comm_U hc' hyk
    have e : c * y * c⁻¹ * y⁻¹ = k * ((k⁻¹ * c * k⁻¹⁻¹) * (k⁻¹ * y * k) *
        (k⁻¹ * c * k⁻¹⁻¹)⁻¹ * (k⁻¹ * y * k)⁻¹) * k⁻¹ := by group
    rw [e, s.le_center hkH h1]
    exact h1
  | one => simp
  | mul a b ha hb h₁ h₂ =>
    have e : c * (a * b) * c⁻¹ * (a * b)⁻¹ =
        (c * a * c⁻¹ * a⁻¹) * (a * (c * b * c⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e, s.le_center (hWH ha) h₂]
    exact (Z0 H V).mul_mem h₁ h₂
  | inv a ha h =>
    have e : c * a⁻¹ * c⁻¹ * a⁻¹⁻¹ = a⁻¹ * (c * a * c⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, s.le_center (hWH (s.W.inv_mem ha)) ((Z0 H V).inv_mem h)]
    exact (Z0 H V).inv_mem h

theorem comm_conj_mem (s : Setting17 H T M V U x z) {k l : G} (hk : k ∈ twoResidual H)
    (hl : l ∈ twoResidual H) {y : G} (hy : y ∈ s.W) :
    (k * l) * y * (k * l)⁻¹ * ((l * k) * y * (l * k)⁻¹)⁻¹ ∈ Z0 H V := by
  have hc := Subgroup.commutator_mem_commutator hk hl
  rw [commutatorElement_def] at hc
  have hy' : (l * k) * y * (l * k)⁻¹ ∈ s.W :=
    s.conj_mem_W (H.mul_mem (twoResidual_le H hl) (twoResidual_le H hk)) hy
  have h1 := s.Kc_comm_W hc hy'
  have e : (k * l) * y * (k * l)⁻¹ * ((l * k) * y * (l * k)⁻¹)⁻¹ =
      (k * l * k⁻¹ * l⁻¹) * ((l * k) * y * (l * k)⁻¹) * (k * l * k⁻¹ * l⁻¹)⁻¹ *
        ((l * k) * y * (l * k)⁻¹)⁻¹ := by group
  rw [e]
  exact h1

end Setting17

end E2

end CFSG.Quasithin
