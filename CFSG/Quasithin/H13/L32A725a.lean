module

public import CFSG.Quasithin.H13.L32A724b

public section

namespace CFSG.Quasithin.H13.S4

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.A6 CFSG.Quasithin.H6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g k : ↥((L ⊔ T) ⊔ H)} {θ : ↥L →* Γ} {c : G}

theorem comm_comm_eq (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) {p q u : G}
    (hp : p ∈ pCoreOf 2 H) (hq : q ∈ H) (hu : u ∈ fsuU T V) :
    (p * q * p⁻¹ * q⁻¹) * u * (p * q * p⁻¹ * q⁻¹)⁻¹ * u⁻¹ =
      p * (u * (q⁻¹ * u * q)⁻¹) * p⁻¹ * (u * (q⁻¹ * u * q)⁻¹)⁻¹ := by
  have hpH : p ∈ H := pCoreOf_le 2 H hp
  have huH := u_le_h C hu
  set v := q⁻¹ * u * q with hv
  have hvU : v ∈ fsuU T V := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_u C D (inv_mem hq)) u).mp hu
    simpa [hv] using this
  have hvH := u_le_h C hvU
  set φ := p⁻¹ * v * p * v⁻¹ with hφ
  have hφV : φ ∈ fsuV1 T V := by
    have := comm_mem_v1 C D (inv_mem hp) hvU
    simpa [hφ] using this
  set f := p * u * p⁻¹ * u⁻¹ with hf
  have hfV : f ∈ fsuV1 T V := comm_mem_v1 C D hp hu
  have e1 : p⁻¹ * v * p = φ * v := by rw [hφ]; group
  have e2 : q * v * q⁻¹ = u := by rw [hv]; group
  have e3 : p * u * p⁻¹ = f * u := by rw [hf]; group
  have lhs : (p * q * p⁻¹ * q⁻¹) * u * (p * q * p⁻¹ * q⁻¹)⁻¹ * u⁻¹ = φ * f := by
    calc (p * q * p⁻¹ * q⁻¹) * u * (p * q * p⁻¹ * q⁻¹)⁻¹ * u⁻¹
        = p * q * (p⁻¹ * v * p) * q⁻¹ * p⁻¹ * u⁻¹ := by rw [hv]; group
      _ = p * q * (φ * v) * q⁻¹ * p⁻¹ * u⁻¹ := by rw [e1]
      _ = (p * (q * φ * q⁻¹) * p⁻¹) * (p * (q * v * q⁻¹) * p⁻¹) * u⁻¹ := by group
      _ = φ * (p * u * p⁻¹) * u⁻¹ := by rw [conj_v1 C hq hφV, conj_v1 C hpH hφV, e2]
      _ = φ * f := by rw [e3]; group
  have e4 : p * v⁻¹ * p⁻¹ = v⁻¹ * φ := by
    have h2 : p * φ * p⁻¹ = φ := conj_v1 C hpH hφV
    have e : p * φ * p⁻¹ = v * p * v⁻¹ * p⁻¹ := by rw [hφ]; group
    rw [e] at h2
    calc p * v⁻¹ * p⁻¹ = v⁻¹ * (v * p * v⁻¹ * p⁻¹) := by group
      _ = v⁻¹ * φ := by rw [h2]
  have huvH : u * v⁻¹ ∈ H := mul_mem huH (inv_mem hvH)
  have rhs : p * (u * v⁻¹) * p⁻¹ * (u * v⁻¹)⁻¹ = φ * f := by
    calc p * (u * v⁻¹) * p⁻¹ * (u * v⁻¹)⁻¹ = (p * u * p⁻¹) * (p * v⁻¹ * p⁻¹) * v * u⁻¹ := by
          group
      _ = f * u * (v⁻¹ * φ) * v * u⁻¹ := by rw [e3, e4]
      _ = f * ((u * v⁻¹) * φ * (u * v⁻¹)⁻¹) := by group
      _ = f * φ := by rw [conj_v1 C huvH hφV]
      _ = φ * f := F7.isElemAbelian_comm D.elem_v (Subgroup.mem_inf.mp hfV).1
          (Subgroup.mem_inf.mp hφV).1
  rw [lhs, rhs]

omit [Finite G] in
theorem mem_pCore_iff {H : Subgroup G} {x : G} (hx : x ∈ H) :
    (⟨x, hx⟩ : ↥H) ∈ CFSG.pCore 2 ↥H ↔ x ∈ pCoreOf 2 H := by
  rw [pCoreOf]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [← this]

theorem exists_q_not_mem (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∃ q ∈ pCoreOf 2 (L ⊔ T), q ∉ conjSub (k : G) (F8.Uγ V H (g : G)) ⊔ pCoreOf 2 H := by
  by_contra hall
  push Not at hall
  set Uα := conjSub (k : G) (F8.Uγ V H (g : G)) with hUα
  set QH := pCoreOf 2 H with hQH
  have hUαH : Uα ≤ H := (ualpha_le_s C).trans (s_le_h C D)
  have hQHH : QH ≤ H := pCoreOf_le 2 H
  have hQH_n : H ≤ Subgroup.normalizer (QH : Set G) := le_normalizer_pCoreOf (r := 2) H
  obtain ⟨a₀, ha₀, ha₀Q⟩ : ∃ a₀ ∈ Uα, a₀ ∉ QH := by
    by_contra h
    push Not at h
    have h1 := C.card_ualpha
    rw [sup_eq_right.mpr h, Subgroup.relIndex_self] at h1
    norm_num at h1
  have ha₀H := hUαH ha₀
  have hidx : (QH.subgroupOf (Uα ⊔ QH)).index = 2 := C.card_ualpha
  have hcoset : ∀ a ∈ Uα ⊔ QH, a ∉ QH → a₀⁻¹ * a ∈ QH := by
    intro a ha haQ
    have key : ((⟨a₀, Subgroup.mem_sup_left ha₀⟩ : ↥(Uα ⊔ QH))⁻¹ * ⟨a, ha⟩ : ↥(Uα ⊔ QH)) ∈
        QH.subgroupOf (Uα ⊔ QH) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inv]
      exact ⟨fun h => absurd (by simpa using QH.inv_mem h) ha₀Q, fun h => absurd h haQ⟩
    rw [Subgroup.mem_subgroupOf] at key
    simpa using key
  have hUUα : ⁅fsuU T V, Uα⁆ ≤ V := le_sup_left.trans (le_of_eq C.comm_ualpha)
  have hcV : ∀ u ∈ fsuU T V, a₀ * u * a₀⁻¹ * u⁻¹ ∈ V := fun u hu => by
    have h1 := Subgroup.commutator_mem_commutator hu ha₀
    rw [commutatorElement_def] at h1
    have e : a₀ * u * a₀⁻¹ * u⁻¹ = (u * a₀ * u⁻¹ * a₀⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hUUα h1)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  let φ : ↥(fsuU T V) →* ↥V :=
    { toFun := fun u => ⟨a₀ * u * a₀⁻¹ * (u : G)⁻¹, hcV u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun u₁ u₂ => Subtype.ext (by
        have h2 := hcV u₂ u₂.2
        have hcomm := u_comm C u₁.2 (hVU h2)
        simp only [Subgroup.coe_mul]
        calc a₀ * ((u₁ : G) * u₂) * a₀⁻¹ * ((u₁ : G) * u₂)⁻¹
            = (a₀ * u₁ * a₀⁻¹ * (u₁ : G)⁻¹) * ((u₁ : G) * (a₀ * u₂ * a₀⁻¹ * (u₂ : G)⁻¹) *
              (u₁ : G)⁻¹) := by group
          _ = (a₀ * u₁ * a₀⁻¹ * (u₁ : G)⁻¹) * (a₀ * u₂ * a₀⁻¹ * (u₂ : G)⁻¹) := by
            rw [hcomm, mul_inv_cancel_right]) }
  have hφ : ∀ u : ↥(fsuU T V), ((φ u : ↥V) : G) = a₀ * u * a₀⁻¹ * (u : G)⁻¹ := fun _ => rfl
  set Z₀' : Subgroup ↥(fsuU T V) := ((fsuV1 T V).subgroupOf V).comap φ with hZ₀'
  set Z₀ : Subgroup G := Z₀'.map (fsuU T V).subtype with hZ₀
  have hZ₀U : Z₀ ≤ fsuU T V := Subgroup.map_subtype_le _
  have hZ₀mem : ∀ {z : G}, z ∈ Z₀ → z ∈ fsuU T V ∧ a₀ * z * a₀⁻¹ * z⁻¹ ∈ fsuV1 T V := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hz)⟩
  have hZ₀idx : Z₀.relIndex (fsuU T V) ≤ 4 := by
    have e1 : Z₀.relIndex (fsuU T V) = Z₀'.index := by
      have h1 : Z₀.subgroupOf (fsuU T V) = Z₀' :=
        Subgroup.comap_map_eq_self_of_injective (fsuU T V).subtype_injective Z₀'
      show (Z₀.subgroupOf (fsuU T V)).index = _
      rw [h1]
    have hV₁V : (fsuV1 T V).relIndex V = 4 := by
      have h1 := Subgroup.relIndex_mul_card (fsuV1 T V) V
      rw [inf_eq_left.mpr inf_le_left, D.card_v1, D.card_v] at h1
      omega
    rw [e1, hZ₀', Subgroup.index_comap]
    calc ((fsuV1 T V).subgroupOf V).relIndex φ.range
        ≤ ((fsuV1 T V).subgroupOf V).relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top (by
          rw [Subgroup.relIndex_top_right]
          exact Subgroup.index_ne_zero_of_finite)
      _ = 4 := by rw [Subgroup.relIndex_top_right]; exact hV₁V
  have hPQZ : ∀ x ∈ pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T), ∀ z ∈ Z₀, x * z = z * x := by
    intro x hx z hz
    obtain ⟨hzU, hza⟩ := hZ₀mem hz
    have hle : pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T) ≤
        Subgroup.centralizer ({z} : Set G) := by
      rw [C.pq_eq]
      refine sup_le ?_ fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy.2 z hzU).symm
      rw [Subgroup.commutator_le]
      intro p hp q hq
      rw [commutatorElement_def, Subgroup.mem_centralizer_singleton_iff]
      have hqH : q ∈ H := (pCoreOf_sup_le C.setting.hyp).trans (t_le_h C) hq
      have hpQH : p ∈ QH := p_le_qh hp
      have hpH : p ∈ H := hQHH hpQH
      have hw : z * (q⁻¹ * z * q)⁻¹ ∈ fsuV1 T V := by
        have hq' := hall q⁻¹ (inv_mem hq)
        by_cases hqQ : q⁻¹ ∈ QH
        · have := comm_mem_v1 C D hqQ hzU
          have e : z * (q⁻¹ * z * q)⁻¹ = (q⁻¹ * z * q⁻¹⁻¹ * z⁻¹)⁻¹ := by group
          rw [e]
          exact inv_mem this
        · obtain h3 := hcoset _ hq' hqQ
          set h' := a₀⁻¹ * q⁻¹ with hh'
          have hqe : q⁻¹ = a₀ * h' := by rw [hh']; group
          have hh'1 := comm_mem_v1 C D h3 hzU
          have e : z * (q⁻¹ * z * q)⁻¹ = ((a₀ * h') * z * (a₀ * h')⁻¹ * z⁻¹)⁻¹ := by
            rw [← hqe]; group
          have e2 : (a₀ * h') * z * (a₀ * h')⁻¹ * z⁻¹ =
              (a₀ * (h' * z * h'⁻¹ * z⁻¹) * a₀⁻¹) * (a₀ * z * a₀⁻¹ * z⁻¹) := by group
          rw [e, e2, conj_v1 C ha₀H hh'1]
          exact inv_mem (mul_mem hh'1 hza)
      have h1 := comm_comm_eq C D hpQH hqH hzU
      rw [conj_v1 C hpH hw, mul_inv_cancel] at h1
      calc p * q * p⁻¹ * q⁻¹ * z
          = ((p * q * p⁻¹ * q⁻¹) * z * (p * q * p⁻¹ * q⁻¹)⁻¹ * z⁻¹) * z *
            (p * q * p⁻¹ * q⁻¹) := by group
        _ = z * (p * q * p⁻¹ * q⁻¹) := by rw [h1, one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hcount := relIndex_inf_centralizer_le C D (A := pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T))
    (inf_le_left.trans p_le_qh) hZ₀U fun z hz => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hPQZ x hx z hz
  have hPC : (pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T)) ⊓
      Subgroup.centralizer (fsuU T V : Set G) =
      pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf ?_ inf_le_right)
    rw [C.pq_eq]
    exact le_sup_right
  rw [hPC] at hcount
  have h16 : (pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G)).relIndex
      (pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T)) = 16 := by
    have m := Subgroup.relIndex_mul_relIndex
      (pCoreOf 2 (oTwoUpper H) ⊓ Subgroup.centralizer (fsuU T V : Set G))
      (pCoreOf 2 (oTwoUpper H) ⊓ pCoreOf 2 (L ⊔ T)) (pCoreOf 2 (oTwoUpper H))
      (by rw [C.pq_eq]; exact le_sup_right) inf_le_left
    rw [C.relIndex_pq, C.relIndex_pc] at m
    omega
  omega

theorem exists_y (C : Ctx722 G T L V H γ γ' g k) (D : Data T L V θ c) :
    ∃ y ∈ pCoreOf 2 (L ⊔ T), y ^ 2 ∉ pCoreOf 2 H ∧ y ^ 4 ∈ pCoreOf 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hqQ, hq⟩ := exists_q_not_mem C D
  have hqH : q ∈ H := (pCoreOf_sup_le C.setting.hyp).trans (t_le_h C) hqQ
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L ⊔ T)) ⟨q, hqQ⟩
  have hqn : q ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hex : ∃ m, q ^ (2 ^ m) ∈ pCoreOf 2 H := ⟨n, by rw [hqn]; exact one_mem _⟩
  set m := Nat.find hex with hm
  have hmspec : q ^ (2 ^ m) ∈ pCoreOf 2 H := Nat.find_spec hex
  have hmin : ∀ j < m, q ^ (2 ^ j) ∉ pCoreOf 2 H := fun j hj => Nat.find_min hex hj
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hmspec
    exact hq (Subgroup.mem_sup_right hmspec)
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1, pow_one] at hmspec
    have hqR : q ∈ pCoreOf 2 (L32A.l1 T L V ⊔ T) := by
      exact le_pCoreOf_of_le_normalizer ((pCoreOf_sup_le C.setting.hyp).trans le_sup_right)
        ((sup_le_sup_right (fun x hx => (D.l1_le hx).1) T).trans
          (le_normalizer_pCoreOf (r := 2) (L ⊔ T)))
        (pCoreOf_isPGroup 2 _) hqQ
    set r := QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨q, hqH⟩ : ↥H) with hr
    have hrR : r ∈ modO2Image H (pCoreOf 2 (L32A.l1 T L V ⊔ T)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hqR)
    have hr2 : r ^ 2 = 1 := by
      rw [hr, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have : (⟨q, hqH⟩ : ↥H) ^ 2 = ⟨q ^ 2, pow_mem hqH 2⟩ := rfl
      rw [this, mem_pCore_iff]
      exact hmspec
    obtain ⟨a, ha, har⟩ := Subgroup.mem_map.mp (C.ualpha_omega r hrR hr2)
    rw [hr, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at har
    have h1 : (a : G)⁻¹ * q ∈ pCoreOf 2 H := by
      refine (mem_pCore_iff (H := H) (x := (a : G)⁻¹ * q) (mul_mem (inv_mem a.2) hqH)).mp ?_
      have h2 : (⟨(a : G)⁻¹ * q, mul_mem (inv_mem a.2) hqH⟩ : ↥H) = a⁻¹ * ⟨q, hqH⟩ :=
        Subtype.ext (by simp)
      rw [h2]
      exact har
    apply hq
    have e : q = a * ((a : G)⁻¹ * q) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha))
      (Subgroup.mem_sup_right h1)
  obtain ⟨j, hj⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  refine ⟨q ^ (2 ^ j), pow_mem hqQ _, ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ]
    exact hmin (j + 1) (by omega)
  · rw [← pow_mul, show 2 ^ j * 4 = 2 ^ (j + 2) by ring, ← hj]
    exact hmspec

end CFSG.Quasithin.H13.S4
