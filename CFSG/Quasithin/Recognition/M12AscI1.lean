module

public import CFSG.Quasithin.Recognition.M12AscV
public import CFSG.Quasithin.Recognition.M12AscEF
public import CFSG.Quasithin.Recognition.M12AscIModel
public import CFSG.Quasithin.Recognition.M12AscGen

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable (m : AscModel z)

include m

theorem zconj_mem_fSub [Finite G] (hyp : Asc03Hyp G z) {x : G} (hxQ : x ∈ ascQ z)
    (hx : IsConj z x) : x ∈ m.fSub := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  have hx1 : x ≠ 1 := by rw [← hc]; exact asc_conj_ne_one hyp c
  exact (m.conj_mem_Q_iff hyp hxQ hx1).1 ⟨c, hc⟩

theorem not_isConj_of_notMem_fSub [Finite G] (hyp : Asc03Hyp G z) {t : G} (htQ : t ∈ ascQ z)
    (htF : t ∉ m.fSub) : ¬ IsConj z t := fun h => htF (m.zconj_mem_fSub hyp htQ h)

theorem V_norm_Q [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {q v : G} (hq : q ∈ ascQ z) (hv : v ∈ m.ascV hyp hgz hsQ) :
    q * v * q⁻¹ ∈ m.ascV hyp hgz hsQ := by
  have hE := extraspecialAt_ascQ hyp
  have hvQ : v ∈ ascQ z := m.fSub_le_ascQ hyp (m.ascV_le_fSub hyp hgz hsQ hv)
  have hzV : z ∈ m.ascV hyp hgz hsQ := (m.mem_ascV hyp hgz hsQ).2 (Or.inr (Or.inl rfl))
  rcases hE.comm_mem q hq v hvQ with h | h
  · have : q * v * q⁻¹ = v := by
      calc q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
        _ = v := by rw [h, one_mul]
    rw [this]
    exact hv
  · have : q * v * q⁻¹ = z * v := by
      calc q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
        _ = z * v := by rw [h]
    rw [this]
    exact mul_mem hzV hv

theorem fSub_comm_mem_V [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {t : G} (htF : t ∉ m.fSub)
    (hVt : ∀ v ∈ m.ascV hyp hgz hsQ, v * t = t * v) :
    ∀ x ∈ m.fSub, x * t = t * x → x ∈ m.ascV hyp hgz hsQ := by
  set V := m.ascV hyp hgz hsQ with hV
  set W : Subgroup G := m.fSub ⊓ Subgroup.centralizer ({t} : Set G) with hW
  have hWle : W ≤ m.fSub := inf_le_left
  have hVW : V ≤ W := fun v hv =>
    ⟨m.ascV_le_fSub hyp hgz hsQ hv, Subgroup.mem_centralizer_singleton_iff.2 (hVt v hv)⟩
  have hWF : W ≠ m.fSub := by
    intro e
    apply htF
    refine m.le_fSub_of_centralizes (fun f hf => ?_)
    have hfW : f ∈ W := by rw [e]; exact hf
    exact (Subgroup.mem_centralizer_singleton_iff.1 hfW.2).symm
  have hdvd : Nat.card W ∣ 8 := by
    have := Subgroup.card_dvd_of_le hWle
    rwa [m.card_fSub] at this
  have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  have hmem : Nat.card W ∈ Nat.divisors 8 := by simp [hdvd]
  rw [hd] at hmem
  have h8 : Nat.card W ≠ 8 := fun h =>
    hWF (Subgroup.eq_of_le_of_card_ge hWle (by rw [m.card_fSub, h]))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hVcard : Nat.card V = 4 := m.card_ascV hyp hgz hsQ
  have hcardle : Nat.card V ≤ Nat.card W := Subgroup.card_le_of_le hVW
  have hW4 : Nat.card W = 4 := by omega
  have hVW' : V = W := Subgroup.eq_of_le_of_card_ge hVW (by omega)
  intro x hx hxt
  rw [hVW']
  exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxt⟩

theorem not_conj_mem_V [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {w : G} (hwQ : w ∈ ascQ z) (hwF : w ∉ m.fSub) (a : G) :
    a⁻¹ * w * a ∉ m.ascV hyp hgz hsQ := by
  intro hmem
  have hF' : a⁻¹ * w * a ∈ m.fSub := m.ascV_le_fSub hyp hgz hsQ hmem
  by_cases h1 : a⁻¹ * w * a = 1
  · apply hwF
    have : w = 1 := by
      calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact one_mem _
  · obtain ⟨c, hc⟩ := (m.conj_mem_Q_iff hyp (m.fSub_le_ascQ hyp hF') h1).2 hF'
    have : (a * c) * z * (a * c)⁻¹ = w := by
      calc (a * c) * z * (a * c)⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by group
        _ = a * (a⁻¹ * w * a) * a⁻¹ := by rw [hc]
        _ = w := by group
    exact hwF (m.zconj_mem_fSub hyp hwQ (isConj_iff.2 ⟨a * c, this⟩))

theorem exists_t_data [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) {g : G}
    (hgz : g * z * g⁻¹ ≠ z) (hsQ : g * z * g⁻¹ ∈ ascQ z) :
    ∃ y t : G, y ∈ Subgroup.normalizer (m.ascV hyp hgz hsQ : Set G) ∧ y * y * y = 1 ∧
      y * z * y⁻¹ ≠ z ∧ t ∈ ascQ z ∧ t ∉ m.fSub ∧ t * t = 1 ∧
      (∀ v ∈ m.ascV hyp hgz hsQ, v * t = t * v) ∧ y * t * y⁻¹ = t := by
  obtain ⟨y, t, hyN, hy3, hyz, htE, htV, hyt⟩ := m.exists_order_three_fixing hyp hgz hsQ
  have hEF := m.E_ne_fSub hyp hgz hsQ
  obtain ⟨-, hE8, helem, -⟩ := config_of_conj hyp hgz hsQ
  have ht2 : t * t = 1 := (helem t htE).1
  have hVE := m.ascV_le_E hyp hgz hsQ
  have hVt : ∀ v ∈ m.ascV hyp hgz hsQ, v * t = t * v := fun v hv =>
    (helem v (hVE v hv)).2 t htE
  refine ⟨y, t, hyN, hy3, hyz, htE.1, ?_, ht2, hVt, hyt⟩
  intro htF
  set V := m.ascV hyp hgz hsQ with hV
  have hrV : ∀ v ∈ V, t * v * t⁻¹ ∈ V := by
    intro v hv
    have h := hVt v hv
    have e : t * v * t⁻¹ = v := by
      calc t * v * t⁻¹ = v * t * t⁻¹ := by rw [← h]
        _ = v := by group
    rw [e]
    exact hv
  set W := extInv V t ht2 hrV with hW
  have hWcard : Nat.card W = 8 := by
    have := card_extInv (V := V) (r := t) (hr2 := ht2) (hrV := hrV) htV
    rw [m.card_ascV hyp hgz hsQ] at this
    omega
  have hWE : W ≤ ascE z g := by
    intro x hx
    rcases hx with h | ⟨v, hv, rfl⟩
    · exact hVE x h
    · exact mul_mem (hVE v hv) htE
  have hWF : W ≤ m.fSub := by
    intro x hx
    rcases hx with h | ⟨v, hv, rfl⟩
    · exact m.ascV_le_fSub hyp hgz hsQ h
    · exact mul_mem (m.ascV_le_fSub hyp hgz hsQ hv) htF
  have h1 : W = ascE z g := Subgroup.eq_of_le_of_card_ge hWE (by rw [hWcard]; exact hE8.le)
  have h2 : W = m.fSub :=
    Subgroup.eq_of_le_of_card_ge hWF (by rw [hWcard, m.card_fSub])
  exact hEF (h1.symm.trans h2)

theorem cSub_maximal [Finite G] (hyp : Asc03Hyp G z) {t : G} (htQ : t ∈ ascQ z)
    (htF : t ∉ m.fSub)
    (hf : m.tb t ∈ qTabs ∧ m.tb t ∉ FTabs ∧ tmul (m.tb t) (m.tb t) = tid) :
    ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({t} : Set G) → IsPGroup 2 R → m.cSub hf ≤ R →
      R = m.cSub hf := by
  apply maximal2_of_normalizer
  intro n hn hS
  have hnt : n * t = t * n := Subgroup.mem_centralizer_singleton_iff.1 hn
  have hnN : n ∈ Subgroup.normalizer ((m.cSub hf : Subgroup G) : Set G) :=
    mem_normalizer_of_forall_conj_mem hS
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hzt : z * t = t * z :=
    (Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH z htQ)).symm
  have hzS : z ∈ m.cSub hf := (m.mem_cSub_iff htQ hf).2 ⟨z_mem_ascH z, hzt⟩
  have hcS : n * z * n⁻¹ ∈ m.cSub hf := hS z hzS
  have hcen : ∀ s ∈ m.cSub hf, (n * z * n⁻¹) * s = s * (n * z * n⁻¹) := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ m.cSub hf := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) s).1 hs
      simpa using this
    have hzc : z * (n⁻¹ * s * n) = (n⁻¹ * s * n) * z :=
      (Subgroup.mem_centralizer_singleton_iff.1 ((m.mem_cSub_iff htQ hf).1 hs').1).symm
    calc (n * z * n⁻¹) * s = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by rw [hzc]
      _ = s * (n * z * n⁻¹) := by group
  rcases m.center_cSub htQ hf hcS hcen with h | h | h | h
  · exfalso
    apply asc_z_ne_one hyp
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · have hnH : n ∈ ascH z := by
      rw [ascH, Subgroup.mem_centralizer_singleton_iff]
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [h]
    exact (m.mem_cSub_iff htQ hf).2 ⟨hnH, hnt⟩
  · exfalso
    exact m.not_isConj_of_notMem_fSub hyp htQ htF (isConj_iff.2 ⟨n, h⟩)
  · exfalso
    have hztQ : z * t ∈ ascQ z := mul_mem (z_mem_ascQ hyp) htQ
    have hztF : z * t ∈ m.fSub := m.zconj_mem_fSub hyp hztQ (isConj_iff.2 ⟨n, h⟩)
    apply htF
    have : t = z * (z * t) := by rw [← mul_assoc, hz2, one_mul]
    rw [this]
    exact mul_mem m.z_mem_fSub hztF

end AscModel

end CFSG.Quasithin
