module

public import CFSG.Quasithin.Recognition.HSTypeL12f

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

theorem alt_five_invol_conj : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ * σ = 1 →
    σ ≠ 1 → ∃ ρ : Equiv.Perm (Fin 5), Equiv.Perm.sign ρ = 1 ∧
      ρ * σ * ρ⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 := by
  decide +kernel

theorem perm_five_odd_invol_conj : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = -1 →
    σ * σ = 1 → ∃ ρ : Equiv.Perm (Fin 5), Equiv.Perm.sign ρ = 1 ∧
      ρ * σ * ρ⁻¹ = Equiv.swap 0 1 := by
  decide +kernel

theorem card_centralizer_double_transposition : ∀ σ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
      (Finset.univ.filter fun π : Equiv.Perm (Fin 5) => π * σ = σ * π).card = 8 := by
  decide +kernel

theorem card_centralizer_perm_of_alt {σ : Equiv.Perm (Fin 5)} (hs : Equiv.Perm.sign σ = 1)
    (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) = 8 := by
  classical
  rw [← card_centralizer_double_transposition σ hs h2 h1, Nat.card_eq_fintype_card,
    ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun π =>
    Subgroup.mem_centralizer_singleton_iff)

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem exists_K_conj_eq_mul [Finite G] (h : HSSetting z V)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    {a b : ↥(hsH z)} {ρ : Equiv.Perm (Fin 5)} (hρ : Equiv.Perm.sign ρ = 1)
    (hab : ρ * φ a * ρ⁻¹ = φ b) :
    ∃ k ∈ hsK z, ∃ q ∈ hsQ z, k * a * k⁻¹ = b * q := by
  have hA : ρ ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.mpr hρ
  rw [← h.map_K_eq_alternating φ hker] at hA
  obtain ⟨k, hk, rfl⟩ := hA
  have h1 : φ (b⁻¹ * (k * a * k⁻¹)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hab, inv_mul_cancel]
  rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf] at h1
  refine ⟨k, Subgroup.mem_subgroupOf.mp hk, _, h1, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_invol_K_not_Q [Finite G] (h : HSSetting z V) :
    ∃ t ∈ hsK z, t ∉ hsQ z ∧ t * t = 1 ∧ t ∈ hsM V ∧ ∃ v ∈ V, v * t * v⁻¹ = z * t := by
  obtain ⟨m, hm, w, hwZ, hwQ⟩ := h.exists_conj_ZQ_not_le_Q
  obtain ⟨w₀, hw₀Z, -, -, hw₀w₀⟩ := h.exists_mem_ZQ_ne
  have hmQ := le_normalizer_quasithinGenFitting (hsM V) hm
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hwQ
    rw [mul_one, mul_inv_cancel]
    exact (hsQ z).one_mem
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · apply hwQ
      rw [h1]
      exact h.two.le ((Subgroup.mem_normalizer_iff.mp hm z).mp h.mem_V)
  have hww : w * w = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hwZ hw1 with h1 | h1
    · exact absurd (h1 ▸ Subgroup.mem_zpowers z) hwz
    · exact h1.symm
  set x := m * w * m⁻¹ with hx
  set z' := m * z * m⁻¹ with hz'
  have hxx : x * x = z' := by rw [hx, hz', ← hww]; group
  have hz'V : z' ∈ V := (Subgroup.mem_normalizer_iff.mp hm z).mp h.mem_V
  have hz'Q : z' ∈ hsQ z := h.two.le hz'V
  have hxP : x ∈ hsP V := (Subgroup.mem_normalizer_iff.mp hmQ w).mp (h.ZQ_le_P hwZ)
  have hxH : x ∈ hsH z := h.P_le_H hxP
  have hz'Z : z' ∉ hsZQ z := by
    intro hz'Z
    have hz'2 : z' * z' = 1 := by
      rw [hz']
      calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
        _ = 1 := by rw [h.z_mul_z, mul_one, mul_inv_cancel]
    have hz'1 : z' ≠ 1 := by
      intro h1
      apply h.z_ne_one
      have : z = m⁻¹ * z' * m := by rw [hz']; group
      rw [this, h1]
      group
    have hzz' : z' = z := h.eq_z_of_mem_ZQ hz'Z hz'2 hz'1
    apply hwQ
    have hmH : m ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc m * z = m * z * m⁻¹ * m := by group
        _ = z * m := by rw [← hz', hzz'])
    exact ((Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ hmH) w).mp hwZ).1
  have hfix := h.card_fixQ_le hxH hwQ (hxx ▸ hz'Q)
  have hcen := h.card_centralizer_Q hz'Q hz'Z
  obtain ⟨c, ⟨hcQ, hcz'⟩, hcD⟩ : ∃ c ∈ hsQ z ⊓ Subgroup.centralizer ({z'} : Set G),
      c ∉ hsFixQ z x := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show hsQ z ⊓ Subgroup.centralizer ({z'} : Set G) ≤
      hsFixQ z x from fun c hc => hne c hc)
    omega
  have hcz'c : c * z' = z' * c := Subgroup.mem_centralizer_singleton_iff.mp hcz'
  have hmc : m⁻¹ * c * m ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc m⁻¹ * c * m * z = m⁻¹ * (c * z') * m := by rw [hz']; group
      _ = m⁻¹ * (z' * c) * m := by rw [hcz'c]
      _ = z * (m⁻¹ * c * m) := by rw [hz']; group)
  have hcx : c * x * c⁻¹ = x⁻¹ := by
    rcases h.mem_K_or_inverts hmc with hK | hinv
    · exfalso
      apply hcD
      refine ⟨hcQ, ?_⟩
      have h1 : (m⁻¹ * c * m) * w * (m⁻¹ * c * m)⁻¹ = w := by
        rw [← (Subgroup.mem_centralizer_iff.mp hK.2 w hwZ), mul_inv_cancel_right]
      have hcx' : c * x * c⁻¹ = x := by
        rw [hx]
        calc c * (m * w * m⁻¹) * c⁻¹ = m * ((m⁻¹ * c * m) * w * (m⁻¹ * c * m)⁻¹) * m⁻¹ := by
              group
          _ = m * w * m⁻¹ := by rw [h1]
      have : x * c * x⁻¹ * c⁻¹ = 1 := by
        have hxc : x * c = c * x := by
          calc x * c = c * x * c⁻¹ * c := by rw [hcx']
            _ = c * x := by group
        rw [hxc]
        group
      rw [this]
      exact (hsZQ z).one_mem
    · have h1 := hinv w hwZ
      rw [hx]
      calc c * (m * w * m⁻¹) * c⁻¹ = m * ((m⁻¹ * c * m) * w * (m⁻¹ * c * m)⁻¹) * m⁻¹ := by
            group
        _ = (m * w * m⁻¹)⁻¹ := by rw [h1]; group
  obtain ⟨c', hc'Q, hc'c', hc'x⟩ : ∃ c' ∈ hsQ z, c' * c' = 1 ∧ c' * x * c'⁻¹ = x⁻¹ := by
    rcases h.mul_self_eq_one_or_z hcQ with hc2 | hc2
    · exact ⟨c, hcQ, hc2, hcx⟩
    · refine ⟨c * w₀, (hsQ z).mul_mem hcQ hw₀Z.1, ?_, ?_⟩
      · have hcw : c * w₀ = w₀ * c := (Subgroup.mem_centralizer_iff.mp hw₀Z.2 c hcQ)
        calc c * w₀ * (c * w₀) = (c * c) * (w₀ * w₀) := by
              rw [show c * w₀ * (c * w₀) = c * (w₀ * c) * w₀ by group, ← hcw]; group
          _ = 1 := by rw [hc2, hw₀w₀, h.z_mul_z]
      · have hw₀x : w₀ * x = x * w₀ := h.P_comm (h.ZQ_le_P hw₀Z) hxP
        calc c * w₀ * x * (c * w₀)⁻¹ = c * (w₀ * x * w₀⁻¹) * c⁻¹ := by group
          _ = c * x * c⁻¹ := by rw [hw₀x, mul_inv_cancel_right]
          _ = x⁻¹ := hcx
  have hc'inv : c'⁻¹ = c' := inv_eq_of_mul_eq_one_left hc'c'
  have hxQ : x ∉ hsQ z := hwQ
  have htQ : c' * x ∉ hsQ z := by
    intro htQ
    apply hxQ
    have := (hsQ z).mul_mem ((hsQ z).inv_mem hc'Q) htQ
    simpa using this
  have htK : c' * x ∈ hsK z := (hsK z).mul_mem (h.Q_le_K hc'Q) (h.P_le_K hxP)
  have htt : c' * x * (c' * x) = 1 := by
    calc c' * x * (c' * x) = (c' * x * c'⁻¹) * (c' * c') * x := by group
      _ = 1 := by rw [hc'x, hc'c', mul_one, inv_mul_cancel]
  have htM : c' * x ∈ hsM V := (hsM V).mul_mem (h.Q_le_M hc'Q) (h.P_le_M hxP)
  have htP : c' * x ∉ hsP V := fun htP => htQ (h.two.le (h.mem_V_of_mem_P htP htt))
  obtain ⟨v, hvV, hvt⟩ : ∃ v ∈ V, v * (c' * x) ≠ (c' * x) * v := by
    by_contra hne
    push Not at hne
    apply htP
    rw [← h.centralizer_V_eq]
    exact ⟨htM, Subgroup.mem_centralizer_iff.mpr fun v hv => hne v hv⟩
  have hvQ : v ∈ hsQ z := h.two.le hvV
  have hvx : Commute v x := h.P_comm (h.V_le_P hvV) hxP
  have hvx' : v⁻¹ * x = x * v⁻¹ := hvx.inv_left.eq
  have hcomm : v * (c' * x) * v⁻¹ * (c' * x)⁻¹ = v * c' * v⁻¹ * c'⁻¹ := by
    calc v * (c' * x) * v⁻¹ * (c' * x)⁻¹ = v * c' * (x * v⁻¹) * x⁻¹ * c'⁻¹ := by group
      _ = v * c' * (v⁻¹ * x) * x⁻¹ * c'⁻¹ := by rw [hvx']
      _ = v * c' * v⁻¹ * c'⁻¹ := by group
  refine ⟨c' * x, htK, htQ, htt, htM, v, hvV, ?_⟩
  rcases h.comm_eq_one_or_z hvQ hc'Q with h1 | h1
  · exfalso
    apply hvt
    rw [← hcomm] at h1
    calc v * (c' * x) = v * (c' * x) * v⁻¹ * (c' * x)⁻¹ * ((c' * x) * v) := by group
      _ = (c' * x) * v := by rw [h1, one_mul]
  · rw [← hcomm] at h1
    calc v * (c' * x) * v⁻¹ = v * (c' * x) * v⁻¹ * (c' * x)⁻¹ * (c' * x) := by group
      _ = z * (c' * x) := by rw [h1]

theorem exists_conj_of_invol_mul_K [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) {v : G} (hvQ : v ∈ hsQ z) (hvt : v * t * v⁻¹ = z * t)
    {q : G} (hq : q ∈ hsQ z) (htq : t * q * (t * q) = 1) : ∃ r ∈ hsQ z, t * q = r * t * r⁻¹ := by
  obtain ⟨r, hr, u, hu, htqu⟩ := h.exists_conj_mul_ZQ_of_invol htK.1 htQ htt hq htq
  have hut : u * t = t * u := Subgroup.mem_centralizer_iff.mp htK.2 u hu
  have huu : u * u = 1 := by
    have h1 : t * u * (t * u) = 1 := by
      have h2 : r * (t * u) * r⁻¹ * (r * (t * u) * r⁻¹) = 1 := by rw [← htqu]; exact htq
      have h3 : r * (t * u * (t * u)) * r⁻¹ = 1 := by
        rw [← h2]
        group
      calc t * u * (t * u) = r⁻¹ * (r * (t * u * (t * u)) * r⁻¹) * r := by group
        _ = 1 := by rw [h3]; group
    have h4 : t * u * (t * u) = u * u := by
      calc t * u * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [hut]
        _ = (t * t) * (u * u) := by group
        _ = u * u := by rw [htt, one_mul]
    rw [← h4]
    exact h1
  by_cases hu1 : u = 1
  · exact ⟨r, hr, by rw [htqu, hu1, mul_one]⟩
  · have huz : u = z := h.eq_z_of_mem_ZQ hu huu hu1
    have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp htK.1
    refine ⟨r * v, (hsQ z).mul_mem hr hvQ, ?_⟩
    rw [htqu, huz, htz, ← hvt]
    group

theorem exists_K_conj_of_invol [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) {v : G} (hvQ : v ∈ hsQ z) (hvt : v * t * v⁻¹ = z * t)
    {t' : G} (ht'K : t' ∈ hsK z) (ht'Q : t' ∉ hsQ z) (ht't' : t' * t' = 1) :
    ∃ k ∈ hsK z, k * t' * k⁻¹ = t := by
  obtain ⟨φ, -, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hsign : ∀ a : ↥(hsH z), (a : G) ∈ hsK z → Equiv.Perm.sign (φ a) = 1 := by
    intro a ha
    have : φ a ∈ alternatingGroup (Fin 5) := by
      rw [← h.map_K_eq_alternating φ hker]
      exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp this
  set a : ↥(hsH z) := ⟨t', ht'K.1⟩
  set b : ↥(hsH z) := ⟨t, htK.1⟩
  have hinv : ∀ c : ↥(hsH z), (c : G) * c = 1 → (c : G) ∉ hsQ z →
      φ c * φ c = 1 ∧ φ c ≠ 1 := by
    intro c hc hcQ
    refine ⟨?_, fun h1 => hcQ ((hkerQ c).mp h1)⟩
    rw [← map_mul]
    have : c * c = 1 := Subtype.ext hc
    rw [this, map_one]
  obtain ⟨ha2, ha1⟩ := hinv a ht't' ht'Q
  obtain ⟨hb2, hb1⟩ := hinv b htt htQ
  obtain ⟨ρa, hρa, ha⟩ := alt_five_invol_conj (φ a) (hsign a ht'K) ha2 ha1
  obtain ⟨ρb, hρb, hb⟩ := alt_five_invol_conj (φ b) (hsign b htK) hb2 hb1
  have hρ : Equiv.Perm.sign (ρb⁻¹ * ρa) = 1 := by
    rw [map_mul, map_inv, hρa, hρb, inv_one, one_mul]
  have hab : ρb⁻¹ * ρa * φ a * (ρb⁻¹ * ρa)⁻¹ = φ b := by
    calc ρb⁻¹ * ρa * φ a * (ρb⁻¹ * ρa)⁻¹ = ρb⁻¹ * (ρa * φ a * ρa⁻¹) * ρb := by group
      _ = ρb⁻¹ * (ρb * φ b * ρb⁻¹) * ρb := by rw [ha, hb]
      _ = φ b := by group
  obtain ⟨k, hk, q, hq, hkq⟩ := h.exists_K_conj_eq_mul hker hρ hab
  have htq : t * q * (t * q) = 1 := by
    have : k * t' * k⁻¹ * (k * t' * k⁻¹) = 1 := by
      calc k * t' * k⁻¹ * (k * t' * k⁻¹) = k * (t' * t') * k⁻¹ := by group
        _ = 1 := by rw [ht't', mul_one, mul_inv_cancel]
    rw [hkq] at this
    exact this
  obtain ⟨r, hr, hrq⟩ := h.exists_conj_of_invol_mul_K htK htQ htt hvQ hvt hq htq
  refine ⟨r⁻¹ * k, (hsK z).mul_mem (h.Q_le_K ((hsQ z).inv_mem hr)) hk, ?_⟩
  have : k * t' * k⁻¹ = r * t * r⁻¹ := by rw [hkq, hrq]
  calc r⁻¹ * k * t' * (r⁻¹ * k)⁻¹ = r⁻¹ * (k * t' * k⁻¹) * r := by group
    _ = t := by rw [this]; group

theorem card_centralizer_invol_K [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) {v : G} (hvQ : v ∈ hsQ z) (hvt : v * t * v⁻¹ = z * t) :
    Nat.card ↥(hsQ z ⊓ Subgroup.centralizer ({t} : Set G)) = 8 := by
  have htH : t ∈ hsH z := htK.1
  have ht2 : t * t ∈ hsQ z := by rw [htt]; exact (hsQ z).one_mem
  set D := hsFixQ z t with hD
  set C := hsQ z ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hCD : C ≤ D := by
    rintro c ⟨hcQ, hct⟩
    refine ⟨hcQ, ?_⟩
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hct, mul_inv_cancel_right, mul_inv_cancel]
    exact (hsZQ z).one_mem
  have he : ∀ d ∈ D, t * d * t⁻¹ * d⁻¹ = 1 ∨ t * d * t⁻¹ * d⁻¹ = z := by
    intro d hd
    set e := t * d * t⁻¹ * d⁻¹ with he
    have heZ : e ∈ hsZQ z := hd.2
    have hed : e * d = d * e := Subgroup.mem_centralizer_iff.mp heZ.2 d hd.1 |>.symm
    have hdd := h.mul_self_eq_one_or_z hd.1
    have htd : (t * d * t⁻¹) * (t * d * t⁻¹) = d * d := by
      calc (t * d * t⁻¹) * (t * d * t⁻¹) = t * (d * d) * t⁻¹ := by group
        _ = d * d := by rw [← comm_of_eq_one_or_z hdd htH, mul_inv_cancel_right]
    have hee : e * e = 1 := by
      have h1 : t * d * t⁻¹ = e * d := by rw [he]; group
      rw [h1] at htd
      have : e * d * (e * d) = (e * e) * (d * d) := by
        rw [show e * d * (e * d) = e * (d * e) * d by group, ← hed]; group
      rw [this] at htd
      exact mul_eq_right.mp htd
    by_cases he1 : e = 1
    · exact Or.inl he1
    · exact Or.inr (h.eq_z_of_mem_ZQ heZ hee he1)
  have hmemC : ∀ d ∈ D, d ∈ C ↔ t * d * t⁻¹ * d⁻¹ = 1 := by
    intro d hd
    constructor
    · rintro ⟨-, hdt⟩
      rw [← Subgroup.mem_centralizer_singleton_iff.mp hdt, mul_inv_cancel_right, mul_inv_cancel]
    · intro h1
      refine ⟨hd.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc d * t = (t * d * t⁻¹ * d⁻¹)⁻¹ * t * d := by group
        _ = t * d := by rw [h1, inv_one, one_mul]
  have hvc : t * v * t⁻¹ * v⁻¹ = z := by
    have h1 : v * t * v⁻¹ * t⁻¹ = z := by rw [hvt]; group
    have h2 := h.comm_eq_one_or_z hvQ (show t * v * t⁻¹ ∈ hsQ z from conj_mem_Q htH hvQ)
    calc t * v * t⁻¹ * v⁻¹ = (v * t * v⁻¹ * t⁻¹)⁻¹ := by group
      _ = z := by rw [h1]; exact inv_eq_of_mul_eq_one_left h.z_mul_z
  have hvD : v ∈ D := ⟨hvQ, by rw [hvc]; exact h.z_mem_ZQ⟩
  have hidx : (C.subgroupOf D).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨v, hvD⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    have hbD : (b : G) ∈ D := b.2
    have hbvD : (b : G) * v ∈ D := D.mul_mem hbD hvD
    rw [hmemC _ hbvD, hmemC _ hbD]
    have hprod : t * ((b : G) * v) * t⁻¹ * ((b : G) * v)⁻¹ =
        (t * (b : G) * t⁻¹ * (b : G)⁻¹) * z := by
      have hb' : t * (b : G) * t⁻¹ * (b : G)⁻¹ ∈ hsH z := by
        rcases he _ hbD with h1 | h1 <;> rw [h1]
        · exact (hsH z).one_mem
        · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      calc t * ((b : G) * v) * t⁻¹ * ((b : G) * v)⁻¹ =
          (t * (b : G) * t⁻¹) * (t * v * t⁻¹ * v⁻¹) * (b : G)⁻¹ := by group
        _ = (t * (b : G) * t⁻¹) * z * (b : G)⁻¹ := by rw [hvc]
        _ = (t * (b : G) * t⁻¹ * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by group
        _ = (t * (b : G) * t⁻¹ * (b : G)⁻¹) * z := by
          rw [h.comm_z_of_mem_Q hbD.1, mul_inv_cancel_right]
    rw [hprod]
    rcases he _ hbD with h1 | h1 <;> rw [h1]
    · rw [one_mul]
      exact Or.inr ⟨rfl, h.z_ne_one⟩
    · rw [h.z_mul_z]
      exact Or.inl ⟨rfl, h.z_ne_one⟩
  have h1 := Subgroup.card_mul_index (C.subgroupOf D)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCD).toEquiv,
    h.card_fixQ_eq htH htQ ht2] at h1
  omega

theorem card_centralizer_H_of_conj [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hφ : Function.Surjective φ)
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    (hconj : ∀ g ∈ hsH z, g * x * g⁻¹ * x⁻¹ ∈ hsQ z → ∃ r ∈ hsQ z, g * x * g⁻¹ = r * x * r⁻¹) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({φ ⟨x, hxH⟩} : Set (Equiv.Perm (Fin 5)))) *
        Nat.card ↥(hsQ z ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set C' : Subgroup ↥(hsH z) := (Subgroup.centralizer ({x} : Set G)).subgroupOf (hsH z)
  set x' : ↥(hsH z) := ⟨x, hxH⟩
  have hmap : C'.map φ = Subgroup.centralizer ({φ x'} : Set (Equiv.Perm (Fin 5))) := by
    ext π
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hcx : c * x' = x' * c :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hc))
      rw [← map_mul, ← map_mul, hcx]
    · intro hπ
      obtain ⟨g, rfl⟩ := hφ π
      have hgx : φ g * φ x' = φ x' * φ g := Subgroup.mem_centralizer_singleton_iff.mp hπ
      have h1 : φ (g * x' * g⁻¹ * x'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgx]
        group
      have h2 := (hkerQ _).mp h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      obtain ⟨r, hr, hgr⟩ := hconj g g.2 h2
      refine ⟨⟨r, h.Q_le_H hr⟩⁻¹ * g, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc r⁻¹ * g * x = r⁻¹ * (g * x * (g : G)⁻¹) * g := by group
          _ = r⁻¹ * (r * x * r⁻¹) * g := by rw [hgr]
          _ = x * (r⁻¹ * g) := by group
      · rw [map_mul, map_inv, (hkerQ ⟨r, h.Q_le_H hr⟩).mpr hr, inv_one, one_mul]
  have hrange : (φ.comp C'.subtype).range = C'.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerc : (φ.comp C'.subtype).ker = ((hsQ z).subgroupOf (hsH z)).subgroupOf C' := by
    ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      Subgroup.mem_subgroupOf]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.comp C'.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hrange, hmap,
    hkerc] at h1
  have e1 : ↥C' ≃ ↥(hsH z ⊓ Subgroup.centralizer ({x} : Set G)) :=
    { toFun := fun y => ⟨y.1.1, y.1.2, Subgroup.mem_subgroupOf.mp y.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, Subgroup.mem_subgroupOf.mpr g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : ↥(((hsQ z).subgroupOf (hsH z)).subgroupOf C') ≃
      ↥(hsQ z ⊓ Subgroup.centralizer ({x} : Set G)) :=
    { toFun := fun y => ⟨y.1.1.1, Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp y.2),
        Subgroup.mem_subgroupOf.mp y.1.2⟩
      invFun := fun g => ⟨⟨⟨g.1, h.Q_le_H g.2.1⟩, Subgroup.mem_subgroupOf.mpr g.2.2⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr g.2.1)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e1, ← Nat.card_congr e2]
  exact h1

theorem card_centralizer_H_invol_K [Finite G] (h : HSSetting z V) {t : G} (htK : t ∈ hsK z)
    (htQ : t ∉ hsQ z) (htt : t * t = 1) {v : G} (hvQ : v ∈ hsQ z) (hvt : v * t * v⁻¹ = z * t) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({t} : Set G)) = 64 := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hconj : ∀ g ∈ hsH z, g * t * g⁻¹ * t⁻¹ ∈ hsQ z →
      ∃ r ∈ hsQ z, g * t * g⁻¹ = r * t * r⁻¹ := by
    intro g hg hq
    have hmem : t⁻¹ * (g * t * g⁻¹) ∈ hsQ z := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_quasithinGenFitting (hsH z)
        ((hsH z).inv_mem htK.1)) _).mp hq
      have heq : t⁻¹ * (g * t * g⁻¹ * t⁻¹) * t⁻¹⁻¹ = t⁻¹ * (g * t * g⁻¹) := by group
      rwa [heq] at this
    have hinvol : t * (t⁻¹ * (g * t * g⁻¹)) * (t * (t⁻¹ * (g * t * g⁻¹))) = 1 := by
      calc t * (t⁻¹ * (g * t * g⁻¹)) * (t * (t⁻¹ * (g * t * g⁻¹))) = g * (t * t) * g⁻¹ := by
            group
        _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
    obtain ⟨r, hr, hrt⟩ := h.exists_conj_of_invol_mul_K htK htQ htt hvQ hvt hmem hinvol
    refine ⟨r, hr, ?_⟩
    rw [← hrt]
    group
  rw [h.card_centralizer_H_of_conj htK.1 hφ hker hconj,
    h.card_centralizer_invol_K htK htQ htt hvQ hvt]
  have hsign : Equiv.Perm.sign (φ ⟨t, htK.1⟩) = 1 := by
    have : φ ⟨t, htK.1⟩ ∈ alternatingGroup (Fin 5) := by
      rw [← h.map_K_eq_alternating φ hker]
      exact ⟨⟨t, htK.1⟩, Subgroup.mem_subgroupOf.mpr htK, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp this
  have h2 : φ ⟨t, htK.1⟩ * φ ⟨t, htK.1⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htK.1⟩ : ↥(hsH z)) * ⟨t, htK.1⟩ = 1 := Subtype.ext htt
    rw [this, map_one]
  have h1 : φ ⟨t, htK.1⟩ ≠ 1 := fun h1 => htQ ((hkerQ _).mp h1)
  rw [card_centralizer_perm_of_alt hsign h2 h1]

end HSSetting

end CFSG.Quasithin.HSType
