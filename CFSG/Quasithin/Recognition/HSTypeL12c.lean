module

public import CFSG.Quasithin.Recognition.HSTypeL12b
public import CFSG.Quasithin.Recognition.HSTypeL11
public import CFSG.Quasithin.Recognition.HSTypeL12a

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem zpowers_eq_ZQ [Finite G] (h : HSSetting z V) {u : G} (hu : u ∈ hsZQ z)
    (huz : u ∉ Subgroup.zpowers z) : Subgroup.zpowers u = hsZQ z := by
  have hu1 : u ≠ 1 := fun h1 => huz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have huz' : u ≠ z := fun h1 => huz (h1 ▸ Subgroup.mem_zpowers z)
  have huu : u * u = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hu hu1 with h1 | h1
    · exact absurd h1.symm huz'
    · exact h1.symm
  have hle : Subgroup.zpowers u ≤ hsZQ z := (Subgroup.zpowers_le).mpr hu
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h.card_ZQ, Nat.card_zpowers]
  have h4 : u ^ 4 = 1 := by
    have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
    calc u ^ 4 = (u * u) * (u * u) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [huu, hzz]
  have hdvd : orderOf u ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hne1 : orderOf u ≠ 1 := fun h1 => hu1 (orderOf_eq_one_iff.mp h1)
  have hne2 : orderOf u ≠ 2 := by
    intro h2
    have : u * u = 1 := by rw [← sq, ← h2]; exact pow_orderOf_eq_one u
    rw [huu] at this
    exact h.z_ne_one this
  have hle4 : orderOf u ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hc : orderOf u <;> simp_all

theorem card_centralizer_Q (h : HSSetting z V) {x : G} (hx : x ∈ hsQ z) (hxZ : x ∉ hsZQ z) :
    Nat.card ↥(hsQ z ⊓ Subgroup.centralizer ({x} : Set G)) = 32 := by
  have hx' : (⟨x, hx⟩ : ↥(hsQ z)) ∉ Subgroup.center ↥(hsQ z) := by
    rw [← ZQ_subgroupOf_eq_center]
    exact hxZ
  rw [← card_centralizer_of_isZ4Q8Q8 h.one.fstar hx']
  refine Nat.card_congr ⟨fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩, fun y => ⟨y.1.1, y.1.2, ?_⟩,
    fun y => rfl, fun y => rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2.2))
  · exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.2))

theorem mem_ZQ_eq [Finite G] (h : HSSetting z V) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {x : G} (hx : x ∈ hsZQ z) :
    x = 1 ∨ x = w ∨ x = z ∨ x = w⁻¹ := by
  have hw1 : w ≠ 1 := fun h1 => hwz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hwz' : w ≠ z := fun h1 => hwz (h1 ▸ Subgroup.mem_zpowers z)
  have hww : w * w = z := by
    rcases h.z_eq_or_sq_of_mem_ZQ hwZ hw1 with h1 | h1
    · exact absurd h1.symm hwz'
    · exact h1.symm
  have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  rcases h.z_eq_or_sq_of_mem_ZQ hx hx1 with h1 | h1
  · exact Or.inr (Or.inr (Or.inl h1.symm))
  have hxw : x * w = w * x := Subgroup.mem_centralizer_iff.mp hwZ.2 x hx.1
  by_cases hxw1 : x * w = 1
  · right; right; right
    exact eq_inv_of_mul_eq_one_left hxw1
  rcases h.z_eq_or_sq_of_mem_ZQ ((hsZQ z).mul_mem hx hwZ) hxw1 with h2 | h2
  · right; left
    calc x = x * w * w⁻¹ := by group
      _ = z * w⁻¹ := by rw [← h2]
      _ = w := by rw [← hww]; group
  · exfalso
    apply h.z_ne_one
    calc z = x * w * (x * w) := h2
      _ = (x * x) * (w * w) := by
        rw [show x * w * (x * w) = x * (w * x) * w by group, ← hxw]; group
      _ = 1 := by rw [← h1, hww, hzz]

theorem conj_eq_or_inv [Finite G] (h : HSSetting z V) {w : G} (hwZ : w ∈ hsZQ z)
    (hwz : w ∉ Subgroup.zpowers z) {g : G} (hg : g ∈ hsH z) :
    g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹ := by
  have hgw : g * w * g⁻¹ ∈ hsZQ z :=
    (Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_ZQ hg) w).mp hwZ
  have hw1 : w ≠ 1 := fun h1 => hwz (h1 ▸ (Subgroup.zpowers z).one_mem)
  have hwz' : w ≠ z := fun h1 => hwz (h1 ▸ Subgroup.mem_zpowers z)
  rcases h.mem_ZQ_eq hwZ hwz hgw with h1 | h1 | h1 | h1
  · exfalso
    apply hw1
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · exact Or.inl h1
  · exfalso
    apply hwz'
    have hgz : g * z * g⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1, hgz]
      _ = z := by group
  · exact Or.inr h1

theorem mem_K_or_inverts [Finite G] (h : HSSetting z V) {g : G} (hg : g ∈ hsH z) :
    g ∈ hsK z ∨ ∀ u ∈ hsZQ z, g * u * g⁻¹ = u⁻¹ := by
  obtain ⟨w, hwZ, hw1, hwz', hww⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
  rcases h.conj_eq_or_inv hwZ hwz hg with hc | hc
  · left
    refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : g * u * g⁻¹ = u := by
      rcases h.mem_ZQ_eq hwZ hwz hu with h1 | h1 | h1 | h1 <;> rw [h1]
      · group
      · exact hc
      · exact hgz
      · calc g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ := by group
          _ = w⁻¹ := by rw [hc]
    calc u * g = g * u * g⁻¹ * g := by rw [hu']
      _ = g * u := by group
  · right
    intro u hu
    rcases h.mem_ZQ_eq hwZ hwz hu with h1 | h1 | h1 | h1 <;> rw [h1]
    · group
    · exact hc
    · rw [hgz, hzinv]
    · calc g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ := by group
        _ = w⁻¹⁻¹ := by rw [hc]

theorem exists_invol_inverts_ZQ [Finite G] (h : HSSetting z V) :
    ∃ s ∈ hsH z ⊓ hsM V, s * s = 1 ∧ (∀ u ∈ hsZQ z, s * u * s⁻¹ = u⁻¹) ∧
      ∃ g : G, g * z * g⁻¹ = s := by
  obtain ⟨m, hm, w, hwZ, hwQ⟩ := h.exists_conj_ZQ_not_le_Q
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
  have hZw := h.zpowers_eq_ZQ hwZ hwz
  set t := m * w * m⁻¹ with ht
  set z' := m * z * m⁻¹ with hz'
  have htt : t * t = z' := by rw [ht, hz', ← hww]; group
  have hz'V : z' ∈ V := (Subgroup.mem_normalizer_iff.mp hm z).mp h.mem_V
  have hz'Q : z' ∈ hsQ z := h.two.le hz'V
  have htP : t ∈ hsP V := (Subgroup.mem_normalizer_iff.mp hmQ w).mp (h.ZQ_le_P hwZ)
  have htH : t ∈ hsH z := h.P_le_H htP
  have hz'Z : z' ∉ hsZQ z := by
    intro hz'Z
    have hz'2 : z' * z' = 1 := by
      rw [hz']
      have hzz : z * z = 1 := by rw [← sq]; exact h.sq_z
      calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
        _ = 1 := by rw [hzz, mul_one, mul_inv_cancel]
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
  have hfix := h.card_fixQ_le htH hwQ (htt ▸ hz'Q)
  have hcen := h.card_centralizer_Q hz'Q hz'Z
  obtain ⟨c, ⟨hcQ, hcz'⟩, hcD⟩ : ∃ c ∈ hsQ z ⊓ Subgroup.centralizer ({z'} : Set G),
      c ∉ hsFixQ z t := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show hsQ z ⊓ Subgroup.centralizer ({z'} : Set G) ≤
      hsFixQ z t from fun c hc => hne c hc)
    omega
  have hcz'c : c * z' = z' * c := Subgroup.mem_centralizer_singleton_iff.mp hcz'
  have hmc : m⁻¹ * c * m ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc m⁻¹ * c * m * z = m⁻¹ * (c * z') * m := by rw [hz']; group
      _ = m⁻¹ * (z' * c) * m := by rw [hcz'c]
      _ = z * (m⁻¹ * c * m) := by rw [hz']; group)
  set s₀ := m⁻¹ * c * m with hs₀
  have hs₀inv : ∀ u ∈ hsZQ z, s₀ * u * s₀⁻¹ = u⁻¹ := by
    rcases h.mem_K_or_inverts hmc with hK | hinv
    · exfalso
      apply hcD
      refine ⟨hcQ, ?_⟩
      have hct : c * t * c⁻¹ = t := by
        have h1 : s₀ * w * s₀⁻¹ = w := by
          rw [(Subgroup.mem_centralizer_iff.mp hK.2 w hwZ).symm, mul_inv_cancel_right]
        rw [ht]
        calc c * (m * w * m⁻¹) * c⁻¹ = m * (s₀ * w * s₀⁻¹) * m⁻¹ := by rw [hs₀]; group
          _ = m * w * m⁻¹ := by rw [h1]
      have hc' : t * c * t⁻¹ * c⁻¹ = 1 := by
        have : t * c = c * t := by
          calc t * c = c * t * c⁻¹ * c := by rw [hct]
            _ = c * t := by group
        rw [this]
        group
      rw [hc']
      exact (hsZQ z).one_mem
    · exact hinv
  have hcPnot : ∀ p ∈ hsP V, c * p ∉ hsZQ z := by
    intro p hp hcpZ
    apply hcD
    have hcP : c ∈ hsP V := by
      have := (hsP V).mul_mem (h.ZQ_le_P hcpZ) ((hsP V).inv_mem hp)
      simpa using this
    refine ⟨hcQ, ?_⟩
    rw [h.P_comm htP hcP, mul_inv_cancel_right, mul_inv_cancel]
    exact (hsZQ z).one_mem
  have hmM : m⁻¹ ∈ hsM V := (hsM V).inv_mem hm
  rcases sq_eq_of_isZ4Q8Q8 h.one.fstar (z := ⟨z, h.mem_Q⟩)
      (fun q => Subtype.ext (h.comm_z_of_mem_Q q.2).symm)
      (Subtype.ext (by simpa [sq] using h.sq_z))
      (fun h1 => h.z_ne_one (congrArg Subtype.val h1)) ⟨c, hcQ⟩ with hc2 | hc2
  · have hcc : c * c = 1 := congrArg Subtype.val hc2
    have hcZ : c ∉ hsZQ z := by
      have := hcPnot 1 (hsP V).one_mem
      rwa [mul_one] at this
    obtain ⟨g, hg⟩ := h.exists_conj_z_of_invol_Q hcQ hcc hcZ
    refine ⟨s₀, ⟨hmc, (hsM V).mul_mem ((hsM V).mul_mem hmM (h.Q_le_M hcQ)) hm⟩, ?_, hs₀inv,
      m⁻¹ * g, by rw [hs₀, ← hg]; group⟩
    rw [hs₀]
    calc m⁻¹ * c * m * (m⁻¹ * c * m) = m⁻¹ * (c * c) * m := by group
      _ = 1 := by rw [hcc, mul_one, inv_mul_cancel]
  · have hcc : c * c = z := congrArg Subtype.val hc2
    obtain ⟨v, hvV, hcv⟩ : ∃ v ∈ V, c * v ≠ v * c := by
      by_contra hne
      push Not at hne
      have hcP : c ∈ hsP V := by
        rw [← h.centralizer_V_eq]
        exact ⟨h.Q_le_M hcQ, Subgroup.mem_centralizer_iff.mpr fun v hv => (hne v hv).symm⟩
      apply hcD
      refine ⟨hcQ, ?_⟩
      rw [h.P_comm htP hcP, mul_inv_cancel_right, mul_inv_cancel]
      exact (hsZQ z).one_mem
    have hcv' : c * v = v * c * z := by
      rcases h.mul_comm_or_mul_z hcQ (h.two.le hvV) with hc | hc
      · exact absurd hc hcv
      · exact hc
    have hvt : v * t = t * v := h.P_comm (h.V_le_P hvV) htP
    have hvz' : v * z' = z' * v :=
      congrArg Subtype.val (h.elem.1.is_comm.comm ⟨v, hvV⟩ ⟨z', hz'V⟩)
    have hvv : v * v = 1 := by
      have := h.elem.2 v hvV
      rwa [sq] at this
    have hzc : c * z = z * c := h.comm_z_of_mem_Q hcQ
    have hzv : v * z = z * v := h.comm_z_of_mem_Q (h.two.le hvV)
    set s₁ := m⁻¹ * (c * v) * m with hs₁
    have hcvQ : c * v ∈ hsQ z := (hsQ z).mul_mem hcQ (h.two.le hvV)
    have hcvZ : c * v ∉ hsZQ z := hcPnot v (h.V_le_P hvV)
    have hs₁M : s₁ ∈ hsM V :=
      (hsM V).mul_mem ((hsM V).mul_mem hmM (h.Q_le_M hcvQ)) hm
    have hcvcv : c * v * (c * v) = 1 := by
      calc c * v * (c * v) = c * (v * c) * v := by group
        _ = c * (c * v * z⁻¹) * v := by
          rw [show v * c = c * v * z⁻¹ by rw [hcv']; group]
        _ = (c * c) * (v * v) * z⁻¹ := by
          rw [show c * (c * v * z⁻¹) * v = c * c * (v * z⁻¹ * v) by group,
            show v * z⁻¹ * v = v * v * z⁻¹ by
              rw [mul_assoc, show z⁻¹ * v = v * z⁻¹ by
                rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hzv, mul_assoc, mul_inv_cancel,
                  mul_one]]
              group]
          group
        _ = 1 := by rw [hcc, hvv, mul_one, mul_inv_cancel]
    obtain ⟨g, hg⟩ := h.exists_conj_z_of_invol_Q hcvQ hcvcv hcvZ
    refine ⟨s₁, ⟨?_, hs₁M⟩, ?_, ?_, m⁻¹ * g, by rw [hs₁, ← hg]; group⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc m⁻¹ * (c * v) * m * z = m⁻¹ * (c * (v * z')) * m := by rw [hz']; group
        _ = m⁻¹ * (c * (z' * v)) * m := by rw [hvz']
        _ = m⁻¹ * ((c * z') * v) * m := by group
        _ = m⁻¹ * ((z' * c) * v) * m := by rw [hcz'c]
        _ = z * (m⁻¹ * (c * v) * m) := by rw [hz']; group
    · rw [hs₁]
      calc m⁻¹ * (c * v) * m * (m⁻¹ * (c * v) * m) = m⁻¹ * (c * v * (c * v)) * m := by group
        _ = 1 := by rw [hcvcv, mul_one, inv_mul_cancel]
    · intro u hu
      have hvu : (m⁻¹ * v * m) * u = u * (m⁻¹ * v * m) := by
        have hmu : m * u * m⁻¹ ∈ hsP V :=
          (Subgroup.mem_normalizer_iff.mp hmQ u).mp (h.ZQ_le_P hu)
        have := h.P_comm (h.V_le_P hvV) hmu
        calc (m⁻¹ * v * m) * u = m⁻¹ * (v * (m * u * m⁻¹)) * m := by group
          _ = m⁻¹ * ((m * u * m⁻¹) * v) * m := by rw [this]
          _ = u * (m⁻¹ * v * m) := by group
      have h1 := hs₀inv u hu
      calc s₁ * u * s₁⁻¹ = s₀ * ((m⁻¹ * v * m) * u * (m⁻¹ * v * m)⁻¹) * s₀⁻¹ := by
            rw [hs₁, hs₀]; group
        _ = s₀ * u * s₀⁻¹ := by rw [hvu, mul_inv_cancel_right]
        _ = u⁻¹ := h1

theorem index_K [Finite G] (h : HSSetting z V) : ((hsK z).subgroupOf (hsH z)).index = 2 := by
  obtain ⟨s, ⟨hsmemH, -⟩, -, hsinv, -⟩ := h.exists_invol_inverts_ZQ
  obtain ⟨w, hwZ, -, -, hww⟩ := h.exists_mem_ZQ_ne
  have hnotinv : ∀ g ∈ hsK z, g * w * g⁻¹ ≠ w⁻¹ := by
    intro g hg h1
    rw [(Subgroup.mem_centralizer_iff.mp hg.2 w hwZ).symm, mul_inv_cancel_right] at h1
    have : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel w
    rw [hww] at this
    exact h.z_ne_one this
  have hsnotK : s ∉ hsK z := fun hs => hnotinv s hs (hsinv w hwZ)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s, hsmemH⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rcases h.mem_K_or_inverts b.2 with hb | hb
  · refine Or.inr ⟨hb, ?_⟩
    intro hbs
    apply hsnotK
    have := (hsK z).mul_mem ((hsK z).inv_mem hb) hbs
    simpa using this
  · refine Or.inl ⟨?_, fun hbK => hnotinv b hbK (hb w hwZ)⟩
    refine ⟨(hsH z).mul_mem b.2 hsmemH, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    simp only [Subgroup.coe_mul]
    have h1 := hsinv u hu
    have h2 := hb (s * u * s⁻¹) (by rw [h1]; exact (hsZQ z).inv_mem hu)
    rw [h1, inv_inv] at h2
    calc u * (b * s) = (b * u⁻¹ * (b : G)⁻¹) * (b * s) := by rw [h2]
      _ = b * (u⁻¹ * s) := by group
      _ = b * (s * (s⁻¹ * u⁻¹ * s)) := by group
      _ = b * (s * u) := by
        congr 2
        calc s⁻¹ * u⁻¹ * s = s⁻¹ * (s * u * s⁻¹) * s := by rw [h1]
          _ = u := by group
      _ = b * s * u := by group

end HSSetting

end CFSG.Quasithin.HSType
