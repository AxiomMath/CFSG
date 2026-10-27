module

public import CFSG.Quasithin.Recognition.HSTypeB1
public import CFSG.Quasithin.Recognition.HSTypeSym

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

namespace HSSetting

variable {z : G} {V : Subgroup G} {s : G}

theorem setting_s (h : HSSetting z V) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    HSSetting s (V.map (MulAut.conj g₀).toMonoidHom) :=
  hg₀ ▸ h.conj g₀

theorem z_mem_hsQ_s_iff [Finite G] (h : HSSetting z V) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    z ∈ hsQ s ↔ s ∈ hsQ z := by
  have := h.mem_hsQ_conj_iff g₀ 1
  simp only [one_mul, inv_one, mul_one] at this
  rw [hg₀] at this
  exact this

theorem z_not_mem_hsQ_s [Finite G] (h : HSSetting z V) (hsQ' : s ∉ hsQ z) {g₀ : G}
    (hg₀ : g₀ * z * g₀⁻¹ = s) : z ∉ hsQ s :=
  fun hz => hsQ' ((h.z_mem_hsQ_s_iff hg₀).mp hz)

theorem z_mem_hsH_s (hsmemH : s ∈ hsH z) : z ∈ hsH s :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm

theorem z_not_mem_hsK_s [Finite G] (h : HSSetting z V) (hsQ' : s ∉ hsQ z) {g₀ : G}
    (hg₀ : g₀ * z * g₀⁻¹ = s) : z ∉ hsK s := by
  intro hz
  have hs' := h.setting_s hg₀
  have e : g₀⁻¹ * s * g₀⁻¹⁻¹ = z := by rw [← hg₀]; group
  have := hs'.mem_Q_of_conj_mem_K (g := g₀⁻¹) (by rw [e]; exact hz)
  rw [e] at this
  exact h.z_not_mem_hsQ_s hsQ' hg₀ this

theorem hsB_symm [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) : hsB s z = hsB z s := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzH := z_mem_hsH_s hsmemH
  have hzK := h.z_not_mem_hsK_s hsQ' hg₀
  have hzz : z * z = 1 := h.z_mul_z
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · refine h.le_hsB_of_normalized hsmemH hsnotK hss hg₀ ?_ ?_ ?_
    · intro x hx
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hsB_le_centralizer hx)),
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hs'.hsB_le_H hzH hx))⟩
    · intro x hx
      exact centralizer_le_normalizer_hsB hzz ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hx.2),
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hx.1)⟩
    · intro y hy hyH φ _ hy3
      have hyy : y * y = 1 := hs'.hsB_sq hzH hzK hzz hy
      have h2 : φ ⟨y, hyH⟩ * φ ⟨y, hyH⟩ = 1 := by
        rw [← map_mul]
        have : (⟨y, hyH⟩ : ↥(hsH z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
        rw [this, map_one]
      rw [h2, one_mul] at hy3
      exact hy3
  · rw [h.card_hsB hsmemH hsnotK hss, hs'.card_hsB hzH hzK hzz]

theorem exists_conj_of_mem_C [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {c c' : G}
    (hc : c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) (hcz : c ∉ Subgroup.zpowers z)
    (hc' : c' ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) (hc'z : c' ∉ Subgroup.zpowers z) :
    ∃ n ∈ hsH z ⊓ Subgroup.normalizer (hsB z s : Set G), n * c * n⁻¹ = c' := by
  classical
  have := Fintype.ofFinite G
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hC
  set N₁ := hsH z ⊓ Subgroup.normalizer (hsB z s : Set G) with hN₁
  have hQN : hsQ z ≤ N₁ := le_inf h.Q_le_H (h.Q_le_normalizer_hsB hsmemH hsnotK hss)
  have hCN : hsH z ⊓ Subgroup.centralizer ({s} : Set G) ≤ N₁ :=
    le_inf inf_le_left (centralizer_le_normalizer_hsB hss)
  have hCZ := h.centralizer_invol_inf_ZQ hsmemH hsnotK
  have hcard := (h.card_centralizer_H_invol_not_K hsmemH hsnotK hss
    (w := (h.exists_mem_ZQ_ne).choose) (h.exists_mem_ZQ_ne).choose_spec.1 (by
      obtain ⟨hw, hw1, hwz, -⟩ := (h.exists_mem_ZQ_ne).choose_spec
      intro hwz'
      rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz' with h1 | h1
      · exact hw1 h1
      · exact hwz h1) hg₀).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite ↥(hsH z ⊓ Subgroup.centralizer ({s} : Set G))
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card
    (G := ↥(hsH z ⊓ Subgroup.centralizer ({s} : Set G))) 3
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  set y : G := (y₀ : G) with hy
  have hyo : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe]; exact hy₀
  have hyH : y ∈ hsH z := y₀.2.1
  have hyC : y ∈ hsH z ⊓ Subgroup.centralizer ({s} : Set G) := y₀.2
  have hyN : y ∈ N₁ := hCN hyC
  have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have hmemCZ : ∀ x ∈ C, x ∉ Subgroup.zpowers z → x ∉ hsZQ z := by
    intro x hx hxz hxZ
    apply hxz
    rw [← hCZ]
    exact ⟨hx, hxZ⟩
  have hyCC : ∀ x ∈ C, y * x * y⁻¹ ∈ C := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp (centralizer_le_normalizer_hsB hss hyC) x).mp
      (centralizer_le_hsB hx)
    refine ⟨conj_mem_Q hyH hx.1, ?_⟩
    have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.mp hyC.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * x * y⁻¹ * s = y * x * (y⁻¹ * s) := by group
      _ = y * x * (s * y⁻¹) := by rw [(Commute.inv_left (show Commute y s from hys)).eq]
      _ = y * (x * s) * y⁻¹ := by group
      _ = y * (s * x) * y⁻¹ := by rw [hxs]
      _ = (y * s) * x * y⁻¹ := by group
      _ = s * (y * x * y⁻¹) := by rw [hys]; group
  have hzpow : ∀ x : G, x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
    intro x
    constructor
    · intro hx
      exact eq_one_or_eq_of_mem_zpowers h.orderOf_z hx
    · rintro (h1 | h1) <;> rw [h1]
      · exact (Subgroup.zpowers z).one_mem
      · exact Subgroup.mem_zpowers z
  set T : Finset G := Finset.univ.filter (fun x => x ∈ C ∧ x ∉ Subgroup.zpowers z) with hT
  set S : Finset G := Finset.univ.filter (fun x => x ∈ C ∧ x ∉ Subgroup.zpowers z ∧
    ∃ n ∈ N₁, n * c * n⁻¹ = x) with hS
  have hST : S ⊆ T := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  have hTcard : T.card = 6 := by
    have h1 : (Finset.univ.filter fun x : G => x ∈ C).card = 8 := by
      rw [← h.card_centralizer_invol hsmemH hsnotK hss, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    have h2 : (Finset.univ.filter fun x : G => x ∈ Subgroup.zpowers z).card = 2 := by
      rw [← h.orderOf_z, ← Nat.card_zpowers, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h3 : T = (Finset.univ.filter fun x : G => x ∈ C) \
        (Finset.univ.filter fun x : G => x ∈ Subgroup.zpowers z) := by
      ext x
      simp [hT]
    have h4 : (Finset.univ.filter fun x : G => x ∈ Subgroup.zpowers z) ⊆
        (Finset.univ.filter fun x : G => x ∈ C) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      rcases (hzpow x).mp hx.2 with h1 | h1 <;> rw [h1]
      · exact C.one_mem
      · exact ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
    rw [h3, Finset.card_sdiff_of_subset h4, h1, h2]
  have h3 : 3 ∣ S.card := by
    refine prime_dvd_card_of_free S (fun w => y * w * y⁻¹) Nat.prime_three
      (fun w _ => by rw [iterate_conj, hy3]; group) (fun w hw => ?_) (fun w hw hfix => ?_)
    · rw [Finset.mem_filter] at hw ⊢
      obtain ⟨-, hwC, hwz, n, hn, hnw⟩ := hw
      refine ⟨Finset.mem_univ _, hyCC w hwC, fun hz' => hwz ?_, y * n, N₁.mul_mem hyN hn, ?_⟩
      · rcases (hzpow _).mp hz' with h1 | h1
        · rw [hzpow]
          left
          calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
            _ = 1 := by rw [h1]; group
        · rw [hzpow]
          right
          calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
            _ = y⁻¹ * z * y := by rw [h1]
            _ = z := by rw [mul_assoc, ← hyz]; group
      · rw [← hnw]
        group
    · rw [Finset.mem_filter] at hw
      obtain ⟨-, hwC, hwz, -⟩ := hw
      apply hmemCZ w hwC hwz
      refine h.mem_ZQ_of_mem_stabQ_three hwC.1 hyo ⟨hyH, ?_⟩
      have : y * w * y⁻¹ = w := hfix
      rw [this, mul_inv_cancel]
      exact (hsZQ z).one_mem
  have h2 : 2 ∣ S.card := by
    refine prime_dvd_card_of_free S (fun w => w * z) Nat.prime_two
      (fun w _ => by simp [mul_assoc, h.z_mul_z]) (fun w hw => ?_) (fun w hw hfix => ?_)
    · rw [Finset.mem_filter] at hw ⊢
      obtain ⟨-, hwC, hwz, n, hn, hnw⟩ := hw
      have hzC : z ∈ C := ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
      refine ⟨Finset.mem_univ _, C.mul_mem hwC hzC, fun hz' => hwz ?_, ?_⟩
      · rcases (hzpow _).mp hz' with h1 | h1
        · rw [hzpow]
          right
          calc w = w * z * z := by rw [mul_assoc, h.z_mul_z, mul_one]
            _ = z := by rw [h1, one_mul]
        · rw [hzpow]
          left
          calc w = w * z * z := by rw [mul_assoc, h.z_mul_z, mul_one]
            _ = 1 := by rw [h1, h.z_mul_z]
      ·
        have hwZ := hmemCZ w hwC hwz
        obtain ⟨q, hq, hqw⟩ : ∃ q ∈ hsQ z, q * w ≠ w * q := by
          by_contra hne
          push Not at hne
          exact hwZ ⟨hwC.1, Subgroup.mem_centralizer_iff.mpr fun q hq => hne q hq⟩
        have hcomm : q * w * q⁻¹ * w⁻¹ = z := by
          rcases h.comm_eq_one_or_z hq hwC.1 with h1 | h1
          · exfalso
            apply hqw
            calc q * w = q * w * q⁻¹ * w⁻¹ * (w * q) := by group
              _ = w * q := by rw [h1, one_mul]
          · exact h1
        refine ⟨q * n, N₁.mul_mem (hQN hq) hn, ?_⟩
        calc q * n * c * (q * n)⁻¹ = q * (n * c * n⁻¹) * q⁻¹ := by group
          _ = q * w * q⁻¹ := by rw [hnw]
          _ = (q * w * q⁻¹ * w⁻¹) * w := by group
          _ = w * z := by rw [hcomm, h.comm_z_of_mem_Q hwC.1]
    · exact h.z_ne_one (by simpa using hfix)
  have hcS : c ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hc, hcz, 1, N₁.one_mem, by group⟩
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨c, hcS⟩
  have hS6 : 6 ≤ S.card := by
    have : 6 ∣ S.card := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    exact Nat.le_of_dvd hSpos this
  have hST' : S = T := Finset.eq_of_subset_of_card_le hST (by rw [hTcard]; exact hS6)
  have hc'T : c' ∈ T := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hc', hc'z⟩
  rw [← hST', Finset.mem_filter] at hc'T
  exact hc'T.2.2.2

theorem exists_conj_z_of_not_mem_hsQ_s [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : G}
    (hx : x ∈ hsB z s) (hxQ : x ∉ hsQ s) :
    ∃ n ∈ Subgroup.normalizer (hsB z s : Set G), n * z * n⁻¹ = x := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzH := z_mem_hsH_s hsmemH
  have hzK := h.z_not_mem_hsK_s hsQ' hg₀
  have hzz : z * z = 1 := h.z_mul_z
  have hB := h.hsB_symm hsmemH hsnotK hss hg₀
  rw [← hB] at hx ⊢
  rcases (mem_hsB_iff hzz).mp hx with hx' | hx'
  · exact absurd hx'.1 hxQ
  · obtain ⟨r, hr, hrz⟩ := hs'.exists_conj_eq_mul_of_invol hzH hzK hzz hx'
    refine ⟨r, hs'.Q_le_normalizer_hsB hzH hzK hzz hr, ?_⟩
    rw [← hrz, ← mul_assoc, hzz, one_mul]

theorem exists_normalizer_conj_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {x : G}
    (hx : x ∈ hsB z s) (hx1 : x ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (hsB z s : Set G), n * z * n⁻¹ = x := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hs' := h.setting_s hg₀
  have hzH := z_mem_hsH_s hsmemH
  have hzK := h.z_not_mem_hsK_s hsQ' hg₀
  have hzz : z * z = 1 := h.z_mul_z
  have hzQs := h.z_not_mem_hsQ_s hsQ' hg₀
  have hB := h.hsB_symm hsmemH hsnotK hss hg₀
  have hsQs : s ∈ hsQ s := hs'.mem_Q
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  set N := Subgroup.normalizer (hsB z s : Set G)
  have hQN := h.Q_le_normalizer_hsB hsmemH hsnotK hss
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hzC : z ∈ C := ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
  have hsz : s * z ∈ hsB z s := (hsB z s).mul_mem s_mem_hsB (centralizer_le_hsB hzC)
  have hszQs : s * z ∉ hsQ s := by
    intro h1
    apply hzQs
    have := (hsQ s).mul_mem ((hsQ s).inv_mem hsQs) h1
    simpa using this
  obtain ⟨n₁, hn₁, hn₁z⟩ := h.exists_conj_z_of_not_mem_hsQ_s hsmemH hsnotK hss hg₀ hsz hszQs
  have hBQ : ∀ y ∈ hsB z s, y ∉ hsQ z → ∃ n ∈ N, n * z * n⁻¹ = y := by
    intro y hy hyQ
    rcases (mem_hsB_iff hss).mp hy with hy' | hy'
    · exact absurd hy'.1 hyQ
    · obtain ⟨r, hr, hry⟩ := h.exists_conj_eq_mul_of_invol hsmemH hsnotK hss hy'
      obtain ⟨r', hr', hr'z⟩ := h.exists_conj_eq_mul_of_invol hsmemH hsnotK hss hzC
      refine ⟨r * r'⁻¹ * n₁, N.mul_mem (N.mul_mem (hQN hr) (N.inv_mem (hQN hr'))) hn₁, ?_⟩
      have e1 : y = r * s * r⁻¹ := by
        calc y = (s * s) * y := by rw [hss, one_mul]
          _ = s * (s * y) := by group
          _ = r * s * r⁻¹ := hry
      calc r * r'⁻¹ * n₁ * z * (r * r'⁻¹ * n₁)⁻¹ = r * r'⁻¹ * (n₁ * z * n₁⁻¹) * r' * r⁻¹ := by
            group
        _ = r * r'⁻¹ * (r' * s * r'⁻¹) * r' * r⁻¹ := by rw [hn₁z, hr'z]
        _ = y := by rw [e1]; group
  set C' := hsQ s ⊓ Subgroup.centralizer ({z} : Set G) with hC'
  have hC'B : C' ≤ hsB z s := hB ▸ centralizer_le_hsB
  have hCB : C ≤ hsB z s := centralizer_le_hsB
  obtain ⟨c, ⟨hcC, hcC'⟩, hc1⟩ : ∃ c ∈ C ⊓ C', c ≠ 1 := by
    have hle : C ≤ Subgroup.normalizer (C' : Set G) :=
      le_normalizer_of_conj_mem fun a ha b hb => by
        rw [h.hsB_comm hsmemH hsnotK hss (hCB ha) (hC'B hb), mul_inv_cancel_right]
        exact hb
    have hprod := card_sup_mul_card_inf_of_le_normalizer hle
    rw [h.card_centralizer_invol hsmemH hsnotK hss, hs'.card_centralizer_invol hzH hzK hzz] at hprod
    have hsup : Nat.card ↥(C ⊔ C') ≤ 16 := by
      rw [← h.card_hsB hsmemH hsnotK hss]
      exact Subgroup.card_le_of_le (sup_le hCB hC'B)
    have hinf : 1 < Nat.card ↥(C ⊓ C') := by nlinarith
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      ((Subgroup.one_lt_card_iff_ne_bot _).mp hinf)
    exact ⟨a, a.2, fun h1 => ha (Subtype.ext h1)⟩
  have hcz1 : c * z ∉ Subgroup.zpowers z := by
    intro h1
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z h1 with h2 | h2
    · apply hzQs
      have : c = z := by
        calc c = c * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = z := by rw [h2, one_mul]
      rw [← this]
      exact hcC'.1
    · apply hc1
      calc c = c * z * z⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel]
  have hczQs : c * z ∉ hsQ s := fun h1 => hzQs (by
    have := (hsQ s).mul_mem ((hsQ s).inv_mem hcC'.1) h1
    simpa using this)
  have hczC : c * z ∈ C := C.mul_mem hcC hzC
  obtain ⟨n₂, hn₂, hn₂z⟩ := h.exists_conj_z_of_not_mem_hsQ_s hsmemH hsnotK hss hg₀
    (hCB hczC) hczQs
  by_cases hxQ : x ∈ hsQ z
  · have hxC : x ∈ C := (hsB_inf_Q hss hsQ').le ⟨hx, hxQ⟩
    by_cases hxz : x ∈ Subgroup.zpowers z
    · rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hxz with h1 | h1
      · exact absurd h1 hx1
      · exact ⟨1, N.one_mem, by rw [h1]; group⟩
    · obtain ⟨n, ⟨-, hn⟩, hnx⟩ :=
        h.exists_conj_of_mem_C hsmemH hsnotK hss hg₀ hczC hcz1 hxC hxz
      refine ⟨n * n₂, N.mul_mem hn hn₂, ?_⟩
      calc n * n₂ * z * (n * n₂)⁻¹ = n * (n₂ * z * n₂⁻¹) * n⁻¹ := by group
        _ = x := by rw [hn₂z, hnx]
  · exact hBQ x hx hxQ

end HSSetting

end CFSG.Quasithin.HSType
