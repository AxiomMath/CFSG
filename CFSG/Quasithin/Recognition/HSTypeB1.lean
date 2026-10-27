module

public import CFSG.Quasithin.Recognition.HSTypeL12h

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

@[expose] def hsB (z s : G) : Subgroup G :=
  (hsQ z ⊓ Subgroup.centralizer ({s} : Set G)) ⊔ Subgroup.zpowers s

theorem perm_five_transp_centralizer_sq : ∀ σ τ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign σ = -1 → σ * σ = 1 → τ * σ = σ * τ → τ * τ ≠ 1 →
      τ * τ * (τ * τ) * (τ * τ) = 1 := by
  decide +kernel

theorem perm_five_transp_centralizer_comm : ∀ σ τ : Equiv.Perm (Fin 5),
    Equiv.Perm.sign σ = -1 → σ * σ = 1 → τ * σ = σ * τ → τ * τ = 1 → τ ≠ 1 → τ ≠ σ →
      ∃ ρ : Equiv.Perm (Fin 5), ρ * σ = σ * ρ ∧ τ * ρ * τ⁻¹ * ρ⁻¹ ≠ 1 ∧
        τ * ρ * τ⁻¹ * ρ⁻¹ * (τ * ρ * τ⁻¹ * ρ⁻¹) * (τ * ρ * τ⁻¹ * ρ⁻¹) = 1 := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem mem_hsB_iff {s : G} (hss : s * s = 1) {x : G} :
    x ∈ hsB z s ↔ x ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ∨
      s * x ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hcs : ∀ c ∈ C, s * c = c * s := fun c hc =>
    (Subgroup.mem_centralizer_singleton_iff.mp hc.2).symm
  let S : Subgroup G :=
    { carrier := {x | x ∈ C ∨ s * x ∈ C}
      one_mem' := Or.inl C.one_mem
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (C.mul_mem hx hy)
        · right
          rw [← mul_assoc, hcs x hx, mul_assoc]
          exact C.mul_mem hx hy
        · right
          rw [← mul_assoc]
          exact C.mul_mem hx hy
        · left
          have e : x * y = (s * x) * (s * y) := by
            calc x * y = s * s * x * y := by rw [hss, one_mul]
              _ = s * (s * x) * y := by group
              _ = (s * x) * s * y := by rw [hcs _ hx]
              _ = (s * x) * (s * y) := by group
          rw [e]
          exact C.mul_mem hx hy
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (C.inv_mem hx)
        · right
          have e : s * x⁻¹ = (s * x)⁻¹ := by
            have h1 := hcs _ (C.inv_mem hx)
            calc s * x⁻¹ = s * (s * x)⁻¹ * s := by group
              _ = (s * x)⁻¹ * s * s := by rw [h1]
              _ = (s * x)⁻¹ := by rw [mul_assoc, hss, mul_one]
          show s * x⁻¹ ∈ C
          rw [e]
          exact C.inv_mem hx }
  have hBS : hsB z s = S := by
    refine le_antisymm (sup_le (fun x hx => Or.inl hx) ?_) ?_
    · rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [hss]; exact C.one_mem)
    · rintro x (hx | hx)
      · exact Subgroup.mem_sup_left hx
      · have e : x = s⁻¹ * (s * x) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((Subgroup.zpowers s).inv_mem
          (Subgroup.mem_zpowers s))) (Subgroup.mem_sup_left hx)
  rw [hBS]
  rfl

variable {s : G}

theorem s_mem_hsB : s ∈ hsB z s := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)

theorem centralizer_le_hsB : hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ≤ hsB z s :=
  le_sup_left

theorem z_mem_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) : z ∈ hsB z s :=
  centralizer_le_hsB ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩

theorem hsB_le_centralizer : hsB z s ≤ Subgroup.centralizer ({s} : Set G) :=
  sup_le inf_le_right (by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl)

theorem hsB_le_H [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) : hsB z s ≤ hsH z :=
  sup_le (inf_le_left.trans h.Q_le_H) (by rw [Subgroup.zpowers_le]; exact hsmemH)

theorem hsB_sq [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {x : G} (hx : x ∈ hsB z s) : x * x = 1 := by
  rcases (mem_hsB_iff hss).mp hx with hx | hx
  · exact h.mul_self_of_mem_centralizer_invol hsmemH hsnotK hss hx
  · have h1 := h.mul_self_of_mem_centralizer_invol hsmemH hsnotK hss hx
    have hsx : s * (s * x) = (s * x) * s := Subgroup.mem_centralizer_singleton_iff.mp hx.2 |>.symm
    calc x * x = (s * s) * x * x := by rw [hss, one_mul]
      _ = s * (s * x) * x := by group
      _ = (s * x) * s * x := by rw [hsx]
      _ = (s * x) * (s * x) := by group
      _ = 1 := h1

theorem hsB_comm [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) {x y : G} (hx : x ∈ hsB z s) (hy : y ∈ hsB z s) : x * y = y * x := by
  have hxy := h.hsB_sq hsmemH hsnotK hss ((hsB z s).mul_mem hx hy)
  have hxx := h.hsB_sq hsmemH hsnotK hss hx
  have hyy := h.hsB_sq hsmemH hsnotK hss hy
  have e1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  have e2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have e3 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  calc x * y = (x * y)⁻¹ := e1.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [e2, e3]

theorem hsB_inf_Q (hss : s * s = 1) (hsQ' : s ∉ hsQ z) :
    hsB z s ⊓ hsQ z = hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
  refine le_antisymm ?_ (le_inf centralizer_le_hsB inf_le_left)
  rintro x ⟨hx, hxQ⟩
  rcases (mem_hsB_iff hss).mp hx with hx | hx
  · exact hx
  · exfalso
    apply hsQ'
    have := (hsQ z).mul_mem hx.1 ((hsQ z).inv_mem hxQ)
    simpa using this

theorem card_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z) (hsnotK : s ∉ hsK z)
    (hss : s * s = 1) : Nat.card (hsB z s) = 16 := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  set C := hsQ z ⊓ Subgroup.centralizer ({s} : Set G) with hC
  have hCB : C ≤ hsB z s := centralizer_le_hsB
  have hidx : (C.subgroupOf (hsB z s)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, s_mem_hsB⟩, fun b => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    have hbs : (b : G) * s = s * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (hsB_le_centralizer b.2)
    rcases (mem_hsB_iff hss).mp b.2 with hb | hb
    · refine Or.inr ⟨hb, fun hbs' => hsQ' ?_⟩
      have := (hsQ z).mul_mem ((hsQ z).inv_mem hb.1) hbs'.1
      simpa using this
    · refine Or.inl ⟨by rw [hbs]; exact hb, fun hb' => hsQ' ?_⟩
      have := (hsQ z).mul_mem hb.1 ((hsQ z).inv_mem hb'.1)
      simpa using this
  have h1 := Subgroup.card_mul_index (C.subgroupOf (hsB z s))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv,
    h.card_centralizer_invol hsmemH hsnotK hss] at h1
  omega

theorem le_normalizer_of_conj_mem {X Y : Subgroup G} (hX : ∀ x ∈ X, ∀ b ∈ Y, x * b * x⁻¹ ∈ Y) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun b => ⟨hX x hx b, fun hb => ?_⟩
  have := hX x⁻¹ (X.inv_mem hx) _ hb
  simpa [mul_assoc] using this

theorem Q_le_normalizer_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) :
    hsQ z ≤ Subgroup.normalizer (hsB z s : Set G) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hzC : z ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨h.mem_Q, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hsmemH).symm⟩
  have hqc : ∀ q ∈ hsQ z, ∀ c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G),
      q * c * q⁻¹ ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro q hq c hc
    have e : q * c * q⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by group
    rw [e]
    refine Subgroup.mul_mem _ ?_ hc
    rcases h.comm_eq_one_or_z hq hc.1 with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact hzC
  refine le_normalizer_of_conj_mem fun q hq b hb => ?_
  rcases (mem_hsB_iff hss).mp hb with hb | hb
  · exact centralizer_le_hsB (hqc q hq b hb)
  ·
    have hqs : q * s * q⁻¹ * s⁻¹ ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
      have := (h.invol_comm_mem_centralizer hsmemH hsnotK hss hq).2
      have e : q * s * q⁻¹ * s⁻¹ = (s * q * s⁻¹ * q⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ this
    have e : q * b * q⁻¹ = (q * s * q⁻¹ * s⁻¹) * s * (q * (s * b) * q⁻¹) := by
      calc q * b * q⁻¹ = q * (s * s) * b * q⁻¹ := by rw [hss, mul_one]
        _ = (q * s * q⁻¹ * s⁻¹) * s * (q * (s * b) * q⁻¹) := by group
    rw [e]
    exact (hsB z s).mul_mem ((hsB z s).mul_mem (centralizer_le_hsB hqs) s_mem_hsB)
      (centralizer_le_hsB (hqc q hq _ hb))

theorem centralizer_le_normalizer_hsB [Finite G] (hss : s * s = 1) :
    hsH z ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (hsB z s : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx b hb => ?_
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hxC : ∀ c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G),
      x * c * x⁻¹ ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G) := by
    intro c hc
    refine ⟨conj_mem_Q hx.1 hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hcs : c * s = s * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    calc x * c * x⁻¹ * s = x * c * (x⁻¹ * s) := by group
      _ = x * c * (s * x⁻¹) := by
        rw [(Commute.inv_left (show Commute x s from hxs)).eq]
      _ = x * (c * s) * x⁻¹ := by group
      _ = x * (s * c) * x⁻¹ := by rw [hcs]
      _ = (x * s) * c * x⁻¹ := by group
      _ = s * (x * c * x⁻¹) := by rw [hxs]; group
  rcases (mem_hsB_iff hss).mp hb with hb | hb
  · exact centralizer_le_hsB (hxC b hb)
  · have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
    have e : x * b * x⁻¹ = s * (x * (s * b) * x⁻¹) := by
      calc x * b * x⁻¹ = x * (s * s) * b * x⁻¹ := by rw [hss, mul_one]
        _ = (x * s) * (s * b) * x⁻¹ := by group
        _ = s * (x * (s * b) * x⁻¹) := by rw [hxs]; group
    rw [e]
    exact (hsB z s).mul_mem s_mem_hsB (centralizer_le_hsB (hxC _ hb))

theorem exists_conj_of_mem_normalizer_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {x : G} (hxH : x ∈ hsH z)
    (hxN : x ∈ Subgroup.normalizer (hsB z s : Set G)) :
    ∃ r ∈ hsQ z, x * s * x⁻¹ = r * s * r⁻¹ := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hss
  have hxs : x * s * x⁻¹ ∈ hsB z s := (Subgroup.mem_normalizer_iff.mp hxN s).mp s_mem_hsB
  rcases (mem_hsB_iff hss).mp hxs with hc | hc
  · exfalso
    apply hsQ'
    have := conj_mem_Q ((hsH z).inv_mem hxH) hc.1
    simpa [mul_assoc] using this
  · obtain ⟨r, hr, hrs⟩ := h.exists_conj_eq_mul_of_invol hsmemH hsnotK hss hc
    refine ⟨r, hr, ?_⟩
    rw [← hrs]
    calc x * s * x⁻¹ = (s * s) * (x * s * x⁻¹) := by rw [hss, one_mul]
      _ = s * (s * (x * s * x⁻¹)) := by group

theorem conj_eq_conj_Q_of_invol [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) {g : G}
    (hq : g * s * g⁻¹ * s⁻¹ ∈ hsQ z) : ∃ r ∈ hsQ z, g * s * g⁻¹ = r * s * r⁻¹ := by
  obtain ⟨w, hwZ, hw1, hwz', -⟩ := h.exists_mem_ZQ_ne
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hwz
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hwz with h1 | h1
    · exact hw1 h1
    · exact hwz' h1
  obtain ⟨hnc, -⟩ := h.not_conj_mul_of_conj_z hsmemH hsnotK hss hwZ hwz hg₀
  have hmem : s⁻¹ * (g * s * g⁻¹) ∈ hsQ z := by
    have := conj_mem_Q ((hsH z).inv_mem hsmemH) hq
    have heq : s⁻¹ * (g * s * g⁻¹ * s⁻¹) * s⁻¹⁻¹ = s⁻¹ * (g * s * g⁻¹) := by group
    rwa [heq] at this
  have hinvol : s * (s⁻¹ * (g * s * g⁻¹)) * (s * (s⁻¹ * (g * s * g⁻¹))) = 1 := by
    calc s * (s⁻¹ * (g * s * g⁻¹)) * (s * (s⁻¹ * (g * s * g⁻¹))) = g * (s * s) * g⁻¹ := by
          group
      _ = 1 := by rw [hss, mul_one, mul_inv_cancel]
  have he : s * (s⁻¹ * (g * s * g⁻¹)) = g * s * g⁻¹ := by group
  obtain ⟨r, hr, hrs⟩ := h.exists_conj_of_invol_mul hsmemH hsnotK hss hwZ hwz hmem hinvol
  rw [he] at hrs
  rcases hrs with hrs | hrs
  · exact ⟨r, hr, hrs⟩
  · exfalso
    apply hnc (r⁻¹ * g * g₀)
    calc r⁻¹ * g * g₀ * z * (r⁻¹ * g * g₀)⁻¹ = r⁻¹ * (g * (g₀ * z * g₀⁻¹) * g⁻¹) * r := by
          group
      _ = s * w := by rw [hg₀, hrs]; group

theorem map_centralizer_invol [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hφ : Function.Surjective φ)
    (hker : φ.ker = (hsQ z).subgroupOf (hsH z)) {π : Equiv.Perm (Fin 5)}
    (hπ : π * φ ⟨s, hsmemH⟩ = φ ⟨s, hsmemH⟩ * π) :
    ∃ x : ↥(hsH z), (x : G) * s = s * x ∧ φ x = π := by
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  obtain ⟨g, rfl⟩ := hφ π
  set s' : ↥(hsH z) := ⟨s, hsmemH⟩
  have h1 : φ (g * s' * g⁻¹ * s'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπ]
    group
  have h2 := (hkerQ _).mp h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  obtain ⟨r, hr, hgr⟩ := h.conj_eq_conj_Q_of_invol hsmemH hsnotK hss hg₀ h2
  refine ⟨⟨r, h.Q_le_H hr⟩⁻¹ * g, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc r⁻¹ * g * s = r⁻¹ * (g * s * (g : G)⁻¹) * g := by group
      _ = r⁻¹ * (r * s * r⁻¹) * g := by rw [hgr]
      _ = s * (r⁻¹ * g) := by group
  · rw [map_mul, map_inv, (hkerQ ⟨r, h.Q_le_H hr⟩).mpr hr, inv_one, one_mul]

theorem exists_pow_orderOf_three [Finite G] (h : HSSetting z V)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    {y : ↥(hsH z)} (hy3 : φ y * φ y * φ y = 1) (hy1 : φ y ≠ 1) :
    orderOf ((y : G) ^ 64) = 3 := by
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hτ64 : φ y ^ 64 = φ y := by
    have : φ y ^ 3 = 1 := by rw [pow_succ, pow_succ, pow_one]; exact hy3
    calc φ y ^ 64 = (φ y ^ 3) ^ 21 * φ y := by rw [← pow_mul, ← pow_succ]
      _ = φ y := by rw [this, one_pow, one_mul]
  have h3Q : (y : G) ^ 3 ∈ hsQ z := by
    have : φ (y ^ 3) = 1 := by rw [map_pow, pow_succ, pow_succ, pow_one]; exact hy3
    have := (hkerQ (y ^ 3)).mp this
    simpa using this
  have hy3' : ((y : G) ^ 64) ^ 3 = 1 := by
    have h64 := pow_card_eq_one' (G := ↥(hsQ z)) (x := ⟨_, h3Q⟩)
    rw [h.card_Q] at h64
    have := congrArg Subtype.val h64
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← pow_mul, show 64 * 3 = 3 * 64 by norm_num, pow_mul]
    exact this
  have hy1' : (y : G) ^ 64 ≠ 1 := by
    intro h1
    apply hy1
    rw [← hτ64, ← map_pow]
    have : y ^ 64 = 1 := Subtype.ext (by simpa using h1)
    rw [this, map_one]
  exact orderOf_eq_prime hy3' hy1'

theorem mem_hsB_of_map (hsmemH : s ∈ hsH z) (hss : s * s = 1)
    {φ : ↥(hsH z) →* Equiv.Perm (Fin 5)} (hker : φ.ker = (hsQ z).subgroupOf (hsH z))
    {x : ↥(hsH z)} (hxs : (x : G) * s = s * x) (hx : φ x = 1 ∨ φ x = φ ⟨s, hsmemH⟩) :
    (x : G) ∈ hsB z s := by
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := by
    intro g
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rcases hx with hx | hx
  · exact centralizer_le_hsB ⟨(hkerQ x).mp hx, Subgroup.mem_centralizer_singleton_iff.mpr hxs⟩
  · refine (mem_hsB_iff hss).mpr (Or.inr ⟨?_, ?_⟩)
    · have h1 : φ (⟨s, hsmemH⟩ * x) = 1 := by
        rw [map_mul, hx, ← map_mul]
        have : (⟨s, hsmemH⟩ : ↥(hsH z)) * ⟨s, hsmemH⟩ = 1 := Subtype.ext hss
        rw [this, map_one]
      exact (hkerQ _).mp h1
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc s * x * s = s * (x * s) := by group
        _ = s * (s * x) := by rw [hxs]

theorem le_hsB_of_normalized [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s)
    {Y : Subgroup G} (hYC : Y ≤ hsH z ⊓ Subgroup.centralizer ({s} : Set G))
    (hYN : hsH z ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hY3 : ∀ y ∈ Y, ∀ hy : y ∈ hsH z, ∀ φ : ↥(hsH z) →* Equiv.Perm (Fin 5),
      φ.ker = (hsQ z).subgroupOf (hsH z) → φ ⟨y, hy⟩ * φ ⟨y, hy⟩ * φ ⟨y, hy⟩ = 1 →
        φ ⟨y, hy⟩ = 1) :
    Y ≤ hsB z s := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hsign := h.sign_eq_neg_one_of_not_mem_K hker (a := ⟨s, hsmemH⟩) hsnotK
  have hs2 : φ ⟨s, hsmemH⟩ * φ ⟨s, hsmemH⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s, hsmemH⟩ : ↥(hsH z)) * ⟨s, hsmemH⟩ = 1 := Subtype.ext hss
    rw [this, map_one]
  intro x hx
  have hxH : x ∈ hsH z := (hYC hx).1
  have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp (hYC hx).2
  set x' : ↥(hsH z) := ⟨x, hxH⟩
  have hτ : φ x' * φ ⟨s, hsmemH⟩ = φ ⟨s, hsmemH⟩ * φ x' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxs
  by_contra hxB
  have hne : φ x' ≠ 1 ∧ φ x' ≠ φ ⟨s, hsmemH⟩ := by
    constructor
    · intro h1
      exact hxB (mem_hsB_of_map hsmemH hss hker hxs (Or.inl h1))
    · intro h1
      exact hxB (mem_hsB_of_map hsmemH hss hker hxs (Or.inr h1))
  by_cases hsq : φ x' * φ x' = 1
  ·
    obtain ⟨ρ, hρ, hρ1, hρ3⟩ := perm_five_transp_centralizer_comm _ _ hsign hs2 hτ hsq
      hne.1 hne.2
    obtain ⟨g, hgs, hgρ⟩ := h.map_centralizer_invol hsmemH hsnotK hss hg₀ hφ hker hρ
    have hgC : (g : G) ∈ hsH z ⊓ Subgroup.centralizer ({s} : Set G) :=
      ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr hgs⟩
    have hc : x * g * x⁻¹ * (g : G)⁻¹ ∈ Y := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hYN hgC) x⁻¹).mp (Y.inv_mem hx)
      have e : x * g * x⁻¹ * (g : G)⁻¹ = x * ((g : G) * x⁻¹ * (g : G)⁻¹) := by group
      rw [e]
      exact Y.mul_mem hx h1
    have hcH : x * g * x⁻¹ * (g : G)⁻¹ ∈ hsH z := (hYC hc).1
    have hφc : φ ⟨x * g * x⁻¹ * (g : G)⁻¹, hcH⟩ = φ x' * ρ * (φ x')⁻¹ * ρ⁻¹ := by
      have : (⟨x * g * x⁻¹ * (g : G)⁻¹, hcH⟩ : ↥(hsH z)) = x' * g * x'⁻¹ * g⁻¹ :=
        Subtype.ext (by simp [x'])
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hgρ]
    have := hY3 _ hc hcH φ hker (by rw [hφc]; exact hρ3)
    rw [hφc] at this
    exact hρ1 this
  ·
    have h6 := perm_five_transp_centralizer_sq _ _ hsign hs2 hτ hsq
    have hxx : x * x ∈ Y := Y.mul_mem hx hx
    have hxxH : x * x ∈ hsH z := (hsH z).mul_mem hxH hxH
    have hφxx : φ ⟨x * x, hxxH⟩ = φ x' * φ x' := by
      rw [← map_mul]
      rfl
    have := hY3 _ hxx hxxH φ hker (by rw [hφxx]; exact h6)
    rw [hφxx] at this
    exact hsq this

theorem centralizer_hsB [Finite G] (h : HSSetting z V) (hsmemH : s ∈ hsH z)
    (hsnotK : s ∉ hsK z) (hss : s * s = 1) {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = s) :
    Subgroup.centralizer (hsB z s : Set G) = hsB z s := by
  have hsQ' : s ∉ hsQ z := fun hsQ => hsnotK (h.Q_le_K hsQ)
  obtain ⟨c, hcC, hcZ⟩ : ∃ c ∈ hsQ z ⊓ Subgroup.centralizer ({s} : Set G), c ∉ hsZQ z := by
    by_contra hne
    push Not at hne
    have hle : hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ≤
        hsQ z ⊓ Subgroup.centralizer ({s} : Set G) ⊓ hsZQ z := fun c hc => ⟨hc, hne c hc⟩
    rw [h.centralizer_invol_inf_ZQ hsmemH hsnotK] at hle
    have := Subgroup.card_le_of_le hle
    rw [h.card_centralizer_invol hsmemH hsnotK hss, Nat.card_zpowers, h.orderOf_z] at this
    omega
  have hzB := h.z_mem_hsB hsmemH
  have hCH : Subgroup.centralizer (hsB z s : Set G) ≤ hsH z ⊓ Subgroup.centralizer ({s} : Set G) :=
    fun x hx => ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx z hzB).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx s s_mem_hsB).symm⟩
  refine le_antisymm ?_ fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    h.hsB_comm hsmemH hsnotK hss hy hx
  refine h.le_hsB_of_normalized hsmemH hsnotK hss hg₀ hCH ?_ ?_
  · intro g hg
    have hgN := centralizer_le_normalizer_hsB hss hg
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      have hb' : g⁻¹ * b * g ∈ hsB z s := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) b).mp hb
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hx _ hb'
      calc b * (g * x * g⁻¹) = g * ((g⁻¹ * b * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * b * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * b := by group
    · refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      have hb' : g * b * g⁻¹ ∈ hsB z s := (Subgroup.mem_normalizer_iff.mp hgN b).mp hb
      have h1 := Subgroup.mem_centralizer_iff.mp hx _ hb'
      calc b * x = g⁻¹ * ((g * b * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * b * g⁻¹)) * g := by rw [h1]
        _ = x * b := by group
  · intro y hy hyH φ hker hy3
    by_contra hy1
    have ho := h.exists_pow_orderOf_three hker hy3 hy1
    apply hcZ
    refine h.mem_ZQ_of_mem_stabQ_three hcC.1 ho ⟨(hsH z).pow_mem hyH 64, ?_⟩
    have hyc : (y : G) ^ 64 * c = c * (y : G) ^ 64 := by
      have h1 : y * c = c * y :=
        (Subgroup.mem_centralizer_iff.mp hy c (centralizer_le_hsB hcC)).symm
      exact (Commute.pow_left h1 64)
    rw [hyc, mul_inv_cancel_right, mul_inv_cancel]
    exact (hsZQ z).one_mem

end HSSetting

end CFSG.Quasithin.HSType
