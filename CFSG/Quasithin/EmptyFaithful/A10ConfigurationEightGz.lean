module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationEightG22
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationEightSylow
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationDelta

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem t_mem_Lam : E.t ∈ E.Lam := ⟨1, one_mem _, by simp⟩

theorem Lam_conj {y h : G} (hy : y ∈ E.Lam) (hh : h ∈ E.Gz) : h⁻¹ * y * h ∈ E.Lam := by
  obtain ⟨g, hg, rfl⟩ := hy
  exact ⟨g * h, E.Gz.mul_mem hg hh, by group⟩

theorem Lam_sq {y : G} (hy : y ∈ E.Lam) : y * y = 1 := by
  obtain ⟨g, -, rfl⟩ := hy
  calc g⁻¹ * E.t * g * (g⁻¹ * E.t * g) = g⁻¹ * (E.t * E.t) * g := by group
    _ = 1 := by rw [E.t_sq]; group

theorem Lam_ne_one {y : G} (hy : y ∈ E.Lam) : y ≠ 1 := by
  obtain ⟨g, -, rfl⟩ := hy
  intro h
  apply E.t_ne_one
  calc E.t = g * (g⁻¹ * E.t * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem s_inv_mul_t_mul_s : E.s⁻¹ * E.t * E.s = E.t * E.z := by
  have := congrArg E.ι s0_conj_t0
  show (E.ι s0)⁻¹ * E.ι t0 * E.ι s0 = E.ι t0 * E.ι z0
  simpa [map_mul, map_inv] using this

theorem Lam_mul_z {y : G} (hy : y ∈ E.Lam) : y * E.z ∈ E.Lam := by
  obtain ⟨g, hg, rfl⟩ := hy
  have hgz : g * E.z = E.z * g := (E.mem_Gz.1 hg).symm
  refine ⟨E.s * g, E.Gz.mul_mem (E.T_le_Gz E.s_mem_T) hg, ?_⟩
  calc (E.s * g)⁻¹ * E.t * (E.s * g) = g⁻¹ * (E.s⁻¹ * E.t * E.s) * g := by group
    _ = g⁻¹ * (E.t * E.z) * g := by rw [E.s_inv_mul_t_mul_s]
    _ = g⁻¹ * E.t * (E.z * g) := by group
    _ = g⁻¹ * E.t * (g * E.z) := by rw [hgz]
    _ = g⁻¹ * E.t * g * E.z := by group

theorem mem_Δ₁_iff {w : Wc} : E.ι w ∈ E.Δ₁ ↔ D1 w = true := by
  rw [E.Δ₁_eq_image]
  constructor
  · rintro ⟨w', hw', h⟩
    have := E.injective h
    subst this
    exact hw'
  · intro h
    exact ⟨w, h, rfl⟩

theorem mem_Δ₄_iff {w : Wc} : E.ι w ∈ E.Δ₄ ↔ D4 w = true := by
  rw [E.Δ₄_eq_image]
  constructor
  · rintro ⟨w', hw', h⟩
    have := E.injective h
    subst this
    exact hw'
  · intro h
    exact ⟨w, h, rfl⟩

theorem Lam_not_mem_Δ₁ [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {y : G} (hy : y ∈ E.Lam) : y ∉ E.Δ₁ := by
  rintro ⟨m, hm, hmy⟩
  obtain ⟨g, hg, rfl⟩ := hy
  apply E.t_not_conj_z hT hM
  refine ⟨m * g⁻¹, ?_⟩
  have h2 : m⁻¹ * E.z * m = g⁻¹ * E.t * g := hmy
  calc (m * g⁻¹)⁻¹ * E.z * (m * g⁻¹) = g * (m⁻¹ * E.z * m) * g⁻¹ := by group
    _ = g * (g⁻¹ * E.t * g) * g⁻¹ := by rw [h2]
    _ = E.t := by group

theorem Lam_le_U {y : G} (hy : y ∈ E.Lam) : y ∈ conjClosure E.V₂ E.Gz := by
  obtain ⟨g, hg, rfl⟩ := hy
  have h := mem_conjClosure (E.Gz.inv_mem hg) E.t_mem_V₂
  rwa [inv_inv] at h

theorem Lam_mem_T [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    {y : G} (hy : y ∈ E.Lam) : y ∈ T :=
  (E.U_facts hEven hT).2.1 (E.Lam_le_U hy)

theorem Lam_comm [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    {y y' : G} (hy : y ∈ E.Lam) (hy' : y' ∈ E.Lam) : y * y' * y⁻¹ * y'⁻¹ ∈ E.V₁ := by
  obtain ⟨hUQ, -, hcomm⟩ := E.U_facts hEven hT
  exact hcomm y (E.Lam_le_U hy) y' (hUQ (E.Lam_le_U hy'))

@[expose] def Rz : Subgroup G where
  carrier := {g | g ∈ E.Gz ∧ ∀ y ∈ E.Lam, g * y * g⁻¹ * y⁻¹ ∈ E.V₁}
  one_mem' := ⟨one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgL⟩ ⟨hh, hhL⟩
    refine ⟨E.Gz.mul_mem hg hh, fun y hy => ?_⟩
    have h1 := hhL y hy
    have h2 := hgL y hy
    have h3 : g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ = h * y * h⁻¹ * y⁻¹ := E.comm_V₁ hg h1
    have : g * h * y * (g * h)⁻¹ * y⁻¹ =
        (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group
    rw [this, h3]
    exact E.V₁.mul_mem h1 h2
  inv_mem' := by
    rintro g ⟨hg, hgL⟩
    refine ⟨E.Gz.inv_mem hg, fun y hy => ?_⟩
    have hc := hgL y hy
    have hcomm := E.comm_V₁ (E.Gz.inv_mem hg) hc
    have key : (g⁻¹ * y * (g⁻¹)⁻¹ * y⁻¹)⁻¹ = g⁻¹ * (g * y * g⁻¹ * y⁻¹) * (g⁻¹)⁻¹ := by group
    have : (g⁻¹ * y * (g⁻¹)⁻¹ * y⁻¹)⁻¹ ∈ E.V₁ := by rw [key, hcomm]; exact hc
    simpa using E.V₁.inv_mem this

theorem Rz_le_Gz : E.Rz ≤ E.Gz := fun _ hg => hg.1

theorem Rz_conj {h g : G} (hh : h ∈ E.Gz) (hg : g ∈ E.Rz) : h * g * h⁻¹ ∈ E.Rz := by
  obtain ⟨hgG, hgL⟩ := hg
  refine ⟨E.Gz.mul_mem (E.Gz.mul_mem hh hgG) (E.Gz.inv_mem hh), fun y hy => ?_⟩
  have hc := hgL (h⁻¹ * y * h) (E.Lam_conj hy hh)
  have hcomm := E.comm_V₁ hh hc
  have key : h * g * h⁻¹ * y * (h * g * h⁻¹)⁻¹ * y⁻¹ =
      h * (g * (h⁻¹ * y * h) * g⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ := by group
  rw [key, hcomm]
  exact hc

theorem sq_comm_of_comm_V₁ {g x : G} (hg : g ∈ E.Gz) (h : g * x * g⁻¹ * x⁻¹ ∈ E.V₁) :
    x * (g * g) = (g * g) * x := by
  have hz : E.z * g = g * E.z := E.mem_Gz.1 hg
  rcases E.mem_V₁.1 h with h1 | h1
  · have h2 : g * x = x * g := by
      calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
        _ = x * g := by rw [h1, one_mul]
    calc x * (g * g) = (x * g) * g := by group
      _ = (g * x) * g := by rw [h2]
      _ = g * (x * g) := by group
      _ = g * (g * x) := by rw [h2]
      _ = g * g * x := by group
  · have h2 : g * x = E.z * (x * g) := by
      calc g * x = (g * x * g⁻¹ * x⁻¹) * (x * g) := by group
        _ = E.z * (x * g) := by rw [h1]
    calc x * (g * g) = (x * g) * g := by group
      _ = (E.z * E.z) * (x * g) * g := by rw [E.z_sq, one_mul]
      _ = E.z * (E.z * (x * g)) * g := by group
      _ = E.z * (g * x) * g := by rw [h2]
      _ = (E.z * g) * x * g := by group
      _ = (g * E.z) * x * g := by rw [hz]
      _ = g * (E.z * x) * g := by group
      _ = g * (E.z * x * g) := by group
      _ = g * (E.z * (x * g)) := by group
      _ = g * (g * x) := by rw [h2]
      _ = g * g * x := by group

theorem Rz_isPGroup [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) : IsPGroup 2 E.Rz := by
  intro g
  obtain ⟨hgG, hgL⟩ := g.2
  have hz : E.z * g.1 = g.1 * E.z := E.mem_Gz.1 hgG
  have hgg : g.1 * g.1 ∈ Subgroup.centralizer ({E.z, E.t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · calc E.z * (g.1 * g.1) = (E.z * g.1) * g.1 := by group
        _ = (g.1 * E.z) * g.1 := by rw [hz]
        _ = g.1 * (E.z * g.1) := by group
        _ = g.1 * (g.1 * E.z) := by rw [hz]
        _ = g.1 * g.1 * E.z := by group
    · exact E.sq_comm_of_comm_V₁ hgG (hgL E.t E.t_mem_Lam)
  rw [E.lemma_13_9_7 hEven hT hM] at hgg
  obtain ⟨k, hk⟩ := E.J_isPGroup ⟨g.1 * g.1, hgg⟩
  have hk' : (g.1 * g.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  refine ⟨k + 1, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  have h2 : g.1 ^ 2 ^ (k + 1) = (g.1 * g.1) ^ 2 ^ k := by
    rw [pow_succ', pow_mul, pow_two]
  rw [h2]
  exact hk'

theorem Qz_le_T [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T) :
    pCoreOf 2 E.Gz ≤ T :=
  (E.almostSpecialHyp hEven hT).pCoreOf_le_T

theorem Rz_eq_Qz [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) : E.Rz = pCoreOf 2 E.Gz := by
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 E.Rz_le_Gz
      (le_normalizer_of_conj_mem fun h hh g hg => E.Rz_conj hh hg) (E.Rz_isPGroup hEven hT hM)
  · intro q hq
    refine ⟨pCoreOf_le 2 E.Gz hq, fun y hy => ?_⟩
    obtain ⟨-, -, hcomm⟩ := E.U_facts hEven hT
    have := hcomm y (E.Lam_le_U hy) q hq
    have h2 : q * y * q⁻¹ * y⁻¹ = (y * q * y⁻¹ * q⁻¹)⁻¹ := by group
    rw [h2]
    exact E.V₁.inv_mem this

theorem Lam_classify [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    ∃ Sel : List Wc, (Sel = [t0] ∨ Sel = [t0, s0] ∨ Sel = [t0, u4] ∨ Sel = [t0, s0, u4] ∨
      Sel = [t0, u3, u5] ∨ Sel = [t0, u3, u4, u5] ∨ Sel = [t0, u7]) ∧
      ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel := by
  refine lam_classify (fun w => w ∈ Th ∧ E.ι w ∈ E.Lam) ?_ ?_ ?_ ?_ ?_
  · rintro w ⟨hw, hy⟩
    refine isCand_iff.2 ⟨hw, E.ι_sq_eq_one.1 (E.Lam_sq hy), ?_, ?_⟩
    · intro h
      exact E.Lam_ne_one hy (by rw [h, map_one])
    · by_contra hD
      have hD' : D1 w = true := by simpa using hD
      exact E.Lam_not_mem_Δ₁ hT hM hy ((E.mem_Δ₁_iff).2 hD')
  · rintro w ⟨hw, hy⟩ v hv
    refine ⟨Th.mul_mem (Th.mul_mem (Th.inv_mem hv) hw) hv, ?_⟩
    have hvT : E.ι v ∈ T := E.mem_T_iff.2 ⟨v, hv, rfl⟩
    have := E.Lam_conj hy (E.T_le_Gz hvT)
    simpa [map_mul, map_inv] using this
  · rintro w ⟨hw, hy⟩
    refine ⟨Th.mul_mem hw z0_mem_Th, ?_⟩
    have e : E.ι (w * z0) = E.ι w * E.z := map_mul _ _ _
    rw [e]
    exact E.Lam_mul_z hy
  · rintro w w' ⟨hw, hy⟩ ⟨hw', hy'⟩
    have h := E.Lam_comm hEven hT hy hy'
    have h' : E.ι (cm w w') ∈ E.V₁ := by simpa [cm, map_mul, map_inv] using h
    rcases E.mem_V₁.1 h' with h1 | h1
    · left
      exact E.injective (by rw [h1, map_one])
    · right
      exact E.injective h1
  · exact ⟨Jh_le_Th (T1h_le_Jh t0_mem_T1h), E.t_mem_Lam⟩

theorem ncard_image_of_nodup (E : Emb G T M) {L : List Wc} (hL : L.Nodup) :
    (E.ι '' {w | w ∈ L}).ncard = L.length := by
  rw [Set.ncard_image_of_injective _ E.injective]
  have : {w | w ∈ L} = ↑(L.toFinset) := by
    ext w
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hL]

theorem Lam_eq_image [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) {Sel : List Wc}
    (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel) :
    E.Lam = E.ι '' {w | w ∈ LS Sel} := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 (E.Lam_mem_T hEven hT hy)
    exact ⟨w, (hSel w).1 ⟨hw, hy⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ((hSel w).2 hw).2

theorem Lam_ncard [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) {Sel : List Wc}
    (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel) :
    E.Lam.ncard = (LS Sel).length := by
  rw [E.Lam_eq_image hEven hT hSel]
  exact E.ncard_image_of_nodup (nodup_LS Sel)

theorem Lam_card [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) : E.Lam.ncard * 64 = Nat.card E.Gz := by
  have h := ncard_conjClass_mul_card E.Gz E.t
  have hJ : E.Gz ⊓ Subgroup.centralizer ({E.t} : Set G) = E.J := by
    rw [← E.lemma_13_9_7 hEven hT hM, E.centralizer_pair_eq]
    rfl
  rw [hJ, E.card_J] at h
  exact h

theorem Qz_eq_image [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {Sel : List Wc}
    (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel) :
    (pCoreOf 2 E.Gz : Set G) = E.ι '' {x | x ∈ Rl (LS Sel)} := by
  have hR := E.Rz_eq_Qz hEven hT hM
  ext g
  constructor
  · intro hg
    have hg' : g ∈ E.Rz := by rw [hR]; exact hg
    have hgT : g ∈ T := E.Qz_le_T hEven hT hg
    obtain ⟨x, hx, rfl⟩ := E.mem_T_iff.1 hgT
    refine ⟨x, mem_Rl.2 ⟨hx, fun w hw => ?_⟩, rfl⟩
    have hy : E.ι w ∈ E.Lam := ((hSel w).2 hw).2
    have := hg'.2 (E.ι w) hy
    have h' : E.ι (cm x w) ∈ E.V₁ := by simpa [cm, map_mul, map_inv] using this
    rcases E.mem_V₁.1 h' with h1 | h1
    · left
      exact E.injective (by rw [h1, map_one])
    · right
      exact E.injective h1
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxT, hxc⟩ := mem_Rl.1 hx
    have hmem : E.ι x ∈ E.Rz := by
      refine ⟨E.T_le_Gz (E.mem_T_iff.2 ⟨x, hxT, rfl⟩), fun y hy => ?_⟩
      obtain ⟨w, hw, rfl⟩ := E.mem_T_iff.1 (E.Lam_mem_T hEven hT hy)
      have hwL : w ∈ LS Sel := (hSel w).1 ⟨hw, hy⟩
      have e : E.ι (cm x w) = E.ι x * E.ι w * (E.ι x)⁻¹ * (E.ι w)⁻¹ := by
        simp [cm, map_mul, map_inv]
      rw [← e]
      rcases hxc w hwL with h1 | h1
      · rw [h1, map_one]
        exact one_mem _
      · rw [h1]
        exact E.z_mem_V₁
    rw [← hR]
    exact hmem

theorem Qz_card [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) {Sel : List Wc}
    (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel) :
    Nat.card (pCoreOf 2 E.Gz) = (Rl (LS Sel)).length := by
  have h1 : Nat.card (pCoreOf 2 E.Gz) = (pCoreOf 2 E.Gz : Set G).ncard :=
    (Nat.card_coe_set_eq _).symm
  rw [h1, E.Qz_eq_image hEven hT hM hSel]
  exact E.ncard_image_of_nodup (nodup_Rl _)

theorem Qz_normal {g q : G} (hg : g ∈ E.Gz) (hq : q ∈ pCoreOf 2 E.Gz) :
    g * q * g⁻¹ ∈ pCoreOf 2 E.Gz :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 E.Gz hg) q).1 hq

theorem bad_case [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) {Sel : List Wc}
    (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS Sel)
    {p a : ℕ} [Fact p.Prime] (hp57 : p = 5 ∨ p = 7) (ha : a ≤ 3)
    (hlen : (LS Sel).length = 2 * p) (hR : (Rl (LS Sel)).length * 2 ^ a = 128) :
    (p = 5 → a ≤ 2) ∧ (p = 7 → a ≤ 1) ∧
      (1 ≤ a → ∃ x ∈ thList, x ^ 2 ^ (a - 1) ∉ Rl (LS Sel)) := by
  have hLam := E.Lam_ncard hEven hT hSel
  have hGz := E.Lam_card hEven hT hM
  have hcardGz : Nat.card E.Gz = p * Nat.card T := by
    rw [← hGz, hLam, hlen, E.card_T]
    ring
  have hQ := E.Qz_card hEven hT hM hSel
  have hcardT : Nat.card T = Nat.card (pCoreOf 2 E.Gz) * 2 ^ a := by
    rw [E.card_T, hQ]
    omega
  have hmax : ∀ K : Subgroup G, K ≤ E.Gz → (∀ x ∈ E.Gz, ∀ k ∈ K, x * k * x⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ pCoreOf 2 E.Gz := fun K hK hconj hK2 =>
    le_pCoreOf_of_le_normalizer 2 hK (le_normalizer_of_conj_mem hconj) hK2
  have key := cyclic_quotient_of_prime_index (X := E.Gz) (N := pCoreOf 2 E.Gz) (T := T)
    (pCoreOf_le 2 E.Gz)
    (fun x hx n hn => (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 E.Gz hx) n).1 hn)
    (pCoreOf_isPGroup 2 E.Gz) hmax (E.Qz_le_T hEven hT) E.T_le_Gz hp57 ha hcardT hcardGz
  obtain ⟨h5, h7, h8⟩ := key
  refine ⟨h5, h7, fun ha1 => ?_⟩
  obtain ⟨g, hgT, hgN⟩ := h8 ha1
  obtain ⟨x, hx, rfl⟩ := E.mem_T_iff.1 hgT
  refine ⟨x, (mem_thList x).2 hx, fun hxR => hgN ?_⟩
  rw [← map_pow]
  have : E.ι (x ^ 2 ^ (a - 1)) ∈ (pCoreOf 2 E.Gz : Set G) := by
    rw [E.Qz_eq_image hEven hT hM hSel]
    exact ⟨_, hxR, rfl⟩
  exact this

theorem true_case [Finite G] (hEven : quasithinEvenCharacteristic G) (hT : quasithinIsSylowTwo T)
    (hM : quasithinIsMaxTwoLocal M) (hSel : ∀ w, (w ∈ Th ∧ E.ι w ∈ E.Lam) ↔ w ∈ LS [t0, u4]) :
    Nat.card E.Gz = 384 ∧ E.B ≤ pCoreOf 2 E.Gz ∧ E.Q ≤ pCoreOf 2 E.Gz ∧
      E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄) := by
  have hLam := E.Lam_ncard hEven hT hSel
  have hGz := E.Lam_card hEven hT hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hGz, hLam, len_S2]
  · rintro _ ⟨x, hx, rfl⟩
    have : E.ι x ∈ (pCoreOf 2 E.Gz : Set G) := by
      rw [E.Qz_eq_image hEven hT hM hSel]
      exact ⟨x, A2_le_Rl_true x hx, rfl⟩
    exact this
  · rintro _ ⟨x, hx, rfl⟩
    have : E.ι x ∈ (pCoreOf 2 E.Gz : Set G) := by
      rw [E.Qz_eq_image hEven hT hM hSel]
      exact ⟨x, Qh_le_Rl_true x hx, rfl⟩
    exact this
  · rw [E.Lam_eq_image hEven hT hSel]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hwB, hwD⟩ := mem_LS_true.1 hw
      refine ⟨⟨w, hwB, rfl⟩, ?_⟩
      rcases hwD with h | h
      · exact Or.inl ((E.mem_Δ₂_iff).2 h)
      · exact Or.inr ((E.mem_Δ₄_iff).2 h)
    · rintro ⟨⟨w, hwB, rfl⟩, hy⟩
      refine ⟨w, mem_LS_true.2 ⟨hwB, ?_⟩, rfl⟩
      rcases hy with h | h
      · exact Or.inl ((E.mem_Δ₂_iff).1 h)
      · exact Or.inr ((E.mem_Δ₄_iff).1 h)

theorem Q_normal_Gz [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hQle : E.Q ≤ pCoreOf 2 E.Gz) :
    ∀ g ∈ E.Gz, ∀ q ∈ E.Q, g * q * g⁻¹ ∈ E.Q := by
  intro g hg q hq
  set Q' : Subgroup G := E.Q.map (MulAut.conj g).toMonoidHom with hQ'
  have hQ'le : Q' ≤ T := by
    rintro _ ⟨q', hq', rfl⟩
    exact E.Qz_le_T hEven hT (E.Qz_normal hg (hQle hq'))
  have hsq : ∀ u ∈ Q', u * u ∈ Subgroup.zpowers E.z := by
    rintro _ ⟨q', hq', rfl⟩
    have h1 : q' * q' ∈ E.V₁ := E.Q_elemAbelian_mod_z.1 q' hq'
    have e : (MulAut.conj g).toMonoidHom q' * (MulAut.conj g).toMonoidHom q' =
        g * (q' * q') * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, E.comm_V₁ hg h1]
    exact h1
  have hc : ∀ u ∈ Q', ∀ v ∈ Q', u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers E.z := by
    rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩
    have h1 : q₁ * q₂ * q₁⁻¹ * q₂⁻¹ ∈ E.V₁ := E.Q_elemAbelian_mod_z.2 q₁ hq₁ q₂ hq₂
    have e : (MulAut.conj g).toMonoidHom q₁ * (MulAut.conj g).toMonoidHom q₂ *
        ((MulAut.conj g).toMonoidHom q₁)⁻¹ * ((MulAut.conj g).toMonoidHom q₂)⁻¹ =
        g * (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, E.comm_V₁ hg h1]
    exact h1
  have hcard : Nat.card Q' = 32 := by
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g).injective, E.card_Q]
  have := (E.Q_unique_maximal Q' hQ'le hsq hc).2 hcard
  have hmem : g * q * g⁻¹ ∈ Q' := ⟨q, hq, by simp [MulAut.conj_apply]⟩
  rw [this] at hmem
  exact hmem

theorem B_normal_Gz [Finite G] (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    (hBle : E.B ≤ pCoreOf 2 E.Gz) : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B := by
  have hwc := E.isWeaklyClosedIn_B hT hM
  have key : ∀ g ∈ E.Gz, ∀ b ∈ E.B, g⁻¹ * b * g ∈ E.B := by
    intro g hg b hb
    have hle : conjSubgroup E.B g⁻¹ ≤ T := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have h2 := E.Qz_normal hg (hBle hx)
      have e : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
      rw [e]
      exact E.Qz_le_T hEven hT h2
    have hb' : b ∈ conjSubgroup E.B g⁻¹ := by rw [hwc g⁻¹ hle]; exact hb
    rw [mem_conjSubgroup_iff] at hb'
    simpa using hb'
  intro g hg b hb
  simpa using key g⁻¹ (E.Gz.inv_mem hg) b hb

theorem lemma_13_9_8 [Finite G] (hG : IsSimpleGroup G) (hEven : quasithinEvenCharacteristic G)
    (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M) :
    Nat.card E.Gz = 384 ∧ E.B ≤ pCoreOf 2 E.Gz ∧ E.Q ≤ pCoreOf 2 E.Gz ∧
      (∀ g ∈ E.Gz, ∀ q ∈ E.Q, g * q * g⁻¹ ∈ E.Q) ∧
      (∀ g ∈ E.Gz, ∀ b ∈ E.B, g * b * g⁻¹ ∈ E.B) ∧
      E.Lam = (E.B : Set G) ∩ (E.Δ₂ ∪ E.Δ₄) := by
  obtain ⟨Sel, hcases, hSel⟩ := E.Lam_classify hEven hT hM
  have hLam := E.Lam_ncard hEven hT hSel
  have hGz := E.Lam_card hEven hT hM
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exfalso
    have hcard : Nat.card E.Gz = Nat.card T := by
      rw [← hGz, hLam, len_S0, E.card_T]
    have hlt := (E.lemma_13_9_5 hG hT hM).1
    have heq : T = E.Gz :=
      Subgroup.eq_of_le_of_card_ge E.T_le_Gz (by rw [hcard])
    exact (ne_of_lt hlt) heq
  ·
    exfalso
    obtain ⟨-, -, h3⟩ := E.bad_case hEven hT hM (p := 5) (a := 2) hSel (Or.inl rfl) (by norm_num)
      (by rw [len_S1]) (by rw [Rlen_S1]; norm_num)
    obtain ⟨x, hx, hxn⟩ := h3 (by norm_num)
    exact hxn (by simpa [pow_two] using sq_mem_Rl_S1 x hx)
  · have h := E.true_case hEven hT hM hSel
    obtain ⟨hc, hB, hQ, hLam'⟩ := h
    exact ⟨hc, hB, hQ, E.Q_normal_Gz hEven hT hQ, E.B_normal_Gz hEven hT hM hB, hLam'⟩
  ·
    exfalso
    obtain ⟨-, h2, -⟩ := E.bad_case hEven hT hM (p := 7) (a := 2) hSel (Or.inr rfl) (by norm_num)
      (by rw [len_S3]) (by rw [Rlen_S3]; norm_num)
    exact absurd (h2 rfl) (by norm_num)
  ·
    exfalso
    obtain ⟨h1, -, -⟩ := E.bad_case hEven hT hM (p := 5) (a := 3) hSel (Or.inl rfl) (by norm_num)
      (by rw [len_S4]) (by rw [Rlen_S4]; norm_num)
    exact absurd (h1 rfl) (by norm_num)
  ·
    exfalso
    obtain ⟨-, h2, -⟩ := E.bad_case hEven hT hM (p := 7) (a := 3) hSel (Or.inr rfl) (by norm_num)
      (by rw [len_S5]) (by rw [Rlen_S5]; norm_num)
    exact absurd (h2 rfl) (by norm_num)
  ·
    exfalso
    obtain ⟨h1, -, -⟩ := E.bad_case hEven hT hM (p := 5) (a := 3) hSel (Or.inl rfl) (by norm_num)
      (by rw [len_S6]) (by rw [Rlen_S6]; norm_num)
    exact absurd (h1 rfl) (by norm_num)

end Emb

end CFSG.Quasithin.A10
