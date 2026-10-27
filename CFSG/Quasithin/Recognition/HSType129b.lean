module

public import CFSG.Quasithin.Recognition.HSType129a
public import CFSG.Quasithin.Recognition.HSTypeL12g

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem perm_five_exists_odd_invol_comm : ∀ τ : Equiv.Perm (Fin 5), τ * τ * τ = 1 → τ ≠ 1 →
    ∃ σ : Equiv.Perm (Fin 5), σ * σ = 1 ∧ Equiv.Perm.sign σ = -1 ∧ σ * τ = τ * σ := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G}

abbrev qAction (z : G) : MulAction ↥(hsQ z) G :=
  MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp (hsQ z).subtype)

theorem ncard_orbit_invol [Finite G] (h : HSSetting z V) {s : G} (hsH : s ∈ hsH z)
    (hsK : s ∉ hsK z) (hss : s * s = 1) :
    (@MulAction.orbit ↥(hsQ z) G (qAction z).toSMul s).ncard = 8 := by
  let := qAction z
  have hstab : MulAction.stabilizer ↥(hsQ z) s =
      (hsQ z ⊓ Subgroup.centralizer ({s} : Set G)).subgroupOf (hsQ z) := by
    ext q
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    change (q : G) * s * (q : G)⁻¹ = s ↔ _
    constructor
    · intro hq
      refine ⟨q.2, ?_⟩
      calc (q : G) * s = (q : G) * s * (q : G)⁻¹ * (q : G) := by group
        _ = s * (q : G) := by rw [hq]
    · rintro ⟨-, hq⟩
      rw [hq, mul_inv_cancel_right]
  have hcardstab : Nat.card (MulAction.stabilizer ↥(hsQ z) s) = 8 := by
    rw [hstab, ← h.card_centralizer_invol hsH hsK hss]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥(hsQ z) s)
  rw [MulAction.index_stabilizer, hcardstab, h.card_Q] at hmul
  omega

@[expose] def cosetInvol (z s : G) : Set G := {g | s⁻¹ * g ∈ hsQ z ∧ g * g = 1}

theorem exists_invol_centralizer_three [Finite G] (h : HSSetting z V) {x : G}
    (hxH : x ∈ hsH z) (hx3 : orderOf x = 3) :
    ∃ d ∈ hsH z, d ∉ hsK z ∧ d * d = 1 ∧ d * x = x * d := by
  classical
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := fun g => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hxN : x ∈ Subgroup.normalizer (hsQ z : Set G) :=
    le_normalizer_quasithinGenFitting (hsH z) hxH
  have hx31 : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
  have hφx3 : φ ⟨x, hxH⟩ * φ ⟨x, hxH⟩ * φ ⟨x, hxH⟩ = 1 := by
    rw [← map_mul, ← map_mul]
    have : (⟨x, hxH⟩ : ↥(hsH z)) * ⟨x, hxH⟩ * ⟨x, hxH⟩ = 1 := Subtype.ext hx31
    rw [this, map_one]
  have hφx1 : φ ⟨x, hxH⟩ ≠ 1 := by
    intro h1
    have h2 : x ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨Subgroup.mem_zpowers x, (hkerQ _).mp h1⟩
    rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  obtain ⟨σ₀, hσ₀2, hσ₀sign, hσ₀x⟩ :=
    perm_five_exists_odd_invol_comm (φ ⟨x, hxH⟩) hφx3 hφx1
  obtain ⟨s₀, hs₀, hss₀, hsinv, -⟩ := h.exists_invol_inverts_ZQ
  obtain ⟨w, hwZ, hw1, hwz', hww⟩ := h.exists_mem_ZQ_ne
  have hs₀K : s₀ ∉ hsK z := by
    intro hs
    have h1 := hsinv w hwZ
    rw [(Subgroup.mem_centralizer_iff.mp hs.2 w hwZ).symm, mul_inv_cancel_right] at h1
    have : w * w = 1 := by
      calc w * w = w * w⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel w
    rw [hww] at this
    exact h.z_ne_one this
  have hφs₀2 : φ ⟨s₀, hs₀.1⟩ * φ ⟨s₀, hs₀.1⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s₀, hs₀.1⟩ : ↥(hsH z)) * ⟨s₀, hs₀.1⟩ = 1 := Subtype.ext hss₀
    rw [this, map_one]
  obtain ⟨ρ, -, hρ⟩ := perm_five_odd_invol_conj (φ ⟨s₀, hs₀.1⟩)
    (h.sign_eq_neg_one_of_not_mem_K hker hs₀K) hφs₀2
  obtain ⟨ρ', -, hρ'⟩ := perm_five_odd_invol_conj σ₀ hσ₀sign hσ₀2
  obtain ⟨k, hk⟩ := hφ (ρ'⁻¹ * ρ)
  set s₁ := (k : G) * s₀ * (k : G)⁻¹ with hs₁
  have hs₁H : s₁ ∈ hsH z := (hsH z).mul_mem ((hsH z).mul_mem k.2 hs₀.1) ((hsH z).inv_mem k.2)
  have hs₁K : s₁ ∉ hsK z := fun hK => hs₀K (by
    have := h.conj_mem_K ((hsH z).inv_mem k.2) hK
    rwa [hs₁, show (k : G)⁻¹ * ((k : G) * s₀ * (k : G)⁻¹) * (k : G)⁻¹⁻¹ = s₀ by group] at this)
  have hs₁2 : s₁ * s₁ = 1 := by
    rw [hs₁, show (k : G) * s₀ * (k : G)⁻¹ * ((k : G) * s₀ * (k : G)⁻¹) =
      (k : G) * (s₀ * s₀) * (k : G)⁻¹ by group, hss₀, mul_one, mul_inv_cancel]
  have hφs₁ : φ ⟨s₁, hs₁H⟩ = σ₀ := by
    have e : (⟨s₁, hs₁H⟩ : ↥(hsH z)) = k * ⟨s₀, hs₀.1⟩ * k⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hk]
    calc ρ'⁻¹ * ρ * φ ⟨s₀, hs₀.1⟩ * (ρ'⁻¹ * ρ)⁻¹ = ρ'⁻¹ * (ρ * φ ⟨s₀, hs₀.1⟩ * ρ⁻¹) * ρ' := by
          group
      _ = ρ'⁻¹ * (ρ' * σ₀ * ρ'⁻¹) * ρ' := by rw [hρ, hρ']
      _ = σ₀ := by group
  have hxs₁ : s₁⁻¹ * x * s₁ * x⁻¹ ∈ hsQ z := by
    have hmemH : s₁⁻¹ * x * s₁ * x⁻¹ ∈ hsH z := (hsH z).mul_mem ((hsH z).mul_mem
      ((hsH z).mul_mem ((hsH z).inv_mem hs₁H) hxH) hs₁H) ((hsH z).inv_mem hxH)
    have e : (⟨s₁⁻¹ * x * s₁ * x⁻¹, hmemH⟩ : ↥(hsH z)) =
        (⟨s₁, hs₁H⟩ : ↥(hsH z))⁻¹ * ⟨x, hxH⟩ * ⟨s₁, hs₁H⟩ * (⟨x, hxH⟩ : ↥(hsH z))⁻¹ := rfl
    refine (hkerQ ⟨_, hmemH⟩).mp ?_
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hφs₁, mul_assoc σ₀⁻¹, ← hσ₀x]
    group
  have hwz : w ∉ Subgroup.zpowers z := by
    intro hw
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hw with e | e
    · exact hw1 e
    · exact hwz' e
  let := qAction z
  set I := cosetInvol z s₁ with hI
  set O₁ := MulAction.orbit ↥(hsQ z) s₁ with hO₁
  set O₂ := MulAction.orbit ↥(hsQ z) (s₁ * w) with hO₂
  have hs₁w : s₁ * w ∈ hsH z := (hsH z).mul_mem hs₁H (h.Q_le_H hwZ.1)
  have hs₁wK : s₁ * w ∉ hsK z := fun hK => hs₁K (by
    have := (hsK z).mul_mem hK (h.Q_le_K ((hsQ z).inv_mem hwZ.1))
    rwa [mul_inv_cancel_right] at this)
  have hs₁w2 : s₁ * w * (s₁ * w) = 1 := by
    have hinv := h.inv_of_not_mem_K hs₁H hs₁K hwZ
    calc s₁ * w * (s₁ * w) = (s₁ * w * s₁⁻¹) * (s₁ * s₁) * w := by group
      _ = 1 := by rw [hinv, hs₁2, mul_one, inv_mul_cancel]
  have hIeq : I = O₁ ∪ O₂ := by
    ext g
    constructor
    · rintro ⟨hgQ, hg2⟩
      have hg : g = s₁ * (s₁⁻¹ * g) := by group
      have hsq : s₁ * (s₁⁻¹ * g) * (s₁ * (s₁⁻¹ * g)) = 1 := by rw [← hg]; exact hg2
      obtain ⟨r, hr, hr'⟩ := h.exists_conj_of_invol_mul hs₁H hs₁K hs₁2 hwZ hwz hgQ hsq
      rw [← hg] at hr'
      rcases hr' with e | e
      · exact Or.inl ⟨⟨r, hr⟩, e.symm⟩
      · exact Or.inr ⟨⟨r, hr⟩, e.symm⟩
    · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
      · refine ⟨?_, ?_⟩
        · change s₁⁻¹ * ((q : G) * s₁ * (q : G)⁻¹) ∈ hsQ z
          rw [show s₁⁻¹ * ((q : G) * s₁ * (q : G)⁻¹) = s₁⁻¹ * (q : G) * s₁ * (q : G)⁻¹ by group]
          refine (hsQ z).mul_mem ?_ ((hsQ z).inv_mem q.2)
          have := conj_mem_Q ((hsH z).inv_mem hs₁H) q.2
          rwa [inv_inv] at this
        · change (q : G) * s₁ * (q : G)⁻¹ * ((q : G) * s₁ * (q : G)⁻¹) = 1
          rw [show (q : G) * s₁ * (q : G)⁻¹ * ((q : G) * s₁ * (q : G)⁻¹) =
            (q : G) * (s₁ * s₁) * (q : G)⁻¹ by group, hs₁2, mul_one, mul_inv_cancel]
      · refine ⟨?_, ?_⟩
        · change s₁⁻¹ * ((q : G) * (s₁ * w) * (q : G)⁻¹) ∈ hsQ z
          rw [show s₁⁻¹ * ((q : G) * (s₁ * w) * (q : G)⁻¹) =
            s₁⁻¹ * (q : G) * s₁ * (w * (q : G)⁻¹) by group]
          refine (hsQ z).mul_mem ?_ ((hsQ z).mul_mem hwZ.1 ((hsQ z).inv_mem q.2))
          have := conj_mem_Q ((hsH z).inv_mem hs₁H) q.2
          rwa [inv_inv] at this
        · change (q : G) * (s₁ * w) * (q : G)⁻¹ * ((q : G) * (s₁ * w) * (q : G)⁻¹) = 1
          rw [show (q : G) * (s₁ * w) * (q : G)⁻¹ * ((q : G) * (s₁ * w) * (q : G)⁻¹) =
            (q : G) * (s₁ * w * (s₁ * w)) * (q : G)⁻¹ by group, hs₁w2, mul_one, mul_inv_cancel]
  have hO₁ : O₁.ncard = 8 := h.ncard_orbit_invol hs₁H hs₁K hs₁2
  have hO₂ : O₂.ncard = 8 := h.ncard_orbit_invol hs₁w hs₁wK hs₁w2
  have hIcard : I.ncard = 8 ∨ I.ncard = 16 := by
    rw [hIeq]
    by_cases hdis : Disjoint O₁ O₂
    · right
      rw [Set.ncard_union_eq hdis (Set.toFinite _) (Set.toFinite _), hO₁, hO₂]
    · left
      have heq : O₁ = O₂ := by
        rcases MulAction.orbit.eq_or_disjoint (G := ↥(hsQ z)) s₁ (s₁ * w) with e | e
        · exact e
        · exact absurd e hdis
      rw [heq, Set.union_self, hO₂]
  have hxI : ∀ g ∈ I, x * g * x⁻¹ ∈ I := by
    rintro g ⟨hgQ, hg2⟩
    refine ⟨?_, ?_⟩
    · have e : s₁⁻¹ * (x * g * x⁻¹) = (s₁⁻¹ * x * s₁ * x⁻¹) * (x * (s₁⁻¹ * g) * x⁻¹) := by
        group
      rw [e]
      exact (hsQ z).mul_mem hxs₁ ((Subgroup.mem_normalizer_iff.mp hxN _).mp hgQ)
    · rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hg2, mul_one,
        mul_inv_cancel]
  have := Fintype.ofFinite ↥I
  let f : Function.End ↥I := fun g => ⟨x * g * x⁻¹, hxI g g.2⟩
  have hf : ∀ (n : ℕ) (g : ↥I), ((f ^ n) g : G) = x ^ n * g * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro g; simp; rfl
    | succ n ih =>
      intro g
      rw [pow_succ']
      show x * ((f ^ n) g : G) * x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext g
    apply Subtype.ext
    show ((f ^ 3 ^ 1) g : G) = (g : G)
    rw [pow_one, hf, ← hx3, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq] at hmod
  have hfix : (Function.fixedPoints f).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty] at hmod
    rcases hIcard with h8 | h16
    · rw [h8] at hmod
      exact absurd hmod (by decide)
    · rw [h16] at hmod
      exact absurd hmod (by decide)
  obtain ⟨⟨d, hdQ, hd2⟩, hdf⟩ := hfix
  have hdx : x * d * x⁻¹ = d := congrArg Subtype.val hdf
  have hdH : d ∈ hsH z := by
    have := (hsH z).mul_mem hs₁H (h.Q_le_H hdQ)
    rwa [mul_inv_cancel_left] at this
  refine ⟨d, hdH, fun hK => hs₁K ?_, hd2, ?_⟩
  · have := (hsK z).mul_mem hK (h.Q_le_K ((hsQ z).inv_mem hdQ))
    rwa [show d * (s₁⁻¹ * d)⁻¹ = s₁ by group] at this
  · calc d * x = x * d * x⁻¹ * x := by rw [hdx]
      _ = x * d := by group

end HSSetting

end CFSG.Quasithin.HSType
