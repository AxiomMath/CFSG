module

public import CFSG.Walter.Ree.Thompson3.Centralizer

public section

namespace CFSG.Walter.Ree.T2.RType

variable {k : Type} [Field k] [CharP k 3] [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

omit [Field k] [CharP k 3] in
theorem card_omega : Nat.card (Option (k × k × k)) = Nat.card k ^ 3 + 1 := by
  rw [Finite.card_option, Nat.card_prod, Nat.card_prod]; ring

theorem invol_comm_fix_eq
    {x y : G} (hx : x * x = 1) (hx1 : x ≠ 1) (hy : y * y = 1)
    (hy1 : y ≠ 1) (hxy : x * y = y * x) {ω : Option (k × k × k)} (hxω : R.act ω x = ω)
    (hyω : R.act ω y = ω) : x = y := by
  by_contra hne
  have hxN := (R.fix_iff_mem_N ω x).mp hxω
  have hyN := (R.fix_iff_mem_N ω y).mp hyω
  obtain ⟨n, hn⟩ := R.exists_ι hxN
  obtain ⟨m, hm⟩ := R.exists_ι hyN
  set r := R.rep ω
  have hconj : ∀ u v : G, (r * u * r⁻¹) * (r * v * r⁻¹) = r * (u * v) * r⁻¹ := fun u v => by group
  have hinj : ∀ u v : G, r * u * r⁻¹ = r * v * r⁻¹ → u = v := fun u v h => by
    have := congrArg (fun z => r⁻¹ * z * r) h
    simpa [mul_assoc] using this
  have hnn : n * n = 1 := R.ι_injective (by rw [map_mul, ← hn, hconj, hx, map_one]; group)
  have hmm : m * m = 1 := R.ι_injective (by rw [map_mul, ← hm, hconj, hy, map_one]; group)
  have hn1 : n ≠ 1 := fun h => hx1 (hinj _ _ (by rw [hn, h, map_one]; group))
  have hm1 : m ≠ 1 := fun h => hy1 (hinj _ _ (by rw [hm, h, map_one]; group))
  have hnm : n * m * (n * m) = 1 := by
    apply R.ι_injective
    simp only [map_mul, ← hn, ← hm, hconj, map_one]
    rw [show x * y * (x * y) = x * (y * x) * y by group, ← hxy,
      show x * (x * y) * y = (x * x) * (y * y) by group, hx, hy]; group
  have hnm1 : n * m ≠ 1 := by
    intro h
    apply hne
    have : n = m⁻¹ := eq_inv_of_mul_eq_one_left h
    have hm' : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
    apply hinj
    rw [hn, hm, this, hm']
  have h1 := (thompsonN_invol_form hnn hn1).1
  have h2 := (thompsonN_invol_form hmm hm1).1
  have h3 := (thompsonN_invol_form hnm hnm1).1
  rw [ThompsonN.mul_κ, h1, h2, neg_one_mul, neg_neg] at h3
  have := congrArg Units.val h3
  simp only [Units.val_one, Units.val_neg] at this
  exact two_ne_zero' (by linear_combination this)

theorem not_mem_fixSet_K_of_J
    {ω : Option (k × k × k)} (hJ : R.act ω R.Jg = ω) :
    R.act ω R.K ≠ ω := by
  intro hK
  have := R.invol_comm_fix_eq R.Jg_mul_Jg (fun h => by
    have := congrArg (fun z => R.act (some (1, 0, 0)) z) h
    simp only [act_J, act_one, Option.some.injEq, Prod.mk.injEq] at this
    exact two_ne_zero' (by linear_combination -this.1)) R.K_mul_K R.K_ne_one R.Jg_mul_K hJ hK
  exact R.K_not_mem (this ▸ R.ι_mem _)

theorem act_YT_J :
    R.act (some (1, 1, d)) R.Jg ≠ some (1, 1, d) := by
  rw [act_J]
  simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, true_and, not_and]
  intro h
  exact absurd h (fun h => two_ne_zero' (by linear_combination -h))

theorem act_001_J :
    R.act (some (0, 0, 1)) R.Jg ≠ some (0, 0, 1) := by
  rw [act_J]
  simp only [neg_zero, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and]
  intro h
  exact two_ne_zero' (by linear_combination -h)

section Orbits

variable {a : ℕ} (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (h69 : Eq69 R)

@[expose] def delta :
    Set (Option (k × k × k)) :=
  (fun h => R.act (some (0, 0, 1)) h) '' (R.hSub ha haσ h69 : Set G)

@[expose] def hOrbit
    (ω : Option (k × k × k)) : Set (Option (k × k × k)) :=
  (fun h => R.act ω h) '' (R.hSub ha haσ h69 : Set G)

theorem delta_eq :
    R.delta ha haσ h69 = R.hOrbit ha haσ h69 (some (0, 0, 1)) := rfl

theorem mem_hOrbit_self
    (ω : Option (k × k × k)) : ω ∈ R.hOrbit ha haσ h69 ω :=
  ⟨1, (R.hSub ha haσ h69).one_mem, R.act_one ω⟩

theorem hOrbit_of_mem
    {ω μ : Option (k × k × k)} (h : μ ∈ R.hOrbit ha haσ h69 ω) :
    R.hOrbit ha haσ h69 μ = R.hOrbit ha haσ h69 ω := by
  obtain ⟨c, hc, rfl⟩ := h
  ext ν
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c * x, (R.hSub ha haσ h69).mul_mem hc hx, R.act_mul ω c x⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ * x, (R.hSub ha haσ h69).mul_mem ((R.hSub ha haσ h69).inv_mem hc) hx, ?_⟩
    simp only
    rw [act_mul, act_act_inv]

theorem not_fix_J_of_mem_hOrbit
    {ω μ : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω)
    (h : μ ∈ R.hOrbit ha haσ h69 ω) : R.act μ R.Jg ≠ μ := by
  obtain ⟨c, hc, rfl⟩ := h
  intro h'
  apply hω
  have hcJ := R.hSet_comm_J hc
  simp only at h'
  rw [← act_mul, hcJ, act_mul] at h'
  exact R.act_injective c h'

theorem card_hOrbit
    {ω : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω) :
    Nat.card (R.hSub ha haσ h69) ≤ 2 * (R.hOrbit ha haσ h69 ω).ncard :=
  R.card_orbit_ge _ (fun _ h => R.hSet_comm_J h) hω

theorem card_hSub' :
    Nat.card k ^ 3 ≤ Nat.card (R.hSub ha haσ h69) + Nat.card k := by
  have h := R.card_hSub ha haσ h69
  have hq : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨m, hm⟩ : ∃ m, Nat.card k = m + 1 := ⟨Nat.card k - 1, by omega⟩
  rw [hm] at h ⊢
  simp only [Nat.add_sub_cancel] at h
  nlinarith [h]

theorem mem_delta_or_orbit
    {ω μ : Option (k × k × k)} (hω : R.act ω R.Jg ≠ ω)
    (hωΔ : ω ∉ R.delta ha haσ h69) (hμ : R.act μ R.Jg ≠ μ) :
    μ ∈ R.delta ha haσ h69 ∨ μ ∈ R.hOrbit ha haσ h69 ω := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hμΔ, hμO⟩ := hcon
  have hDO : Disjoint (R.delta ha haσ h69) (R.hOrbit ha haσ h69 ω) := by
    rw [Set.disjoint_left]
    intro ν hνD hνO
    apply hωΔ
    have e1 := R.hOrbit_of_mem ha haσ h69 (ω := some (0, 0, 1)) hνD
    have e2 := R.hOrbit_of_mem ha haσ h69 hνO
    have : ω ∈ R.hOrbit ha haσ h69 (some (0, 0, 1)) := by
      rw [← e1, e2]; exact R.mem_hOrbit_self ha haσ h69 ω
    exact this
  have hFD : Disjoint (R.fixSet R.Jg) (R.delta ha haσ h69) := by
    rw [Set.disjoint_left]
    intro ν hνF hνD
    exact R.not_fix_J_of_mem_hOrbit ha haσ h69 R.act_001_J hνD hνF
  have hFO : Disjoint (R.fixSet R.Jg) (R.hOrbit ha haσ h69 ω) := by
    rw [Set.disjoint_left]
    intro ν hνF hνO
    exact R.not_fix_J_of_mem_hOrbit ha haσ h69 hω hνO hνF
  have hcardD : Nat.card (R.hSub ha haσ h69) ≤ 2 * (R.delta ha haσ h69).ncard :=
    R.card_hOrbit ha haσ h69 R.act_001_J
  have hcardO := R.card_hOrbit ha haσ h69 hω
  have hH := R.card_hSub' ha haσ h69
  have hF := R.ncard_fixSet_J
  have hμ' : μ ∉ R.fixSet R.Jg ∪ R.delta ha haσ h69 ∪ R.hOrbit ha haσ h69 ω := by
    simp only [Set.mem_union, not_or]
    exact ⟨⟨hμ, hμΔ⟩, hμO⟩
  have hcard := Set.ncard_le_ncard (Set.subset_univ
    (insert μ (R.fixSet R.Jg ∪ R.delta ha haσ h69 ∪ R.hOrbit ha haσ h69 ω))) (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem hμ' (Set.toFinite _), Set.ncard_univ, card_omega,
    Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hFO, hDO⟩) (Set.toFinite _)
      (Set.toFinite _),
    Set.ncard_union_eq hFD (Set.toFinite _) (Set.toFinite _), hF] at hcard
  generalize Nat.card (R.hSub ha haσ h69) = h at hcardD hcardO hH
  generalize Nat.card k ^ 3 = Q at hH hcard
  omega

theorem fixSet_K_subset_delta :
    R.fixSet R.K ⊆ R.delta ha haσ h69 := by
  intro ω hωK
  by_contra hωΔ
  have hω : R.act ω R.Jg ≠ ω := fun hJ => R.not_mem_fixSet_K_of_J hJ hωK
  have hKH := R.K_mem_hSub ha haσ h69
  have hJKH : R.Jg * R.K ∈ R.hSub ha haσ h69 :=
    (R.hSub ha haσ h69).mul_mem (R.Jg_mem_hSub ha haσ h69) hKH
  have key : ∀ c ∈ R.hSub ha haσ h69, R.act (some (1, 1, d)) (c⁻¹ * R.K * c) =
      some (1, 1, d) → False := by
    intro c hc hfix
    obtain ⟨s₀, hs₀⟩ := R.fix_comm_J_eq R.act_YT_J
    have hcH : c⁻¹ * R.K * c ∈ R.hSub ha haσ h69 :=
      (R.hSub ha haσ h69).mul_mem ((R.hSub ha haσ h69).mul_mem
        ((R.hSub ha haσ h69).inv_mem hc) hKH) hc
    have hne1 : c⁻¹ * R.K * c ≠ 1 := by
      intro h1; apply R.K_ne_one
      calc R.K = c * (c⁻¹ * R.K * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have e1 := (hs₀ _ hfix (R.hSet_comm_J hcH)).resolve_left hne1
    have e2 := (hs₀ _ R.JK_fixes_b (R.hSet_comm_J hJKH)).resolve_left R.JK_ne_one
    exact R.K_not_conj_JK (R.hSet_comm_J hc) (e1.trans e2.symm)
  rcases R.mem_delta_or_orbit ha haσ h69 hω hωΔ R.act_YT_J with hYT | hYT
  ·
    obtain ⟨c₂, hc₂, he₂⟩ := hYT
    have hc₁ := R.ι_mem_hSub ha haσ h69 (pp0_mem_bSet σ (-1))
    have he₁ : R.act (some (0, 0, 1)) (R.ι (pp σ 0 (-1) 0)) = some (0, -1, 1) := by
      rw [act_ι]
      simp only [ppv, pp]
      rw [ThompsonN.mul_P]
      simp [coords]
    obtain ⟨c, hcdef⟩ : ∃ c, c = (R.ι (pp σ 0 (-1) 0))⁻¹ * c₂ := ⟨_, rfl⟩
    have hc : c ∈ R.hSub ha haσ h69 := by
      rw [hcdef]
      exact (R.hSub ha haσ h69).mul_mem ((R.hSub ha haσ h69).inv_mem hc₁) hc₂
    apply key c hc
    have hmove : R.act (some (0, -1, 1)) c = some (1, 1, d) := by
      rw [← he₁, ← act_mul, hcdef, show R.ι (pp σ 0 (-1) 0) * ((R.ι (pp σ 0 (-1) 0))⁻¹ * c₂) =
        c₂ by group]
      exact he₂
    rw [← hmove, ← act_mul, show c * (c⁻¹ * R.K * c) = R.K * c by group, act_mul, R.K_fixes_a]
  · obtain ⟨c, hc, hce⟩ := hYT
    apply key c hc
    simp only at hce
    rw [← hce, ← act_mul, show c * (c⁻¹ * R.K * c) = R.K * c by group, act_mul, hωK]

end Orbits

end CFSG.Walter.Ree.T2.RType
