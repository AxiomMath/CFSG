module

public import CFSG.Quasithin.Vol2.Ch5ModulesFFA5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin Equiv

theorem eq_alternatingGroup_of_card_sixty {P : Subgroup (Perm (Fin 5))} (hP : Nat.card P = 60) :
    P = alternatingGroup (Fin 5) := by
  have h120 : Nat.card (Perm (Fin 5)) = 120 := by rw [Nat.card_perm, Nat.card_fin]; decide
  have hidx : P.index = 2 := by
    have h1 := P.card_mul_index
    rw [hP, h120] at h1
    omega
  have hle : alternatingGroup (Fin 5) ≤ P := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    have h3 : σ ^ 3 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hσ.orderOf] at this
    have h4 : σ = (σ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rw [h4]
    exact Subgroup.sq_mem_of_index_two hidx _
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [hP, SteinbergCB.nat_card_alternating_five])).symm

variable {V : Type} [CommGroup V]

theorem alternatingNatural_of_symmetricNatural_five {X K : Subgroup (MulAut V)}
    {U Z : Subgroup V} (h : SymmetricNatural X U Z 5) (hKX : K ≤ X) (hK60 : Nat.card K = 60) :
    AlternatingNatural K U Z 5 := by
  obtain ⟨π, hπ⟩ := h
  let π₀ : Perm (Fin 5) →* ↥X := π
  have hπi : Function.Injective π₀ :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful le_rfl) hπ
  set P : Subgroup (Perm (Fin 5)) := (K.subgroupOf X).comap π₀ with hP
  have hPcard : Nat.card P = 60 := by
    have hmap : P.map π₀ = K.subgroupOf X := Subgroup.map_comap_eq_self_of_surjective hπ.1 _
    rw [← hK60, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv, ← hmap,
      Subgroup.card_map_of_injective hπi]
  have hPA := eq_alternatingGroup_of_card_sixty hPcard
  have hmem : ∀ σ : ↥(alternatingGroup (Fin 5)), ((π₀ σ : ↥X) : MulAut V) ∈ K := by
    intro σ
    have hσ : (σ : Perm (Fin 5)) ∈ P := by
      rw [hPA]
      exact σ.2
    exact hσ
  let π' : ↥(alternatingGroup (Fin 5)) →* ↥K :=
    { toFun := fun σ => ⟨((π₀ σ : ↥X) : MulAut V), hmem σ⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  obtain ⟨hs, hZU, hks, hU, hZ, hsec, hker, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨π', ⟨?_, hZU, hks, fun k u hu => hU ⟨k, hKX k.2⟩ u hu,
    fun k z hz => hZ ⟨k, hKX k.2⟩ z hz,
    fun γ m hm => hsec (γ : ↥(alternatingGroup (Fin 5))).1 m hm,
    fun γ m hm => hker (γ : ↥(alternatingGroup (Fin 5))).1 m hm, β, hβs, hβk,
    fun γ u m hu hm hum => hβe (γ : ↥(alternatingGroup (Fin 5))).1 u m hu hm hum⟩⟩
  rintro ⟨k, hk⟩
  obtain ⟨σ, hσ⟩ := hs ⟨k, hKX hk⟩
  have hσP : (σ : Perm (Fin 5)) ∈ P := by
    show π₀ σ ∈ K.subgroupOf X
    rw [show π₀ σ = π σ from rfl, hσ, Subgroup.mem_subgroupOf]
    exact hk
  rw [hPA] at hσP
  exact ⟨⟨σ, hσP⟩, Subtype.ext
    (show ((π σ : ↥X) : MulAut V) = k from congrArg Subtype.val hσ)⟩

theorem mem_iff_sign_eq_one_of_symmetricNatural {X K : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : Perm (Fin 5) →* ↥X} (hπ : (FFModel.symDn 5).RealizesVia X U Z π) (hKX : K ≤ X)
    (hK60 : Nat.card K = 60) (σ : Perm (Fin 5)) :
    ((π σ : ↥X) : MulAut V) ∈ K ↔ Perm.sign σ = 1 := by
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful le_rfl) hπ
  set P : Subgroup (Perm (Fin 5)) := (K.subgroupOf X).comap π with hP
  have hPcard : Nat.card P = 60 := by
    have hmap : P.map π = K.subgroupOf X := Subgroup.map_comap_eq_self_of_surjective hπ.1 _
    rw [← hK60, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv, ← hmap,
      Subgroup.card_map_of_injective hπi]
  have hPA := eq_alternatingGroup_of_card_sixty hPcard
  rw [← Perm.mem_alternatingGroup, ← hPA]
  exact Iff.rfl

@[expose] def IsPair5 (x : Fin 5 → ZMod 2) : Prop :=
  (Finset.univ.filter fun i => x i ≠ 0).card = 2

instance : DecidablePred IsPair5 := fun x =>
  inferInstanceAs (Decidable ((Finset.univ.filter fun i => x i ≠ 0).card = 2))

@[expose] def pair01 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

theorem d5_pair_of_ne_zero : ∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → x ≠ 0 →
    IsPair5 x ∨ ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ IsPair5 (fun i => x i + x (σ⁻¹ i)) := by
  decide +kernel

theorem d5_pair_transitive : ∀ y : Fin 5 → ZMod 2, IsPair5 y →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ ∀ i, y i = pair01 (σ⁻¹ i) := by
  decide +kernel

theorem d5_sum_pairs : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 →
    y = 0 ∨ IsPair5 y ∨ ∃ p q : Fin 5 → ZMod 2, IsPair5 p ∧ IsPair5 q ∧ y = p + q := by
  decide +kernel

theorem exists_d5_coords {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥K} (h : (FFModel.altDn 5).RealizesVia K U Z π) :
    ∃ vec : ↥U → Fin 5 → ZMod 2, (∀ u w, vec (u * w) = vec u + vec w) ∧
      (∀ u, vec u = 0 ↔ (u : V) ∈ Z) ∧ (∀ u, ∑ i, vec u i = 0) ∧
      (∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → ∃ u, vec u = x) ∧
      ∀ (σ : ↥(alternatingGroup (Fin 5))) (u : ↥U)
        (hu : ((π σ : ↥K) : MulAut V) (u : V) ∈ U),
        vec ⟨_, hu⟩ = fun i => vec u (((σ : Perm (Fin 5))⁻¹) i) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let rep : ↥U → ↥(FFModel.altDn 5).sec := fun u => d5Rep (β u)
  have hrep : ∀ u, (QuotientGroup.mk (rep u) : ↥(FFModel.altDn 5).sec ⧸ _) = β u :=
    fun u => mk_d5Rep _
  have hmk : ∀ a b : ↥(FFModel.altDn 5).sec,
      (QuotientGroup.mk a : ↥(FFModel.altDn 5).sec ⧸ _) = QuotientGroup.mk b → a = b :=
    fun a b hab => A7.altDn_five_mk_injective hab
  have hrep_one : ∀ u, rep u = 1 ↔ (u : V) ∈ Z := by
    intro u
    rw [← hβk u, ← hrep]
    constructor
    · intro h1
      rw [h1]
      rfl
    · intro h1
      exact hmk _ _ (h1.trans rfl)
  refine ⟨fun u => d5Vec (rep u), ?_, ?_, fun u => (rep u).2, ?_, ?_⟩
  · intro u w
    have h1 : rep (u * w) = rep u * rep w := by
      apply hmk
      rw [hrep, QuotientGroup.mk_mul, hrep, hrep]
      exact map_mul β u w
    show d5Vec (rep (u * w)) = _
    rw [h1]
    rfl
  · intro u
    rw [← hrep_one u]
    constructor
    · intro h0
      apply d5Vec_injective
      exact h0
    · intro h1
      show d5Vec (rep u) = 0
      rw [h1]
      rfl
  · intro x hx
    set m : ↥(FFModel.altDn 5).sec := ⟨Multiplicative.ofAdd x, hx⟩ with hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    refine ⟨u, ?_⟩
    have h1 : rep u = m := hmk _ _ (by rw [hrep]; exact hu)
    show d5Vec (rep u) = x
    rw [h1]
    rfl
  · intro σ u hu
    have hm' : (FFModel.altDn 5).act σ ((rep u : ↥(FFModel.altDn 5).sec) :
        (FFModel.altDn 5).Amb) ∈ (FFModel.altDn 5).sec := G6.permAct_mem_coreMod _ (rep u).2
    have key := hβe σ u (rep u) hu hm' (hrep u).symm
    have h1 : rep ⟨_, hu⟩ =
        ⟨(FFModel.altDn 5).act σ ((rep u : ↥(FFModel.altDn 5).sec) :
          (FFModel.altDn 5).Amb), hm'⟩ := hmk _ _ (by rw [hrep]; exact key)
    show d5Vec (rep ⟨_, hu⟩) = _
    rw [h1]
    rfl

theorem exists_s5_coords {X : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : Perm (Fin 5) →* ↥X} (h : (FFModel.symDn 5).RealizesVia X U Z π) :
    ∃ vec : ↥U → Fin 5 → ZMod 2, (∀ u w, vec (u * w) = vec u + vec w) ∧
      (∀ u, vec u = 0 ↔ (u : V) ∈ Z) ∧ (∀ u, ∑ i, vec u i = 0) ∧
      (∀ x : Fin 5 → ZMod 2, ∑ i, x i = 0 → ∃ u, vec u = x) ∧
      ∀ (σ : Perm (Fin 5)) (u : ↥U) (hu : ((π σ : ↥X) : MulAut V) (u : V) ∈ U),
        vec ⟨_, hu⟩ = fun i => vec u (σ⁻¹ i) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let rep : ↥U → ↥(FFModel.altDn 5).sec := fun u => d5Rep (β u)
  have hrep : ∀ u, (QuotientGroup.mk (rep u) : ↥(FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = β u :=
    fun u => mk_d5Rep _
  have hmk : ∀ a b : ↥(FFModel.altDn 5).sec,
      (QuotientGroup.mk a : ↥(FFModel.altDn 5).sec ⧸ _) = QuotientGroup.mk b → a = b :=
    fun a b hab => A7.altDn_five_mk_injective hab
  have hrep_one : ∀ u, rep u = 1 ↔ (u : V) ∈ Z := by
    intro u
    rw [← hβk u, ← hrep]
    constructor
    · intro h1
      rw [h1]
      rfl
    · intro h1
      exact hmk _ _ (h1.trans rfl)
  refine ⟨fun u => d5Vec (rep u), ?_, ?_, fun u => (rep u).2, ?_, ?_⟩
  · intro u w
    have h1 : rep (u * w) = rep u * rep w := by
      apply hmk
      rw [hrep, QuotientGroup.mk_mul, hrep, hrep]
      exact map_mul β u w
    show d5Vec (rep (u * w)) = _
    rw [h1]
    rfl
  · intro u
    rw [← hrep_one u]
    constructor
    · intro h0
      apply d5Vec_injective
      exact h0
    · intro h1
      show d5Vec (rep u) = 0
      rw [h1]
      rfl
  · intro x hx
    set m : ↥(FFModel.altDn 5).sec := ⟨Multiplicative.ofAdd x, hx⟩ with hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
    refine ⟨u, ?_⟩
    have h1 : rep u = m := hmk _ _ (by rw [hrep]; exact hu)
    show d5Vec (rep u) = x
    rw [h1]
    rfl
  · intro σ u hu
    have hm' : (FFModel.symDn 5).act σ (rep u).1 ∈ (FFModel.symDn 5).sec :=
      G6.permAct_mem_coreMod _ (rep u).2
    have key := hβe σ u (rep u) hu hm' (hrep u).symm
    have h1 : rep ⟨_, hu⟩ = ⟨(FFModel.symDn 5).act σ (rep u).1, hm'⟩ :=
      hmk _ _ (by rw [hrep]; exact key)
    show d5Vec (rep ⟨_, hu⟩) = _
    rw [h1]
    rfl

theorem eq_or_eq_of_alternatingNatural_five {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : AlternatingNatural K U Z 5) {Y : Subgroup V} (hY : ∀ k ∈ K, ∀ y ∈ Y, k y ∈ Y)
    (hZY : Z ≤ Y) (hYU : Y ≤ U) : Y = Z ∨ Y = U := by
  obtain ⟨π, hπ⟩ := h
  have hUinv : ∀ k : ↥K, ∀ u ∈ U, (k : MulAut V) u ∈ U := hπ.2.2.2.1
  obtain ⟨vec, hvec_mul, hvec_ker, hvec_sum, -, hvec_act⟩ := exists_d5_coords hπ
  have hvec_one : vec 1 = 0 := (hvec_ker 1).2 Z.one_mem
  by_cases hYZ : Y ≤ Z
  · exact Or.inl (le_antisymm hYZ hZY)
  right
  obtain ⟨y, hyY, hyZ⟩ := Set.not_subset.mp hYZ
  let inY : (Fin 5 → ZMod 2) → Prop := fun x => ∃ w : ↥U, (w : V) ∈ Y ∧ vec w = x
  have hmulY : ∀ x x', inY x → inY x' → inY (x + x') := by
    rintro x x' ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
    exact ⟨w * w', Y.mul_mem hw hw', hvec_mul w w'⟩
  have hactY : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ x, inY x →
      inY (fun i => x (σ⁻¹ i)) := by
    rintro σ hσ x ⟨w, hw, rfl⟩
    set σ' : ↥(alternatingGroup (Fin 5)) := ⟨σ, Perm.mem_alternatingGroup.mpr hσ⟩
    exact ⟨⟨_, hUinv (π σ') w w.2⟩, hY _ (π σ').2 _ hw, hvec_act σ' w (hUinv (π σ') w w.2)⟩
  have hx₀ : inY (vec ⟨y, hYU hyY⟩) := ⟨⟨y, hYU hyY⟩, hyY, rfl⟩
  have hx₀ne : vec ⟨y, hYU hyY⟩ ≠ 0 := fun h0 => hyZ ((hvec_ker _).1 h0)
  obtain ⟨p₁, hp₁Y, hp₁⟩ : ∃ p, inY p ∧ IsPair5 p := by
    rcases d5_pair_of_ne_zero _ (hvec_sum _) hx₀ne with hp | ⟨σ, hσ, hp⟩
    · exact ⟨_, hx₀, hp⟩
    · exact ⟨_, hmulY _ _ hx₀ (hactY σ hσ _ hx₀), hp⟩
  have hpairs : ∀ p, IsPair5 p → inY p := by
    intro p hp
    obtain ⟨σ₁, hσ₁, hσ₁e⟩ := d5_pair_transitive p₁ hp₁
    obtain ⟨σ₂, hσ₂, hσ₂e⟩ := d5_pair_transitive p hp
    have hτ : Perm.sign (σ₂ * σ₁⁻¹) = 1 := by
      rw [map_mul, map_inv, hσ₁, hσ₂, inv_one, mul_one]
    have h1 := hactY _ hτ _ hp₁Y
    have h2 : (fun i => p₁ ((σ₂ * σ₁⁻¹)⁻¹ i)) = p := by
      funext i
      rw [hσ₂e i, hσ₁e]
      congr 1
      simp [mul_inv_rev]
    rwa [h2] at h1
  refine le_antisymm hYU fun u hu => ?_
  have hu' : inY (vec ⟨u, hu⟩) := by
    rcases d5_sum_pairs _ (hvec_sum ⟨u, hu⟩) with h0 | hp | ⟨p, q, hp, hq, hpq⟩
    · exact ⟨1, Y.one_mem, by rw [hvec_one, h0]⟩
    · exact hpairs _ hp
    · rw [hpq]
      exact hmulY _ _ (hpairs p hp) (hpairs q hq)
  obtain ⟨w, hwY, hwv⟩ := hu'
  have h1 : vec (⟨u, hu⟩ * w⁻¹) = 0 := by
    have h3 := hvec_mul (⟨u, hu⟩ * w⁻¹) w
    rw [inv_mul_cancel_right, hwv] at h3
    exact right_eq_add.mp h3
  have h2 : ((⟨u, hu⟩ * w⁻¹ : ↥U) : V) ∈ Y := hZY ((hvec_ker _).1 h1)
  have h3 : u = ((⟨u, hu⟩ * w⁻¹ : ↥U) : V) * w := by simp
  rw [h3]
  exact Y.mul_mem h2 hwY

theorem isIrrSec_of_alternatingNatural_five [Finite V] {K : Subgroup (MulAut V)}
    (h : AlternatingNatural K ⊤ ⊥ 5) : XMod.IsIrrSec ↥K (⊥ : Subgroup V) ⊤ := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨vec, -, hvec_ker, -, hvec_surj, -⟩ := exists_d5_coords hπ
  obtain ⟨v₀, hv₀⟩ := hvec_surj pair01 (by decide)
  have hv₀1 : (v₀ : V) ≠ 1 := fun h1 => by
    have h0 := (hvec_ker v₀).2 (Subgroup.mem_bot.mpr h1)
    rw [hv₀] at h0
    exact absurd (congrFun h0 0) (by decide)
  refine ⟨bot_lt_iff_ne_bot.mpr fun hb => hv₀1 ?_, fun J hJ hJ0 _ =>
    eq_or_eq_of_alternatingNatural_five ⟨π, hπ⟩ (fun k hk w hw => hJ ⟨k, hk⟩ w hw) hJ0 le_top⟩
  exact (Subgroup.eq_bot_iff_forall _).1 hb _ (Subgroup.mem_top _)

@[expose] def pair04 : Fin 5 → ZMod 2 := ![1, 0, 0, 0, 1]

theorem d5_average : ∀ m : Fin 5 → ZMod 2, ∑ i, m i = 0 → ∀ i : Fin 5,
    ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin 5) => Perm.sign σ = 1),
      m (σ 0) * pair04 (σ⁻¹ i) = m i := by
  decide +kernel

theorem d5_comm_odd : ∀ τ : Perm (Fin 5), τ * τ = 1 → Perm.sign τ ≠ 1 →
    ∀ m : Fin 5 → ZMod 2, (fun i => m (τ⁻¹ i) + m i) = 0 ∨
      (fun i => m (τ⁻¹ i) + m i) = (fun i => if τ i = i then (0 : ZMod 2) else 1) := by
  decide +kernel

theorem s5_elemAbelian_rank : ∀ γ : Perm (Fin 5), γ * γ = 1 → ∀ δ : Perm (Fin 5),
    δ * δ = 1 → γ * δ = δ * γ → ∀ ε : Perm (Fin 5), ε * ε = 1 → γ * ε = ε * γ →
    δ * ε = ε * δ → γ = 1 ∨ δ = 1 ∨ δ = γ ∨ ε = 1 ∨ ε = γ ∨ ε = δ ∨ ε = γ * δ := by
  decide +kernel

theorem card_of_symmetricNatural_five [Finite V] {X : Subgroup (MulAut V)}
    (h : SymmetricNatural X ⊤ ⊥ 5) : Nat.card V = 16 := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  have h1 : Nat.card (↥(FFModel.altDn 5).sec ⧸
      (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec) = 16 := by
    rw [Nat.card_congr d5Rep]
    exact Explicit.card_coreMod (n := 5) (by norm_num)
  rw [← Subgroup.card_top (G := V), Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)]
  exact h1

end CFSG.Quasithin.H13
