module

public import CFSG.Quasithin.EmptyFaithful.S153OrthStruct
public import CFSG.Quasithin.EmptyFaithful.S1417Fix

public section

open CFSG.QuasithinUnique CFSG.Quasithin.S1417

namespace CFSG.Quasithin

section General

variable {W : Type*} [CommGroup W]

theorem commV_map_conjAut (g : MulAut W) (L : Subgroup (MulAut W)) :
    (commV L).map g.toMonoidHom = commV (B1.conjAut g L) := by
  apply le_antisymm
  · rw [commV, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * x * g⁻¹, ?_, g v, ?_⟩
    · rw [B1.mem_conjAut]
      simpa [mul_assoc] using hx
    · simp [MulAut.mul_apply]
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x', hx', v', rfl⟩
    rw [B1.mem_conjAut] at hx'
    refine ⟨(g⁻¹ * x' * g) (g⁻¹ v') * (g⁻¹ v')⁻¹, Subgroup.subset_closure ⟨_, hx', g⁻¹ v', rfl⟩, ?_⟩
    simp [MulAut.mul_apply]

theorem coset_of_relIndex_two {G : Type*} [Group G] {H K : Subgroup G} (h : H.relIndex K = 2)
    {x τ : G} (hx : x ∈ K) (hτ : τ ∈ K) (hτH : τ ∉ H) : x ∈ H ∨ x * τ⁻¹ ∈ H := by
  obtain ⟨a, haK, ha⟩ := Subgroup.relIndex_eq_two_iff.1 h
  by_cases hxH : x ∈ H
  · exact Or.inl hxH
  · right
    have hxa : x * a ∈ H := by
      rcases ha x hx with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h1 hxH
    have hτa : τ * a ∈ H := by
      rcases ha τ hτ with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1
      · exact absurd h1 hτH
    have e : x * τ⁻¹ = (x * a) * (τ * a)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hxa (Subgroup.inv_mem _ hτa)

end General

namespace OfourStruct

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}

theorem L₁_le (h : OfourStruct X L₁ L₂ t) : L₁ ≤ X := by
  rw [h.eq]
  exact le_sup_left.trans le_sup_left

theorem L₂_le (h : OfourStruct X L₁ L₂ t) : L₂ ≤ X := by
  rw [h.eq]
  exact le_sup_right.trans le_sup_left

theorem t_mem (h : OfourStruct X L₁ L₂ t) : t ∈ X := by
  rw [h.eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem perm (h : OfourStruct X L₁ L₂ t) : ∀ g ∈ X,
    (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁) := by
  let Pm : Subgroup (MulAut W) :=
    { carrier := {g | (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
        (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁)}
      one_mem' := by
        left
        constructor
        · ext x; simp [B1.mem_conjAut]
        · ext x; simp [B1.mem_conjAut]
      mul_mem' := by
        rintro a b (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩) (⟨hb1, hb2⟩ | ⟨hb1, hb2⟩)
        · left
          exact ⟨by rw [conjAut_mul, hb1, ha1], by rw [conjAut_mul, hb2, ha2]⟩
        · right
          exact ⟨by rw [conjAut_mul, hb1, ha2], by rw [conjAut_mul, hb2, ha1]⟩
        · right
          exact ⟨by rw [conjAut_mul, hb1, ha1], by rw [conjAut_mul, hb2, ha2]⟩
        · left
          exact ⟨by rw [conjAut_mul, hb1, ha2], by rw [conjAut_mul, hb2, ha1]⟩
      inv_mem' := by
        rintro a (⟨ha1, ha2⟩ | ⟨ha1, ha2⟩)
        · left
          exact ⟨calc B1.conjAut a⁻¹ L₁ = B1.conjAut a⁻¹ (B1.conjAut a L₁) := by rw [ha1]
              _ = L₁ := B1.conjAut_inv_conjAut a L₁,
            calc B1.conjAut a⁻¹ L₂ = B1.conjAut a⁻¹ (B1.conjAut a L₂) := by rw [ha2]
              _ = L₂ := B1.conjAut_inv_conjAut a L₂⟩
        · right
          exact ⟨calc B1.conjAut a⁻¹ L₁ = B1.conjAut a⁻¹ (B1.conjAut a L₂) := by rw [ha2]
              _ = L₂ := B1.conjAut_inv_conjAut a L₂,
            calc B1.conjAut a⁻¹ L₂ = B1.conjAut a⁻¹ (B1.conjAut a L₁) := by rw [ha1]
              _ = L₁ := B1.conjAut_inv_conjAut a L₁⟩ }
  have hL₁ : L₁ ≤ Pm := by
    intro a ha
    left
    exact ⟨conjAut_eq_of_mem ha, conjAut_eq_of_commute fun b hb => h.comm a ha b hb⟩
  have hL₂ : L₂ ≤ Pm := by
    intro a ha
    left
    exact ⟨conjAut_eq_of_commute fun b hb => (h.comm b hb a ha).symm, conjAut_eq_of_mem ha⟩
  have ht : t ∈ Pm := Or.inr ⟨h.conj₁, h.conj₂⟩
  have hX : X ≤ Pm := by
    rw [h.eq]
    exact sup_le (sup_le hL₁ hL₂) ((Subgroup.zpowers_le).2 ht)
  exact fun g hg => hX hg

theorem card_L₁ (h : OfourStruct X L₁ L₂ t) : Nat.card L₁ = 6 := (card_of_actsAsNaturalL2 h.nat₁).1

theorem card_L₂ (h : OfourStruct X L₁ L₂ t) : Nat.card L₂ = 6 := (card_of_actsAsNaturalL2 h.nat₂).1

theorem card_U₁ (h : OfourStruct X L₁ L₂ t) : Nat.card (commV L₁) = 4 :=
  (card_of_actsAsNaturalL2 h.nat₁).2

theorem card_sup (h : OfourStruct X L₁ L₂ t) : Nat.card ↥(L₁ ⊔ L₂) = 36 := by
  have := B2F.card_sup_mul_card_inf_of_commute h.comm
  rw [h.Linf, Subgroup.card_bot, mul_one, h.card_L₁, h.card_L₂] at this
  omega

theorem L₁_ne_L₂ (h : OfourStruct X L₁ L₂ t) : L₁ ≠ L₂ := by
  intro heq
  have h1 := h.Linf
  rw [← heq, inf_idem] at h1
  have h2 := h.card_L₁
  rw [h1, Subgroup.card_bot] at h2
  omega

theorem sup_le_normalizer_L₁ (h : OfourStruct X L₁ L₂ t) :
    L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  exact Subgroup.centralizer_le_normalizer (s := (L₁ : Set (MulAut W)))
    (Subgroup.mem_centralizer_iff.mpr fun a ha => h.comm a ha b hb)

theorem sup_le_normalizer_L₂ (h : OfourStruct X L₁ L₂ t) :
    L₁ ⊔ L₂ ≤ Subgroup.normalizer (L₂ : Set (MulAut W)) := by
  refine sup_le (fun a ha => ?_) Subgroup.le_normalizer
  exact Subgroup.centralizer_le_normalizer (s := (L₂ : Set (MulAut W)))
    (Subgroup.mem_centralizer_iff.mpr fun b hb => (h.comm a ha b hb).symm)

theorem t_not_mem_sup (h : OfourStruct X L₁ L₂ t) : t ∉ L₁ ⊔ L₂ := by
  intro ht
  have h1 : B1.conjAut t L₁ = L₁ :=
    conjAut_eq_iff_mem_normalizer.mpr (h.sup_le_normalizer_L₁ ht)
  exact h.L₁_ne_L₂ (h1.symm.trans h.conj₁)

theorem normalizer_sup (h : OfourStruct X L₁ L₂ t) :
    X ≤ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.tsq
  have hmap : ∀ n ∈ L₁ ⊔ L₂, t * n * t⁻¹ ∈ L₁ ⊔ L₂ := by
    have hle : L₁ ⊔ L₂ ≤ (L₁ ⊔ L₂).comap (MulAut.conj t).toMonoidHom := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · have : t * l * t⁻¹ ∈ B1.conjAut t L₁ := by
          rw [B1.mem_conjAut]; simpa [mul_assoc] using hl
        rw [h.conj₁] at this
        exact Subgroup.mem_sup_right this
      · have : t * l * t⁻¹ ∈ B1.conjAut t L₂ := by
          rw [B1.mem_conjAut]; simpa [mul_assoc] using hl
        rw [h.conj₂] at this
        exact Subgroup.mem_sup_left this
    intro n hn
    exact hle hn
  have ht : t ∈ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hmap n hn, fun hn => ?_⟩
    have := hmap _ hn
    have e : t * (t * n * t⁻¹) * t⁻¹ = n := by
      rw [htinv]
      calc t * (t * n * t) * t = (t * t) * n * (t * t) := by simp only [mul_assoc]
        _ = n := by rw [h.tsq]; simp
    rwa [e] at this
  rw [h.eq]
  exact sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 ht)

theorem mem_or_mul_t_mem (h : OfourStruct X L₁ L₂ t) {b : MulAut W} (hb : b ∈ X) :
    b ∈ L₁ ⊔ L₂ ∨ b * t ∈ L₁ ⊔ L₂ := by
  have hH : Subgroup.zpowers t ≤
      Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) :=
    ((Subgroup.zpowers_le).2 h.t_mem).trans h.normalizer_sup
  have hb' : b ∈ ((L₁ ⊔ L₂) ⊔ Subgroup.zpowers t : Subgroup (MulAut W)) := by
    rw [← h.eq]; exact hb
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hH] at hb'
  obtain ⟨n, hn, u, hu, rfl⟩ := Set.mem_mul.mp hb'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h.tsq
  rw [zpow_eq_zpow_emod k ht2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [hk, zpow_zero, mul_one]
    exact hn
  · right
    rw [hk, zpow_one, mul_assoc, h.tsq, mul_one]
    exact hn

theorem relIndex_sup (h : OfourStruct X L₁ L₂ t) : (L₁ ⊔ L₂).relIndex X = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, h.t_mem, fun b hb => ?_⟩
  by_cases hbN : b ∈ L₁ ⊔ L₂
  · right
    refine ⟨hbN, fun hbt => h.t_not_mem_sup ?_⟩
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hbN) hbt
    simpa using this
  · left
    exact ⟨(h.mem_or_mul_t_mem hb).resolve_left hbN, hbN⟩

theorem le_X_sup (h : OfourStruct X L₁ L₂ t) : L₁ ⊔ L₂ ≤ X := sup_le h.L₁_le h.L₂_le

theorem card_X (h : OfourStruct X L₁ L₂ t) : Nat.card X = 72 := by
  have h1 := Subgroup.relIndex_mul_card (L₁ ⊔ L₂) X
  rw [inf_eq_left.mpr h.le_X_sup, h.relIndex_sup, h.card_sup] at h1
  omega

theorem card_T (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X) :
    Nat.card T' = 8 := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [h.card_X]; omega)
  have hfinT : Finite T' := Finite.of_injective (Subgroup.inclusion hT.1)
    (Subgroup.inclusion_injective _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT.2.1
  have h1 := Subgroup.relIndex_mul_card T' X
  rw [inf_eq_left.mpr hT.1, hk, h.card_X] at h1
  have hodd : ¬ 2 ∣ T'.relIndex X := hT.2.2
  rcases k with _ | _ | _ | _ | k
  · exfalso
    apply hodd
    have : T'.relIndex X = 72 := by simpa using h1
    rw [this]
    norm_num
  · exfalso
    apply hodd
    have : T'.relIndex X = 36 := by
      have : T'.relIndex X * 2 = 72 := by simpa using h1
      omega
    rw [this]
    norm_num
  · exfalso
    apply hodd
    have : T'.relIndex X = 18 := by
      have : T'.relIndex X * 4 = 72 := by simpa using h1
      omega
    rw [this]
    norm_num
  · rw [hk]
    norm_num
  · exfalso
    have : 16 ∣ 72 := ⟨T'.relIndex X * 2 ^ k, by rw [← h1]; ring⟩
    omega

theorem isSylow_sup [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) : IsSylowTwoOf (T' ⊓ (L₁ ⊔ L₂)) (L₁ ⊔ L₂) :=
  A4.isSylowTwoOf_inf_normal hT h.le_X_sup h.normalizer_sup

theorem card_S [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) :
    Nat.card ↥(T' ⊓ (L₁ ⊔ L₂)) = 4 := by
  have hfin : Finite ↥(L₁ ⊔ L₂) := Nat.finite_of_card_ne_zero (by rw [h.card_sup]; omega)
  exact card_eq_four_of_isSylowTwoOf (h.isSylow_sup hT) h.card_sup

theorem relIndex_S [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) : (T' ⊓ (L₁ ⊔ L₂)).relIndex T' = 2 := by
  have h1 := Subgroup.relIndex_mul_card (T' ⊓ (L₁ ⊔ L₂)) T'
  rw [inf_eq_left.mpr (inf_le_left : T' ⊓ (L₁ ⊔ L₂) ≤ T'), h.card_S hT, h.card_T hT] at h1
  omega

theorem conjAut_inf_of_mem (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    {τ : MulAut W} (hτT : τ ∈ T') (hτX : τ ∈ X) :
    B1.conjAut τ (T' ⊓ (L₁ ⊔ L₂)) = T' ⊓ (L₁ ⊔ L₂) := by
  have hnorm := Subgroup.mem_normalizer_iff.mp (h.normalizer_sup hτX)
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hτT h1) (Subgroup.inv_mem _ hτT)
      simpa [mul_assoc] using this
    · have := (hnorm (τ⁻¹ * x * τ)).mp h2
      simpa [mul_assoc] using this
  · rintro ⟨h1, h2⟩
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hτT) h1) hτT, ?_⟩
    rw [hnorm (τ⁻¹ * x * τ)]
    simpa [mul_assoc] using h2

theorem commV_apply_mem (g : MulAut W) (L L' : Subgroup (MulAut W)) (hg : B1.conjAut g L = L')
    {u : W} (hu : u ∈ commV L) : g u ∈ commV L' := by
  have : g u ∈ (commV L).map g.toMonoidHom := ⟨u, hu, rfl⟩
  rw [commV_map_conjAut, hg] at this
  exact this

structure SylowFacts {W : Type*} [CommGroup W] (L₁ L₂ T' : Subgroup (MulAut W))
    (s₁ s₂ τ : MulAut W) (a₁ a₂ : W) : Prop where
  sylow : SylowData (T' ⊓ (L₁ ⊔ L₂)) L₁ L₂ s₁ s₂ a₁ a₂
  s₁_sq : s₁ * s₁ = 1
  s₂_sq : s₂ * s₂ = 1
  ne : s₁ ≠ s₂
  mul_ne : s₁ * s₂ ≠ 1
  comm : s₁ * s₂ = s₂ * s₁
  τ_T : τ ∈ T'
  τ_N : τ ∉ L₁ ⊔ L₂
  conj₁ : B1.conjAut τ L₁ = L₂
  conj₂ : B1.conjAut τ L₂ = L₁
  τs₁ : τ * s₁ * τ⁻¹ = s₂
  τs₂ : τ * s₂ * τ⁻¹ = s₁
  S_eq : ∀ x, x ∈ T' ⊓ (L₁ ⊔ L₂) ↔ x = 1 ∨ x = s₁ ∨ x = s₂ ∨ x = s₁ * s₂
  τa₁ : τ a₁ = a₂
  τa₂ : τ a₂ = a₁
  a_ne : a₁ ≠ a₂
  fix : ∀ w, (∀ x ∈ T', x w = w) → w = 1 ∨ w = a₁ * a₂
  card_fix : Nat.card ↥(fixV (T' ⊓ (L₁ ⊔ L₂))) = 4

theorem exists_sylowFacts [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) :
    ∃ (s₁ s₂ τ : MulAut W) (a₁ a₂ : W), SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂ := by
  classical
  have hSyl := h.isSylow_sup hT
  have hS4 := h.card_S hT
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ := exists_sylowData hSyl h.nat₁ h.nat₂ h.comm h.Linf h.inf h.sup
  obtain ⟨τ, hτT, hτ1⟩ := exists_swap_mem_of_isSylowTwoOf hT h.t_mem
    (by rw [h.conj₁]; exact h.L₁_ne_L₂.symm) h.perm
  have hτX : τ ∈ X := hT.1 hτT
  have hτsw : B1.conjAut τ L₁ = L₂ ∧ B1.conjAut τ L₂ = L₁ :=
    (h.perm τ hτX).resolve_left fun hh => hτ1 hh.1
  have hτN : τ ∉ L₁ ⊔ L₂ := fun hτN =>
    hτ1 (conjAut_eq_iff_mem_normalizer.mpr (h.sup_le_normalizer_L₁ hτN))
  have hτS := h.conjAut_inf_of_mem hτT hτX
  have key₁ : τ * s₁ * τ⁻¹ = s₂ := by
    have hmS : τ * s₁ * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := by
      have : τ * s₁ * τ⁻¹ ∈ B1.conjAut τ (T' ⊓ (L₁ ⊔ L₂)) := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₁_mem_S
      rwa [hτS] at this
    have hmL : τ * s₁ * τ⁻¹ ∈ L₂ := by
      have : τ * s₁ * τ⁻¹ ∈ B1.conjAut τ L₁ := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₁_mem_L
      rwa [hτsw.1] at this
    rcases hd.inf₂ _ hmS hmL with h' | h'
    · exfalso
      apply hd.s₁_ne
      have h2 : s₁ = τ⁻¹ * (τ * s₁ * τ⁻¹) * τ := by group
      rw [h', mul_one, inv_mul_cancel] at h2
      exact h2
    · exact h'
  have key₂ : τ * s₂ * τ⁻¹ = s₁ := by
    have hmS : τ * s₂ * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := by
      have : τ * s₂ * τ⁻¹ ∈ B1.conjAut τ (T' ⊓ (L₁ ⊔ L₂)) := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₂_mem_S
      rwa [hτS] at this
    have hmL : τ * s₂ * τ⁻¹ ∈ L₁ := by
      have : τ * s₂ * τ⁻¹ ∈ B1.conjAut τ L₂ := by
        rw [B1.mem_conjAut]; simpa [mul_assoc] using hd.s₂_mem_L
      rwa [hτsw.2] at this
    rcases hd.inf₁ _ hmS hmL with h' | h'
    · exfalso
      apply hd.s₂_ne
      have h2 : s₂ = τ⁻¹ * (τ * s₂ * τ⁻¹) * τ := by group
      rw [h', mul_one, inv_mul_cancel] at h2
      exact h2
    · exact h'
  have hne12 : s₁ ≠ s₂ := by
    intro heq
    apply hd.s₁_ne
    have : s₁ ∈ L₁ ⊓ L₂ := ⟨hd.s₁_mem_L, heq ▸ hd.s₂_mem_L⟩
    rw [h.Linf, Subgroup.mem_bot] at this
    exact this
  have hm1 : s₁ * s₂ ≠ 1 := by
    intro h1
    apply hd.s₂_ne
    have h2 : s₂ = s₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have : s₂ ∈ L₁ ⊓ L₂ := ⟨h2 ▸ L₁.inv_mem hd.s₁_mem_L, hd.s₂_mem_L⟩
    rw [h.Linf, Subgroup.mem_bot] at this
    exact this
  have hm2 : s₁ * s₂ ≠ s₁ := fun h1 => hd.s₂_ne (mul_left_cancel (h1.trans (mul_one s₁).symm))
  have hm3 : s₁ * s₂ ≠ s₂ := fun h1 => hd.s₁_ne (mul_right_cancel (h1.trans (one_mul s₂).symm))
  have hsq₁ : s₁ * s₁ = 1 := by
    rcases hd.inf₁ (s₁ * s₁) (Subgroup.mul_mem _ hd.s₁_mem_S hd.s₁_mem_S)
      (Subgroup.mul_mem _ hd.s₁_mem_L hd.s₁_mem_L) with h1 | h1
    · exact h1
    · exact absurd (mul_left_cancel (h1.trans (mul_one s₁).symm)) hd.s₁_ne
  have hsq₂ : s₂ * s₂ = 1 := by
    rcases hd.inf₂ (s₂ * s₂) (Subgroup.mul_mem _ hd.s₂_mem_S hd.s₂_mem_S)
      (Subgroup.mul_mem _ hd.s₂_mem_L hd.s₂_mem_L) with h1 | h1
    · exact h1
    · exact absurd (mul_left_cancel (h1.trans (mul_one s₂).symm)) hd.s₂_ne
  have hS_eq : ∀ x, x ∈ T' ⊓ (L₁ ⊔ L₂) ↔ x = 1 ∨ x = s₁ ∨ x = s₂ ∨ x = s₁ * s₂ := by
    have hfinS : Finite ↥(T' ⊓ (L₁ ⊔ L₂)) := Nat.finite_of_card_ne_zero (by rw [hS4]; omega)
    have hcard : ({1, s₁, s₂, s₁ * s₂} : Finset (MulAut W)).card = 4 := by
      simp [Finset.card_insert_of_notMem, hd.s₁_ne.symm, hd.s₂_ne.symm, hm1.symm, hne12,
        hm2.symm, hm3.symm]
    have hsub : (↑({1, s₁, s₂, s₁ * s₂} : Finset (MulAut W)) : Set (MulAut W)) ⊆
        ↑(T' ⊓ (L₁ ⊔ L₂)) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact hd.s₁_mem_S
      · exact hd.s₂_mem_S
      · exact Subgroup.mul_mem _ hd.s₁_mem_S hd.s₂_mem_S
    have hS4' : ((T' ⊓ (L₁ ⊔ L₂) : Subgroup (MulAut W)) : Set (MulAut W)).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hS4
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_coe_finset, hcard, hS4']) (Set.toFinite _)
    intro x
    have := Set.ext_iff.mp heq x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, SetLike.mem_coe] at this
    exact this.symm
  have hU₁ : ∀ u ∈ commV L₁, τ u ∈ commV L₂ := fun u hu => commV_apply_mem τ L₁ L₂ hτsw.1 hu
  have hU₂ : ∀ u ∈ commV L₂, τ u ∈ commV L₁ := fun u hu => commV_apply_mem τ L₂ L₁ hτsw.2 hu
  obtain ⟨hτa₁, hτa₂⟩ := hd.swap_apply hτS hτsw.1 hτsw.2 hU₁ hU₂
  have hdisj : ∀ x, x ∈ commV L₁ → x ∈ commV L₂ → x = 1 := by
    intro x h₁ h₂
    have : x ∈ commV L₁ ⊓ commV L₂ := ⟨h₁, h₂⟩
    rw [h.inf, Subgroup.mem_bot] at this
    exact this
  have ha_ne : a₁ ≠ a₂ := fun heq => hd.a₁_ne (hdisj a₁ hd.a₁_mem (heq ▸ hd.a₂_mem))
  have hfix : ∀ w, (∀ x ∈ T', x w = w) → w = 1 ∨ w = a₁ * a₂ := by
    intro w hw
    rcases (hd.fixS w).1 (fun x hx => hw x hx.1) with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exfalso
      have := hw τ hτT
      rw [h1, hτa₁] at this
      exact ha_ne this.symm
    · exfalso
      have := hw τ hτT
      rw [h1, hτa₂] at this
      exact ha_ne this
    · exact Or.inr h1
  have hcardfix := (fixV_swap hSyl h.nat₁ h.nat₂ h.comm h.Linf h.inf h.sup
    (inf_le_left : T' ⊓ (L₁ ⊔ L₂) ≤ T') hτT hτS hτsw.1 hτsw.2 hU₁ hU₂).1
  exact ⟨s₁, s₂, τ, a₁, a₂, ⟨hd, hsq₁, hsq₂, hne12, hm1, h.comm s₁ hd.s₁_mem_L s₂ hd.s₂_mem_L,
    hτT, hτN, hτsw.1, hτsw.2, key₁, key₂, hS_eq, hτa₁, hτa₂, ha_ne, hfix, hcardfix⟩⟩

theorem sq_mem_sup' (h : OfourStruct X L₁ L₂ t) {g : MulAut W} (hg : g ∈ X) :
    g * g ∈ L₁ ⊔ L₂ :=
  sq_mem_sup h.nat₁ h.nat₂ h.comm h.inf h.sup h.perm (fun g _ => commV_map_conjAut g L₁)
    (fun g _ => commV_map_conjAut g L₂) hg

theorem odd_mem_sup (h : OfourStruct X L₁ L₂ t) {y : MulAut W} (hy : y ∈ X)
    (hodd : Odd (orderOf y)) : y ∈ L₁ ⊔ L₂ :=
  mem_of_sq_mem_of_odd (h.sq_mem_sup' hy) hodd

theorem cube_of_odd {L : Subgroup (MulAut W)} (hc : Nat.card L = 6) {l : MulAut W} (hl : l ∈ L)
    (hodd : Odd (orderOf l)) : l ^ 3 = 1 := by
  have hdvd : orderOf l ∣ 6 := by
    have h1 : orderOf (⟨l, hl⟩ : L) ∣ Nat.card L := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hc] at h1
    exact h1
  have h3 : orderOf l ∣ 3 := by
    have hcop : Nat.Coprime (orderOf l) 2 := Nat.coprime_two_right.mpr hodd
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem odd_decomp (h : OfourStruct X L₁ L₂ t) {y : MulAut W} (hy : y ∈ L₁ ⊔ L₂)
    (hodd : Odd (orderOf y)) :
    ∃ l₁ ∈ L₁, ∃ l₂ ∈ L₂, y = l₁ * l₂ ∧ l₁ ^ 3 = 1 ∧ l₂ ^ 3 = 1 := by
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute h.comm hy
  have hcomm : l₁ * l₂ = l₂ * l₁ := h.comm l₁ hl₁ l₂ hl₂
  set n := orderOf (l₁ * l₂) with hn
  have hn1 : (l₁ * l₂) ^ n = 1 := pow_orderOf_eq_one _
  have hpow : l₁ ^ n * l₂ ^ n = 1 := by
    rw [← Commute.mul_pow hcomm]
    exact hn1
  have hl₁n : l₁ ^ n = 1 := by
    have h1 : l₁ ^ n ∈ L₁ ⊓ L₂ := ⟨L₁.pow_mem hl₁ n, by
      have : l₁ ^ n = (l₂ ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact L₂.inv_mem (L₂.pow_mem hl₂ n)⟩
    rw [h.Linf, Subgroup.mem_bot] at h1
    exact h1
  have hl₂n : l₂ ^ n = 1 := by
    rw [hl₁n, one_mul] at hpow
    exact hpow
  have hodd₁ : Odd (orderOf l₁) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hl₁n)
  have hodd₂ : Odd (orderOf l₂) := Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one hl₂n)
  exact ⟨l₁, hl₁, l₂, hl₂, rfl, cube_of_odd h.card_L₁ hl₁ hodd₁, cube_of_odd h.card_L₂ hl₂ hodd₂⟩

theorem coset (h : OfourStruct X L₁ L₂ t) {x s : MulAut W} (hx : x ∈ X) (hs : s ∈ X)
    (hsN : s ∉ L₁ ⊔ L₂) : x ∈ L₁ ⊔ L₂ ∨ x * s⁻¹ ∈ L₁ ⊔ L₂ := by
  rcases h.mem_or_mul_t_mem hx with hx' | hx'
  · exact Or.inl hx'
  · right
    have hs' : s * t ∈ L₁ ⊔ L₂ := (h.mem_or_mul_t_mem hs).resolve_left hsN
    have e : x * s⁻¹ = (x * t) * (s * t)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hx' (Subgroup.inv_mem _ hs')

theorem conj_inv_cube {L : Subgroup (MulAut W)} {U : Subgroup W} (hN : ActsAsNaturalL2 L U)
    {s x : MulAut W} (hs : s ∈ L) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) (hx : x ∈ L) (hx3 : x ^ 3 = 1) :
    s * x * s⁻¹ = x⁻¹ := by
  by_cases hx1 : x = 1
  · subst hx1
    simp
  · exact conj_inv hN hs hs2 hs1 hx hx3 hx1

theorem maximal [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) {K : Subgroup (MulAut W)} (hTK : T' ≤ K) (hKX : K ≤ X) :
    K = T' ∨ K = X := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hs₁1 : s₁ ≠ 1 := hF.sylow.s₁_ne
  have hs₂1 : s₂ ≠ 1 := hF.sylow.s₂_ne
  have hs₁sq : s₁ * s₁ = 1 := hF.s₁_sq
  have hs₂sq : s₂ * s₂ = 1 := hF.s₂_sq
  have hτT : τ ∈ T' := hF.τ_T
  have hτN : τ ∉ L₁ ⊔ L₂ := hF.τ_N
  have hτ1 : B1.conjAut τ L₁ = L₂ := hF.conj₁
  have hτ2 : B1.conjAut τ L₂ = L₁ := hF.conj₂
  by_cases hKT : K = T'
  · exact Or.inl hKT
  right
  have hT8 := h.card_T hT
  have hX72 := h.card_X
  have h8K : 8 ∣ Nat.card K := hT8 ▸ Subgroup.card_dvd_of_le hTK
  have hK72 : Nat.card K ∣ 72 := hX72 ▸ Subgroup.card_dvd_of_le hKX
  obtain ⟨m, hm⟩ := h8K
  have hm9 : m ∣ 3 ^ 2 := by
    have h1 : 8 * m ∣ 8 * 9 := by rw [← hm]; exact hK72
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 8) h1
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hm9
  rcases i with _ | i
  · exfalso
    apply hKT
    exact (Subgroup.eq_of_le_of_card_ge hTK (by rw [hm, hT8]; norm_num)).symm
  have h3K : 3 ∣ Nat.card K := by
    rw [hm]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (Nat.succ_ne_zero i)) 8
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3K
  have hyK : (x : MulAut W) ∈ K := x.2
  have hy3 : orderOf (x : MulAut W) = 3 := by rw [Subgroup.orderOf_coe]; exact hx3
  set y : MulAut W := (x : MulAut W) with hy
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3
    omega
  have hycube : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyN : y ∈ L₁ ⊔ L₂ := h.odd_mem_sup (hKX hyK) (by rw [hy3]; exact ⟨1, rfl⟩)
  obtain ⟨l₁, hl₁, l₂, hl₂, hyeq, hl₁3, hl₂3⟩ := h.odd_decomp hyN (by rw [hy3]; exact ⟨1, rfl⟩)
  have hτK : τ ∈ K := hTK hτT
  have hs₁K : s₁ ∈ K := hTK hs₁T
  have hs₂K : s₂ ∈ K := hTK hs₂T
  have hs₁2 : s₁ ^ 2 = 1 := by rw [pow_two]; exact hs₁sq
  have hs₂2 : s₂ ^ 2 = 1 := by rw [pow_two]; exact hs₂sq
  have hcon : ∀ g ∈ K, ∀ l : MulAut W, l ∈ K → g * l * g⁻¹ ∈ K := fun g hg l hl =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg)
  have hboth : (∃ c ∈ L₁, c ∈ K ∧ c ≠ 1 ∧ c ^ 3 = 1) ∧ (∃ c ∈ L₂, c ∈ K ∧ c ≠ 1 ∧ c ^ 3 = 1) := by
    by_cases hl₂1 : l₂ = 1
    · have hl₁y : l₁ = y := by rw [hyeq, hl₂1, mul_one]
      have hl₁1 : l₁ ≠ 1 := by rw [hl₁y]; exact hy1
      refine ⟨⟨l₁, hl₁, hl₁y ▸ hyK, hl₁1, hl₁3⟩, ⟨τ * l₁ * τ⁻¹, ?_, hcon τ hτK l₁ (hl₁y ▸ hyK),
        ?_, ?_⟩⟩
      · have : τ * l₁ * τ⁻¹ ∈ B1.conjAut τ L₁ := by
          rw [B1.mem_conjAut]; simpa [mul_assoc] using hl₁
        rwa [hτ1] at this
      · intro h1
        apply hl₁1
        have h2 : l₁ = τ⁻¹ * (τ * l₁ * τ⁻¹) * τ := by group
        rw [h1, mul_one, inv_mul_cancel] at h2
        exact h2
      · have : (τ * l₁ * τ⁻¹) ^ 3 = τ * l₁ ^ 3 * τ⁻¹ := by
          simp [conj_pow]
        rw [this, hl₁3]
        simp
    by_cases hl₁1 : l₁ = 1
    · have hl₂y : l₂ = y := by rw [hyeq, hl₁1, one_mul]
      refine ⟨⟨τ * l₂ * τ⁻¹, ?_, hcon τ hτK l₂ (hl₂y ▸ hyK), ?_, ?_⟩,
        ⟨l₂, hl₂, hl₂y ▸ hyK, hl₂1, hl₂3⟩⟩
      · have : τ * l₂ * τ⁻¹ ∈ B1.conjAut τ L₂ := by
          rw [B1.mem_conjAut]; simpa [mul_assoc] using hl₂
        rwa [hτ2] at this
      · intro h1
        apply hl₂1
        have h2 : l₂ = τ⁻¹ * (τ * l₂ * τ⁻¹) * τ := by group
        rw [h1, mul_one, inv_mul_cancel] at h2
        exact h2
      · have : (τ * l₂ * τ⁻¹) ^ 3 = τ * l₂ ^ 3 * τ⁻¹ := by
          simp [conj_pow]
        rw [this, hl₂3]
        simp
    ·
      have hinv : s₂ * l₂ * s₂⁻¹ = l₂⁻¹ := conj_inv_cube h.nat₂ hs₂L hs₂2 hs₂1 hl₂ hl₂3
      have hc21 : s₂ * l₁ * s₂⁻¹ = l₁ := by
        have : s₂ * l₁ = l₁ * s₂ := (h.comm l₁ hl₁ s₂ hs₂L).symm
        rw [this]; simp
      have hcy : s₂ * y * s₂⁻¹ = l₁ * l₂⁻¹ := by
        have : s₂ * (l₁ * l₂) * s₂⁻¹ = (s₂ * l₁ * s₂⁻¹) * (s₂ * l₂ * s₂⁻¹) := by group
        rw [hyeq, this, hc21, hinv]
      have hK1 : y * (s₂ * y * s₂⁻¹) ∈ K := Subgroup.mul_mem _ hyK (hcon s₂ hs₂K y hyK)
      have hl₁sq : l₁ * l₁ ∈ K := by
        have : y * (s₂ * y * s₂⁻¹) = l₁ * l₁ := by
          rw [hcy, hyeq]
          have hcomm : l₁ * l₂ = l₂ * l₁ := h.comm l₁ hl₁ l₂ hl₂
          calc l₁ * l₂ * (l₁ * l₂⁻¹) = l₁ * (l₂ * l₁) * l₂⁻¹ := by group
            _ = l₁ * (l₁ * l₂) * l₂⁻¹ := by rw [hcomm]
            _ = l₁ * l₁ := by group
        rwa [this] at hK1
      have hl₁K : l₁ ∈ K := by
        have h4 : (l₁ * l₁) * (l₁ * l₁) = l₁ := by
          calc (l₁ * l₁) * (l₁ * l₁) = l₁ ^ 3 * l₁ := by rw [pow_three]; group
            _ = l₁ := by rw [hl₁3, one_mul]
        rw [← h4]
        exact Subgroup.mul_mem _ hl₁sq hl₁sq
      have hl₂K : l₂ ∈ K := by
        have : l₂ = l₁⁻¹ * y := by rw [hyeq]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₁K) hyK
      exact ⟨⟨l₁, hl₁, hl₁K, hl₁1, hl₁3⟩, ⟨l₂, hl₂, hl₂K, hl₂1, hl₂3⟩⟩
  have hgen : ∀ (L : Subgroup (MulAut W)) (hc : Nat.card L = 6) (s c : MulAut W), s ∈ L → c ∈ L →
      s ∈ K → c ∈ K → s ≠ 1 → s ^ 2 = 1 → c ≠ 1 → c ^ 3 = 1 → L ≤ K := by
    intro L hc s c hsL hcL hsK hcK hs1 hs2 hc1 hc3
    have hdvd : Nat.card ↥(K ⊓ L) ∣ 6 := hc ▸ Subgroup.card_dvd_of_le (inf_le_right : K ⊓ L ≤ L)
    have h2 : 2 ∣ Nat.card ↥(K ⊓ L) := by
      have h1 : orderOf (⟨s, Subgroup.mem_inf.2 ⟨hsK, hsL⟩⟩ : ↥(K ⊓ L)) ∣
          Nat.card ↥(K ⊓ L) := orderOf_dvd_natCard _
      have h2' : orderOf (⟨s, Subgroup.mem_inf.2 ⟨hsK, hsL⟩⟩ : ↥(K ⊓ L)) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hs2 hs1
      rwa [h2'] at h1
    have h3 : 3 ∣ Nat.card ↥(K ⊓ L) := by
      have h1 : orderOf (⟨c, Subgroup.mem_inf.2 ⟨hcK, hcL⟩⟩ : ↥(K ⊓ L)) ∣
          Nat.card ↥(K ⊓ L) := orderOf_dvd_natCard _
      have h2' : orderOf (⟨c, Subgroup.mem_inf.2 ⟨hcK, hcL⟩⟩ : ↥(K ⊓ L)) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime hc3 hc1
      rwa [h2'] at h1
    have h6 : Nat.card ↥(K ⊓ L) = 6 := by
      have hle : Nat.card ↥(K ⊓ L) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card ↥(K ⊓ L) := Nat.card_pos
      omega
    have heq : K ⊓ L = L := Subgroup.eq_of_le_of_card_ge (inf_le_right) (by rw [h6, hc])
    rw [← heq]
    exact inf_le_left
  obtain ⟨⟨c₁, hc₁L, hc₁K, hc₁1, hc₁3⟩, ⟨c₂, hc₂L, hc₂K, hc₂1, hc₂3⟩⟩ := hboth
  have hL₁K : L₁ ≤ K := hgen L₁ h.card_L₁ s₁ c₁ hs₁L hc₁L hs₁K hc₁K hs₁1 hs₁2 hc₁1 hc₁3
  have hL₂K : L₂ ≤ K := hgen L₂ h.card_L₂ s₂ c₂ hs₂L hc₂L hs₂K hc₂K hs₂1 hs₂2 hc₂1 hc₂3
  apply le_antisymm hKX
  intro g hg
  rcases h.coset hg (hT.1 hτT) hτN with hgN | hgN
  · exact (sup_le hL₁K hL₂K) hgN
  · have : g = (g * τ⁻¹) * τ := by group
    rw [this]
    exact Subgroup.mul_mem _ ((sup_le hL₁K hL₂K) hgN) hτK

theorem exists_central [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) :
    ∃ r ∈ T', r ≠ 1 ∧ r * r = 1 ∧ (∀ x ∈ T', x * r = r * x) ∧
      (∀ z ∈ T', (∀ x ∈ T', x * z = z * x) → z = 1 ∨ z = r) ∧
      (∀ y ∈ X, Odd (orderOf y) → r * y * r⁻¹ = y⁻¹) := by
  classical
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hs₁1 : s₁ ≠ 1 := hF.sylow.s₁_ne
  have hs₂1 : s₂ ≠ 1 := hF.sylow.s₂_ne
  have hs₁sq : s₁ * s₁ = 1 := hF.s₁_sq
  have hs₂sq : s₂ * s₂ = 1 := hF.s₂_sq
  have hτT : τ ∈ T' := hF.τ_T
  have hτN : τ ∉ L₁ ⊔ L₂ := hF.τ_N
  have k₁ : τ * s₁ * τ⁻¹ = s₂ := hF.τs₁
  have k₂ : τ * s₂ * τ⁻¹ = s₁ := hF.τs₂
  have hSeq := hF.S_eq
  have hne12 : s₁ ≠ s₂ := hF.ne
  have hm1 : s₁ * s₂ ≠ 1 := hF.mul_ne
  have hc12 : s₁ * s₂ = s₂ * s₁ := hF.comm
  have hS4 := h.card_S hT
  have hT8 := h.card_T hT
  have hrel : (T' ⊓ (L₁ ⊔ L₂)).relIndex T' = 2 := by
    have h1 := Subgroup.relIndex_mul_card (T' ⊓ (L₁ ⊔ L₂)) T'
    rw [inf_eq_left.mpr (inf_le_left : T' ⊓ (L₁ ⊔ L₂) ≤ T'), hS4, hT8] at h1
    omega
  have hcos : ∀ x ∈ T', x ∈ T' ⊓ (L₁ ⊔ L₂) ∨ x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := fun x hx =>
    coset_of_relIndex_two hrel hx hτT (fun hτS => hτN hτS.2)
  have e1 : s₁ * (s₁ * s₂) = s₂ := by rw [← mul_assoc, hs₁sq, one_mul]
  have e2 : (s₁ * s₂) * s₁ = s₂ := by rw [hc12, mul_assoc, hs₁sq, mul_one]
  have e3 : s₂ * (s₁ * s₂) = s₁ := by rw [hc12, ← mul_assoc, hs₂sq, one_mul]
  have e4 : (s₁ * s₂) * s₂ = s₁ := by rw [mul_assoc, hs₂sq, mul_one]
  have hrsq : (s₁ * s₂) * (s₁ * s₂) = 1 := by rw [← mul_assoc, e2, hs₂sq]
  have hτr : τ * (s₁ * s₂) * τ⁻¹ = s₁ * s₂ := by
    have : τ * (s₁ * s₂) * τ⁻¹ = (τ * s₁ * τ⁻¹) * (τ * s₂ * τ⁻¹) := by group
    rw [this, k₁, k₂, ← hc12]
  have hτr' : τ * (s₁ * s₂) = (s₁ * s₂) * τ := by
    calc τ * (s₁ * s₂) = (τ * (s₁ * s₂) * τ⁻¹) * τ := by group
      _ = (s₁ * s₂) * τ := by rw [hτr]
  have hCent : ∀ x ∈ T' ⊓ (L₁ ⊔ L₂), x * (s₁ * s₂) = (s₁ * s₂) * x := by
    intro x hx
    rcases (hSeq x).1 hx with h1 | h1 | h1 | h1
    · rw [h1]; simp
    · rw [h1, e1, e2]
    · rw [h1, e3, e4]
    · rw [h1]
  have hcentral : ∀ x ∈ T', x * (s₁ * s₂) = (s₁ * s₂) * x := by
    intro x hx
    rcases hcos x hx with hxS | hxS
    · exact hCent x hxS
    · have hw := hCent _ hxS
      calc x * (s₁ * s₂) = (x * τ⁻¹) * (τ * (s₁ * s₂)) := by group
        _ = (x * τ⁻¹) * ((s₁ * s₂) * τ) := by rw [hτr']
        _ = ((x * τ⁻¹) * (s₁ * s₂)) * τ := by group
        _ = ((s₁ * s₂) * (x * τ⁻¹)) * τ := by rw [hw]
        _ = (s₁ * s₂) * x := by group
  have hnc : ∀ z ∈ T', (∀ x ∈ T', x * z = z * x) → z = 1 ∨ z = s₁ * s₂ := by
    intro z hz hzc
    rcases hcos z hz with hzS | hzS
    · rcases (hSeq z).1 hzS with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exfalso
        have h2 := hzc τ hτT
        rw [h1] at h2
        exact hne12 (calc s₁ = (s₁ * τ) * τ⁻¹ := by group
          _ = (τ * s₁) * τ⁻¹ := by rw [h2]
          _ = s₂ := k₁)
      · exfalso
        have h2 := hzc τ hτT
        rw [h1] at h2
        exact hne12 (calc s₁ = (τ * s₂) * τ⁻¹ := k₂.symm
          _ = (s₂ * τ) * τ⁻¹ := by rw [h2]
          _ = s₂ := by group)
      · exact Or.inr h1
    · exfalso
      have hwc : (z * τ⁻¹) * s₁ = s₁ * (z * τ⁻¹) := by
        rcases (hSeq _).1 hzS with h1 | h1 | h1 | h1
        · rw [h1]; simp
        · rw [h1]
        · rw [h1]; exact hc12.symm
        · rw [h1, e2, e1]
      have hz1 := hzc s₁ hs₁T
      have h2 : s₁ * τ = τ * s₁ := by
        have h3 : (z * τ⁻¹) * (s₁ * τ) = (z * τ⁻¹) * (τ * s₁) := by
          calc (z * τ⁻¹) * (s₁ * τ) = ((z * τ⁻¹) * s₁) * τ := by group
            _ = (s₁ * (z * τ⁻¹)) * τ := by rw [hwc]
            _ = s₁ * z := by group
            _ = z * s₁ := hz1
            _ = (z * τ⁻¹) * (τ * s₁) := by group
        exact mul_left_cancel h3
      exact hne12 (calc s₁ = (s₁ * τ) * τ⁻¹ := by group
        _ = (τ * s₁) * τ⁻¹ := by rw [h2]
        _ = s₂ := k₁)
  have hinv : ∀ y ∈ X, Odd (orderOf y) → (s₁ * s₂) * y * (s₁ * s₂)⁻¹ = y⁻¹ := by
    intro y hy hodd
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl, hl₁3, hl₂3⟩ := h.odd_decomp (h.odd_mem_sup hy hodd) hodd
    have hs₁2 : s₁ ^ 2 = 1 := by rw [pow_two]; exact hs₁sq
    have hs₂2 : s₂ ^ 2 = 1 := by rw [pow_two]; exact hs₂sq
    have i₁ : s₁ * l₁ * s₁⁻¹ = l₁⁻¹ := conj_inv_cube h.nat₁ hs₁L hs₁2 hs₁1 hl₁ hl₁3
    have i₂ : s₂ * l₂ * s₂⁻¹ = l₂⁻¹ := conj_inv_cube h.nat₂ hs₂L hs₂2 hs₂1 hl₂ hl₂3
    have hc₂₁ : Commute s₂ l₁ := (h.comm l₁ hl₁ s₂ hs₂L).symm
    have hc₁₂ : Commute s₁ l₂ := h.comm s₁ hs₁L l₂ hl₂
    have c₁ : s₂ * l₁ * s₂⁻¹ = l₁ := by rw [hc₂₁.eq]; simp
    have c₂ : s₁ * l₂⁻¹ * s₁⁻¹ = l₂⁻¹ := by rw [hc₁₂.inv_right.eq]; simp
    have hc : Commute l₁ l₂ := h.comm l₁ hl₁ l₂ hl₂
    have e : (s₁ * s₂) * (l₁ * l₂) * (s₁ * s₂)⁻¹ =
        (s₁ * (s₂ * l₁ * s₂⁻¹) * s₁⁻¹) * (s₁ * (s₂ * l₂ * s₂⁻¹) * s₁⁻¹) := by group
    rw [e, c₁, i₂, i₁, c₂, mul_inv_rev]
    exact hc.inv_inv.eq
  exact ⟨s₁ * s₂, Subgroup.mul_mem _ hs₁T hs₂T, hm1, hrsq, hcentral, hnc, hinv⟩

theorem card_fixV_le_two [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) : Nat.card ↥(fixV T') ≤ 2 := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hsub : ((fixV T' : Subgroup W) : Set W) ⊆ {1, a₁ * a₂} := fun w hw => by
    rcases hF.fix w (mem_fixV.1 hw) with h1 | h1 <;> simp [h1]
  have h1 : Nat.card (fixV T') = ((fixV T' : Subgroup W) : Set W).ncard := Nat.card_coe_set_eq _
  rw [h1]
  calc ((fixV T' : Subgroup W) : Set W).ncard ≤ ({1, a₁ * a₂} : Set W).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)

theorem symm (h : OfourStruct X L₁ L₂ t) : OfourStruct X L₂ L₁ t where
  nat₁ := h.nat₂
  nat₂ := h.nat₁
  comm := fun a ha b hb => (h.comm b hb a ha).symm
  Linf := by rw [inf_comm]; exact h.Linf
  inf := by rw [inf_comm]; exact h.inf
  sup := by rw [sup_comm]; exact h.sup
  swap₁ := h.swap₂
  swap₂ := h.swap₁
  conj₁ := h.conj₂
  conj₂ := h.conj₁
  tsq := h.tsq
  eq := by rw [sup_comm L₂ L₁]; exact h.eq

theorem L₂_fix₁ (h : OfourStruct X L₁ L₂ t) {l : MulAut W} {x : W} (hl : l ∈ L₂)
    (hx : x ∈ commV L₁) : l x = x :=
  apply_eq_of_mem_commV_of_commute (fun a ha b hb => (h.comm b hb a ha).symm)
    (by rw [inf_comm]; exact h.inf) hl hx

theorem sup_le_stab₁ (h : OfourStruct X L₁ L₂ t) : L₁ ⊔ L₂ ≤ stabSub (commV L₁) := by
  refine sup_le (fun l hl => ?_) (fun l hl => ?_)
  · exact mem_stabSub_of_forall (fun u hu => commV_stable L₁ hl hu)
      (fun u hu => commV_stable L₁ (L₁.inv_mem hl) hu)
  · refine mem_stabSub_of_forall (fun u hu => ?_) (fun u hu => ?_)
    · rw [h.L₂_fix₁ hl hu]; exact hu
    · rw [h.L₂_fix₁ (L₂.inv_mem hl) hu]; exact hu

theorem sup_le_stab₂ (h : OfourStruct X L₁ L₂ t) : L₁ ⊔ L₂ ≤ stabSub (commV L₂) := by
  rw [sup_comm]
  exact h.symm.sup_le_stab₁

theorem mem_sup_iff (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hx : x ∈ X) :
    x ∈ L₁ ⊔ L₂ ↔ ∀ u ∈ commV L₁, x u ∈ commV L₁ := by
  constructor
  · intro hxN u hu
    exact (mem_stabSub.1 (h.sup_le_stab₁ hxN) u).2 hu
  · intro hstab
    by_contra hxN
    have hxt : x * t ∈ L₁ ⊔ L₂ := (h.mem_or_mul_t_mem hx).resolve_left hxN
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ commV L₁, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : commV L₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      have h4 := h.card_U₁
      rw [this, Subgroup.card_bot] at h4
      omega
    have htt : t (t u) = u := by
      have := congrArg (fun φ : MulAut W => φ u) h.tsq
      simpa using this
    have e : (x * t) (t u) = x u := by
      rw [MulAut.mul_apply, htt]
    have h1 : x u ∈ commV L₂ := by
      have := (mem_stabSub.1 (h.sup_le_stab₂ hxt) (t u)).2 (h.swap₁ u hu)
      rwa [e] at this
    have h2 : x u ∈ commV L₁ := hstab u hu
    have : x u ∈ commV L₁ ⊓ commV L₂ := ⟨h2, h1⟩
    rw [h.inf, Subgroup.mem_bot] at this
    exact hu1 (x.injective (by rw [this, map_one]))

theorem mem_L₁_iff (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hx : x ∈ X) :
    x ∈ L₁ ↔ ∀ u ∈ commV L₂, x u = u := by
  constructor
  · intro hxl u hu
    exact apply_eq_of_mem_commV_of_commute h.comm h.inf hxl hu
  · intro hfix
    have hxN' : x ∈ L₂ ⊔ L₁ := (h.symm.mem_sup_iff hx).2 fun u hu => by rw [hfix u hu]; exact hu
    rw [sup_comm] at hxN'
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := exists_mul_of_mem_sup_of_commute h.comm hxN'
    have hl₂1 : l₂ = 1 := by
      refine eq_one_of_forall_apply_eq h.nat₂ (fun l hl u hu => commV_stable L₂ hl hu) hl₂ ?_
      intro u hu
      have h1 : l₁ (l₂ u) = l₂ u :=
        apply_eq_of_mem_commV_of_commute h.comm h.inf hl₁ (commV_stable L₂ hl₂ hu)
      have := hfix u hu
      rwa [MulAut.mul_apply, h1] at this
    rw [hl₂1, mul_one]
    exact hl₁

theorem mem_L₂_iff (h : OfourStruct X L₁ L₂ t) {x : MulAut W} (hx : x ∈ X) :
    x ∈ L₂ ↔ ∀ u ∈ commV L₁, x u = u :=
  h.symm.mem_L₁_iff hx

theorem exists_decomp_W (h : OfourStruct X L₁ L₂ t) (w : W) :
    ∃ u₁ ∈ commV L₁, ∃ u₂ ∈ commV L₂, w = u₁ * u₂ := by
  have hw : w ∈ commV L₁ ⊔ commV L₂ := by rw [h.sup]; exact Subgroup.mem_top w
  obtain ⟨u₁, hu₁, u₂, hu₂, e⟩ := Subgroup.mem_sup.mp hw
  exact ⟨u₁, hu₁, u₂, hu₂, e.symm⟩

theorem L₁_fix₂ (h : OfourStruct X L₁ L₂ t) {l : MulAut W} {x : W} (hl : l ∈ L₁)
    (hx : x ∈ commV L₂) : l x = x :=
  apply_eq_of_mem_commV_of_commute h.comm h.inf hl hx

theorem fix_of_fix_mul (h : OfourStruct X L₁ L₂ t) {s₁ s₂ : MulAut W} (hs₁ : s₁ ∈ L₁)
    (hs₂ : s₂ ∈ L₂) {w : W} (hw : (s₁ * s₂) w = w) : s₁ w = w ∧ s₂ w = w := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
  have e1 : s₂ u₁ = u₁ := h.L₂_fix₁ hs₂ hu₁
  have e2 : s₁ u₂ = u₂ := h.L₁_fix₂ hs₁ hu₂
  have hs₁u₁ : s₁ u₁ ∈ commV L₁ := commV_stable L₁ hs₁ hu₁
  have hs₂u₂ : s₂ u₂ ∈ commV L₂ := commV_stable L₂ hs₂ hu₂
  have e3 : s₁ (s₂ u₂) = s₂ u₂ := h.L₁_fix₂ hs₁ hs₂u₂
  have e : (s₁ * s₂) (u₁ * u₂) = (s₁ u₁) * (s₂ u₂) := by
    rw [MulAut.mul_apply, map_mul, e1, map_mul, e3]
  rw [e] at hw
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf hs₁u₁ hu₁ hs₂u₂ hu₂ hw
  constructor
  · rw [map_mul, h1, e2]
  · rw [map_mul, e1, h2]

theorem card_fixV_le_four_of_swap [Finite W] (h : OfourStruct X L₁ L₂ t) {x : MulAut W}
    (hX : x ∈ X) (hxN : x ∉ L₁ ⊔ L₂) {B : Subgroup (MulAut W)} (hxB : x ∈ B) :
    Nat.card ↥(fixV B) ≤ 4 := by
  have hxt : x * t ∈ L₁ ⊔ L₂ := (h.mem_or_mul_t_mem hX).resolve_left hxN
  have htt : ∀ u : W, t (t u) = u := fun u => by
    have := congrArg (fun φ : MulAut W => φ u) h.tsq
    simpa using this
  have hx_eq : ∀ u : W, x u = (x * t) (t u) := fun u => by rw [MulAut.mul_apply, htt]
  have hx₁ : ∀ u ∈ commV L₁, x u ∈ commV L₂ := fun u hu => by
    rw [hx_eq]
    exact (mem_stabSub.1 (h.sup_le_stab₂ hxt) (t u)).2 (h.swap₁ u hu)
  have hx₂ : ∀ u ∈ commV L₂, x u ∈ commV L₁ := fun u hu => by
    rw [hx_eq]
    exact (mem_stabSub.1 (h.sup_le_stab₁ hxt) (t u)).2 (h.swap₂ u hu)
  have hsub : ((fixV B : Subgroup W) : Set W) ⊆ (fun u => x u * u) '' (commV L₂ : Set W) := by
    intro w hw
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := h.exists_decomp_W w
    have hfix : x (u₁ * u₂) = u₁ * u₂ := mem_fixV.1 hw x hxB
    rw [map_mul] at hfix
    have hc : x u₁ * x u₂ = x u₂ * x u₁ := mul_comm _ _
    obtain ⟨e1, e2⟩ := eq_of_mul_eq_of_inf_eq_bot h.inf hu₁ (hx₂ u₂ hu₂) hu₂ (hx₁ u₁ hu₁)
      (hfix.symm.trans hc)
    refine ⟨u₂, hu₂, ?_⟩
    show x u₂ * u₂ = u₁ * u₂
    rw [e1]
  have h1 : Nat.card (fixV B) = ((fixV B : Subgroup W) : Set W).ncard := Nat.card_coe_set_eq _
  have h2 : ((commV L₂ : Subgroup W) : Set W).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (card_of_actsAsNaturalL2 h.nat₂).2
  rw [h1]
  calc ((fixV B : Subgroup W) : Set W).ncard
      ≤ ((fun u => x u * u) '' (commV L₂ : Set W)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((commV L₂ : Subgroup W) : Set W).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 4 := h2

theorem offender_classification [Finite W] (h : OfourStruct X L₁ L₂ t) {T' : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T' X) :
    ∃ (s₁ s₂ τ : MulAut W) (a₁ a₂ : W), SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂ ∧
      ∀ B : Subgroup (MulAut W), B ≤ T' → B ≠ ⊥ → IsElemAbelian2 B →
        Nat.card W ≤ Nat.card B * Nat.card ↥(fixV B) →
          B ≤ T' ⊓ (L₁ ⊔ L₂) ∧ (s₁ ∈ B ∨ s₂ ∈ B) := by
  classical
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  refine ⟨s₁, s₂, τ, a₁, a₂, hF, ?_⟩
  intro B hBT hBne hBab hff
  have hW : Nat.card W = 16 := by
    have := Subgroup.card_top (G := W)
    have h4 := (card_of_actsAsNaturalL2 h.nat₁).2
    have h4' := (card_of_actsAsNaturalL2 h.nat₂).2
    have hmul := B2F.card_sup_mul_card_inf_of_commute (A := commV L₁) (B := commV L₂)
      (fun a _ b _ => mul_comm a b)
    rw [h.sup, h.inf, Subgroup.card_bot, mul_one, h4, h4', Subgroup.card_top] at hmul
    omega
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hs₁1 : s₁ ≠ 1 := hF.sylow.s₁_ne
  have hs₂1 : s₂ ≠ 1 := hF.sylow.s₂_ne
  have hne12 : s₁ ≠ s₂ := hF.ne
  have hc12 : s₁ * s₂ = s₂ * s₁ := hF.comm
  have hτT : τ ∈ T' := hF.τ_T
  have hτN : τ ∉ L₁ ⊔ L₂ := hF.τ_N
  have hSeq := hF.S_eq
  have hrel := h.relIndex_S hT
  have hcos : ∀ x ∈ T', x ∈ T' ⊓ (L₁ ⊔ L₂) ∨ x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := fun x hx =>
    coset_of_relIndex_two hrel hx hτT (fun hτS => hτN hτS.2)
  have e1 : s₁ * (s₁ * s₂) = s₂ := by rw [← mul_assoc, hF.s₁_sq, one_mul]
  have e2 : (s₁ * s₂) * s₁ = s₂ := by rw [hc12, mul_assoc, hF.s₁_sq, mul_one]
  have e3 : s₂ * (s₁ * s₂) = s₁ := by rw [hc12, ← mul_assoc, hF.s₂_sq, one_mul]
  have e4 : (s₁ * s₂) * s₂ = s₁ := by rw [mul_assoc, hF.s₂_sq, mul_one]
  have hScomm : ∀ x ∈ T' ⊓ (L₁ ⊔ L₂), ∀ y ∈ T' ⊓ (L₁ ⊔ L₂), x * y = y * x := by
    intro x hx y hy
    rcases (hSeq x).1 hx with h1 | h1 | h1 | h1 <;>
      rcases (hSeq y).1 hy with h2 | h2 | h2 | h2 <;>
      rw [h1, h2] <;>
      first
        | rfl
        | simp only [one_mul, mul_one]
        | exact hc12
        | exact hc12.symm
        | rw [e1, e2]
        | rw [e3, e4]
  have hconj : ∀ x ∈ T', x ∉ T' ⊓ (L₁ ⊔ L₂) → x * s₁ * x⁻¹ = s₂ ∧ x * s₂ * x⁻¹ = s₁ := by
    intro x hx hxS
    have hw : x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := (hcos x hx).resolve_left hxS
    have hx' : x = (x * τ⁻¹) * τ := by group
    have c1 : (x * τ⁻¹) * s₁ = s₁ * (x * τ⁻¹) := hScomm _ hw _ hF.sylow.s₁_mem_S
    have c2 : (x * τ⁻¹) * s₂ = s₂ * (x * τ⁻¹) := hScomm _ hw _ hF.sylow.s₂_mem_S
    constructor
    · calc x * s₁ * x⁻¹ = (x * τ⁻¹) * (τ * s₁ * τ⁻¹) * (x * τ⁻¹)⁻¹ := by group
        _ = (x * τ⁻¹) * s₂ * (x * τ⁻¹)⁻¹ := by rw [hF.τs₁]
        _ = s₂ := by rw [c2]; group
    · calc x * s₂ * x⁻¹ = (x * τ⁻¹) * (τ * s₂ * τ⁻¹) * (x * τ⁻¹)⁻¹ := by group
        _ = (x * τ⁻¹) * s₁ * (x * τ⁻¹)⁻¹ := by rw [hF.τs₂]
        _ = s₁ := by rw [c1]; group
  by_cases hs : s₁ ∈ B ∨ s₂ ∈ B
  · refine ⟨fun z hz => ?_, hs⟩
    by_contra hzS
    obtain ⟨hz1, hz2⟩ := hconj z (hBT hz) hzS
    rcases hs with hs | hs
    ·
      have hcz : z * s₁ = s₁ * z := hBab.1 z hz s₁ hs
      apply hne12
      calc s₁ = z * s₁ * z⁻¹ := by rw [hcz]; group
        _ = s₂ := hz1
    · have hcz : z * s₂ = s₂ * z := hBab.1 z hz s₂ hs
      apply hne12
      calc s₁ = z * s₂ * z⁻¹ := hz2.symm
        _ = s₂ := by rw [hcz]; group
  · exfalso
    push Not at hs
    obtain ⟨hs1B, hs2B⟩ := hs
    have hBS : ∀ z ∈ B, z ∈ T' ⊓ (L₁ ⊔ L₂) → z = 1 ∨ z = s₁ * s₂ := by
      intro z hz hzS
      rcases (hSeq z).1 hzS with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd (h1 ▸ hz) hs1B
      · exact absurd (h1 ▸ hz) hs2B
      · exact Or.inr h1
    obtain ⟨y, hyB, hy1⟩ : ∃ y ∈ B, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hBne ((Subgroup.eq_bot_iff_forall B).2 hcon)
    have hfixr : ∀ w, (s₁ * s₂) w = w → w = 1 ∨ w = a₁ ∨ w = a₂ ∨ w = a₁ * a₂ := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := h.fix_of_fix_mul hs₁L hs₂L hw
      refine (hF.sylow.fixS w).1 fun x hx => ?_
      rcases (hSeq x).1 hx with h1 | h1 | h1 | h1
      · rw [h1]; simp
      · rw [h1]; exact hw1
      · rw [h1]; exact hw2
      · rw [h1]; exact hw
    by_cases hS' : ∀ z ∈ B, z ∈ T' ⊓ (L₁ ⊔ L₂)
    ·
      have hrB : s₁ * s₂ ∈ B := by
        rcases hBS y hyB (hS' y hyB) with h1 | h1
        · exact absurd h1 hy1
        · exact h1 ▸ hyB
      have hBsub : (B : Set (MulAut W)) ⊆ {1, s₁ * s₂} := fun z hz => by
        rcases hBS z hz (hS' z hz) with h1 | h1 <;> simp [h1]
      have hcardB : Nat.card B ≤ 2 := by
        have h1 : Nat.card B = (B : Set (MulAut W)).ncard := Nat.card_coe_set_eq _
        rw [h1]
        exact (Set.ncard_le_ncard hBsub (Set.toFinite _)).trans
          ((Set.ncard_insert_le _ _).trans (by simp))
      have hfixsub : ((fixV B : Subgroup W) : Set W) ⊆ {1, a₁, a₂, a₁ * a₂} := fun w hw => by
        have := hfixr w (mem_fixV.1 hw _ hrB)
        simpa using this
      have hcardfix : Nat.card ↥(fixV B) ≤ 4 := by
        have h1 : Nat.card (fixV B) = ((fixV B : Subgroup W) : Set W).ncard :=
          Nat.card_coe_set_eq _
        rw [h1]
        refine (Set.ncard_le_ncard hfixsub (Set.toFinite _)).trans ?_
        exact (Set.ncard_insert_le _ _).trans ((Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
          (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (by simp))))))
      have := Nat.mul_le_mul hcardB hcardfix
      omega
    · push Not at hS'
      obtain ⟨x, hxB, hxS⟩ := hS'
      have hxT : x ∈ T' := hBT hxB
      have hxX : x ∈ X := hT.1 hxT
      have hxN : x ∉ L₁ ⊔ L₂ := fun hxN => hxS ⟨hxT, hxN⟩
      have hfix4 := h.card_fixV_le_four_of_swap hxX hxN hxB
      have hBx : ∀ z ∈ B, z ∈ T' ⊓ (L₁ ⊔ L₂) ∨ z * x⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := by
        intro z hz
        by_cases hzS : z ∈ T' ⊓ (L₁ ⊔ L₂)
        · exact Or.inl hzS
        · refine Or.inr ?_
          have hzτ : z * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := (hcos z (hBT hz)).resolve_left hzS
          have hxτ : x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := (hcos x hxT).resolve_left hxS
          have e : z * x⁻¹ = (z * τ⁻¹) * (x * τ⁻¹)⁻¹ := by group
          rw [e]
          exact Subgroup.mul_mem _ hzτ (Subgroup.inv_mem _ hxτ)
      by_cases hrB : s₁ * s₂ ∈ B
      ·
        have hBsub : (B : Set (MulAut W)) ⊆ {1, s₁ * s₂, x, (s₁ * s₂) * x} := fun z hz => by
          rcases hBx z hz with h1 | h1
          · rcases hBS z hz h1 with h2 | h2 <;> simp [h2]
          · have hzx : z * x⁻¹ ∈ B := B.mul_mem hz (B.inv_mem hxB)
            rcases hBS _ hzx h1 with h2 | h2
            · have : z = x := by
                have := congrArg (· * x) h2
                simpa using this
              simp [this]
            · have : z = (s₁ * s₂) * x := by
                have := congrArg (· * x) h2
                simpa using this
              simp [this]
        have hcardB : Nat.card B ≤ 4 := by
          have h1 : Nat.card B = (B : Set (MulAut W)).ncard := Nat.card_coe_set_eq _
          rw [h1]
          refine (Set.ncard_le_ncard hBsub (Set.toFinite _)).trans ?_
          exact (Set.ncard_insert_le _ _).trans ((Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans
            (Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans (by simp))))))
        have hfixsub : ((fixV B : Subgroup W) : Set W) ⊆ {1, a₁ * a₂} := fun w hw => by
          have hw' := mem_fixV.1 hw
          have hwS : w = 1 ∨ w = a₁ ∨ w = a₂ ∨ w = a₁ * a₂ := hfixr w (hw' _ hrB)
          have hwS' : ∀ v ∈ T' ⊓ (L₁ ⊔ L₂), ∀ u, (u = 1 ∨ u = a₁ ∨ u = a₂ ∨ u = a₁ * a₂) →
              v u = u := fun v hv u hu =>
            (hF.sylow.fixS u).2 hu v hv
          have hxv : x * τ⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := (hcos x hxT).resolve_left hxS
          have hτw : τ w = w := by
            have h1 : x w = w := hw' x hxB
            have h2 : x w = (x * τ⁻¹) (τ w) := by
              rw [MulAut.mul_apply]
              simp
            have hτw' : τ w = 1 ∨ τ w = a₁ ∨ τ w = a₂ ∨ τ w = a₁ * a₂ := by
              rcases hwS with h3 | h3 | h3 | h3
              · left; rw [h3, map_one]
              · right; right; left; rw [h3, hF.τa₁]
              · right; left; rw [h3, hF.τa₂]
              · right; right; right; rw [h3, map_mul, hF.τa₁, hF.τa₂, mul_comm]
            rw [h2, hwS' _ hxv _ hτw'] at h1
            exact h1
          have hTfix : ∀ v ∈ T', v w = w := by
            intro v hv
            rcases hcos v hv with h1 | h1
            · exact hwS' v h1 w hwS
            · have h2 : v = (v * τ⁻¹) * τ := by group
              rw [h2, MulAut.mul_apply, hτw, hwS' _ h1 w hwS]
          simpa using hF.fix w hTfix
        have hcardfix : Nat.card ↥(fixV B) ≤ 2 := by
          have h1 : Nat.card (fixV B) = ((fixV B : Subgroup W) : Set W).ncard :=
            Nat.card_coe_set_eq _
          rw [h1]
          exact (Set.ncard_le_ncard hfixsub (Set.toFinite _)).trans
            ((Set.ncard_insert_le _ _).trans (by simp))
        have := Nat.mul_le_mul hcardB hcardfix
        omega
      ·
        have hBsub : (B : Set (MulAut W)) ⊆ {1, x} := fun z hz => by
          rcases hBx z hz with h1 | h1
          · rcases hBS z hz h1 with h2 | h2
            · simp [h2]
            · exact absurd (h2 ▸ hz) hrB
          · have hzx : z * x⁻¹ ∈ B := B.mul_mem hz (B.inv_mem hxB)
            rcases hBS _ hzx h1 with h2 | h2
            · have : z = x := by
                have := congrArg (· * x) h2
                simpa using this
              simp [this]
            · exact absurd (h2 ▸ hzx) hrB
        have hcardB : Nat.card B ≤ 2 := by
          have h1 : Nat.card B = (B : Set (MulAut W)).ncard := Nat.card_coe_set_eq _
          rw [h1]
          exact (Set.ncard_le_ncard hBsub (Set.toFinite _)).trans
            ((Set.ncard_insert_le _ _).trans (by simp))
        have := Nat.mul_le_mul hcardB hfix4
        omega

end OfourStruct

end CFSG.Quasithin
