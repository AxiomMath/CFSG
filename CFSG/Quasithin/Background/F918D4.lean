module

public import CFSG.Quasithin.Background.FFC6P
public import CFSG.Quasithin.Vol2.Ch10SecD31D

public section

namespace CFSG.Quasithin

private theorem l3_eq_one_of_central (γ : L3.Γ) (hγ : ∀ δ : L3.Γ, γ * δ = δ * γ) : γ = 1 := by
  obtain ⟨c, hc0, hcim⟩ := L3.invol_center L3.x12 L3.x12_invol
  have hcγ : L3.act γ c = c := by
    have hc : c ∈ L3.cim L3.x12 := by rw [hcim]; simp
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hc
    have hv' : L3.act L3.x12 v - v = c := hv
    have h1 : L3.act γ c ∈ L3.cim L3.x12 := by
      refine Finset.mem_image.mpr ⟨L3.act γ v, Finset.mem_univ _, ?_⟩
      show L3.act L3.x12 (L3.act γ v) - L3.act γ v = L3.act γ c
      rw [← hv', L3.act_sub, ← L3.act_mul, ← L3.act_mul, hγ]
    rw [hcim] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h0 | h0
    · exfalso
      apply hc0
      have := L3.act_inv_act γ c
      rw [h0, L3.act_zero] at this
      exact this.symm
    · exact h0
  apply L3.act_injective
  intro v
  by_cases hv : v = 0
  · rw [hv, L3.act_zero]
  · obtain ⟨δ, rfl⟩ := L3.act_trans c v hc0 hv
    rw [← L3.act_mul, hγ, L3.act_mul, hcγ]

section Cover

variable {W : Type} [CommGroup W]

private theorem commSub_eq_xmodCommOf (L : Subgroup (MulAut W)) (V : Subgroup W) :
    commSub V L = XMod.commOf ↥L V := by
  unfold commSub XMod.commOf
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, w, hw, rfl⟩
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨a, a.2, l, hl, rfl⟩

private theorem l3Data_faithful {L : Subgroup (MulAut W)} {U Z : Subgroup W} (D : L3Data L U Z)
    {l : MulAut W} (hl : l ∈ L) (h : ∀ u ∈ U, l u = u) : l = 1 := by
  obtain ⟨γ, rfl⟩ := D.exists_rho hl
  have hγ : γ = 1 := by
    apply L3.act_injective
    intro w
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd w)
    have hmem : D.rho γ (u : W) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h2 := D.β_rho γ (u : W) u.2 hmem
    have h3 : (⟨D.rho γ (u : W), hmem⟩ : ↥U) = u := Subtype.ext (h _ u.2)
    rw [h3, hu] at h2
    exact (Multiplicative.ofAdd.injective h2).symm
  rw [hγ, map_one]

private theorem l3Data_irr {L : Subgroup (MulAut W)} {U Z : Subgroup W} (D : L3Data L U Z)
    (J : Subgroup W) (hJ : ∀ x ∈ L, ∀ w ∈ J, x w ∈ J) (hZJ : Z ≤ J) (hJU : J ≤ U) :
    J = Z ∨ J = U := by
  set K : Subgroup (Multiplicative L3.Vec) := (J.subgroupOf U).map D.β
  have hKinv : ∀ γ : L3.Γ, ∀ v ∈ K,
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd v)) ∈ K := by
    rintro γ _ ⟨j, hj, rfl⟩
    have hmem : D.rho γ (j : W) ∈ U := D.inv_U _ (D.rho_mem γ) _ j.2
    refine ⟨⟨D.rho γ (j : W), hmem⟩, ?_, D.β_rho γ (j : W) j.2 hmem⟩
    exact Subgroup.mem_subgroupOf.mpr (hJ _ (D.rho_mem γ) _ (Subgroup.mem_subgroupOf.mp hj))
  by_cases hK1 : K = ⊥
  · left
    refine le_antisymm (fun j hj => ?_) hZJ
    have : D.β ⟨j, hJU hj⟩ ∈ K := ⟨⟨j, hJU hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    rw [hK1, Subgroup.mem_bot] at this
    exact (D.ker_β _).mp this
  · right
    have hKt := Vol2.Ch10.SecD.L3.eq_top_of_invariant hKinv hK1
    refine le_antisymm hJU fun u hu => ?_
    have : D.β ⟨u, hu⟩ ∈ K := by rw [hKt]; exact Subgroup.mem_top _
    obtain ⟨j, hj, hju⟩ := this
    have h1 : D.β (j⁻¹ * ⟨u, hu⟩) = 1 := by
      rw [map_mul, map_inv, hju]
      exact inv_mul_cancel _
    have h2 : ((j⁻¹ * ⟨u, hu⟩ : ↥U) : W) ∈ J := hZJ ((D.ker_β _).mp h1)
    have h3 : (j : W) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have h4 : u = (j : W) * ((j⁻¹ * ⟨u, hu⟩ : ↥U) : W) := by simp
    rw [h4]
    exact J.mul_mem h3 h2

variable {L : Subgroup (MulAut W)} {V : Subgroup W}

private theorem cover_card (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZ : Nat.card ↥(V ⊓ fixV L) = 2) : Nat.card V = 16 := by
  obtain ⟨D⟩ := hnat.toL3Coord
  rw [D.card_U, hZ]

private theorem cover_natAut (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hfaith : ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1) :
    BinaryNaturalSL (autSub L V) ⊤ (fixV (autSub L V)) 3 1 := by
  obtain ⟨K, hK, hfin, hc, hr⟩ := hnat
  refine ⟨K, hK, hfin, hc, ?_⟩
  have hst := B1.le_stabSub_of_invariant hinv
  have h1 := FFC.B59.realizes_comap hst hfaith hr
  have hC : (V ⊓ fixV L).comap V.subtype = fixV (autSub L V) := by
    rw [← map_subtype_fixV_autSub hst]
    exact Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
  rwa [hC] at h1

private theorem commV_autSub_eq_top (hst : L ≤ stabSub V) (hcomm : commSub V L = V) :
    commV (autSub L V) = ⊤ := by
  have key : commSub V L ≤ (commV (autSub L V)).map V.subtype := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact ⟨resHom V ⟨x, hst hx⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹, Subgroup.subset_closure
      ⟨_, mem_autSub.mpr ⟨⟨x, hst hx⟩, hx, rfl⟩, ⟨w, hw⟩, rfl⟩, rfl⟩
  rw [eq_top_iff]
  intro v _
  have hv : (v : W) ∈ commSub V L := by
    rw [hcomm]
    exact v.2
  obtain ⟨c, hc, hcv⟩ := key hv
  have : c = v := Subtype.ext hcv
  rw [← this]
  exact hc

variable [Finite W]

private theorem eq_bot_or_eq_of_le_card_two {S Z : Subgroup W} (hSZ : S ≤ Z)
    (hZ : Nat.card Z = 2) : S = ⊥ ∨ S = Z := by
  have hd : Nat.card S ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hSZ
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact Or.inl (Subgroup.card_eq_one.mp h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hSZ (by rw [h, hZ]))

private theorem cover_not_decomp (hcomm : XMod.commOf ↥L V = V)
    (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1) (hZ : Nat.card ↥(V ⊓ fixV L) = 2) :
    ¬ ∃ A' B' : Subgroup W, ⊥ < A' ∧ ⊥ < B' ∧ XMod.IsInv ↥L A' ∧ XMod.IsInv ↥L B' ∧
      A' ⊔ B' = V ∧ A' ⊓ B' = ⊥ := by
  obtain ⟨D⟩ := hnat.toL3Coord
  exact FFC.B59.not_decomp_of_card ((commSub_eq_xmodCommOf L V).trans hcomm)
    (fun J hJ hZJ hJV => l3Data_irr D J hJ hZJ hJV) (cover_card hnat hZ) hZ

end Cover

theorem cover_faithful {W : Type} [CommGroup W] [Finite W] (_hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (_hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (_hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (_hZ : Nat.card ↥(V ⊓ fixV L) = 2) (l : MulAut W) (hl : l ∈ L) (h : ∀ v ∈ V, l v = v) :
    l = 1 := by
  obtain ⟨D⟩ := hnat.toL3Coord
  exact l3Data_faithful D hl h

theorem cover_uniserial {W : Type} [CommGroup W] [Finite W] (_hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (_hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZ : Nat.card ↥(V ⊓ fixV L) = 2) (S : Subgroup W) (hSV : S ≤ V)
    (hS : ∀ x ∈ L, ∀ s ∈ S, x s ∈ S) :
    S = ⊥ ∨ S = V ⊓ fixV L ∨ S = V := by
  obtain ⟨D⟩ := hnat.toL3Coord
  have hZinv : ∀ x ∈ L, ∀ z ∈ V ⊓ fixV L, x z ∈ V ⊓ fixV L := fun x hx z hz => by
    rw [hz.2 x hx]
    exact hz
  have hSZinv : ∀ x ∈ L, ∀ w ∈ S ⊔ V ⊓ fixV L, x w ∈ S ⊔ V ⊓ fixV L := by
    intro x hx w hw
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hS x hx a ha) (hZinv x hx c hc)
  rcases l3Data_irr D (S ⊔ V ⊓ fixV L) hSZinv le_sup_right (sup_le hSV inf_le_left) with h | h
  · have hSZ : S ≤ V ⊓ fixV L := h ▸ le_sup_left
    rcases eq_bot_or_eq_of_le_card_two hSZ hZ with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · by_cases hZS : V ⊓ fixV L ≤ S
    · right
      right
      rw [← h, sup_eq_left.mpr hZS]
    · exfalso
      have hSZ : S ⊓ (V ⊓ fixV L) = ⊥ := by
        rcases eq_bot_or_eq_of_le_card_two
            (inf_le_right : S ⊓ (V ⊓ fixV L) ≤ V ⊓ fixV L) hZ with h' | h'
        · exact h'
        · exact absurd (h' ▸ inf_le_left) hZS
      have hS0 : S ≠ ⊥ := by
        intro hS0
        rw [hS0, bot_sup_eq] at h
        have := cover_card hnat hZ
        rw [← h, hZ] at this
        norm_num at this
      have hZ0 : V ⊓ fixV L ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.card_bot] at hZ
        norm_num at hZ
      exact cover_not_decomp hcomm hnat hZ ⟨S, V ⊓ fixV L, bot_lt_iff_ne_bot.mpr hS0,
        bot_lt_iff_ne_bot.mpr hZ0, fun a s hs => hS a a.2 s hs,
        fun a z hz => hZinv a a.2 z hz, h, hSZ⟩

theorem cover_commSub_involution {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZ : Nat.card ↥(V ⊓ fixV L) = 2) (l : MulAut W) (hl : l ∈ L) (h1 : l ≠ 1) (h2 : l ^ 2 = 1) :
    Nat.card ↥(commSub V (Subgroup.zpowers l)) = 4 ∧
      commSub V (Subgroup.zpowers l) = V ⊓ fixV (Subgroup.zpowers l) := by
  have hst := B1.le_stabSub_of_invariant hinv
  have hfaith : ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1 := fun g hg h =>
    cover_faithful hexp L V hinv hcomm hnat hZ g hg h
  have hl'L : resHom V ⟨l, hst hl⟩ ∈ autSub L V := mem_autSub.mpr ⟨⟨l, hst hl⟩, hl, rfl⟩
  have hl'1 : resHom V ⟨l, hst hl⟩ ≠ 1 := by
    intro h
    apply h1
    refine hfaith l hl fun v hv => ?_
    exact congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) h
  have hl'2 : resHom V ⟨l, hst hl⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨l, hst hl⟩ : ↥(stabSub V)) ^ 2 = 1 := Subtype.ext h2
    rw [this, map_one]
  obtain ⟨-, -, -, h4⟩ := B4_8_2 (B1.sq_eq_one_sub hexp V) (cover_card hnat hZ)
    (cover_natAut hinv hnat hfaith)
    (FFC.B59.isIndecompModule_autSub hst (cover_not_decomp hcomm hnat hZ))
  obtain ⟨hcf, hrk⟩ := h4 _ hl'L hl'1 hl'2
  have hW : ∀ x ∈ Subgroup.zpowers l, ∀ w ∈ V, x w ∈ V := fun x hx w hw =>
    hinv x (Subgroup.zpowers_le.mpr hl hx) w hw
  have r1 := rk_commV_resHom (hst hl) hW
  have r2 := rk_fixV_resHom (W := V) (hst hl)
  rw [hcf, hrk] at r1
  rw [hrk] at r2
  have heq := eq_of_le_of_rk_le hexp (commSub_zpowers_le_inf_fixV hexp h2 hW) (by omega)
  refine ⟨?_, heq⟩
  rw [card_eq_two_pow hexp, ← r1]
  norm_num

theorem cover_normalizer_stab {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (hZ : Nat.card ↥(V ⊓ fixV L) = 2) (g : MulAut W)
    (hgL : ∀ x : MulAut W, x ∈ L ↔ g * x * g⁻¹ ∈ L) (hgV : ∀ v : W, g v ∈ V ↔ v ∈ V) :
    ∃ l ∈ L, ∀ v ∈ V, g v = l v := by
  have hst := B1.le_stabSub_of_invariant hinv
  have hfaith : ∀ g ∈ L, (∀ v ∈ V, g v = v) → g = 1 := fun g hg h =>
    cover_faithful hexp L V hinv hcomm hnat hZ g hg h
  obtain ⟨D⟩ := (cover_natAut hinv hnat hfaith).toL3Coord
  set g' : ↥(stabSub V) := ⟨g, hgV⟩
  have hx : ∀ φ, φ ∈ autSub L V ↔ resHom V g' * φ * (resHom V g')⁻¹ ∈ autSub L V := by
    intro φ
    constructor
    · intro hφ
      obtain ⟨y, hy, rfl⟩ := mem_autSub.mp hφ
      refine mem_autSub.mpr ⟨g' * y * g'⁻¹, (hgL y).mp hy, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hφ
      obtain ⟨y, hy, hyφ⟩ := mem_autSub.mp hφ
      refine mem_autSub.mpr ⟨g'⁻¹ * y * g', ?_, ?_⟩
      · rw [hgL]
        show g * (g⁻¹ * (y : MulAut W) * g) * g⁻¹ ∈ L
        have e : g * (g⁻¹ * (y : MulAut W) * g) * g⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [map_mul, map_mul, map_inv, hyφ]
        group
  obtain ⟨y, hy, hyg⟩ := mem_autSub.mp (Vol2.Ch10.SecD.mem_of_normalizes D
    (commV_autSub_eq_top hst ((commSub_eq_xmodCommOf L V).trans hcomm)) hx)
  refine ⟨y, hy, fun v hv => ?_⟩
  exact (congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : W)) hyg).symm

theorem cover_center_trivial {W : Type} [CommGroup W] [Finite W] (_hexp : ∀ w : W, w ^ 2 = 1)
    (L : Subgroup (MulAut W)) (V : Subgroup W) (_hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V)
    (_hcomm : XMod.commOf ↥L V = V) (hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1)
    (_hZ : Nat.card ↥(V ⊓ fixV L) = 2) (c : MulAut W) (hc : c ∈ L)
    (hcc : ∀ x ∈ L, c * x = x * c) : c = 1 := by
  obtain ⟨D⟩ := hnat.toL3Coord
  obtain ⟨γ, rfl⟩ := D.exists_rho hc
  have hγ : ∀ δ : L3.Γ, γ * δ = δ * γ := fun δ => D.rho_injective (by
    rw [map_mul, map_mul]
    exact hcc _ (D.rho_mem δ))
  rw [l3_eq_one_of_central γ hγ, map_one]

end CFSG.Quasithin
