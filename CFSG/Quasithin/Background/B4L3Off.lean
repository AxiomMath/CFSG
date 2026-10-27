module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B4L3Inv
public import CFSG.Quasithin.Background.FixVZPowers

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def IsEqFixGroup (G : Subgroup (MulAut V)) (a : MulAut V) (E : Subgroup (MulAut V)) :
    Prop :=
  ∀ g, g ∈ E ↔ g ∈ G ∧ (g = 1 ∨ (g ^ 2 = 1 ∧ fixV (Subgroup.zpowers g) = fixV (Subgroup.zpowers a)))

structure OffHyp (G : Subgroup (MulAut V)) : Prop where
  card_four : Nat.card V = 16
  sq : ∀ v : V, v ^ 2 = 1
  FF : ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 → Nat.card (fixV (Subgroup.zpowers a)) = 4
  E4 : ∀ A : Subgroup (MulAut V), A ≤ G → IsElemAbelian2 A → Nat.card A ≤ 4
  El : ∀ a ∈ G, a ≠ 1 → a ^ 2 = 1 → ∃ E : Subgroup (MulAut V), E ≤ G ∧ Nat.card E = 4 ∧
    IsElemAbelian2 E ∧ IsEqFixGroup G a E

namespace OffHyp

variable {G : Subgroup (MulAut V)} (H : OffHyp G)

include H in
theorem card_fixV_le {A : Subgroup (MulAut V)} (hA : A ≤ G) (hAel : IsElemAbelian2 A)
    {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) : Nat.card (fixV A) ≤ 4 := by
  have h1 : fixV A ≤ fixV (Subgroup.zpowers a) := B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ha)
  have h2 := H.FF a (hA ha) ha1 (hAel.2 a ha)
  rw [← h2]
  exact Subgroup.card_le_of_le h1

include H in
theorem fixV_eq_of_card {A : Subgroup (MulAut V)} (hA : A ≤ G) (hAel : IsElemAbelian2 A)
    {a : MulAut V} (ha : a ∈ A) (ha1 : a ≠ 1) (hc : 4 ≤ Nat.card (fixV A)) :
    fixV A = fixV (Subgroup.zpowers a) := by
  have h1 : fixV A ≤ fixV (Subgroup.zpowers a) := B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ha)
  have h2 := H.FF a (hA ha) ha1 (hAel.2 a ha)
  exact Subgroup.eq_of_le_of_card_ge h1 (by omega)

include H in
theorem isFFStarOffender_iff_eqFix (A : Subgroup (MulAut V)) :
    IsFFStarOffender G A ↔
      ∃ a ∈ G, a ≠ 1 ∧ a ^ 2 = 1 ∧ IsEqFixGroup G a A := by
  constructor
  · intro hA
    obtain ⟨hAG, hAne, hAel, hAoff⟩ := hA
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
    have ha1' : (a : MulAut V) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have haA' : (a : MulAut V) ∈ A := a.2
    have hAcard : Nat.card A ≤ 4 := H.E4 A hAG hAel
    have hVle := hAoff ⊥ bot_le
    rw [B1.card_bot_mul_card_fixV, H.card_four] at hVle
    have hfx : Nat.card (fixV A) ≤ 4 := H.card_fixV_le hAG hAel haA' ha1'
    have hcA : Nat.card A = 4 := by
      by_contra hne
      have : Nat.card A ≤ 3 := by omega
      have : Nat.card A * Nat.card (fixV A) ≤ 3 * 4 := Nat.mul_le_mul this hfx
      omega
    have hcF : 4 ≤ Nat.card (fixV A) := by
      rw [hcA] at hVle
      omega
    have hFeq := H.fixV_eq_of_card hAG hAel haA' ha1' hcF
    refine ⟨a, hAG haA', ha1', hAel.2 a haA', ?_⟩
    obtain ⟨E, hEG, hEc, hEel, hE⟩ := H.El a (hAG haA') ha1' (hAel.2 a haA')
    have hAE : A ≤ E := by
      intro g hg
      refine (hE g).2 ⟨hAG hg, ?_⟩
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · refine Or.inr ⟨hAel.2 g hg, ?_⟩
        have h1 : fixV A ≤ fixV (Subgroup.zpowers g) := B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hg)
        have h2 := H.FF g (hAG hg) hg1 (hAel.2 g hg)
        have h3 : fixV (Subgroup.zpowers g) = fixV A :=
          (Subgroup.eq_of_le_of_card_ge h1 (by omega)).symm
        rw [h3, hFeq]
    have hAeqE : A = E := Subgroup.eq_of_le_of_card_ge hAE (by omega)
    subst hAeqE
    exact hE
  · rintro ⟨a, haG, ha1, ha2, hA⟩
    obtain ⟨E, hEG, hEc, hEel, hE⟩ := H.El a haG ha1 ha2
    have hAE : A = E := by
      ext g
      rw [hA g, hE g]
    subst hAE
    refine ⟨hEG, ?_, hEel, fun B hB => ?_⟩
    · intro h
      rw [h, Subgroup.card_bot] at hEc
      omega
    ·
      have haA : a ∈ A := (hA a).2 ⟨haG, Or.inr ⟨ha2, rfl⟩⟩
      have hFeq : fixV A = fixV (Subgroup.zpowers a) := by
        apply le_antisymm
        · exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr haA)
        · intro v hv g hg
          rcases ((hA g).1 hg).2 with rfl | ⟨hg2, hgfix⟩
          · rfl
          · have : v ∈ fixV (Subgroup.zpowers g) := by rw [hgfix]; exact hv
            exact mem_fixV_zpowers_iff.mp this
      have hFc : Nat.card (fixV A) = 4 := by rw [hFeq]; exact H.FF a haG ha1 ha2
      rw [hEc, hFc]
      by_cases hB1 : B = ⊥
      · subst hB1
        rw [B1.card_bot_mul_card_fixV, H.card_four]
      · obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
        have hb1' : (b : MulAut V) ≠ 1 := fun h => hb1 (Subtype.ext h)
        have hBcard : Nat.card B ≤ 4 := hEc ▸ Subgroup.card_le_of_le hB
        have hBfx : Nat.card (fixV B) ≤ 4 :=
          H.card_fixV_le (hB.trans hEG) ⟨fun x hx y hy => hEel.1 x (hB hx) y (hB hy),
            fun x hx => hEel.2 x (hB hx)⟩ b.2 hb1'
        calc Nat.card B * Nat.card (fixV B) ≤ 4 * 4 := Nat.mul_le_mul hBcard hBfx
          _ = 4 * 4 := rfl

omit [Finite V] in
theorem fixV_eq_of_isEqFixGroup {a : MulAut V} {E : Subgroup (MulAut V)} (haG : a ∈ G)
    (ha2 : a ^ 2 = 1) (hE : IsEqFixGroup G a E) : fixV E = fixV (Subgroup.zpowers a) := by
  have haE : a ∈ E := (hE a).2 ⟨haG, Or.inr ⟨ha2, rfl⟩⟩
  apply le_antisymm
  · exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr haE)
  · intro v hv g hg
    rcases ((hE g).1 hg).2 with rfl | ⟨hg2, hgfix⟩
    · rfl
    · have : v ∈ fixV (Subgroup.zpowers g) := by rw [hgfix]; exact hv
      exact mem_fixV_zpowers_iff.mp this

include H in
theorem qOf_eq_one (hex : ∃ a ∈ G, a ≠ 1 ∧ a ^ 2 = 1) : qOf G = 1 := by
  obtain ⟨a, haG, ha1, ha2⟩ := hex
  obtain ⟨E, hEG, hEc, hEel, hE⟩ := H.El a haG ha1 ha2
  have hEoff : IsFFStarOffender G E :=
    (H.isFFStarOffender_iff_eqFix E).2 ⟨a, haG, ha1, ha2, hE⟩
  have hFE := fixV_eq_of_isEqFixGroup (G := G) haG ha2 hE
  have hFc : Nat.card (fixV E) = 4 := by rw [hFE]; exact H.FF a haG ha1 ha2
  apply le_antisymm
  · have hA2 : IsA2 G E := hEoff.isA2
    have hquad : IsQuadratic E := by
      unfold IsQuadratic commV
      rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      by_cases hx1 : x = 1
      · subst hx1
        simp
      · obtain ⟨hxG, hx'⟩ := (hE x).1 hx
        rcases hx' with h | ⟨hx2, hxfix⟩
        · exact absurd h hx1
        · have h1 := commV_zpowers_le_fixV_b4 H.sq hx2 (commHom_mem_commV x v)
          rw [hxfix, ← hFE] at h1
          exact h1
    have hr : rAV E ≤ 1 := by
      refine (rAV_le_one_iff H.sq hA2).2 ?_
      rw [H.card_four, hEc, hFc]
    have := (qOf_le_iff (X := G) (r := 1)).2 ⟨E, hA2, hquad, hr⟩
    simpa using this
  · have : ((1 : ℚ) : WithTop ℚ) ≤ qOf G := by
      unfold qOf
      refine le_kq_iff.2 fun A hA2 _ => ?_
      by_contra hlt
      push Not at hlt
      have h1 := (rAV_lt_one_iff H.sq hA2).1 hlt
      obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA2.2.1
      have hb1' : (b : MulAut V) ≠ 1 := fun h => hb1 (Subtype.ext h)
      have h2 := H.E4 A hA2.1 hA2.2.2
      have h3 := H.card_fixV_le hA2.1 hA2.2.2 b.2 hb1'
      rw [H.card_four] at h1
      nlinarith
    simpa using this

end OffHyp

omit [Finite V] in
theorem zpowers_conj_eq (g a : MulAut V) :
    Subgroup.zpowers (g * a * g⁻¹) = B1.conjAut g (Subgroup.zpowers a) := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by rw [conj_zpow]; group⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [conj_zpow, hn]
    group

omit [Finite V] in
theorem eqFix_conj {G : Subgroup (MulAut V)} {a b g : MulAut V} (hg : g ∈ G) (hgab : g * a * g⁻¹ = b)
    {E E' : Subgroup (MulAut V)} (hE : IsEqFixGroup G a E) (hE' : IsEqFixGroup G b E') :
    E' = B1.conjAut g E := by
  ext x
  rw [hE' x, B1.mem_conjAut, hE (g⁻¹ * x * g)]
  have hG : x ∈ G ↔ g⁻¹ * x * g ∈ G := by
    constructor
    · intro hx
      exact G.mul_mem (G.mul_mem (G.inv_mem hg) hx) hg
    · intro hx
      have := G.mul_mem (G.mul_mem hg hx) (G.inv_mem hg)
      simpa [mul_assoc] using this
  have h1 : x = 1 ↔ g⁻¹ * x * g = 1 := by
    constructor
    · rintro rfl; simp
    · intro h
      have : g * (g⁻¹ * x * g) * g⁻¹ = 1 := by rw [h]; simp
      simpa [mul_assoc] using this
  have h2 : x ^ 2 = 1 ↔ (g⁻¹ * x * g) ^ 2 = 1 := by
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      simp only [pow_two]; group
    rw [this]
    constructor
    · intro h; rw [h]; simp
    · intro h
      have : g * (g⁻¹ * x ^ 2 * g) * g⁻¹ = 1 := by rw [h]; simp
      simpa [mul_assoc] using this
  have h3 : fixV (Subgroup.zpowers x) = fixV (Subgroup.zpowers b) ↔
      fixV (Subgroup.zpowers (g⁻¹ * x * g)) = fixV (Subgroup.zpowers a) := by
    have e1 : fixV (Subgroup.zpowers x) =
        (fixV (Subgroup.zpowers (g⁻¹ * x * g))).map g.toMonoidHom := by
      have := fixV_zpowers_conj g (g⁻¹ * x * g)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at this
    have e2 : fixV (Subgroup.zpowers b) = (fixV (Subgroup.zpowers a)).map g.toMonoidHom := by
      rw [← hgab]
      exact fixV_zpowers_conj g a
    rw [e1, e2]
    exact (Subgroup.map_injective g.injective).eq_iff
  rw [← hG, ← h1, ← h2, ← h3]


end CFSG.Quasithin
