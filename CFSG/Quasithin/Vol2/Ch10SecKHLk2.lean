module

public import CFSG.Quasithin.Vol2.Ch10SecKHLk2D
public import CFSG.Quasithin.Vol2.Ch10SecB5EvFact
public import CFSG.Quasithin.Vol2.Ch10SecKHLk2C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits SteinbergCH

namespace C10KH

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {X U : Subgroup G} (hUX : U ≤ Subgroup.normalizer (X : Set G))
    {t : G} (htX : t ∈ Subgroup.normalizer (X : Set G))
    (htU : t ∈ Subgroup.normalizer (U : Set G)) :
    t ∈ Subgroup.normalizer ((X ⊔ U : Subgroup G) : Set G) := by
  have hconj : ∀ s ∈ Subgroup.normalizer (X : Set G), s ∈ Subgroup.normalizer (U : Set G) →
      ∀ y ∈ X ⊔ U, s * y * s⁻¹ ∈ X ⊔ U := by
    intro s hsX hsU y hy
    have hy' : y ∈ ((X ⊔ U : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X U hUX] at hy'
    obtain ⟨x, hx, u, hu, rfl⟩ := hy'
    have he : s * (x * u) * s⁻¹ = (s * x * s⁻¹) * (s * u * s⁻¹) := by group
    rw [he]
    exact Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.1 hsX x).1 hx)
      ((Subgroup.mem_normalizer_iff.1 hsU u).1 hu)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hconj t htX htU y, fun h => ?_⟩
  have h' := hconj t⁻¹ (Subgroup.inv_mem _ htX) (Subgroup.inv_mem _ htU) _ h
  simpa [mul_assoc] using h'

theorem conj_inv_mul_conj_mem {K : Subgroup G} {g m : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hm : m ∈ Subgroup.normalizer (K : Set G))
    (h : SteinbergBS.conjQuotientHom K (CFSG.pCore 2 ↥K) ⟨g, hg⟩ =
      SteinbergBS.conjQuotientHom K (CFSG.pCore 2 ↥K) ⟨m, hm⟩) {l : G} (hl : l ∈ K) :
    (g * l * g⁻¹)⁻¹ * (m * l * m⁻¹) ∈ (CFSG.pCore 2 ↥K).map K.subtype := by
  have h1 := DFunLike.congr_fun h (QuotientGroup.mk ⟨l, hl⟩)
  simp only [SteinbergBS.conjQuotientHom, MonoidHom.coe_mk, OneHom.coe_mk,
    QuotientGroup.congr_mk] at h1
  have h2 := QuotientGroup.eq.1 h1
  refine ⟨_, h2, ?_⟩
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

end C10KH

open C10KH in
theorem fact10_2_5Lk2 : Fact10_2_5Lk2 := by
  intro G _ _ K T X k hk hQ hT hTK hU hAut hXK hTX _ h9 _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := T ⊓ K with hUdef
  set W := pCoreOf 2 (X ⊔ U) with hWdef
  have hEN : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hsurj := conjLBar_surjective hQ hT hTK hEN hAut
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := hQ
  have hF2 : Nat.card F = 2 := by simpa using hF
  set e := e₀.trans (Setup.Family.statedProjSL_equiv_of_card_two k F hF2)
  set θ : ↥K →* Matrix.SpecialLinearGroup (Fin k) (ZMod 2) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hθdef
  have hθ : Function.Surjective θ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 θ.ker := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le fun x hx => ?_
    have hx' : e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) = 1 := hx
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  have hUX : U ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hTX
  have hUK : U ≤ K := inf_le_right
  have hJK : X ⊔ U ≤ K := sup_le hXK hUK
  have hKcase : ∀ m ∈ K, (∀ w ∈ W, m * w * m⁻¹ ∈ U) → m ∈ X ⊔ U := fun m hm h =>
    mem_sup_of_conj_le_of_le hk hθ hker hU hXK hUX h9 hm h
  set O := (CFSG.pCore 2 ↥K).map K.subtype with hOdef
  have hOp : O = pCoreOf 2 K := by rw [hOdef, pCoreOf]
  have hOU : O ≤ U :=
    hOp ▸ pCoreOf_le_of_isSylowTwoOf' hU le_rfl (hUK.trans Subgroup.le_normalizer)
  have hOW : O ≤ W := by
    refine le_pCoreOf_of_le_normalizer 2 (hOU.trans le_sup_right) ?_ ?_
    · exact hJK.trans (hOp ▸ le_normalizer_pCoreOf 2 K)
    · exact hOp ▸ pCoreOf_isPGroup 2 K
  have hWU : W ≤ U :=
    pCoreOf_le_of_isSylowTwoOf' hU hJK (le_sup_right.trans Subgroup.le_normalizer)
  refine ⟨fun g hg hle => ?_, fun g hg h3 => ?_⟩
  ·
    obtain ⟨m, hm⟩ := hsurj (SteinbergBS.conjQuotientHom K (CFSG.pCore 2 ↥K) ⟨g, hg⟩)
    have hmN : (m : G) ∈ Subgroup.normalizer (K : Set G) := hEN m.2
    have hgm : SteinbergBS.conjQuotientHom K (CFSG.pCore 2 ↥K) ⟨g, hg⟩ =
        SteinbergBS.conjQuotientHom K (CFSG.pCore 2 ↥K) ⟨m, hmN⟩ := hm.symm
    have hmKT : (m : G) ∈ ((K ⊔ T : Subgroup G) : Set G) := m.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hmKT
    obtain ⟨c, hc, t, ht, hct⟩ := hmKT
    have htW : t ∈ Subgroup.normalizer (W : Set G) := by
      have htU : t ∈ Subgroup.normalizer (U : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨hyT, hyK⟩
          exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
            (Subgroup.mem_normalizer_iff.1 (hTK ht) y).1 hyK⟩
        · rintro ⟨hyT, hyK⟩
          have h1 : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ ∈ T :=
            T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) (T.inv_mem (T.inv_mem ht))
          have h2 := (Subgroup.mem_normalizer_iff.1 (hTK (T.inv_mem ht)) _).1 hyK
          have he : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
          rw [he] at h1 h2
          exact ⟨h1, h2⟩
      exact normalizer_le_normalizer_pCoreOf 2 _ (mem_normalizer_sup hUX (hTX ht) htU)
    have hcJ : c ∈ X ⊔ U := by
      refine hKcase c hc fun w hw => ?_
      have hw' : t⁻¹ * w * t⁻¹⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htW) w).1 hw
      have h1 := conj_inv_mul_conj_mem hg hmN hgm (hWU.trans hUK hw')
      have h2 : g * (t⁻¹ * w * t⁻¹⁻¹) * g⁻¹ ∈ U := hle ⟨_, hw', rfl⟩
      have he : c * w * c⁻¹ = (g * (t⁻¹ * w * t⁻¹⁻¹) * g⁻¹) *
          ((g * (t⁻¹ * w * t⁻¹⁻¹) * g⁻¹)⁻¹ * ((m : G) * (t⁻¹ * w * t⁻¹⁻¹) * (m : G)⁻¹)) := by
        rw [← hct]
        group
      rw [he]
      exact U.mul_mem h2 (hOU h1)
    have hcW : c ∈ Subgroup.normalizer (W : Set G) := le_normalizer_pCoreOf 2 _ hcJ
    have hgW : W.map (MulAut.conj g).toMonoidHom ≤ W := by
      rintro _ ⟨w, hw, rfl⟩
      have h1 := conj_inv_mul_conj_mem hg hmN hgm (hWU.trans hUK hw)
      have hmw : (m : G) * w * (m : G)⁻¹ ∈ W := by
        have h2 := (Subgroup.mem_normalizer_iff.1 htW w).1 hw
        have h3 := (Subgroup.mem_normalizer_iff.1 hcW _).1 h2
        have he : (m : G) * w * (m : G)⁻¹ = c * (t * w * t⁻¹) * c⁻¹ := by
          rw [← hct]
          group
        rw [he]
        exact h3
      have he : (MulAut.conj g).toMonoidHom w =
          ((m : G) * w * (m : G)⁻¹) * ((g * w * g⁻¹)⁻¹ * ((m : G) * w * (m : G)⁻¹))⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [he]
      exact W.mul_mem hmw (W.inv_mem (hOW h1))
    refine Subgroup.eq_of_le_of_card_ge hgW ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  · obtain ⟨hgK, hgN⟩ := hg
    refine mem_of_orderOf_eq_three hU.2.1 hUX (hKcase g hgK fun w hw => ?_) h3
    exact hWU ((Subgroup.mem_normalizer_iff.1 hgN w).1 hw)

end CFSG.Quasithin.Vol2.Ch10.SecB
