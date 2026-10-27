module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqCases
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqOrder

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped commutatorElement

namespace Lem1227Lt

section Simple

theorem center_eq_bot_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

theorem pCore_le_ker_of_surjective_simple {L X : Type*} [Group L] [Finite L] [Group X]
    [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (φ : L →* X)
    (hφ : Function.Surjective φ) : CFSG.pCore 2 L ≤ φ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_surjective φ hφ
  have hN : ((CFSG.pCore 2 L).map φ).Normal := CFSG.pCore_normal.map φ hφ
  rcases hN.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have h2 : IsPGroup 2 ((CFSG.pCore 2 L).map φ) := CFSG.pCore_isPGroup.map φ
    rw [h] at h2
    have h3 : IsPGroup 2 X := h2.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent X := h3.isNilpotent
    have hs : Group.IsSolvable X := inferInstance
    obtain ⟨a, b, hab⟩ := hX
    have : Nontrivial X := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hperf : commutator X = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h0 | h1
      · exfalso
        apply hab
        have hmem : ⁅a, b⁆ ∈ commutator X :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      · exact h1
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := X)).ne hperf

end Simple

section Star

variable {G : Type} [Group G] [Finite G] {T K H M₀ : Subgroup G}

theorem kstar_equiv (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) (ψ : ↥K →* X) (hψ : Function.Surjective ψ) :
    Nonempty (↥(E2.star M₀ H K) ≃* X) ∧
      ∀ k : ↥K, ψ k = 1 ↔ (k : G) ∈ kerIn M₀ H := by
  have hle := pCore_le_ker_of_surjective_simple hX ψ hψ
  have : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  set ψ' : (↥K ⧸ CFSG.pCore 2 ↥K) →* X := QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ hle with hψ'
  have hψ's : Function.Surjective ψ' := QuotientGroup.lift_surjective_of_surjective _ ψ hψ hle
  obtain ⟨hkerc, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq hX ψ' hψ's
  refine ⟨nonempty_star_equiv hKH hHK hmin hker eQ, fun k => ?_⟩
  rw [mem_kerIn_iff_central hKH hHK hker k, ← hkerc, MonoidHom.mem_ker]
  rfl

theorem inner_of_hinner (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hmin : MinParabolic H T M₀) (hker : KerChar M₀ H K)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {X : Type} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) (ψ : ↥K →* X) (hψ : Function.Surjective ψ)
    (hinner : ∀ t : ↥T, ∃ k : ↥K, ∀ x : ↥K,
      ψ (K.normalizerMonoidHom ⟨(t : G), hTK t.2⟩ x) = ψ (k * x * k⁻¹)) :
    ∀ d ∈ E2.star M₀ H T, ∃ k ∈ E2.star M₀ H K, ∀ x ∈ E2.star M₀ H K,
      d * x * d⁻¹ = k * x * k⁻¹ := by
  obtain ⟨-, hψk⟩ := kstar_equiv hKH hHK hmin hker hq hX ψ hψ
  refine inner_star (M₀ := M₀) (T := T) hKH fun t ht => ?_
  obtain ⟨k, hk⟩ := hinner ⟨t, ht⟩
  refine ⟨(k : G), k.2, fun x hx => ?_⟩
  let xK : ↥K := ⟨x, hx⟩
  let u : ↥K := k⁻¹ * K.normalizerMonoidHom ⟨t, hTK ht⟩ xK * k * xK⁻¹
  have hu : (u : G) = ((k : G)⁻¹ * t) * x * ((k : G)⁻¹ * t)⁻¹ * x⁻¹ := by
    show ((k : G))⁻¹ * (t * x * t⁻¹) * k * x⁻¹ = _
    group
  rw [← hu, ← hψk]
  simp only [u, map_mul, map_inv, hk xK]
  group

theorem false_of_card_168 (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    {X : Type} [Group X] [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hcard : Nat.card X = 168) (ψ : ↥K →* X) (hψ : Function.Surjective ψ)
    (hinner : ∀ t : ↥T, ∃ k : ↥K, ∀ x : ↥K,
      ψ (K.normalizerMonoidHom ⟨(t : G), hTK t.2⟩ x) = ψ (k * x * k⁻¹)) : False := by
  obtain ⟨⟨eS⟩, -⟩ := kstar_equiv hKH hHK hmin hker hq hX ψ hψ
  have hinn := inner_of_hinner hKH hHK hmin hker hq hTK hX ψ hψ hinner
  have : IsSimpleGroup ↥(E2.star M₀ H K) := eS.isSimpleGroup
  have hcardK : Nat.card ↥(E2.star M₀ H K) = 168 := by
    rw [Nat.card_congr eS.toEquiv]
    exact hcard
  have hZK : Subgroup.center ↥(E2.star M₀ H K) = ⊥ :=
    Lem8.center_eq_bot_of_mulEquiv eS (center_eq_bot_of_simple hX)
  obtain ⟨hT2, hSyl⟩ := isSylowTwoOf_star hKH hHK hmin
  have hnn : ¬ E2.star M₀ H K ≤ Subgroup.normalizer ((E2.star M₀ H (T ⊓ K) :
      Subgroup (E2.StarQuot M₀ H)) : Set (E2.StarQuot M₀ H)) :=
    not_le_normalizer_of_simple hSyl (by rw [hcardK]; norm_num)
      (not_isPGroup_two_of_three_dvd (by rw [hcardK]; norm_num))
  have hD := not_isDiagramNontrivial_of_inner hSyl hnn (star_le_normalizer hTK)
    (star_le_normalizer_star (le_normalizer_inf_self hTK)) hinn
  have hA := autCard_le_eight_of_inner hT2 (star_le_normalizer hTK) hZK hcardK hinn
  rcases E22TwoAlt.of_card_168 hlist hcardK with ⟨-, hD'⟩ | ⟨-, hA'⟩
  · exact hD hD'
  · exact absurd hA' (not_lt.2 hA)

theorem false_of_card_360 (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hlist : E22TwoAlt ↥(E2.star M₀ H K)
      (E2.IsDiagramNontrivial (E2.star M₀ H T) (E2.star M₀ H K) (E2.star M₀ H (T ⊓ K)))
      (8 < E2.autCard (E2.star M₀ H T) (E2.star M₀ H K))
      (E2.InducesOuter (E2.star M₀ H T) (E2.star M₀ H K)))
    (ψ : ↥K →* ↥(alternatingGroup (Fin 6))) (hψ : Function.Surjective ψ)
    (P : Subgroup ↥(alternatingGroup (Fin 6))) (hP : P ≠ ⊤) (hPidx : P.index ≤ 44)
    (hstable : ∀ t : ↥T, ∀ x : ↥K,
      ψ (K.normalizerMonoidHom ⟨(t : G), hTK t.2⟩ x) ∈ P ↔ ψ x ∈ P) : False := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := Seven.alt6_simple
  obtain ⟨⟨eS⟩, hψk⟩ := kstar_equiv hKH hHK hmin hker hq Seven.alt6_nonabelian ψ hψ
  have hcard6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hcardK : Nat.card ↥(E2.star M₀ H K) = 360 := by
    rw [Nat.card_congr eS.toEquiv]
    exact hcard6
  set W : Subgroup G := (P.comap ψ).map K.subtype with hW
  have hmemW : ∀ x : ↥K, (x : G) ∈ W ↔ ψ x ∈ P := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hWK : W ≤ K := Subgroup.map_subtype_le _
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hK' := Subgroup.mem_normalizer_iff.1 (hTK ht) g
    constructor
    · intro hg
      have hgK : g ∈ K := hWK hg
      have h1 := (hmemW ⟨g, hgK⟩).1 hg
      have h2 := (hstable ⟨t, ht⟩ ⟨g, hgK⟩).2 h1
      exact (hmemW (K.normalizerMonoidHom ⟨t, hTK ht⟩ ⟨g, hgK⟩)).2 h2
    · intro hg
      have hgK : g ∈ K := hK'.2 (hWK hg)
      have h2 := (hmemW (K.normalizerMonoidHom ⟨t, hTK ht⟩ ⟨g, hgK⟩)).1 hg
      exact (hmemW ⟨g, hgK⟩).2 ((hstable ⟨t, ht⟩ ⟨g, hgK⟩).1 h2)
  have hJW : K ⊓ kerIn M₀ H ≤ Subgroup.normalizer (W : Set G) := by
    rintro x ⟨hxK, hxJ⟩
    refine Subgroup.le_normalizer ((hmemW ⟨x, hxK⟩).2 ?_)
    rw [(hψk ⟨x, hxK⟩).2 hxJ]
    exact P.one_mem
  have hKW : ¬ K ≤ Subgroup.normalizer (W : Set G) := by
    intro hKN
    have hnorm : P.Normal := by
      refine ⟨fun p hp g => ?_⟩
      obtain ⟨a, rfl⟩ := hψ p
      obtain ⟨k, rfl⟩ := hψ g
      have haW : (a : G) ∈ W := (hmemW a).2 hp
      have h1 := (Subgroup.mem_normalizer_iff.1 (hKN k.2) a).1 haW
      have h2 : ((k * a * k⁻¹ : ↥K) : G) ∈ W := h1
      have := (hmemW (k * a * k⁻¹)).1 h2
      simpa [map_mul] using this
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h0 | h1
    · rw [h0, Subgroup.index_bot, hcard6] at hPidx
      omega
    · exact hP h1
  have hidx : (K ⊓ Subgroup.normalizer (W : Set G)).relIndex K ≤ 44 := by
    have h1 : W ≤ K ⊓ Subgroup.normalizer (W : Set G) := le_inf hWK Subgroup.le_normalizer
    have h2 : (K ⊓ Subgroup.normalizer (W : Set G)).relIndex K ∣ W.relIndex K :=
      Subgroup.relIndex_dvd_of_le_left K h1
    have h3 : W.relIndex K = P.index := by
      rw [Subgroup.relIndex, hW]
      show (((P.comap ψ).map K.subtype).comap K.subtype).index = P.index
      rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective,
        Subgroup.index_comap_of_surjective _ hψ]
    have hpos : 0 < W.relIndex K := by
      rw [h3]
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos h2).trans (h3 ▸ hPidx)
  have hdiag := not_isDiagramNontrivial_of_stable_subgroup hKH hHK hmin hTK ⟨eS⟩ hTW hJW hKW hidx
  obtain ⟨-, hD⟩ := E22TwoAlt.of_card_360 hlist hcardK
  exact hdiag hD

theorem false_of_card_20160 (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hmin : MinParabolic H T M₀)
    (hker : KerChar M₀ H K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hfam : B69.E22Fam ↥(E2.star M₀ H K))
    {X : Type} [Group X] [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (ψ : ↥K →* X)
    (hψ : Function.Surjective ψ) : False := by
  obtain ⟨⟨eS⟩, -⟩ := kstar_equiv hKH hHK hmin hker hq hX ψ hψ
  have e2 : ↥(E2.star M₀ H K) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := eS.trans e
  have hN : Nat.card ↥(E2.star M₀ H K) = 20160 := by
    rw [Nat.card_congr e2.toEquiv]
    exact card_sl_four_zmod_two
  exact false_of_lieModel_four hfam (lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e2) hN

end Star

section Positive

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem lieModel_of_surjective_alt5
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (ψ : ↥K →* ↥(alternatingGroup (Fin 5)))
    (hψ : Function.Surjective ψ) : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 2 2 := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := Seven.alt5_simple
  have hle := pCore_le_ker_of_surjective_simple Seven.alt5_nonabelian ψ hψ
  have : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  set ψ' : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(alternatingGroup (Fin 5)) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥K) ψ hle with hψ'
  have hψ's : Function.Surjective ψ' := QuotientGroup.lift_surjective_of_surjective _ ψ hψ hle
  obtain ⟨-, eQ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq Seven.alt5_nonabelian ψ'
    hψ's
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  obtain ⟨h58, -, -⟩ := five_alternating_small_central_cover_reduction hq hodd (Or.inl rfl) eQ
  obtain ⟨-, ⟨eK⟩⟩ := h58 (Or.inl rfl)
  exact Or.inl ⟨by decide,
    CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨eK⟩⟩

end Positive

end Lem1227Lt

end CFSG.Quasithin.H13
