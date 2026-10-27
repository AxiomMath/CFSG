module

public import CFSG.Quasithin.Background.GoldschmidtShultStatements
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.QuasithinUnique CFSG.ShultStronglyClosedTI
open scoped MatrixGroups

theorem isSylowTwoOf_inf_normal {G : Type*} [Group G] [Finite G] {T L : Subgroup G} [L.Normal]
    (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T ⊓ L) L := by
  refine ⟨inf_le_right, hT.2.1.to_inf_left, ?_⟩
  have h1 : (T ⊓ L).relIndex T * T.relIndex (T ⊔ L) = (T ⊓ L).relIndex (T ⊔ L) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (T ⊓ L).relIndex L * L.relIndex (T ⊔ L) = (T ⊓ L).relIndex (T ⊔ L) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : L.relIndex (T ⊔ L) = L.relIndex T := Subgroup.relIndex_sup_right T L
  have h4 : (T ⊓ L).relIndex T = L.relIndex T := Subgroup.inf_relIndex_left T L
  have hne : (T ⊓ L).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2' : (T ⊓ L).relIndex L * (T ⊓ L).relIndex T = (T ⊓ L).relIndex (T ⊔ L) := by
    rw [← h2, h3, h4]
  have h5 : (T ⊓ L).relIndex L = T.relIndex (T ⊔ L) := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) ?_
    calc (T ⊓ L).relIndex T * (T ⊓ L).relIndex L
        = (T ⊓ L).relIndex L * (T ⊓ L).relIndex T := mul_comm _ _
      _ = (T ⊓ L).relIndex (T ⊔ L) := h2'
      _ = (T ⊓ L).relIndex T * T.relIndex (T ⊔ L) := h1.symm
  have h6 : T.relIndex (T ⊔ L) * (T ⊔ L).index = T.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h7 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  have hodd : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [h7] at this
  have h8 : ¬ 2 ∣ T.relIndex (T ⊔ L) := fun hd => hodd (h6 ▸ Dvd.dvd.mul_right hd _)
  change ¬ 2 ∣ (T ⊓ L).relIndex L
  rwa [h5]

theorem eq_one_of_mem_odd {X : Type*} [Group X] {Z : Subgroup X} (hZ : Odd (Nat.card Z)) {x : X}
    (hx : x ∈ Z) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hx2
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Z) := (Nat.coprime_two_left.mpr hZ).pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem card_eq_of_omegaOne {X : Type} [Group X] [Finite X] {Z : Subgroup X} [Z.Normal]
    (hZ : Odd (Nat.card Z)) {P : Sylow 2 X} {W : Subgroup X} (hWP : W ≤ (P : Subgroup X))
    (hWel : IsElemAbelian 2 W) (hΩ : ∀ x ∈ (P : Subgroup X), x ^ 2 = 1 → x ∈ W) {q : ℕ}
    (hS : ∀ Q : Sylow 2 (X ⧸ Z), HasFieldScalarStructure
      ((CFSG.omega₁ (G := (Q : Subgroup (X ⧸ Z))) (p := 2)).map
        (Q : Subgroup (X ⧸ Z)).subtype) q) :
    Nat.card W = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  let Q : Sylow 2 (X ⧸ Z) := P.mapSurjective hπ
  have hQ : (Q : Subgroup (X ⧸ Z)) = (P : Subgroup X).map π := Sylow.coe_mapSurjective hπ P
  have hΩQ : (CFSG.omega₁ (G := (Q : Subgroup (X ⧸ Z))) (p := 2)).map
      (Q : Subgroup (X ⧸ Z)).subtype = W.map π := by
    rw [SuzukiLayerKernel.map_omega₁_subtype]
    apply le_antisymm
    · refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨hyQ, hy2⟩
      rw [hQ] at hyQ
      obtain ⟨p, hpP, rfl⟩ := hyQ
      have hp2 : p ^ 2 = 1 := by
        have hmem : p ^ 2 ∈ Z :=
          (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hy2)
        obtain ⟨k, hk⟩ := P.isPGroup' ⟨p, hpP⟩
        have hpk : p ^ 2 ^ k = 1 := by
          have := congrArg (fun z : ↥(P : Subgroup X) => (z : X)) hk
          simpa using this
        exact eq_one_of_mem_odd hZ hmem ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hpk, one_pow]⟩
      exact ⟨p, hΩ p hpP hp2, rfl⟩
    · rintro y ⟨w, hw, rfl⟩
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · rw [hQ]
        exact ⟨w, hWP hw, rfl⟩
      · rw [← map_pow, hWel.2 w hw, map_one]
  have hinj : Function.Injective (π.domRestrict W) := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have hwZ : (w : X) ∈ Z := (QuotientGroup.eq_one_iff _).1 hw
    exact Subtype.ext (eq_one_of_mem_odd hZ hwZ ⟨1, by simpa using hWel.2 w w.2⟩)
  have hcard : Nat.card W = Nat.card (W.map π) := by
    have := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rwa [MonoidHom.domRestrict_range] at this
  rw [hcard, ← hΩQ]
  exact (hS Q).card_eq

theorem benderQuasisimple_of_hull {G : Type} [Group G] [Finite G]
    {T V L : Subgroup G} [L.Normal] (hT : IsSylowTwoOf T ⊤) (hVL : V ≤ L)
    (hVel : IsElemAbelian 2 V) (hH : IsBenderHull L) (hΩ : IsOmegaOne V (T ⊓ L)) :
    ∃ f : ℕ, Nat.card V = 2 ^ f ∧ IsBenderQuasisimple L f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hH.2.1]
    exact CFSG.ComponentClassification.OddCore.odd_card ↥L
  have hsyl := isSylowTwoOf_inf_normal (L := L) hT
  obtain ⟨P, hP⟩ := exists_sylow_subgroupOf hsyl.1 hsyl.2.1 hsyl.2.2
  have hWP : V.subgroupOf L ≤ (P : Subgroup ↥L) := by
    rw [hP]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hΩ.1 (Subgroup.mem_subgroupOf.mp hx))
  have hWel : IsElemAbelian 2 (V.subgroupOf L) := by
    constructor
    · apply isMulCommutative_iff.mpr
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : V => (a : G)) (isMulCommutative_iff.mp hVel.1
        (⟨((a : L) : G), a.property⟩ : V) (⟨((b : L) : G), b.property⟩ : V))
    · intro a ha
      exact Subtype.ext (hVel.2 a ha)
  have hΩ' : ∀ x ∈ (P : Subgroup ↥L), x ^ 2 = 1 → x ∈ V.subgroupOf L := by
    intro x hx hx2
    rw [hP] at hx
    exact Subgroup.mem_subgroupOf.mpr (hΩ.2 (x : G) hx (by simpa using congrArg Subtype.val hx2))
  have hcardW : Nat.card V = Nat.card (V.subgroupOf L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).symm.toEquiv
  rcases hH.2.2 with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨P₀, hP₀⟩ := linear_standard f hf
    have hcard := card_eq_of_omegaOne (Z := Subgroup.center ↥L) hZodd hWP hWel hΩ'
      (fun Q => hasFieldScalarStructure_omega₁_of_mulEquiv e P₀ hP₀ Q)
    exact ⟨f, hcardW.trans hcard, hH.1, hH.2.1, Or.inl ⟨hf, ⟨e⟩⟩⟩
  · obtain ⟨P₀, hP₀⟩ := unitary_standard f hf
    have := finite_psu3 f
    have hcard := card_eq_of_omegaOne (Z := Subgroup.center ↥L) hZodd hWP hWel hΩ'
      (fun Q => hasFieldScalarStructure_omega₁_of_mulEquiv e P₀ hP₀ Q)
    exact ⟨f, hcardW.trans hcard, hH.1, hH.2.1, Or.inr (Or.inl ⟨hf, ⟨e⟩⟩)⟩
  · obtain ⟨P₀, hP₀⟩ := suzuki_standard a ha
    have := finite_sz a
    have hcard := card_eq_of_omegaOne (Z := Subgroup.center ↥L) hZodd hWP hWel hΩ'
      (fun Q => hasFieldScalarStructure_omega₁_of_mulEquiv e P₀ hP₀ Q)
    exact ⟨2 * a + 1, hcardW.trans hcard, hH.1, hH.2.1, Or.inr (Or.inr ⟨a, ha, rfl, ⟨e⟩⟩)⟩

end CFSG.Quasithin.Shult
