module

public import CFSG.RankThree.PartOne.S9.OddCore.TorsionInflate

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.Assembly.RankThreeEven CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

section InflateMain

variable {G : Type*} [Group G]

theorem commutator_map_inl_prod_top {C : Type*} [CommGroup C] (H K : Subgroup G) :
    ⁅H.map (MonoidHom.inl G C), K.prod (⊤ : Subgroup C)⁆ = ⁅H, K⁆.map (MonoidHom.inl G C) := by
  apply le_antisymm
  · refine Subgroup.commutator_le.2 ?_
    rintro _ ⟨h, hh, rfl⟩ ⟨k, c⟩ hk
    refine ⟨⁅h, k⁆, Subgroup.commutator_mem_commutator hh (Subgroup.mem_prod.1 hk).1, ?_⟩
    refine Prod.ext rfl ?_
    change (1 : C) = 1 * c * 1⁻¹ * c⁻¹
    simp
  · rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono le_rfl ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_prod.2 ⟨hk, Subgroup.mem_top _⟩

theorem minimalTwoAction_inflated_gen (hMTAWR3 : MinimalTwoActionWithoutRankThreeFixedGroup)
    {G : Type} [Group G] [Finite G] {C : Type} [CommGroup C] [Finite C] {p q : ℕ}
    {A D R : Subgroup G} (hC : Nat.card C = p)
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hA : Nat.card A = p) (hDinv : R ⊔ A ≤ Subgroup.normalizer (D : Set G))
    (hDq : IsPGroup q D) (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hR2 : IsPGroup 2 R) (hRA : A ≤ Subgroup.normalizer (R : Set G)) (hcomm : ⁅R, A⁆ = R)
    (hRne : R ≠ ⊥) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hmin : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (D : Set G))
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    p = 5 ∧ Nonempty (R ≃* QD32) ∧ ⁅D, R⁆ = D ∧ IsQDShape q D := by
  set ι : G →* G × C := MonoidHom.inl G C with hι
  have hιinj : Function.Injective ι := fun a b h => (Prod.ext_iff.1 h).1
  set A' : Subgroup (G × C) := A.prod ⊤ with hA'
  have hAA' : A.map ι ≤ A' := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_prod.2 ⟨hk, Subgroup.mem_top _⟩
  have hsetting : MinTwoActionSetting p q A' (D.map ι) (R.map ι) := by
    refine ⟨hp, hq, hp3, hq2, hpq, (isElementaryAbelian_prod_top hp hA hC).1,
      (isElementaryAbelian_prod_top hp hA hC).2, ?_, hDq.map ι, ?_, ?_, hR2.map ι, ?_, ?_, ?_, ?_,
      ?_⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨r, hr, rfl⟩
        exact prod_mem_normalizer_map_inl (hDinv (Subgroup.mem_sup_left hr)) 1
      · rintro ⟨a, c⟩ ha
        exact prod_mem_normalizer_map_inl
          (hDinv (Subgroup.mem_sup_right (Subgroup.mem_prod.1 ha).1)) c
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_pow, hDexp d hd, map_one]
    · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hDcl, Subgroup.map_bot]
    · rintro ⟨a, c⟩ ha
      exact prod_mem_normalizer_map_inl (hRA (Subgroup.mem_prod.1 ha).1) c
    · have h := commutator_map_inl_prod_top (C := C) R A
      rw [hcomm] at h
      exact h
    · exact fun h => hRne ((Subgroup.map_eq_bot_iff_of_injective R hιinj).1 h)
    · rw [← Subgroup.map_commutator]
      exact fun h => hRD ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).1 h)
    · intro U hlt hUA hUc
      have hUle : U ≤ ι.range := hlt.le.trans (fun x ⟨r, _, hx⟩ => ⟨r, hx⟩)
      have hU : (U.comap ι).map ι = U := Subgroup.map_comap_eq_self hUle
      have hlt0 : U.comap ι < R := by
        rw [← Subgroup.map_lt_map_iff_of_injective hιinj, hU]
        exact hlt
      have hnorm : A ≤ Subgroup.normalizer ((U.comap ι : Subgroup G) : Set G) := by
        intro a ha
        have h1 := Subgroup.mem_normalizer_iff.1 (hUA (Subgroup.mem_prod.2 ⟨ha, Subgroup.mem_top
          (1 : C)⟩ : (a, (1 : C)) ∈ A'))
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have h3 : ι (a * x * a⁻¹) =
            (a, (1 : C)) * ι x * (a, (1 : C))⁻¹ :=
          Prod.ext rfl (by
            show (1 : C) = 1 * 1 * (1 : C)⁻¹
            rw [inv_one, mul_one, mul_one])
        rw [Subgroup.mem_comap, Subgroup.mem_comap, h3]
        exact h1 (ι x)
      have hcomm0 : ⁅U.comap ι, A⁆ = U.comap ι := by
        apply Subgroup.map_injective hιinj
        have h := commutator_map_inl_prod_top (C := C) (U.comap ι) A
        have hU' : (U.comap ι).map (MonoidHom.inl G (C)) = U := hU
        have h2 : ⁅(U.comap ι).map (MonoidHom.inl G (C)),
            A.prod (⊤ : Subgroup (C))⁆ = U := by
          rw [hU']
          exact hUc
        exact h.symm.trans (h2.trans hU.symm)
      have hcen := hmin _ hlt0 hnorm hcomm0
      rw [← hU]
      rintro _ ⟨u, hu, rfl⟩ _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 (hcen hu) d hd]
  have hrank' : ∀ r ∈ R.map ι, r ≠ 1 →
      CFSG.pRank q ↥(D.map ι ⊓ Subgroup.centralizer ({r} : Set (G × C))) ≤ 2 := by
    rintro _ ⟨s, hs, rfl⟩ hs1
    rw [map_inf_centralizer_singleton ι hιinj, pRank_map_eq ι hιinj hq]
    exact hrank s hs (fun h => hs1 (by rw [h, map_one]))
  obtain ⟨h5, ⟨e⟩, hDR, hshape⟩ := hMTAWR3 _ p q A' (D.map ι) (R.map ι) hsetting hrank'
  refine ⟨h5, ⟨(R.equivMapOfInjective ι hιinj).trans e⟩, ?_, ?_⟩
  · apply Subgroup.map_injective hιinj
    rw [Subgroup.map_commutator]
    exact hDR
  · exact (isQDShape_map_iff ι hιinj q D).1 hshape

theorem minimalTwoAction_inflated (hMTAWR3 : MinimalTwoActionWithoutRankThreeFixedGroup)
    {G : Type} [Group G] [Finite G] {p q : ℕ} {A D R : Subgroup G}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hA : Nat.card A = p) (hDinv : R ⊔ A ≤ Subgroup.normalizer (D : Set G))
    (hDq : IsPGroup q D) (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hR2 : IsPGroup 2 R) (hRA : A ≤ Subgroup.normalizer (R : Set G)) (hcomm : ⁅R, A⁆ = R)
    (hRne : R ≠ ⊥) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hmin : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (D : Set G))
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    p = 5 ∧ Nonempty (R ≃* QD32) ∧ ⁅D, R⁆ = D ∧ IsQDShape q D := by
  have : NeZero p := ⟨hp.ne_zero⟩
  exact minimalTwoAction_inflated_gen hMTAWR3 (C := Multiplicative (ZMod p))
    (by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]) hp hq hp3 hq2 hpq hA hDinv hDq
    hDexp hDcl hR2 hRA hcomm hRne hRD hmin hrank

theorem exists_minimal_action [Finite G] (A D W : Subgroup G)
    (hWA : A ≤ Subgroup.normalizer (W : Set G)) (hcomm : ⁅W, A⁆ = W) (hWD : ⁅W, D⁆ ≠ ⊥) :
    ∃ S : Subgroup G, S ≤ W ∧ A ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, A⁆ = S ∧ ⁅S, D⁆ ≠ ⊥ ∧
      ∀ U : Subgroup G, U < S → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
        U ≤ Subgroup.centralizer (D : Set G) := by
  let P : Subgroup G → Prop := fun S =>
    S ≤ W ∧ A ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, A⁆ = S ∧ ⁅S, D⁆ ≠ ⊥
  obtain ⟨S, hS⟩ := Set.Finite.exists_minimal (s := {S | P S}) (Set.toFinite _)
    ⟨W, le_rfl, hWA, hcomm, hWD⟩
  refine ⟨S, hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2, fun U hU hUA hUc => ?_⟩
  by_contra hcen
  have hUD : ⁅U, D⁆ ≠ ⊥ := fun h => hcen (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)
  exact hU.not_ge (hS.2 (y := U) ⟨hU.le.trans hS.1.1, hUA, hUc, hUD⟩ hU.le)

theorem exists_qd32_below (hMTAWR3 : MinimalTwoActionWithoutRankThreeFixedGroup)
    {G : Type} [Group G] [Finite G] {p q : ℕ} {A D W : Subgroup G}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hA : Nat.card A = p) (hDinv : W ⊔ A ≤ Subgroup.normalizer (D : Set G))
    (hDq : IsPGroup q D) (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥)
    (hW2 : IsPGroup 2 W) (hWA : A ≤ Subgroup.normalizer (W : Set G)) (hcomm : ⁅W, A⁆ = W)
    (hWD : ⁅W, D⁆ ≠ ⊥)
    (hrank : ∀ r ∈ W, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2) :
    ∃ S : Subgroup G, S ≤ W ∧ A ≤ Subgroup.normalizer (S : Set G) ∧ p = 5 ∧
      Nonempty (S ≃* QD32) ∧ ⁅D, S⁆ = D ∧ IsQDShape q D := by
  obtain ⟨S, hSW, hSA, hSc, hSD, hmin⟩ := exists_minimal_action A D W hWA hcomm hWD
  have hSne : S ≠ ⊥ := fun h => hSD (by rw [h, Subgroup.commutator_bot_left])
  have hinv : S ⊔ A ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (hSW.trans (le_sup_left.trans hDinv)) (le_sup_right.trans hDinv)
  obtain ⟨h5, he, hDS, hshape⟩ := minimalTwoAction_inflated hMTAWR3 hp hq hp3 hq2 hpq hA hinv hDq
    hDexp hDcl (hW2.to_le hSW) hSA hSc hSne hSD hmin (fun r hr hr1 => hrank r (hSW hr) hr1)
  exact ⟨S, hSW, hSA, h5, he, hDS, hshape⟩

end InflateMain

end CFSG.RankThree.PartOne.OddCore37
