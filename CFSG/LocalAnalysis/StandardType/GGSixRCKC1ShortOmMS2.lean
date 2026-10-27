module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1ShortOmMRefl
public import CFSG.ClassicalGroups.PCoreSection
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType.RCKC1

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
  CFSG.ClassicalGroups.PCoreSection CFSG.Open

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem rckSOmM2_exists_singular [CharP K 2] [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {e w w₁ : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hew : polar Q e w = 0) (hw : Q w ≠ 0) (hw₁ : w₁ = w + Q w • e) {y : V}
    (hye : polar Q y e = 0) (hyw : polar Q y w = 0) (hyL : y ∉ Submodule.span K {e, w₁}) :
    ∃ u : V, polar Q u e = 0 ∧ polar Q u w = 0 ∧ Q u = 0 ∧ polar Q y u ≠ 0 := by
  have hwe : polar Q w e = 0 := by rw [polar_comm]; exact hew
  have hww : polar Q w w = 0 := polar_self_eq_zero Q w
  have hee : polar Q e e = 0 := polar_self_eq_zero Q e
  have hw1e : polar Q w₁ e = 0 := by
    rw [hw₁, polar_add_left, polar_smul_left_eq, hwe, hee]; ring
  have hw1w : polar Q w₁ w = 0 := by
    rw [hw₁, polar_add_left, polar_smul_left_eq, hww, hew]; ring
  have hQw1 : Q w₁ = Q w := by
    have h := rckSOmMR_quad_span he hew (Q w) 1
    have h' : w₁ = Q w • e + (1 : K) • w := by rw [hw₁, one_smul]; abel
    rw [h', h]; ring
  have h1 : ∃ u₁ : V, polar Q u₁ e = 0 ∧ polar Q u₁ w = 0 ∧ polar Q y u₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨α, l, hd⟩ := rckSOmMR_exists_of_orth hQ he he0 hew hw (d := y) (fun x hx1 hx2 => by
      rw [polar_comm]; exact hcon x hx1 hx2)
    apply hyL
    rw [hd]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (by simp)
    · have hw' : w = w₁ - Q w • e := by rw [hw₁]; abel
      rw [hw']
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨u₁, hu1e, hu1w, hyu1⟩ := h1
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q u₁ / Q w)
  have hu1w1 : polar Q u₁ w₁ = 0 := by
    rw [hw₁, polar_add_right, polar_smul_right_eq, hu1w, hu1e]; ring
  refine ⟨u₁ + b • w₁, ?_, ?_, ?_, ?_⟩
  · rw [polar_add_left, polar_smul_left_eq, hu1e, hw1e]; ring
  · rw [polar_add_left, polar_smul_left_eq, hu1w, hw1w]; ring
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQw1, polar_smul_right_eq, hu1w1]
    have hbb : Q u₁ = b * b * Q w := by
      rw [← hb]; field_simp
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (-1 : K) * hbb + (Q u₁) * h2
  · have hyw1 : polar Q y w₁ = 0 := by
      rw [hw₁, polar_add_right, polar_smul_right_eq, hyw, hye]; ring
    rw [polar_add_right, polar_smul_right_eq, hyw1]
    simpa using hyu1

theorem rckSOmM2_pCore_perp [CharP K 2] [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V))
    (hρ : Function.Injective ρ) (hρO : ∀ g, ρ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE : ∀ u w, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ ρ.range) {e w : V} (he : Q e = 0)
    (he0 : e ≠ 0) (hew : polar Q e w = 0) (hw : Q w ≠ 0) {x : G} (hx : ρ x = eichler Q e w)
    (hfix : ∀ t ∈ Subgroup.centralizer ({x} : Set G),
      ρ t e = e ∧ ∃ a : K, ρ t (w + Q w • e) = (w + Q w • e) + a • e)
    {t : G} (ht : t ∈ pCoreOf 2 (Subgroup.centralizer ({x} : Set G))) :
    ∀ y, polar Q y e = 0 → polar Q y w = 0 → ∃ c : K, ρ t y - y = c • e := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  have hwe : polar Q w e = 0 := by rw [polar_comm]; exact hew
  have hww : polar Q w w = 0 := polar_self_eq_zero Q w
  have hee : polar Q e e = 0 := polar_self_eq_zero Q e
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : V, w₁ = w + Q w • e := ⟨_, rfl⟩
  have hw1e : polar Q w₁ e = 0 := by
    rw [hw₁, polar_add_left, polar_smul_left_eq, hwe, hee]; ring
  have hw1w : polar Q w₁ w = 0 := by
    rw [hw₁, polar_add_left, polar_smul_left_eq, hww, hew]; ring
  have hew1 : polar Q e w₁ = 0 := by rw [polar_comm]; exact hw1e
  have hQw1 : Q w₁ = Q w := by
    have h := rckSOmMR_quad_span he hew (Q w) 1
    have h' : w₁ = Q w • e + (1 : K) • w := by rw [hw₁, one_smul]; abel
    rw [h', h]; ring
  have hw' : w = w₁ - Q w • e := by rw [hw₁]; abel
  obtain ⟨P, hPmem⟩ : ∃ P : Submodule K V,
      ∀ y, y ∈ P ↔ polar Q y e = 0 ∧ polar Q y w = 0 :=
    ⟨{ carrier := {y | polar Q y e = 0 ∧ polar Q y w = 0}
       add_mem' := fun {a b} ha hb => by
         show polar Q (a + b) e = 0 ∧ polar Q (a + b) w = 0
         exact ⟨by rw [polar_add_left, ha.1, hb.1, add_zero],
           by rw [polar_add_left, ha.2, hb.2, add_zero]⟩
       zero_mem' := by
         show polar Q 0 e = 0 ∧ polar Q 0 w = 0
         exact ⟨by rw [polar_zero_left], by rw [polar_zero_left]⟩
       smul_mem' := fun c y hy => by
         show polar Q (c • y) e = 0 ∧ polar Q (c • y) w = 0
         exact ⟨by rw [polar_smul_left_eq, hy.1, mul_zero],
           by rw [polar_smul_left_eq, hy.2, mul_zero]⟩ }, fun y => Iff.rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : Submodule K V, L = Submodule.span K {e, w₁} := ⟨_, rfl⟩
  have hLmem : ∀ y, y ∈ L ↔ ∃ a b : K, a • e + b • w₁ = y := by
    intro y; rw [hLdef]; exact Submodule.mem_span_pair
  have heL : e ∈ L := (hLmem e).mpr ⟨1, 0, by simp⟩
  have hw1L : w₁ ∈ L := (hLmem w₁).mpr ⟨0, 1, by simp⟩
  have hLP : L ≤ P := by
    intro y hy
    obtain ⟨a, b, rfl⟩ := (hLmem y).mp hy
    refine (hPmem _).mpr ⟨?_, ?_⟩
    · rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hee, hw1e]; ring
    · rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hew, hw1w]; ring
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = Subgroup.centralizer ({x} : Set G) := ⟨_, rfl⟩
  have hfix' : ∀ s ∈ S, ρ s e = e ∧ ∃ a : K, ρ s w₁ = w₁ + a • e := by
    intro s hs
    rw [hSdef] at hs
    obtain ⟨h1, a, h2⟩ := hfix s hs
    exact ⟨h1, a, by rw [hw₁]; exact h2⟩
  have hlin : IsLinearAction K (fun (g : G) (v : V) => ρ g v) :=
    { one := fun v => by simp
      mul := fun g h v => by simp
      add := fun g v w => by simp
      smul := fun g c v => by simp }
  have hLinv : ∀ s ∈ S, ∀ y ∈ L, ρ s y ∈ L := by
    intro s hs y hy
    obtain ⟨h1, a', h2⟩ := hfix' s hs
    obtain ⟨a, b, rfl⟩ := (hLmem y).mp hy
    refine (hLmem _).mpr ⟨a + b * a', b, ?_⟩
    rw [map_add, map_smul, map_smul, h1, h2]
    module
  have hPinv : ∀ s ∈ S, ∀ y ∈ P, ρ s y ∈ P := by
    intro s hs y hy
    obtain ⟨hye, hyw⟩ := (hPmem y).mp hy
    obtain ⟨h1, a', h2⟩ := hfix' s hs
    have hy1 : polar Q y w₁ = 0 := by
      rw [hw₁, polar_add_right, polar_smul_right_eq, hyw, hye]; ring
    have h3 : polar Q (ρ s y) e = 0 := by
      have h := polar_map_of_mem (hρO s) y e
      rw [h1] at h
      rw [h]; exact hye
    have h4 : polar Q (ρ s y) w₁ = 0 := by
      have h := polar_map_of_mem (hρO s) y w₁
      rw [h2, polar_add_right, polar_smul_right_eq, h3, mul_zero, add_zero, hy1] at h
      exact h
    refine (hPmem _).mpr ⟨h3, ?_⟩
    rw [hw', polar_sub_right, polar_smul_right_eq, h3, h4]
    ring
  have hB2 : ∀ u, polar Q u e = 0 → polar Q u w = 0 → Q u = 0 →
      ∃ s ∈ S, ρ s = eichler Q u w₁ := by
    intro u hue huw hQu
    have huw1 : polar Q u w₁ = 0 := by
      rw [hw₁, polar_add_right, polar_smul_right_eq, huw, hue]; ring
    obtain ⟨s, hs⟩ := hE u w₁ hQu huw1
    refine ⟨s, ?_, hs⟩
    rw [hSdef, Subgroup.mem_centralizer_singleton_iff]
    apply hρ
    rw [map_mul, map_mul, hs, hx]
    have hg := eichler_conj (eichler_mem_orthogonalGroup Q u w₁) e w
    have hge : eichler Q u w₁ e = e := by
      rw [eichler_apply hQu huw1, polar_comm Q e u, hue, polar_comm Q e w₁, hw1e]; simp
    have hgw : eichler Q u w₁ w = w := by
      rw [eichler_apply hQu huw1, polar_comm Q w u, huw, polar_comm Q w w₁, hw1w]; simp
    rw [hge, hgw] at hg
    exact (mul_inv_eq_iff_eq_mul.mp hg)
  have hirr : ∀ X : Submodule K V, L ≤ X → X ≤ P → (∀ s ∈ S, ∀ y ∈ X, ρ s y ∈ X) →
      X = L ∨ X = P := by
    intro X hLX hXP hXinv
    by_cases hXL : X ≤ L
    · exact Or.inl (le_antisymm hXL hLX)
    right
    refine le_antisymm hXP ?_
    obtain ⟨y, hyX, hyL⟩ := SetLike.not_le_iff_exists.mp hXL
    obtain ⟨hye, hyw⟩ := (hPmem y).mp (hXP hyX)
    have hyL' : y ∉ Submodule.span K {e, w₁} := by rw [← hLdef]; exact hyL
    have hSX : ∀ y' ∈ X, ∀ u, polar Q u e = 0 → polar Q u w = 0 → Q u = 0 →
        polar Q y' u ≠ 0 → u ∈ X := by
      intro y' hy'X u hue huw hQu hy'u
      obtain ⟨hy'e, hy'w⟩ := (hPmem y').mp (hXP hy'X)
      obtain ⟨s, hs, hsE⟩ := hB2 u hue huw hQu
      have hmem : ρ s y' ∈ X := hXinv s hs y' hy'X
      have huw1 : polar Q u w₁ = 0 := by
        rw [hw₁, polar_add_right, polar_smul_right_eq, huw, hue]; ring
      have hy'w1 : polar Q y' w₁ = 0 := by
        rw [hw₁, polar_add_right, polar_smul_right_eq, hy'w, hy'e]; ring
      have hval : ρ s y' - y' = polar Q y' u • w₁ - (Q w * polar Q y' u) • u := by
        rw [hsE, eichler_apply hQu huw1, hy'w1, hQw1]
        module
      have hdiff : ρ s y' - y' ∈ X := X.sub_mem hmem hy'X
      have hw1X : polar Q y' u • w₁ ∈ X := X.smul_mem _ (hLX hw1L)
      have hcu : (Q w * polar Q y' u) • u ∈ X := by
        have h := X.sub_mem hw1X hdiff
        rw [hval] at h
        have : polar Q y' u • w₁ - (polar Q y' u • w₁ - (Q w * polar Q y' u) • u) =
            (Q w * polar Q y' u) • u := by abel
        rw [this] at h
        exact h
      have hne : Q w * polar Q y' u ≠ 0 := mul_ne_zero hw hy'u
      have h := X.smul_mem (Q w * polar Q y' u)⁻¹ hcu
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
    obtain ⟨u₀, hu0e, hu0w, hQu0, hyu0⟩ :=
      rckSOmM2_exists_singular hQ he he0 hew hw hw₁ hye hyw hyL'
    have hu0X : u₀ ∈ X := hSX y hyX u₀ hu0e hu0w hQu0 hyu0
    have hsing : ∀ u, polar Q u e = 0 → polar Q u w = 0 → Q u = 0 → u ∈ X := by
      intro u hue huw hQu
      by_cases hyu : polar Q y u = 0
      · by_cases hu0u : polar Q u₀ u = 0
        · have hQ' : Q (u + u₀) = 0 := by
            rw [QuadraticMap.map_add Q, hQu, hQu0, polar_comm Q u u₀, hu0u]; ring
          have hX' : u + u₀ ∈ X := by
            refine hSX y hyX (u + u₀) (by rw [polar_add_left, hue, hu0e]; ring)
              (by rw [polar_add_left, huw, hu0w]; ring) hQ' ?_
            rw [polar_add_right, hyu, zero_add]; exact hyu0
          have := X.sub_mem hX' hu0X
          rwa [add_sub_cancel_right] at this
        · exact hSX u₀ hu0X u hue huw hQu hu0u
      · exact hSX y hyX u hue huw hQu hyu
    intro z hz
    obtain ⟨hze, hzw⟩ := (hPmem z).mp hz
    by_cases hzL : z ∈ L
    · exact hLX hzL
    have hzL' : z ∉ Submodule.span K {e, w₁} := by rw [← hLdef]; exact hzL
    obtain ⟨u₁, hu1e, hu1w, hQu1, hzu1⟩ :=
      rckSOmM2_exists_singular hQ he he0 hew hw hw₁ hze hzw hzL'
    have hu1X : u₁ ∈ X := hsing u₁ hu1e hu1w hQu1
    obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = Q z / polar Q z u₁ := ⟨_, rfl⟩
    have hc : lam * polar Q z u₁ = Q z := by rw [hlam]; field_simp
    have hz' : Q (z + lam • u₁) = 0 := by
      rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQu1, polar_smul_right_eq]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination hc + (Q z) * h2
    have hz'X : z + lam • u₁ ∈ X :=
      hsing _ (by rw [polar_add_left, polar_smul_left_eq, hze, hu1e]; ring)
        (by rw [polar_add_left, polar_smul_left_eq, hzw, hu1w]; ring) hz'
    have := X.sub_mem hz'X (X.smul_mem lam hu1X)
    rwa [add_sub_cancel_right] at this
  have hTac := apply_sub_mem_of_isPGroup hlin (S := S) (T := pCoreOf 2 S)
    (pCoreOf_le 2 S) (isPGroup_pCoreOf 2 S) (fun s hs t' ht' => conj_mem_pCoreOf hs ht')
    hLP hPinv hLinv hirr
  have htS : t ∈ pCoreOf 2 S := by rw [hSdef]; exact ht
  intro y hye hyw
  have hyP : y ∈ P := (hPmem y).mpr ⟨hye, hyw⟩
  have hyL : ρ t y - y ∈ L := hTac t htS y hyP
  obtain ⟨a, b, hab⟩ := (hLmem _).mp hyL
  have hty : ρ t y = y + (a • e + b • w₁) := by rw [hab]; abel
  have hyw1 : polar Q y w₁ = 0 := by
    rw [hw₁, polar_add_right, polar_smul_right_eq, hyw, hye]; ring
  have hb : b = 0 := by
    have hQt : Q (ρ t y) = Q y := map_of_mem (hρO t) y
    rw [hty, QuadraticMap.map_add Q, rckSOmMR_quad_span he hew1 a b, polar_add_right,
      polar_smul_right_eq, polar_smul_right_eq, hye, hyw1, hQw1] at hQt
    have hb2 : b ^ 2 * Q w = 0 := by linear_combination hQt
    exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp hb2).resolve_right hw)
  exact ⟨a, by rw [← hab, hb, zero_smul, add_zero]⟩

end CFSG.StandardType.RCKC1
