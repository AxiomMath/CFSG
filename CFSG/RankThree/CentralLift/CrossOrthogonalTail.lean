module

public import CFSG.RankThree.CentralLift.CrossOrthogonalTailTools
public import CFSG.RankThree.CentralLiftSO.TailTriangular

public section

namespace CFSG.RankThree.CentralLift

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (ne_succ_of_lt)
open CFSG.RankThree.CentralLiftSO.TailO (TailHyp liftTorus liftWeyl sLift sLift_sq_mem etaLift
  rhoLift normal_liftTorus_subgroupOf weylHom ker_weylHom liftUnip liftUnipExcept liftBorel
  xPlusLong xMinusLong xPlusShort xMinusShort xPlusLong_mem_liftUnip xPlusShort_mem_liftUnip
  odd_orthogonal_tail_cross_characteristic_central_prime_triangular_factorization)
open CFSG.LieType.Chevalley (uSL vSL)
open scoped Pointwise

theorem tail_orthogonal_cross_splitting {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hpℓ : p ≠ ℓ) (_hf : 1 ≤ f) {K L : Type} [Field K] [Field L] [Algebra K L]
    [Finite K] (hk : Nat.card K = ℓ ^ f) (T : NormTailData K L)
    (hm : Module.finrank K L = 1 ∨ Module.finrank K L = 2) {r : ℕ} (hr : 3 ≤ r) {E : Type*}
    [Group E] [Finite E] (π : E →* G0 T r) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker) :
    (∃! s : G0 T r →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : G0 T r →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  have hchar : ringChar K = ℓ := ringChar.eq K ℓ
  have hk2 : ringChar K ≠ 2 := by
    rw [hchar]
    exact hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  have : Fact (ringChar K).Prime := ⟨hchar ▸ hℓ⟩
  have hpℓ' : p ≠ ringChar K := hchar ▸ hpℓ
  have hpos : 0 < Module.finrank K L := by rcases hm with h | h <;> omega
  have : Module.Finite K L := Module.finite_of_finrank_pos hpos
  have : Finite L := Module.finite_of_finite K
  have hS : TailHyp T π := ⟨hk2, ⟨hπ, hC, ⟨p, hp, hp3, hCp⟩⟩, inferInstance, inferInstance⟩
  obtain ⟨-, -, hBset, hBmap, hBle, -, -, hBinj, -, hconj, hlong, -, -, hfactS, hrewS, hsignS⟩ :=
    odd_orthogonal_tail_cross_characteristic_central_prime_triangular_factorization hk2 T hm hr
      hp hp3 hpℓ' hπ hC hCp
  set i₀ : Fin r := ⟨r - 1, by omega⟩ with hi₀
  have hlast : ∀ i : Fin r, ¬i.val + 1 < r → i = i₀ := fun i hi =>
    Fin.ext (by simp only [hi₀]; omega)
  let Xp : Fin r → Subgroup E := fun i => if h : i.val + 1 < r then
      ((etaLift T π (ne_succ_of_lt h)).comp LinearRoots.uSLHom).range
    else ((rhoLift T π i).comp LinearRoots.uSLHom).range
  let Xm : Fin r → Subgroup E := fun i => if h : i.val + 1 < r then
      ((etaLift T π (ne_succ_of_lt h)).comp vSLHom).range
    else ((rhoLift T π i).comp vSLHom).range
  have hXpL : ∀ i (h : i.val + 1 < r) x, x ∈ Xp i ↔ ∃ t : K, xPlusLong π h t = x := by
    intro i h x
    simp only [Xp, dite_eq_left h]
    exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hXmL : ∀ i (h : i.val + 1 < r) x, x ∈ Xm i ↔ ∃ t : K, xMinusLong π h t = x := by
    intro i h x
    simp only [Xm, dite_eq_left h]
    exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hXpS : ∀ i, ¬i.val + 1 < r → ∀ x, x ∈ Xp i ↔ ∃ t : L, xPlusShort π i t = x := by
    intro i h x
    simp only [Xp, dite_eq_right h]
    exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hXmS : ∀ i, ¬i.val + 1 < r → ∀ x, x ∈ Xm i ↔ ∃ t : L, xMinusShort π i t = x := by
    intro i h x
    simp only [Xm, dite_eq_right h]
    exact ⟨fun ⟨t, ht⟩ => ⟨t.toAdd, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩
  have hInj : Set.InjOn π (liftBorel π : Set E) := fun x hx y hy hxy =>
    congrArg Subtype.val (hBinj (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hXpU : ∀ i, Xp i ≤ liftUnip π := by
    intro i x hx
    by_cases h : i.val + 1 < r
    · obtain ⟨t, rfl⟩ := (hXpL i h x).1 hx
      exact xPlusLong_mem_liftUnip hS h t
    · obtain ⟨t, rfl⟩ := (hXpS i h x).1 hx
      exact xPlusShort_mem_liftUnip hS h t
  have hfact : ∀ i, (liftBorel π : Set E) =
      (Xp i : Set E) * (liftUnipExcept π i : Set E) * (liftTorus T π : Set E) := by
    intro i
    ext x
    by_cases h : i.val + 1 < r
    · rw [SetLike.mem_coe, ((hlong i h).2.2.1) x]
      constructor
      · rintro ⟨t, u, hu, g, hg, rfl⟩
        exact ⟨_, ⟨_, (hXpL i h _).2 ⟨t, rfl⟩, u, hu, rfl⟩, g, hg, rfl⟩
      · rintro ⟨_, ⟨y, hy, u, hu, rfl⟩, g, hg, rfl⟩
        obtain ⟨t, rfl⟩ := (hXpL i h y).1 hy
        exact ⟨t, u, hu, g, hg, rfl⟩
    · obtain rfl := hlast i h
      rw [SetLike.mem_coe, hfactS x]
      constructor
      · rintro ⟨t, u, hu, g, hg, rfl⟩
        exact ⟨_, ⟨_, (hXpS _ h _).2 ⟨t, rfl⟩, u, hu, rfl⟩, g, hg, rfl⟩
      · rintro ⟨_, ⟨y, hy, u, hu, rfl⟩, g, hg, rfl⟩
        obtain ⟨t, rfl⟩ := (hXpS _ h y).1 hy
        exact ⟨t, u, hu, g, hg, rfl⟩
  have hrew : ∀ i, ∀ x ∈ Xp i, x ≠ 1 → x * sLift T π i ∈
      (Xm i : Set E) * (liftTorus T π : Set E) * (Xp i : Set E) := by
    intro i x hx hx1
    by_cases h : i.val + 1 < r
    · obtain ⟨t, rfl⟩ := (hXpL i h x).1 hx
      have ht : t ≠ 0 := by
        rintro rfl
        apply hx1
        change etaLift T π (ne_succ_of_lt h) (uSL 0) = 1
        rw [LinearRoots.uSL_zero, map_one]
      obtain ⟨hr1, hr2⟩ := (hlong i h).2.2.2.1 t ht
      rw [hr1]
      exact ⟨_, ⟨_, (hXmL i h _).2 ⟨t⁻¹, rfl⟩, _, hr2, rfl⟩, _, (hXpL i h _).2 ⟨-t⁻¹, rfl⟩, rfl⟩
    · obtain rfl := hlast i h
      obtain ⟨t, rfl⟩ := (hXpS _ h x).1 hx
      have ht : t ≠ 0 := by
        rintro rfl
        apply hx1
        change rhoLift T π i₀ (uSL 0) = 1
        rw [LinearRoots.uSL_zero, map_one]
      obtain ⟨hr1, hr2⟩ := hrewS t ht
      rw [hr1]
      exact ⟨_, ⟨_, (hXmS _ h _).2 ⟨t⁻¹, rfl⟩, _, hr2, rfl⟩, _, (hXpS _ h _).2 ⟨-t⁻¹, rfl⟩, rfl⟩
  have hsign : ∀ n ∈ liftWeyl T π, ∀ i, (∀ x ∈ Xp i, n * x * n⁻¹ ∈ liftUnip π) ∨
      (∀ y ∈ Xm i, n * y * n⁻¹ ∈ liftUnip π) := by
    intro n hn i
    by_cases h : i.val + 1 < r
    · rcases (hlong i h).2.2.2.2 n hn with hl | hl
      · left
        intro x hx
        obtain ⟨t, rfl⟩ := (hXpL i h x).1 hx
        exact hl t
      · right
        intro y hy
        obtain ⟨t, rfl⟩ := (hXmL i h y).1 hy
        exact hl t
    · obtain rfl := hlast i h
      rcases hsignS n hn with hl | hl
      · left
        intro x hx
        obtain ⟨t, rfl⟩ := (hXpS _ h x).1 hx
        exact hl t
      · right
        intro y hy
        obtain ⟨t, rfl⟩ := (hXmS _ h y).1 hy
        exact hl t
  have hBN : ∀ n ∈ liftWeyl T π, π n ∈ (liftBorel π).map π → n ∈ liftTorus T π := by
    intro n hn hnB
    obtain ⟨b, hb, hbn⟩ := hnB
    have h1 := weylHom_eq_one_of_mem_tailBorel hS ⟨n, hn⟩ (by
      change ((π n : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
        tailBorel r (normForm T)
      rw [← hbn]
      exact hBle ⟨b, hb, rfl⟩)
    have h2 : (⟨n, hn⟩ : liftWeyl T π) ∈ (weylHom hS).ker := h1
    rw [ker_weylHom hS] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have hU : ∀ u ∈ tailUnipotent r (normForm T), ∃ b ∈ liftBorel π, ((π b : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) = u := by
    intro u hu
    have hu' : u ∈ ((liftBorel π).map ((orthElementaryGroup (quadTail r (normForm T))).subtype.comp
        π) : Set (((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))) := by
      rw [hBmap]
      exact ⟨u, hu, 1, one_mem _, mul_one u⟩
    obtain ⟨b, hb, hbu⟩ := hu'
    exact ⟨b, hb, hbu⟩
  obtain ⟨-, -, σ, hσ⟩ :=
    CFSG.RankThree.CentralExtension.central_extension_faithful_bruhat_lift_splitting π hC hBset
      hInj (normal_liftTorus_subgroupOf hS) (sLift T π) rfl (fun i => sLift_sq_mem i) Xp Xm
      (liftUnipExcept π) hXpU hfact hconj hrew hsign hBN (sup_map_eq_top_tail hS hU)
  have : Group.IsPerfect (G0 T r) :=
    isPerfect_G0 hr (nondegenerate_polarBilin_normForm_of_two_ne_zero (Ring.two_ne_zero hk2))
  refine ⟨⟨σ, hσ, fun σ' hσ' => section_eq_of_forall π hC (fun δ hδ =>
    eq_one_of_isPerfect_of_mem_center δ fun x => hC (hδ x)) hσ' hσ⟩,
    fun s hs => LinearRoots.exists_mulEquiv_prod_of_section hC hs⟩

end CFSG.RankThree.CentralLift
