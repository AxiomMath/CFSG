module

public import CFSG.RankThree.PartOne.KF1514B.Siegel
public import CFSG.RankThree.PartOne.KF1514B.Numbers
public import CFSG.RankThree.PartOne.KF1514B.Sylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap Matrix



section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

variable (K) in
@[expose] noncomputable def tdHom : (Fin 3 → Kˣ) →* (Vt K ≃ₗ[K] Vt K) :=
  MonoidHom.mk' (fun t => tailDiag 3 t (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) (fun t t' => by
    rw [tailDiag_mul, mul_one])

theorem tdHom_apply (t : Fin 3 → Kˣ) (v : Vt K) :
    tdHom K t v = (torusElt 3 K t v.1, v.2) := rfl

theorem tdHom_apply_hypVec_inl (t : Fin 3 → Kˣ) (i : Fin 3) :
    tdHom K t (hypVec K (Fin 2 → K) (Sum.inl i)) =
      ((t i : Kˣ) : K) • hypVec K (Fin 2 → K) (Sum.inl i) := by
  refine Prod.ext (funext fun c' => ?_) ?_
  · rw [tdHom_apply]
    show torusElt 3 K t (Pi.single (Sum.inl i) 1) c' = _
    rw [torusElt_apply]
    rcases c' with j | j
    · by_cases hji : j = i
      · subst hji
        simp [hypVec]
      · simp [hypVec, hji]
    · simp [hypVec]
  · simp [tdHom_apply, hypVec]

theorem tdHom_injective : Function.Injective (tdHom K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  funext i
  have h1 := tdHom_apply_hypVec_inl t i
  rw [ht] at h1
  have h2 := congrFun (congrArg Prod.fst h1) (Sum.inl i)
  simp [hypVec] at h2
  exact Units.ext (by simpa using h2.symm)

theorem tdHom_mem_G0 (t : Fin 3 → Kˣ) : tdHom K t ∈ G0 b c := by
  have h1 : torusElt 3 K t ∈ rootSupr 3 K := by
    rw [← (orthogonal_geometry_split_root_generation (K := K) (le_refl 3)).1]
    exact torusElt_mem_orthElementaryGroup (le_refl 3) t
  exact tailRootSupr_le (map_rootSupr_le (A := Fin 2 → K) (qA := minusTailForm K b c) ⟨_, h1, rfl⟩)

theorem tdHom_mem_P13 (t : Fin 3 → Kˣ) : tdHom K t ∈ P13 b c := by
  have key : ∀ k : ℕ, ∀ w ∈ tailFlag K (Fin 2 → K) 3 k, tdHom K t w ∈ tailFlag K (Fin 2 → K) 3 k := by
    intro k w hw
    have h := Submodule.mem_map_of_mem (f := ((tdHom K t : Vt K ≃ₗ[K] Vt K) : Vt K →ₗ[K] Vt K)) hw
    have e : tdHom K t = dMap (diagGL t) (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
      tailDiag_eq_dMap t 1
    rw [e, map_tailFlag_dMap (diagGL_isUpperTriangular t) 1 k] at h
    rw [e]
    exact h
  exact ⟨tdHom_mem_G0 t, key 1, key 3⟩

theorem tdHom_commute_x0 {t : Fin 3 → Kˣ} (ht : ((t 0 : Kˣ) : K) * ((t 1 : Kˣ) : K) = 1) :
    tdHom K t * x0 b c = x0 b c * tdHom K t := by
  have hO := orthElementaryGroup_le _ (tdHom_mem_G0 (b := b) (c := c) t)
  refine commute_x0_of_coeff hO (α := ((t 0 : Kˣ) : K)) (γ := 0) (δ := 0) (ε := ((t 1 : Kˣ) : K)) ?_ ?_ ?_
  · rw [tdHom_apply_hypVec_inl]
    simp
  · rw [tdHom_apply_hypVec_inl]
    simp
  · simpa using ht

end Torus


section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem card_tdHom_range : Nat.card (tdHom K).range = (Nat.card K - 1) ^ 3 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (tdHom_injective (K := K))).toEquiv.symm, Nat.card_pi]
  simp [Nat.card_units]

theorem exists_conj_le_tdHom {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, A.map (MulAut.conj h).toMonoidHom ≤ (tdHom K).range := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
  have hpr : p ∣ r := by rwa [hr, Nat.add_sub_cancel] at hpq
  have hrpos : 0 < r := by omega
  have hG : Nat.card ↥(G0 b c) = r ^ 3 * ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) *
      ((r + 2) ^ 3 * (r ^ 2 + 2 * r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
    rw [hcard, hr]
    exact order_factor_three r
  set Ts : Subgroup (Vt K ≃ₗ[K] Vt K) := (tdHom K).range with hTs
  have hTsG : Ts ≤ G0 b c := by
    rintro _ ⟨t, rfl⟩
    exact tdHom_mem_G0 t
  set T' : Subgroup ↥(G0 b c) := Ts.subgroupOf (G0 b c) with hT'
  have hT'card : Nat.card T' = r ^ 3 := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsG).toEquiv, hTs, card_tdHom_range,
      hr, Nat.add_sub_cancel]
  have hindex : T'.index = ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) *
      ((r + 2) ^ 3 * (r ^ 2 + 2 * r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
    have h := T'.card_mul_index
    rw [hT'card, hG] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hnd : ¬ p ∣ T'.index := by
    rw [hindex]
    exact not_dvd_cofactor_three Fact.out hp5 hpr
  have hAp : IsPGroup p (A.subgroupOf (G0 b c)) := fun x => ⟨1, by
    have := hA (x : ↥(G0 b c)) (Subgroup.mem_subgroupOf.1 x.2)
    exact Subtype.ext (Subtype.ext (by simpa using this))⟩
  obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index hnd hAp
  refine ⟨(g : Vt K ≃ₗ[K] Vt K), g.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : (⟨a, hAG ha⟩ : ↥(G0 b c)) ∈ A.subgroupOf (G0 b c) := Subgroup.mem_subgroupOf.2 ha
  have h2 := hg (Subgroup.mem_map_of_mem _ h1)
  rw [hT', Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.conj_apply] using h2

theorem row3_clause_one {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, A.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.normalizer (pushingUpS (U0 b c) : Set (Vt K ≃ₗ[K] Vt K)) := by
  obtain ⟨h, hh, hAh⟩ := exists_conj_le_tdHom hp5 hcard hpq hAG hA
  refine ⟨h, hh, hAh.trans fun y hy => ?_⟩
  obtain ⟨t, rfl⟩ := hy
  exact P13_le_normalizer_pushingUpS (tdHom_mem_P13 t)

theorem row3_clause_two {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, ∃ B : Subgroup (Vt K ≃ₗ[K] Vt K), B ≤ A ∧ Nat.card A ≤ p * Nat.card B ∧
      B.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({x0 b c} : Set (Vt K ≃ₗ[K] Vt K)) := by
  obtain ⟨h, hh, hAh⟩ := exists_conj_le_tdHom hp5 hcard hpq hAG hA
  let ψ : (Fin 3 → Kˣ) →* Kˣ :=
    (Pi.evalMonoidHom (fun _ : Fin 3 => Kˣ) 0) * (Pi.evalMonoidHom (fun _ : Fin 3 => Kˣ) 1)
  obtain ⟨B, hBA, hBcard, hB⟩ := exists_torus_subgroup (Fact.out : p.Prime).pos (tdHom K)
    tdHom_injective ψ hA hAh
  refine ⟨h, hh, B, hBA, hBcard, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨t, ht, hty⟩ := hB y hy
  have ht' : ((t 0 : Kˣ) : K) * ((t 1 : Kˣ) : K) = 1 := by
    have : t 0 * t 1 = 1 := ht
    simpa using congrArg (fun u : Kˣ => (u : K)) this
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have e : (MulAut.conj h).toMonoidHom y = tdHom K t := by
    rw [← hty]
    simp [MulAut.conj_apply]
  rw [e]
  exact (tdHom_commute_x0 ht').symm

end Main

end CFSG.RankThree.PartOne.KF1514B
