module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Vertex
public import CFSG.Quasithin.Recognition.SzVBEvenDist

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

theorem eq_one_or_eq_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {c y : G} (hc : c ∈ Z)
    (hc1 : c ≠ 1) (hy : y ∈ Z) : y = 1 ∨ y = c := by
  by_contra hne
  push Not at hne
  classical
  have : Fintype Z := Fintype.ofFinite Z
  let s : Finset Z := {⟨1, Z.one_mem⟩, ⟨c, hc⟩, ⟨y, hy⟩}
  have hs : s.card = 3 := by
    have h1 : (⟨1, Z.one_mem⟩ : Z) ≠ ⟨c, hc⟩ := fun h => hc1 (congrArg Subtype.val h).symm
    have h2 : (⟨1, Z.one_mem⟩ : Z) ≠ ⟨y, hy⟩ := fun h => hne.1 (congrArg Subtype.val h).symm
    have h3 : (⟨c, hc⟩ : Z) ≠ ⟨y, hy⟩ := fun h => hne.2 (congrArg Subtype.val h).symm
    simp only [s]
    rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3]
  have := s.card_le_univ
  rw [hs, ← Nat.card_eq_fintype_card, hZ] at this
  omega

theorem eq_one_or_eq_of_mem_zpowers {x y : G} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  have hord : orderOf x = 2 := orderOf_eq_prime h2 hx1
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hord]
  exact eq_one_or_eq_of_card_two hcard (Subgroup.mem_zpowers x) hx1 hy

structure CritGeo (p : ℕ → CosetGeom G₀ G₁ G₂) (V : Subgroup G) : Prop where
  b7 : 7 ≤ critDist G₀ G₁ G₂ V
  odd : Odd (critDist G₀ G₁ G₂ V)
  geo : IsGeo p (critDist G₀ G₁ G₂ V)
  p0 : p 0 = γ₀ G₀ G₁ G₂
  p1 : p 1 = γ₁ G₀ G₁ G₂
  crit : ¬ V ≤ ballStab 1 (p (critDist G₀ G₁ G₂ V))

namespace CritGeo

variable {p : ℕ → CosetGeom G₀ G₁ G₂} (H : CritGeo p V)

include H

omit [Finite G] in
theorem dist_eq {i j : ℕ} (hij : i ≤ j) (hj : j ≤ critDist G₀ G₁ G₂ V) :
    dist (p i) (p j) = j - i := H.geo i j hij hj

omit [Finite G] in
theorem vtype_even (hG : G₀ = G₁ ⊔ G₂) {i : ℕ} (hi : i ≤ critDist G₀ G₁ G₂ V) (he : Even i) :
    vtype (p i) = false := by
  apply vtype_eq_false_of_even hG
  rw [← H.p0, H.dist_eq (Nat.zero_le i) hi]
  simpa using he

omit [Finite G] in
theorem vtype_odd (hG : G₀ = G₁ ⊔ G₂) {i : ℕ} (hi : i ≤ critDist G₀ G₁ G₂ V) (ho : Odd i) :
    vtype (p i) = true := by
  apply vtype_eq_true_of_odd hG
  rw [← H.p0, H.dist_eq (Nat.zero_le i) hi]
  simpa using ho

omit [Finite G] in
theorem adj {i : ℕ} (hi : i < critDist G₀ G₁ G₂ V) : (graph G₀ G₁ G₂).Adj (p i) (p (i + 1)) :=
  H.geo.adj hi

theorem s1 (C : Ctx G₀ G₁ G₂ T V z) :
    Zv z (p (critDist G₀ G₁ G₂ V)) ≤ conjClosure V G₂ ∧
      ¬ Vv V (p (critDist G₀ G₁ G₂ V)) ≤ pCoreOf 2 G₂ := by
  set b := critDist G₀ G₁ G₂ V with hbdef
  have hb := H.b7
  have hG := C.hyp.gen
  have hN := C.hyp.normalizes
  have hα : vtype (p b) = true := H.vtype_odd hG le_rfl H.odd
  have hW : Vv V (γ₁ G₀ G₁ G₂) = conjClosure V G₂ := Vv_γ₁ C.hyp.le₂ hN
  have hWab : IsElemAbelian 2 (conjClosure V G₂) := by
    rw [← hW]; exact SzVB.isElemAbelian_Vv_of_vtype C.toGeoCtx vtype_γ₁ (by omega)
  have hW'ab : IsElemAbelian 2 (Vv V (p b)) :=
    SzVB.isElemAbelian_Vv_of_vtype C.toGeoCtx hα (by omega)
  have d1b : dist (γ₁ G₀ G₁ G₂) (p b) = b - 1 := by
    rw [← H.p1]; exact H.dist_eq (by omega) le_rfl
  have hWα : conjClosure V G₂ ≤ stab (p b) := by
    rw [← hW]; exact SzVB.Vv_le_stab_of_dist_le_B C.toGeoCtx vtype_γ₁ (by omega)
  have hW'β : Vv V (p b) ≤ G₂ := by
    have := SzVB.Vv_le_stab_of_dist_le_B C.toGeoCtx hα (x := γ₁ G₀ G₁ G₂)
      (by rw [CosetGeom.dist_comm]; omega)
    rwa [stab_γ₁ C.hyp.le₂] at this
  have hW'NW : ∀ x ∈ Vv V (p b), ∀ a ∈ conjClosure V G₂, x * a * x⁻¹ ∈ conjClosure V G₂ := by
    intro x hx a ha
    have hxN : x ∈ Subgroup.normalizer (conjClosure V G₂ : Set G) := by
      have := stab_le_normalizer_Vv hN (γ₁ G₀ G₁ G₂)
        (show x ∈ stab (γ₁ G₀ G₁ G₂) by rw [stab_γ₁ C.hyp.le₂]; exact hW'β hx)
      rwa [hW] at this
    exact (Subgroup.mem_normalizer_iff.mp hxN a).mp ha
  have hVQ : ¬ V ≤ pCoreOf 2 (stab (p b)) := fun h =>
    H.crit (h.trans (pCoreOf_stab_le_ballStab_one C.hyp.toAmalgamHyp _))
  obtain ⟨w, hwV, hwQ⟩ := IsConcreteLE.not_le_iff_exists.mp hVQ
  have hwW : w ∈ conjClosure V G₂ := le_conjClosure V G₂ hwV
  have hw2 : w * w = 1 := by
    have := isElemAbelian_pow_eq_one hWab hwW; rwa [pow_two] at this
  have hidx : ∀ e ∈ conjClosure V G₂,
      e ∈ pCoreOf 2 (stab (p b)) ∨ e * w ∈ pCoreOf 2 (stab (p b)) := by
    intro e he
    have he2 : e * e = 1 := by
      have := isElemAbelian_pow_eq_one hWab he; rwa [pow_two] at this
    have hq : ∀ a ∈ Vv V (p b), w * (e * a * e⁻¹ * a⁻¹) * w⁻¹ = e * a * e⁻¹ * a⁻¹ := by
      intro a ha
      have hmem : e * a * e⁻¹ * a⁻¹ ∈ conjClosure V G₂ := by
        have h1 : a * e⁻¹ * a⁻¹ ∈ conjClosure V G₂ := hW'NW a ha e⁻¹ (inv_mem he)
        have e1 : e * a * e⁻¹ * a⁻¹ = e * (a * e⁻¹ * a⁻¹) := by group
        rw [e1]; exact mul_mem he h1
      have hc := isElemAbelian_comm hWab hwW hmem
      calc w * (e * a * e⁻¹ * a⁻¹) * w⁻¹ = e * a * e⁻¹ * a⁻¹ * w * w⁻¹ := by rw [hc]
        _ = e * a * e⁻¹ * a⁻¹ := by group
    rcases C.quad_pair_at hα (hWα he) (hWα hwW) he2 hw2 (isElemAbelian_comm hWab he hwW) hq with
      h | h | h
    · exact Or.inl h
    · exact absurd h hwQ
    · exact Or.inr h
  have hW'Q : ¬ Vv V (p b) ≤ pCoreOf 2 G₂ := by
    intro hle
    obtain ⟨a, ha, h1, h2⟩ := C.comm_big_at hα (hWα hwW) hw2 hwQ z
    have hmem : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.zpowers z := by
      apply SzVB.commutator_conjClosure_pCoreOf_le C.toGeoCtx
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hwW (hle ha)
    rcases eq_one_or_eq_of_mem_zpowers (SzVB.z_mul_self C.toGeoCtx) C.klein.z_ne_one hmem with
      h | h
    · exact h1 h
    · exact h2 h
  refine ⟨?_, hW'Q⟩
  obtain ⟨w', hw'W', hw'Q⟩ := IsConcreteLE.not_le_iff_exists.mp hW'Q
  have hw'2 : w' * w' = 1 := by
    have := isElemAbelian_pow_eq_one hW'ab hw'W'; rwa [pow_two] at this
  have hw'G : w' ∈ G₂ := hW'β hw'W'
  have hII : ∃ h ∈ conjClosure V G₂, h ∈ pCoreOf 2 (stab (p b)) ∧
      ∃ x ∈ Vv V (p b), h * x ≠ x * h := by
    by_contra hI
    push Not at hI
    have hcw : w' * w * w'⁻¹ * w⁻¹ ∈ conjClosure V G₂ := by
      have h1 : w' * w * w'⁻¹ ∈ conjClosure V G₂ := hW'NW w' hw'W' w hwW
      exact mul_mem h1 (inv_mem hwW)
    obtain ⟨a, haW, h1, h2⟩ := C.comm_big w' hw'G hw'2 hw'Q (w' * w * w'⁻¹ * w⁻¹)
    rcases hidx a haW with ha | ha
    · apply h1
      have hc := hI a haW ha w' hw'W'
      calc w' * a * w'⁻¹ * a⁻¹ = a * w' * w'⁻¹ * a⁻¹ := by rw [hc]
        _ = 1 := by group
    · apply h2
      have hhW : a * w ∈ conjClosure V G₂ := mul_mem haW hwW
      have hc := hI (a * w) hhW ha w' hw'W'
      have hcomm := isElemAbelian_comm hWab hhW hcw
      have ha' : a = a * w * w := by rw [mul_assoc, hw2, mul_one]
      calc w' * a * w'⁻¹ * a⁻¹
          = w' * (a * w * w) * w'⁻¹ * (a * w * w)⁻¹ := by rw [← ha']
        _ = w' * (a * w) * w * w'⁻¹ * w⁻¹ * (a * w)⁻¹ := by group
        _ = a * w * w' * w * w'⁻¹ * w⁻¹ * (a * w)⁻¹ := by rw [← hc]
        _ = a * w * (w' * w * w'⁻¹ * w⁻¹) * (a * w)⁻¹ := by group
        _ = w' * w * w'⁻¹ * w⁻¹ * (a * w) * (a * w)⁻¹ := by rw [hcomm]
        _ = w' * w * w'⁻¹ * w⁻¹ := by group
  obtain ⟨h, hhW, hhQ, x, hx, hne⟩ := hII
  have hc1 : h * x * h⁻¹ * x⁻¹ ≠ 1 := by
    intro hc
    apply hne
    calc h * x = h * x * h⁻¹ * x⁻¹ * x * h := by group
      _ = x * h := by rw [hc]; group
  have hcZ : h * x * h⁻¹ * x⁻¹ ∈ Zv z (p b) := by
    have h1 : x * h * x⁻¹ * h⁻¹ ∈ Zv z (p b) := by
      apply SzVB.commutator_Vv_pCoreOf_le_Zv C.toGeoCtx hα
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hx hhQ
    have e : h * x * h⁻¹ * x⁻¹ = (x * h * x⁻¹ * h⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem h1
  have hcW : h * x * h⁻¹ * x⁻¹ ∈ conjClosure V G₂ := by
    have h1 := hW'NW x hx h⁻¹ (inv_mem hhW)
    have e : h * x * h⁻¹ * x⁻¹ = h * (x * h⁻¹ * x⁻¹) := by group
    rw [e]; exact mul_mem hhW h1
  intro y hy
  rcases eq_one_or_eq_of_card_two (SzVB.card_Zv C.toGeoCtx hα) hcZ hc1 hy with rfl | rfl
  · exact one_mem _
  · exact hcW

end CritGeo

end CFSG.Quasithin.Kleidman.VBOdd
