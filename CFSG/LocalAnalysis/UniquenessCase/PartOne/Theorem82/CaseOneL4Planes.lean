module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieChar
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem sumZero_point_reps_vA :
    ∀ v : Fin 4 → ZMod 3, (¬ ∃ d : ZMod 3, v = fun _ => d) →
      ∃ (σ : Equiv.Perm (Fin 4)) (s d : ZMod 3), s ≠ 0 ∧
        ((∀ i, v (σ i) = s * ![1, 1, -1, -1] i + d) ∨
         (∀ i, v (σ i) = s * ![1, -1, 0, 0] i + d) ∨
         (∀ i, v (σ i) = s * ![1, 1, 1, 0] i + d)) := by
  intro v hv
  obtain ⟨σ, s, d, hs, hrep⟩ := sumZero_point_reps v hv
  rcases hrep with h | h | h
  · exact ⟨σ, s, d, hs, Or.inl h⟩
  · exact ⟨σ, s, d, hs, Or.inr (Or.inl h)⟩
  · refine ⟨(Equiv.swap 1 3).trans σ, 2 * s, d, mul_ne_zero (by decide) hs,
      Or.inr (Or.inr ?_)⟩
    intro i
    rw [Equiv.trans_apply, h (Equiv.swap 1 3 i)]
    have hvec : (![2, 0, 2, 2] : Fin 4 → ZMod 3) (Equiv.swap 1 3 i) =
        2 * ![1, 1, 1, 0] i := by
      fin_cases i <;> decide
    rw [hvec]
    ring

private abbrev rep : Fin 3 → Fin 4 → ZMod 3
  | 0 => ![1, 1, -1, -1]
  | 1 => ![1, -1, 0, 0]
  | 2 => ![1, 1, 1, 0]

private abbrev HasRep (i : Fin 3) (v : Fin 4 → ZMod 3) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 4)) (s d : ZMod 3), s ≠ 0 ∧ ∀ j, v (σ j) = s * rep i j + d

private abbrev repVal : Fin 3 → ℕ := ![2, 1, 3]

private def countVal (v : Fin 4 → ZMod 3) (c : ZMod 3) : ℕ :=
  (Finset.univ.filter (fun i => v i = c)).card

private abbrev NC (u : Fin 4 → ZMod 3) : Prop := ¬ ∃ d : ZMod 3, u = fun _ => d

private abbrev vA1' : Fin 4 → ZMod 3 := ![1, 1, -1, -1]

private abbrev vA2' : Fin 4 → ZMod 3 := ![1, -1, 0, 0]

private abbrev vD2' : Fin 4 → ZMod 3 := ![0, 0, 1, -1]

private def classOf (u : Fin 4 → ZMod 3) : Fin 3 :=
  if countVal u 0 = 3 ∨ countVal u 1 = 3 ∨ countVal u 2 = 3 then 2
  else if countVal u 0 = 1 ∨ countVal u 1 = 1 ∨ countVal u 2 = 1 then 1
  else 0

private theorem hasRep_classOf : ∀ u : Fin 4 → ZMod 3, NC u → HasRep (classOf u) u := by
  decide

private theorem classOf_aux_a2 :
    ∀ w : Fin 4 → ZMod 3, NC w → NC (vA2' + w) → NC (vA2' + 2 • w) →
      ¬ (classOf w = 1 ∧ classOf (vA2' + w) = 1 ∧ classOf (vA2' + 2 • w) = 1) := by
  decide

private theorem classOf_aux_a1 :
    ∀ u : Fin 4 → ZMod 3, NC u → classOf u = 0 → NC (vA2' + u) →
      classOf (vA2' + u) = classOf (vA2' + vA1') → NC (vA2' + 2 • u) →
      classOf (vA2' + 2 • u) = classOf (vA2' + 2 • vA1') →
      ∃ s d : ZMod 3, s ≠ 0 ∧ u = s • vA1' + fun _ => d := by
  decide

private theorem classOf_aux_d2 :
    ∀ u : Fin 4 → ZMod 3, NC u → classOf u = 1 → NC (vA2' + u) →
      classOf (vA2' + u) = 0 → NC (vA2' + 2 • u) → classOf (vA2' + 2 • u) = 0 →
      ∃ s d : ZMod 3, s ≠ 0 ∧ u = s • vD2' + fun _ => d := by
  decide

namespace Case811L4

variable {c : Counterexample4 G} (t : Case811L4 c)

private theorem zpowers_mul_self {y : G} (hy : y ^ 3 = 1) :
    Subgroup.zpowers (y * y) = Subgroup.zpowers y := by
  have h2 : y * y = y⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa [pow_three, mul_assoc] using hy
  rw [h2, Subgroup.zpowers_inv]

private theorem zpowers_e_smul {w : Fin 4 → ZMod 3} {s : ZMod 3} (hs : s ≠ 0) :
    Subgroup.zpowers (t.e (Multiplicative.ofAdd (s • w))) =
      Subgroup.zpowers (t.e (Multiplicative.ofAdd w)) := by
  have hy : t.e (Multiplicative.ofAdd w) ^ 3 = 1 := t.e_pow_three _
  have hs12 : s = 1 ∨ s = 2 := by
    have h : ∀ s : ZMod 3, s ≠ 0 → s = 1 ∨ s = 2 := by decide
    exact h s hs
  rcases hs12 with rfl | rfl
  · simp
  · have h2 : (2 : ZMod 3) • w = w + w := by
      funext i
      rw [Pi.smul_apply, Pi.add_apply, two_smul]
    rw [h2, ofAdd_add, map_mul]
    exact zpowers_mul_self hy

theorem exists_conj_point {X : Subgroup G} (hXA : X ≤ t.A) (hX : Nat.card X = 3) :
    ∃ n ∈ c.L, n ∈ Subgroup.normalizer (t.A : Set G) ∧
      (X.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers t.a1 ∨
        X.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers t.a2 ∨
        X.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers t.a3) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hX
    omega
  obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hXne ((Subgroup.eq_bot_iff_forall X).mpr fun y hy => by
      by_contra hy1
      exact hy1 (h y hy))
  have hxpow : x ^ 3 = 1 := t.elemAbelian.2 x (hXA hxX)
  have hxord : orderOf x = 3 := orderOf_eq_prime hxpow hxne
  have hzX : Subgroup.zpowers x = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) (by
      rw [Nat.card_zpowers, hxord, hX])
  have hxA : x ∈ t.e.range := by
    rw [t.range_e]
    exact hXA hxX
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hxA
  have hvnc : ¬ ∃ d : ZMod 3, Multiplicative.toAdd v = fun _ => d := by
    rintro ⟨d, hd⟩
    apply hxne
    rw [← hv]
    exact (t.e_eq_one_iff v).mpr ⟨d, hd⟩
  obtain ⟨σ, s, d, hs, hrep⟩ := sumZero_point_reps_vA (Multiplicative.toAdd v) hvnc
  obtain ⟨n, hnL, hn⟩ := t.exists_perm σ
  have hconjx : n * x * n⁻¹ =
      t.e (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
    rw [← hv]
    exact hn v
  have hconst : t.e (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1 :=
    (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
  have hnNorm : n ∈ Subgroup.normalizer (t.A : Set G) := by
    have hle : Subgroup.map (MulAut.conj n).toMonoidHom t.A ≤ t.A := by
      rw [← t.range_e]
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp ha
      refine MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd fun i => Multiplicative.toAdd u (σ i),
        ?_⟩
      show t.e (Multiplicative.ofAdd fun i => Multiplicative.toAdd u (σ i)) = n * t.e u * n⁻¹
      exact (hn u).symm
    have hcard : Nat.card ↥(Subgroup.map (MulAut.conj n).toMonoidHom t.A) = Nat.card t.A :=
      Subgroup.card_map_of_injective (K := t.A) (f := (MulAut.conj n).toMonoidHom)
        (MulAut.conj n).injective
    have hmapA : Subgroup.map (MulAut.conj n).toMonoidHom t.A = t.A :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using hmapA)
  have key : ∀ (W : Fin 4 → ZMod 3) (a : G), t.e (Multiplicative.ofAdd W) = a →
      (∀ i, Multiplicative.toAdd v (σ i) = s * W i + d) →
      Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers a := by
    intro W a ha hW
    have hvec : (fun i => Multiplicative.toAdd v (σ i)) = s • W + (fun _ => d) := by
      funext i
      rw [hW i, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsplit : Multiplicative.ofAdd (fun i => Multiplicative.toAdd v (σ i)) =
        Multiplicative.ofAdd (s • W) * Multiplicative.ofAdd (fun _ : Fin 4 => d) := by
      rw [hvec, ofAdd_add]
    rw [hconjx, hsplit, map_mul, hconst, mul_one, ← ha]
    exact zpowers_e_smul t hs
  have hmap : X.map (MulAut.conj n).toMonoidHom = Subgroup.zpowers (n * x * n⁻¹) := by
    rw [← hzX, MonoidHom.map_zpowers]
    rfl
  refine ⟨n, hnL, hnNorm, ?_⟩
  rcases hrep with h1 | h2 | h3
  · left
    rw [hmap]
    exact key ![1, 1, -1, -1] t.a1 rfl h1
  · right; left
    rw [hmap]
    exact key ![1, -1, 0, 0] t.a2 rfl h2
  · right; right
    rw [hmap]
    exact key ![1, 1, 1, 0] t.a3 rfl h3

theorem factorization_card_centralizer_a2 :
    (Nat.card (Subgroup.centralizer ({t.a2} : Set G))).factorization t.r = 1 := by
  classical
  have hrp : t.r.Prime := t.mem_sigma.1.1
  haveI : Fact t.r.Prime := ⟨hrp⟩
  have hr5 : 5 ≤ t.r := t.five_le
  let C : Subgroup G := Subgroup.centralizer ({t.a2} : Set G)
  let CM : Subgroup G := c.S.M ⊓ C
  have hCMle : CM ≤ C := inf_le_right
  have hCMfac : (Nat.card CM).factorization t.r = 1 := by
    simpa [C, CM, Case811L4.a2] using t.factorization_a2
  obtain ⟨R0⟩ := (inferInstance : Nonempty (Sylow t.r CM))
  let R0g : Subgroup G := (R0 : Subgroup CM).map CM.subtype
  have hR0syl : CFSG.ABGLocalTools.IsSylowOf t.r R0g CM := ⟨R0, rfl⟩
  have hR0card : Nat.card R0g = t.r := by
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hR0syl, hCMfac, pow_one]
  have hR0M : R0g ≤ c.S.M := (Subgroup.map_subtype_le _).trans inf_le_left
  have hR0ne : R0g ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hR0card
    omega
  have hT : CFSG.ABGLocalTools.IsSylowOf t.r R0g (CM ⊓ C) := by
    rw [inf_eq_left.mpr hCMle]
    exact hR0syl
  have hN : Subgroup.normalizer (R0g : Set G) ⊓ C ≤ CM := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxM : x ∈ c.S.M :=
      (c.isStronglyPEmbedded_of_mem_sigma t.mem_sigma).normalizer_le hR0ne
        hR0syl.isPGroup hR0M hxN
    exact Subgroup.mem_inf.mpr ⟨hxM, hxC⟩
  have hSylC : CFSG.ABGLocalTools.IsSylowOf t.r R0g C :=
    CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hN
  have h1 : t.r ^ (Nat.card C).factorization t.r = t.r := by
    rw [← CFSG.ABGLocalTools.IsSylowOf.card_eq hSylC, hR0card]
  have h2 : t.r ^ (Nat.card C).factorization t.r = t.r ^ 1 := by simpa using h1
  simpa [C] using (Nat.pow_right_inj (by omega : 1 < t.r)).mp h2

private noncomputable def pointFactor (X : Subgroup G) : ℕ :=
  (Nat.card (Subgroup.centralizer (X : Set G))).factorization t.r

private theorem map_conj_centralizer (X : Subgroup G) (n : G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj n).toMonoidHom =
      Subgroup.centralizer ((X.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (X : Set G) (MulAut.conj n).toMonoidHom
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy
    refine Subgroup.mem_map.mpr ⟨n⁻¹ * y * n, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := hy (n * x * n⁻¹) (Subgroup.mem_map_of_mem _ hx)
      calc x * (n⁻¹ * y * n) = n⁻¹ * ((n * x * n⁻¹) * y) * n := by group
        _ = n⁻¹ * (y * (n * x * n⁻¹)) * n := by rw [h]
        _ = (n⁻¹ * y * n) * x := by group
    · show n * (n⁻¹ * y * n) * n⁻¹ = y
      group

private theorem pointFactor_map_conj (X : Subgroup G) (n : G) :
    t.pointFactor (X.map (MulAut.conj n).toMonoidHom) = t.pointFactor X := by
  unfold pointFactor
  rw [← map_conj_centralizer]
  exact congrArg (fun m => m.factorization t.r)
    (Subgroup.card_map_of_injective (K := Subgroup.centralizer (X : Set G))
      (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective)

private theorem pointFactor_zpowers (x : G) :
    t.pointFactor (Subgroup.zpowers x) =
      (Nat.card (Subgroup.centralizer ({x} : Set G))).factorization t.r := by
  unfold pointFactor
  have h : ((Subgroup.zpowers x : Subgroup G) : Set G) =
      ((Subgroup.closure {x} : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure]
  rw [h, Subgroup.centralizer_closure]

private theorem pointFactor_zpowers_a1
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M) :
    t.pointFactor (Subgroup.zpowers t.a1) = 2 := by
  rw [pointFactor_zpowers]
  have hle : Subgroup.centralizer ({t.a1} : Set G) ≤ c.S.M :=
    (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers t.a1).trans hN1
  rw [← inf_eq_right.mpr hle]
  simpa [Case811L4.a1] using t.factorization_a1

private theorem pointFactor_zpowers_a2 :
    t.pointFactor (Subgroup.zpowers t.a2) = 1 := by
  rw [pointFactor_zpowers]
  exact factorization_card_centralizer_a2 t

private theorem pointFactor_zpowers_a3
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    t.pointFactor (Subgroup.zpowers t.a3) = 3 := by
  rw [pointFactor_zpowers]
  have hle : Subgroup.centralizer ({t.a3} : Set G) ≤ c.S.M :=
    (CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers t.a3).trans hN3
  rw [← inf_eq_right.mpr hle]
  simpa [Case811L4.a3] using t.factorization_a3

private theorem repVal_inj {i j : Fin 3} (h : repVal i = repVal j) : i = j := by
  revert i j
  decide

private theorem pointFactor_of_hasRep
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {i : Fin 3} {v : Fin 4 → ZMod 3} (h : HasRep i v) :
    t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd v))) = repVal i := by
  obtain ⟨σ, s, d, hs, hv⟩ := h
  obtain ⟨n, hnL, hn⟩ := t.exists_perm σ
  have hconst : t.e (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1 :=
    (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
  have hvec : (fun j => v (σ j)) = s • rep i + (fun _ : Fin 4 => d) := by
    funext j
    rw [hv j, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hconj : n * t.e (Multiplicative.ofAdd v) * n⁻¹ =
      t.e (Multiplicative.ofAdd (s • rep i)) := by
    rw [hn (Multiplicative.ofAdd v)]
    simp only [toAdd_ofAdd]
    have hsplit : Multiplicative.ofAdd (fun j => v (σ j)) =
        Multiplicative.ofAdd (s • rep i) * Multiplicative.ofAdd (fun _ : Fin 4 => d) := by
      rw [hvec, ofAdd_add]
    rw [hsplit, map_mul, hconst, mul_one]
  have h1 : t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd v))) =
      t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd (s • rep i)))) := by
    rw [← pointFactor_map_conj t (Subgroup.zpowers (t.e (Multiplicative.ofAdd v))) n,
      MonoidHom.map_zpowers]
    change t.pointFactor (Subgroup.zpowers (n * t.e (Multiplicative.ofAdd v) * n⁻¹)) =
      t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd (s • rep i))))
    rw [hconj]
  have h2 : t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd (s • rep i)))) =
      t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd (rep i)))) := by
    rw [zpowers_e_smul t hs]
  have h3 : t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd (rep i)))) = repVal i := by
    fin_cases i
    · simpa [rep, repVal, Case811L4.a1, Case811L4.vA1] using pointFactor_zpowers_a1 t hN1
    · simpa [rep, repVal, Case811L4.a2, Case811L4.vA2] using pointFactor_zpowers_a2 t
    · simpa [rep, repVal, Case811L4.a3, Case811L4.vA3] using pointFactor_zpowers_a3 t hN3
  rw [h1, h2, h3]

private theorem hasRep_of_pointFactor
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {i : Fin 3} {v : Fin 4 → ZMod 3}
    (hv : ¬ ∃ d : ZMod 3, v = fun _ => d)
    (h : t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd v))) = repVal i) :
    HasRep i v := by
  obtain ⟨σ, s, d, hs, hrep⟩ := sumZero_point_reps_vA v hv
  have key : ∀ (k : Fin 3), (∀ j, v (σ j) = s * rep k j + d) → k = i := by
    intro k hk
    have h1 := pointFactor_of_hasRep t hN1 hN3 (i := k) ⟨σ, s, d, hs, hk⟩
    have h2 : repVal k = repVal i := by rw [← h1, h]
    exact repVal_inj h2
  rcases hrep with h0 | h1 | h2
  · rw [← key 0 h0]
    exact ⟨σ, s, d, hs, h0⟩
  · rw [← key 1 h1]
    exact ⟨σ, s, d, hs, h1⟩
  · rw [← key 2 h2]
    exact ⟨σ, s, d, hs, h2⟩

private theorem a1_ne_one : t.a1 ≠ 1 := by
  intro h
  have hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd Case811L4.vA1 = fun _ => s := by decide
  have hord := t.orderOf_e hv
  have h' : t.e Case811L4.vA1 = 1 := h
  rw [h', orderOf_one] at hord
  exact absurd hord (by norm_num)

private theorem d2_ne_one : t.d2 ≠ 1 := by
  intro h
  have hv : ¬ ∃ s : ZMod 3, Multiplicative.toAdd Case811L4.vD2 = fun _ => s := by decide
  have hord := t.orderOf_e hv
  have h' : t.e Case811L4.vD2 = 1 := h
  rw [h', orderOf_one] at hord
  exact absurd hord (by norm_num)

private noncomputable def pf (x : G) : ℕ := t.pointFactor (Subgroup.zpowers x)

private theorem pf_conj (x g : G) : pf t (g * x * g⁻¹) = pf t x := by
  show t.pointFactor (Subgroup.zpowers (g * x * g⁻¹)) = t.pointFactor (Subgroup.zpowers x)
  have h : Subgroup.zpowers (g * x * g⁻¹) =
      (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom :=
    (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom x).symm
  rw [h, pointFactor_map_conj t]

private theorem pf_e
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {u : Fin 4 → ZMod 3} (hu : NC u) :
    pf t (t.e (Multiplicative.ofAdd u)) = repVal (classOf u) :=
  pointFactor_of_hasRep t hN1 hN3 (hasRep_classOf u hu)

private theorem e_add (a b : Fin 4 → ZMod 3) :
    t.e (Multiplicative.ofAdd (a + b)) =
      t.e (Multiplicative.ofAdd a) * t.e (Multiplicative.ofAdd b) := by
  rw [← map_mul, ← ofAdd_add]

private theorem e_sq (c : Fin 4 → ZMod 3) :
    t.e (Multiplicative.ofAdd c) ^ 2 = t.e (Multiplicative.ofAdd (2 • c)) := by
  rw [sq, ← e_add]
  congr 1
  exact (two_nsmul c).symm

private theorem a2_mul_e (u : Fin 4 → ZMod 3) :
    t.a2 * t.e (Multiplicative.ofAdd u) = t.e (Multiplicative.ofAdd (vA2' + u)) := by
  show t.e (Multiplicative.ofAdd vA2') * t.e (Multiplicative.ofAdd u) = _
  rw [← e_add]

private theorem a2_mul_e_sq (u : Fin 4 → ZMod 3) :
    t.a2 * t.e (Multiplicative.ofAdd u) ^ 2 =
      t.e (Multiplicative.ofAdd (vA2' + 2 • u)) := by
  rw [e_sq]
  show t.e (Multiplicative.ofAdd vA2') * t.e (Multiplicative.ofAdd (2 • u)) = _
  rw [← e_add]

private theorem a2_mul_e_ne_one {w : Fin 4 → ZMod 3} (h : NC (vA2' + w)) :
    t.a2 * t.e (Multiplicative.ofAdd w) ≠ 1 := by
  intro h1
  apply h
  have h2 : t.e (Multiplicative.ofAdd (vA2' + w)) = 1 := by
    rw [e_add]
    exact h1
  exact (by simpa using (t.e_eq_one_iff _).mp h2)

private theorem a2_mul_e_sq_ne_one {w : Fin 4 → ZMod 3} (h : NC (vA2' + 2 • w)) :
    t.a2 * t.e (Multiplicative.ofAdd w) ^ 2 ≠ 1 := by
  intro h1
  apply h
  have h2 : t.e (Multiplicative.ofAdd (vA2' + 2 • w)) = 1 := by
    rw [e_add, ← e_sq]
    exact h1
  exact (by simpa using (t.e_eq_one_iff _).mp h2)

private theorem pf_e_ne_one
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {u : Fin 4 → ZMod 3} (hu : NC u) (h : classOf u ≠ 1) :
    pf t (t.e (Multiplicative.ofAdd u)) ≠ 1 := by
  rw [pf_e t hN1 hN3 hu]
  intro h1
  exact h (repVal_inj (by simpa [repVal] using h1))

private theorem mem_normalizer_zpowers_of_conj_eq {a z g n₁ n₂ : G}
    (h1 : Subgroup.zpowers (n₁ * z * n₁⁻¹) = Subgroup.zpowers a)
    (h2 : Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = Subgroup.zpowers a) :
    n₂ * g * n₁⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have hka : Subgroup.zpowers ((n₂ * g * n₁⁻¹) * a * (n₂ * g * n₁⁻¹)⁻¹) =
      Subgroup.zpowers a := by
    change Subgroup.zpowers ((MulAut.conj (n₂ * g * n₁⁻¹)).toMonoidHom a) =
      Subgroup.zpowers a
    rw [← MonoidHom.map_zpowers (f := (MulAut.conj (n₂ * g * n₁⁻¹)).toMonoidHom)]
    have step : Subgroup.map (MulAut.conj (n₂ * g * n₁⁻¹)).toMonoidHom
          (Subgroup.zpowers a) =
        Subgroup.map (MulAut.conj (n₂ * g * n₁⁻¹)).toMonoidHom
          (Subgroup.zpowers (n₁ * z * n₁⁻¹)) := by rw [h1]
    rw [step, MonoidHom.map_zpowers]
    have hk : (MulAut.conj (n₂ * g * n₁⁻¹)).toMonoidHom (n₁ * z * n₁⁻¹) =
        n₂ * (g * z * g⁻¹) * n₂⁻¹ := by
      change (n₂ * g * n₁⁻¹) * (n₁ * z * n₁⁻¹) * (n₂ * g * n₁⁻¹)⁻¹ =
        n₂ * (g * z * g⁻¹) * n₂⁻¹
      group
    rw [hk, h2]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  exact hka

private theorem mem_M_of_conj_mem_A
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {z g : G} (hz : z ∈ t.A) (hz1 : z ≠ 1) (hpf : pf t z = 2 ∨ pf t z = 3)
    (hg : g * z * g⁻¹ ∈ t.A) : g ∈ c.S.M := by
  have hz3 : z ^ 3 = 1 := t.elemAbelian.2 z hz
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hXcard : Nat.card (Subgroup.zpowers z) = 3 := by
    rw [Nat.card_zpowers, hzord]
  have hXA : Subgroup.zpowers z ≤ t.A := Subgroup.zpowers_le.mpr hz
  have hw3 : (g * z * g⁻¹) ^ 3 = 1 := t.elemAbelian.2 _ hg
  have hw1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hYcard : Nat.card (Subgroup.zpowers (g * z * g⁻¹)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hYA : Subgroup.zpowers (g * z * g⁻¹) ≤ t.A := Subgroup.zpowers_le.mpr hg
  obtain ⟨n₁, hn₁L, -, hX1⟩ := t.exists_conj_point hXA hXcard
  obtain ⟨n₂, hn₂L, -, hY1⟩ := t.exists_conj_point hYA hYcard
  have hXz : Subgroup.zpowers (n₁ * z * n₁⁻¹) = Subgroup.zpowers t.a1 ∨
      Subgroup.zpowers (n₁ * z * n₁⁻¹) = Subgroup.zpowers t.a2 ∨
      Subgroup.zpowers (n₁ * z * n₁⁻¹) = Subgroup.zpowers t.a3 := by
    have h := hX1
    rw [MonoidHom.map_zpowers] at h
    exact h
  have hYz : Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = Subgroup.zpowers t.a1 ∨
      Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = Subgroup.zpowers t.a2 ∨
      Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = Subgroup.zpowers t.a3 := by
    have h := hY1
    rw [MonoidHom.map_zpowers] at h
    exact h
  have hXpf : ∀ {P : Subgroup G}, Subgroup.zpowers (n₁ * z * n₁⁻¹) = P →
      t.pointFactor P = pf t z := by
    intro P hP
    rw [← hP]
    exact pf_conj t z n₁
  have hYpf : ∀ {P : Subgroup G},
      Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = P → t.pointFactor P = pf t z := by
    intro P hP
    rw [← hP]
    exact (pf_conj t (g * z * g⁻¹) n₂).trans (pf_conj t z g)
  have hmem : ∀ {a : G}, Subgroup.zpowers (n₁ * z * n₁⁻¹) = Subgroup.zpowers a →
      Subgroup.zpowers (n₂ * (g * z * g⁻¹) * n₂⁻¹) = Subgroup.zpowers a →
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ c.S.M → g ∈ c.S.M := by
    intro a h1 h2 hNa
    have hk := mem_normalizer_zpowers_of_conj_eq (z := z) (g := g) (n₁ := n₁) h1 h2
    have hkM : n₂ * g * n₁⁻¹ ∈ c.S.M := hNa hk
    have hn₁M : n₁ ∈ c.S.M := c.hyp81.1 hn₁L
    have hn₂M : n₂ ∈ c.S.M := c.hyp81.1 hn₂L
    have hg_eq : g = n₂⁻¹ * (n₂ * g * n₁⁻¹) * n₁ := by group
    rw [hg_eq]
    exact c.S.M.mul_mem (c.S.M.mul_mem (c.S.M.inv_mem hn₂M) hkM) hn₁M
  rcases hXz with hXa | hXa | hXa <;> rcases hYz with hYa | hYa | hYa
  · exact hmem hXa hYa hN1
  · exfalso
    have h1 : pf t z = 2 := (hXpf hXa).symm.trans (pointFactor_zpowers_a1 t hN1)
    have h2 : pf t z = 1 := (hYpf hYa).symm.trans (pointFactor_zpowers_a2 t)
    omega
  · exfalso
    have h1 : pf t z = 2 := (hXpf hXa).symm.trans (pointFactor_zpowers_a1 t hN1)
    have h2 : pf t z = 3 := (hYpf hYa).symm.trans (pointFactor_zpowers_a3 t hN3)
    omega
  · exfalso
    have h1 : pf t z = 1 := (hXpf hXa).symm.trans (pointFactor_zpowers_a2 t)
    have h2 : pf t z = 2 := (hYpf hYa).symm.trans (pointFactor_zpowers_a1 t hN1)
    omega
  · exfalso
    have h1 : pf t z = 1 := (hXpf hXa).symm.trans (pointFactor_zpowers_a2 t)
    rcases hpf with hpf | hpf <;> omega
  · exfalso
    have h1 : pf t z = 1 := (hXpf hXa).symm.trans (pointFactor_zpowers_a2 t)
    have h2 : pf t z = 3 := (hYpf hYa).symm.trans (pointFactor_zpowers_a3 t hN3)
    omega
  · exfalso
    have h1 : pf t z = 3 := (hXpf hXa).symm.trans (pointFactor_zpowers_a3 t hN3)
    have h2 : pf t z = 2 := (hYpf hYa).symm.trans (pointFactor_zpowers_a1 t hN1)
    omega
  · exfalso
    have h1 : pf t z = 3 := (hXpf hXa).symm.trans (pointFactor_zpowers_a3 t hN3)
    have h2 : pf t z = 1 := (hYpf hYa).symm.trans (pointFactor_zpowers_a2 t)
    omega
  · exact hmem hXa hYa hN3

private theorem pf_eq_two_or_three
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {z : G} (hzA : z ∈ t.A) (hz1 : z ≠ 1) (hzpf : pf t z ≠ 1) :
    pf t z = 2 ∨ pf t z = 3 := by
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (by rwa [t.range_e] : z ∈ t.e.range)
  have hwe : z = t.e (Multiplicative.ofAdd (Multiplicative.toAdd w)) := by
    rw [ofAdd_toAdd]
    exact hw.symm
  have hu : NC (Multiplicative.toAdd w) := by
    rintro ⟨d, hd⟩
    apply hz1
    rw [hwe, hd]
    exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
  have h1 : pf t z = repVal (classOf (Multiplicative.toAdd w)) := by
    rw [hwe]
    exact pf_e t hN1 hN3 hu
  have hdisp := (show ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 from by decide)
    (classOf (Multiplicative.toAdd w))
  rcases hdisp with hd | hd | hd
  · left
    rw [h1, hd]
    simp [repVal]
  · exfalso
    apply hzpf
    rw [h1, hd]
    simp [repVal]
  · right
    rw [h1, hd]
    simp [repVal]

private theorem exists_pf_ne_one_mem
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {B : Subgroup G} (hBA : B ≤ t.A) (hB : Nat.card B = 9) :
    ∃ z ∈ B, z ≠ 1 ∧ pf t z ≠ 1 := by
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB
    omega
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hBne ((Subgroup.eq_bot_iff_forall B).mpr fun y hy => by
      by_contra hy1
      exact hy1 (h y hy))
  by_cases hxpf : pf t x ≠ 1
  · exact ⟨x, hxB, hx1, hxpf⟩
  · push Not at hxpf
    have hxA : x ∈ t.A := hBA hxB
    have hx3 : x ^ 3 = 1 := t.elemAbelian.2 x hxA
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hXcard : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxord]
    obtain ⟨n, hnL, hnA, hX1⟩ :=
      t.exists_conj_point (Subgroup.zpowers_le.mpr hxA) hXcard
    have hXz : Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers t.a1 ∨
        Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers t.a2 ∨
        Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers t.a3 := by
      have h := hX1
      rw [MonoidHom.map_zpowers] at h
      exact h
    have hxa : Subgroup.zpowers (n * x * n⁻¹) = Subgroup.zpowers t.a2 := by
      rcases hXz with h | h | h
      · exfalso
        have h2 : t.pointFactor (Subgroup.zpowers t.a1) = pf t x := by
          rw [← h]
          exact pf_conj t x n
        rw [pointFactor_zpowers_a1 t hN1] at h2
        omega
      · exact h
      · exfalso
        have h2 : t.pointFactor (Subgroup.zpowers t.a3) = pf t x := by
          rw [← h]
          exact pf_conj t x n
        rw [pointFactor_zpowers_a3 t hN3] at h2
        omega
    let B' : Subgroup G := B.map (MulAut.conj n).toMonoidHom
    have hB'A : B' ≤ t.A := by
      intro y hy
      obtain ⟨b, hbB, hbe⟩ := Subgroup.mem_map.mp hy
      rw [← hbe]
      exact (Subgroup.mem_normalizer_iff.mp hnA b).mp (hBA hbB)
    have hB'card : Nat.card B' = 9 := by
      rw [show Nat.card B' = Nat.card B from
        Subgroup.card_map_of_injective (K := B) (f := (MulAut.conj n).toMonoidHom)
          (MulAut.conj n).injective, hB]
    have ha2B' : t.a2 ∈ B' := by
      have hle : Subgroup.zpowers t.a2 ≤ B' := by
        rw [← hxa]
        exact Subgroup.zpowers_le.mpr
          (Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hxB)
      exact hle (Subgroup.mem_zpowers _)
    have hne : B' ≠ Subgroup.zpowers t.a2 := by
      intro heq
      rw [heq] at hB'card
      have hcarda2 : Nat.card (Subgroup.zpowers t.a2) = 3 :=
        t.card_zpowers_e (v := Case811L4.vA2) (by decide)
      omega
    have hnotle : ¬ B' ≤ Subgroup.zpowers t.a2 := by
      intro hle
      exact hne (le_antisymm hle (Subgroup.zpowers_le.mpr ha2B'))
    obtain ⟨y, hyB', hyz⟩ : ∃ y ∈ B', y ∉ Subgroup.zpowers t.a2 := by
      by_contra h
      push Not at h
      exact hnotle fun z hz => h z hz
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (by
      rw [t.range_e]
      exact hB'A hyB')
    let u : Fin 4 → ZMod 3 := Multiplicative.toAdd w
    have hydef : y = t.e (Multiplicative.ofAdd u) := by
      rw [← hw, show Multiplicative.ofAdd u = w from ofAdd_toAdd w]
    have hy1 : y ≠ 1 := by
      intro h
      rw [h] at hyz
      exact hyz (Subgroup.one_mem _)
    have hy3 : y ^ 3 = 1 := t.elemAbelian.2 y (hB'A hyB')
    have hu : NC u := by
      rintro ⟨d, hd⟩
      apply hy1
      rw [hydef, hd]
      exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
    have hnc1 : NC (vA2' + u) := by
      rintro ⟨d, hd⟩
      apply hyz
      have h1 : t.a2 * y = 1 := by
        rw [hydef, a2_mul_e, hd]
        exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
      have h2 : y = t.a2⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    have hnc2 : NC (vA2' + 2 • u) := by
      rintro ⟨d, hd⟩
      apply hyz
      have h1 : t.a2 * y ^ 2 = 1 := by
        rw [hydef, a2_mul_e_sq, hd]
        exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
      have h2 : y ^ 2 = t.a2⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : y = (y ^ 2) ^ 2 := by
        calc y = y * y ^ 3 := by rw [hy3, mul_one]
          _ = (y ^ 2) ^ 2 := by group
      rw [h3, h2]
      exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) 2
    have hcand : classOf u ≠ 1 ∨ classOf (vA2' + u) ≠ 1 ∨
        classOf (vA2' + 2 • u) ≠ 1 := by
      by_contra h
      push Not at h
      exact classOf_aux_a2 u hu hnc1 hnc2 ⟨h.1, h.2.1, h.2.2⟩
    rcases hcand with h | h | h
    · have hne1 : pf t y ≠ 1 := by
        rw [hydef]
        exact pf_e_ne_one t hN1 hN3 hu h
      obtain ⟨b, hbB, hbe⟩ := Subgroup.mem_map.mp hyB'
      refine ⟨n⁻¹ * y * n, ?_, ?_, ?_⟩
      · have hconj : (MulAut.conj n).toMonoidHom b = n * b * n⁻¹ := rfl
        have hb_eq : n⁻¹ * y * n = b := by
          rw [← hbe, hconj]
          group
        rwa [hb_eq]
      · intro h1
        apply hy1
        calc y = n * (n⁻¹ * y * n) * n⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · have h2 := pf_conj t y n⁻¹
        rw [inv_inv] at h2
        rwa [h2]
    · obtain ⟨b, hbB, hbe⟩ := Subgroup.mem_map.mp (B'.mul_mem ha2B' hyB')
      have hne1 : t.a2 * y ≠ 1 := by
        rw [hydef]
        exact a2_mul_e_ne_one t hnc1
      have hne2 : pf t (t.a2 * y) ≠ 1 := by
        rw [hydef, a2_mul_e]
        exact pf_e_ne_one t hN1 hN3 hnc1 h
      refine ⟨n⁻¹ * (t.a2 * y) * n, ?_, ?_, ?_⟩
      · have hconj : (MulAut.conj n).toMonoidHom b = n * b * n⁻¹ := rfl
        have hb_eq : n⁻¹ * (t.a2 * y) * n = b := by
          rw [← hbe, hconj]
          group
        rwa [hb_eq]
      · intro h1
        apply hne1
        calc t.a2 * y = n * (n⁻¹ * (t.a2 * y) * n) * n⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · have h2 := pf_conj t (t.a2 * y) n⁻¹
        rw [inv_inv] at h2
        rwa [h2]
    · obtain ⟨b, hbB, hbe⟩ :=
        Subgroup.mem_map.mp (B'.mul_mem ha2B' (B'.pow_mem hyB' 2))
      have hne1 : t.a2 * y ^ 2 ≠ 1 := by
        rw [hydef]
        exact a2_mul_e_sq_ne_one t hnc2
      have hne2 : pf t (t.a2 * y ^ 2) ≠ 1 := by
        rw [hydef, a2_mul_e_sq]
        exact pf_e_ne_one t hN1 hN3 hnc2 h
      refine ⟨n⁻¹ * (t.a2 * y ^ 2) * n, ?_, ?_, ?_⟩
      · have hconj : (MulAut.conj n).toMonoidHom b = n * b * n⁻¹ := rfl
        have hb_eq : n⁻¹ * (t.a2 * y ^ 2) * n = b := by
          rw [← hbe, hconj]
          group
        rwa [hb_eq]
      · intro h1
        apply hne1
        calc t.a2 * y ^ 2 = n * (n⁻¹ * (t.a2 * y ^ 2) * n) * n⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · have h2 := pf_conj t (t.a2 * y ^ 2) n⁻¹
        rw [inv_inv] at h2
        rwa [h2]

theorem normalizer_le_of_le_A_of_card_nine
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {B : Subgroup G} (hBA : B ≤ t.A) (hB : Nat.card B = 9) :
    Subgroup.normalizer (B : Set G) ≤ c.S.M := by
  intro g hg
  obtain ⟨z, hzB, hz1, hzpf⟩ := exists_pf_ne_one_mem t hN1 hN3 hBA hB
  have hzA : z ∈ t.A := hBA hzB
  have hz23 : pf t z = 2 ∨ pf t z = 3 := pf_eq_two_or_three t hN1 hN3 hzA hz1 hzpf
  have hgz : g * z * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg z).mp hzB
  exact mem_M_of_conj_mem_A t hN1 hN3 hzA hz1 hz23 (hBA hgz)

private theorem mem_normalizer_zpowers_of_exists_smul
    {y n : G} {w u : Fin 4 → ZMod 3} (hw : NC w)
    (hy : y = t.e (Multiplicative.ofAdd w))
    (hx : n * y * n⁻¹ = t.e (Multiplicative.ofAdd u))
    (hsmul : ∃ s d : ZMod 3, s ≠ 0 ∧ u = s • w + fun _ => d) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
  obtain ⟨s, d, hs, hu⟩ := hsmul
  subst hu
  have hconst : t.e (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1 :=
    (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
  have hx' : n * y * n⁻¹ = t.e (Multiplicative.ofAdd (s • w)) := by
    rw [hx, e_add, hconst, mul_one]
  have hcardy : Nat.card (Subgroup.zpowers y) = 3 := by
    rw [hy]
    exact t.card_zpowers_e hw
  have hcardx : Nat.card (Subgroup.zpowers (n * y * n⁻¹)) = 3 := by
    rw [hx', zpowers_e_smul t (w := w) hs, ← hy, hcardy]
  have hmem : n * y * n⁻¹ ∈ Subgroup.zpowers y := by
    rw [hx', hy, ← zpowers_e_smul t (w := w) hs]
    exact Subgroup.mem_zpowers _
  have hzeq : Subgroup.zpowers (n * y * n⁻¹) = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (by rw [hcardy, hcardx])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  exact hzeq

private theorem classOf_conj_companions
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M)
    {n y : G} {w u : Fin 4 → ZMod 3}
    (hw : NC w) (hncc1 : NC (vA2' + w)) (hncc2 : NC (vA2' + 2 • w))
    (hy : y = t.e (Multiplicative.ofAdd w)) (hy1 : y ≠ 1)
    (hn : n * t.a2 = t.a2 * n)
    (hne1 : t.a2 * y ≠ 1) (hne2 : t.a2 * y ^ 2 ≠ 1)
    (hx : n * y * n⁻¹ = t.e (Multiplicative.ofAdd u)) :
    NC u ∧ classOf u = classOf w ∧ NC (vA2' + u) ∧
      classOf (vA2' + u) = classOf (vA2' + w) ∧ NC (vA2' + 2 • u) ∧
        classOf (vA2' + 2 • u) = classOf (vA2' + 2 • w) := by
  have hyx : n * y * n⁻¹ ≠ 1 := by
    intro h
    apply hy1
    calc y = n⁻¹ * (n * y * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hu : NC u := by
    rintro ⟨d, hd⟩
    apply hyx
    rw [hx, hd]
    exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
  have hclu : classOf u = classOf w := by
    apply repVal_inj
    have h1 : pf t (n * y * n⁻¹) = repVal (classOf u) := by
      rw [hx]
      exact pf_e t hN1 hN3 hu
    have h2 : pf t y = repVal (classOf w) := by
      rw [hy]
      exact pf_e t hN1 hN3 hw
    rw [← h1, pf_conj t y n, h2]
  have hcomp : t.a2 * (n * y * n⁻¹) = n * (t.a2 * y) * n⁻¹ := by
    calc t.a2 * (n * y * n⁻¹) = (t.a2 * n) * y * n⁻¹ := by group
      _ = (n * t.a2) * y * n⁻¹ := by rw [show t.a2 * n = n * t.a2 from hn.symm]
      _ = n * (t.a2 * y) * n⁻¹ := by group
  have hpow : (n * y * n⁻¹) ^ 2 = n * y ^ 2 * n⁻¹ := by
    calc (n * y * n⁻¹) ^ 2 = (n * y * n⁻¹) * (n * y * n⁻¹) := sq _
      _ = n * (y * y) * n⁻¹ := by group
      _ = n * y ^ 2 * n⁻¹ := by rw [sq]
  have hcomp2 : t.a2 * (n * y * n⁻¹) ^ 2 = n * (t.a2 * y ^ 2) * n⁻¹ := by
    rw [hpow]
    calc t.a2 * (n * y ^ 2 * n⁻¹) = (t.a2 * n) * y ^ 2 * n⁻¹ := by group
      _ = (n * t.a2) * y ^ 2 * n⁻¹ := by rw [show t.a2 * n = n * t.a2 from hn.symm]
      _ = n * (t.a2 * y ^ 2) * n⁻¹ := by group
  have hnc1 : NC (vA2' + u) := by
    rintro ⟨d, hd⟩
    apply hne1
    have h1 : t.a2 * (n * y * n⁻¹) = 1 := by
      rw [hx, a2_mul_e, hd]
      exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
    rw [hcomp] at h1
    calc t.a2 * y = n⁻¹ * (n * (t.a2 * y) * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hcl1 : classOf (vA2' + u) = classOf (vA2' + w) := by
    apply repVal_inj
    have h1 : pf t (t.a2 * (n * y * n⁻¹)) = repVal (classOf (vA2' + u)) := by
      rw [hx, a2_mul_e]
      exact pf_e t hN1 hN3 hnc1
    have h2 : pf t (t.a2 * y) = repVal (classOf (vA2' + w)) := by
      rw [hy, a2_mul_e]
      exact pf_e t hN1 hN3 hncc1
    rw [← h1, hcomp]
    exact (pf_conj t (t.a2 * y) n).trans h2
  have hnc2 : NC (vA2' + 2 • u) := by
    rintro ⟨d, hd⟩
    apply hne2
    have h1 : t.a2 * (n * y * n⁻¹) ^ 2 = 1 := by
      rw [hx, a2_mul_e_sq, hd]
      exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
    rw [hcomp2] at h1
    calc t.a2 * y ^ 2 = n⁻¹ * (n * (t.a2 * y ^ 2) * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  have hcl2 : classOf (vA2' + 2 • u) = classOf (vA2' + 2 • w) := by
    apply repVal_inj
    have h1 : pf t (t.a2 * (n * y * n⁻¹) ^ 2) =
        repVal (classOf (vA2' + 2 • u)) := by
      rw [hx, a2_mul_e_sq]
      exact pf_e t hN1 hN3 hnc2
    have h2 : pf t (t.a2 * y ^ 2) = repVal (classOf (vA2' + 2 • w)) := by
      rw [hy, a2_mul_e_sq]
      exact pf_e t hN1 hN3 hncc2
    rw [← h1, hcomp2]
    exact (pf_conj t (t.a2 * y ^ 2) n).trans h2
  exact ⟨hu, hclu, hnc1, hcl1, hnc2, hcl2⟩

theorem mem_normalizer_zpowers_of_mem_normalizer_A
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) {n : G}
    (hnA : n ∈ Subgroup.normalizer (t.A : Set G)) (hn : n * t.a2 = t.a2 * n) :
    n ∈ Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ∧
      n ∈ Subgroup.normalizer ((Subgroup.zpowers t.d2 : Subgroup G) : Set G) := by
  constructor
  · have hx'A : n * t.a1 * n⁻¹ ∈ t.A :=
      (Subgroup.mem_normalizer_iff.mp hnA t.a1).mp (t.e_mem_A _)
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (by
      rwa [t.range_e] : n * t.a1 * n⁻¹ ∈ t.e.range)
    let u : Fin 4 → ZMod 3 := Multiplicative.toAdd w
    have hx : n * t.a1 * n⁻¹ = t.e (Multiplicative.ofAdd u) := by
      rw [← hw, show Multiplicative.ofAdd u = w from ofAdd_toAdd w]
    have hy : t.a1 = t.e (Multiplicative.ofAdd vA1') := rfl
    obtain ⟨hu, hclu, hnc1, hcl1, hnc2, hcl2⟩ :=
      classOf_conj_companions t hN1 hN3 (by decide : NC vA1')
        (by decide : NC (vA2' + vA1')) (by decide : NC (vA2' + 2 • vA1')) hy t.a1_ne_one hn
        (a2_mul_e_ne_one t (w := vA1') (by decide))
        (a2_mul_e_sq_ne_one t (w := vA1') (by decide)) hx
    have hclu' : classOf u = 0 := by rw [hclu]; decide
    have hsmul := classOf_aux_a1 u hu hclu' hnc1 hcl1 hnc2 hcl2
    exact mem_normalizer_zpowers_of_exists_smul t (w := vA1') (by decide) hy hx hsmul
  · have hx''A : n * t.d2 * n⁻¹ ∈ t.A :=
      (Subgroup.mem_normalizer_iff.mp hnA t.d2).mp (t.e_mem_A _)
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (by
      rwa [t.range_e] : n * t.d2 * n⁻¹ ∈ t.e.range)
    let u : Fin 4 → ZMod 3 := Multiplicative.toAdd w
    have hx : n * t.d2 * n⁻¹ = t.e (Multiplicative.ofAdd u) := by
      rw [← hw, show Multiplicative.ofAdd u = w from ofAdd_toAdd w]
    have hy : t.d2 = t.e (Multiplicative.ofAdd vD2') := rfl
    obtain ⟨hu, hclu, hnc1, hcl1, hnc2, hcl2⟩ :=
      classOf_conj_companions t hN1 hN3 (by decide : NC vD2')
        (by decide : NC (vA2' + vD2')) (by decide : NC (vA2' + 2 • vD2')) hy t.d2_ne_one hn
        (a2_mul_e_ne_one t (w := vD2') (by decide))
        (a2_mul_e_sq_ne_one t (w := vD2') (by decide)) hx
    have hclu' : classOf u = 1 := by rw [hclu]; decide
    have hcl1' : classOf (vA2' + u) = 0 := by rw [hcl1]; decide
    have hcl2' : classOf (vA2' + 2 • u) = 0 := by rw [hcl2]; decide
    have hsmul := classOf_aux_d2 u hu hclu' hnc1 hcl1' hnc2 hcl2'
    exact mem_normalizer_zpowers_of_exists_smul t (w := vD2') (by decide) hy hx hsmul

theorem normalizer_A_le
    (hN1 : Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) ≤ c.S.M)
    (hN3 : Subgroup.normalizer ((Subgroup.zpowers t.a3 : Subgroup G) : Set G) ≤ c.S.M) :
    Subgroup.normalizer (t.A : Set G) ≤ c.S.M := by
  intro g hg
  have ha1A : t.a1 ∈ t.A := t.e_mem_A _
  have hmem : g * t.a1 * g⁻¹ ∈ t.A := (Subgroup.mem_normalizer_iff.mp hg t.a1).mp ha1A
  have hmem' : g * t.a1 * g⁻¹ ∈ t.e.range := by
    rw [t.range_e]
    exact hmem
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hmem' 
  let v : Fin 4 → ZMod 3 := Multiplicative.toAdd w
  have hw' : t.e (Multiplicative.ofAdd v) = g * t.a1 * g⁻¹ := by
    rw [ofAdd_toAdd]
    exact hw
  have hfac : t.pointFactor (Subgroup.zpowers (t.e (Multiplicative.ofAdd v))) = 2 := by
    rw [hw']
    have hmap : Subgroup.zpowers (g * t.a1 * g⁻¹) =
        (Subgroup.zpowers t.a1).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (g * t.a1 * g⁻¹) = Subgroup.zpowers ((MulAut.conj g) t.a1)
      rw [MulAut.conj_apply]
    rw [hmap, pointFactor_map_conj t, pointFactor_zpowers_a1 t hN1]
  have hv : ¬ ∃ d : ZMod 3, v = fun _ => d := by
    rintro ⟨d, hd⟩
    have h1 : t.e (Multiplicative.ofAdd v) = 1 := by
      rw [hd]
      exact (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
    rw [hw'] at h1
    have h2 : t.a1 = 1 := by
      calc t.a1 = g⁻¹ * (g * t.a1 * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    exact t.a1_ne_one h2
  obtain ⟨σ, s, d, hs, hvrep⟩ :=
    hasRep_of_pointFactor t hN1 hN3 (i := 0) hv (by simpa [repVal] using hfac)
  obtain ⟨n, hnL, hn⟩ := t.exists_perm σ
  have hzp : Subgroup.zpowers (n * (g * t.a1 * g⁻¹) * n⁻¹) = Subgroup.zpowers t.a1 := by
    rw [← hw', hn (Multiplicative.ofAdd v)]
    simp only [toAdd_ofAdd]
    have hvec : (fun j => v (σ j)) = s • rep 0 + (fun _ : Fin 4 => d) := by
      funext j
      rw [hvrep j, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hsplit : Multiplicative.ofAdd (fun j => v (σ j)) =
        Multiplicative.ofAdd (s • rep 0) * Multiplicative.ofAdd (fun _ : Fin 4 => d) := by
      rw [hvec, ofAdd_add]
    have hconst : t.e (Multiplicative.ofAdd (fun _ : Fin 4 => d)) = 1 :=
      (t.e_eq_one_iff _).mpr ⟨d, rfl⟩
    rw [hsplit, map_mul, hconst, mul_one, zpowers_e_smul t hs]
    rfl
  have hmemN : n * g ∈ Subgroup.normalizer ((Subgroup.zpowers t.a1 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmap : (Subgroup.zpowers t.a1).map (MulAut.conj (n * g)).toMonoidHom =
        Subgroup.zpowers t.a1 := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj (n * g)) t.a1) = Subgroup.zpowers t.a1
      rw [MulAut.conj_apply,
        show (n * g) * t.a1 * (n * g)⁻¹ = n * (g * t.a1 * g⁻¹) * n⁻¹ from by group, hzp]
    simpa using hmap
  have hngM : n * g ∈ c.S.M := hN1 hmemN
  have hnM : n ∈ c.S.M := c.hyp81.1 hnL
  have hg_eq : g = n⁻¹ * (n * g) := by group
  rw [hg_eq]
  exact c.S.M.mul_mem (c.S.M.inv_mem hnM) hngM

end Case811L4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
