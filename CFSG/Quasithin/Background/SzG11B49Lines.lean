module

public import CFSG.Quasithin.Background.SzG11B49Shape

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def B49Ln (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V))
    (U : Submodule (ZMod 2) V) (v z : V) : Set V :=
  {w | (∀ u ∈ U, B w u = B v u) ∧ ∃ t, B49Tv B H U t v z ∧ ∃ x, w = t x + x}

namespace B49Aux

theorem eq_or_eq_add_of_add_eq {p a z : V} (c : ZMod 2) (h : p + a = c • z) :
    p = a ∨ p = a + z := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · left
    rw [zero_smul] at h
    exact (two_add_eq_iff.1 h).trans (zero_add a)
  · right
    rw [one_smul] at h
    rw [two_add_eq_iff.1 h, add_comm]

theorem coeff_eq_zero {z z' : V} (hz : z ≠ 0) (hz' : z' ≠ 0) (hzz : z ≠ z') {a b : ZMod 2}
    (h : a • z + b • z' = 0) : a = 0 ∧ b = 0 := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, zero_add, one_smul] at h
    exact absurd h hz'
  · rw [zero_smul, add_zero, one_smul] at h
    exact absurd h hz
  · rw [one_smul, one_smul] at h
    exact absurd ((two_add_eq_iff.1 h).trans (zero_add z')) hzz

theorem mul_D_eq {t t' : GLV V} (hq : ∀ x, t (t' x + x) = t' x + x) (x : V) :
    (t * t') x + x = (t x + x) + (t' x + x) := by
  have h1 := hq x
  rw [map_add] at h1
  have h2 : t (t' x) = t' x + x + t x := by
    rw [← h1, add_assoc, two_add_self, add_zero]
  change t (t' x) + x = _
  rw [h2]
  abel

end B49Aux

open B49Aux

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {t t' : GLV V} {v v' z z' : V}

include hy

theorem mem_Ln_iff [Finite V] (hz0 : z ≠ 0) (hv : ∃ u ∈ U, B v u ≠ 0)
    (ht : B49Tv B H U t v z) {a : V} (ha : ∀ u ∈ U, B a u = B v u)
    (hsh : ∀ x, t x + x = B a x • z + B z x • a) {w : V} :
    w ∈ B49Ln B H U v z ↔ w = a ∨ w = a + z := by
  have hz : z ∈ U := ht.z_mem
  obtain ⟨u₀, hu₀, hu₀ne⟩ := hv
  have hu₀1 : B v u₀ = 1 := zmod_two_eq_one_of_ne_zero hu₀ne
  obtain ⟨x₁, hx₁⟩ := hy.exists_pair hz0
  have hex : ∀ ε : ZMod 2, ∃ x, t x + x = ε • z + a := by
    intro ε
    have key : ∀ x, B z x = 1 → t x + x = B a x • z + a := fun x hx => by
      rw [hsh x, hx, one_smul]
    by_cases h : B a x₁ = ε
    · exact ⟨x₁, by rw [key x₁ hx₁, h]⟩
    · refine ⟨x₁ + u₀, ?_⟩
      have hz1 : B z (x₁ + u₀) = 1 := by rw [map_add, hx₁, hy.iso z hz u₀ hu₀, add_zero]
      rw [key _ hz1, map_add, ha u₀ hu₀, hu₀1]
      have hs : ∀ s e : ZMod 2, ¬ s = e → s + 1 = e := by decide
      rw [hs _ _ h]
  constructor
  · rintro ⟨hcls, t', ht', x, hw⟩
    have htt : t' = t := hy.tv_eq ht' ht fun u hu => rfl
    subst htt
    have hw' : w = B a x • z + B z x • a := by rw [hw, hsh x]
    rcases zmod_two_eq_zero_or_one (B z x) with h0 | h1
    · exfalso
      have hwU : w ∈ U := by
        rw [hw', h0, zero_smul, add_zero]
        exact U.smul_mem _ hz
      apply hu₀ne
      rw [← hcls u₀ hu₀]
      exact hy.iso w hwU u₀ hu₀
    · refine eq_or_eq_add_of_add_eq (B a x) ?_
      rw [hw', h1, one_smul, add_assoc, two_add_self, add_zero]
  · rintro (rfl | rfl)
    · refine ⟨ha, t, ht, ?_⟩
      obtain ⟨x, hx⟩ := hex 0
      exact ⟨x, by rw [hx, zero_smul, zero_add]⟩
    · refine ⟨fun u hu => ?_, t, ht, ?_⟩
      · rw [map_add, LinearMap.add_apply, ha u hu, hy.iso z hz u hu, add_zero]
      · obtain ⟨x, hx⟩ := hex 1
        exact ⟨x, by rw [hx, one_smul, add_comm]⟩

theorem Ln_two [Finite V] (hz0 : z ≠ 0) (hQ : B49Quad B H U z) (hv : ∃ u ∈ U, B v u ≠ 0)
    (hz : z ∈ U) (hvz : B v z = 0) {p w : V} (hp : p ∈ B49Ln B H U v z) :
    w ∈ B49Ln B H U v z ↔ w = p ∨ w = p + z := by
  obtain ⟨t, ht⟩ := hy.exists_isTv hz hvz
  obtain ⟨a, ha, hsa⟩ := hy.tv_shape0 hz0 hQ ht
  rw [hy.mem_Ln_iff hz0 hv ht ha hsa] at hp ⊢
  rcases hp with rfl | rfl
  · exact Iff.rfl
  · constructor
    · rintro (rfl | rfl)
      · right
        rw [add_assoc, two_add_self, add_zero]
      · left
        rfl
    · rintro (rfl | h)
      · right
        rfl
      · left
        rw [h, add_assoc, two_add_self, add_zero]

theorem tv_DD_formula (ht : B49Tv B H U t v z) (ht' : B49Tv B H U t' v z') {a b : V}
    (ha : ∀ u ∈ U, B a u = B v u) (hb : ∀ u ∈ U, B b u = B v u)
    (hsa : ∀ x, t x + x = B a x • z + B z x • a)
    (hsb : ∀ x, t' x + x = B b x • z' + B z' x • b) (x : V) :
    t (t' x + x) + (t' x + x) = (B z' x * B a b) • z := by
  have hz := ht.z_mem
  have hz' := ht'.z_mem
  have hDz' : t z' + z' = 0 := by
    rw [hsa z', ha z' hz', hy.iso z hz z' hz', ht'.vz]
    simp
  have hDb : t b + b = B a b • z := by
    rw [hsa b, hy.symm z b, hb z hz, ht.vz]
    simp
  have e : t (t' x + x) + (t' x + x) = B b x • (t z' + z') + B z' x • (t b + b) := by
    rw [hsb x]
    simp only [map_add, map_smul]
    module
  rw [e, hDz', hDb, smul_zero, zero_add, smul_smul]

theorem exists_concurrent [Finite V] (hQ : ∀ z ∈ U, z ≠ 0 → B49Quad B H U z)
    (hv : ∃ u ∈ U, B v u ≠ 0) (hz : z ∈ U) (hz' : z' ∈ U) (hz0 : z ≠ 0) (hz0' : z' ≠ 0)
    (hzz' : z ≠ z') (hvz : B v z = 0) (hvz' : B v z' = 0) :
    ∃ p, p ∈ B49Ln B H U v z ∧ p ∈ B49Ln B H U v z' ∧ p ∈ B49Ln B H U v (z + z') := by
  obtain ⟨t, ht⟩ := hy.exists_isTv hz hvz
  obtain ⟨t', ht'⟩ := hy.exists_isTv hz' hvz'
  have hzz0 : z + z' ≠ 0 := fun h => hzz' ((two_add_eq_iff.1 h).trans (zero_add z'))
  have hzz : z + z' ∈ U := U.add_mem hz hz'
  have ht'' : B49Tv B H U (t * t') v (z + z') := B49Tv.mul_centre ht ht'
  have ht2 : B49Tv B H U (t' * t) v (z' + z) := B49Tv.mul_centre ht' ht
  have hcomm : t * t' = t' * t := hy.tv_eq ht'' ht2 fun u hu => by rw [add_comm]
  obtain ⟨a, ha, hsa⟩ := hy.tv_shape0 hz0 (hQ z hz hz0) ht
  obtain ⟨b, hb, hsb⟩ := hy.tv_shape0 hz0' (hQ z' hz' hz0') ht'
  obtain ⟨g, hg, hsg⟩ := hy.tv_shape0 hzz0 (hQ _ hzz hzz0) ht''
  have hz'span : z' ∉ Submodule.span (ZMod 2) {z} := by
    rw [mem_span_singleton_iff_two]
    rintro (h | h)
    · exact hz0' h
    · exact hzz' h.symm
  obtain ⟨x₂, hx₂z, hx₂z'⟩ := hy.exists_sep hz'span
  have hab : B a b = 0 := by
    have e1 := hy.tv_DD_formula ht ht' ha hb hsa hsb x₂
    have e2 := hy.tv_DD_formula ht' ht hb ha hsb hsa x₂
    have hc : t (t' x₂ + x₂) + (t' x₂ + x₂) = t' (t x₂ + x₂) + (t x₂ + x₂) := by
      have : t (t' x₂) = t' (t x₂) := congrArg (fun g : GLV V => g x₂) hcomm
      simp only [map_add, this]
      abel
    rw [e1, e2, hx₂z', hx₂z] at hc
    simp only [one_mul, zero_mul, zero_smul] at hc
    exact (smul_eq_zero.1 hc).resolve_right hz0
  have hq : ∀ x, t (t' x + x) = t' x + x := by
    intro x
    have e1 := hy.tv_DD_formula ht ht' ha hb hsa hsb x
    rw [hab, mul_zero, zero_smul] at e1
    exact (two_add_eq_iff.1 e1).trans (zero_add _)
  have heq : ∀ x, B g x • (z + z') + B (z + z') x • g =
      (B a x • z + B z x • a) + (B b x • z' + B z' x • b) := by
    intro x
    rw [← hsg x, mul_D_eq hq x, hsa x, hsb x]
  have E1 : ∀ x, B (g + a) x • z + B (g + b) x • z' + B z x • (g + a) + B z' x • (g + b) = 0 := by
    intro x
    calc B (g + a) x • z + B (g + b) x • z' + B z x • (g + a) + B z' x • (g + b)
        = (B g x • (z + z') + B (z + z') x • g) +
          ((B a x • z + B z x • a) + (B b x • z' + B z' x • b)) := by
          simp only [map_add, LinearMap.add_apply]
          module
      _ = (B g x • (z + z') + B (z + z') x • g) + (B g x • (z + z') + B (z + z') x • g) := by
          rw [← heq x]
      _ = 0 := two_add_self _
  have hxy : ∀ w, B z w = 0 → B z' w = 0 → B (g + a) w = 0 ∧ B (g + b) w = 0 := by
    intro w hw hw'
    have := E1 w
    rw [hw, hw', zero_smul, zero_smul, add_zero, add_zero] at this
    exact coeff_eq_zero hz0 hz0' hzz' this
  have hx₁ : g + a ∈ Submodule.span (ZMod 2) {z, z'} :=
    hy.mem_span_pair_of_orth fun w hw hw' => (hxy w hw hw').1
  have hy₁ : g + b ∈ Submodule.span (ZMod 2) {z, z'} :=
    hy.mem_span_pair_of_orth fun w hw hw' => (hxy w hw hw').2
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hx₁
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.1 hy₁
  have hβ : B (g + a) x₂ = β := by
    rw [← hαβ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hx₂z,
      hx₂z']
    simp
  have hδ : B (g + b) x₂ = δ := by
    rw [← hγδ]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hx₂z,
      hx₂z']
    simp
  have hβγ : β = γ := by
    have E := E1 x₂
    rw [hβ, hδ, hx₂z, hx₂z', zero_smul, one_smul, add_zero, ← hγδ] at E
    have hc : (β + γ) • z + (δ + δ) • z' = 0 := by
      rw [← E]
      module
    rw [zmod_two_add_self, zero_smul, add_zero] at hc
    have h0 : β + γ = 0 := (smul_eq_zero.1 hc).resolve_right hz0
    have hs : ∀ b c : ZMod 2, b + c = 0 → b = c := by decide
    exact hs _ _ h0
  subst hβγ
  refine ⟨g + β • (z + z'), ?_, ?_, ?_⟩
  · refine (hy.mem_Ln_iff hz0 hv ht ha hsa).2 (eq_or_eq_add_of_add_eq (α + β) ?_)
    calc g + β • (z + z') + a = (g + a) + β • (z + z') := by abel
      _ = (α • z + β • z') + β • (z + z') := by rw [hαβ]
      _ = (α + β) • z := by
          match_scalars <;> ring_nf
          reduce_mod_char
  · refine (hy.mem_Ln_iff hz0' hv ht' hb hsb).2 (eq_or_eq_add_of_add_eq (δ + β) ?_)
    calc g + β • (z + z') + b = (g + b) + β • (z + z') := by abel
      _ = (β • z + δ • z') + β • (z + z') := by rw [hγδ]
      _ = (δ + β) • z' := by
          match_scalars <;> ring_nf
          reduce_mod_char
  · refine (hy.mem_Ln_iff hzz0 hv ht'' hg hsg).2 (eq_or_eq_add_of_add_eq β ?_)
    calc g + β • (z + z') + g = β • (z + z') + (g + g) := by abel
      _ = β • (z + z') := by rw [two_add_self, add_zero]

theorem exists_star [Finite V] (hQ : ∀ z ∈ U, z ≠ 0 → B49Quad B H U z) (hv : ∃ u ∈ U, B v u ≠ 0) :
    ∃ p, ∀ z ∈ U, z ≠ 0 → B v z = 0 → p ∈ B49Ln B H U v z := by
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁0, hz₂0, hz₁₂, hvz₁, hvz₂⟩ := hy.exists_two_zeros v
  obtain ⟨p, hp₁, hp₂, hp₃⟩ := hy.exists_concurrent hQ hv hz₁ hz₂ hz₁0 hz₂0 hz₁₂ hvz₁ hvz₂
  refine ⟨p, fun z hz hz0 hvz => ?_⟩
  by_cases h1 : z = z₁
  · rw [h1]
    exact hp₁
  by_cases h2 : z = z₂
  · rw [h2]
    exact hp₂
  by_cases h3 : z = z₁ + z₂
  · rw [h3]
    exact hp₃
  by_contra hpz
  obtain ⟨q₁, hq₁z, hq₁z₁, -⟩ := hy.exists_concurrent hQ hv hz hz₁ hz0 hz₁0 h1 hvz hvz₁
  obtain ⟨q₂, hq₂z, hq₂z₂, -⟩ := hy.exists_concurrent hQ hv hz hz₂ hz0 hz₂0 h2 hvz hvz₂
  have e1 : q₁ = p + z₁ := by
    rcases (hy.Ln_two hz₁0 (hQ z₁ hz₁ hz₁0) hv hz₁ hvz₁ hp₁).1 hq₁z₁ with h | h
    · exact absurd (h ▸ hq₁z) hpz
    · exact h
  have e2 : q₂ = p + z₂ := by
    rcases (hy.Ln_two hz₂0 (hQ z₂ hz₂ hz₂0) hv hz₂ hvz₂ hp₂).1 hq₂z₂ with h | h
    · exact absurd (h ▸ hq₂z) hpz
    · exact h
  rcases (hy.Ln_two hz0 (hQ z hz hz0) hv hz hvz hq₁z).1 hq₂z with h | h
  · rw [e1, e2] at h
    exact hz₁₂ (add_left_cancel h).symm
  · rw [e1, e2] at h
    have h' : z₂ = z₁ + z := add_left_cancel (by rw [h, add_assoc])
    exact h3 (by rw [h', ← add_assoc, two_add_self, zero_add])

end B49Hyp

@[expose] def B49Center (B : LinearMap.BilinForm (ZMod 2) V) (H : Subgroup (GLV V))
    (U : Submodule (ZMod 2) V) (v p : V) : Prop :=
  (∀ u ∈ U, B p u = B v u) ∧ ∀ z ∈ U, z ≠ 0 → B v z = 0 → p ∈ B49Ln B H U v z

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U) {t t' : GLV V} {v v' z z' p p' : V}

include hy

theorem exists_isCenter [Finite V] (hQ : ∀ z ∈ U, z ≠ 0 → B49Quad B H U z) (v : V) :
    ∃ p, B49Center B H U v p := by
  by_cases hv : ∃ u ∈ U, B v u ≠ 0
  · obtain ⟨p, hp⟩ := hy.exists_star hQ hv
    obtain ⟨z₁, hz₁, -, -, hz₁0, -, -, hvz₁, -⟩ := hy.exists_two_zeros v
    exact ⟨p, (hp z₁ hz₁ hz₁0 hvz₁).1, hp⟩
  · push Not at hv
    refine ⟨0, fun u hu => by rw [map_zero, LinearMap.zero_apply, hv u hu],
      fun z hz hz0 hvz => ⟨fun u hu => by rw [map_zero, LinearMap.zero_apply, hv u hu], ?_⟩⟩
    obtain ⟨t, ht⟩ := hy.exists_isTv hz hvz
    exact ⟨t, ht, 0, by rw [map_zero, add_zero]⟩

theorem isCenter_conj (h : B49Center B H U v p) {g : GLV V} (hg : g ∈ H) :
    B49Center B H U (g v) (g p) := by
  have hcls : ∀ u ∈ U, B (g p) u = B (g v) u := fun u hu => by
    rw [hy.B_apply_left hg, hy.B_apply_left hg]
    exact h.1 _ (hy.inv_apply_mem hg hu)
  refine ⟨hcls, fun z hz hz0 hvz => ?_⟩
  have hz' : g⁻¹ z ∈ U := hy.inv_apply_mem hg hz
  have hz'0 : g⁻¹ z ≠ 0 := fun h0 => hz0 (by simpa [apply_inv_apply] using congrArg g h0)
  have hvz' : B v (g⁻¹ z) = 0 := by rw [← hy.B_apply_left hg]; exact hvz
  obtain ⟨-, t, ht, x, hx⟩ := h.2 _ hz' hz'0 hvz'
  refine ⟨hcls, g * t * g⁻¹, ?_, g x, ?_⟩
  · have := hy.tv_conj ht hg
    rwa [apply_inv_apply] at this
  · rw [hx, map_add]
    change g (t x) + g x = g (t (g⁻¹ (g x))) + g x
    rw [inv_apply_apply]

theorem isCenter_orth [Finite V] (hQ : ∀ z ∈ U, z ≠ 0 → B49Quad B H U z)
    (h : B49Center B H U v p) (h' : B49Center B H U v' p') : B p p' = 0 := by
  obtain ⟨z, hz, hz0, hvz, hv'z⟩ := hy.exists_common_zero v v'
  obtain ⟨-, t, ht, x, hx⟩ := h.2 z hz hz0 hvz
  obtain ⟨-, t', ht', x', hx'⟩ := h'.2 z hz hz0 hv'z
  have hq := hQ z hz hz0 v v' t t' ht ht' x'
  have hp' : t p' + p' = 0 := by
    rw [hx', hq, two_add_self]
  rw [hx, hy.tv_selfadj ht x p', hp', map_zero]

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
