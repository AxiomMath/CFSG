module

public import CFSG.Quasithin.Background.G117CanonDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Canon

open CFSG.Quasithin CFSG.Quasithin.G11
open scoped TensorProduct

private theorem add_self_eq_zero' {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (v : V) :
    v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 by decide, zero_smul]

private theorem finrank_permCore_six : Module.finrank (ZMod 2) ↥(permCore 6) = 5 := by
  let s : (Fin 6 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := ∑ i : Fin 6, LinearMap.proj i
  have hs : ∀ x, s x = ∑ i, x i := fun x => by simp [s]
  have hker : permCore 6 = LinearMap.ker s := by
    ext x
    rw [LinearMap.mem_ker, hs]
    exact Iff.rfl
  have hsurj : Function.Surjective s := fun c => ⟨Pi.single 0 c, by rw [hs]; simp⟩
  have h := LinearMap.finrank_range_add_finrank_ker s
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  rw [hker]
  omega

private theorem finrank_range_eq_four {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (β : ↥(permCore 6) →ₗ[ZMod 2] V)
    (hker : ∀ u : ↥(permCore 6), β u = 0 ↔ (u = 0 ∨ u = onesCore6)) :
    Module.finrank (ZMod 2) (LinearMap.range β) = 4 := by
  have hK : LinearMap.ker β = Submodule.span (ZMod 2) {onesCore6} := by
    ext z
    rw [LinearMap.mem_ker, hker, Submodule.mem_span_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, zero_smul _ _⟩
      · exact ⟨1, one_smul _ _⟩
    · rintro ⟨a, rfl⟩
      rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
      · exact Or.inl (zero_smul _ _)
      · exact Or.inr (one_smul _ _)
  have hne : onesCore6 ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : ↥(permCore 6) => (z : Fin 6 → ZMod 2) 0) h
    simp [onesCore6] at h0
  have h := LinearMap.finrank_range_add_finrank_ker β
  rw [hK, finrank_span_singleton hne, finrank_permCore_six] at h
  omega

private theorem sq_eq_add_of_cube {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (c : GLV V)
    (h3 : c ^ 3 = 1) (hfix : ∀ v : V, c v = v → v = 0) (v : V) : c (c v) = c v + v := by
  have hc3 : c (c (c v)) = v := by
    rw [pow_three] at h3
    have h := congrArg (fun g : GLV V => g v) h3
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h
  have h0 : c (c v) + c v + v = 0 := hfix _ (by rw [map_add, map_add, hc3]; abel)
  calc c (c v) = c (c v) + c v + v + (c v + v) := by
        rw [add_assoc (c (c v)) (c v) v, add_assoc, add_self_eq_zero', add_zero]
    _ = c v + v := by rw [h0, zero_add]

private theorem gf4_mul_self {ω : GaloisField 2 2} (h1 : ω ≠ 1) (h3 : ω ^ 3 = 1) :
    ω * ω = 1 + ω := by
  have h2 : (2 : GaloisField 2 2) = 0 := CharTwo.two_eq_zero
  have key : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · linear_combination h - (1 + ω) * h2

private theorem gf4_coords {ω : GaloisField 2 2} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ∃ f₀ f₁ : GaloisField 2 2 →ₗ[ZMod 2] ZMod 2,
      (∀ b, f₀ b • (1 : GaloisField 2 2) + f₁ b • ω = b) ∧
        f₀ 1 = 1 ∧ f₁ 1 = 0 ∧ f₀ ω = 0 ∧ f₁ ω = 1 := by
  have hlin : LinearIndependent (ZMod 2) ![(1 : GaloisField 2 2), ω] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
    · rw [zero_smul]
      exact h0.symm
    · rw [one_smul]
      exact h1.symm
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) (GaloisField 2 2) := by
    rw [Fintype.card_fin, GaloisField.finrank 2 two_ne_zero]
  let B := basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = ω := by simp [B]
  refine ⟨B.coord 0, B.coord 1, fun b => ?_, ?_, ?_, ?_, ?_⟩
  · have h := B.sum_repr b
    simp only [Fin.sum_univ_two, hB0, hB1] at h
    simpa only [Module.Basis.coord_apply] using h
  · rw [← hB0, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    decide
  · rw [← hB0, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    decide
  · rw [← hB1, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    decide
  · rw [← hB1, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    decide

private theorem gf4_ext {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {ω : GaloisField 2 2}
    {f₀ f₁ : GaloisField 2 2 →ₗ[ZMod 2] ZMod 2}
    (hdec : ∀ b, f₀ b • (1 : GaloisField 2 2) + f₁ b • ω = b)
    {L₁ L₂ : GaloisField 2 2 →ₗ[ZMod 2] W} (h1 : L₁ 1 = L₂ 1) (hω : L₁ ω = L₂ ω)
    (b : GaloisField 2 2) : L₁ b = L₂ b := by
  rw [← hdec b, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hω]

private theorem exists_tensor_map {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (β : ↥(permCore 6) →ₗ[ZMod 2] V) (c : GLV V) (f₀ f₁ : GaloisField 2 2 →ₗ[ZMod 2] ZMod 2) :
    ∃ β' : (↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2) →ₗ[ZMod 2] V,
      ∀ a b, β' (a ⊗ₜ b) = f₀ b • β a + f₁ b • c (β a) := by
  refine ⟨TensorProduct.lift (LinearMap.mk₂ (ZMod 2)
    (fun (a : ↥(permCore 6)) (b : GaloisField 2 2) => f₀ b • β a + f₁ b • c (β a))
    ?_ ?_ ?_ ?_), fun a b => ?_⟩
  · intro a a' b
    rw [map_add, map_add, smul_add, smul_add]
    abel
  · intro r a b
    rw [map_smul, map_smul, smul_add, smul_comm r (f₀ b), smul_comm r (f₁ b)]
  · intro a b b'
    rw [map_add, map_add, add_smul, add_smul]
    abel
  · intro r a b
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul, smul_add]
  · rw [TensorProduct.lift.tmul]
    rfl

private theorem inf_eq_bot_sup_eq_top {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (E : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (c : GLV V)
    (hdim : Module.finrank (ZMod 2) V = 8) (hI : Module.finrank (ZMod 2) I = 4)
    (hirr : IsIrr E I) (hcomm : ∀ e ∈ E, e * c = c * e) (hmove : conjSub c I ≠ I) :
    I ⊓ conjSub c I = ⊥ ∧ I ⊔ conjSub c I = ⊤ := by
  obtain ⟨hinvI, -, hmax⟩ := hirr
  have hcI : Module.finrank (ZMod 2) (conjSub c I) = 4 := by
    change Module.finrank (ZMod 2) ↥(I.map (c : V →ₗ[ZMod 2] V)) = 4
    rw [LinearEquiv.finrank_map_eq, hI]
  have hinv : Invariant E (I ⊓ conjSub c I) := by
    intro e he v hv
    obtain ⟨hvI, hvc⟩ := Submodule.mem_inf.mp hv
    refine Submodule.mem_inf.mpr ⟨hinvI e he v hvI, ?_⟩
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hvc
    refine Submodule.mem_map.mpr ⟨e u, hinvI e he u hu, ?_⟩
    have h := congrArg (fun g : GLV V => g u) (hcomm e he)
    simp only [LinearEquiv.mul_apply] at h
    simp only [LinearEquiv.coe_coe]
    exact h.symm
  have hbot : I ⊓ conjSub c I = ⊥ := by
    rcases hmax _ hinv bot_le inf_le_left with h | h
    · exact h
    · exact absurd (Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp h) (by rw [hI, hcI])).symm
        hmove
  refine ⟨hbot, Submodule.eq_top_of_finrank_eq ?_⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq I (conjSub c I)
  rw [hbot, finrank_bot, hI, hcI] at h
  rw [hdim]
  omega

theorem tensorA6Z3WithMarking_of_homogeneous
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (E P : Subgroup (GLV V)) (φ : ↥E ≃* ↥(alternatingGroup (Fin 6)))
    (I : Submodule (ZMod 2) V) (β : ↥(permCore 6) →ₗ[ZMod 2] V)
    (hdim : Module.finrank (ZMod 2) V = 8)
    (hrange : LinearMap.range β = I)
    (hker : ∀ u : ↥(permCore 6), β u = 0 ↔ (u = 0 ∨ u = onesCore6))
    (hequ : ∀ (e : ↥E) (u u' : ↥(permCore 6)),
      (u' : Fin 6 → ZMod 2) = permAct ((φ e : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
        (u : Fin 6 → ZMod 2) → β u' = (e : GLV V) (β u))
    (hirr : IsIrr E I)
    (hPcard : Nat.card ↥P = 3) (hcomm : ∀ e ∈ E, ∀ p ∈ P, e * p = p * e)
    (hfix : ∀ p ∈ P, p ≠ 1 → ∀ v : V, p v = v → v = 0)
    (hmove : ∀ p ∈ P, p ≠ 1 → conjSub p I ≠ I) :
    TensorA6Z3WithMarking E P φ := by
  subst hrange
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU : Nat.card (GaloisField 2 2)ˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 two_ne_zero]
    norm_num
  let θ : ↥P ≃* (GaloisField 2 2)ˣ := mulEquivOfPrimeCardEq hPcard hU
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
  haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hPcard]; norm_num)
  obtain ⟨p₀, hp₀⟩ := exists_ne (1 : ↥P)
  have hp₀3 : p₀ ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := p₀)
    rwa [hPcard] at h
  obtain ⟨c, hc⟩ : ∃ c : GLV V, c = (p₀ : GLV V) := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : GaloisField 2 2, ω = ((θ p₀ : (GaloisField 2 2)ˣ) : GaloisField 2 2) :=
    ⟨_, rfl⟩
  have hcP : c ∈ P := hc ▸ p₀.2
  have hc1 : c ≠ 1 := by
    rw [hc]
    exact fun h => hp₀ (Subtype.ext h)
  have hc3 : c ^ 3 = 1 := by
    rw [hc, ← SubgroupClass.coe_pow, hp₀3, OneMemClass.coe_one]
  have hω0 : ω ≠ 0 := hω ▸ Units.ne_zero _
  have hω1 : ω ≠ 1 := by
    rw [hω, Ne, Units.val_eq_one, EmbeddingLike.map_eq_one_iff]
    exact hp₀
  have hω3 : ω ^ 3 = 1 := by
    rw [hω, ← Units.val_pow_eq_pow_val, ← map_pow, hp₀3, map_one, Units.val_one]
  have hcc := sq_eq_add_of_cube c hc3 (hfix c hcP hc1)
  have hωω := gf4_mul_self hω1 hω3
  obtain ⟨f₀, f₁, hdec, h01, h11, h0ω, h1ω⟩ := gf4_coords hω0 hω1
  obtain ⟨hdisj, hsup⟩ := inf_eq_bot_sup_eq_top E (LinearMap.range β) c hdim
    (finrank_range_eq_four β hker) hirr (fun e he => hcomm e he c hcP) (hmove c hcP hc1)
  have hEc : ∀ e ∈ E, ∀ v : V, c (e v) = e (c v) := by
    intro e he v
    have h := congrArg (fun g : GLV V => g v) (hcomm e he c hcP)
    simp only [LinearEquiv.mul_apply] at h
    exact h.symm
  obtain ⟨β', hβ'⟩ := exists_tensor_map β c f₀ f₁
  have hβ'1 : ∀ a, β' (a ⊗ₜ (1 : GaloisField 2 2)) = β a := fun a => by
    rw [hβ', h01, h11, one_smul, zero_smul, add_zero]
  have hβ'ω : ∀ a, β' (a ⊗ₜ ω) = c (β a) := fun a => by
    rw [hβ', h0ω, h1ω, one_smul, zero_smul, zero_add]
  have hdecomp : ∀ t : ↥(permCore 6) ⊗[ZMod 2] GaloisField 2 2,
      ∃ a₁ a₂ : ↥(permCore 6), t = a₁ ⊗ₜ 1 + a₂ ⊗ₜ ω := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      refine ⟨f₀ b • a, f₁ b • a, ?_⟩
      conv_lhs => rw [← hdec b]
      rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨a₁, a₂, rfl⟩ := hx
      obtain ⟨a₁', a₂', rfl⟩ := hy
      exact ⟨a₁ + a₁', a₂ + a₂', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul]; abel⟩
  have hωact : ∀ a b, β' (a ⊗ₜ (ω * b)) = c (β' (a ⊗ₜ b)) := by
    intro a b
    refine gf4_ext hdec
      (L₁ := β' ∘ₗ TensorProduct.mk (ZMod 2) ↥(permCore 6) (GaloisField 2 2) a ∘ₗ
        LinearMap.mulLeft (ZMod 2) ω)
      (L₂ := (c : V →ₗ[ZMod 2] V) ∘ₗ β' ∘ₗ
        TensorProduct.mk (ZMod 2) ↥(permCore 6) (GaloisField 2 2) a) ?_ ?_ b
    · change β' (a ⊗ₜ (ω * 1)) = c (β' (a ⊗ₜ 1))
      rw [mul_one, hβ'1, hβ'ω]
    · change β' (a ⊗ₜ (ω * ω)) = c (β' (a ⊗ₜ ω))
      rw [hωω, TensorProduct.tmul_add, map_add, hβ'1, hβ'ω, hcc, add_comm]
  have hpow : ∀ (n : ℕ) (a : ↥(permCore 6)) (b : GaloisField 2 2),
      β' (a ⊗ₜ (ω ^ n * b)) = (c ^ n) (β' (a ⊗ₜ b)) := by
    intro n
    induction n with
    | zero =>
      intro a b
      rw [pow_zero, one_mul, pow_zero, LinearEquiv.coe_one, id_eq]
    | succ n ih =>
      intro a b
      rw [pow_succ' ω, mul_assoc, hωact, ih, pow_succ' c, LinearEquiv.mul_apply]
  unfold TensorA6Z3WithMarking
  refine ⟨θ, β', ?_, ?_, ?_, ?_⟩
  ·
    intro v
    have hv : v ∈ LinearMap.range β ⊔ conjSub c (LinearMap.range β) := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a₁, rfl⟩ := LinearMap.mem_range.mp hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨a₂, rfl⟩ := LinearMap.mem_range.mp hw
    exact ⟨a₁ ⊗ₜ 1 + a₂ ⊗ₜ ω, by rw [map_add, hβ'1, hβ'ω]; rfl⟩
  ·
    intro t
    constructor
    · intro ht
      obtain ⟨a₁, a₂, rfl⟩ := hdecomp t
      rw [map_add, hβ'1, hβ'ω] at ht
      have h1 : β a₁ = c (β a₂) :=
        (eq_neg_of_add_eq_zero_left ht).trans (neg_eq_of_add_eq_zero_right (add_self_eq_zero' _))
      have hmem : β a₁ ∈ LinearMap.range β ⊓ conjSub c (LinearMap.range β) := by
        refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self β a₁, ?_⟩
        rw [h1]
        exact Submodule.mem_map_of_mem (LinearMap.mem_range_self β a₂)
      rw [hdisj, Submodule.mem_bot] at hmem
      have h2 : β a₂ = 0 := by
        rw [hmem] at h1
        exact (LinearEquiv.map_eq_zero_iff c).mp h1.symm
      rcases (hker a₁).mp hmem with rfl | rfl <;> rcases (hker a₂).mp h2 with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨ω, by rw [TensorProduct.zero_tmul, zero_add]⟩
      · exact ⟨1, by rw [TensorProduct.zero_tmul, add_zero]⟩
      · exact ⟨1 + ω, (TensorProduct.tmul_add _ _ _).symm⟩
    · rintro ⟨b, rfl⟩
      rw [hβ', (hker onesCore6).mpr (Or.inr rfl), map_zero, smul_zero, smul_zero, add_zero]
  ·
    intro e a a' b hexp
    rw [hβ', hβ', hequ e a a' hexp, map_add, map_smul, map_smul, hEc e e.2]
  ·
    intro p a b
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff p p₀).mp (mem_powers_of_prime_card hPcard hp₀)
    rw [map_pow, Units.val_pow_eq_pow_val, SubgroupClass.coe_pow, ← hω, ← hc]
    exact hpow n a b

end CFSG.Quasithin.G11.Canon
