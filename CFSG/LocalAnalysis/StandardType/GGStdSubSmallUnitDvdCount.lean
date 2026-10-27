module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdBlock

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

section Count

variable {K : Type} [Field K] [Finite K] {d p : ℕ}

theorem card_le_of_restrict {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) (ν : G →* (Fin d → Kˣ)) (hν : ∀ g k, ν g k ^ p = 1)
    {S T : Finset (Fin d)} (hT : T ⊆ S) (hT1 : ∀ g, ∀ k ∈ T, ν g k = 1) (N : Subgroup G)
    (hN : ∀ g, (∀ k ∈ S, ν g k = 1) → g ∈ N) :
    Nat.card G ≤ Nat.card N * p ^ (S.card - T.card) := by
  classical
  let ρ : G →* (S → Kˣ) :=
    { toFun := fun g k => ν g k
      map_one' := by
        funext k
        simp
      map_mul' := by
        intro g g'
        funext k
        simp }
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have hker : Nat.card ρ.ker ≤ Nat.card N := by
    apply Subgroup.card_le_of_le
    intro g hg
    apply hN g
    intro k hk
    exact congrFun (MonoidHom.mem_ker.mp hg) ⟨k, hk⟩
  have hr : ∀ r : ρ.range, ∀ k : S, (r.1 k) ^ p = 1 := by
    intro r k
    obtain ⟨g, hg⟩ := r.2
    rw [← hg]
    exact hν g k
  have hr1 : ∀ r : ρ.range, ∀ k : S, (k : Fin d) ∈ T → r.1 k = 1 := by
    intro r k hk
    obtain ⟨g, hg⟩ := r.2
    rw [← hg]
    exact hT1 g k hk
  let f : ρ.range → ((S \ T : Finset (Fin d)) → rootsOfUnity p K) := fun r k =>
    ⟨r.1 ⟨k, (Finset.mem_sdiff.mp k.2).1⟩, (mem_rootsOfUnity _ _).mpr
      (hr r ⟨k, (Finset.mem_sdiff.mp k.2).1⟩)⟩
  have hf : Function.Injective f := by
    intro r r' hrr'
    apply Subtype.ext
    funext ⟨k, hk⟩
    by_cases hkT : k ∈ T
    · rw [hr1 r ⟨k, hk⟩ hkT, hr1 r' ⟨k, hk⟩ hkT]
    · have := congrFun hrr' ⟨k, Finset.mem_sdiff.mpr ⟨hk, hkT⟩⟩
      exact congrArg Subtype.val this
  have hrange : Nat.card ρ.range ≤ p ^ (S.card - T.card) := by
    have h2 := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard,
      Finset.card_sdiff_of_subset hT] at h2
  rw [← h1]
  exact Nat.mul_le_mul hker hrange

end Count


section Torus

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem exists_torus (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) {S : Finset (Fin d)} {k₀ : Fin d} (hk₀ : k₀ ∉ S)
    (r : Fin d → Fin d) (hr : ∀ k ∈ S, r k ∈ S) :
    ∃ E : Subgroup L', p ^ ((S.image r).card - 1) ≤ Nat.card E ∧
      ∀ e ∈ E, ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
        (g : GL (Fin d) K) = diagHom d τ ∧ (∀ k, τ k ^ p = 1) ∧ (∀ k, k ∉ S → τ k = 1) ∧
        ∀ i ∈ S, ∀ j ∈ S, r i = r j → τ i = τ j := by
  classical
  have hpK : p ∣ Nat.card K - 1 := dvd_card_sub_one hK hpq
  set C : Finset (Fin d) := S.image r with hC
  let ext₀ : (↥C → rootsOfUnity p K) →* (Fin d → Kˣ) :=
    { toFun := fun x k => if hk : k ∈ S then
        ((x ⟨r k, Finset.mem_image_of_mem r hk⟩ : rootsOfUnity p K) : Kˣ) else 1
      map_one' := by
        funext k
        by_cases hk : k ∈ S <;> simp [hk]
      map_mul' := by
        intro x y
        funext k
        by_cases hk : k ∈ S <;> simp [hk] }
  have hext_pow : ∀ x k, ext₀ x k ^ p = 1 := by
    intro x k
    by_cases hk : k ∈ S
    · have h1 := (x ⟨r k, Finset.mem_image_of_mem r hk⟩).2
      rw [mem_rootsOfUnity] at h1
      simpa [ext₀, hk] using h1
    · simp [ext₀, hk]
  have hext_off : ∀ x k, k ∉ S → ext₀ x k = 1 := by
    intro x k hk
    simp [ext₀, hk]
  have hext_tie : ∀ x, ∀ i ∈ S, ∀ j ∈ S, r i = r j → ext₀ x i = ext₀ x j := by
    intro x i hi j hj hij
    simp only [ext₀, MonoidHom.coe_mk, OneHom.coe_mk, hi, hj, dite_true]
    congr 2
    exact Subtype.ext hij
  have hext_inj : ∀ x, (∀ k, ext₀ x k = 1) → x = 1 := by
    intro x hx
    funext ⟨c, hc⟩
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    have := hx k
    simp only [ext₀, MonoidHom.coe_mk, OneHom.coe_mk, hk, dite_true] at this
    exact Subtype.ext this
  let ϖ : (↥C → rootsOfUnity p K) →* Kˣ :=
    { toFun := fun x => ∏ k, ext₀ x k
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [Finset.prod_mul_distrib] }
  have hϖ : ϖ.range ≤ rootsOfUnity p K := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity]
    show (∏ k, ext₀ x k) ^ p = 1
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun k _ => hext_pow x k
  have hrange : Nat.card ϖ.range ≤ p := by
    have := Subgroup.card_le_of_le hϖ
    rwa [TypeA.card_rootsOfUnity_of_dvd hp hpK] at this
  have hcardH : Nat.card (↥C → rootsOfUnity p K) = p ^ C.card := by
    rw [Nat.card_fun, TypeA.card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_finsetCard]
  have hker : p ^ (C.card - 1) ≤ Nat.card ϖ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range ϖ
    rw [hcardH] at h1
    have h2 : p ^ C.card ≤ Nat.card ϖ.ker * p := h1 ▸ Nat.mul_le_mul_left _ hrange
    rcases Nat.eq_zero_or_pos C.card with h0 | h0
    · rw [h0, pow_zero]
      exact Nat.card_pos
    · rw [show p ^ C.card = p ^ (C.card - 1) * p by
        rw [← pow_succ, Nat.sub_add_cancel h0]] at h2
      exact Nat.le_of_mul_le_mul_right h2 hp.pos
  have hmem : ∀ x : ϖ.ker, diagHom d (ext₀ x) ∈ unitarySU 2 n K d := by
    intro x
    refine diagHom_mem_unitarySU hM.field (fun k => ?_) (MonoidHom.mem_ker.mp x.2)
    obtain ⟨m, hm⟩ := hpq
    rw [hm, pow_mul, hext_pow x k, one_pow]
  let θ : ϖ.ker →* ↥(unitarySU 2 n K d) :=
    ((diagHom d).comp (ext₀.comp ϖ.ker.subtype)).codRestrict (unitarySU 2 n K d) hmem
  have hθ : ∀ x, ((θ x : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = diagHom d (ext₀ x) := fun x => rfl
  have hinj : Function.Injective (φ.comp θ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, hc⟩ := hM.ker (θ x) hx
    rw [hθ, coe_diagHom] at hc
    have hf := Matrix.diagonal_injective hc
    have hk := congrFun hf k₀
    have hc1 : c = 1 := by
      rw [← hk, hext_off x k₀ hk₀]
      rfl
    have hall : ∀ k, ext₀ x k = 1 := fun k => Units.ext (by rw [congrFun hf k, hc1]; rfl)
    exact Subtype.ext (hext_inj x hall)
  refine ⟨(φ.comp θ).range, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hker
  · rintro _ ⟨x, rfl⟩
    exact ⟨θ x, ext₀ x, rfl, hθ x, hext_pow x, hext_off x, hext_tie x⟩

theorem isElemAbelian_torus {E : Subgroup L'}
    (hdesc : ∀ e ∈ E, ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
      (g : GL (Fin d) K) = diagHom d τ ∧ ∀ k, τ k ^ p = 1) :
    CFSG.Open.IsElemAbelian p E := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, τ, hg, hgτ, -⟩ := hdesc x x.2
    obtain ⟨g', τ', hg', hgτ', -⟩ := hdesc y y.2
    apply Subtype.ext
    show (x : L') * y = y * x
    rw [← hg, ← hg', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hgτ, hgτ']
    exact (diagHom_commute τ τ').eq
  · obtain ⟨g, τ, hg, hgτ, hτp⟩ := hdesc x hx
    have h1 : g ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgτ, ← map_pow]
      have : τ ^ p = 1 := funext fun k => by simpa using hτp k
      rw [this, map_one]
      rfl
    rw [← hg, ← map_pow, h1, map_one]

theorem fix_of_torus {E : Subgroup L'} {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    (hdesc : ∀ e ∈ E, ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
      (g : GL (Fin d) K) = diagHom d τ) : ∀ e ∈ E, a e = e := by
  intro e he
  obtain ⟨g, τ, rfl, hgτ⟩ := hdesc e he
  exact ha.actsDiagU.fix_of_diagonal g (v := fun k => ((τ k : Kˣ) : K))
    (by rw [hgτ, coe_diagHom])

end Torus

end CFSG.StandardType.SmallU

end
