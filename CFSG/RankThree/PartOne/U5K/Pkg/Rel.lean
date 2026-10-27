module

public import CFSG.RankThree.PartOne.U5K.Pkg.Orbit
public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.WeylIso
import CFSG.RankThree.PartOne.S12.TerminalWeylPerm

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E} (M : Model p E c)

noncomputable def u (f : Multiplicative (Fin 4 → ZMod p) ≃* E) (i : Fin 5) : Fin 4 → ZMod p :=
  Multiplicative.toAdd (f.symm (M.v i))

noncomputable def Φ (f : Multiplicative (Fin 4 → ZMod p) ≃* E) :
    (Fin 5 → ZMod p) →ₗ[ZMod p] (Fin 4 → ZMod p) :=
  Fintype.linearCombination (ZMod p) (M.u f)

variable (f : Multiplicative (Fin 4 → ZMod p) ≃* E)

theorem f_ofAdd_u (i : Fin 5) : f (Multiplicative.ofAdd (M.u f i)) = M.v i := by
  unfold u
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem coordLin_u [Fact p.Prime] (x : MulAut E) (hx : x ∈ reflectionGroup p E) (i : Fin 5) :
    LinAlg.coordLin f x (M.u f i) = M.u f (M.ψ ⟨x, hx⟩ i) := by
  apply Multiplicative.ofAdd.injective
  apply f.injective
  rw [LinAlg.apply_coordLin, M.f_ofAdd_u f i, M.f_ofAdd_u f]
  exact M.equivariant ⟨x, hx⟩ i

theorem sum_u_eq_zero : ∑ i, M.u f i = 0 := by
  have : Fact p.Prime := ⟨M.prime⟩
  set s : Fin 4 → ZMod p := ∑ i, M.u f i with hs
  have h1 : f (Multiplicative.ofAdd s) = 1 := by
    apply M.key
    intro x hx
    rw [← LinAlg.apply_coordLin f x s]
    have h2 : LinAlg.coordLin f x s = s := by
      rw [hs, map_sum]
      simp_rw [M.coordLin_u f x hx]
      exact Equiv.sum_comp (M.ψ ⟨x, hx⟩) (M.u f)
    rw [h2]
  have h3 : Multiplicative.ofAdd s = 1 := f.injective (by rw [h1, map_one])
  exact (toAdd_eq_zero.2 h3 : Multiplicative.toAdd (Multiplicative.ofAdd s) = 0)

theorem range_Φ : LinearMap.range (M.Φ f) = ⊤ := by
  have : Fact p.Prime := ⟨M.prime⟩
  rw [Φ, Fintype.range_linearCombination]
  have key : ∀ x ∈ Subgroup.closure (Set.range M.v),
      Multiplicative.toAdd (f.symm x) ∈ Submodule.span (ZMod p) (Set.range (M.u f)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | one => simp
    | mul y z _ _ hy hz =>
      rw [map_mul, toAdd_mul]; exact Submodule.add_mem _ hy hz
    | inv y _ hy =>
      rw [map_inv, toAdd_inv]; exact Submodule.neg_mem _ hy
  rw [eq_top_iff]
  intro w _
  have := key (f (Multiplicative.ofAdd w)) (by rw [M.span_eq_top]; trivial)
  rwa [MulEquiv.symm_apply_apply, toAdd_ofAdd] at this

theorem ker_Φ : LinearMap.ker (M.Φ f) =
    Submodule.span (ZMod p) {fun _ : Fin 5 => (1 : ZMod p)} := by
  have : Fact p.Prime := ⟨M.prime⟩
  have hj : (fun _ : Fin 5 => (1 : ZMod p)) ∈ LinearMap.ker (M.Φ f) := by
    rw [LinearMap.mem_ker]
    simp [Φ, Fintype.linearCombination_apply, M.sum_u_eq_zero f]
  have hle : Submodule.span (ZMod p) {fun _ : Fin 5 => (1 : ZMod p)} ≤
      LinearMap.ker (M.Φ f) := (Submodule.span_singleton_le_iff_mem _ _).2 hj
  have hfin : Module.finrank (ZMod p) (LinearMap.ker (M.Φ f)) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (M.Φ f)
    have h2 : Module.finrank (ZMod p) (LinearMap.range (M.Φ f)) = 4 := by
      rw [M.range_Φ f]
      exact (finrank_top (ZMod p) (Fin 4 → ZMod p)).trans (Module.finrank_fin_fun _)
    have h3 : Module.finrank (ZMod p) (Fin 5 → ZMod p) = 5 := Module.finrank_fin_fun _
    have h4 : Module.finrank (ZMod p) (LinearMap.range (M.Φ f)) +
        Module.finrank (ZMod p) (LinearMap.ker (M.Φ f)) =
        Module.finrank (ZMod p) (Fin 5 → ZMod p) := h1
    omega
  have hj0 : (fun _ : Fin 5 => (1 : ZMod p)) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  have h5 : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) {fun _ : Fin 5 => (1 : ZMod p)}) = 1 := finrank_span_singleton hj0
  exact (Submodule.eq_of_le_of_finrank_eq hle (h5.trans hfin.symm)).symm

theorem toAdd_prod (a : Fin 5 → ℤ) :
    Multiplicative.toAdd (f.symm (M.v 0 ^ a 0 * M.v 1 ^ a 1 * M.v 2 ^ a 2 * M.v 3 ^ a 3 *
      M.v 4 ^ a 4)) = M.Φ f (fun i => (a i : ZMod p)) := by
  simp only [Φ, Fintype.linearCombination_apply, Fin.sum_univ_five, map_mul, map_zpow, toAdd_mul,
    toAdd_zpow, Int.cast_smul_eq_zsmul]
  rfl

theorem exists_prod (x : E) :
    ∃ a : Fin 5 → ℤ, x = M.v 0 ^ a 0 * M.v 1 ^ a 1 * M.v 2 ^ a 2 * M.v 3 ^ a 3 * M.v 4 ^ a 4 := by
  have : Fact p.Prime := ⟨M.prime⟩
  have := M.elem
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E M.card
  have hx : Multiplicative.toAdd (f.symm x) ∈ LinearMap.range (M.Φ f) := by
    rw [M.range_Φ f]; trivial
  obtain ⟨cc, hcc⟩ := hx
  refine ⟨fun i => ((cc i).val : ℤ), ?_⟩
  beta_reduce
  apply f.symm.injective
  apply Multiplicative.toAdd.injective
  have h := M.toAdd_prod f (fun i => ((cc i).val : ℤ))
  beta_reduce at h
  rw [h, ← hcc]
  congr 1
  funext i
  simp

theorem prod_eq_one_iff (a : Fin 5 → ℤ) :
    M.v 0 ^ a 0 * M.v 1 ^ a 1 * M.v 2 ^ a 2 * M.v 3 ^ a 3 * M.v 4 ^ a 4 = 1 ↔
      ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m := by
  have : Fact p.Prime := ⟨M.prime⟩
  have := M.elem
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E M.card
  have h1 : M.v 0 ^ a 0 * M.v 1 ^ a 1 * M.v 2 ^ a 2 * M.v 3 ^ a 3 * M.v 4 ^ a 4 = 1 ↔
      M.Φ f (fun i => (a i : ZMod p)) = 0 := by
    rw [← M.toAdd_prod f, toAdd_eq_zero, MulEquiv.map_eq_one_iff]
  rw [h1, ← LinearMap.mem_ker, M.ker_Φ f, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨(s.val : ℤ), fun i => ?_⟩
    have := congrFun hs i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at this
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp [this]
  · rintro ⟨m, hm⟩
    refine ⟨(m : ZMod p), funext fun i => ?_⟩
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub m (a i) p).2 (hm i)
    simp [this]

theorem swap_of_mem {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    ∃ a b : Fin 5, a ≠ b ∧ M.ψ ⟨t, Subgroup.subset_closure ht⟩ = Equiv.swap a b := by
  have : Fact p.Prime := ⟨M.prime⟩
  have := M.elem
  obtain ⟨f⟩ := LinAlg.exists_coords (p := p) E M.card
  have hX : t ∈ reflectionGroup p E := Subgroup.subset_closure ht
  set σ := M.ψ ⟨t, hX⟩ with hσ
  have hrefl : IsAutReflection p E t := ht.1
  have htt : t * t = 1 := RefFacts.mul_self_eq_one hrefl
  have hσσ : σ * σ = 1 := by
    have : (⟨t, hX⟩ : ↥(reflectionGroup p E)) * ⟨t, hX⟩ = 1 := Subtype.ext htt
    rw [hσ, ← map_mul, this, map_one]
  have hσne : σ ≠ 1 := by
    intro h1
    have h2 : (⟨t, hX⟩ : ↥(reflectionGroup p E)) = 1 := (M.ψ.map_eq_one_iff).1 h1
    have h3 : t = 1 := congrArg Subtype.val h2
    have := hrefl.1
    rw [h3, orderOf_one] at this
    omega
  have hσinv : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : Equiv.Perm (Fin 5) => τ x) hσσ
    simpa [Equiv.Perm.mul_apply] using this
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hσne (Equiv.ext hcon)
  set b := σ a with hb
  have hab : a ≠ b := fun h => ha h.symm
  have hσb : σ b = a := hσinv a
  have key : ∀ x, x ≠ a → x ≠ b → σ x = x := by
    intro x hxa hxb
    by_contra hxne
    set y := σ x with hy
    have hya : y ≠ a := fun h => hxb (by rw [← hσinv x, ← hy, h])
    have hyb : y ≠ b := fun h => hxa (by rw [← hσinv x, ← hy, h, hσb])
    obtain ⟨e, hea, heb, hex, hey⟩ := WeylIso.exists_fin_ne (n := 4) (by norm_num) a b x y
    have hrank : Module.finrank (ZMod p) (LinearMap.range (LinAlg.coordSub f t)) = 1 :=
      ((LinAlg.isAutReflection_iff f t).1 hrefl).2
    have hNa : LinAlg.coordSub f t (M.u f a) = M.u f b - M.u f a := by
      rw [LinAlg.coordSub_apply, M.coordLin_u f t hX a]
    have hNx : LinAlg.coordSub f t (M.u f x) = M.u f y - M.u f x := by
      rw [LinAlg.coordSub_apply, M.coordLin_u f t hX x]
    obtain ⟨g, hg0, hg⟩ := finrank_eq_one_iff'.1 hrank
    obtain ⟨c₁, hc₁⟩ := hg ⟨LinAlg.coordSub f t (M.u f a), LinearMap.mem_range_self _ _⟩
    obtain ⟨c₂, hc₂⟩ := hg ⟨LinAlg.coordSub f t (M.u f x), LinearMap.mem_range_self _ _⟩
    obtain ⟨α, β, hαβ, hrel⟩ : ∃ α β : ZMod p, (α ≠ 0 ∨ β ≠ 0) ∧
        α • (M.u f b - M.u f a) + β • (M.u f y - M.u f x) = 0 := by
      by_cases h0 : c₁ = 0 ∧ c₂ = 0
      · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
        have h1 : LinAlg.coordSub f t (M.u f a) = 0 := by
          have := congrArg Subtype.val hc₁
          rw [h0.1, zero_smul] at this
          exact this.symm
        rw [hNa] at h1
        simp [h1]
      · refine ⟨c₂, -c₁, ?_, ?_⟩
        · by_contra hcon
          push Not at hcon
          exact h0 ⟨neg_eq_zero.1 hcon.2, hcon.1⟩
        · have e1 : c₁ • (g : Fin 4 → ZMod p) = M.u f b - M.u f a := by
            have := congrArg Subtype.val hc₁
            simpa [hNa] using this
          have e2 : c₂ • (g : Fin 4 → ZMod p) = M.u f y - M.u f x := by
            have := congrArg Subtype.val hc₂
            simpa [hNx] using this
          rw [← e1, ← e2, smul_smul, smul_smul, ← add_smul]
          have : c₂ * c₁ + -c₁ * c₂ = 0 := by ring
          rw [this, zero_smul]
    classical
    set n : Fin 5 → ZMod p := Pi.single a (-α) + Pi.single b α + Pi.single x (-β) +
      Pi.single y β with hn
    have hΦn : M.Φ f n = 0 := by
      simp only [hn, map_add, Φ, Fintype.linearCombination_apply_single]
      rw [← hrel]
      simp only [smul_sub, neg_smul]
      abel
    have hmem : n ∈ Submodule.span (ZMod p) {fun _ : Fin 5 => (1 : ZMod p)} := by
      rw [← M.ker_Φ f]; exact hΦn
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
    have hne : ∀ i, n i = s := fun i => by
      have := congrFun hs i
      simpa using this.symm
    have hne_e : n e = 0 := by
      simp [hn, hea, heb, hex, hey]
    have hne_b : n b = α := by
      simp [hn, Ne.symm hab, hxb, hyb]
    have hne_y : n y = β := by
      simp [hn, hya, hyb, hxne]
    have hs0 : s = 0 := by rw [← hne e, hne_e]
    have hα : α = 0 := by rw [← hne_b, hne b, hs0]
    have hβ : β = 0 := by rw [← hne_y, hne y, hs0]
    rcases hαβ with h | h
    · exact h hα
    · exact h hβ
  refine ⟨a, b, hab, Equiv.ext fun x => ?_⟩
  by_cases hxa : x = a
  · rw [hxa, Equiv.swap_apply_left]
  · by_cases hxb : x = b
    · rw [hxb, Equiv.swap_apply_right, hσb]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb, key x hxa hxb]

theorem surj_swap {σ : Equiv.Perm (Fin 5)} (hσ : σ.IsSwap) :
    ∃ (t : MulAut E) (ht : t ∈ reflectionSet p E),
      M.ψ ⟨t, Subgroup.subset_closure ht⟩ = σ := by
  obtain ⟨t₀, ht₀⟩ := M.D_ne
  obtain ⟨g, hg⟩ := TerminalPerm.swap_conj_swap (M.ψ ⟨t₀, Subgroup.subset_closure ht₀⟩) σ
    (M.swap_of_mem ht₀) hσ
  set g' : ↥(reflectionGroup p E) := M.ψ.symm g with hg'
  have hg'W : (g' : MulAut E) ∈ torusWeyl E := WeylIso.closure_le_weyl g'.2
  have ht : (g' : MulAut E) * t₀ * (g' : MulAut E)⁻¹ ∈ reflectionSet p E :=
    WeylIso.conj_mem_reflectionSet_of_weyl M.prime hg'W ht₀
  refine ⟨_, ht, ?_⟩
  have h1 : (⟨(g' : MulAut E) * t₀ * (g' : MulAut E)⁻¹, Subgroup.subset_closure ht⟩ :
      ↥(reflectionGroup p E)) = g' * ⟨t₀, Subgroup.subset_closure ht₀⟩ * g'⁻¹ := rfl
  have h2 : M.ψ (g' * ⟨t₀, Subgroup.subset_closure ht₀⟩ * g'⁻¹) = σ := by
    rw [map_mul, map_mul, map_inv, hg', MulEquiv.apply_symm_apply, hg]
  exact (congrArg M.ψ h1).trans h2

end Model

theorem exists_rel_of_finrank_one {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod q) V] (R : Submodule (ZMod q) V) (hR : Module.finrank (ZMod q) R = 1)
    {x y : V} (hx : x ∈ R) (hy : y ∈ R) :
    ∃ α β : ZMod q, (α ≠ 0 ∨ β ≠ 0) ∧ α • x + β • y = 0 := by
  obtain ⟨g, hg0, hg⟩ := finrank_eq_one_iff'.1 hR
  obtain ⟨c₁, hc₁⟩ := hg ⟨x, hx⟩
  obtain ⟨c₂, hc₂⟩ := hg ⟨y, hy⟩
  have e1 : c₁ • (g : V) = x := congrArg Subtype.val hc₁
  have e2 : c₂ • (g : V) = y := congrArg Subtype.val hc₂
  by_cases h0 : c₁ = 0 ∧ c₂ = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [← e1, h0.1]
    simp
  · refine ⟨c₂, -c₁, ?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      exact h0 ⟨neg_eq_zero.1 hcon.2, hcon.1⟩
    · rw [← e1, ← e2, smul_smul, smul_smul, ← add_smul]
      have : c₂ * c₁ + -c₁ * c₂ = 0 := by ring
      rw [this, zero_smul]

namespace Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} {E : Subgroup G} {c : E} (M : Model p E c)
variable (f : Multiplicative (Fin 4 → ZMod p) ≃* E)

theorem const_of_Φ_eq_zero [Fact p.Prime] {n : Fin 5 → ZMod p} (hn : M.Φ f n = 0) :
    ∃ s : ZMod p, ∀ i, n i = s := by
  have hmem : n ∈ Submodule.span (ZMod p) {fun _ : Fin 5 => (1 : ZMod p)} := by
    rw [← M.ker_Φ f]
    exact hn
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨s, fun i => by simpa using (congrFun hs i).symm⟩

theorem u_ne [Fact p.Prime] {a b : Fin 5} (hab : a ≠ b) : M.u f b - M.u f a ≠ 0 := by
  classical
  intro h
  have hΦ : M.Φ f (Pi.single b 1 - Pi.single a 1) = 0 := by
    simp only [map_sub, Φ, Fintype.linearCombination_apply_single, one_smul]
    exact h
  obtain ⟨s, hs⟩ := M.const_of_Φ_eq_zero f hΦ
  obtain ⟨e, hea, heb, -, -⟩ := WeylIso.exists_fin_ne (n := 4) (by norm_num) a b a b
  have h1 := hs e
  have h2 := hs b
  simp [hea, heb, Ne.symm hab] at h1 h2
  exact one_ne_zero (h2.trans h1.symm)

theorem u_indep [Fact p.Prime] {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d)
    (hne1 : ¬ (a = c ∧ b = d)) (hne2 : ¬ (a = d ∧ b = c)) (α β : ZMod p)
    (h : α • (M.u f b - M.u f a) + β • (M.u f d - M.u f c) = 0) : α = 0 ∧ β = 0 := by
  classical
  have hΦ : M.Φ f (Pi.single b α - Pi.single a α + Pi.single d β - Pi.single c β) = 0 := by
    simp only [map_add, map_sub, Φ, Fintype.linearCombination_apply_single]
    rw [← h]
    simp only [smul_sub]
    abel
  obtain ⟨s, hs⟩ := M.const_of_Φ_eq_zero f hΦ
  obtain ⟨e, hea, heb, hec, hed⟩ := WeylIso.exists_fin_ne (n := 4) (by norm_num) a b c d
  have hs0 : s = 0 := by
    rw [← hs e]
    simp [hea, heb, hec, hed]
  have hn : ∀ i, (Pi.single b α - Pi.single a α + Pi.single d β - Pi.single c β : Fin 5 → ZMod p) i
      = 0 := fun i => by rw [hs i, hs0]
  by_cases hda : d = a
  ·
    have hca : c ≠ a := fun hc => hcd (hc.trans hda.symm)
    have hcb : c ≠ b := fun hc => hne2 ⟨hda.symm, hc.symm⟩
    have hβ : β = 0 := by
      have := hn c
      simp [hca, hcb, hcd] at this
      exact this
    refine ⟨?_, hβ⟩
    have := hn b
    simp [Ne.symm hab, hβ] at this
    exact this
  · by_cases hdb : d = b
    · have hca : c ≠ a := fun hc => hne1 ⟨hc.symm, hdb.symm⟩
      have hcb : c ≠ b := fun hc => hcd (hc.trans hdb.symm)
      have hβ : β = 0 := by
        have := hn c
        simp [hca, hcb, hcd] at this
        exact this
      refine ⟨?_, hβ⟩
      have := hn b
      simp [Ne.symm hab, hβ] at this
      exact this
    · have hβ : β = 0 := by
        have := hn d
        simp [hda, hdb, Ne.symm hcd] at this
        exact this
      refine ⟨?_, hβ⟩
      have := hn b
      simp [Ne.symm hab, hβ] at this
      exact this

end Model

end CFSG.RankThree.PartOne.U5K.Pkg
