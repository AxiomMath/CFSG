module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2
public import CFSG.LocalAnalysis.StandardType.GGIndepFixLinePerm
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6km_ext_basis {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M] [Module (ZMod p) M]
    {n : ℕ} (b : Module.Basis (Fin n) (ZMod p) M) {e₁ e₂ : M ≃ₗ[ZMod p] M}
    (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : M →ₗ[ZMod p] M) = (e₂ : M →ₗ[ZMod p] M) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : M →ₗ[ZMod p] M => f v) h'

private lemma l6km_restrict_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (T : Submodule (ZMod p) V) (g : ↥(ggLinStab T)) (v : ↥T) :
    (((ggLinRestrictHom T g) v : ↥T) : V) = (g : V ≃ₗ[ZMod p] V) (v : V) := by
  simp [ggLinRestrictHom, LinearEquiv.ofSubmodules_apply]

theorem l6km_monomial_setup {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) ↥(ggFixLineT r s))
    (hmon : ∀ a ∈ ggFixLineQ S, ∀ i, ∃ j, ∃ c : ZMod p, c ≠ 0 ∧ a (f i) = c • f j) :
    ∃ (π : ↥(ggFixLineQ S) →* Equiv.Perm (Fin n))
      (η : ↥(Subgroup.closure (Set.range r)) →* ↥(ggFixLineQ S)),
      (∀ (a : ↥(ggFixLineQ S)) (i : Fin n), ∃ c : ZMod p, c ≠ 0 ∧
        (a : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f i) = c • f (π a i)) ∧
      (∀ a : ↥(ggFixLineQ S), π a = 1 → ∀ i : Fin n, ∃ c : ZMod p,
        (a : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) (f i) = c • f i) ∧
      Function.Injective (π.comp η) ∧
      Nat.card ↥(Subgroup.closure (Set.range r)) = N.factorial ∧
      (∀ (i : Fin (N - 1)) (u : ↥(ggFixLineT r s)),
        (((η ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩ :
            ↥(ggFixLineQ S)) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) u : V)
          = r i (u : V)) ∧
      n = N := by
  classical
  let T : Submodule (ZMod p) V := ggFixLineT r s
  let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r ∪ Set.range s)
  let P : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r)
  let Q : Subgroup (↥T ≃ₗ[ZMod p] ↥T) := ggFixLineQ S
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s S.s_refl S.fix_H
  have hPA : P ≤ A := Subgroup.closure_mono (Set.subset_union_left)
  let ρA : ↥A →* (↥T ≃ₗ[ZMod p] ↥T) :=
    (ggLinRestrictHom T).comp (Subgroup.inclusion (ggFixLine_A_le_stab S))
  let ρP : ↥P →* (↥T ≃ₗ[ZMod p] ↥T) := ρA.comp (Subgroup.inclusion hPA)
  have hρAinj : Function.Injective ρA := ggFixLine_restrict_injective S
  have hQrange : Q = ρA.range := rfl
  have hmon_all : ∀ a : ↥Q, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
      (∀ i, c i ≠ 0) ∧ ∀ i, (a : ↥T ≃ₗ[ZMod p] ↥T) (f i) = c i • f (σ i) := by
    intro a
    let σf : Fin n → Fin n := fun i => (hmon a.1 a.2 i).choose
    let cf : Fin n → ZMod p := fun i => ((hmon a.1 a.2 i).choose_spec).choose
    have hcf : ∀ i, cf i ≠ 0 := fun i => ((hmon a.1 a.2 i).choose_spec).choose_spec.1
    have hσf : ∀ i, (a : ↥T ≃ₗ[ZMod p] ↥T) (f i) = cf i • f (σf i) :=
      fun i => ((hmon a.1 a.2 i).choose_spec).choose_spec.2
    have hinj : Function.Injective σf := by
      intro i j hij
      have h1 : cf j • (a : ↥T ≃ₗ[ZMod p] ↥T) (f i) = cf i • (a : ↥T ≃ₗ[ZMod p] ↥T) (f j) := by
        rw [hσf i, hσf j, hij, smul_smul, smul_smul, mul_comm]
      have h2 : (a : ↥T ≃ₗ[ZMod p] ↥T) (cf j • f i) = (a : ↥T ≃ₗ[ZMod p] ↥T) (cf i • f j) := by
        rw [map_smul, map_smul]
        exact h1
      have h3 : cf j • f i = cf i • f j := (a : ↥T ≃ₗ[ZMod p] ↥T).injective h2
      exact f.linearIndependent.eq_of_smul_apply_eq_smul_apply (cf j) (cf i) i j (hcf j) h3
    have hsurj : Function.Surjective σf := by
      intro k
      have hsymm_mem : (a : ↥T ≃ₗ[ZMod p] ↥T).symm ∈ Q := by
        have hh : ((a⁻¹ : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) = (a : ↥T ≃ₗ[ZMod p] ↥T).symm := by
          rw [Subgroup.coe_inv]
          rfl
        rw [← hh]
        exact Q.inv_mem a.2
      let b : ↥Q := ⟨(a : ↥T ≃ₗ[ZMod p] ↥T).symm, hsymm_mem⟩
      let d : ZMod p := ((hmon b.1 b.2 k).choose_spec).choose
      have hd : d ≠ 0 := ((hmon b.1 b.2 k).choose_spec).choose_spec.1
      let j : Fin n := (hmon b.1 b.2 k).choose
      have hdj : (b : ↥T ≃ₗ[ZMod p] ↥T) (f k) = d • f j :=
        ((hmon b.1 b.2 k).choose_spec).choose_spec.2
      have hbcoe : (b : ↥T ≃ₗ[ZMod p] ↥T) = (a : ↥T ≃ₗ[ZMod p] ↥T).symm := rfl
      have h1 : f k = d • (a : ↥T ≃ₗ[ZMod p] ↥T) (f j) := by
        have hh := congrArg (fun w => (a : ↥T ≃ₗ[ZMod p] ↥T) w) hdj
        rw [hbcoe, LinearEquiv.apply_symm_apply, map_smul] at hh
        exact hh
      have h2 : f k = (d * cf j) • f (σf j) := by
        rw [h1, hσf j, smul_smul]
      have h3 : (1 : ZMod p) • f k = (d * cf j) • f (σf j) := by
        rw [one_smul]
        exact h2
      have hk_eq : k = σf j :=
        f.linearIndependent.eq_of_smul_apply_eq_smul_apply (1 : ZMod p) (d * cf j) k (σf j)
          one_ne_zero h3
      exact ⟨j, hk_eq.symm⟩
    exact ⟨Equiv.ofBijective σf ⟨hinj, hsurj⟩, cf, hcf, fun i => by
      show (a : ↥T ≃ₗ[ZMod p] ↥T) (f i) = cf i • f ((Equiv.ofBijective σf ⟨hinj, hsurj⟩) i)
      rw [hσf i]
      rfl⟩
  obtain ⟨π, hπ, hπker, _hπcomm, _hπp⟩ := ggRC_monomial_hom f Q (fun a ha => hmon_all ⟨a, ha⟩)
  have hρPmem : ∀ g : ↥P, ρP g ∈ Q := by
    intro g
    rw [hQrange]
    exact MonoidHom.mem_range.mpr ⟨Subgroup.inclusion hPA g, rfl⟩
  let η : ↥P →* ↥Q := ρP.codRestrict Q hρPmem
  let ψ : ↥P →* Equiv.Perm (Fin n) := π.comp η
  have hηinj : Function.Injective η := by
    intro y z hyz
    have hval : ρP y = ρP z := by
      have hh := congrArg (fun t : ↥Q => (t : ↥T ≃ₗ[ZMod p] ↥T)) hyz
      simpa [η, MonoidHom.codRestrict_apply] using hh
    have hyzA : Subgroup.inclusion hPA y = Subgroup.inclusion hPA z := by
      apply hρAinj
      simpa [ρP, MonoidHom.comp_apply] using hval
    exact Subtype.ext (by
      simpa using congrArg (fun t : ↥A => (t : V ≃ₗ[ZMod p] V)) hyzA)
  have hdiag_comm : ∀ a b : ↥Q, π a = 1 → π b = 1 → a * b = b * a := by
    intro a b ha hb
    apply Subtype.ext
    apply l6km_ext_basis f
    intro i
    obtain ⟨c, hc⟩ := hπker a ha i
    obtain ⟨d, hd⟩ := hπker b hb i
    show (a : ↥T ≃ₗ[ZMod p] ↥T) ((b : ↥T ≃ₗ[ZMod p] ↥T) (f i))
        = (b : ↥T ≃ₗ[ZMod p] ↥T) ((a : ↥T ≃ₗ[ZMod p] ↥T) (f i))
    rw [hd, hc, map_smul, map_smul, hc, hd, smul_smul, smul_smul, mul_comm]
  let KP : Subgroup ↥P := ψ.ker
  let K : Subgroup (V ≃ₗ[ZMod p] V) := KP.map (Subgroup.subtype P)
  have hKP : K ≤ P := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, _hz, rfl⟩ := hy
    exact z.2
  have hKn : ∀ g ∈ P, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    rw [Subgroup.mem_map] at hk ⊢
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    refine ⟨⟨g, hg⟩ * k₀ * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · exact ψ.normal_ker.conj_mem k₀ hk₀ ⟨g, hg⟩
    · simp
  have hKab : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k := by
    intro k hk k' hk'
    rw [Subgroup.mem_map] at hk hk'
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    obtain ⟨k₀', hk₀', rfl⟩ := hk'
    have h1 : k₀ * k₀' = k₀' * k₀ := by
      apply hηinj
      rw [map_mul, map_mul]
      exact hdiag_comm (η k₀) (η k₀') hk₀ hk₀'
    rw [← map_mul, ← map_mul, h1]
  have hKbot : K = ⊥ := ggFixLine_P_abelian_normal_trivial S K hKP hKn hKab
  have hKPbot : KP = ⊥ := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_bot]
      have hgK : (Subgroup.subtype P) g ∈ K := ⟨g, hg, rfl⟩
      rw [hKbot, Subgroup.mem_bot] at hgK
      apply Subtype.ext
      simpa using hgK
    · exact bot_le
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hKPbot
  have hPcard : Nat.card ↥P = N.factorial := ggFixLine_P_card S
  have hcard_le : N.factorial ≤ n.factorial := by
    calc N.factorial = Nat.card ↥P := hPcard.symm
      _ ≤ Nat.card (Equiv.Perm (Fin n)) := Nat.card_le_card_of_injective ψ hψinj
      _ = n.factorial := by rw [Nat.card_perm, Nat.card_fin]
  have hne : n ≠ N - 1 := by
    have hN5 : 5 ≤ N := S.five_le
    intro hn
    rw [hn] at hcard_le
    have hlt : Nat.factorial (N - 1) < Nat.factorial N :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    omega
  have hTprops := ggFixLine_T_props S
  have hfinT : Module.finrank (ZMod p) ↥T = n := by
    simpa using Module.finrank_eq_card_basis f
  have hn : n = N := by
    have h1 : N - 1 ≤ n := hfinT ▸ hTprops.2.2.1
    have h2 : n ≤ N := hfinT ▸ hTprops.2.2.2
    omega
  let gi : Fin (N - 1) → ↥P := fun i => ⟨r i, Subgroup.subset_closure (Set.mem_range_self i)⟩
  let Afun : Fin (N - 1) → ↥Q := fun i => η (gi i)
  have hcoord : ∀ (i : Fin (N - 1)) (u : ↥T),
      (((Afun i : ↥Q) : ↥T ≃ₗ[ZMod p] ↥T) u : V) = r i (u : V) := by
    intro i u
    change (((ggLinRestrictHom T) (Subgroup.inclusion (ggFixLine_A_le_stab S)
      (Subgroup.inclusion hPA (gi i))) u : V)) = r i (u : V)
    rw [l6km_restrict_apply]
    rfl
  exact ⟨π, η, hπ, hπker, hψinj, hPcard, hcoord, hn⟩


private lemma l6km_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hp2 : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact hp hp2

lemma l6km_pair_diag {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) : α i (h i) = 2 := by
  rw [S.pair i i]
  simp [CartanMatrix.A]

lemma l6km_rsq {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V} (S : GGFixLineHyp p N h α r s x)
    (i : Fin (N - 1)) : r i * r i = 1 := by
  ext v
  change r i (r i v) = v
  rw [S.r_form i (r i v), S.r_form i v, map_sub, map_smul, l6km_pair_diag S i]
  module

lemma l6km_eq_swap_of {n : ℕ} (τ : Equiv.Perm (Fin n)) {p q : Fin n}
    (hp : τ p = q) (hq : τ q = p)
    (hfix : ∀ k, τ k ≠ k → k = p ∨ k = q) : τ = Equiv.swap p q := by
  ext k
  by_cases hk : k = p
  · subst hk
    rw [hp, Equiv.swap_apply_left]
  · by_cases hk' : k = q
    · subst hk'
      rw [hq, Equiv.swap_apply_right]
    · have hfixk : τ k = k := by
        by_contra hne
        rcases hfix k hne with h | h
        · exact hk h
        · exact hk' h
      rw [hfixk, Equiv.swap_apply_of_ne_of_ne hk hk']

lemma l6km_move_rank_one {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)}
    {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (Afun : Fin (N - 1) → ↥(ggFixLineQ S))
    (hcoord : ∀ (i : Fin (N - 1)) (u : ↥(ggFixLineT r s)),
      (((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s)) u : V) = r i (u : V))
    (i : Fin (N - 1)) :
    Module.finrank (ZMod p) (ggLinMove
      ((Afun i) : ↥(ggFixLineT r s) ≃ₗ[ZMod p] ↥(ggFixLineT r s))) = 1 := by
  classical
  haveI : Finite ι := S.finite_family
  haveI : Module.Finite (ZMod p) V := ggFixLine_finite (p := p) s S.s_refl S.fix_H
  let T : Submodule (ZMod p) V := ggFixLineT r s
  have hTprops := ggFixLine_T_props S
  have hhiT : ∀ i, h i ∈ T := fun i =>
    hTprops.2.1 (Submodule.subset_span (Set.mem_range_self i))
  let hi : ↥T := ⟨h i, hhiT i⟩
  have hhi_ne : hi ≠ 0 := by
    intro h0
    exact S.indep.ne_zero i (by simpa [hi] using congrArg Subtype.val h0)
  have hval : ∀ u : ↥T,
      (((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) u - u : ↥T) = (-α i (u : V)) • hi := by
    intro u
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, hcoord i u, S.r_form i (u : V)]
    module
  have hle : ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) ≤
      Submodule.span (ZMod p) {hi} := by
    intro w hw
    rw [ggLinMove, LinearMap.mem_range] at hw
    obtain ⟨u, hu⟩ := hw
    rw [Submodule.mem_span_singleton]
    refine ⟨-α i (u : V), ?_⟩
    rw [← hu, LinearMap.sub_apply, LinearMap.id_apply]
    exact Subtype.ext (by
      simpa [Submodule.coe_smul] using congrArg Subtype.val (hval u).symm)
  have h1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {hi}) = 1 :=
    finrank_span_singleton hhi_ne
  have h2 : 1 ≤ Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T)) := by
    have hw0 : ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi ≠ 0 := by
      intro h0
      have hz : ((-α i (hi : V)) • hi : ↥T) = 0 := by
        rw [← hval hi, h0]
      have hcoef : (-α i (h i)) • h i = 0 := by
        have := congrArg Subtype.val hz
        simpa [hi] using this
      have hcoef' : (α i (h i)) • h i = 0 := by
        have := congrArg Neg.neg hcoef
        simpa using this
      have h2 : (2 : ZMod p) • h i = 0 := by
        simpa [l6km_pair_diag S i] using hcoef'
      exact (l6km_two_ne_zero S.odd) ((smul_eq_zero.mp h2).resolve_right (S.indep.ne_zero i))
    have hmem : ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi ∈
        ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) := by
      rw [ggLinMove, LinearMap.mem_range]
      exact ⟨hi, rfl⟩
    have hspan_le : Submodule.span (ZMod p)
        {((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) hi - hi} ≤
        ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T) := by
      rw [Submodule.span_le]
      rintro w (rfl : w = _)
      exact hmem
    have hfin := Submodule.finrank_mono hspan_le
    rwa [finrank_span_singleton hw0] at hfin
  have h3 : Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T)) ≤ 1 := by
    have hfin := Submodule.finrank_mono hle
    rwa [h1] at hfin
  show Module.finrank (ZMod p)
      (ggLinMove ((Afun i : ↥(ggFixLineQ S)) : ↥T ≃ₗ[ZMod p] ↥T)) = 1
  omega

end CFSG.StandardType

end
