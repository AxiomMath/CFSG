module

public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatumTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoCaseIIDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin

public section

namespace CFSG.StandardType

open CFSG Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def GGQ2WDatum.dualTranspose {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) :
    GGQ2WDatum p where
  Λ := D.Λ
  coxeter := D.coxeter
  cartan := D.cartan.transpose
  V := Module.Dual (ZMod p) D.V
  coroot := D.root
  root := fun k => Module.Dual.eval (ZMod p) D.V (D.coroot k)
  isWeyl := D.isWeyl
  isCartan := by
    refine ⟨fun i => by simpa using D.isCartan.1 i, fun i j hij => ?_⟩
    simp only [Matrix.transpose_apply]
    rcases D.isCartan.2 i j hij with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, h3, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, by rw [mul_comm]; exact h2, h4, h3⟩))
  pairing := fun i j => by
    simp [D.pairing]

theorem ggContra_simpleRefl_wdDual {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (k : D.Λ) :
    ggContra (D.simpleRefl k) = D.dualTranspose.simpleRefl k := by
  have h_ours : (Dual.eval (ZMod p) D.V) (D.coroot k) (D.root k) = 2 := by
    simpa using D.root_coroot_self k
  ext f v
  rw [ggContra_apply]
  change f ((Module.reflection (D.root_coroot_self k)).symm v) =
    (Module.reflection h_ours) f v
  rw [Module.reflection_symm (D.root_coroot_self k),
    Module.reflection_apply v (D.root_coroot_self k), Module.reflection_apply f h_ours]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Dual.eval_apply,
    smul_eq_mul]
  ring

theorem ggContra_weyl_wdDual {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) :
    D.weyl.map ggContra = D.dualTranspose.weyl := by
  change (Subgroup.closure (Set.range D.simpleRefl)).map ggContra =
    Subgroup.closure (Set.range D.dualTranspose.simpleRefl)
  rw [MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  exact congrArg Set.range (funext fun k => ggContra_simpleRefl_wdDual D k)

theorem GGQ2WDatum.ker_pi_root_le {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    LinearMap.ker (LinearMap.pi fun i : D.Λ => D.root i) ≤ Submodule.span (ZMod p) {u} := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [← hfix v]
  intro g hg
  have hv0 : ∀ i : D.Λ, D.root i v = 0 := fun i => congrFun hv i
  refine Subgroup.closure_induction (p := fun g _ => g v = v) ?_ ?_ ?_ ?_ hg
  · rintro g ⟨k, rfl⟩
    rw [D.simpleRefl_apply, hv0 k, zero_smul, sub_zero]
  · rfl
  · intro g h _ _ hg hh
    rw [LinearEquiv.mul_apply, hh, hg]
  · intro g _ hg
    have h1 : g.symm (g v) = v := g.symm_apply_apply v
    rw [hg] at h1
    exact h1

theorem GGQ2WDatum.finrank_le_card_add_one_of_fix {p : ℕ} [Fact p.Prime] (D : GGQ2WDatum p)
    (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u}) :
    Module.finrank (ZMod p) D.V ≤ Fintype.card D.Λ + 1 := by
  classical
  by_cases hfd : FiniteDimensional (ZMod p) D.V
  swap
  · rw [Module.finrank_of_not_finite hfd]
    omega
  let Φ : D.V →ₗ[ZMod p] (D.Λ → ZMod p) := LinearMap.pi fun i => D.root i
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hr : Module.finrank (ZMod p) (LinearMap.range Φ) ≤ Fintype.card D.Λ := by
    have h := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hsp : Module.finrank (ZMod p) (Submodule.span (ZMod p) {u}) ≤ 1 := by
    by_cases h0 : u = 0
    · rw [h0, Submodule.span_zero_singleton, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton h0]
  have hk : Module.finrank (ZMod p) (LinearMap.ker Φ) ≤ 1 :=
    (Submodule.finrank_mono (D.ker_pi_root_le u hfix)).trans hsp
  omega

theorem GGQ2WDatum.root_linearIndependent_of_finrank {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (D : GGQ2WDatum p) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod p) {u})
    (hdim : Module.finrank (ZMod p) D.V = Fintype.card D.Λ + 1) :
    LinearIndependent (ZMod p) D.root := by
  classical
  have : FiniteDimensional (ZMod p) D.V := Module.finite_of_finrank_pos (by omega)
  let Φ : D.V →ₗ[ZMod p] (D.Λ → ZMod p) := LinearMap.pi fun i => D.root i
  have hker : LinearMap.ker Φ = Submodule.span (ZMod p) {u} := by
    refine le_antisymm (D.ker_pi_root_le u hfix) fun v hv => ?_
    rw [LinearMap.mem_ker]
    rw [← hfix v] at hv
    funext i
    have h1 : D.simpleRefl i v = v := hv _ (D.simpleRefl_mem_weyl i)
    rw [D.simpleRefl_apply] at h1
    have h2 : D.root i v • D.coroot i = 0 := sub_eq_self.mp h1
    have hc : D.coroot i ≠ 0 := by
      intro h0
      have h3 := D.root_coroot_self i
      rw [h0, map_zero] at h3
      exact zmod_two_ne_zero hp h3.symm
    exact (smul_eq_zero.mp h2).resolve_right hc
  have hrange : LinearMap.range Φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hker, finrank_span_singleton hu0, hdim] at hrn
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  obtain ⟨v, hv⟩ : ∃ v, Φ v = Pi.single j 1 := by
    have : Pi.single j (1 : ZMod p) ∈ LinearMap.range Φ := by rw [hrange]; trivial
    exact this
  have h1 := congrArg (fun f : Module.Dual (ZMod p) D.V => f v) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at h1
  have hvi : ∀ i : D.Λ, D.root i v = (Pi.single j (1 : ZMod p) : D.Λ → ZMod p) i :=
    fun i => congrFun hv i
  simp only [hvi, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  exact h1

theorem GGQ2WDatum.inner_of_ker (D : GGQ2WDatum 3) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u})
    (hker : ∃ κ : D.Λ → ZMod 3, κ ≠ 0 ∧ ∀ i : D.Λ, ∑ j : D.Λ, (D.cartan i j : ZMod 3) * κ j = 0)
    (hcard : 3 ≤ Fintype.card D.Λ)
    (hpos : LinearIndependent (ZMod 3) D.coroot ∨
      Module.finrank (ZMod 3) D.V = Fintype.card D.Λ + 1)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.weyl, ∀ g ∈ D.weyl, T * g * T⁻¹ = w * g * w⁻¹ := by
  classical
  obtain ⟨n, C₀, e, hC, hsymm, hW⟩ : ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ)
      (e : Fin n ≃ D.Λ), (∀ i j, D.cartan (e i) (e j) = C₀ i j) ∧
        (∀ i j, C₀ i j = C₀ j i) ∧ GGQ2WeylInner n C₀ := by
    rcases D.A_or_E6_of_ker hker hcard with ⟨k, hk, e, he⟩ | ⟨e, he⟩
    · refine ⟨3 * k - 1, CartanMatrix.A (3 * k - 1), e, he, fun i j => ?_,
        ggQ2WeylInner_A (by omega)⟩
      exact congrFun (congrFun (CartanMatrix.A_transpose (3 * k - 1)) j) i
    · refine ⟨6, CartanMatrix.E 6, e, he, fun i j => ?_, ggQ2WeylInner_E6⟩
      exact congrFun (congrFun (CartanMatrix.E_transpose 6) j) i
  rcases hpos with hind | hdimeq
  · exact D.inner_of_transport C₀ e hC hind hW T hT
  have hpar : D.weyl.map ggContra = D.dualTranspose.weyl := ggContra_weyl_wdDual D
  have hC' : ∀ i j, D.dualTranspose.cartan (e i) (e j) = C₀ i j := fun i j => by
    change D.cartan (e j) (e i) = C₀ i j
    rw [hC, hsymm]
  have hind' : LinearIndependent (ZMod 3) D.dualTranspose.coroot :=
    D.root_linearIndependent_of_finrank (by decide) u hu0 hfix hdimeq
  let Wd : Subgroup (Module.Dual (ZMod 3) D.V ≃ₗ[ZMod 3] Module.Dual (ZMod 3) D.V) :=
    D.weyl.map ggContra
  have hTd : ggContra T ∈ Subgroup.normalizer (Wd : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g'
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨T * g * T⁻¹, (Subgroup.mem_normalizer_iff.mp hT g).mp hg, ?_⟩
      simp only [map_mul, map_inv]
    · rintro ⟨g, hg, hgg⟩
      refine ⟨T⁻¹ * g * T, ?_, ?_⟩
      · have h2 : T * (T⁻¹ * g * T) * T⁻¹ = g := by group
        exact (Subgroup.mem_normalizer_iff.mp hT (T⁻¹ * g * T)).mpr (by rw [h2]; exact hg)
      · have h3 : ggContra (T⁻¹ * g * T) = (ggContra T)⁻¹ * ggContra g * ggContra T := by
          rw [map_mul, map_mul, map_inv]
        rw [h3, hgg]
        group
  obtain ⟨w', hw', hconj'⟩ :=
    D.dualTranspose.inner_of_transport C₀ e hC' hind' hW (ggContra T) (hpar ▸ hTd)
  have hw'd : w' ∈ D.weyl.map ggContra := hpar ▸ hw'
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hw'd
  refine ⟨w, hw, fun g hg => ggContra_injective ?_⟩
  have hgd : ggContra g ∈ D.dualTranspose.weyl := hpar ▸ Subgroup.mem_map_of_mem _ hg
  have h := hconj' (ggContra g) hgd
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact h

theorem GGQ2WDatum.pmW_of_inner (D : GGQ2WDatum 3) (u : D.V)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u})
    (hcard : 3 ≤ Fintype.card D.Λ) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hinner : ∃ w ∈ D.weyl, ∀ g ∈ D.weyl, T * g * T⁻¹ = w * g * w⁻¹) :
    ∃ w ∈ D.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u} := by
  obtain ⟨w, hwW, hw⟩ := hinner
  set S : D.V ≃ₗ[ZMod 3] D.V := w⁻¹ * T with hSdef
  have hcommS : ∀ g ∈ D.weyl, S * g = g * S := by
    intro g hg
    have h1 : S * g * S⁻¹ = g := by
      rw [hSdef]
      calc (w⁻¹ * T) * g * (w⁻¹ * T)⁻¹
          = w⁻¹ * (T * g * T⁻¹) * w := by group
        _ = w⁻¹ * (w * g * w⁻¹) * w := by rw [hw g hg]
        _ = g := by group
    calc S * g = (S * g * S⁻¹) * S := by group
      _ = g * S := by rw [h1]
  obtain ⟨c, hc⟩ := D.exists_scalar_of_commute rfl u hfix (D.reflTransGen hcard)
      (S : D.V →ₗ[ZMod 3] D.V) (fun g hg v => by
        have h := congrArg (fun (e : D.V ≃ₗ[ZMod 3] D.V) => e v) (hcommS g hg)
        simp only [LinearEquiv.mul_apply] at h
        have h' : (S : D.V →ₗ[ZMod 3] D.V) (g v) = g ((S : D.V →ₗ[ZMod 3] D.V) v) := h
        rw [h', sub_self]
        exact Submodule.zero_mem _)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have hS : ∀ v, S v ∈ Submodule.span (ZMod 3) {u} := by
      intro v
      have hv := hc v
      rw [hc0, zero_smul, sub_zero] at hv
      exact hv
    obtain ⟨j⟩ := D.nonempty
    have hj : D.coroot j ∈ Submodule.span (ZMod 3) {u} := by
      obtain ⟨v, hv⟩ := S.surjective (D.coroot j)
      rw [← hv]
      exact hS v
    exact D.coroot_not_mem_span_of_fix rfl u hfix j hj
  have hc01 : c = 1 ∨ c = -1 := ggQ2_zmod3_eq_one_or_neg_one c hc_ne
  have hTw : ∀ v : D.V, T (w⁻¹ v) = S v := by
    intro v
    have hT_eq : T = w * S := by
      rw [hSdef]
      group
    have hSw : S (w⁻¹ v) = w⁻¹ (S v) := by
      have h := congrArg (fun (e : D.V ≃ₗ[ZMod 3] D.V) => e v)
        (hcommS w⁻¹ (Subgroup.inv_mem _ hwW))
      simpa only [LinearEquiv.mul_apply] using h
    rw [hT_eq, LinearEquiv.mul_apply, hSw]
    exact LinearEquiv.apply_symm_apply w (S v)
  refine ⟨w⁻¹, Subgroup.inv_mem _ hwW, c, hc01, ?_⟩
  intro v
  rw [hTw v]
  exact hc v

theorem GGQ2WDatum.pmW_of_ker (D : GGQ2WDatum 3) (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u})
    (hker : ∃ κ : D.Λ → ZMod 3, κ ≠ 0 ∧ ∀ i : D.Λ, ∑ j : D.Λ, (D.cartan i j : ZMod 3) * κ j = 0)
    (hdim : Module.finrank (ZMod 3) D.V ≤ Fintype.card D.Λ + 1)
    (h4 : 4 ≤ Module.finrank (ZMod 3) D.V)
    (_hTF : TransvectionFree D.weyl)
    (hpos : LinearIndependent (ZMod 3) D.coroot ∨
      Module.finrank (ZMod 3) D.V = Fintype.card D.Λ + 1)
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u} := by
  have hcard : 3 ≤ Fintype.card D.Λ := by omega
  exact D.pmW_of_inner u hfix hcard T (D.inner_of_ker u hu0 hfix hker hcard hpos T hT)

end CFSG.StandardType

end
