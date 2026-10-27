module

public import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.S12.Sec1322Reflect
public import CFSG.RankThree.PartOne.N1322.CoreDefs

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G} {c : G}
  {L E : Subgroup G} (f : Multiplicative (Fin 3 → ZMod p) ≃* E)

omit [Finite G] in
theorem isRefl_coordGL {t : MulAut E} (ht : IsAutReflection p E t) :
    IsRefl (LinAlg.coordGL f t) := by
  obtain ⟨hord, hrank⟩ := (LinAlg.isAutReflection_iff_matrix f t).mp ht
  refine isRefl_of_rank_one ?_ hrank
  have h1 := pow_orderOf_eq_one (LinAlg.coordGL f t)
  rwa [hord, pow_two] at h1

omit [Finite G] in
theorem map_reflectionGroup :
    (reflectionGroup p E).map (LinAlg.coordGL f) =
      Subgroup.closure (LinAlg.coordGL f '' reflectionSet p E) := by
  show (Subgroup.closure (reflectionSet p E)).map (LinAlg.coordGL f) = _
  rw [MonoidHom.map_closure]

theorem coordGL_conj_mem {x t : MulAut E} (hx : x ∈ reflectionGroup p E)
    (ht : t ∈ reflectionSet p E) : x * t * x⁻¹ ∈ reflectionSet p E := by
  obtain ⟨w, hw, rfl⟩ := Sec1322.exists_lift (Sec1322.reflectionGroup_le E hx)
  exact conj_mem_reflectionSet (Fact.out : p.Prime) ht hw

omit [Fact p.Prime] in
theorem torusImage_le_reflectionGroup (hF12 : Sec12Facts G p A c L E) :
    torusImage E L ≤ reflectionGroup p E := by
  rw [hF12.three.1]
  exact Subgroup.closure_mono Set.inter_subset_left

theorem map_closure_inter (hF12 : Sec12Facts G p A c L E) :
    Subgroup.closure (LinAlg.coordGL f '' reflectionSet p E ∩
        (((torusImage E L).map (LinAlg.coordGL f) : Subgroup (GL (Fin 3) (ZMod p))) :
          Set (GL (Fin 3) (ZMod p)))) = (torusImage E L).map (LinAlg.coordGL f) := by
  have h1 : LinAlg.coordGL f '' reflectionSet p E ∩
      (((torusImage E L).map (LinAlg.coordGL f) : Subgroup (GL (Fin 3) (ZMod p))) :
        Set (GL (Fin 3) (ZMod p))) =
      LinAlg.coordGL f '' (reflectionSet p E ∩ (torusImage E L : Set (MulAut E))) := by
    rw [Set.image_inter (LinAlg.coordGL_injective f)]
    try rfl
  rw [h1, ← MonoidHom.map_closure, ← hF12.three.1]

omit [Finite G] in
theorem coordGL_mulVec_eq (φ : MulAut E) (w : Fin 3 → ZMod p) :
    ((LinAlg.coordGL f φ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w =
      LinAlg.coordHom f φ w := LinAlg.coordGL_mulVec f φ w

theorem fixes_field (h12 : Sec12Hyp G p A c L E) {v : Fin 3 → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) :
    ∀ l ∈ (torusImage E L).map (LinAlg.coordGL f),
      (l : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = v := by
  intro l hl
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hl
  rw [coordGL_mulVec_eq]
  exact Sec127.fixes_of_mem_map f hv (Sec12Three.comm_c_L h12) _
    (Subgroup.mem_map_of_mem _ hψ)

theorem inv_cases (h12 : Sec12Hyp G p A c L E) (hF12 : Sec12Facts G p A c L E)
    {v : Fin 3 → ZMod p} (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hv0 : v ≠ 0)
    (U : Submodule (ZMod p) (Fin 3 → ZMod p))
    (hU : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), ∀ x ∈ U, l x ∈ U)
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) :
    U = Submodule.span (ZMod p) {v} ∨
      (U = LinAlg.bsub f ⁅E, L ⊓ torusNormalizer E⁆ ∧ Module.finrank (ZMod p) U + 1 = 3) := by
  obtain ⟨B, hBE, rfl⟩ := LinAlg.exists_bsub_eq f U
  have hinv : torusInvariant E L B := by
    rw [LinAlg.torusInvariant_iff f L hBE]
    intro φ hφ y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact hU _ (Subgroup.mem_map_of_mem _ hφ) z hz
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact hU0 (LinAlg.bsub_bot f)
  have hBE' : B ≠ E := by
    rintro rfl
    exact hU1 (LinAlg.bsub_self f)
  have hcE : Subgroup.zpowers c ≤ E :=
    Subgroup.zpowers_le.mpr (hv ▸ (f (Multiplicative.ofAdd v)).2)
  obtain ⟨h1, h2⟩ := hF12.four
  rcases h1 B hBE hinv hB0 hBE' with rfl | rfl
  · exact Or.inl (Sec127.bsub_zpowers_eq_span f hv)
  · rcases h2 with ⟨hsup, hinf⟩ | ⟨-, hEE⟩
    · right
      exact ⟨rfl, Sec127.finrank_bsub_add_one f hv hv0 hcE hBE hsup hinf⟩
    · exact absurd hEE hBE'

theorem lines_field (h12 : Sec12Hyp G p A c L E) (hF12 : Sec12Facts G p A c L E)
    {v : Fin 3 → ZMod p} (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hv0 : v ≠ 0) :
    ∀ w : Fin 3 → ZMod p, w ≠ 0 →
      (∀ l ∈ (torusImage E L).map (LinAlg.coordGL f), ∃ μ : ZMod p,
        (l : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w = μ • w) → ∃ μ : ZMod p, w = μ • v := by
  intro w hw0 hinv
  have hU : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), ∀ x ∈ Submodule.span (ZMod p) {w},
      l x ∈ Submodule.span (ZMod p) {w} := by
    intro l hl x hx
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hl
    obtain ⟨μ, hμ⟩ := hinv (LinAlg.coordGL f ψ) (Subgroup.mem_map_of_mem _ hψ)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h1 : LinAlg.coordHom f ψ w = μ • w := by rw [← coordGL_mulVec_eq f ψ w]; exact hμ
    rw [map_smul, h1, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hne : Submodule.span (ZMod p) {w} ≠ ⊥ := by
    intro h
    exact hw0 (Submodule.span_singleton_eq_bot.mp h)
  have hfr : Module.finrank (ZMod p) (Submodule.span (ZMod p) {w}) = 1 :=
    finrank_span_singleton hw0
  have hnt : Submodule.span (ZMod p) {w} ≠ ⊤ := by
    intro h
    rw [h, finrank_top, Module.finrank_fin_fun] at hfr
    omega
  rcases inv_cases f h12 hF12 hv hv0 _ hU hne hnt with h | ⟨-, h⟩
  · have : w ∈ Submodule.span (ZMod p) {v} := h ▸ Submodule.mem_span_singleton_self w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨a, ha.symm⟩
  · rw [hfr] at h
    omega

theorem N_field (hF12 : Sec12Facts G p A c L E)
    {v : Fin 3 → ZMod p} (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) :
    ∀ h ∈ (reflectionGroup p E).map (LinAlg.coordGL f),
      (∃ μ : ZMod p, (h : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = μ • v) →
      ∀ l ∈ (torusImage E L).map (LinAlg.coordGL f),
        h * l * h⁻¹ ∈ (torusImage E L).map (LinAlg.coordGL f) := by
  intro h hh hμ l hl
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hh
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hl
  obtain ⟨μ, hμ⟩ := hμ
  have hφW : φ ∈ torusWeyl E := Sec1322.reflectionGroup_le E hφ
  have hg : LinAlg.coordHom f φ ∈ (torusWeyl E).map (LinAlg.coordHom f) :=
    Subgroup.mem_map_of_mem _ hφW
  have hgv : LinAlg.coordHom f φ v ∈ Submodule.span (ZMod p) {v} := by
    rw [← coordGL_mulVec_eq f φ v, hμ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have h3 := Sec127.normalizes_map f hv (hF12.twoB) _ hg hgv (LinAlg.coordHom f ψ)
    (Subgroup.mem_map_of_mem _ hψ)
  obtain ⟨ψ', hψ', hψ'eq⟩ := Subgroup.mem_map.mp h3
  have hψ'' : ψ' = φ * ψ * φ⁻¹ := by
    apply LinAlg.coordHom_injective f
    rw [hψ'eq, map_mul, map_mul, map_inv]
  refine Subgroup.mem_map.mpr ⟨ψ', hψ', ?_⟩
  rw [hψ'', map_mul, map_mul, map_inv]

end CFSG.RankThree.PartOne.N1322
