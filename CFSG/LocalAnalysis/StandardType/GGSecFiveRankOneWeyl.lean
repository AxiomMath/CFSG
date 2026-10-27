module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj

public section

namespace CFSG.StandardType

variable {G : Type} [Group G] [Finite G]

theorem ggRankOneIn_le (X Bs : Subgroup G) (r : MulAut ↥Bs) : ggRankOneIn X Bs r ≤ X := by
  rw [ggRankOneIn, ggOTwoPrime]
  exact (Subgroup.closure_le X).mpr fun y hy => (Subgroup.mem_inf.mp hy.1).1

theorem ggWeylElt_conj {Bs H : Subgroup G} {a r₀ : MulAut ↥Bs} (ha : a ∈ ggAutomizer H Bs)
    {n₀ : G} (hn₀S : n₀ ∈ ggRankOnePerf Bs r₀) (hn₀N : n₀ ∈ Subgroup.normalizer (Bs : Set G))
    (hn₀r : ∀ b : ↥Bs, ((r₀ b : ↥Bs) : G) = n₀ * b * n₀⁻¹) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) ∧
      g * n₀ * g⁻¹ ∈ ggRankOnePerf Bs (a * r₀ * a⁻¹) ∧
      g * n₀ * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, (((a * r₀ * a⁻¹) b : ↥Bs) : G) = (g * n₀ * g⁻¹) * b * (g * n₀ * g⁻¹)⁻¹ := by
  obtain ⟨g, hgH, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  refine ⟨g, hgH, hgN, hg, ?_, ?_, ?_⟩
  · exact (mem_ggRankOnePerf_conj_iff hg r₀ n₀).2 hn₀S
  · exact Subgroup.mul_mem (Subgroup.normalizer (Bs : Set G))
      (Subgroup.mul_mem _ hgN hn₀N) (Subgroup.inv_mem _ hgN)
  · intro b
    let b' : ↥Bs := a⁻¹ b
    have hb'a : a b' = b := by
      change a (a⁻¹ b) = b
      rw [MulAut.apply_inv_self]
    have hb'G : (b : G) = g * b' * g⁻¹ := by
      rw [← hb'a]
      exact hg b'
    have hstep : (a * r₀ * a⁻¹) b = a (r₀ b') := by
      rw [MulAut.mul_apply, MulAut.mul_apply]
    have hconj : (((a * r₀ * a⁻¹) b : ↥Bs) : G) = g * (n₀ * b' * n₀⁻¹) * g⁻¹ := by
      rw [hstep, hg (r₀ b'), hn₀r b']
    rw [hconj, hb'G]
    group

theorem ggRankOnePerf_commute_transport {Bs H : Subgroup G} {a r r' : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer H Bs)
    (h : ∀ x ∈ ggRankOnePerf Bs r, ∀ y ∈ ggRankOnePerf Bs r', x * y = y * x) :
    ∀ x ∈ ggRankOnePerf Bs (a * r * a⁻¹), ∀ y ∈ ggRankOnePerf Bs (a * r' * a⁻¹), x * y = y * x := by
  obtain ⟨g, -, -, hg⟩ := mem_ggAutomizer_iff.mp ha
  intro x hx y hy
  let x' : G := g⁻¹ * x * g
  let y' : G := g⁻¹ * y * g
  have hx'eq : g * x' * g⁻¹ = x := by
    unfold x'; group
  have hy'eq : g * y' * g⁻¹ = y := by
    unfold y'; group
  have hx' : x' ∈ ggRankOnePerf Bs r := by
    apply (mem_ggRankOnePerf_conj_iff hg r x').1
    rw [hx'eq]
    exact hx
  have hy' : y' ∈ ggRankOnePerf Bs r' := by
    apply (mem_ggRankOnePerf_conj_iff hg r' y').1
    rw [hy'eq]
    exact hy
  have key : x' * y' = y' * x' := h x' hx' y' hy'
  calc x * y = (g * x' * g⁻¹) * (g * y' * g⁻¹) := by rw [hx'eq, hy'eq]
    _ = g * (x' * y') * g⁻¹ := by group
    _ = g * (y' * x') * g⁻¹ := by rw [key]
    _ = (g * y' * g⁻¹) * (g * x' * g⁻¹) := by group
    _ = y * x := by rw [hy'eq, hx'eq]

theorem ggExists_mem_induces_of_simple {Bs N : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hN : ∀ i : ι, ∃ n ∈ N, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple i) : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹) :
    ∀ a ∈ A, ∃ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹ := by
  intro a ha
  let w : M.Group := e.symm ⟨a, ha⟩
  have hw : e w = ⟨a, ha⟩ := MulEquiv.apply_symm_apply e ⟨a, ha⟩
  have key : ∀ w : M.Group, ∃ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e w : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = g * b * g⁻¹ := by
    intro w
    refine CoxeterSystem.simple_induction M.toCoxeterSystem
      (p := fun v : M.Group => ∃ g ∈ N, g ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((((e v : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = g * b * g⁻¹) w ?_ ?_ ?_
    · intro i
      obtain ⟨n, hnN, hnnorm, hni⟩ := hN i
      exact ⟨n, hnN, hnnorm, by
        intro b
        simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hni b⟩
    · refine ⟨1, N.one_mem, (Subgroup.normalizer (Bs : Set G)).one_mem, ?_⟩
      intro b
      simp
    · intro w w' hw hw'
      obtain ⟨g, hgN, hgnorm, hgi⟩ := hw
      obtain ⟨g', hg'N, hg'norm, hg'i⟩ := hw'
      refine ⟨g * g', Subgroup.mul_mem N hgN hg'N,
        Subgroup.mul_mem (Subgroup.normalizer (Bs : Set G)) hgnorm hg'norm, ?_⟩
      intro b
      have hmul : ((e (w * w') : ↥A) : MulAut ↥Bs) b
          = ((e w : ↥A) : MulAut ↥Bs) (((e w' : ↥A) : MulAut ↥Bs) b) := by
        rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply]
      rw [hmul, hgi (((e w' : ↥A) : MulAut ↥Bs) b), hg'i b]
      group
  obtain ⟨g, hgN, hgnorm, hgind⟩ := key w
  refine ⟨g, hgN, hgnorm, ?_⟩
  intro b
  have hwij : ((e w : ↥A) : MulAut ↥Bs) = a := by
    rw [hw]
  rw [hwij] at hgind
  exact hgind b

theorem ggRankOnePerf_conj_le_iSup {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A)
    (hN : ∀ i : ι, ∃ n ∈ ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs),
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple i) : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹)
    (w : M.Group) (i : ι) :
    ggRankOnePerf Bs ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) ≤
      ⨆ j : ι, ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs) := by
  let T : Subgroup G := ⨆ j : ι, ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs)
  have hN' : ∀ j : ι, ∃ n ∈ T, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((((e (M.simple j) : ↥A) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹ := by
    intro j
    obtain ⟨n, hnS, hnN, hnj⟩ := hN j
    exact ⟨n, le_iSup (fun j : ι => ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs)) j hnS,
      hnN, hnj⟩
  obtain ⟨g, hgT, hgN, hgi⟩ :=
    ggExists_mem_induces_of_simple (Bs := Bs) (N := T) (A := A) e hN'
      ((e w : ↥A) : MulAut ↥Bs) (e w).2
  have hconj : (ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs)).map
      (MulAut.conj g).toMonoidHom
      = ggRankOnePerf Bs ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) := by
    have heq : ((e w : ↥A) : MulAut ↥Bs) * ((e (M.simple i) : ↥A) : MulAut ↥Bs)
        * (((e w : ↥A) : MulAut ↥Bs))⁻¹
        = ((e (w * M.simple i * w⁻¹) : ↥A) : MulAut ↥Bs) := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
      congr 1
      rw [← map_mul, ← map_inv, ← map_mul]
    rw [ggRankOnePerf_map_conj (Bs := Bs) (g := g) (a := ((e w : ↥A) : MulAut ↥Bs)) hgi
      ((e (M.simple i) : ↥A) : MulAut ↥Bs), heq]
  rw [← hconj]
  intro z hz
  obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hz
  rw [← hsz]
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Subgroup.mul_mem T
    (Subgroup.mul_mem T hgT
      (le_iSup (fun j : ι => ggRankOnePerf Bs ((e (M.simple j) : ↥A) : MulAut ↥Bs)) i hs))
    (Subgroup.inv_mem T hgT)

end CFSG.StandardType

end
