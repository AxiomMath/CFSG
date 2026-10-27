module

public import CFSG.Quasithin.Recognition.Stroth.Un5ModelFacts
public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleNormal

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons
  CFSG.Quasithin.H13.F431.Un CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {V W : Type} {Γ : SimpleGraph V} {Δ : SimpleGraph W}

private theorem exists_ne_ne_of_three_le_encard {X : Type} {s : Set X} (hs : 3 ≤ s.encard)
    (x y : X) : ∃ a ∈ s, a ≠ x ∧ a ≠ y := by
  by_contra h
  have hxy : ∀ a, a ∈ s → a = x ∨ a = y := by
    intro a ha
    by_contra hc
    push Not at hc
    exact h ⟨a, ha, hc.1, hc.2⟩
  have hsub : s ⊆ {x, y} := by
    intro a ha
    rcases hxy a ha with h | h
    · simp [h]
    · simp [h]
  have h1 := Set.encard_le_encard hsub
  have h2 : ({x, y} : Set X).encard ≤ 2 := by
    calc ({x, y} : Set X).encard ≤ ({y} : Set X).encard + 1 := Set.encard_insert_le _ _
      _ = 2 := by simp; norm_num
  have h3 := le_trans hs (le_trans h1 h2)
  norm_num at h3

theorem exists_rootGroup_map [Fintype V] [DecidableRel Γ.Adj] [Fintype W] [DecidableRel Δ.Adj]
    {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]
    {H : Type} [Group H] [MulAction H W] [FaithfulSMul H W] [GraphAction H Δ]
    (hTΓ : IsThick Γ) (hPΔ : IsGenPolygon Δ 4)
    (hTΔ : ∀ v : W, 3 ≤ (Δ.neighborSet v).encard) (hMΔ : MoufangCondition H Δ 4)
    (φ : Γ ≃g Δ) {p : GPath Γ 4} (hp : p.NoBack) {g : D}
    (hg : g ∈ pathRootGroup D Γ p) :
    ∃ h ∈ pathRootGroup H Δ (p.map φ (fun a b h => φ.map_adj_iff.mpr h)),
      ∀ x : V, φ (g • x) = h • φ x := by
  have hthick : 3 ≤ (Γ.neighborSet (p 0)).encard := three_le_encard_of_isThick hTΓ (p 0)
  obtain ⟨y, hy, hy1, -⟩ := exists_ne_ne_of_three_le_encard hthick (p 1) (p 1)
  rw [SimpleGraph.mem_neighborSet] at hy
  set q : GPath Δ 4 := p.map φ (fun a b h => φ.map_adj_iff.mpr h) with hqdef
  have hq : q.NoBack := by
    rw [hqdef]
    exact GPath.NoBack.map_of_injective (f := φ) (fun a b h => φ.map_adj_iff.mpr h)
      φ.toEquiv.injective hp
  have hqr : q.rev.NoBack := hq.rev
  have hqr4 : q.rev 4 = φ (p 0) := by
    rw [GPath.rev_apply _ (by omega)]
    simp [hqdef]
  have hqr3 : q.rev 3 = φ (p 1) := by
    rw [GPath.rev_apply _ (by omega)]
    simp [hqdef]
  have hyadj : Δ.Adj (q.rev 4) (φ y) := by
    rw [hqr4]
    exact φ.map_adj_iff.mpr hy
  have hgp0 : g • (p 0) = p 0 :=
    (mem_pathRootGroup.mp hg) 1 (by norm_num) (by norm_num) (p 0) (p.adj 0 (by norm_num)).symm
  have hgyadj : Δ.Adj (q.rev 4) (φ (g • y)) := by
    rw [hqr4]
    have h1 : Γ.Adj (g • (p 0)) (g • y) := (GraphAction.adj_smul g (p 0) y).mpr hy
    rw [hgp0] at h1
    exact φ.map_adj_iff.mpr h1
  have hyne : φ y ≠ q.rev 3 := by
    rw [hqr3]
    exact fun h => hy1 (φ.toEquiv.injective h)
  have hgyne : φ (g • y) ≠ q.rev 3 := by
    rw [hqr3]
    intro h
    have h1 : g • y = p 1 := φ.toEquiv.injective h
    have hgp1 : g • (p 1) = p 1 :=
      (mem_pathRootGroup.mp hg) 2 (by norm_num) (by norm_num) (p 1) (p.adj 1 (by norm_num)).symm
    have hgp1' : g⁻¹ • (p 1) = p 1 := by
      calc g⁻¹ • (p 1) = g⁻¹ • (g • (p 1)) := by rw [hgp1]
        _ = p 1 := by simp
    have h2 : y = p 1 := by
      have := congrArg (fun z => g⁻¹ • z) h1
      simpa [hgp1'] using this
    exact hy1 h2
  obtain ⟨h, hhfix, hhmap⟩ := hMΔ q.rev hqr (φ y) (φ (g • y)) hyadj hgyadj hyne hgyne
  have hh : h ∈ pathRootGroup H Δ q := by
    rw [← pathRootGroup_rev q]
    exact mem_pathRootGroup.mpr hhfix
  let gperm : Equiv.Perm V := MulAction.toPerm g
  let hperm : Equiv.Perm W := MulAction.toPerm h
  let σ : Equiv.Perm W := φ.toEquiv.symm.trans (gperm.trans φ.toEquiv)
  have hσ_apply : ∀ w, σ w = φ (g • (φ.symm w)) := by
    intro w
    show (gperm.trans φ.toEquiv) (φ.toEquiv.symm w) = φ (g • (φ.symm w))
    rfl
  have hσ_adj : ∀ a b, Δ.Adj (σ a) (σ b) ↔ Δ.Adj a b := by
    intro a b
    rw [hσ_apply, hσ_apply]
    constructor
    · intro hab
      have h1 : Γ.Adj (g • (φ.symm a)) (g • (φ.symm b)) := φ.map_adj_iff.mp hab
      have h2 : Γ.Adj (φ.symm a) (φ.symm b) :=
        (GraphAction.adj_smul g (φ.symm a) (φ.symm b)).mp h1
      exact φ.symm.map_adj_iff.mp h2
    · intro hab
      have h2 : Γ.Adj (φ.symm a) (φ.symm b) := φ.symm.map_adj_iff.mpr hab
      have h1 : Γ.Adj (g • (φ.symm a)) (g • (φ.symm b)) :=
        (GraphAction.adj_smul g (φ.symm a) (φ.symm b)).mpr h2
      exact φ.map_adj_iff.mpr h1
  let ρ : Equiv.Perm W := hperm⁻¹ * σ
  have hρ_apply : ∀ w, ρ w = h⁻¹ • (σ w) := by
    intro w
    show (hperm⁻¹ * σ) w = h⁻¹ • σ w
    rw [Equiv.Perm.mul_apply]
    rfl
  have hρ_adj : ∀ a b, Δ.Adj (ρ a) (ρ b) ↔ Δ.Adj a b := by
    intro a b
    have h1 : Δ.Adj (hperm⁻¹ (σ a)) (hperm⁻¹ (σ b)) ↔ Δ.Adj (σ a) (σ b) := by
      have hGA : Δ.Adj (h⁻¹ • (σ a)) (h⁻¹ • (σ b)) ↔ Δ.Adj (σ a) (σ b) :=
        GraphAction.adj_smul (h⁻¹) (σ a) (σ b)
      simpa [hperm] using hGA
    have h2 : ρ a = hperm⁻¹ (σ a) := rfl
    have h3 : ρ b = hperm⁻¹ (σ b) := rfl
    rw [h2, h3]
    exact h1.trans (hσ_adj a b)
  have hfix : ∀ i, 1 ≤ i → i ≤ 3 → ∀ w, Δ.Adj (q i) w → ρ w = w := by
    intro i hi1 hi3 w hw
    obtain ⟨v, rfl⟩ : ∃ v, φ v = w := ⟨φ.symm w, by simp⟩
    have hvw : Γ.Adj (p i) v := by
      apply φ.map_adj_iff.mp
      rwa [hqdef, GPath.map_apply] at hw
    have hgv : g • v = v := (mem_pathRootGroup.mp hg) i hi1 (by omega) v hvw
    have hσw : σ (φ v) = φ v := by
      rw [hσ_apply, show φ.symm (φ v) = v from φ.toEquiv.symm_apply_apply v, hgv]
    have hqr_mem : h ∈ pathRootGroup H Δ q.rev := by
      rw [pathRootGroup_rev]
      exact hh
    have hrev : q.rev (4 - i) = q i := by
      rw [GPath.rev_apply _ (by omega)]
      congr 1
      omega
    have hhw : h • (φ v) = φ v := by
      exact (mem_pathRootGroup.mp hqr_mem) (4 - i) (by omega) (by omega) (φ v) (by
        rwa [hrev])
    calc ρ (φ v) = h⁻¹ • (σ (φ v)) := hρ_apply _
      _ = h⁻¹ • (φ v) := by rw [hσw]
      _ = h⁻¹ • (h • (φ v)) := by rw [hhw]
      _ = φ v := by simp
  have hfix_rev : ∀ i, 1 ≤ i → i ≤ 3 → ∀ w, Δ.Adj (q.rev i) w → ρ w = w := by
    intro i hi1 hi3 w hw
    have hrev : q.rev i = q (4 - i) := GPath.rev_apply _ (by omega)
    exact hfix (4 - i) (by omega) (by omega) w (by rwa [hrev] at hw)
  have hgw : ρ (φ y) = φ y := by
    have hσy : σ (φ y) = φ (g • y) := by
      rw [hσ_apply, show φ.symm (φ y) = y from φ.toEquiv.symm_apply_apply y]
    calc ρ (φ y) = h⁻¹ • (σ (φ y)) := hρ_apply _
      _ = h⁻¹ • (φ (g • y)) := by rw [hσy]
      _ = h⁻¹ • (h • (φ y)) := by rw [← hhmap]
      _ = φ y := by simp
  have hρ : ρ = 1 :=
    IsGenPolygon.eq_one_of_fix_root hPΔ (by norm_num) hTΔ q.rev hqr hρ_adj
      hfix_rev hyadj hyne hgw
  have hσeq : σ = hperm := by
    have h1 : hperm * ρ = σ := by
      show hperm * (hperm⁻¹ * σ) = σ
      group
    rw [hρ, mul_one] at h1
    exact h1.symm
  refine ⟨h, hh, fun x => ?_⟩
  calc φ (g • x) = σ (φ x) := by
        rw [hσ_apply, show φ.symm (φ x) = x from φ.toEquiv.symm_apply_apply x]
    _ = hperm (φ x) := by rw [hσeq]
    _ = h • φ x := rfl

section Kappa

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [Fact ((ζ : F) ≠ 0)]
  [Fintype V] [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

def un5KappaSubgroup (φ : Γ ≃g (un5System hF ζ).graph) : Subgroup D where
  carrier := {g | ∃ h : Un5Group k F,
    ∀ x : V, φ.toEquiv (g • x) = (un5System hF ζ).action h (φ.toEquiv x)}
  one_mem' := ⟨1, fun x => by simp⟩
  mul_mem' := by
    rintro g g' ⟨h, hh⟩ ⟨h', hh'⟩
    refine ⟨h * h', fun x => ?_⟩
    rw [mul_smul, hh, hh', map_mul]
    rfl
  inv_mem' := by
    rintro g ⟨h, hh⟩
    refine ⟨h⁻¹, fun x => ?_⟩
    have h1 := hh (g⁻¹ • x)
    rw [smul_inv_smul] at h1
    calc φ.toEquiv (g⁻¹ • x) = (un5System hF ζ).action h⁻¹
          ((un5System hF ζ).action h (φ.toEquiv (g⁻¹ • x))) := by rw [map_inv]; simp
      _ = (un5System hF ζ).action h⁻¹ (φ.toEquiv x) := by rw [h1]

theorem un5KappaSubgroup_unique (φ : Γ ≃g (un5System hF ζ).graph) {g : D}
    {h h' : Un5Group k F}
    (hh : ∀ x : V, φ.toEquiv (g • x) = (un5System hF ζ).action h (φ.toEquiv x))
    (hh' : ∀ x : V, φ.toEquiv (g • x) = (un5System hF ζ).action h' (φ.toEquiv x)) : h = h' := by
  refine (un5System hF ζ).action_injective ?_
  refine Equiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := φ.toEquiv.surjective y
  rw [← hh x, ← hh' x]

theorem pathRootGroup_le_un5KappaSubgroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph) {p : GPath Γ 4}
    (hp : p.NoBack) : pathRootGroup D Γ p ≤ un5KappaSubgroup hF ζ φ := by
  intro g hg
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  have hgen : IsGenPolygon (un5System hF ζ).graph 4 :=
    CFSG.Quasithin.H13.F431.BN.isGenPolygon (un5System hF ζ)
  have hthick : ∀ v : (un5System hF ζ).Vertex,
      3 ≤ ((un5System hF ζ).graph.neighborSet v).encard :=
    three_le_encard_of_isThick (un5System_isThick hF ζ)
  have hmou := rankTwoSystem_moufang (un5System hF ζ)
  obtain ⟨h, -, hh⟩ := exists_rootGroup_map hT hgen hthick hmou φ hp hg
  exact ⟨h, fun x => by rw [show φ.toEquiv (g • x) = φ (g • x) from rfl, hh x]; rfl⟩

theorem littleGroup_le_un5KappaSubgroup (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph) :
    littleGroup D Γ 4 ≤ un5KappaSubgroup hF ζ φ := by
  rw [littleGroup]
  exact iSup_le fun p => iSup_le fun hp =>
    pathRootGroup_le_un5KappaSubgroup hF ζ hP hT hM φ hp

noncomputable def un5KappaFun (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph)
    (g : ↥(littleGroup D Γ 4)) : Un5Group k F :=
  Classical.choose (littleGroup_le_un5KappaSubgroup hF ζ hP hT hM φ g.2)

theorem un5KappaFun_spec (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph)
    (g : ↥(littleGroup D Γ 4)) (x : V) :
    φ.toEquiv ((g : D) • x) =
      (un5System hF ζ).action (un5KappaFun hF ζ hP hT hM φ g) (φ.toEquiv x) :=
  Classical.choose_spec (littleGroup_le_un5KappaSubgroup hF ζ hP hT hM φ g.2) x

noncomputable def un5KappaHom (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph) :
    ↥(littleGroup D Γ 4) →* Un5Group k F where
  toFun := un5KappaFun hF ζ hP hT hM φ
  map_one' := un5KappaSubgroup_unique hF ζ φ
    (un5KappaFun_spec hF ζ hP hT hM φ 1) (fun x => by simp)
  map_mul' g g' := un5KappaSubgroup_unique hF ζ φ
    (un5KappaFun_spec hF ζ hP hT hM φ (g * g')) (fun x => by
      rw [Subgroup.coe_mul, mul_smul, un5KappaFun_spec hF ζ hP hT hM φ g,
        un5KappaFun_spec hF ζ hP hT hM φ g', map_mul]
      rfl)

theorem un5KappaHom_injective (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ 4) (φ : Γ ≃g (un5System hF ζ).graph) :
    Function.Injective (un5KappaHom hF ζ hP hT hM φ) := by
  intro g g' hgg'
  have h1 : (g : D) = g' := by
    refine FaithfulSMul.eq_of_smul_eq_smul (α := V) (m₁ := (g : D)) (m₂ := (g' : D))
      (fun x => ?_)
    exact φ.toEquiv.injective ((un5KappaFun_spec hF ζ hP hT hM φ g x).trans
      ((congrArg (fun h => (un5System hF ζ).action h (φ.toEquiv x)) hgg').trans
        (un5KappaFun_spec hF ζ hP hT hM φ g' x).symm))
  exact Subtype.ext h1

end Kappa

section BasePath

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [Fact ((ζ : F) ≠ 0)]

private theorem basePath_getD_apply (m₁ m₂ : (un5System hF ζ).N) (first : Bool) {i : ℕ}
    (hi : i ≤ 4) :
    ((un5System hF ζ).basePath m₁ m₂ first).getD i ((un5System hF ζ).vv m₁ m₂ first 4) =
      (un5System hF ζ).vv m₁ m₂ first i := by
  rw [List.getD_eq_getElem _ _ (by rw [RankTwoSystem.basePath_length]; omega)]
  simp [RankTwoSystem.basePath, List.getElem_map, List.getElem_range]

private theorem basePath_getD_default (m₁ m₂ : (un5System hF ζ).N) (first : Bool) {i : ℕ}
    (hi : 5 ≤ i) :
    ((un5System hF ζ).basePath m₁ m₂ first).getD i ((un5System hF ζ).vv m₁ m₂ first 4) =
      (un5System hF ζ).vv m₁ m₂ first 4 := by
  apply List.getD_eq_default
  rw [RankTwoSystem.basePath_length]
  omega

private theorem mem_interiorVertices_basePath (m₁ m₂ : (un5System hF ζ).N) (first : Bool)
    {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    (un5System hF ζ).vv m₁ m₂ first i ∈
      interiorVertices ((un5System hF ζ).basePath m₁ m₂ first) := by
  rw [RankTwoSystem.basePath]
  have h := CFSG.GH74.BNPair.getElem_mem_interiorVertices
    (l := (List.range 5).map ((un5System hF ζ).vv m₁ m₂ first)) (i := i) hi1 (by simp; omega)
  simpa [List.getElem_map] using h

private noncomputable def baseGPath (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) :
    GPath (un5System hF ζ).graph 4 where
  toFun i := ((un5System hF ζ).basePath m₁ m₂ first).getD i
    ((un5System hF ζ).vv m₁ m₂ first 4)
  adj i hi := by
    rw [basePath_getD_apply hF ζ m₁ m₂ first (by omega : i ≤ 4),
      basePath_getD_apply hF ζ m₁ m₂ first (by omega : i + 1 ≤ 4)]
    exact (un5System hF ζ).vv_adj m₁ m₂ hm₁ hm₂ first i
  tail i hi := by
    rcases Nat.lt_or_ge i 5 with h | h
    · have hi4 : i = 4 := by omega
      subst hi4
      rw [basePath_getD_apply hF ζ m₁ m₂ first (by omega : 4 ≤ 4)]
    · rw [basePath_getD_default hF ζ m₁ m₂ first h,
        basePath_getD_apply hF ζ m₁ m₂ first (by omega : 4 ≤ 4)]

@[simp] private theorem baseGPath_apply (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) {i : ℕ}
    (hi : i ≤ 4) : baseGPath hF ζ m₁ m₂ hm₁ hm₂ first i = (un5System hF ζ).vv m₁ m₂ first i :=
  basePath_getD_apply hF ζ m₁ m₂ first hi

private theorem pathRootGroup_baseGPath (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) :
    letI := rtsMulAction (un5System hF ζ)
    pathRootGroup (Un5Group k F) (un5System hF ζ).graph (baseGPath hF ζ m₁ m₂ hm₁ hm₂ first) =
      (un5System hF ζ).root (jIdx 4 first 0) := by
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  ext x
  rw [mem_pathRootGroup]
  constructor
  · intro hx
    refine (rankTwoSystem_rootGroup (un5System hF ζ) m₁ m₂ hm₁ hm₂ first x).mp ?_
    intro v hv w hw
    obtain ⟨t, ht, rfl⟩ := CFSG.GH74.BNPair.mem_interior_map_range
      ((un5System hF ζ).vv m₁ m₂ first) 3 (by
        rw [RankTwoSystem.basePath] at hv
        simpa [show 3 + 2 = 5 by norm_num] using hv)
    exact hx (t + 1) (by omega) (by omega) w (by
      rwa [baseGPath_apply hF ζ m₁ m₂ hm₁ hm₂ first (by omega : t + 1 ≤ 4)])
  · intro hx i hi1 hi3 w hw
    have hfix := (rankTwoSystem_rootGroup (un5System hF ζ) m₁ m₂ hm₁ hm₂ first x).mpr hx
    have hmem := mem_interiorVertices_basePath hF ζ m₁ m₂ first hi1 hi3
    have hw' : (un5System hF ζ).graph.Adj ((un5System hF ζ).vv m₁ m₂ first i) w := by
      rwa [baseGPath_apply hF ζ m₁ m₂ hm₁ hm₂ first (by omega : i ≤ 4)] at hw
    change (un5System hF ζ).action x w = w
    exact hfix ((un5System hF ζ).vv m₁ m₂ first i) hmem w hw'

end BasePath

section Range

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [Fact ((ζ : F) ≠ 0)]
  [Fintype V] [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]
  (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition D Γ 4)
  (φ : Γ ≃g (un5System hF ζ).graph)

theorem pathRootGroup_un5System_le_range_un5KappaHom
    (q : GPath (un5System hF ζ).graph 4) (hq : q.NoBack) :
    letI := rtsMulAction (un5System hF ζ)
    pathRootGroup (Un5Group k F) (un5System hF ζ).graph q ≤
      (un5KappaHom hF ζ hP hT hM φ).range := by
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  intro u hu
  have hgenΓ : IsGenPolygon Γ 4 :=
    isGenPolygon_of_isGeneralizedPolygon (by norm_num) hP hT
  have hthickΓ : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard :=
    three_le_encard_of_isThick hT
  have hthickM : ∀ v : (un5System hF ζ).Vertex,
      3 ≤ ((un5System hF ζ).graph.neighborSet v).encard :=
    three_le_encard_of_isThick (un5System_isThick hF ζ)
  have hmouM := rankTwoSystem_moufang (un5System hF ζ)
  obtain ⟨h, hhU, hh⟩ := exists_rootGroup_map (Γ := (un5System hF ζ).graph) (Δ := Γ)
    (D := Un5Group k F) (H := D) (un5System_isThick hF ζ) hgenΓ hthickΓ hM φ.symm hq hu
  have hspec : ∀ x : V,
      φ.toEquiv (h • x) = (un5System hF ζ).action u (φ.toEquiv x) := by
    intro x
    have h1 := hh (φ.toEquiv x)
    rw [show φ.symm (φ.toEquiv x) = x from φ.toEquiv.symm_apply_apply x] at h1
    calc φ.toEquiv (h • x) = φ.toEquiv (φ.symm (u • φ.toEquiv x)) := by rw [h1]
      _ = u • φ.toEquiv x := by simp
      _ = (un5System hF ζ).action u (φ.toEquiv x) := rfl
  have hmemL : h ∈ littleGroup D Γ 4 :=
    pathRootGroup_le_littleGroup
      (GPath.NoBack.map_of_injective (f := φ.symm)
        (fun a b h => φ.symm.map_adj_iff.mpr h) φ.symm.toEquiv.injective hq) hhU
  refine ⟨⟨h, hmemL⟩, ?_⟩
  exact un5KappaSubgroup_unique hF ζ φ (un5KappaFun_spec hF ζ hP hT hM φ ⟨h, hmemL⟩) hspec

end Range


section Surj

variable {k : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] [Fact (Nat.Prime 2)]
  (hF : Nat.card F = (2 ^ k) ^ 2) (ζ : traceZero (unitaryInvolution F 2 k))
  [Fact ((ζ : F) ≠ 0)]
  [Fintype V] [DecidableRel Γ.Adj]
  {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]
  (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition D Γ 4)
  (φ : Γ ≃g (un5System hF ζ).graph)

private theorem baseGPath_noBack (m₁ m₂ : (un5System hF ζ).N)
    (hm₁ : (m₁ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₁)
    (hm₂ : (m₂ : (un5System hF ζ).Weyl) = (un5System hF ζ).w₂) (first : Bool) :
    (baseGPath hF ζ m₁ m₂ hm₁ hm₂ first).NoBack := by
  intro i hi
  rw [baseGPath_apply hF ζ m₁ m₂ hm₁ hm₂ first (by omega : i ≤ 4),
    baseGPath_apply hF ζ m₁ m₂ hm₁ hm₂ first (by omega : i + 2 ≤ 4)]
  exact (un5System hF ζ).vv_ne m₁ m₂ hm₁ hm₂ first i

private theorem root_le_range (i : ℤ) (hi : IsRoot 4 i) :
    letI := rtsMulAction (un5System hF ζ)
    (un5System hF ζ).root i ≤ (un5KappaHom hF ζ hP hT hM φ).range := by
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective (un5System hF ζ).w₂
  have hq1 : (un5System hF ζ).root 1 =
      pathRootGroup (Un5Group k F) (un5System hF ζ).graph
        (baseGPath hF ζ m₁ m₂ hm₁ hm₂ false) := by
    rw [pathRootGroup_baseGPath hF ζ m₁ m₂ hm₁ hm₂ false]
    simp [jIdx, stType]
  have hqn : (un5System hF ζ).root (4 : ℤ) =
      pathRootGroup (Un5Group k F) (un5System hF ζ).graph
        (baseGPath hF ζ m₁ m₂ hm₁ hm₂ true) := by
    rw [pathRootGroup_baseGPath hF ζ m₁ m₂ hm₁ hm₂ true]
    simp [jIdx, stType]
  have hnb1 := baseGPath_noBack hF ζ m₁ m₂ hm₁ hm₂ false
  have hnbn := baseGPath_noBack hF ζ m₁ m₂ hm₁ hm₂ true
  obtain ⟨m, hm⟩ := (un5System hF ζ).exists_conj_root_one_or_n hi
  rcases hm with hm | hm
  · rw [← hm]
    intro x hx
    have hx' : x ∈ ((un5System hF ζ).root 1).map
        (MulAut.conj (((m : (un5System hF ζ).N) : Un5Group k F)⁻¹)).toMonoidHom := hx
    rw [hq1] at hx'
    rw [pathRootGroup_map_conj] at hx'
    exact pathRootGroup_un5System_le_range_un5KappaHom hF ζ hP hT hM φ
      ((((m : (un5System hF ζ).N) : Un5Group k F))⁻¹ •
        baseGPath hF ζ m₁ m₂ hm₁ hm₂ false) (GPath.noBack_smul_iff.mpr hnb1) hx'
  · rw [← hm]
    intro x hx
    have hx' : x ∈ ((un5System hF ζ).root (4 : ℤ)).map
        (MulAut.conj (((m : (un5System hF ζ).N) : Un5Group k F)⁻¹)).toMonoidHom := hx
    rw [hqn] at hx'
    rw [pathRootGroup_map_conj] at hx'
    exact pathRootGroup_un5System_le_range_un5KappaHom hF ζ hP hT hM φ
      ((((m : (un5System hF ζ).N) : Un5Group k F))⁻¹ •
        baseGPath hF ζ m₁ m₂ hm₁ hm₂ true) (GPath.noBack_smul_iff.mpr hnbn) hx'

theorem un5System_xplus_le_range_un5KappaHom :
    letI := rtsMulAction (un5System hF ζ)
    (un5System hF ζ).Xplus ≤ (un5KappaHom hF ζ hP hT hM φ).range := by
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  rw [RankTwoSystem.Xplus]
  refine (Subgroup.closure_le (un5KappaHom hF ζ hP hT hM φ).range).mpr ?_
  rintro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨i, hx⟩ := hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨hi, hxi⟩ := hx
  exact root_le_range hF ζ hP hT hM φ i hi hxi

theorem un5KappaHom_surjective : Function.Surjective (un5KappaHom hF ζ hP hT hM φ) := by
  intro u
  letI := rtsMulAction (un5System hF ζ)
  haveI := rtsGraphAction (un5System hF ζ)
  haveI := un5System_faithfulSMul hF ζ
  have htop : (un5System hF ζ).Xplus = ⊤ := un5System_xplus_eq_top hF ζ
  have hle : (un5System hF ζ).Xplus ≤ (un5KappaHom hF ζ hP hT hM φ).range :=
    un5System_xplus_le_range_un5KappaHom hF ζ hP hT hM φ
  have hrange : (un5KappaHom hF ζ hP hT hM φ).range = ⊤ := top_unique (by rw [← htop]; exact hle)
  exact MonoidHom.mem_range.mp (by rw [hrange]; exact Subgroup.mem_top u)

noncomputable def un5Kappa : ↥(littleGroup D Γ 4) ≃* Un5Group k F :=
  MulEquiv.ofBijective (un5KappaHom hF ζ hP hT hM φ)
    ⟨un5KappaHom_injective hF ζ hP hT hM φ, un5KappaHom_surjective hF ζ hP hT hM φ⟩

theorem un5Kappa_equivariant (g : ↥(littleGroup D Γ 4)) (v : V) :
    φ.toEquiv ((g : D) • v) =
      (un5System hF ζ).action (un5Kappa hF ζ hP hT hM φ g) (φ.toEquiv v) :=
  un5KappaFun_spec hF ζ hP hT hM φ g v

end Surj

end CFSG.Quasithin.Stroth