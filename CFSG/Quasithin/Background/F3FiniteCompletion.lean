module

public import CFSG.Quasithin.Background.F3HatTree
public import CFSG.Geometry.Trees.FreeAction

public section

namespace CFSG.Quasithin.RankTwoAmalgam

universe u w

open CFSG.Quasithin

variable {α : RankTwoAmalgam.{u}}

private abbrev Gsub (α : RankTwoAmalgam.{u}) : Subgroup α.Ghat := α.Ghat1 ⊔ α.Ghat2

private noncomputable def thetaSub {Y : Type w} [Group Y] (c : α.Completion Y) :
    ↥(Gsub α) →* Y :=
  c.theta.comp (Gsub α).subtype

private theorem thetaSub_apply {Y : Type w} [Group Y] (c : α.Completion Y) (g : ↥(Gsub α)) :
    thetaSub c g = c.theta (g : α.Ghat) := rfl

private theorem injective_α1 {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Function.Injective α.α1 := by
  intro x y hxy
  apply hc₀.2.1
  rw [← c₀.comm1 x, ← c₀.comm1 y, hxy]

private theorem injective_α2 {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Function.Injective α.α2 := by
  intro x y hxy
  have h : c₀.φ12 x = c₀.φ12 y := by rw [← c₀.comm2 x, ← c₀.comm2 y, hxy]
  exact hc₀.2.1 h

private theorem graphHat_isTree_of_faithful {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : α.graphHat.IsTree :=
  graphHat_isTree α (injective_α1 hc₀) (injective_α2 hc₀)

private theorem finite_G1 {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Finite α.G1 :=
  Finite.of_injective c₀.φ1 hc₀.1

private theorem finite_G2 {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Finite α.G2 :=
  Finite.of_injective c₀.φ2 hc₀.2.2

private theorem finite_Ghat1 {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Finite ↥α.Ghat1 := by
  haveI := finite_G1 (α := α) hc₀
  exact Finite.of_surjective
    (fun g : α.G1 => (⟨Amalgam.ξ α.toAmalgam RankTwoIndex.one g, ⟨g, rfl⟩⟩ : ↥α.Ghat1))
    (by rintro ⟨y, g, rfl⟩; exact ⟨g, rfl⟩)

private theorem finite_Ghat2 {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Finite ↥α.Ghat2 := by
  haveI := finite_G2 (α := α) hc₀
  exact Finite.of_surjective
    (fun g : α.G2 => (⟨Amalgam.ξ α.toAmalgam RankTwoIndex.two g, ⟨g, rfl⟩⟩ : ↥α.Ghat2))
    (by rintro ⟨y, g, rfl⟩; exact ⟨g, rfl⟩)

private def embedGhat1 (g : ↥α.Ghat1) : ↥(Gsub α) :=
  ⟨(g : α.Ghat), Subgroup.mem_sup_left g.2⟩

private def embedGhat2 (g : ↥α.Ghat2) : ↥(Gsub α) :=
  ⟨(g : α.Ghat), Subgroup.mem_sup_right g.2⟩

private theorem finite_nbrs_γ₀ {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) :
    (α.graphHat.neighborSet
      (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)).Finite := by
  haveI := finite_Ghat1 (α := α) hc₀
  let f : ↥α.Ghat1 → α.Γhat := fun g =>
    (⟨(g : α.Ghat), Subgroup.mem_sup_left g.2⟩ : ↥(α.Ghat1 ⊔ α.Ghat2)) •
      CosetGeom.γ₁ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2
  have hfin : (Set.range f).Finite := Set.finite_range f
  refine hfin.subset ?_
  intro v hv
  cases v with
  | inl x =>
    simp only [SimpleGraph.mem_neighborSet] at hv
    exact absurd hv (CosetGeom.not_adj_inl_inl (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2))
  | inr y =>
    obtain ⟨g, hg1, hgy⟩ := CosetGeom.adj_γ₀_inr_iff.mp hv
    refine ⟨⟨(g : α.Ghat), hg1⟩, ?_⟩
    show (⟨(g : α.Ghat), Subgroup.mem_sup_left hg1⟩ : ↥(α.Ghat1 ⊔ α.Ghat2)) •
      CosetGeom.γ₁ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2 = Sum.inr y
    rw [CosetGeom.smul_γ₁]
    exact congrArg Sum.inr hgy

private theorem finite_nbrs_γ₁ {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) :
    (α.graphHat.neighborSet
      (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)).Finite := by
  haveI := finite_Ghat2 (α := α) hc₀
  let f : ↥α.Ghat2 → α.Γhat := fun g =>
    (⟨(g : α.Ghat), Subgroup.mem_sup_right g.2⟩ : ↥(α.Ghat1 ⊔ α.Ghat2)) •
      CosetGeom.γ₀ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2
  have hfin : (Set.range f).Finite := Set.finite_range f
  refine hfin.subset ?_
  intro v hv
  cases v with
  | inl x =>
    obtain ⟨g, hg2, hgy⟩ := CosetGeom.adj_γ₁_inl_iff.mp hv
    refine ⟨⟨(g : α.Ghat), hg2⟩, ?_⟩
    show (⟨(g : α.Ghat), Subgroup.mem_sup_right hg2⟩ : ↥(α.Ghat1 ⊔ α.Ghat2)) •
      CosetGeom.γ₀ (α.Ghat1 ⊔ α.Ghat2) α.Ghat1 α.Ghat2 = Sum.inl x
    rw [CosetGeom.smul_γ₀]
    exact congrArg Sum.inl hgy
  | inr y =>
    simp only [SimpleGraph.mem_neighborSet] at hv
    exact absurd hv (CosetGeom.not_adj_inr_inr (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2))

private theorem neighborSet_smul {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}
    (g : ↥G₀) (v : CosetGeom G₀ G₁ G₂) :
    (CosetGeom.graph G₀ G₁ G₂).neighborSet (g • v) =
      (fun w => g • w) '' (CosetGeom.graph G₀ G₁ G₂).neighborSet v := by
  ext w
  constructor
  · intro hw
    refine ⟨g⁻¹ • w, ?_, ?_⟩
    · exact (CosetGeom.smul_adj (G₀ := G₀) g
        (u := v) (v := g⁻¹ • w)).mp (by simpa using hw)
    · simp
  · rintro ⟨w, hw, rfl⟩
    exact (CosetGeom.smul_adj (G₀ := G₀) g (u := v) (v := w)).mpr hw

private theorem finite_nbrs {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (u : α.Γhat) : (α.graphHat.neighborSet u).Finite := by
  rcases u with x | y
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) (γ := Sum.inl x) rfl
    rw [hg, neighborSet_smul]
    exact Set.Finite.image _ (finite_nbrs_γ₀ (α := α) hc₀)
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) (γ := Sum.inr y) rfl
    rw [hg, neighborSet_smul]
    exact Set.Finite.image _ (finite_nbrs_γ₁ (α := α) hc₀)

private theorem finite_ball {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (x : α.Γhat) (k : ℕ) :
    {v : α.Γhat | α.graphHat.dist x v ≤ k}.Finite := by
  have hconn : α.graphHat.Connected :=
    CosetGeom.connected (G₀ := Gsub α) (G₁ := α.Ghat1) (G₂ := α.Ghat2) rfl
  induction k with
  | zero =>
    refine (Set.finite_singleton x).subset ?_
    intro v hv
    have hd : α.graphHat.dist x v = 0 := Nat.le_zero.mp hv
    exact (hconn.dist_eq_zero_iff.mp hd).symm
  | succ k ih =>
    refine (ih.union (ih.biUnion fun u _ => finite_nbrs (α := α) hc₀ u)).subset ?_
    intro v hv
    by_cases hle : α.graphHat.dist x v ≤ k
    · exact Or.inl hle
    · right
      have hd : α.graphHat.dist x v = k + 1 :=
        le_antisymm hv (Nat.succ_le_of_lt (Nat.lt_of_not_le hle))
      obtain ⟨p, hp0, hpv, -⟩ := GPath.exists_geodesic' hconn x v hd
      have hgeo : α.graphHat.dist (p 0) (p (k + 1)) = k + 1 := by rw [hp0, hpv]; exact hd
      have hk : α.graphHat.dist x (p k) = k := by
        have := GPath.dist_prefix hconn p hgeo (show k ≤ k + 1 by omega)
        rwa [hp0] at this
      refine Set.mem_iUnion₂.mpr ⟨p k, le_of_eq hk, ?_⟩
      show α.graphHat.Adj (p k) v
      have := p.adj k (by omega)
      rwa [hpv] at this

private theorem free_action_vertices {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (f : ↥(thetaSub c₀).ker) (v : α.Γhat)
    (h : (f : Gsub α) • v = v) : f = 1 := by
  have hθ : c₀.theta0 hc₀ (f : Gsub α) = 1 := by
    refine Subtype.ext ?_
    have hf : thetaSub c₀ (f : Gsub α) = 1 := MonoidHom.mem_ker.mp f.2
    simpa [thetaSub_apply] using congrArg id hf
  have h1 : (f : Gsub α) = 1 := (c₀.stabIso hc₀ v).inj (f : Gsub α) h hθ
  exact Subtype.ext h1

private theorem free_action_eq_one {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) {f : ↥(thetaSub c₀).ker} {v : α.Γhat}
    (h : (f : Gsub α) • v = v) : f = 1 :=
  free_action_vertices hc₀ f v h

private theorem no_inversions {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (f : ↥(thetaSub c₀).ker) {a b : α.Γhat}
    (h : α.graphHat.Adj a b) (hfa : (f : Gsub α) • a = b) : (f : Gsub α) • b ≠ a := by
  intro hfb
  have hne := CosetGeom.vtype_ne_of_adj h
  rw [← hfa, CosetGeom.vtype_smul] at hne
  exact hne rfl

private theorem finite_orbits {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) :
    Finite (MulAction.orbitRel.Quotient ↥(thetaSub c₀).ker α.Γhat) := by
  haveI hF : (thetaSub c₀).ker.FiniteIndex := by
    haveI : Finite ↥(thetaSub c₀).range := inferInstance
    exact Subgroup.finiteIndex_ker (thetaSub c₀)
  haveI : Fintype (↥(Gsub α) ⧸ (thetaSub c₀).ker) :=
    (thetaSub c₀).ker.fintypeQuotientOfFiniteIndex
  haveI : Finite (↥(Gsub α) ⧸ (thetaSub c₀).ker) :=
    Fintype.finite (inferInstance : Fintype (↥(Gsub α) ⧸ (thetaSub c₀).ker))
  let base : Bool → α.Γhat := fun b =>
    if b then CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2
    else CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2
  let f : (↥(Gsub α) ⧸ (thetaSub c₀).ker) × Bool →
      MulAction.orbitRel.Quotient ↥(thetaSub c₀).ker α.Γhat :=
    fun p => Quotient.mk'' ((Quotient.out p.1 : ↥(Gsub α)) • base p.2)
  refine Finite.of_surjective f ?_
  rintro ⟨v⟩
  by_cases hv : CosetGeom.vtype v = false
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) hv
    refine ⟨(QuotientGroup.mk g, false), ?_⟩
    show Quotient.mk'' ((Quotient.out (QuotientGroup.mk (s := (thetaSub c₀).ker) g) :
      ↥(Gsub α)) • base false) = Quotient.mk'' v
    set t : ↥(Gsub α) := Quotient.out (QuotientGroup.mk (s := (thetaSub c₀).ker) g)
    have hout : t⁻¹ * g ∈ (thetaSub c₀).ker := by
      have hq : QuotientGroup.mk t = QuotientGroup.mk (s := (thetaSub c₀).ker) g :=
        Quotient.out_eq' (QuotientGroup.mk (s := (thetaSub c₀).ker) g)
      exact QuotientGroup.eq.mp hq
    let n : ↥(thetaSub c₀).ker := ⟨t⁻¹ * g, hout⟩
    let fker : ↥(thetaSub c₀).ker := ⟨t * (n : ↥(Gsub α))⁻¹ * t⁻¹,
      Subgroup.Normal.conj_mem (H := (thetaSub c₀).ker) inferInstance (n : ↥(Gsub α))⁻¹
        ((thetaSub c₀).ker.inv_mem n.2) t⟩
    refine Quotient.sound ⟨fker, ?_⟩
    rw [hg]
    change (fker : ↥(Gsub α)) •
      (g • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) =
      t • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2
    have hfval : (fker : ↥(Gsub α)) = t * (n : ↥(Gsub α))⁻¹ * t⁻¹ := rfl
    have hnval : (n : ↥(Gsub α)) = t⁻¹ * g := rfl
    rw [← mul_smul]
    congr 1
    rw [hfval, hnval]
    group
  · have hv' : CosetGeom.vtype v = true := by
      cases h : CosetGeom.vtype v <;> simp_all
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) hv'
    refine ⟨(QuotientGroup.mk g, true), ?_⟩
    show Quotient.mk'' ((Quotient.out (QuotientGroup.mk (s := (thetaSub c₀).ker) g) :
      ↥(Gsub α)) • base true) = Quotient.mk'' v
    set t : ↥(Gsub α) := Quotient.out (QuotientGroup.mk (s := (thetaSub c₀).ker) g)
    have hout : t⁻¹ * g ∈ (thetaSub c₀).ker := by
      have hq : QuotientGroup.mk t = QuotientGroup.mk (s := (thetaSub c₀).ker) g :=
        Quotient.out_eq' (QuotientGroup.mk (s := (thetaSub c₀).ker) g)
      exact QuotientGroup.eq.mp hq
    let n : ↥(thetaSub c₀).ker := ⟨t⁻¹ * g, hout⟩
    let fker : ↥(thetaSub c₀).ker := ⟨t * (n : ↥(Gsub α))⁻¹ * t⁻¹,
      Subgroup.Normal.conj_mem (H := (thetaSub c₀).ker) inferInstance (n : ↥(Gsub α))⁻¹
        ((thetaSub c₀).ker.inv_mem n.2) t⟩
    refine Quotient.sound ⟨fker, ?_⟩
    rw [hg]
    change (fker : ↥(Gsub α)) •
      (g • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) =
      t • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2
    have hfval : (fker : ↥(Gsub α)) = t * (n : ↥(Gsub α))⁻¹ * t⁻¹ := rfl
    have hnval : (n : ↥(Gsub α)) = t⁻¹ * g := rfl
    rw [← mul_smul]
    congr 1
    rw [hfval, hnval]
    group

private theorem residuallyFinite_ker {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) : Group.ResiduallyFinite ↥(thetaSub c₀).ker := by
  haveI := finite_orbits (α := α) hc₀
  exact CFSG.Geometry.Trees.residuallyFinite_of_free_action
    (F := ↥(thetaSub c₀).ker) (V := α.Γhat) (T := α.graphHat)
    (graphHat_isTree_of_faithful hc₀)
    (fun f a b => CosetGeom.smul_adj (G₀ := Gsub α) (f : Gsub α) (u := a) (v := b))
    (fun f v h => free_action_vertices hc₀ f v h)
    (fun f a b h hfa => no_inversions hc₀ f h hfa)

private def badSet {Y : Type w} [Group Y] (c₀ : α.Completion Y) (m : ℕ) : Set ↥(Gsub α) :=
  {g | g ∈ (thetaSub c₀).ker ∧ g ≠ 1 ∧
    (α.graphHat.dist (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)
        (g • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) ≤ m ∨
      α.graphHat.dist (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)
        (g • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) ≤ m)}

private theorem badSet_finite {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (m : ℕ) : (badSet (α := α) c₀ m).Finite := by
  have h0 : {g : ↥(Gsub α) | g ∈ (thetaSub c₀).ker ∧
      α.graphHat.dist (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)
        (g • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) ≤ m}.Finite := by
    refine Set.Finite.of_finite_image (f := fun g : ↥(Gsub α) =>
      g • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) ?_ ?_
    · refine (finite_ball (α := α) hc₀
        (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) m).subset ?_
      rintro _ ⟨g, hg, rfl⟩
      exact hg.2
    · intro g hg g' hg' heq
      have hmem : g⁻¹ * g' ∈ (thetaSub c₀).ker :=
        (thetaSub c₀).ker.mul_mem ((thetaSub c₀).ker.inv_mem hg.1) hg'.1
      have hfix : ((⟨g⁻¹ * g', hmem⟩ : ↥(thetaSub c₀).ker) : ↥(Gsub α)) •
          CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 =
          CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 := by
        have hco : ((⟨g⁻¹ * g', hmem⟩ : ↥(thetaSub c₀).ker) : ↥(Gsub α)) = g⁻¹ * g' :=
          rfl
        rw [hco]
        have hcancel := congrArg (fun x => (g⁻¹ : ↥(Gsub α)) • x) heq
        calc (g⁻¹ * g') • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2
            = g⁻¹ • (g' • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) :=
              mul_smul g⁻¹ g' (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)
          _ = g⁻¹ • (g • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) := hcancel.symm
          _ = (g⁻¹ * g) • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 :=
              (mul_smul g⁻¹ g (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)).symm
          _ = CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 := by
              rw [inv_mul_cancel, one_smul]
      have hone := free_action_vertices hc₀ ⟨g⁻¹ * g', hmem⟩ _ hfix
      have h1 : g⁻¹ * g' = 1 := congrArg Subtype.val hone
      exact inv_mul_eq_one.mp h1
  have h1 : {g : ↥(Gsub α) | g ∈ (thetaSub c₀).ker ∧
      α.graphHat.dist (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)
        (g • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) ≤ m}.Finite := by
    refine Set.Finite.of_finite_image (f := fun g : ↥(Gsub α) =>
      g • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) ?_ ?_
    · refine (finite_ball (α := α) hc₀
        (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) m).subset ?_
      rintro _ ⟨g, hg, rfl⟩
      exact hg.2
    · intro g hg g' hg' heq
      have hmem : g⁻¹ * g' ∈ (thetaSub c₀).ker :=
        (thetaSub c₀).ker.mul_mem ((thetaSub c₀).ker.inv_mem hg.1) hg'.1
      have hfix : ((⟨g⁻¹ * g', hmem⟩ : ↥(thetaSub c₀).ker) : ↥(Gsub α)) •
          CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 =
          CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 := by
        have hco : ((⟨g⁻¹ * g', hmem⟩ : ↥(thetaSub c₀).ker) : ↥(Gsub α)) = g⁻¹ * g' :=
          rfl
        rw [hco]
        have hcancel := congrArg (fun x => (g⁻¹ : ↥(Gsub α)) • x) heq
        calc (g⁻¹ * g') • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2
            = g⁻¹ • (g' • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) :=
              mul_smul g⁻¹ g' (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)
          _ = g⁻¹ • (g • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) := hcancel.symm
          _ = (g⁻¹ * g) • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 :=
              (mul_smul g⁻¹ g (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)).symm
          _ = CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 := by
              rw [inv_mul_cancel, one_smul]
      have hone := free_action_vertices hc₀ ⟨g⁻¹ * g', hmem⟩ _ hfix
      have h1 : g⁻¹ * g' = 1 := congrArg Subtype.val hone
      exact inv_mul_eq_one.mp h1
  refine (h0.union h1).subset ?_
  rintro g ⟨hg, -, hd | hd⟩
  · exact Or.inl ⟨hg, hd⟩
  · exact Or.inr ⟨hg, hd⟩

private theorem exists_normal_ker {Y : Type w} [Group Y] [Finite Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) (m : ℕ) :
    ∃ N : Subgroup ↥(Gsub α), N.Normal ∧ N.FiniteIndex ∧ N ≤ (thetaSub c₀).ker ∧
      ∀ r ∈ badSet (α := α) c₀ m, r ∉ N := by
  haveI : (thetaSub c₀).ker.FiniteIndex := by
    haveI : Finite ↥(thetaSub c₀).range := inferInstance
    exact Subgroup.finiteIndex_ker (thetaSub c₀)
  haveI : Group.ResiduallyFinite ↥(thetaSub c₀).ker := residuallyFinite_ker hc₀
  exact CFSG.Geometry.Trees.exists_normal_finiteIndex_le_of_residuallyFinite
    (G := ↥(Gsub α)) (F := (thetaSub c₀).ker) (badSet (α := α) c₀ m)
    (badSet_finite hc₀ m) (fun r hr => hr.1) (by
      intro h
      exact h.2.1 rfl)

private noncomputable def iota1 : α.G1 →* ↥(Gsub α) where
  toFun g := ⟨Amalgam.ξ α.toAmalgam RankTwoIndex.one g,
    Subgroup.mem_sup_left ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one (Amalgam.ξ α.toAmalgam RankTwoIndex.one))
  map_mul' a b := Subtype.ext (map_mul (Amalgam.ξ α.toAmalgam RankTwoIndex.one) a b)

private noncomputable def iota2 : α.G2 →* ↥(Gsub α) where
  toFun g := ⟨Amalgam.ξ α.toAmalgam RankTwoIndex.two g,
    Subgroup.mem_sup_right ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one (Amalgam.ξ α.toAmalgam RankTwoIndex.two))
  map_mul' a b := Subtype.ext (map_mul (Amalgam.ξ α.toAmalgam RankTwoIndex.two) a b)

private theorem thetaSub_iota1 {Y : Type w} [Group Y] (c : α.Completion Y) (g : α.G1) :
    thetaSub c (iota1 g) = c.φ1 g := by
  simp [thetaSub, iota1, Completion.theta_ξ1]

private theorem thetaSub_iota2 {Y : Type w} [Group Y] (c : α.Completion Y) (g : α.G2) :
    thetaSub c (iota2 g) = c.φ2 g := by
  simp [thetaSub, iota2, Completion.theta_ξ2]

private theorem iota1_range : (iota1 (α := α)).range = α.Ghat1.subgroupOf (Gsub α) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

private theorem iota2_range : (iota2 (α := α)).range = α.Ghat2.subgroupOf (Gsub α) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩

private theorem iota1_comp_α1 (g : α.G12) : iota1 (α.α1 g) = iota2 (α.α2 g) := by
  apply Subtype.ext
  exact (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.one)
    trivial g).trans
    (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo) (e := RankTwoIndex.two)
      trivial g).symm

private theorem subgroupOf_sup_eq_top :
    (α.Ghat1.subgroupOf (Gsub α)) ⊔ (α.Ghat2.subgroupOf (Gsub α)) = ⊤ := by
  refine Subgroup.map_injective (f := (Gsub α).subtype) (Gsub α).subtype_injective ?_
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right,
    Subgroup.map_top, Subgroup.range_subtype]

private noncomputable def quotientCompletion {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    α.Completion (↥(Gsub α) ⧸ N) where
  φ1 := (QuotientGroup.mk' N).comp iota1
  φ12 := ((QuotientGroup.mk' N).comp iota1).comp α.α1
  φ2 := (QuotientGroup.mk' N).comp iota2
  comm1 _ := rfl
  comm2 g := by
    show (QuotientGroup.mk' N) (iota2 (α.α2 g)) = (QuotientGroup.mk' N) (iota1 (α.α1 g))
    rw [iota1_comp_α1]
  inter := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
      have hEq : (QuotientGroup.mk' N) (iota1 a) = (QuotientGroup.mk' N) (iota2 b) := hb.symm
      have hmk : QuotientGroup.mk (s := N) (iota1 a) = QuotientGroup.mk (s := N) (iota2 b) := hEq
      have hn : (iota1 a)⁻¹ * iota2 b ∈ N := QuotientGroup.eq.mp hmk
      have hθ : thetaSub c₀ ((iota1 a)⁻¹ * iota2 b) = 1 := MonoidHom.mem_ker.mp (hN hn)
      have hval : c₀.φ1 a = c₀.φ2 b := by
        rw [map_mul, map_inv, thetaSub_iota1, thetaSub_iota2] at hθ
        exact inv_mul_eq_one.mp hθ
      have hmem : c₀.φ1 a ∈ c₀.φ1.range ⊓ c₀.φ2.range :=
        ⟨⟨a, rfl⟩, ⟨b, hval.symm⟩⟩
      rw [c₀.inter] at hmem
      obtain ⟨e, he⟩ := hmem
      have ha : a = α.α1 e := hc₀.1 (he.symm.trans (c₀.comm1 e).symm)
      exact ⟨e, by rw [ha]; rfl⟩
    · rintro y ⟨e, rfl⟩
      exact ⟨⟨α.α1 e, rfl⟩, ⟨α.α2 e, by
        show (QuotientGroup.mk' N) (iota2 (α.α2 e)) =
          (QuotientGroup.mk' N) (iota1 (α.α1 e))
        rw [iota1_comp_α1]⟩⟩
  gen := by
    have htop : ((α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N)) ⊔
        ((α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N)) = ⊤ := by
      rw [← Subgroup.map_sup, subgroupOf_sup_eq_top, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := N) y
        exact ⟨x, rfl⟩)
    calc (((QuotientGroup.mk' N).comp iota1).range ⊔
          ((QuotientGroup.mk' N).comp iota2).range)
        = ((α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N)) ⊔
          ((α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N)) := by
          rw [MonoidHom.range_comp, MonoidHom.range_comp, iota1_range, iota2_range]
      _ = ⊤ := htop

private theorem quotientCompletion_isFaithful {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientCompletion c₀ hc₀ N hN).IsFaithful := by
  have hα1 : Function.Injective α.α1 := injective_α1 hc₀
  have hq1 : Function.Injective (quotientCompletion c₀ hc₀ N hN).φ1 := by
    intro a b hab
    change QuotientGroup.mk (s := N) (iota1 a) =
      QuotientGroup.mk (s := N) (iota1 b) at hab
    have hn : (iota1 a)⁻¹ * iota1 b ∈ N := QuotientGroup.eq.mp hab
    have hθ : thetaSub c₀ ((iota1 a)⁻¹ * iota1 b) = 1 := MonoidHom.mem_ker.mp (hN hn)
    rw [map_mul, map_inv, thetaSub_iota1, thetaSub_iota1] at hθ
    exact hc₀.1 (inv_mul_eq_one.mp hθ)
  have hq2 : Function.Injective (quotientCompletion c₀ hc₀ N hN).φ2 := by
    intro a b hab
    change QuotientGroup.mk (s := N) (iota2 a) =
      QuotientGroup.mk (s := N) (iota2 b) at hab
    have hn : (iota2 a)⁻¹ * iota2 b ∈ N := QuotientGroup.eq.mp hab
    have hθ : thetaSub c₀ ((iota2 a)⁻¹ * iota2 b) = 1 := MonoidHom.mem_ker.mp (hN hn)
    rw [map_mul, map_inv, thetaSub_iota2, thetaSub_iota2] at hθ
    exact hc₀.2.2 (inv_mul_eq_one.mp hθ)
  exact ⟨hq1, hq1.comp hα1, hq2⟩

private noncomputable def toGsub : α.Ghat →* ↥(Gsub α) where
  toFun x := ⟨x, by
    show x ∈ α.Ghat1 ⊔ α.Ghat2
    rw [α.Ghat1_sup_Ghat2]
    exact Subgroup.mem_top x⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem toGsub_val (x : α.Ghat) : (toGsub x : α.Ghat) = x := rfl

private theorem toGsub_xi1 (g : α.G1) : toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.one g) =
    iota1 g := Subtype.ext rfl

private theorem toGsub_xi2 (g : α.G2) : toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.two g) =
    iota2 g := Subtype.ext rfl

private theorem toGsub_xi12 (g : α.G12) :
    toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo g) = iota1 (α.α1 g) := by
  apply Subtype.ext
  exact (Amalgam.ξ_map (α := α.toAmalgam) (d := RankTwoIndex.onetwo)
    (e := RankTwoIndex.one) trivial g).symm

private theorem quotientCompletion_theta_hom {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientCompletion c₀ hc₀ N hN).theta =
      (QuotientGroup.mk' N).comp (toGsub (α := α)) := by
  refine Amalgam.hom_ext (α := α.toAmalgam)
    (f := (quotientCompletion c₀ hc₀ N hN).theta)
    (g := (QuotientGroup.mk' N).comp (toGsub (α := α))) ?_
  intro d x
  cases d with
  | one =>
    change (quotientCompletion c₀ hc₀ N hN).theta
      (Amalgam.ξ α.toAmalgam RankTwoIndex.one (show α.G1 from x)) =
      QuotientGroup.mk (toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.one
        (show α.G1 from x)))
    rw [Completion.theta_ξ1, toGsub_xi1]
    rfl
  | two =>
    change (quotientCompletion c₀ hc₀ N hN).theta
      (Amalgam.ξ α.toAmalgam RankTwoIndex.two (show α.G2 from x)) =
      QuotientGroup.mk (toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.two
        (show α.G2 from x)))
    rw [Completion.theta_ξ2, toGsub_xi2]
    rfl
  | onetwo =>
    change (quotientCompletion c₀ hc₀ N hN).theta
      (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo (show α.G12 from x)) =
      QuotientGroup.mk (toGsub (Amalgam.ξ α.toAmalgam RankTwoIndex.onetwo
        (show α.G12 from x)))
    rw [Completion.theta_ξ12, toGsub_xi12]
    rfl

private theorem quotientCompletion_theta {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) (g : ↥(Gsub α)) :
    (quotientCompletion c₀ hc₀ N hN).theta (g : α.Ghat) =
      QuotientGroup.mk (s := N) g := by
  rw [quotientCompletion_theta_hom c₀ hc₀ N hN]
  show QuotientGroup.mk (toGsub (g : α.Ghat)) = QuotientGroup.mk g
  congr 1

private noncomputable def quotientPi {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (N : Subgroup ↥(Gsub α)) [N.Normal] (hN : N ≤ (thetaSub c₀).ker) :
    (↥(Gsub α) ⧸ N) →* Y :=
  QuotientGroup.lift N (thetaSub c₀) hN

private theorem quotientPi_comp_φ1 {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientPi c₀ N hN).comp (quotientCompletion c₀ hc₀ N hN).φ1 = c₀.φ1 := by
  ext a
  simp [quotientPi, quotientCompletion, thetaSub_iota1]

private theorem quotientPi_comp_φ2 {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientPi c₀ N hN).comp (quotientCompletion c₀ hc₀ N hN).φ2 = c₀.φ2 := by
  ext a
  simp [quotientPi, quotientCompletion, thetaSub_iota2]

private theorem quotientCompletion_range_φ1 {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientCompletion c₀ hc₀ N hN).φ1.range =
      (α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N) := by
  rw [show (quotientCompletion c₀ hc₀ N hN).φ1 =
    (QuotientGroup.mk' N).comp iota1 from rfl, MonoidHom.range_comp, iota1_range]

private theorem quotientCompletion_range_φ2 {Y : Type w} [Group Y] (c₀ : α.Completion Y)
    (hc₀ : c₀.IsFaithful) (N : Subgroup ↥(Gsub α)) [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) :
    (quotientCompletion c₀ hc₀ N hN).φ2.range =
      (α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N) := by
  rw [show (quotientCompletion c₀ hc₀ N hN).φ2 =
    (QuotientGroup.mk' N).comp iota2 from rfl, MonoidHom.range_comp, iota2_range]

private theorem fibre_inl {N : Subgroup ↥(Gsub α)} [N.Normal]
    {c : α.Completion (↥(Gsub α) ⧸ N)} (hc : c.IsFaithful)
    (htheta : ∀ g : ↥(Gsub α), c.theta (g : α.Ghat) = QuotientGroup.mk (s := N) g)
    (hphi1 : c.φ1.range = (α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N))
    {x x' : ↥(Gsub α) ⧸ α.Ghat1.subgroupOf (Gsub α)}
    (h : c.Θ hc (Sum.inl x) = c.Θ hc (Sum.inl x')) :
    ∃ n ∈ N, n • (Sum.inl x : α.Γhat) = Sum.inl x' := by
  let γ₀h : α.Γhat := CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2
  let γ₀c : c.Γ := CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range
  have hΘ0 : c.Θ hc γ₀h = γ₀c := by
    show (c.coverData hc).Θ (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) =
      CosetGeom.γ₀ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range
    exact (c.coverData hc).Θ_γ₀
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := Gsub α) (G₁ := α.Ghat1)
    (G₂ := α.Ghat2) (γ := Sum.inl x) rfl
  obtain ⟨g', hg'⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := Gsub α) (G₁ := α.Ghat1)
    (G₂ := α.Ghat2) (γ := Sum.inl x') rfl
  rw [hg, hg'] at h ⊢
  have hbase : c.theta0 hc g • γ₀c = c.theta0 hc g' • γ₀c := by
    have hh := h
    rw [c.Θ_smul hc g γ₀h, c.Θ_smul hc g' γ₀h, hΘ0] at hh
    exact hh
  have hstab : (((c.theta0 hc g)⁻¹ * c.theta0 hc g' :
      ↥(c.φ1.range ⊔ c.φ2.range)) : ↥(Gsub α) ⧸ N) ∈ c.φ1.range := by
    have hs : ((c.theta0 hc g)⁻¹ * c.theta0 hc g') • γ₀c = γ₀c := by
      calc ((c.theta0 hc g)⁻¹ * c.theta0 hc g') • γ₀c
          = (c.theta0 hc g)⁻¹ • (c.theta0 hc g' • γ₀c) := mul_smul _ _ _
        _ = (c.theta0 hc g)⁻¹ • (c.theta0 hc g • γ₀c) := by rw [hbase]
        _ = ((c.theta0 hc g)⁻¹ * c.theta0 hc g) • γ₀c := (mul_smul _ _ _).symm
        _ = γ₀c := by rw [inv_mul_cancel, one_smul]
    have := CosetGeom.mem_stab_of_smul_eq hs
    rwa [CosetGeom.stab_γ₀ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
      (G₂ := c.φ2.range) le_sup_left] at this
  have hmemY : (c.theta (g : α.Ghat))⁻¹ * c.theta (g' : α.Ghat) ∈ c.φ1.range := by
    have hcast := hstab
    push_cast at hcast
    simpa only [Completion.coe_theta0] using hcast
  rw [hphi1, Subgroup.mem_map] at hmemY
  obtain ⟨y, hy, hxy⟩ := hmemY
  let p : ↥(Gsub α) := ⟨(y : α.Ghat), Subgroup.mem_sup_left hy⟩
  have hp_eq : p = y := Subtype.ext rfl
  have hpθ : c.theta (p : α.Ghat) =
      (c.theta (g : α.Ghat))⁻¹ * c.theta (g' : α.Ghat) := by
    rw [htheta p, hp_eq]
    exact hxy
  have hp0 : c.theta0 hc p = (c.theta0 hc g)⁻¹ * c.theta0 hc g' := by
    apply Subtype.ext
    simp only [Completion.coe_theta0]
    exact hpθ
  let n : ↥(Gsub α) := p⁻¹ * g⁻¹ * g'
  have hn0 : c.theta0 hc n = 1 := by
    show c.theta0 hc (p⁻¹ * g⁻¹ * g') = 1
    rw [map_mul, map_mul, map_inv, map_inv, hp0]
    group
  have hnN : n ∈ N := by
    have hnY : (c.theta0 hc n : ↥(Gsub α) ⧸ N) = 1 := congrArg Subtype.val hn0
    have hnY' : c.theta (n : α.Ghat) = 1 := by
      simpa only [Completion.coe_theta0] using hnY
    have hmk : QuotientGroup.mk (s := N) n = 1 := by
      rw [← htheta n, hnY']
    have hmk' : QuotientGroup.mk (s := N) (1 : ↥(Gsub α)) =
        QuotientGroup.mk (s := N) n := hmk.symm
    have := QuotientGroup.eq.mp hmk'
    simpa using this
  let f : ↥(Gsub α) := g * p * n * p⁻¹ * g⁻¹
  have hfN : f ∈ N := by
    have h1 : p * n * p⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (H := N) inferInstance n hnN p
    have h2 : g * (p * n * p⁻¹) * g⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (H := N) inferInstance (p * n * p⁻¹) h1 g
    simpa [f, mul_assoc] using h2
  have hg'' : g' = g * p * n := by
    show g' = g * p * (p⁻¹ * g⁻¹ * g')
    group
  have hpiγ : p⁻¹ • γ₀h = γ₀h :=
    CosetGeom.smul_γ₀_of_mem (G₀ := Gsub α) (G₁ := α.Ghat1) (G₂ := α.Ghat2)
      le_sup_left ((α.Ghat1.subgroupOf (Gsub α)).inv_mem hy)
  refine ⟨f, hfN, ?_⟩
  rw [hg'']
  calc f • (g • γ₀h)
      = (f * g) • γ₀h := (mul_smul _ _ _).symm
    _ = (g * p * n * p⁻¹) • γ₀h := by
        rw [show f * g = g * p * n * p⁻¹ by
          show g * p * n * p⁻¹ * g⁻¹ * g = g * p * n * p⁻¹
          group]
    _ = (g * p * n) • (p⁻¹ • γ₀h) := mul_smul _ _ _
    _ = (g * p * n) • γ₀h := by rw [hpiγ]


private theorem fibre_inr {N : Subgroup ↥(Gsub α)} [N.Normal]
    {c : α.Completion (↥(Gsub α) ⧸ N)} (hc : c.IsFaithful)
    (htheta : ∀ g : ↥(Gsub α), c.theta (g : α.Ghat) = QuotientGroup.mk (s := N) g)
    (hphi2 : c.φ2.range = (α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N))
    {y y' : ↥(Gsub α) ⧸ α.Ghat2.subgroupOf (Gsub α)}
    (h : c.Θ hc (Sum.inr y) = c.Θ hc (Sum.inr y')) :
    ∃ n ∈ N, n • (Sum.inr y : α.Γhat) = Sum.inr y' := by
  let γ₁h : α.Γhat := CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2
  let γ₁c : c.Γ := CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range
  have hΘ1 : c.Θ hc γ₁h = γ₁c := by
    show (c.coverData hc).Θ (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) =
      CosetGeom.γ₁ (c.φ1.range ⊔ c.φ2.range) c.φ1.range c.φ2.range
    exact (c.coverData hc).Θ_γ₁
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := Gsub α) (G₁ := α.Ghat1)
    (G₂ := α.Ghat2) (γ := Sum.inr y) rfl
  obtain ⟨g', hg'⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := Gsub α) (G₁ := α.Ghat1)
    (G₂ := α.Ghat2) (γ := Sum.inr y') rfl
  rw [hg, hg'] at h ⊢
  have hbase : c.theta0 hc g • γ₁c = c.theta0 hc g' • γ₁c := by
    have hh := h
    rw [c.Θ_smul hc g γ₁h, c.Θ_smul hc g' γ₁h, hΘ1] at hh
    exact hh
  have hstab : (((c.theta0 hc g)⁻¹ * c.theta0 hc g' :
      ↥(c.φ1.range ⊔ c.φ2.range)) : ↥(Gsub α) ⧸ N) ∈ c.φ2.range := by
    have hs : ((c.theta0 hc g)⁻¹ * c.theta0 hc g') • γ₁c = γ₁c := by
      calc ((c.theta0 hc g)⁻¹ * c.theta0 hc g') • γ₁c
          = (c.theta0 hc g)⁻¹ • (c.theta0 hc g' • γ₁c) := mul_smul _ _ _
        _ = (c.theta0 hc g)⁻¹ • (c.theta0 hc g • γ₁c) := by rw [hbase]
        _ = ((c.theta0 hc g)⁻¹ * c.theta0 hc g) • γ₁c := (mul_smul _ _ _).symm
        _ = γ₁c := by rw [inv_mul_cancel, one_smul]
    have := CosetGeom.mem_stab_of_smul_eq hs
    rwa [CosetGeom.stab_γ₁ (G₀ := c.φ1.range ⊔ c.φ2.range) (G₁ := c.φ1.range)
      (G₂ := c.φ2.range) le_sup_right] at this
  have hmemY : (c.theta (g : α.Ghat))⁻¹ * c.theta (g' : α.Ghat) ∈ c.φ2.range := by
    have hcast := hstab
    push_cast at hcast
    simpa only [Completion.coe_theta0] using hcast
  rw [hphi2, Subgroup.mem_map] at hmemY
  obtain ⟨y, hy, hxy⟩ := hmemY
  let p : ↥(Gsub α) := ⟨(y : α.Ghat), Subgroup.mem_sup_right hy⟩
  have hp_eq : p = y := Subtype.ext rfl
  have hpθ : c.theta (p : α.Ghat) =
      (c.theta (g : α.Ghat))⁻¹ * c.theta (g' : α.Ghat) := by
    rw [htheta p, hp_eq]
    exact hxy
  have hp0 : c.theta0 hc p = (c.theta0 hc g)⁻¹ * c.theta0 hc g' := by
    apply Subtype.ext
    simp only [Completion.coe_theta0]
    exact hpθ
  let n : ↥(Gsub α) := p⁻¹ * g⁻¹ * g'
  have hn0 : c.theta0 hc n = 1 := by
    show c.theta0 hc (p⁻¹ * g⁻¹ * g') = 1
    rw [map_mul, map_mul, map_inv, map_inv, hp0]
    group
  have hnN : n ∈ N := by
    have hnY : (c.theta0 hc n : ↥(Gsub α) ⧸ N) = 1 := congrArg Subtype.val hn0
    have hnY' : c.theta (n : α.Ghat) = 1 := by
      simpa only [Completion.coe_theta0] using hnY
    have hmk : QuotientGroup.mk (s := N) n = 1 := by
      rw [← htheta n, hnY']
    have hmk' : QuotientGroup.mk (s := N) (1 : ↥(Gsub α)) =
        QuotientGroup.mk (s := N) n := hmk.symm
    have := QuotientGroup.eq.mp hmk'
    simpa using this
  let f : ↥(Gsub α) := g * p * n * p⁻¹ * g⁻¹
  have hfN : f ∈ N := by
    have h1 : p * n * p⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (H := N) inferInstance n hnN p
    have h2 : g * (p * n * p⁻¹) * g⁻¹ ∈ N :=
      Subgroup.Normal.conj_mem (H := N) inferInstance (p * n * p⁻¹) h1 g
    simpa [f, mul_assoc] using h2
  have hg'' : g' = g * p * n := by
    show g' = g * p * (p⁻¹ * g⁻¹ * g')
    group
  have hpiγ : p⁻¹ • γ₁h = γ₁h :=
    CosetGeom.smul_γ₁_of_mem (G₀ := Gsub α) (G₁ := α.Ghat1) (G₂ := α.Ghat2)
      le_sup_right ((α.Ghat2.subgroupOf (Gsub α)).inv_mem hy)
  refine ⟨f, hfN, ?_⟩
  rw [hg'']
  calc f • (g • γ₁h)
      = (f * g) • γ₁h := (mul_smul _ _ _).symm
    _ = (g * p * n * p⁻¹) • γ₁h := by
        rw [show f * g = g * p * n * p⁻¹ by
          show g * p * n * p⁻¹ * g⁻¹ * g = g * p * n * p⁻¹
          group]
    _ = (g * p * n) • (p⁻¹ • γ₁h) := mul_smul _ _ _
    _ = (g * p * n) • γ₁h := by rw [hpiγ]


private theorem exists_mem_N_smul_of_Θ_eq {N : Subgroup ↥(Gsub α)} [N.Normal]
    {c : α.Completion (↥(Gsub α) ⧸ N)} (hc : c.IsFaithful)
    (htheta : ∀ g : ↥(Gsub α), c.theta (g : α.Ghat) = QuotientGroup.mk (s := N) g)
    (hphi1 : c.φ1.range = (α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N))
    (hphi2 : c.φ2.range = (α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N))
    {a b : α.Γhat} (h : c.Θ hc a = c.Θ hc b) : ∃ n ∈ N, n • a = b := by
  cases a with
  | inl x =>
    cases b with
    | inl x' => exact fibre_inl hc htheta hphi1 h
    | inr y =>
      exfalso
      change Sum.inl _ = Sum.inr _ at h
      have hv := congrArg CosetGeom.vtype h
      simp [CosetGeom.vtype] at hv
  | inr y =>
    cases b with
    | inl x =>
      exfalso
      change Sum.inr _ = Sum.inl _ at h
      have hv := congrArg CosetGeom.vtype h
      simp [CosetGeom.vtype] at hv
    | inr y' => exact fibre_inr hc htheta hphi2 h

private abbrev gpathTail {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (q : GPath Γ (n + 1)) :
    GPath Γ n where
  toFun i := q (i + 1)
  adj i hi := by
    have h := q.adj (i + 1) (by omega)
    simpa [Nat.add_assoc] using h
  tail i hi := q.tail (i + 1) (by omega)

private def gpathToWalk {V : Type*} {Γ : SimpleGraph V} :
    ∀ {n : ℕ}, (q : GPath Γ n) → Γ.Walk (q 0) (q n)
  | 0, q => SimpleGraph.Walk.nil
  | n + 1, q => SimpleGraph.Walk.cons (q.adj 0 (Nat.succ_pos n)) (gpathToWalk (gpathTail q))

private theorem gpathToWalk_length {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (q : GPath Γ n) :
    (gpathToWalk q).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gpathToWalk]
    simp only [SimpleGraph.Walk.length_cons, ih]

private theorem gpathToWalk_edges {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (q : GPath Γ n) :
    (gpathToWalk q).edges =
      (List.range n).map (fun i => s(q i, q (i + 1))) := by
  induction n with
  | zero => simp [gpathToWalk]
  | succ n ih =>
    rw [gpathToWalk, SimpleGraph.Walk.edges_cons, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1

private theorem gpathToWalk_chain {V : Type*} {Γ : SimpleGraph V} {n : ℕ} (q : GPath Γ n)
    (hq : q.NoBack) : List.IsChain (· ≠ ·) (gpathToWalk q).edges := by
  cases n with
  | zero => simp [gpathToWalk]
  | succ n =>
    cases n with
    | zero => simp [gpathToWalk]
    | succ m =>
      rw [gpathToWalk, SimpleGraph.Walk.edges_cons, gpathToWalk_edges (gpathTail q),
        List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Function.comp]
      refine List.IsChain.cons_cons ?_ ?_
      · intro heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact (q.adj 0 (by omega)).ne h1
        · exact hq 0 (by omega) h1
      · have hq' : (gpathTail q).NoBack := by
          intro i hi
          exact hq (i + 1) (by omega)
        have hrec := gpathToWalk_chain (gpathTail q) hq'
        simpa [gpathToWalk_edges (gpathTail q), List.range_succ_eq_map,
          List.map_cons, List.map_map, Function.comp] using hrec

private theorem no_closed_nb {Y : Type w} [Group Y] {c₀ : α.Completion Y}
    (hc₀ : c₀.IsFaithful) {n : ℕ} (q : GPath α.graphHat n) (hq : q.NoBack)
    (hn : 1 ≤ n) : q 0 ≠ q n := by
  intro heq
  have hacyc : α.graphHat.IsAcyclic :=
    graphHat_isAcyclic α (injective_α1 hc₀) (injective_α2 hc₀)
  let p : α.graphHat.Walk (q 0) (q n) := gpathToWalk q
  have hp : p.IsPath := (hacyc.isPath_iff_isChain p).2 (gpathToWalk_chain q hq)
  let p' : α.graphHat.Walk (q 0) (q 0) := p.copy rfl heq.symm
  have hp' : p'.IsPath := by
    rw [SimpleGraph.Walk.isPath_copy]
    exact hp
  have hnil : p'.Nil := (SimpleGraph.Walk.isPath_iff_nil).mp hp'
  have hlen : p'.length = n := by
    rw [SimpleGraph.Walk.length_copy]
    exact gpathToWalk_length q
  have hzero : p'.length = 0 := by
    rw [SimpleGraph.Walk.eq_nil_iff_nil.mpr hnil]
    rfl
  omega

private theorem quotientCompletion_no_short_cycle {Y : Type w} [Group Y]
    (c₀ : α.Completion Y) (hc₀ : c₀.IsFaithful)
    {N : Subgroup ↥(Gsub α)} [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) (m : ℕ)
    (hR : ∀ r ∈ badSet (α := α) c₀ m, r ∉ N) :
    ∀ (u : (quotientCompletion c₀ hc₀ N hN).Γ)
      (p : (quotientCompletion c₀ hc₀ N hN).graph.Walk u u),
      p.IsCycle → m + 1 ≤ p.length := by
  let c := quotientCompletion c₀ hc₀ N hN
  have hc : c.IsFaithful := quotientCompletion_isFaithful c₀ hc₀ N hN
  have hcov : GraphCovering α.graphHat c.graph (c.Θ hc) := c.graphCovering hc
  have htheta : ∀ g : ↥(Gsub α), c.theta (g : α.Ghat) = QuotientGroup.mk (s := N) g :=
    quotientCompletion_theta c₀ hc₀ N hN
  have hphi1 : c.φ1.range = (α.Ghat1.subgroupOf (Gsub α)).map (QuotientGroup.mk' N) :=
    quotientCompletion_range_φ1 c₀ hc₀ N hN
  have hphi2 : c.φ2.range = (α.Ghat2.subgroupOf (Gsub α)).map (QuotientGroup.mk' N) :=
    quotientCompletion_range_φ2 c₀ hc₀ N hN
  have hconn : α.graphHat.Connected :=
    CosetGeom.connected (G₀ := Gsub α) (G₁ := α.Ghat1) (G₂ := α.Ghat2) rfl
  intro u p hp
  by_contra hlt
  have hlen : p.length ≤ m := by omega
  have hp3 : 3 ≤ p.length := hp.isCircuit.three_le_length
  let pth : GPath c.graph p.length := GPath.ofWalk p
  have hnb : pth.NoBack := CFSG.Quasithin.GoldAmalgam.WalkNB.of_isCycle hp
  obtain ⟨v0, hv0⟩ := hcov.surj (pth 0)
  obtain ⟨q, ⟨hq0, hqmap⟩, -⟩ := hcov.lift_path v0 p.length pth hv0.symm
  have hqnb : q.NoBack := (hcov.noBack_pathMap_iff q).mp (by rw [hqmap]; exact hnb)
  have hclose : c.Θ hc (q 0) = c.Θ hc (q p.length) := by
    have h0 : c.Θ hc (q 0) = pth 0 := by rw [hq0]; exact hv0
    have h1 : c.Θ hc (q p.length) = pth p.length := by
      have := congrArg (fun r : GPath c.graph p.length => r p.length) hqmap
      simpa [GraphCovering.pathMap_apply] using this
    have hpclosed : pth p.length = pth 0 := by
      simp [pth, GPath.ofWalk, SimpleGraph.Walk.getVert_length]
    rw [h0, h1, hpclosed]
  obtain ⟨f, hfN, hfq⟩ := exists_mem_N_smul_of_Θ_eq hc htheta hphi1 hphi2 hclose
  have hqne : q 0 ≠ q p.length := no_closed_nb hc₀ q hqnb (by omega)
  have hfne : f ≠ 1 := by
    intro hf1
    exact hqne (by rw [← hfq, hf1, one_smul])
  have hdist_q : α.graphHat.dist (q 0) (q p.length) ≤ p.length :=
    GPath.dist_le_length hconn q
  cases hvt : CosetGeom.vtype (q 0) with
  | false =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) (γ := q 0) hvt
    let r : ↥(Gsub α) := g⁻¹ * f * g
    have hrN : r ∈ N := by
      have h := Subgroup.Normal.conj_mem (H := N) inferInstance f hfN g⁻¹
      simpa [r, mul_assoc] using h
    have hrne : r ≠ 1 := by
      intro hr1
      apply hfne
      have h := congrArg (fun x => g * x * g⁻¹) hr1
      simpa [r, mul_assoc] using h
    have hdist : α.graphHat.dist (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) (r •
        CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2) ≤ m := by
      have h1 : r • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 =
          g⁻¹ • q p.length := by
        rw [show r = g⁻¹ * f * g from rfl, mul_smul, mul_smul, hg.symm, hfq]
      have h2 : g⁻¹ • q 0 = CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2 := by
        rw [hg]; simp
      calc α.graphHat.dist (CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)
            (r • CosetGeom.γ₀ (Gsub α) α.Ghat1 α.Ghat2)
          = α.graphHat.dist (g⁻¹ • q 0) (g⁻¹ • q p.length) := by rw [h1, h2]
        _ = α.graphHat.dist (q 0) (q p.length) :=
            CosetGeom.dist_smul (G₀ := Gsub α) g⁻¹ (q 0) (q p.length)
        _ ≤ p.length := hdist_q
        _ ≤ m := hlen
    exact hR r ⟨hN hrN, hrne, Or.inl hdist⟩ hrN
  | true =>
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ (G₀ := Gsub α) (G₁ := α.Ghat1)
      (G₂ := α.Ghat2) (γ := q 0) hvt
    let r : ↥(Gsub α) := g⁻¹ * f * g
    have hrN : r ∈ N := by
      have h := Subgroup.Normal.conj_mem (H := N) inferInstance f hfN g⁻¹
      simpa [r, mul_assoc] using h
    have hrne : r ≠ 1 := by
      intro hr1
      apply hfne
      have h := congrArg (fun x => g * x * g⁻¹) hr1
      simpa [r, mul_assoc] using h
    have hdist : α.graphHat.dist (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) (r •
        CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2) ≤ m := by
      have h1 : r • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 =
          g⁻¹ • q p.length := by
        rw [show r = g⁻¹ * f * g from rfl, mul_smul, mul_smul, hg.symm, hfq]
      have h2 : g⁻¹ • q 0 = CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2 := by
        rw [hg]; simp
      calc α.graphHat.dist (CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)
            (r • CosetGeom.γ₁ (Gsub α) α.Ghat1 α.Ghat2)
          = α.graphHat.dist (g⁻¹ • q 0) (g⁻¹ • q p.length) := by rw [h1, h2]
        _ = α.graphHat.dist (q 0) (q p.length) :=
            CosetGeom.dist_smul (G₀ := Gsub α) g⁻¹ (q 0) (q p.length)
        _ ≤ p.length := hdist_q
        _ ≤ m := hlen
    exact hR r ⟨hN hrN, hrne, Or.inr hdist⟩ hrN

private theorem quotientCompletion_egirth_gt {Y : Type w} [Group Y]
    (c₀ : α.Completion Y) (hc₀ : c₀.IsFaithful)
    {N : Subgroup ↥(Gsub α)} [N.Normal]
    (hN : N ≤ (thetaSub c₀).ker) (m : ℕ)
    (hR : ∀ r ∈ badSet (α := α) c₀ m, r ∉ N) :
    (m : ℕ∞) < (quotientCompletion c₀ hc₀ N hN).graph.egirth := by
  let c := quotientCompletion c₀ hc₀ N hN
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ c.graph.egirth := by
    rw [SimpleGraph.le_egirth]
    intro u p hp
    exact_mod_cast quotientCompletion_no_short_cycle c₀ hc₀ (N := N) hN m hR u p hp
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hle

theorem exists_faithful_finite_completion_lt_egirth {α : RankTwoAmalgam.{u}} {Y₀ : Type w}
    [Group Y₀] [Finite Y₀] (c₀ : α.Completion Y₀) (hc₀ : c₀.IsFaithful) (m : ℕ) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (c : α.Completion Y),
      c.IsFaithful ∧ (∃ π : Y →* Y₀, π.comp c.φ1 = c₀.φ1 ∧ π.comp c.φ2 = c₀.φ2) ∧
      (m : ℕ∞) < c.graph.egirth := by
  obtain ⟨N, hNnormal, hNfin, hNle, hR⟩ := exists_normal_ker (α := α) (c₀ := c₀) hc₀ m
  letI : N.Normal := hNnormal
  let c : α.Completion (↥(Gsub α) ⧸ N) := quotientCompletion c₀ hc₀ N hNle
  have hc : c.IsFaithful := quotientCompletion_isFaithful c₀ hc₀ N hNle
  letI : Fintype (↥(Gsub α) ⧸ N) := N.fintypeQuotientOfFiniteIndex
  haveI : Finite (↥(Gsub α) ⧸ N) :=
    Fintype.finite (inferInstance : Fintype (↥(Gsub α) ⧸ N))
  refine ⟨↥(Gsub α) ⧸ N, inferInstance, inferInstance, c, hc, ?_, ?_⟩
  · exact ⟨quotientPi c₀ N hNle, quotientPi_comp_φ1 c₀ hc₀ N hNle,
      quotientPi_comp_φ2 c₀ hc₀ N hNle⟩
  · exact quotientCompletion_egirth_gt c₀ hc₀ (N := N) hNle m hR

theorem ofSubgroups_exists_faithful_finite_completion_lt_egirth {X : Type u} [Group X] [Finite X]
    (P1 P2 : Subgroup X) (m : ℕ) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (c : (ofSubgroups P1 P2).Completion Y),
      c.IsFaithful ∧ (∃ π : Y →* X, (∀ g : ↥P1, π (c.φ1 g) = (g : X)) ∧
        ∀ g : ↥P2, π (c.φ2 g) = (g : X)) ∧
      (m : ℕ∞) < c.graph.egirth := by
  let c₀ := RankTwoAmalgam.inclusionCompletion P1 P2 (P1 ⊔ P2) rfl
  have hc₀ : c₀.IsFaithful :=
    RankTwoAmalgam.inclusionCompletion_isFaithful P1 P2 (P1 ⊔ P2) rfl
  obtain ⟨Y, hY, hFin, c, hc, ⟨π, hπ1, hπ2⟩, hgirth⟩ :=
    exists_faithful_finite_completion_lt_egirth c₀ hc₀ m
  letI : Group Y := hY
  letI : Finite Y := hFin
  refine ⟨Y, hY, hFin, c, hc, ⟨(P1 ⊔ P2).subtype.comp π, ?_, ?_⟩, hgirth⟩
  · intro g
    have h : π (c.φ1 g) = c₀.φ1 g := DFunLike.congr_fun hπ1 g
    change ((P1 ⊔ P2).subtype (π (c.φ1 g)) : X) = (g : X)
    rw [h]
    rfl
  · intro g
    have h : π (c.φ2 g) = c₀.φ2 g := DFunLike.congr_fun hπ2 g
    change ((P1 ⊔ P2).subtype (π (c.φ2 g)) : X) = (g : X)
    rw [h]
    rfl

end CFSG.Quasithin.RankTwoAmalgam
