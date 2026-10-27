module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenWeylLift
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGWeylFrame (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L')) {ι : Type}
    (M : CoxeterMatrix ι) : Prop :=
  ∃ (n : ι → L') (hn : ∀ i, MulAut.conj (n i) ∈ Subgroup.normalizer (A : Set (MulAut L'))),
    (∀ i, GGTorusWeylElt p A (n i)) ∧ (∀ i, GGIsReflection p (ggConjAut A (hn i))) ∧
      ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
        ∀ i, (e (M.simple i) : MulAut ↥A) = ggConjAut A (hn i)

theorem ggWeylOfType_of_frame {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ p) {ι : Type}
    {M : CoxeterMatrix ι} (hF : GGWeylFrame p (ggGamma K hN).range M) :
    GGWeylOfType p M (ggAutomizer K Bs) := by
  classical
  let A : Subgroup (MulAut ↥K) := (ggGamma K hN).range
  let H : Subgroup (MulAut ↥K) := (MulAut.conj : ↥K →* MulAut ↥K).range
  let A' : Subgroup (MulAut ↥A) := ggAutomizer H A
  change GGWeylFrame p A M at hF
  obtain ⟨n, hn, hnW, hrefl, e, he⟩ := hF
  let ρ : M.Group →* MulAut ↥A :=
    { toFun := fun w => (e w : MulAut ↥A)
      map_one' := by rw [map_one]; rfl
      map_mul' := fun x y => by rw [map_mul]; rfl }
  have hρsimple : ∀ i, ρ (M.simple i) = ggConjAut A (hn i) := fun i => he i
  have hexists : ∀ i, ∃ φ : MulAut ↥Bs, φ ∈ ggAutomizer K Bs ∧
      GGIsReflection p φ ∧ GGOverGamma hN φ (ggConjAut A (hn i)) := by
    intro i
    obtain ⟨g, hgK, hg, hrefl', hover⟩ :=
      exists_isReflection_overGamma_of_weylElt (n := n i) hp hp2 hBs hSC hN
        (hnW i) (hn i) (hrefl i)
    exact ⟨ggConjAut Bs hg, ggConjAut_mem_ggAutomizer hgK hg, hrefl', hover⟩
  choose φ hφ using hexists
  have hφauto : ∀ i, φ i ∈ ggAutomizer K Bs := fun i => (hφ i).1
  have hφrefl : ∀ i, GGIsReflection p (φ i) := fun i => (hφ i).2.1
  have hφover : ∀ i, GGOverGamma hN (φ i) (ggConjAut A (hn i)) := fun i => (hφ i).2.2
  have hρ : ∀ i j, (ggConjAut A (hn i) * ggConjAut A (hn j)) ^ (M i j) = 1 := by
    intro i j
    have hs : (M.simple i * M.simple j) ^ (M i j) = 1 :=
      (M.toCoxeterSystem).simple_mul_simple_pow i j
    calc (ggConjAut A (hn i) * ggConjAut A (hn j)) ^ (M i j)
        = ρ ((M.simple i * M.simple j) ^ (M i j)) := by
          rw [map_pow, map_mul, hρsimple i, hρsimple j]
      _ = 1 := by rw [hs, map_one]
  have hrel : M.IsLiftable φ := by
    intro i j
    have hover : GGOverGamma hN ((φ i * φ j) ^ (M i j))
        ((ggConjAut A (hn i) * ggConjAut A (hn j)) ^ (M i j)) :=
      ((hφover i).mul (hφover j)).pow _
    rw [hρ i j] at hover
    exact eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (hφauto i) (hφauto j)) _) hover
  let F : M.Group →* MulAut ↥Bs := (M.toCoxeterSystem).lift ⟨φ, hrel⟩
  have hFsimple : ∀ i, F (M.simple i) = φ i := fun i =>
    (M.toCoxeterSystem).lift_apply_simple hrel i
  have hFover : ∀ w : M.Group, GGOverGamma hN (F w) (e w : MulAut ↥A) := by
    intro w
    refine (M.toCoxeterSystem).simple_induction
      (p := fun w => GGOverGamma hN (F w) (e w : MulAut ↥A)) w ?_ ?_ ?_
    · intro i
      change GGOverGamma hN (F (M.simple i)) (e (M.simple i) : MulAut ↥A)
      rw [hFsimple i, he i]
      exact hφover i
    · change GGOverGamma hN (F 1) (e 1 : MulAut ↥A)
      rw [map_one F, map_one e]
      exact GGOverGamma.one
    · intro x y hx hy
      change GGOverGamma hN (F (x * y)) (e (x * y) : MulAut ↥A)
      rw [map_mul F, map_mul e]
      exact hx.mul hy
  have hFrange : F.range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← (M.toCoxeterSystem).subgroup_closure_range_simple,
      MonoidHom.map_closure]
    apply congrArg Subgroup.closure
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨i, rfl⟩ := hy
      exact ⟨i, (hFsimple i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.simple i, ⟨i, rfl⟩, hFsimple i⟩
  have hφcl_le : Subgroup.closure (Set.range φ) ≤ ggAutomizer K Bs :=
    (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr hφauto)
  have hFw_mem : ∀ w : M.Group, F w ∈ Subgroup.closure (Set.range φ) := by
    intro w
    rw [← hFrange]
    exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hGen_ge : ggAutomizer K Bs ≤ Subgroup.closure (Set.range φ) := by
    intro c hc
    obtain ⟨g, hgK, hg, hcg⟩ := mem_ggAutomizer_iff.mp hc
    have hceq : c = ggConjAut Bs hg := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [ggConjAut_apply]
      exact hcg b
    let a : MulAut ↥A := ggConjAut A (conj_mem_normalizer_range_ggGamma hN hgK hg)
    have ha : a ∈ A' := by
      change ggConjAut A (conj_mem_normalizer_range_ggGamma hN hgK hg) ∈ ggAutomizer H A
      exact ggConjAut_mem_ggAutomizer (H := H)
        (MonoidHom.mem_range.mpr ⟨⟨g, hgK⟩, rfl⟩)
        (conj_mem_normalizer_range_ggGamma hN hgK hg)
    obtain ⟨w, hw⟩ := e.surjective ⟨a, ha⟩
    have hew : (e w : MulAut ↥A) = a := congrArg Subtype.val hw
    have hoverw : GGOverGamma hN (F w) a := by
      have h := hFover w
      rwa [hew] at h
    have hoverc : GGOverGamma hN c a := by
      rw [hceq]
      exact ggOverGamma_conjAut (hN := hN) hgK hg
    have hκ : (F w)⁻¹ * c ∈ ggAutomizer K Bs :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hφcl_le (hFw_mem w))) hc
    have h1 : GGOverGamma hN ((F w)⁻¹ * c) 1 := by
      have hh := hoverw.inv.mul hoverc
      rwa [inv_mul_cancel] at hh
    have heq : (F w)⁻¹ * c = 1 := eq_one_of_ggOverGamma_one hp hBs hNoTr hN hZ hκ h1
    rw [inv_mul_eq_one] at heq
    rw [← heq]
    exact hFw_mem w
  have hGen : Subgroup.closure (Set.range φ) = ggAutomizer K Bs :=
    le_antisymm hφcl_le hGen_ge
  have hFrange' : F.range = ggAutomizer K Bs := hFrange.trans hGen
  have hF'cod : ∀ x : M.Group, F x ∈ ggAutomizer K Bs := fun x => by
    rw [← hFrange']
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let F' : M.Group →* ↥(ggAutomizer K Bs) := F.codRestrict (ggAutomizer K Bs) hF'cod
  have hF'surj : Function.Surjective F' := by
    intro y
    have hy : (y : MulAut ↥Bs) ∈ F.range := by rw [hFrange']; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hker : ∀ w : M.Group, F w = 1 → w = 1 := by
    intro w hw
    have hover : GGOverGamma hN (1 : MulAut ↥Bs) (e w : MulAut ↥A) := by
      rw [← hw]
      exact hFover w
    have hew : e w = 1 := by
      apply Subtype.ext
      exact GGOverGamma.eq_one_of_one hover
    exact e.injective (hew.trans (map_one e).symm)
  have hFinj : Function.Injective F := by
    intro w w' h
    have h1 : F (w⁻¹ * w') = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 : w⁻¹ * w' = 1 := hker (w⁻¹ * w') h1
    rwa [inv_mul_eq_one] at h3
  have hF'inj : Function.Injective F' :=
    (MonoidHom.injective_codRestrict F (ggAutomizer K Bs) hF'cod).mpr hFinj
  refine ⟨MulEquiv.ofBijective F' ⟨hF'inj, hF'surj⟩, ?_⟩
  intro i
  show GGIsReflection p (F (M.simple i))
  rw [hFsimple i]
  exact hφrefl i

end CFSG.StandardType

end
