module

public import CFSG.LieType.Chevalley.BraidWalk
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

section WW

variable {τ : Tag} {K : Type} [Field K]

theorem end_ext' {f g : Module.End K (RootModule τ K)}
    (hh : ∀ j, f (hVec τ K j) = g (hVec τ K j))
    (hr : ∀ k < τ.rootCertificate.roots.length,
      f (rootVec τ K (τ.rootCertificate.root k)) = g (rootVec τ K (τ.rootCertificate.root k))) :
    f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    have := hr k hk
    rwa [rootVec_eq_single_of_isRoot hα] at this

@[expose] noncomputable def wElt (ω : List (Fin τ.rank)) : adjointGroup τ K :=
  ⟨(ω.map fun i => weylElt τ K i 1).prod, Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_adjointGroup i 1⟩

theorem coe_wElt (ω : List (Fin τ.rank)) :
    ((wElt ω : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) =
      (ω.map fun i => weylElt τ K i 1).prod := rfl

theorem wElt_append (ω ω' : List (Fin τ.rank)) :
    (wElt (ω ++ ω') : adjointGroup τ K) = wElt ω * wElt ω' :=
  Subtype.ext (by simp [coe_wElt, List.map_append, List.prod_append])

@[expose] def WSq (τ : Tag) (ω : List (Fin τ.rank)) : Prop :=
  (∀ k < τ.rootCertificate.roots.length, walk τ (ω ++ ω) k = (k, 0)) ∧
    ∀ j : Fin τ.rank, (ω ++ ω).foldr (hStep τ) (Pi.single j 1) = Pi.single j 1

instance (τ : Tag) (ω : List (Fin τ.rank)) : Decidable (WSq τ ω) := by
  unfold WSq
  infer_instance

theorem wElt_mul_wElt_eq_one {ω : List (Fin τ.rank)} (h : WSq τ ω) :
    (wElt ω * wElt ω : adjointGroup τ K) = 1 := by
  rw [← wElt_append]
  refine Subtype.ext (Units.ext (end_ext' (fun j => ?_) (fun k hk => ?_)))
  · have := prod_weylElt_hVecSum K (ω ++ ω) (Pi.single j 1)
    rw [hVecSum_single, h.2 j, hVecSum_single] at this
    exact this
  · have := prod_weylElt_rootVec_root K (ω ++ ω) hk
    rw [h.1 k hk, pow_zero, one_smul] at this
    exact this

theorem torus_apply_hVecSum (i : Fin τ.rank) (t : Kˣ) (c : Fin τ.rank → ℤ) :
    (torusElt τ K i t : Module.End K (RootModule τ K)) (hVecSum K c) = hVecSum K c := by
  simp only [hVecSum, map_sum, map_smul, torusElt_hVec]

theorem neg_one_zpow_parity {m m' : ℤ} (h : m % 2 = m' % 2) :
    (((-1 : Kˣ) ^ m : Kˣ) : K) = (((-1 : Kˣ) ^ m' : Kˣ) : K) := by
  have key : ∀ n : ℤ, (((-1 : Kˣ) ^ n : Kˣ) : K) = if n % 2 = 0 then 1 else -1 := by
    intro n
    rcases Int.even_or_odd n with hn | hn
    · have h0 : n % 2 = 0 := Int.even_iff.1 hn
      simp [h0, hn.neg_one_zpow]
    · have h0 : ¬ n % 2 = 0 := by
        have := Int.odd_iff.1 hn
        omega
      simp [h0, hn.neg_one_zpow]
  rw [key, key, h]

theorem wElt_comm_dElt (ω : List (Fin τ.rank)) (i : Fin τ.rank)
    (hpar : ∀ k < τ.rootCertificate.roots.length,
      (∑ j, τ.cartan i j * τ.rootCertificate.root k j) % 2 =
        (∑ j, τ.cartan i j * τ.rootCertificate.root (walk τ ω k).1 j) % 2) :
    (wElt ω * dElt i (-1 : Kˣ) : adjointGroup τ K) = dElt i (-1 : Kˣ) * wElt ω := by
  refine Subtype.ext (Units.ext (end_ext' (fun j => ?_) (fun k hk => ?_)))
  · have h1 := prod_weylElt_hVecSum K ω (Pi.single j 1)
    rw [hVecSum_single] at h1
    show (((wElt ω : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        ((torusElt τ K i (-1) : Module.End K (RootModule τ K)) (hVec τ K j)) =
      (torusElt τ K i (-1) : Module.End K (RootModule τ K))
        ((((wElt ω : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) (hVec τ K j))
    rw [torusElt_hVec, coe_wElt, h1, torus_apply_hVecSum]
  · have hr := isRoot_rootCertificate_root (τ := τ) hk
    have hr' := isRoot_rootCertificate_root (τ := τ) (walk_fst_lt ω hk)
    have h1 := prod_weylElt_rootVec_root K ω hk
    show (((wElt ω : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
        ((torusElt τ K i (-1) : Module.End K (RootModule τ K))
          (rootVec τ K (τ.rootCertificate.root k))) =
      (torusElt τ K i (-1) : Module.End K (RootModule τ K))
        ((((wElt ω : adjointGroup τ K) : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
          (rootVec τ K (τ.rootCertificate.root k)))
    rw [torusElt_rootVec i (-1) hr, map_smul, coe_wElt, h1, map_smul,
      torusElt_rootVec i (-1) hr', smul_smul, smul_smul, mul_comm,
      neg_one_zpow_parity (hpar k hk)]

end WW

end CFSG.RankThree.PartOne.SLB4A
