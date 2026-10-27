module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerBorel
public import CFSG.LieType.Steinberg.PartBRankOne

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

namespace PsiDiag

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_torus_conj_of_mem_borel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank)
    (hcomm : ∀ y ∈ D.rootGroup (Pi.single i 1), ∀ z ∈ D.rootGroup (Pi.single i 1),
      y * z = z * y)
    {h : K} (hB : h ∈ borel D H)
    (hN : h ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K)) :
    ∃ t ∈ ⨆ j, H j, ∀ z ∈ D.rootGroup (Pi.single i 1), h * z * h⁻¹ = t * z * t⁻¹ := by
  obtain ⟨t, ht, u, hu, y, hy, rfl⟩ := exists_eq_mul_mul_of_mem_borel hct hext i hB
  refine ⟨t, ht, fun z hz => ?_⟩
  have hyz : y * z * y⁻¹ = z := by rw [hcomm y hy z hz]; group
  have htN : t ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) :=
    iSup_le_normalizer_rootGroup hct (single_mem_roots i) ht
  have hsplit : t * u * y * z * (t * u * y)⁻¹ = t * (u * z * u⁻¹) * t⁻¹ := by
    rw [show t * u * y * z * (t * u * y)⁻¹ = t * (u * (y * z * y⁻¹) * u⁻¹) * t⁻¹ by group, hyz]
  have h1 : u * z * u⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
    have hh := (Subgroup.mem_normalizer_iff.mp hN z).mp hz
    rw [hsplit] at hh
    have h' := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) _).mp hh
    rwa [show t⁻¹ * (t * (u * z * u⁻¹) * t⁻¹) * t⁻¹⁻¹ = u * z * u⁻¹ by group] at h'
  have h2 : z⁻¹ * (u * z * u⁻¹) ∈ posUnipotentExcept D i := by
    have hzN := rootGroup_single_le_normalizer hext i (inv_mem hz)
    rw [show z⁻¹ * (u * z * u⁻¹) = z⁻¹ * u * z⁻¹⁻¹ * u⁻¹ by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hzN u).mp hu) (inv_mem hu)
  have h3 := eq_one_of_mem_rootGroup_single_of_mem_posUnipotentExcept hct hext i
    (mul_mem (inv_mem hz) h1) h2
  have huz : u * z * u⁻¹ = z := by
    calc u * z * u⁻¹ = z * (z⁻¹ * (u * z * u⁻¹)) := by group
      _ = z := by rw [h3, mul_one]
  rw [hsplit, huz]

theorem exists_torus_conj_of_mem_ggTorus
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank)
    (hcomm : ∀ y ∈ D.rootGroup (Pi.single i 1), ∀ z ∈ D.rootGroup (Pi.single i 1),
      y * z = z * y)
    {h : K} (hh : h ∈ ggTorus D) :
    ∃ t ∈ ⨆ j, H j, ∀ z ∈ D.rootGroup (Pi.single i 1), h * z * h⁻¹ = t * z * t⁻¹ := by
  refine exists_torus_conj_of_mem_borel hct hext i hcomm (mem_borel_of_mem_ggTorus hct hext hh) ?_
  simp only [ggTorus, Subgroup.mem_iInf] at hh
  exact hh _ (single_mem_roots i)

theorem mul_comm_of_mem_range {A : Type*} [CommGroup A] (f : A →* K) {y z : K}
    (hy : y ∈ f.range) (hz : z ∈ f.range) : y * z = z * y := by
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  rw [← map_mul, mul_comm, map_mul]

@[expose] def rankOneRelsMap {G G' : Type*} [Group G] [Group G'] {k : Type*} [Field k]
    (R : RankOneRels G k) (ψ : G →* G') : RankOneRels G' k where
  x a := ψ (R.x a)
  y a := ψ (R.y a)
  x_add a b := by rw [R.x_add, map_mul]
  y_add a b := by rw [R.y_add, map_mul]
  conj_x t ht a := by
    have h := congrArg ψ (R.conj_x t ht a)
    simpa only [map_mul, map_inv] using h

theorem rankOneRelsMap_x {G G' : Type*} [Group G] [Group G'] {k : Type*} [Field k]
    (R : RankOneRels G k) (ψ : G →* G') (a : k) : (rankOneRelsMap R ψ).x a = ψ (R.x a) :=
  rfl

theorem rankOneRelsMap_y {G G' : Type*} [Group G] [Group G'] {k : Type*} [Field k]
    (R : RankOneRels G k) (ψ : G →* G') (a : k) : (rankOneRelsMap R ψ).y a = ψ (R.y a) :=
  rfl

theorem eq_of_conj_rankOneRels {G : Type*} [Group G] {F : Type*} [Field F] (R : RankOneRels G F)
    (hy : Function.Injective R.y)
    (hE7 : ∀ s, (∀ b, ∃ b', R.x s * R.y b * (R.x s)⁻¹ = R.y b') → s = 0)
    {d : G} {φ : F → F} (hu : ∀ a, d⁻¹ * R.x a * d = R.x a)
    (hl : ∀ a, d⁻¹ * R.y a * d = R.y (φ a)) (a : F) : φ a = a := by
  have hxc : ∀ u a, R.x u * R.x a * (R.x u)⁻¹ = R.x a := fun u a => by
    rw [← R.x_add, ← R.x_neg, ← R.x_add, add_comm u a, add_neg_cancel_right]
  obtain ⟨e, he⟩ : ∃ e, e = φ (-1) := ⟨_, rfl⟩
  have hw : d⁻¹ * R.w 1 * d = R.x 1 * R.y e * R.x 1 := by
    rw [R.w_def, inv_one]
    calc d⁻¹ * (R.x 1 * R.y (-1) * R.x 1) * d =
        (d⁻¹ * R.x 1 * d) * (d⁻¹ * R.y (-1) * d) * (d⁻¹ * R.x 1 * d) := by group
      _ = R.x 1 * R.y e * R.x 1 := by rw [hu, hl, he]
  have key : ∀ a, (R.x 1 * R.y e * R.x 1) * R.x a * (R.x 1 * R.y e * R.x 1)⁻¹ =
      R.y (φ (-a)) := by
    intro a
    have h := R.w_conj_x one_ne_zero a
    rw [one_pow, inv_one, neg_one_mul] at h
    calc (R.x 1 * R.y e * R.x 1) * R.x a * (R.x 1 * R.y e * R.x 1)⁻¹ =
        (d⁻¹ * R.w 1 * d) * (d⁻¹ * R.x a * d) * (d⁻¹ * R.w 1 * d)⁻¹ := by rw [hw, hu]
      _ = d⁻¹ * (R.w 1 * R.x a * (R.w 1)⁻¹) * d := by group
      _ = d⁻¹ * R.y (-a) * d := by rw [h]
      _ = R.y (φ (-a)) := hl _
  have he1 : e = -1 := by
    by_cases he0 : e = 0
    · exfalso
      have h1 : R.x 1 = 1 := by
        have h := key 1
        rw [← he, he0, R.y_zero] at h
        calc R.x 1 = R.x 1 * 1 * R.x 1 * R.x 1 * (R.x 1 * 1 * R.x 1)⁻¹ := by group
          _ = 1 := h
      exact one_ne_zero (hE7 1 fun b => ⟨b, by rw [h1]; group⟩)
    · have ht : -e⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero he0)
      have hye : R.y e = (R.x (-e⁻¹))⁻¹ * R.w (-e⁻¹) * (R.x (-e⁻¹))⁻¹ := by
        rw [R.w_def, inv_neg, inv_inv, neg_neg]
        group
      have hxs : R.x 1 * (R.x (-e⁻¹))⁻¹ = R.x (1 + e⁻¹) := by
        rw [← R.x_neg, neg_neg, ← R.x_add]
      have hxs' : (R.x (-e⁻¹))⁻¹ * R.x 1 = R.x (1 + e⁻¹) := by
        rw [← R.x_neg, neg_neg, ← R.x_add, add_comm]
      have h1 : ∀ a, R.x (1 + e⁻¹) * R.y (-((-e⁻¹) ^ 2)⁻¹ * a) * (R.x (1 + e⁻¹))⁻¹ =
          R.y (φ (-a)) := by
        intro a
        rw [← key a, ← R.w_conj_x ht a, hye]
        calc R.x (1 + e⁻¹) * (R.w (-e⁻¹) * R.x a * (R.w (-e⁻¹))⁻¹) * (R.x (1 + e⁻¹))⁻¹
            = R.x (1 + e⁻¹) * R.w (-e⁻¹) * (R.x (1 + e⁻¹) * R.x a * (R.x (1 + e⁻¹))⁻¹) *
                (R.w (-e⁻¹))⁻¹ * (R.x (1 + e⁻¹))⁻¹ := by rw [hxc]; group
          _ = (R.x 1 * (R.x (-e⁻¹))⁻¹) * R.w (-e⁻¹) *
                ((R.x (-e⁻¹))⁻¹ * R.x 1 * R.x a * ((R.x (-e⁻¹))⁻¹ * R.x 1)⁻¹) *
                (R.w (-e⁻¹))⁻¹ * (R.x 1 * (R.x (-e⁻¹))⁻¹)⁻¹ := by rw [hxs, hxs']
          _ = R.x 1 * ((R.x (-e⁻¹))⁻¹ * R.w (-e⁻¹) * (R.x (-e⁻¹))⁻¹) * R.x 1 * R.x a *
                (R.x 1 * ((R.x (-e⁻¹))⁻¹ * R.w (-e⁻¹) * (R.x (-e⁻¹))⁻¹) * R.x 1)⁻¹ := by group
      have hs : 1 + e⁻¹ = 0 := by
        refine hE7 _ fun b => ⟨φ (-(-((-e⁻¹) ^ 2) * b)), ?_⟩
        rw [← h1]
        congr 3
        have ht2 : (-e⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 ht
        field_simp
      have hinv : e⁻¹ = -1 := by linear_combination hs
      rw [← inv_inv e, hinv, inv_neg, inv_one]
  have hfix : ∀ a, φ (-a) = -a := by
    intro a
    apply hy
    have hw1 : R.x 1 * R.y (-1) * R.x 1 = R.w 1 := by rw [R.w_def, inv_one]
    rw [← key a, he1, hw1]
    have h := R.w_conj_x one_ne_zero a
    rw [one_pow, inv_one, neg_one_mul] at h
    exact h
  simpa using hfix (-a)

theorem mem_centralizer_of_fix_simple
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) {G : Type*} [Group G] (ψ : K →* G) {d : G}
    (hpos : ∀ i, ∀ z ∈ D.rootGroup (Pi.single i 1), d⁻¹ * ψ z * d = ψ z)
    (hneg : ∀ i, ∀ z ∈ D.rootGroup (-Pi.single i 1), d⁻¹ * ψ z * d = ψ z) :
    d ∈ Subgroup.centralizer (ψ.range : Set G) := by
  set S := (Subgroup.centralizer ({d} : Set G)).comap ψ with hS
  have hR : ∀ i, rankOne D.rootGroup i ≤ S := fun i =>
    sup_le (fun z hz => (mem_fix_iff ψ).mpr (hpos i z hz))
      (fun z hz => (mem_fix_iff ψ).mpr (hneg i z hz))
  have hnrep : ∀ w, nrep hct w ∈ S := by
    intro w
    obtain ⟨ω, hω, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
    rw [nrep_wordProd hct hω]
    refine S.list_prod_mem fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact hR i (hct.n_mem i)
  have hall : ∀ γ ∈ D.roots, D.rootGroup γ ≤ S := by
    rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩)
    · rw [← actsAs_nrep hct w _ (single_mem_roots j)]
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem (hnrep w) ((mem_fix_iff ψ).mpr (hpos j z hz))) (inv_mem (hnrep w))
    · rw [hdiv] at hj
      exact absurd hj (Set.notMem_empty j)
  have htop : (⊤ : Subgroup K) ≤ S := by
    rw [← hct.iSup_eq_top]
    exact iSup₂_le hall
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (htop (Subgroup.mem_top z)))

end PsiDiag

end CFSG.StandardType
