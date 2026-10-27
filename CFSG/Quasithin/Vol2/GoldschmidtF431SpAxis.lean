module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.H13.F431

open scoped commutatorElement

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique.Setup.X7b

section Axis

variable {G : Type*} [Group G] {K : Type} [Field K] {U A : Subgroup G} {s : SL₂ K →* G}
  {d : Kˣ →* G} {coord : K → G} {vec : G → Fin 2 → K}

theorem axis_d_mem_N (hS : RootAxisStructure U A s d coord vec) (l : Kˣ) :
    d l ∈ Subgroup.normalizer (U : Set G) := by
  have := hS.ds_mem_N l 1
  rwa [map_one, mul_one] at this

theorem centralizer_conj_mem {n c : G} (hn : n ∈ Subgroup.normalizer (U : Set G))
    (hc : c ∈ Subgroup.centralizer (U : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro u hu
  have hu' : n⁻¹ * u * n ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) u).mp hu
    simpa using this
  have := hc _ hu'
  calc u * (n * c * n⁻¹) = n * ((n⁻¹ * u * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * u * n)) * n⁻¹ := by rw [this]
    _ = n * c * n⁻¹ * u := by group

theorem axis_exists_mul_d (hS : RootAxisStructure U A s d coord vec) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    ∃ c ∈ Subgroup.centralizer (U : Set G), ∃ l : Kˣ, g = c * d l := by
  obtain ⟨a, ha, l, M, rfl⟩ := hS.N_decomp g hg
  refine ⟨a * s M, ?_, l, ?_⟩
  · exact Subgroup.mul_mem _ (hS.A_le_C ha) (hS.s_mem_C M)
  · rw [mul_assoc, ← hS.s_comm_d M l]

theorem axis_commutator_normalizer_le (hS : RootAxisStructure U A s d coord vec) :
    ⁅Subgroup.normalizer (U : Set G), Subgroup.normalizer (U : Set G)⁆ ≤
      Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.commutator_def]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, h, hh, rfl⟩
  obtain ⟨c₁, hc₁, l₁, rfl⟩ := axis_exists_mul_d hS hg
  obtain ⟨c₂, hc₂, l₂, rfl⟩ := axis_exists_mul_d hS hh
  have hd : d l₁ * d l₂ = d l₂ * d l₁ := by
    rw [← map_mul, ← map_mul, mul_comm]
  set δ₁ := d l₁ with hδ₁
  set δ₂ := d l₂ with hδ₂
  have e1 : c₁ * δ₁ * (c₂ * δ₂) = c₁ * (δ₁ * c₂ * δ₁⁻¹) * (δ₁ * δ₂) := by group
  have e2 : c₂ * δ₂ * (c₁ * δ₁) = c₂ * (δ₂ * c₁ * δ₂⁻¹) * (δ₁ * δ₂) := by
    rw [hd]
    group
  have e3 : ⁅c₁ * δ₁, c₂ * δ₂⁆ = (c₁ * δ₁ * (c₂ * δ₂)) * (c₂ * δ₂ * (c₁ * δ₁))⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e3, e1, e2]
  have hδ₁N := axis_d_mem_N hS l₁
  have hδ₂N := axis_d_mem_N hS l₂
  have h1 := centralizer_conj_mem hδ₁N hc₂
  have h2 := centralizer_conj_mem hδ₂N hc₁
  have : c₁ * (δ₁ * c₂ * δ₁⁻¹) * (δ₁ * δ₂) * (c₂ * (δ₂ * c₁ * δ₂⁻¹) * (δ₁ * δ₂))⁻¹ =
      c₁ * (δ₁ * c₂ * δ₁⁻¹) * (c₂ * (δ₂ * c₁ * δ₂⁻¹))⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁ h1)
    (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc₂ h2))

theorem axis_perfectCore_normalizer (hS : RootAxisStructure U A s d coord vec) :
    perfectCore (Subgroup.normalizer (A : Set G)) = Subgroup.centralizer (U : Set G) := by
  rw [← hS.N_eq]
  apply le_antisymm
  · exact (perfectCore_le_derivedSeriesOf _ 1).trans (axis_commutator_normalizer_le hS)
  · exact le_perfectCore_of_perfect (Subgroup.centralizer_le_normalizer _)
      (Subgroup.isPerfect_iff.mp hS.C_perfect)

theorem axis_centerOf_centralizer (hS : RootAxisStructure U A s d coord vec)
    (hUA : U ≤ A) (hK : 2 < Nat.card K) :
    centerOf (Subgroup.centralizer (U : Set G)) = U := by
  apply le_antisymm
  · rintro z ⟨hzC, hzc⟩
    have hzc' : ∀ c ∈ Subgroup.centralizer (U : Set G), c * z = z * c := fun c hc =>
      Subgroup.mem_centralizer_iff.mp hzc c hc
    obtain ⟨a, ha, M, rfl⟩ := hS.C_decomp z hzC
    have hM : M = 1 := by
      have hMc : M ∈ Subgroup.center (SL₂ K) := by
        rw [Subgroup.mem_center_iff]
        intro M'
        have h1 := hzc' (s M') (hS.s_mem_C M')
        have h2 : s M' * (a * s M) = (s M' * a * (s M')⁻¹) * s (M' * M) := by
          rw [map_mul]
          group
        have h3 : a * s M * s M' = a * s (M * M') := by rw [mul_assoc, ← map_mul]
        rw [h2, h3] at h1
        have hA' : s M' * a * (s M')⁻¹ ∈ A := hS.A_normal_C _ (hS.s_mem_C M') a ha
        exact (hS.C_unique _ hA' a ha _ _ (by rw [h1])).2
      rw [hS.S_center, Subgroup.mem_bot] at hMc
      exact hMc
    subst hM
    rw [map_one, mul_one]
    have hvec : ∀ M' : SL₂ K, (M' : Matrix (Fin 2) (Fin 2) K) *ᵥ vec a = vec a := by
      intro M'
      have h1 := hzc' (s M') (hS.s_mem_C M')
      rw [map_one, mul_one] at h1
      have h2 : s M' * a * (s M')⁻¹ = a := by
        rw [mul_inv_eq_iff_eq_mul]
        exact h1
      rw [← hS.vec_conj M' a ha, h2]
    have hv0 : vec a = 0 := by
      by_contra hv
      obtain ⟨c₁, hc₀, hc₁⟩ := exists_ne_zero_ne hK 1
      have hw : c₁ • vec a ≠ 0 := fun h => hv (by
        have := smul_eq_zero.mp h
        exact this.resolve_left hc₀)
      obtain ⟨M', hM'⟩ := exists_sl2_mulVec_eq hv hw
      have := hvec M'
      rw [hM'] at this
      apply hv
      have h2 : (c₁ - 1) • vec a = 0 := by
        rw [sub_smul, this, one_smul, sub_self]
      exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm hc₁))
    exact (hS.vec_ker a ha).mp hv0
  · intro u hu
    refine ⟨hS.A_le_C (hUA hu), ?_⟩
    show u ∈ Subgroup.centralizer ((Subgroup.centralizer (U : Set G) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc u hu).symm

theorem axis_exists_normalizer_conj [Finite K] [CharP K 2]
    (hS : RootAxisStructure U A s d coord vec) (h0 : coord 0 = 1) {x y : G} (hx : x ∈ U)
    (hy : y ∈ U) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ m ∈ Subgroup.normalizer (A : Set G), m * x * m⁻¹ = y := by
  obtain ⟨a, rfl⟩ := hS.coord_surj x hx
  obtain ⟨b, rfl⟩ := hS.coord_surj y hy
  have ha : a ≠ 0 := fun h => hx1 (by rw [h, h0])
  have hb : b ≠ 0 := fun h => hy1 (by rw [h, h0])
  obtain ⟨r, hr⟩ := exists_sq_eq (b * a⁻¹)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : b * a⁻¹ = 0 := by rw [← hr]; ring
    exact mul_ne_zero hb (inv_ne_zero ha) this
  refine ⟨d (Units.mk0 r hr0), ?_, ?_⟩
  · rw [← hS.N_eq]
    exact axis_d_mem_N hS _
  · rw [hS.d_coord]
    congr 1
    rw [Units.val_mk0, hr, mul_assoc, inv_mul_cancel₀ ha, mul_one]

omit [Field K] in
theorem unit_eq_one_of_sq_eq_one [Field K] [CharP K 2] {l : Kˣ} (h : (l : K) ^ 2 = 1) :
    l = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : ((l : K) - 1) ^ 2 = 0 := by linear_combination h + (1 - (l : K)) * h2
  exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

theorem axis_pCoreOf_centralizer_singleton [CharP K 2]
    (hS : RootAxisStructure U A s d coord vec) (hinj : Function.Injective coord)
    (hcent : Subgroup.centralizer ({coord 1} : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    pCoreOf 2 (Subgroup.centralizer ({coord 1} : Set G)) = A := by
  have hC : Subgroup.centralizer ({coord 1} : Set G) = Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨c, hc, l, rfl⟩ := axis_exists_mul_d hS (hcent hg)
      have hg' : c * d l * coord 1 = coord 1 * (c * d l) :=
        Subgroup.mem_centralizer_singleton_iff.mp hg
      have h1 : c * d l * coord 1 * (c * d l)⁻¹ = coord 1 := by
        rw [hg']
        group
      have h2 : c * d l * coord 1 * (c * d l)⁻¹ = coord ((l : K) ^ 2 * 1) := by
        have hcc : c * coord ((l : K) ^ 2 * 1) * c⁻¹ = coord ((l : K) ^ 2 * 1) := by
          rw [mul_inv_eq_iff_eq_mul]
          exact (Subgroup.mem_centralizer_iff.mp hc _ (hS.coord_mem _)).symm
        calc c * d l * coord 1 * (c * d l)⁻¹
            = c * (d l * coord 1 * (d l)⁻¹) * c⁻¹ := by group
          _ = coord ((l : K) ^ 2 * 1) := by rw [hS.d_coord, hcc]
      have h3 := hinj (h2.symm.trans h1)
      have hl : l = 1 := unit_eq_one_of_sq_eq_one (by simpa using h3)
      subst hl
      simpa using hc
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hS.coord_mem 1))
  rw [hC]
  have hAC : A ≤ Subgroup.centralizer (U : Set G) := hS.A_le_C
  unfold pCoreOf
  rw [hS.C_pCore]
  exact Subgroup.map_subgroupOf_eq_of_le hAC

end Axis

end CFSG.Quasithin.H13.F431
