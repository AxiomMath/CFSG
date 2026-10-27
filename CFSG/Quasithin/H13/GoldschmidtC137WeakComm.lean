module

public import CFSG.Quasithin.H13.GoldschmidtC137WeakAux
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

section PartIII

variable [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem commutator_alpha_le' (hVN : V.Normal) {M I : Subgroup G} (hVR : V ≤ R)
    (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ A, ¬ IsStrongFFOffender hV R A)
    (hM : M ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hI : I = ⨆ g ∈ M, cjSub g (thompsonJ R)) :
    ∀ x ∈ omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))), ∀ i ∈ I,
      x * i * x⁻¹ * i⁻¹ ∈ V := by
  have hfacts := alpha_facts' hV hVR hRN hc
  have : V.Normal := hVN
  set Q := R ⊓ Subgroup.centralizer (V : Set G) with hQ
  set α' := omegaOneCenterOf (thompsonJ Q) with hα'
  let π : G →* G ⧸ V := QuotientGroup.mk' V
  have hπ1 : ∀ v : G, π v = 1 ↔ v ∈ V := fun v => QuotientGroup.eq_one_iff v
  have hαM : ∀ g ∈ M, g ∈ Subgroup.normalizer (α' : Set G) := fun g hg =>
    normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf (thompsonJ X))
      (fun φ X => by rw [omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]) Q (hM hg)
  have hJ1 : ∀ x ∈ α', thompsonJ R ≤
      (Subgroup.centralizer ({π x} : Set (G ⧸ V))).comap π := by
    intro x hx
    refine iSup_le fun A => iSup_le fun hA a ha => ?_
    obtain ⟨c, hc', v, hv, hcv⟩ := Subgroup.mem_sup_of_normal_right.1 (hfacts.2.2.2 A hA hx)
    have hπx : π x = π c := by
      rw [← hcv, map_mul, (hπ1 v).2 hv, mul_one]
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, hπx, ← map_mul, ← map_mul, isElemAbelian_comm hA.2.1 hc'.1 ha]
  let P : Subgroup G := ⨅ x ∈ α', (Subgroup.centralizer ({π x} : Set (G ⧸ V))).comap π
  have hJP : ∀ g ∈ M, cjSub g (thompsonJ R) ≤ P := by
    intro g hg y hy
    simp only [P, Subgroup.mem_iInf]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hx' : g⁻¹ * x * g ∈ α' := by
      have : x ∈ cjSub g α' := by
        rw [cjSub_eq_of_mem_normalizer (hαM g hg)]
        exact hx
      exact mem_cjSub.1 this
    have hj : g⁻¹ * y * g ∈ thompsonJ R := mem_cjSub.1 hy
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 (hJ1 _ hx' hj)) _ rfl
    calc π x * π y = π g * (π (g⁻¹ * x * g) * π (g⁻¹ * y * g)) * (π g)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = π g * (π (g⁻¹ * y * g) * π (g⁻¹ * x * g)) * (π g)⁻¹ := by rw [h1]
      _ = π y * π x := by
          simp only [map_mul, map_inv]
          group
  have hIP : I ≤ P := by
    rw [hI]
    exact iSup₂_le hJP
  intro x hx i hi
  have h1 := Subgroup.mem_centralizer_iff.1
    (Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hIP hi) x) hx)) (π x) rfl
  have h2 : π (x * i * x⁻¹ * i⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h1]
    group
  exact (hπ1 _).1 h2

end PartIII

end B2F

end CFSG.Quasithin
