module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private abbrev a8nrGL : Type := GGSL9V ≃ₗ[ZMod 2] GGSL9V

private theorem a8nr_exists_inducing {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) :
    ∃ n : ↥K, ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (n : G) * (b : G) * (n : G)⁻¹ := by
  obtain ⟨g, hgK, _, hg⟩ := mem_ggAutomizer_iff.mp φ.2
  exact ⟨⟨g, hgK⟩, hg⟩

private noncomputable def a8nr_inducing {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) : ↥K :=
  Classical.choose (a8nr_exists_inducing (Bs := Bs) (K := K) φ)

private theorem a8nr_inducing_spec {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) :
    ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (a8nr_inducing (Bs := Bs) (K := K) φ : G) * (b : G) *
        (a8nr_inducing (Bs := Bs) (K := K) φ : G)⁻¹ :=
  Classical.choose_spec (a8nr_exists_inducing (Bs := Bs) (K := K) φ)

private theorem a8nr_inducing_mem_normalizer {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) :
    (a8nr_inducing (Bs := Bs) (K := K) φ : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  let n : ↥K := a8nr_inducing (Bs := Bs) (K := K) φ
  have hn : ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (n : G) * (b : G) * (n : G)⁻¹ := a8nr_inducing_spec (Bs := Bs) (K := K) φ
  rw [mem_normalizer_iff_map_conj]
  apply le_antisymm
  · rintro x ⟨b, hb, rfl⟩
    change MulAut.conj (n : G) b ∈ Bs
    rw [MulAut.conj_apply, ← hn ⟨b, hb⟩]
    exact (((φ : MulAut ↥Bs) ⟨b, hb⟩ : ↥Bs)).2
  · intro b hb
    refine ⟨(((φ : MulAut ↥Bs)⁻¹ ⟨b, hb⟩ : ↥Bs) : G),
      (((φ : MulAut ↥Bs)⁻¹ ⟨b, hb⟩ : ↥Bs)).2, ?_⟩
    change MulAut.conj (n : G) (((φ : MulAut ↥Bs)⁻¹ ⟨b, hb⟩ : ↥Bs) : G) = b
    rw [MulAut.conj_apply, ← hn ((φ : MulAut ↥Bs)⁻¹ ⟨b, hb⟩)]
    rw [MulAut.apply_inv_self]

private theorem a8nr_e_mem_E {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (f : Multiplicative (Fin 3 → ZMod 7)) :
    ρ.symm (ggSL9TorusCoord f) ∈ (Bs ⊓ K).subgroupOf K := by
  have hmem : ggSL9TorusCoord f ∈ ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom := by
    rw [hρ, ← range_ggSL9TorusCoord]
    exact MonoidHom.mem_range.mpr ⟨f, rfl⟩
  obtain ⟨y, hy, hyρ⟩ := Subgroup.mem_map.mp hmem
  have hsymm : ρ.symm (ggSL9TorusCoord f) = y := by
    rw [← hyρ]
    exact MulEquiv.symm_apply_apply ρ y
  rw [hsymm]
  exact hy

private theorem a8nr_conj_mem_E {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) {e : ↥K}
    (he : e ∈ (Bs ⊓ K).subgroupOf K) :
    a8nr_inducing (Bs := Bs) (K := K) φ * e *
      (a8nr_inducing (Bs := Bs) (K := K) φ)⁻¹ ∈ (Bs ⊓ K).subgroupOf K := by
  let n : ↥K := a8nr_inducing (Bs := Bs) (K := K) φ
  have hnBs : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    a8nr_inducing_mem_normalizer (Bs := Bs) (K := K) φ
  rw [Subgroup.mem_subgroupOf] at he ⊢
  refine ⟨?_, K.mul_mem (K.mul_mem n.2 e.2) (K.inv_mem n.2)⟩
  simpa using (Subgroup.mem_normalizer_iff.mp hnBs (e : G)).mp he.1

private theorem a8nr_inv_conj_mem_E {G : Type} [Group G] {Bs K : Subgroup G}
    (φ : ↥(ggAutomizer K Bs)) {e : ↥K}
    (he : e ∈ (Bs ⊓ K).subgroupOf K) :
    (a8nr_inducing (Bs := Bs) (K := K) φ)⁻¹ * e *
      a8nr_inducing (Bs := Bs) (K := K) φ ∈ (Bs ⊓ K).subgroupOf K := by
  let n : ↥K := a8nr_inducing (Bs := Bs) (K := K) φ
  have hnBs : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    a8nr_inducing_mem_normalizer (Bs := Bs) (K := K) φ
  rw [Subgroup.mem_subgroupOf] at he ⊢
  refine ⟨?_, K.mul_mem (K.mul_mem (K.inv_mem n.2) e.2) n.2⟩
  simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnBs) (e : G)).mp he.1

private theorem a8nr_rho_mem_normalizer {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) :
    ρ (a8nr_inducing (Bs := Bs) (K := K) φ) ∈
      Subgroup.normalizer (ggSL9Torus : Set a8nrGL) := by
  let n : ↥K := a8nr_inducing (Bs := Bs) (K := K) φ
  rw [mem_normalizer_iff_map_conj]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom := by
      rw [hρ]
      exact hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy'
    change MulAut.conj (ρ n) (ρ e) ∈ ggSL9Torus
    rw [show MulAut.conj (ρ n) (ρ e) = ρ (MulAut.conj n e) by
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]]
    rw [← hρ]
    exact Subgroup.mem_map.mpr ⟨MulAut.conj n e, a8nr_conj_mem_E φ he, rfl⟩
  · intro y hy
    have hy' : y ∈ ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom := by
      rw [hρ]
      exact hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hy'
    change ρ e ∈ ggSL9Torus.map (MulAut.conj (ρ n)).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨ρ (n⁻¹ * e * n), ?_, ?_⟩
    · rw [← hρ]
      exact Subgroup.mem_map.mpr ⟨n⁻¹ * e * n, a8nr_inv_conj_mem_E φ he, rfl⟩
    · change MulAut.conj (ρ n) (ρ (n⁻¹ * e * n)) = ρ e
      simp only [MulAut.conj_apply, map_mul, map_inv]
      group

private theorem a8nr_conj_eq_of_inducing {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) (n m : ↥K)
    (hn : ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (n : G) * (b : G) * (n : G)⁻¹)
    (hm : ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (m : G) * (b : G) * (m : G)⁻¹)
    (f : Multiplicative (Fin 3 → ZMod 7)) :
    ρ (n * ρ.symm (ggSL9TorusCoord f) * n⁻¹) =
      ρ (m * ρ.symm (ggSL9TorusCoord f) * m⁻¹) := by
  let e : ↥K := ρ.symm (ggSL9TorusCoord f)
  have heE : e ∈ (Bs ⊓ K).subgroupOf K := a8nr_e_mem_E hρ f
  have heBs : (e : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp heE).1
  have hK : (((φ : MulAut ↥Bs) ⟨(e : G), heBs⟩ : ↥Bs) : G) ∈ K := by
    rw [hn ⟨(e : G), heBs⟩]
    simpa using K.mul_mem (K.mul_mem n.2 e.2) (K.inv_mem n.2)
  let z : ↥K := ⟨(((φ : MulAut ↥Bs) ⟨(e : G), heBs⟩ : ↥Bs) : G), hK⟩
  have hzn : z = n * e * n⁻¹ := by
    apply Subtype.ext
    show (((φ : MulAut ↥Bs) ⟨(e : G), heBs⟩ : ↥Bs) : G) = ((n * e * n⁻¹ : ↥K) : G)
    rw [hn ⟨(e : G), heBs⟩]
    simp
  have hzm : z = m * e * m⁻¹ := by
    apply Subtype.ext
    show (((φ : MulAut ↥Bs) ⟨(e : G), heBs⟩ : ↥Bs) : G) = ((m * e * m⁻¹ : ↥K) : G)
    rw [hm ⟨(e : G), heBs⟩]
    simp
  rw [← hzn, ← hzm]

private noncomputable def a8nr_coordEquiv :
    Multiplicative (Fin 3 → ZMod 7) ≃* ↥ggSL9Torus :=
  (MonoidHom.ofInjective ggSL9TorusCoord_injective).trans
    (MulEquiv.subgroupCongr range_ggSL9TorusCoord)

private theorem a8nr_coordEquiv_apply (f : Multiplicative (Fin 3 → ZMod 7)) :
    ((a8nr_coordEquiv f : ↥ggSL9Torus) : a8nrGL) = ggSL9TorusCoord f := rfl

private theorem a8nr_coordEquiv_symm_apply (x : ↥ggSL9Torus) :
    ggSL9TorusCoord (a8nr_coordEquiv.symm x) = (x : a8nrGL) := by
  have h := congrArg (fun y : ↥ggSL9Torus => (y : a8nrGL))
    (a8nr_coordEquiv.apply_symm_apply x)
  rwa [a8nr_coordEquiv_apply] at h

private noncomputable def a8nr_torusConj {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) : ↥ggSL9Torus ≃* ↥ggSL9Torus where
  toFun x := ⟨MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ)) (x : a8nrGL),
    (Subgroup.mem_normalizer_iff.mp (a8nr_rho_mem_normalizer hρ φ)
      (x : a8nrGL)).1 x.2⟩
  invFun x := ⟨(MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ)))⁻¹ (x : a8nrGL),
    (Subgroup.mem_normalizer_iff.mp (a8nr_rho_mem_normalizer hρ φ)
      ((MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ)))⁻¹ (x : a8nrGL))).2 (by
        change MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ))
          ((MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ)))⁻¹ (x : a8nrGL)) ∈
            ggSL9Torus
        rw [MulAut.apply_inv_self]
        exact x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

private theorem a8nr_torusConj_apply {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) (x : ↥ggSL9Torus) :
    ((a8nr_torusConj hρ φ x : ↥ggSL9Torus) : a8nrGL) =
      ρ (a8nr_inducing (Bs := Bs) (K := K) φ) * (x : a8nrGL) *
        (ρ (a8nr_inducing (Bs := Bs) (K := K) φ))⁻¹ := by
  change MulAut.conj (ρ (a8nr_inducing (Bs := Bs) (K := K) φ)) (x : a8nrGL) =
    ρ (a8nr_inducing (Bs := Bs) (K := K) φ) * (x : a8nrGL) *
      (ρ (a8nr_inducing (Bs := Bs) (K := K) φ))⁻¹
  rw [MulAut.conj_apply]

private noncomputable def a8nr_actAut {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) :
    MulAut (Multiplicative (Fin 3 → ZMod 7)) :=
  (a8nr_coordEquiv.trans (a8nr_torusConj hρ φ)).trans a8nr_coordEquiv.symm

private theorem a8nr_actAut_apply_spec {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ : ↥(ggAutomizer K Bs)) (n : ↥K)
    (hn : ∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) =
      (n : G) * (b : G) * (n : G)⁻¹)
    (f : Multiplicative (Fin 3 → ZMod 7)) :
    ggSL9TorusCoord (a8nr_actAut hρ φ f) =
      ρ (n * ρ.symm (ggSL9TorusCoord f) * n⁻¹) := by
  change ggSL9TorusCoord (a8nr_coordEquiv.symm
    (a8nr_torusConj hρ φ (a8nr_coordEquiv f))) =
      ρ (n * ρ.symm (ggSL9TorusCoord f) * n⁻¹)
  rw [a8nr_coordEquiv_symm_apply, a8nr_torusConj_apply, a8nr_coordEquiv_apply]
  rw [show ρ (a8nr_inducing (Bs := Bs) (K := K) φ) * ggSL9TorusCoord f *
      (ρ (a8nr_inducing (Bs := Bs) (K := K) φ))⁻¹ =
      ρ (a8nr_inducing (Bs := Bs) (K := K) φ * ρ.symm (ggSL9TorusCoord f) *
        (a8nr_inducing (Bs := Bs) (K := K) φ)⁻¹) by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]]
  exact a8nr_conj_eq_of_inducing hρ φ (a8nr_inducing (Bs := Bs) (K := K) φ) n
    (a8nr_inducing_spec (Bs := Bs) (K := K) φ) hn f

private theorem a8nr_inducing_mul_spec {G : Type} [Group G] {Bs K : Subgroup G}
    (φ ψ : ↥(ggAutomizer K Bs)) :
    ∀ b : ↥Bs, ((((φ * ψ : ↥(ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) =
      ((a8nr_inducing (Bs := Bs) (K := K) φ * a8nr_inducing (Bs := Bs) (K := K) ψ :
        ↥K) : G) * (b : G) *
        ((a8nr_inducing (Bs := Bs) (K := K) φ * a8nr_inducing (Bs := Bs) (K := K) ψ :
          ↥K) : G)⁻¹ := by
  intro b
  rw [show (((φ * ψ : ↥(ggAutomizer K Bs)) : MulAut ↥Bs)) =
      (φ : MulAut ↥Bs) * (ψ : MulAut ↥Bs) from rfl, MulAut.mul_apply,
    a8nr_inducing_spec (Bs := Bs) (K := K) φ ((ψ : MulAut ↥Bs) b),
    a8nr_inducing_spec (Bs := Bs) (K := K) ψ b]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

private theorem a8nr_actAut_mul {G : Type} [Group G] {Bs K : Subgroup G}
    {ρ : ↥K ≃* a8nrGL}
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus)
    (φ ψ : ↥(ggAutomizer K Bs)) :
    a8nr_actAut hρ (φ * ψ) = a8nr_actAut hρ φ * a8nr_actAut hρ ψ := by
  apply MulEquiv.ext
  intro f
  apply ggSL9TorusCoord_injective
  rw [a8nr_actAut_apply_spec hρ (φ * ψ)
      (a8nr_inducing (Bs := Bs) (K := K) φ * a8nr_inducing (Bs := Bs) (K := K) ψ)
      (a8nr_inducing_mul_spec φ ψ) f]
  rw [MulAut.mul_apply]
  rw [a8nr_actAut_apply_spec hρ φ (a8nr_inducing (Bs := Bs) (K := K) φ)
      (a8nr_inducing_spec (Bs := Bs) (K := K) φ) (a8nr_actAut hρ ψ f)]
  rw [a8nr_actAut_apply_spec hρ ψ (a8nr_inducing (Bs := Bs) (K := K) ψ)
      (a8nr_inducing_spec (Bs := Bs) (K := K) ψ) f]
  simp only [MulEquiv.symm_apply_apply]
  congr 1
  group

theorem ggA8NR_actHom {G : Type} [Group G] {Bs K : Subgroup G}
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V))
    (hρ : ((Bs ⊓ K).subgroupOf K).map ρ.toMonoidHom = ggSL9Torus) :
    ∃ act : ↥(ggAutomizer K Bs) →* MulAut (Multiplicative (Fin 3 → ZMod 7)),
      ∀ (φ : ↥(ggAutomizer K Bs)) (n : ↥K),
        (∀ b : ↥Bs, (((φ : MulAut ↥Bs) b : ↥Bs) : G) = (n : G) * (b : G) * (n : G)⁻¹) →
        ∀ f : Multiplicative (Fin 3 → ZMod 7),
          ρ (n * ρ.symm (ggSL9TorusCoord f) * n⁻¹) = ggSL9TorusCoord (act φ f) := by
  refine ⟨MonoidHom.mk' (a8nr_actAut hρ) (a8nr_actAut_mul hρ), ?_⟩
  intro φ n hn f
  exact (a8nr_actAut_apply_spec hρ φ n hn f).symm

end CFSG.StandardType

end
