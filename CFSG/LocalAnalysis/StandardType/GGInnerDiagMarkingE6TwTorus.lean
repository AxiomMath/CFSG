module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6Tw
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerBorel
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionTwistedE6

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

namespace InnerDiagTwE6

section Generic

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_torus_conj_of_mem_ggTorus
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (i : Fin D.rank)
    (hcomm : ∀ x ∈ D.rootGroup (Pi.single i 1), ∀ y ∈ D.rootGroup (Pi.single i 1),
      x * y = y * x) {h : K} (hh : h ∈ ggTorus D) :
    ∃ t ∈ ⨆ j, H j, ∀ z ∈ D.rootGroup (Pi.single i 1), h * z * h⁻¹ = t * z * t⁻¹ := by
  have hN : h ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh
    exact hh _ (single_mem_roots i)
  obtain ⟨t, ht, u, hu, y, hy, rfl⟩ :=
    exists_eq_mul_mul_of_mem_borel hct hext i (PsiDiag.mem_borel_of_mem_ggTorus hct hext hh)
  refine ⟨t, ht, fun z hz => ?_⟩
  have hyz : y * z * y⁻¹ = z := by
    rw [hcomm y hy z hz, mul_inv_cancel_right]
  have htN : t ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1) : Set K) :=
    iSup_le_normalizer_rootGroup hct (single_mem_roots i) ht
  have hsplit : t * u * y * z * (t * u * y)⁻¹ = t * (u * z * u⁻¹) * t⁻¹ := by
    rw [show t * u * y * z * (t * u * y)⁻¹ = t * (u * (y * z * y⁻¹) * u⁻¹) * t⁻¹ by group, hyz]
  have h1 : u * z * u⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
    have hh' := (Subgroup.mem_normalizer_iff.mp hN _).mp hz
    rw [hsplit] at hh'
    have h' := (Subgroup.mem_normalizer_iff.mp (inv_mem htN) _).mp hh'
    rwa [show t⁻¹ * (t * (u * z * u⁻¹) * t⁻¹) * t⁻¹⁻¹ = u * z * u⁻¹ by group] at h'
  have h2 : z⁻¹ * (u * z * u⁻¹) ∈ posUnipotentExcept D i := by
    have hzN := rootGroup_single_le_normalizer hext i (inv_mem hz)
    rw [show z⁻¹ * (u * z * u⁻¹) = z⁻¹ * u * z⁻¹⁻¹ * u⁻¹ by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hzN u).mp hu) (inv_mem hu)
  have h3 := PsiDiag.eq_one_of_mem_rootGroup_single_of_mem_posUnipotentExcept hct hext i
    (mul_mem (inv_mem hz) h1) h2
  have huz : u * z * u⁻¹ = z := by
    calc u * z * u⁻¹ = z * (z⁻¹ * (u * z * u⁻¹)) := by group
      _ = z := by rw [h3, mul_one]
  rw [hsplit, huz]

theorem orbitMap_rhoPerm (a : Fin (Tag.rank .E6)) : orbitMap (rhoPerm a) = orbitMap a := by
  revert a
  decide

end Generic

section Twisted


theorem exists_twistedTorus_conj {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (i : Fin (Tag.rank .F4)) {h : fixedGroup k θ} (hh : h ∈ ggTorus (twistedDatum k θ)) :
    ∃ t ∈ ⨆ j, hHat k θ j, ∀ z ∈ twistedRootGroup k θ (Pi.single i 1),
      h * z * h⁻¹ = t * z * t⁻¹ :=
  exists_torus_conj_of_mem_ggTorus
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ) i
    (twistedRootGroup_mul_comm θ hθ (IsRoot.basis i)) hh

theorem zpow_cartan_rho {k : Type*} [Field k] (a i : Fin (Tag.rank .E6)) (s : kˣ) :
    s ^ Tag.cartan .E6 a (rhoPerm i) = s ^ Tag.cartan .E6 (rhoPerm a) i := by
  rw [← cartan_rhoPerm_rhoPerm (rhoPerm a) i, rhoPerm_apply_rhoPerm]

theorem iSup_hHat_le_ggTorus {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ⨆ i, hHat k θ i ≤ ggTorus (twistedDatum k θ) := by
  intro t ht
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  exact iSup_le_normalizer_rootGroup
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)) hγ ht

end Twisted

section Isogeny

open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {k : Type} [Field k] [Finite k]

theorem e6Isogeny_nt (a : Fin (Tag.rank .E6)) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.nt k a s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      weylElt .E6 k a s := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  change ((e6Isogeny k (e6Data_valid.xm k (Pi.single a 1) s *
    e6Data_valid.xm k (-Pi.single a 1) (-((s⁻¹ : kˣ) : k)) *
      e6Data_valid.xm k (Pi.single a 1) s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) = _
  rw [map_mul, map_mul, e6Isogeny_xm_single, e6Isogeny_xm_neg_single, eltElement_simpleRoot_E6,
    eltElement_neg_simpleRoot_E6]
  rfl

theorem e6Isogeny_hm (a : Fin (Tag.rank .E6)) (s : kˣ) :
    ((e6Isogeny k (e6Data_valid.hm k a s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
      rootDiagUnit .E6 (fun j => s ^ Tag.cartan .E6 a j) := by
  rw [← torusElt_eq_rootDiagUnit]
  change ((e6Isogeny k (e6Data_valid.nt k a s * (e6Data_valid.nt k a 1)⁻¹) :
    ↥(adjointGroup .E6 k)) : ModGL .E6 k) = _
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, e6Isogeny_nt, e6Isogeny_nt,
    weylElt_inv]
  rfl

variable (θ : k →+* k)

theorem exists_compat_hm_fixed {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {s : kˣ}
    (hs : Units.map θ.toMonoidHom s = s) :
    ∃ b : Fin (Tag.rank .E6) → kˣ, (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ((e6Isogeny k (e6Data_valid.hm k a s) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
        rootDiagUnit .E6 b := by
  refine ⟨fun j => s ^ Tag.cartan .E6 a j, fun i => ?_, e6Isogeny_hm a s⟩
  simp only
  rw [zpow_cartan_rho, ha, map_zpow, hs]

theorem exists_compat_hm_pair (hθ : ∀ c, θ (θ c) = c) (a : Fin (Tag.rank .E6)) (s : kˣ) :
    ∃ b : Fin (Tag.rank .E6) → kˣ, (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ((e6Isogeny k (e6Data_valid.hm k a s *
          e6Data_valid.hm k (rhoPerm a) (Units.map θ.toMonoidHom s)) :
        ↥(adjointGroup .E6 k)) : ModGL .E6 k) = rootDiagUnit .E6 b := by
  refine ⟨(fun j => s ^ Tag.cartan .E6 a j) *
      (fun j => (Units.map θ.toMonoidHom s) ^ Tag.cartan .E6 (rhoPerm a) j), fun i => ?_, ?_⟩
  · have hss : Units.map θ.toMonoidHom (Units.map θ.toMonoidHom s) = s :=
      Units.ext (by rw [Units.coe_map, Units.coe_map]; exact hθ _)
    simp only [Pi.mul_apply]
    rw [zpow_cartan_rho, zpow_cartan_rho, rhoPerm_apply_rhoPerm, map_mul, map_zpow, map_zpow, hss,
      mul_comm]
  · rw [map_mul, Subgroup.coe_mul, e6Isogeny_hm, e6Isogeny_hm, rootDiagUnit_mul]

theorem exists_compat_of_mem_iSup_hHat (hθ : ∀ c, θ (θ c) = c) {t : fixedGroup k θ}
    (ht : t ∈ ⨆ j, hHat k θ j) :
    ∃ b : Fin (Tag.rank .E6) → kˣ, (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ((e6Isogeny k (t : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
        rootDiagUnit .E6 b := by
  refine Subgroup.iSup_induction (hHat k θ) (C := fun t => ∃ b : Fin (Tag.rank .E6) → kˣ,
    (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ((e6Isogeny k (t : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
        rootDiagUnit .E6 b) ht (fun j x hx => ?_) ⟨1, fun i => by simp, by
          rw [OneMemClass.coe_one, map_one, rootDiagUnit_one]; rfl⟩ ?_
  · have hx' : (x : e6Data_valid.minGroup k) ∈ hHatE k θ j := Subgroup.mem_subgroupOf.mp hx
    fin_cases j
    · obtain ⟨s, hs⟩ := hx'
      rw [← hs]
      exact exists_compat_hm_fixed θ (a := nd 1) (by decide)
        (show Units.map θ.toMonoidHom (s : kˣ) = s from s.2)
    · obtain ⟨s, hs⟩ := hx'
      rw [← hs]
      exact exists_compat_hm_fixed θ (a := nd 3) (by decide)
        (show Units.map θ.toMonoidHom (s : kˣ) = s from s.2)
    · obtain ⟨s, hs⟩ := hx'
      rw [← hs]
      exact exists_compat_hm_pair θ hθ (nd 2) s
    · obtain ⟨s, hs⟩ := hx'
      rw [← hs]
      exact exists_compat_hm_pair θ hθ (nd 0) s
  · rintro x y ⟨b₁, hb₁, e₁⟩ ⟨b₂, hb₂, e₂⟩
    refine ⟨b₁ * b₂, fun i => by simp only [Pi.mul_apply, hb₁, hb₂, map_mul], ?_⟩
    rw [Subgroup.coe_mul, map_mul, Subgroup.coe_mul, e₁, e₂, rootDiagUnit_mul]

theorem conj_rootDiagUnit_e6Isogeny_single {c : Fin (Tag.rank .E6) → kˣ}
    {a : Fin (Tag.rank .E6)} (hc : c a = 1) {y : e6Data_valid.minGroup k}
    (hy : y ∈ e6Data_valid.rootGroup k (Pi.single a 1)) :
    rootDiagUnit .E6 c * ((e6Isogeny k y : ↥(adjointGroup .E6 k)) : ModGL .E6 k) *
      (rootDiagUnit .E6 c)⁻¹ = ((e6Isogeny k y : ↥(adjointGroup .E6 k)) : ModGL .E6 k) := by
  obtain ⟨s, rfl⟩ := (e6Data_valid.mem_rootGroup k).mp hy
  rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]
  change rootDiagUnit .E6 c * xUnit .E6 k a s * (rootDiagUnit .E6 c)⁻¹ = xUnit .E6 k a s
  rw [(root_diagonal_conjugation .E6 k c).1 a s, hc, Units.val_one, one_mul]

theorem conj_rootDiagUnit_e6Isogeny_neg_single {c : Fin (Tag.rank .E6) → kˣ}
    {a : Fin (Tag.rank .E6)} (hc : c a = 1) {y : e6Data_valid.minGroup k}
    (hy : y ∈ e6Data_valid.rootGroup k (-Pi.single a 1)) :
    rootDiagUnit .E6 c * ((e6Isogeny k y : ↥(adjointGroup .E6 k)) : ModGL .E6 k) *
      (rootDiagUnit .E6 c)⁻¹ = ((e6Isogeny k y : ↥(adjointGroup .E6 k)) : ModGL .E6 k) := by
  obtain ⟨s, rfl⟩ := (e6Data_valid.mem_rootGroup k).mp hy
  rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]
  change rootDiagUnit .E6 c * yUnit .E6 k a s * (rootDiagUnit .E6 c)⁻¹ = yUnit .E6 k a s
  rw [(root_diagonal_conjugation .E6 k c).2.1 a s, hc, inv_one, Units.val_one, one_mul]

variable (θ : k →+* k)

theorem rootDiagUnit_conj_eq_of_agree (j : Fin (Tag.rank .F4)) {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ = Pi.single j 1 ∨ γ = -Pi.single j 1) {b b' : Fin (Tag.rank .E6) → kˣ}
    (hbb : ∀ a, orbitMap a = j → b' a = b a) {z : fixedGroup k θ}
    (hz : z ∈ twistedRootGroup k θ γ) :
    rootDiagUnit .E6 b' * ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) :
      ModGL .E6 k) * (rootDiagUnit .E6 b')⁻¹ =
      rootDiagUnit .E6 b * ((e6Isogeny k (z : e6Data_valid.minGroup k) :
        ↥(adjointGroup .E6 k)) : ModGL .E6 k) * (rootDiagUnit .E6 b)⁻¹ := by
  set c := b' * b⁻¹ with hcdef
  have hc : ∀ a, orbitMap a = j → c a = 1 := fun a ha => by
    rw [hcdef, Pi.mul_apply, Pi.inv_apply, hbb a ha, mul_inv_cancel]
  have hb' : b' = c * b := by rw [hcdef, inv_mul_cancel_right]
  have ha₀ : orbitMap (firstNode j) = j := orbitMap_firstNode j
  have ha₁ : orbitMap (rhoPerm (firstNode j)) = j := by rw [orbitMap_rhoPerm, ha₀]
  let S : Subgroup (e6Data_valid.minGroup k) := MonoidHom.eqLocus
    ((MulAut.conj (rootDiagUnit .E6 c)).toMonoidHom.comp
      ((adjointGroup .E6 k).subtype.comp (e6Isogeny k)))
    ((adjointGroup .E6 k).subtype.comp (e6Isogeny k))
  have hmem : (z : e6Data_valid.minGroup k) ∈ S := by
    rcases hγ with rfl | rfl
    · have h1 := (mem_twistedRootGroup_iff θ (isRoot_single .E6 (firstNode j))
        (by rw [proj_single, ha₀]) z).mp hz
      rw [rho_single] at h1
      have hle : e6Data_valid.rootGroup k (Pi.single (firstNode j) 1) ⊔
          e6Data_valid.rootGroup k (Pi.single (rhoPerm (firstNode j)) 1) ≤ S :=
        sup_le (fun _ hy => conj_rootDiagUnit_e6Isogeny_single (hc _ ha₀) hy)
          (fun _ hy => conj_rootDiagUnit_e6Isogeny_single (hc _ ha₁) hy)
      exact hle h1
    · have h1 := (mem_twistedRootGroup_iff θ (isRoot_neg_single .E6 (firstNode j))
        (by rw [proj_neg_single, ha₀]) z).mp hz
      rw [rho_neg_single] at h1
      have hle : e6Data_valid.rootGroup k (-Pi.single (firstNode j) 1) ⊔
          e6Data_valid.rootGroup k (-Pi.single (rhoPerm (firstNode j)) 1) ≤ S :=
        sup_le (fun _ hy => conj_rootDiagUnit_e6Isogeny_neg_single (hc _ ha₀) hy)
          (fun _ hy => conj_rootDiagUnit_e6Isogeny_neg_single (hc _ ha₁) hy)
      exact hle h1
  have e : rootDiagUnit .E6 c *
      ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) *
        (rootDiagUnit .E6 c)⁻¹ =
      ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) :=
    hmem
  rw [hb', rootDiagUnit_mul, mul_inv_rev,
    show rootDiagUnit .E6 c * rootDiagUnit .E6 b = rootDiagUnit .E6 b * rootDiagUnit .E6 c by
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]]
  calc rootDiagUnit .E6 b * rootDiagUnit .E6 c *
        ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) *
        ((rootDiagUnit .E6 b)⁻¹ * (rootDiagUnit .E6 c)⁻¹) =
      rootDiagUnit .E6 b * (rootDiagUnit .E6 c *
        ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) *
          (rootDiagUnit .E6 c)⁻¹) * (rootDiagUnit .E6 b)⁻¹ := by
        rw [show (rootDiagUnit .E6 b)⁻¹ * (rootDiagUnit .E6 c)⁻¹ =
          (rootDiagUnit .E6 c)⁻¹ * (rootDiagUnit .E6 b)⁻¹ by
            rw [rootDiagUnit_inv, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
              mul_comm]]
        group
    _ = _ := by rw [e]

variable (hθ : ∀ c, θ (θ c) = c)

include hθ in
theorem exists_diag_of_rankOne {G : Type*} [Group G] (ψ : fixedGroup k θ →* G)
    (hR : ∀ (d : G) (j : Fin (Tag.rank .F4)) (h : fixedGroup k θ),
      h ∈ ggTorus (twistedDatum k θ) →
      (∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1), d⁻¹ * ψ z * d = ψ z) →
      (∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
        d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) →
      ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1), d⁻¹ * ψ z * d = ψ z)
    {c : G} (hc : GGPsiInnerDiag (twistedDatum k θ) ψ c) :
    ∃ g ∈ ψ.range, ∃ b : Fin (Tag.rank .E6) → kˣ,
      (∀ i, b (rhoPerm i) = Units.map θ.toMonoidHom (b i)) ∧
      ∀ (j : Fin (Tag.rank .F4)) (γ : Fin (Tag.rank .F4) → ℤ),
        (γ = Pi.single j 1 ∨ γ = -Pi.single j 1) →
        ∀ z ∈ (twistedDatum k θ).rootGroup γ, ∃ z' : fixedGroup k θ,
          (c * g)⁻¹ * ψ z * (c * g) = ψ z' ∧
            ((e6Isogeny k (z' : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) :
              ModGL .E6 k) =
              rootDiagUnit .E6 b *
                ((e6Isogeny k (z : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) :
                  ModGL .E6 k) * (rootDiagUnit .E6 b)⁻¹ := by
  obtain ⟨g, hg, hγ⟩ := hc
  have hT := iSup_hHat_le_ggTorus θ hθ
  have hpos : ∀ j : Fin (Tag.rank .F4), ∃ t ∈ ⨆ i, hHat k θ i,
      ∃ bt : Fin (Tag.rank .E6) → kˣ, (∀ i, bt (rhoPerm i) = Units.map θ.toMonoidHom (bt i)) ∧
        ((e6Isogeny k (t : e6Data_valid.minGroup k) : ↥(adjointGroup .E6 k)) : ModGL .E6 k) =
          rootDiagUnit .E6 bt ∧
        ∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1),
          (c * g)⁻¹ * ψ z * (c * g) = ψ (t * z * t⁻¹) := by
    intro j
    obtain ⟨h, hh, hz⟩ := hγ _ (single_mem_roots j)
    obtain ⟨t, ht, htz⟩ := exists_twistedTorus_conj θ hθ j hh
    obtain ⟨bt, hbt, hπ⟩ := exists_compat_of_mem_iSup_hHat θ hθ ht
    exact ⟨t, ht, bt, hbt, hπ, fun z hzz => by rw [hz z hzz, htz z hzz]⟩
  choose t ht bt hbt hπ hact using hpos
  have hneg : ∀ j : Fin (Tag.rank .F4), ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
      (c * g)⁻¹ * ψ z * (c * g) = ψ (t j * z * (t j)⁻¹) := by
    intro j
    obtain ⟨h, hh, hz⟩ := hγ _ (neg_single_mem_roots j)
    have hcen : ∀ z ∈ (twistedDatum k θ).rootGroup (Pi.single j 1),
        ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) = ψ z := by
      intro z hzz
      calc ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
            (ψ (t j))⁻¹ * ((c * g)⁻¹ * ψ z * (c * g)) * ψ (t j) := by group
        _ = (ψ (t j))⁻¹ * ψ (t j * z * (t j)⁻¹) * ψ (t j) := by rw [hact j z hzz]
        _ = ψ z := by rw [map_mul, map_mul, map_inv]; group
    have hact' : ∀ z ∈ (twistedDatum k θ).rootGroup (-Pi.single j 1),
        ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
          ψ (((t j)⁻¹ * h) * z * ((t j)⁻¹ * h)⁻¹) := by
      intro z hzz
      calc ((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j)) =
            (ψ (t j))⁻¹ * ((c * g)⁻¹ * ψ z * (c * g)) * ψ (t j) := by group
        _ = (ψ (t j))⁻¹ * ψ (h * z * h⁻¹) * ψ (t j) := by rw [hz z hzz]
        _ = ψ (((t j)⁻¹ * h) * z * ((t j)⁻¹ * h)⁻¹) := by
          rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul,
            map_inv]
          group
    have key := hR ((c * g) * ψ (t j)) j ((t j)⁻¹ * h) (mul_mem (inv_mem (hT (ht j))) hh) hcen
      hact'
    intro z hzz
    calc (c * g)⁻¹ * ψ z * (c * g) = ψ (t j) *
          (((c * g) * ψ (t j))⁻¹ * ψ z * ((c * g) * ψ (t j))) * (ψ (t j))⁻¹ := by group
      _ = ψ (t j) * ψ z * (ψ (t j))⁻¹ := by rw [key z hzz]
      _ = ψ (t j * z * (t j)⁻¹) := by rw [map_mul, map_mul, map_inv]
  refine ⟨g, hg, fun a => bt (orbitMap a) a, fun i => ?_, fun j γ hγ' z hz =>
    ⟨t j * z * (t j)⁻¹, ?_, ?_⟩⟩
  · simp only
    rw [orbitMap_rhoPerm]
    exact hbt _ i
  · rcases hγ' with rfl | rfl
    · exact hact j z hz
    · exact hneg j z hz
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hπ j]
    exact rootDiagUnit_conj_eq_of_agree θ j hγ' (b := fun a => bt (orbitMap a) a)
      (fun a ha => by simp only [ha]) hz

end Isogeny

section RankOne

@[expose] def TwE6RankOneInput (f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (ψ : twistedE6Group 2 f →* G),
    ψ.ker ≤ Subgroup.center (twistedE6Group 2 f) →
    ∀ (d : G) (j : Fin (Tag.rank .F4)) (h : twistedE6Group 2 f),
      h ∈ ggTorus (twistedE6Datum 2 f) →
      (∀ z ∈ (twistedE6Datum 2 f).rootGroup (Pi.single j 1), d⁻¹ * ψ z * d = ψ z) →
      (∀ z ∈ (twistedE6Datum 2 f).rootGroup (-Pi.single j 1),
        d⁻¹ * ψ z * d = ψ (h * z * h⁻¹)) →
      ∀ z ∈ (twistedE6Datum 2 f).rootGroup (-Pi.single j 1), d⁻¹ * ψ z * d = ψ z

theorem twE6DiagInput_of_rankOne {f : ℕ} (hf : 1 ≤ f) (hR : TwE6RankOneInput f) :
    TwE6DiagInput f := by
  intro G _ ψ hker c hc
  exact exists_diag_of_rankOne (k := GaloisField 2 (2 * f)) (frobQ 2 f) (frobQ_frobQ 2 f hf) ψ
    (hR G ψ hker) hc

end RankOne

end InnerDiagTwE6

section Genuine

theorem ggInnerDiagMarkingAt_twistedE6_of_rankOne
    (hR : ∀ f, 1 ≤ f → InnerDiagTwE6.TwE6RankOneInput f) : GGInnerDiagMarkingAt .twistedE6 :=
  ggInnerDiagMarkingAt_twistedE6_of_diag fun f hf =>
    InnerDiagTwE6.twE6DiagInput_of_rankOne hf (hR f hf)

end Genuine

end CFSG.StandardType
