module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalogModel
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalDiagHom
public import CFSG.RankThree.CentralLiftSO.TailRho
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalHermitianLifts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open Matrix
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup)
open CFSG.QuasithinUnique (IsSylowTwoOf isSylowTwoOf_top_of_sylow)
open TauCeti.Subgroup (normalizerQuotient)

section LinearMap

variable {K F : Type} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}
  [CharP K 2]

private theorem coe_rhoG_diagHom_eq_torusMap (i : Fin r) {s : Fˣ} {a : Kˣ}
    (hN : normUnits T s = a) (hB : barQuot T s = 1) :
    ((rhoG T i (diagHom F s) : G0 T r) :
      ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F)) =
      torusMap F (Pi.mulSingle i a) 1 := by
  rw [coe_rhoG, diagHom_apply, rho_diagSL_eq_torusMap, hN, hB]

end LinearMap

private theorem normTail_inversion_data
    {k F : Type} [Field k] [Field F] [Algebra k F] [CharP k 2]
    (T : NormTailData k F) {m : ℕ} (h4 : 4 ≤ m) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {ζ : kˣ} (hζ : orderOf ζ = r) :
    ∃ (h w : Fin 4 → G0 T m),
      (∀ i, ((h i : G0 T m) :
        ((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F)) =
        torusMap F (Pi.mulSingle (Fin.castLE h4 i) (ζ ^ 2)) 1) ∧
      (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = r) ∧
      (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) := by
  let s : Fˣ := Units.map (algebraMap k F : k →* F) ζ
  have hsN : normUnits T s = ζ ^ 2 := normUnits_algebraMap T ζ
  have hsB : barQuot T s = 1 := barQuot_algebraMap T ζ
  have hsbar : Units.map (T.bar : F →* F) s = s := barUnits_algebraMap T ζ
  let c : Fin 4 → Fin m := Fin.castLE h4
  let h : Fin 4 → G0 T m := fun i => rhoG T (c i) (diagHom F s)
  let w : Fin 4 → G0 T m := fun i => wG T (c i)
  have hlin : ∀ i : Fin 4, ((h i : G0 T m) :
      ((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F)) =
      torusMap F (Pi.mulSingle (c i) (ζ ^ 2)) 1 := fun i =>
    coe_rhoG_diagHom_eq_torusMap T (c i) hsN hsB
  have hcomm : ∀ i j : Fin 4, Commute (h i) (h j) := by
    intro i j
    show h i * h j = h j * h i
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [hlin i, hlin j]
    exact (torusMap_commute (Pi.mulSingle (c i) (ζ ^ 2)) (Pi.mulSingle (c j) (ζ ^ 2)) 1 1).eq
  have hord : ∀ i : Fin 4, orderOf (h i) = r := by
    intro i
    have h1 : orderOf (h i) = orderOf s :=
      (orderOf_injective (rhoG T (c i)) (rhoG_injective T (c i)) (diagHom F s)).trans
        (orderOf_injective (diagHom F) (diagHom_injective F) s)
    rw [h1]
    dsimp only [s]
    rw [orderOf_injective (Units.map (algebraMap k F : k →* F))
      (Units.map_injective (f := (algebraMap k F : k →* F)) (algebraMap k F).injective) ζ, hζ]
  have hinv : ∀ i : Fin 4, w i * h i * (w i)⁻¹ = (h i)⁻¹ := by
    intro i
    have he : swapSL F * diagHom F s * (swapSL F)⁻¹ = (diagHom F s)⁻¹ := by
      rw [diagHom_apply, swapSL_mul_diagSL, mul_inv_cancel_right, ← diagHom_apply,
        ← diagHom_apply, map_inv]
    calc w i * h i * (w i)⁻¹
        = rhoG T (c i) (swapSL F) * rhoG T (c i) (diagHom F s) *
            (rhoG T (c i) (swapSL F))⁻¹ := by dsimp only [w, h, wG]
      _ = rhoG T (c i) (swapSL F * diagHom F s * (swapSL F)⁻¹) := by
            rw [← map_mul, ← map_inv, ← map_mul]
      _ = rhoG T (c i) ((diagHom F s)⁻¹) := by rw [he]
      _ = (h i)⁻¹ := by dsimp only [h]; rw [map_inv]
  have hfix : ∀ i j : Fin 4, i ≠ j → w i * h j * (w i)⁻¹ = h j := by
    intro i j hij
    have hcij : c i ≠ c j := fun hcij => hij (Fin.castLE_injective h4 hcij)
    have hbarSL : barSL T (diagHom F s) = diagHom F s := by
      simp only [diagHom_apply, barSL_diagSL, hsbar]
    have hw := wG_conj_rhoG T (i := c j) (j := c i) hcij (diagHom F s)
    simpa [w, h, wG, hbarSL] using hw
  exact ⟨h, w, hlin, hcomm, hord, hinv, hfix⟩

private theorem exists_inversion_basis_torus
    {k F : Type} [Field k] [Field F] [Algebra k F] [CharP k 2]
    (T : NormTailData k F) {m : ℕ} (h4 : 4 ≤ m) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {ζ : kˣ} (hζ : orderOf ζ = r) {Y : Type} [Group Y]
    (φ : Y →* G0 T m) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ D : Subgroup (G0 T m), IsElemAbelian r D ∧ Nat.card D = r ^ 4 ∧
      (∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) ∧
      D ≤ (tailBorel m (normForm T)).subgroupOf
        (orthElementaryGroup (quadTail m (normForm T))) := by
  obtain ⟨h, w, hlin, hcomm, hord, hinv, hfix⟩ :=
    normTail_inversion_data T h4 hr hr2 hζ
  let D : Subgroup (G0 T m) := Subgroup.closure (Set.range h)
  obtain ⟨hDabelian, hDcard, hDcomm⟩ :=
    CFSG.RankThree.CentralCover.inversion_basis_package (φ := φ) hφ hker hr hr2 h w
      hcomm hord hinv hfix
  have hmem : ∀ i : Fin 4, ((h i : G0 T m) :
      ((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F)) ∈ tailBorel m (normForm T) := by
    intro i
    rw [hlin i]
    exact tailTorus_le_tailBorel
      (CFSG.RankThree.CentralLiftSO.TailO.torusMap_mem_tailTorus T
        (Pi.mulSingle (Fin.castLE h4 i) (ζ ^ 2)) (one_mem _) (hlin i ▸ (h i).2))
  have hDborel : D ≤ (tailBorel m (normForm T)).subgroupOf
      (orthElementaryGroup (quadTail m (normForm T))) := by
    change Subgroup.closure (Set.range h) ≤ _
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    exact (Subgroup.mem_subgroupOf (H := tailBorel m (normForm T))
      (K := orthElementaryGroup (quadTail m (normForm T)))).2 (hmem i)
  exact ⟨D, hDabelian, by simpa using hDcard, hDcomm, hDborel⟩

private theorem pomegaMinus_witness
    {k F : Type} [Field k] [Finite k] [Field F] [Algebra k F] [CharP k 2] [Finite F]
    (T : NormTailData k F) {m : ℕ} (h4 : 4 ≤ m) (hFdim : Module.finrank k F = 2)
    {K : Type} [Group K] [Finite K] (e : K ⧸ Subgroup.center K ≃* G0 T m)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ζ : kˣ} (hζ : orderOf ζ = r)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  classical
  have h3m : 3 ≤ m := by omega
  haveI : Finite (((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F)) :=
    Finite.of_injective
      (fun g : (((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F)) =>
        (g : ((Fin m ⊕ Fin m → k) × F) → ((Fin m ⊕ Fin m → k) × F)))
      (fun _ _ h => LinearEquiv.ext fun x => congrFun h x)
  haveI : Finite (G0 T m) :=
    Finite.of_injective (fun g : G0 T m =>
      (g : ((Fin m ⊕ Fin m → k) × F) ≃ₗ[k] ((Fin m ⊕ Fin m → k) × F))) Subtype.coe_injective
  let ψ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let φ : K →* G0 T m := e.toMonoidHom.comp ψ
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_eq : φ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkerle : φ.ker ≤ Subgroup.center K := le_of_eq hker_eq
  obtain ⟨D, hDabelian, hDcard, hDcomm, hDborel⟩ :=
    exists_inversion_basis_torus T h4 hr hr2 hζ φ hφ hkerle
  obtain ⟨⟨S₀, hS₀coe⟩, hnorm, -⟩ :=
    orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (K := k) (A := F) (r := m)
      (qA := normForm T) h3m (normForm_anisotropic T)
      (nondegenerate_polarBilin_normForm T hFdim) (Or.inr hFdim)
  let U : Subgroup (G0 T m) := (S₀ : Subgroup (G0 T m))
  have hU : IsSylowTwoOf U ⊤ := isSylowTwoOf_top_of_sylow S₀
  have hDU : D ≤ Subgroup.normalizer (U : Set (G0 T m)) := by
    have hnormU : Subgroup.normalizer (U : Set (G0 T m)) =
        (tailBorel m (normForm T)).subgroupOf
          (orthElementaryGroup (quadTail m (normForm T))) := by
      rw [show U = (tailUnipotent m (normForm T)).subgroupOf
        (orthElementaryGroup (quadTail m (normForm T))) from hS₀coe, hnorm]
    rw [hnormU]
    exact hDborel
  have hbound := le_pRank_normalizerQuotient_of_comap_comm (φ := φ) hφ hkerle hr hr2
    (D := D) (fun x hx => hDabelian.2 x hx) hDcomm (k := 4) (by rw [hDcard])
    (U := U) hU hDU S hS
  omega

theorem k_CartanRankLarge_pomegaMinus :
    ∀ (K : Type) [Group K] [Finite K] (n f : ℕ),
      CFSG.Open.StatedLieAdmissible .POmegaMinus n 2 f → 2 < 2 ^ f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus n 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .POmegaMinus n →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  intro K _ _ n f _ h2f hL _ _ S hS hrank
  have hrank' : 4 ≤ n - 1 := by
    simpa only [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] using hrank
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at h2f
  obtain ⟨k, hkField, hkFin, hkChar, hkcard, hn4, F, hFField, hFAlg, T, hFdim, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog.exists_normTail_of_lieModel hL
  letI := hkField
  letI := hkFin
  letI := hkChar
  letI := hFField
  letI := hFAlg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hFfin : Finite F := finite_of_finrank_eq_two hFdim
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hcard_units : r ∣ Nat.card kˣ := by
    rw [Nat.card_units, hkcard]
    exact hrdvd
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := kˣ) r hcard_units
  exact ⟨r, hr, hr2, hrdvd, pomegaMinus_witness T hrank' hFdim e hr hr2 hζo S hS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
