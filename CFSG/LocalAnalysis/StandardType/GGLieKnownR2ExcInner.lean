module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcRoots
public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat

public section

namespace CFSG.StandardType.LieKnownR2.ExcInner

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction CFSG.StandardType.RootCentExc CFSG.LieType.Steinberg

private theorem l10sx78_a_eq_highRoot_of_isRoot_maxHeight
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (h : ht (highRoot τ) ≤ ht γ) : γ = highRoot τ := by
  rcases hτ with rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)).1 hγ
    have hall : (List.range Tag.E7.rootCertificate.roots.length).all fun k =>
        decide (ht (highRoot .E7) ≤ ht (Tag.E7.rootCertificate.root k) →
          Tag.E7.rootCertificate.root k = highRoot .E7) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)).1 hγ
    have hall : (List.range Tag.E8.rootCertificate.roots.length).all fun k =>
        decide (ht (highRoot .E8) ≤ ht (Tag.E8.rootCertificate.root k) →
          Tag.E8.rootCertificate.root k = highRoot .E8) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h

private def l10sx78_a_i₀ : (τ : Tag) → Fin τ.rank
  | .G2 => ⟨0, by decide⟩
  | .F4 => ⟨0, by decide⟩
  | .D4 => ⟨0, by decide⟩
  | .E6 => ⟨0, by decide⟩
  | .E7 => ⟨0, by decide⟩
  | .E8 => ⟨7, by decide⟩

private theorem l10sx78_a_highRootData {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8) :
    HighRootData τ (highRoot τ) (l10sx78_a_i₀ τ) := by
  rcases hτ with rfl | rfl
  · exact RootCentExc.highRootData_E7
  · exact RootCentExc.highRootData_E8

private def l10sx78_a_scalarGroup
    (τ : Tag) (K : Type) [Field K] (θ : Fin τ.rank → ℤ) : Subgroup (ModGL τ K) where
  carrier := {g | ∃ l : K, ∀ c : K, g * pinnedX τ K θ c * g⁻¹ = pinnedX τ K θ (l * c)}
  one_mem' := ⟨1, by intro c; rw [one_mul, inv_one, mul_one, one_mul]⟩
  mul_mem' := by
    rintro g h ⟨l, hl⟩ ⟨l', hl'⟩
    refine ⟨l * l', fun c => ?_⟩
    calc g * h * pinnedX τ K θ c * (g * h)⁻¹
        = g * (h * pinnedX τ K θ c * h⁻¹) * g⁻¹ := by group
      _ = g * pinnedX τ K θ (l' * c) * g⁻¹ := by rw [hl' c]
      _ = pinnedX τ K θ (l * (l' * c)) := hl (l' * c)
      _ = pinnedX τ K θ ((l * l') * c) := by rw [mul_assoc]
  inv_mem' := by
    rintro g ⟨l, hl⟩
    have hl0 : l ≠ 0 := by
      intro h0
      have h1 := hl 1
      rw [h0, zero_mul, pinnedX_zero, mul_inv_eq_one, mul_eq_left] at h1
      exact one_ne_zero (pinnedX_injective τ K θ (h1.trans (pinnedX_zero τ K θ).symm))
    refine ⟨l⁻¹, fun c => ?_⟩
    have h2 := hl (l⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul] at h2
    calc g⁻¹ * pinnedX τ K θ c * (g⁻¹)⁻¹
        = g⁻¹ * (g * pinnedX τ K θ (l⁻¹ * c) * g⁻¹) * g := by rw [← h2]; group
      _ = pinnedX τ K θ (l⁻¹ * c) := by group

private theorem l10sx78_a_posUnipotent_le_scalarGroup
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] :
    posUnipotent τ K ≤ l10sx78_a_scalarGroup τ K (highRoot τ) := by
  intro g hg
  have hθ : IsMaxHeight τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight
  refine ⟨1, fun c => ?_⟩
  rw [one_mul]
  rw [(RootCentExc.commute_of_mem_posUnipotent hθ hg c).eq, mul_inv_cancel_right]

private theorem l10sx78_a_leviGens_centralizes
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [CharP K 2] :
    ∀ x ∈ leviGens τ K {i | i ≠ l10sx78_a_i₀ τ},
      x * pinnedX τ K (highRoot τ) 1 = pinnedX τ K (highRoot τ) 1 * x := by
  have hθ : IsMaxHeight τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rintro x ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single,
      (RootCentExc.commute_pinnedX_of_isMaxHeight hθ (isRoot_single τ j)
        (by rw [height_single]; norm_num) c 1).eq]
  · have hj0 : ∑ k, Tag.cartan τ j k * highRoot τ k = 0 := by
      have hco := (l10sx78_a_highRootData hτ).coPair j
      split_ifs at hco with h
      · exact absurd h hj
      · simpa using hco
    rw [RootCentExc.yUnit_mul_pinnedX_comm (K := K) h2 hθ hj0 c 1]

private theorem l10sx78_a_closure_radLeviGens_le_scalarGroup
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [CharP K 2] :
    Subgroup.closure (radLeviGens τ K {i | i ≠ l10sx78_a_i₀ τ}) ≤
      l10sx78_a_scalarGroup τ K (highRoot τ) := by
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  rcases hx with ⟨γ, hγ, c, rfl⟩ | hx
  · exact l10sx78_a_posUnipotent_le_scalarGroup hτ
      (RootCentExc.pinnedX_mem_posUnipotent (mem_parabolicRadicalRoots_iff.1 hγ).1
        (mem_parabolicRadicalRoots_iff.1 hγ).2.1 c)
  · rcases hx with ⟨j, hj, c, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact l10sx78_a_posUnipotent_le_scalarGroup hτ
        (RootCentExc.pinnedX_mem_posUnipotent (isRoot_single τ j)
          (by rw [height_single]; norm_num) c)
    · have hθ : IsMaxHeight τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight
      have hj0 : ∑ k, Tag.cartan τ j k * highRoot τ k = 0 := by
        have hco := (l10sx78_a_highRootData hτ).coPair j
        split_ifs at hco with h
        · exact absurd h hj
        · simpa using hco
      refine ⟨1, fun d => ?_⟩
      rw [one_mul,
        RootCentExc.yUnit_mul_pinnedX_comm (K := K) (CharP.cast_eq_zero K 2) hθ hj0 c d,
        mul_inv_cancel_right]

private theorem l10sx78_a_torusElt_mem_scalarGroup
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] (t : Kˣ) :
    torusElt τ K (l10sx78_a_i₀ τ) t ∈ l10sx78_a_scalarGroup τ K (highRoot τ) := by
  have hθ : IsRoot τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight.1
  have hexp : ∑ j, Tag.cartan τ (l10sx78_a_i₀ τ) j * highRoot τ j = 1 := by
    rw [(l10sx78_a_highRootData hτ).coPair (l10sx78_a_i₀ τ), if_pos rfl]
  refine ⟨(t : K), fun c => ?_⟩
  rw [conj_pinnedX_of_mem_torusGroup (torusElt_mem_torusGroup (l10sx78_a_i₀ τ) t) hθ c,
    torusRootChar_torusElt (l10sx78_a_i₀ τ) t hθ, hexp, zpow_one]

private theorem l10sx78_a_rootGroup_eq_subgroupOf
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) (K : Type) [Field K] :
    (adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) =
      (rootSubgroup τ K (highRoot τ)).subgroupOf (adjointGroup τ K) := by
  have hθ : IsRoot τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight.1
  change rootGroup (rootOperatorFamily τ) K (highRoot τ) = _
  rw [rootGroup_of_isRoot (F := rootOperatorFamily τ) hθ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (F := rootOperatorFamily τ) (K := K)
      (α := ⟨highRoot τ, hθ⟩)]

private theorem l10sx78_a_conj_eq_of_mem {G : Type*} [Group G] {R : Subgroup G} {y : MulAut G}
    (hcent : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≤ Subgroup.centralizer (R : Set G))
    (hy : ∀ m ∈ Subgroup.normalizer (R : Set G),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set G)))
    {m : G} (hm : m ∈ Subgroup.normalizer (R : Set G)) {x : G} (hx : x ∈ R) :
    y m * x * (y m)⁻¹ = m * x * m⁻¹ := by
  have hq : y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set G)) := hy m hm
  have hqc : y m * m⁻¹ ∈ Subgroup.centralizer (R : Set G) := hcent hq
  have hmx : m * x * m⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hm x).mp hx
  have hcomm : (m * x * m⁻¹) * (y m * m⁻¹) = (y m * m⁻¹) * (m * x * m⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hqc (m * x * m⁻¹) hmx
  calc y m * x * (y m)⁻¹ = (y m * m⁻¹) * (m * x * m⁻¹) * (y m * m⁻¹)⁻¹ := by group
    _ = m * x * m⁻¹ := by rw [← hcomm]; group

private theorem l10sx78_a_entrywise_conj_pinnedX
    {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K) {h : ↥(adjointGroup τ K)} (χ : K)
    (hh : ∀ c : K, (h : ModGL τ K) * pinnedX τ K (highRoot τ) c *
        (h : ModGL τ K)⁻¹ = pinnedX τ K (highRoot τ) (χ * c)) (c : K) :
    Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        pinnedX τ K (highRoot τ) c *
        (Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))⁻¹ =
      pinnedX τ K (highRoot τ) (σ χ * c) := by
  let f : Module.End K (RootModule τ K) →* Module.End K (RootModule τ K) :=
    entrywiseHom σ.toRingHom
  have hf : f = entrywiseHom σ.toRingHom := rfl
  have hx : Units.map f (pinnedX τ K (highRoot τ) (σ.symm c)) =
      pinnedX τ K (highRoot τ) c := by
    refine Units.ext ?_
    rw [Units.coe_map, hf]
    change entrywise σ.toRingHom
      (pinnedX τ K (highRoot τ) (σ.symm c) : Module.End K (RootModule τ K)) =
        pinnedX τ K (highRoot τ) c
    rw [entrywise_pinnedX, show σ.toRingHom (σ.symm c) = c from σ.apply_symm_apply c]
  calc Units.map f (h : ModGL τ K) * pinnedX τ K (highRoot τ) c *
        (Units.map f (h : ModGL τ K))⁻¹
      = Units.map f (h : ModGL τ K) *
          Units.map f (pinnedX τ K (highRoot τ) (σ.symm c)) *
          (Units.map f (h : ModGL τ K))⁻¹ := by rw [hx]
    _ = Units.map f ((h : ModGL τ K) * pinnedX τ K (highRoot τ) (σ.symm c) *
          (h : ModGL τ K)⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = Units.map f (pinnedX τ K (highRoot τ) (χ * σ.symm c)) := by rw [hh (σ.symm c)]
    _ = pinnedX τ K (highRoot τ) (σ (χ * σ.symm c)) := by
      refine Units.ext ?_
      rw [Units.coe_map, hf]
      change entrywise σ.toRingHom
        (pinnedX τ K (highRoot τ) (χ * σ.symm c) : Module.End K (RootModule τ K)) =
          pinnedX τ K (highRoot τ) (σ (χ * σ.symm c))
      rw [entrywise_pinnedX]
      rfl
    _ = pinnedX τ K (highRoot τ) (σ χ * c) := by rw [map_mul, σ.apply_symm_apply]

private theorem l10sx78_a_pCore_le_centralizer_highRoot
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer
        (((adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) :
          Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K))) ≤
      Subgroup.centralizer
        (((adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) :
          Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) := by
  have hX := l10sx78_a_rootGroup_eq_subgroupOf hτ K
  have hH : rootSubgroup τ K (highRoot τ) ≤ adjointGroup τ K :=
    rootSubgroup_le_adjointGroup (highRoot τ)
  have hτ3 : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by rcases hτ with h | h <;> simp [h]
  have hN : Subgroup.normalizer (((adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) :
        Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) =
      (parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank))).subgroupOf
        (adjointGroup τ K) := by
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hH, Subgroup.subgroupOf_inj,
      (even_exc_highest_root_normalizer τ hτ3 K).1,
      inf_eq_left.2 (parabolicSubgroup_le_adjointGroup τ K (thetaPerpF τ : Set _))]
  intro x hx
  have hxp : x ∈ (pCoreOf 2 (parabolicSubgroup τ K
      (thetaPerpF τ : Set (Fin τ.rank)))).subgroupOf (adjointGroup τ K) := by
    have hHP : parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank)) ≤
        adjointGroup τ K :=
      parabolicSubgroup_le_adjointGroup τ K _
    rw [← CFSG.StandardType.GGRootNorm.pCoreOf_subgroupOf hHP, ← hN]
    exact hx
  have hxrad : (x : ModGL τ K) ∈ parabolicRadical τ K
      (thetaPerpF τ : Set (Fin τ.rank)) := by
    have hxpc : (x : ModGL τ K) ∈ pCoreOf 2 (parabolicSubgroup τ K
        (thetaPerpF τ : Set (Fin τ.rank))) :=
      Subgroup.mem_subgroupOf.1 hxp
    have heq := (even_exc_highest_root_normalizer τ hτ3 K).2
    rw [heq] at hxpc
    exact (Subgroup.mem_inf.1 hxpc).1
  have hxpos : (x : ModGL τ K) ∈ posUnipotent τ K :=
    parabolicRadical_le_posUnipotent _ hxrad
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply Subtype.ext
  have hyroot : (y : ModGL τ K) ∈ rootSubgroup τ K (highRoot τ) := by
    rw [hX] at hy
    exact Subgroup.mem_subgroupOf.1 hy
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hyroot
  simp only [Subgroup.coe_mul]
  rw [show (y : ModGL τ K) = pinnedX τ K (highRoot τ) c from hc.symm]
  exact (RootCentExc.commute_of_mem_posUnipotent (l10sx78_a_highRootData hτ).maxHeight
    hxpos c).eq.symm

private theorem l10sx78_a_normalizer_conj_scalar
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [CharP K 2]
    {g : ↥(adjointGroup τ K)} {μ : K}
    (hgμ : (g : ModGL τ K) * pinnedX τ K (highRoot τ) 1 *
        (g : ModGL τ K)⁻¹ = pinnedX τ K (highRoot τ) μ) :
    (g : ModGL τ K) ∈ l10sx78_a_scalarGroup τ K (highRoot τ) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hθ : IsMaxHeight τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight
  have hco : ∀ i : Fin τ.rank, ∑ j, Tag.cartan τ i j * highRoot τ j =
      if i = l10sx78_a_i₀ τ then 1 else 0 :=
    (l10sx78_a_highRootData hτ).coPair
  obtain ⟨c, hc, hform⟩ := (l10sx78_a_highRootData hτ).form
  have hW : ∀ w : WeylGroup τ, w • (highRoot τ) = highRoot τ →
      w ∈ parabolicWeylGroup τ {i | i ≠ l10sx78_a_i₀ τ} :=
    fun w hw => RootCentExc.mem_parabolicWeylGroup_of_smul_eq hc hform hw
  have hP : (g : ModGL τ K) ∈ parabolicSubgroup τ K {i | i ≠ l10sx78_a_i₀ τ} :=
    RootCentExc.mem_parabolicSubgroup_of_conj h2 hθ hW g.2 hgμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, pinnedX_zero] at hgμ
    have hX1 : pinnedX τ K (highRoot τ) 1 = 1 := by
      have := congrArg (fun z : ModGL τ K =>
        (g : ModGL τ K)⁻¹ * z * (g : ModGL τ K)) hgμ
      simpa [mul_assoc] using this
    exact one_ne_zero (pinnedX_injective τ K (highRoot τ)
      (hX1.trans (pinnedX_zero τ K (highRoot τ)).symm))
  let u : Kˣ := Units.mk0 μ hμ0
  let h : ↥(adjointGroup τ K) := ⟨torusElt τ K (l10sx78_a_i₀ τ) u,
    torusElt_mem_adjointGroup (l10sx78_a_i₀ τ) u⟩
  set H : ModGL τ K := (h : ModGL τ K) with hH
  have hT : H ∈ torusGroup τ K := by
    rw [hH]
    exact torusElt_mem_torusGroup (l10sx78_a_i₀ τ) u
  have hPlevi : H ∈ parabolicSubgroup τ K {i | i ≠ l10sx78_a_i₀ τ} :=
    (parabolic_root_radical_Levi_factors τ K {i | i ≠ l10sx78_a_i₀ τ}).2.2.2.1
      (torusGroup_le_parabolicLevi {i | i ≠ l10sx78_a_i₀ τ} hT)
  have hhS : H ∈ l10sx78_a_scalarGroup τ K (highRoot τ) := by
    rw [hH]
    exact l10sx78_a_torusElt_mem_scalarGroup hτ u
  have hhμ : H * pinnedX τ K (highRoot τ) 1 * H⁻¹ = pinnedX τ K (highRoot τ) μ := by
    have hexp : ∑ j, Tag.cartan τ (l10sx78_a_i₀ τ) j * highRoot τ j = 1 := by
      rw [(l10sx78_a_highRootData hτ).coPair (l10sx78_a_i₀ τ), if_pos rfl]
    rw [hH]
    change torusElt τ K (l10sx78_a_i₀ τ) u * pinnedX τ K (highRoot τ) 1 *
        (torusElt τ K (l10sx78_a_i₀ τ) u)⁻¹ = pinnedX τ K (highRoot τ) μ
    rw [conj_pinnedX_of_mem_torusGroup (torusElt_mem_torusGroup (l10sx78_a_i₀ τ) u) hθ.1 1,
      torusRootChar_torusElt (l10sx78_a_i₀ τ) u hθ.1, hexp, zpow_one, mul_one]
    rfl
  set G : ModGL τ K := (g : ModGL τ K) with hG
  have hP' : G ∈ parabolicSubgroup τ K {i | i ≠ l10sx78_a_i₀ τ} := by
    rw [hG]; exact hP
  have hgc_conj : (H⁻¹ * G) * pinnedX τ K (highRoot τ) 1 * (H⁻¹ * G)⁻¹ =
      pinnedX τ K (highRoot τ) 1 := by
    calc (H⁻¹ * G) * pinnedX τ K (highRoot τ) 1 * (H⁻¹ * G)⁻¹
        = H⁻¹ * (G * pinnedX τ K (highRoot τ) 1 * G⁻¹) * H := by group
      _ = H⁻¹ * pinnedX τ K (highRoot τ) μ * H := by
          rw [show G * pinnedX τ K (highRoot τ) 1 * G⁻¹ =
            pinnedX τ K (highRoot τ) μ from by rw [hG]; exact hgμ]
      _ = pinnedX τ K (highRoot τ) 1 := by
          rw [← hhμ]; group
  have hgc : (H⁻¹ * G) * pinnedX τ K (highRoot τ) 1 =
      pinnedX τ K (highRoot τ) 1 * (H⁻¹ * G) := by
    calc (H⁻¹ * G) * pinnedX τ K (highRoot τ) 1
        = (H⁻¹ * G) * pinnedX τ K (highRoot τ) 1 * (H⁻¹ * G)⁻¹ * (H⁻¹ * G) := by group
      _ = pinnedX τ K (highRoot τ) 1 * (H⁻¹ * G) := by rw [hgc_conj]
  have hmem := RootCentExc.mem_closure_radLeviGens hθ hco
    (l10sx78_a_leviGens_centralizes hτ (K := K)) (mul_mem (inv_mem hPlevi) hP') hgc
  have hg'S : H⁻¹ * G ∈ l10sx78_a_scalarGroup τ K (highRoot τ) :=
    l10sx78_a_closure_radLeviGens_le_scalarGroup hτ hmem
  have hg_eq : G = H * (H⁻¹ * G) := by group
  rw [hg_eq]
  exact mul_mem hhS hg'S

private theorem l10sx78_field_trivial
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ₀ : Fin (adjDatum (rootOperatorFamily τ) K).rank → ℤ}
    (hγ₀ : γ₀ ∈ (adjDatum (rootOperatorFamily τ) K).roots)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily τ) K).roots, ∑ i, δ i ≤ ∑ i, γ₀ i)
    (y : MulAut ↥(adjointGroup τ K)) (g : ↥(adjointGroup τ K)) (σ : K ≃+* K)
    (hyeq : ∀ h : ↥(adjointGroup τ K), (y h : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (g : ModGL τ K)⁻¹)
    (hyR : ((adjDatum (rootOperatorFamily τ) K).rootGroup γ₀).map y.toMonoidHom =
      (adjDatum (rootOperatorFamily τ) K).rootGroup γ₀)
    (hy : ∀ m ∈ Subgroup.normalizer
        (((adjDatum (rootOperatorFamily τ) K).rootGroup γ₀ :
          Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)),
      y m * m⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer
        (((adjDatum (rootOperatorFamily τ) K).rootGroup γ₀ :
          Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)))) :
    σ = 1 := by
  have hθroot : IsRoot τ (highRoot τ) := (l10sx78_a_highRootData hτ).maxHeight.1
  have hγ : IsRoot τ γ₀ := mem_adjDatum_roots.1 hγ₀
  have hθmem : highRoot τ ∈ (adjDatum (rootOperatorFamily τ) K).roots :=
    mem_adjDatum_roots.2 hθroot
  have hsum : ht (highRoot τ) ≤ ht γ₀ := by
    simpa only [ht] using hmax (highRoot τ) hθmem
  have hγ₀eq : γ₀ = highRoot τ := l10sx78_a_eq_highRoot_of_isRoot_maxHeight hτ hγ hsum
  subst hγ₀eq
  have hgμ_exists : ∃ μ : K, (g : ModGL τ K) * pinnedX τ K (highRoot τ) 1 *
      (g : ModGL τ K)⁻¹ = pinnedX τ K (highRoot τ) μ := by
    let z : ↥(adjointGroup τ K) := ⟨pinnedX τ K (highRoot τ) 1,
      pinnedX_mem_adjointGroup _ _⟩
    have hz : z ∈ (adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) := by
      rw [l10sx78_a_rootGroup_eq_subgroupOf hτ K]
      exact Subgroup.mem_subgroupOf.2 (mem_rootSubgroup.2 ⟨1, rfl⟩)
    have hyz : y z ∈ (adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) := by
      rw [← hyR]
      exact ⟨z, hz, rfl⟩
    have hyz' : (y z : ModGL τ K) ∈ rootSubgroup τ K (highRoot τ) := by
      rw [l10sx78_a_rootGroup_eq_subgroupOf hτ K] at hyz
      exact Subgroup.mem_subgroupOf.1 hyz
    obtain ⟨μ, hμ⟩ := mem_rootSubgroup.1 hyz'
    refine ⟨μ, ?_⟩
    have hentry : Units.map (entrywiseHom σ.toRingHom) (pinnedX τ K (highRoot τ) 1) =
        pinnedX τ K (highRoot τ) 1 := by
      refine Units.ext ?_
      rw [Units.coe_map]
      change entrywise σ.toRingHom (pinnedX τ K (highRoot τ) 1 :
        Module.End K (RootModule τ K)) = pinnedX τ K (highRoot τ) 1
      rw [entrywise_pinnedX, map_one]
    have h1 : (y z : ModGL τ K) = (g : ModGL τ K) * pinnedX τ K (highRoot τ) 1 *
        (g : ModGL τ K)⁻¹ := by
      rw [hyeq z]
      change (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (pinnedX τ K (highRoot τ) 1) *
        (g : ModGL τ K)⁻¹ = (g : ModGL τ K) * pinnedX τ K (highRoot τ) 1 *
        (g : ModGL τ K)⁻¹
      rw [hentry]
    exact h1.symm.trans hμ.symm
  obtain ⟨μ, hgμ⟩ := hgμ_exists
  obtain ⟨l, hl⟩ := l10sx78_a_normalizer_conj_scalar hτ (K := K) hgμ
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := hl 1
    rw [h0, mul_one, pinnedX_zero] at h1
    have hX1 : pinnedX τ K (highRoot τ) 1 = 1 := by
      have := congrArg (fun z : ModGL τ K => (g : ModGL τ K)⁻¹ * z * (g : ModGL τ K)) h1
      simpa [mul_assoc] using this
    exact one_ne_zero (pinnedX_injective τ K (highRoot τ)
      (hX1.trans (pinnedX_zero τ K (highRoot τ)).symm))
  have hcent := l10sx78_a_pCore_le_centralizer_highRoot hτ (K := K)
  have hkey : ∀ t : Kˣ, σ (t : K) = (t : K) := by
    intro t
    let h : ↥(adjointGroup τ K) := ⟨torusElt τ K (l10sx78_a_i₀ τ) t,
      torusElt_mem_adjointGroup (l10sx78_a_i₀ τ) t⟩
    let x : ↥(adjointGroup τ K) := ⟨pinnedX τ K (highRoot τ) 1,
      pinnedX_mem_adjointGroup _ _⟩
    have hH : rootSubgroup τ K (highRoot τ) ≤ adjointGroup τ K :=
      rootSubgroup_le_adjointGroup (highRoot τ)
    have hχ : torusRootChar (torusElt τ K (l10sx78_a_i₀ τ) t) (highRoot τ) = (t : K) := by
      rw [torusRootChar_torusElt (l10sx78_a_i₀ τ) t hθroot]
      have hexp : ∑ j, Tag.cartan τ (l10sx78_a_i₀ τ) j * highRoot τ j = 1 := by
        rw [(l10sx78_a_highRootData hτ).coPair (l10sx78_a_i₀ τ), if_pos rfl]
      rw [hexp, zpow_one]
    have hh_tor : ∀ c : K, (h : ModGL τ K) * pinnedX τ K (highRoot τ) c *
        (h : ModGL τ K)⁻¹ = pinnedX τ K (highRoot τ) ((t : K) * c) := by
      intro c
      change torusElt τ K (l10sx78_a_i₀ τ) t * pinnedX τ K (highRoot τ) c *
          (torusElt τ K (l10sx78_a_i₀ τ) t)⁻¹ = pinnedX τ K (highRoot τ) ((t : K) * c)
      rw [conj_pinnedX_of_mem_torusGroup (torusElt_mem_torusGroup (l10sx78_a_i₀ τ) t)
        hθroot c, hχ]
    have hN : h ∈ Subgroup.normalizer ((adjDatum (rootOperatorFamily τ) K).rootGroup
        (highRoot τ) : Set ↥(adjointGroup τ K)) := by
      rw [l10sx78_a_rootGroup_eq_subgroupOf hτ K, ← Subgroup.subgroupOf_normalizer_eq hH,
        Subgroup.mem_subgroupOf]
      exact RootCentExc.torusGroup_le_normalizer_rootSubgroup hθroot
        (torusElt_mem_torusGroup (l10sx78_a_i₀ τ) t)
    have hxR : x ∈ (adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) := by
      rw [l10sx78_a_rootGroup_eq_subgroupOf hτ K]
      exact Subgroup.mem_subgroupOf.2 (mem_rootSubgroup.2 ⟨1, rfl⟩)
    have hconj := l10sx78_a_conj_eq_of_mem hcent hy hN hxR
    have hRHS : (h : ModGL τ K) * (x : ModGL τ K) * (h : ModGL τ K)⁻¹ =
        pinnedX τ K (highRoot τ) (t : K) := by
      change torusElt τ K (l10sx78_a_i₀ τ) t * pinnedX τ K (highRoot τ) 1 *
          (torusElt τ K (l10sx78_a_i₀ τ) t)⁻¹ = pinnedX τ K (highRoot τ) (t : K)
      rw [conj_pinnedX_of_mem_torusGroup (torusElt_mem_torusGroup (l10sx78_a_i₀ τ) t)
        hθroot 1, hχ, mul_one]
    have hginv : (g : ModGL τ K)⁻¹ * pinnedX τ K (highRoot τ) 1 * (g : ModGL τ K) =
        pinnedX τ K (highRoot τ) l⁻¹ := by
      have h1 := hl l⁻¹
      rw [mul_inv_cancel₀ hl0] at h1
      calc (g : ModGL τ K)⁻¹ * pinnedX τ K (highRoot τ) 1 * (g : ModGL τ K)
          = (g : ModGL τ K)⁻¹ * ((g : ModGL τ K) * pinnedX τ K (highRoot τ) l⁻¹ *
              (g : ModGL τ K)⁻¹) * (g : ModGL τ K) := by rw [h1]
        _ = pinnedX τ K (highRoot τ) l⁻¹ := by group
    have hLHS : (y h : ModGL τ K) * (x : ModGL τ K) * (y h : ModGL τ K)⁻¹ =
        pinnedX τ K (highRoot τ) (σ (t : K)) := by
      change (y h : ModGL τ K) * pinnedX τ K (highRoot τ) 1 * (y h : ModGL τ K)⁻¹ =
        pinnedX τ K (highRoot τ) (σ (t : K))
      rw [hyeq h]
      calc (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
              (g : ModGL τ K)⁻¹ * pinnedX τ K (highRoot τ) 1 *
              ((g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
                (g : ModGL τ K)⁻¹)⁻¹
          = (g : ModGL τ K) * (Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
              ((g : ModGL τ K)⁻¹ * pinnedX τ K (highRoot τ) 1 * (g : ModGL τ K)) *
              (Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))⁻¹) *
              (g : ModGL τ K)⁻¹ := by group
        _ = (g : ModGL τ K) * (Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
              pinnedX τ K (highRoot τ) l⁻¹ *
              (Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K))⁻¹) *
              (g : ModGL τ K)⁻¹ := by rw [hginv]
        _ = (g : ModGL τ K) * pinnedX τ K (highRoot τ) (σ (t : K) * l⁻¹) *
              (g : ModGL τ K)⁻¹ := by
              rw [l10sx78_a_entrywise_conj_pinnedX σ (t : K) hh_tor l⁻¹]
        _ = pinnedX τ K (highRoot τ) (l * (σ (t : K) * l⁻¹)) := hl (σ (t : K) * l⁻¹)
        _ = pinnedX τ K (highRoot τ) (σ (t : K)) := by
              congr 1
              rw [← mul_assoc, mul_comm l (σ (t : K)), mul_assoc, mul_inv_cancel₀ hl0, mul_one]
    have hval : pinnedX τ K (highRoot τ) (σ (t : K)) =
        pinnedX τ K (highRoot τ) (t : K) := by
      have heq := congrArg Subtype.val hconj
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at heq
      rw [hLHS, hRHS] at heq
      exact heq
    exact pinnedX_injective τ K (highRoot τ) hval
  refine RingEquiv.ext fun a => ?_
  by_cases ha : a = 0
  · subst ha
    simpa using map_zero σ
  · simpa using hkey (Units.mk0 a ha)

private theorem l10sx78_inner_maxHeight
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f)
    {γ₀ : Fin (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rank → ℤ}
    (hγ₀ : γ₀ ∈ (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).roots)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).roots,
      ∑ i, δ i ≤ ∑ i, γ₀ i) :
    GGRootNormInner ((adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rootGroup γ₀) := by
  intro y hy2 hyR hytriv
  haveI : CharP (GaloisField 2 f) 2 := inferInstance
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hnf, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf
    (GaloisField 2 f) hcard τ hτ
  obtain ⟨⟨g, σ⟩, hyeq, -⟩ := hnf y
  have hσ : σ = 1 := l10sx78_field_trivial hτ hγ₀ hmax y g σ hyeq hyR hytriv
  subst hσ
  refine ⟨g, ?_⟩
  refine MulEquiv.ext fun h => Subtype.ext ?_
  have hvey : Units.map (entrywiseHom (RingHom.id (GaloisField 2 f)))
      (h : ModGL τ (GaloisField 2 f)) = (h : ModGL τ (GaloisField 2 f)) := by
    apply Units.ext
    simpa [entrywiseHom] using RootDetectExc.entrywise_ringHomId
      ((h : ModGL τ (GaloisField 2 f)) :
        Module.End (GaloisField 2 f) (RootModule τ (GaloisField 2 f)))
  have hconv := hyeq h
  rw [show (1 : GaloisField 2 f ≃+* GaloisField 2 f).toRingHom =
    RingHom.id (GaloisField 2 f) from rfl] at hconv
  rw [hvey] at hconv
  rw [MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hconv ⊢
  exact hconv

private theorem l10sx78_inner_root
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rank → ℤ}
    (hβ : β ∈ (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).roots) :
    GGRootNormInner ((adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rootGroup β) := by
  have hsym : ∀ i j, (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).cartan i j =
      (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).cartan j i := by
    rcases hτ with rfl | rfl
    · exact cartanE_symm 7
    · exact cartanE_symm 8
  have hirr : CFSG.ClassicalInvolution.ModelFacts.IsIrreducible
      (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).cartan := by
    rcases hτ with rfl | rfl
    · exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7
    · exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8
  obtain ⟨w, γ₀, hγ₀mem, hγ₀max, hβeq⟩ :=
    ggLongRoot_of_symmetric hirr hsym rfl hβ
  have hI0 := l10sx78_inner_maxHeight τ hτ hf hγ₀mem hγ₀max
  have hct := adjDatum_isCTGroupDatum (rootOperatorFamily τ) (GaloisField 2 f)
  set m : adjointGroup τ (GaloisField 2 f) :=
    CFSG.LieType.Steinberg.nrep hct w with hm
  have ham : CFSG.LieType.Steinberg.ActsAs
      (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)) m w := by
    rw [hm]
    exact CFSG.LieType.Steinberg.actsAs_nrep hct w
  have hβmap : (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rootGroup β =
      ((adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rootGroup γ₀).map
        (MulAut.conj m).toMonoidHom := by
    rw [hβeq, ← ham γ₀ hγ₀mem]
  have hI := ggRootNormInner_map_mulEquiv (MulAut.conj m) hI0
  rwa [← hβmap] at hI

theorem ggRootNormInner_adj_E78
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    {β : Fin (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rank → ℤ}
    (hβ : β ∈ (adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).roots) :
    GGRootNormInner ((adjDatum (rootOperatorFamily τ) (GaloisField 2 f)).rootGroup β) :=
  l10sx78_inner_root τ hτ hf hβ

end CFSG.StandardType.LieKnownR2.ExcInner
