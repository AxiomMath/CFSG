module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.Timmesfeld CFSG.HardMathSupport.Timmesfeld.RootAut
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private theorem rckTwAut_iform_single_single_E6
    (i j : Fin Tag.E6.rank) :
    CFSG.LieType.Steinberg.Adjoint.iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
      (Pi.single j 1) = Tag.E6.cartan i j := by
  rw [rckIo_iform_single_left_eq_E6]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

private theorem rckTwAut_isRootComponent_E6 :
    IsRootComponent ({γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}) := by
  let χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (ZMod 2) := 1
  have hχ : ∀ γ : Fin Tag.E6.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1 := fun γ => rfl
  let i : KernelComponent χ :=
    Quotient.mk _ ⟨(Pi.single 0 1 : Fin Tag.E6.rank → ℤ),
      ⟨isRoot_single Tag.E6 0, hχ _⟩⟩
  rw [← CFSG.StandardType.TableCRes.famTrivial_componentRoots_eq_univ
    (τ := Tag.E6) (Or.inl rfl) χ hχ i]
  exact isRootComponent_componentRoots i

private theorem rckTwAut_compRank_E6 :
    compRank ({γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}) = 6 := by
  unfold compRank
  have htop : Submodule.span ℚ ((fun γ (i : Fin Tag.E6.rank) => (γ i : ℚ)) ''
      {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α}) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v k • (Pi.single k (1 : ℚ) : Fin Tag.E6.rank → ℚ) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
    rw [hv]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨Pi.single k 1, IsRoot.basis k, ?_⟩
    funext j
    simp [Pi.single_apply]
  rw [htop, finrank_top, Module.finrank_fin_fun]
  rfl

private theorem rckTwAut_simpleRoots_E6 :
    Finset.univ.image (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
      simpleRoots ({γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}) := by
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := {γ : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 γ}
  have hΨ : IsRootComponent Ψ := rckTwAut_isRootComponent_E6
  have hsub : Finset.univ.image (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
      ⊆ simpleRoots Ψ := by
    intro β hβ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hβ
    rw [CFSG.LieType.Chevalley.mem_simpleRoots]
    refine ⟨IsRoot.basis i, ⟨IsRoot.basis i, ?_⟩, ?_⟩
    · rw [height_single]; exact one_pos
    · intro γ hγ δ hδ e
      have h1 : height (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = height γ + height δ := by
        rw [e, height_add]
      rw [height_single] at h1
      have h2 : 0 < height γ := hγ.2
      have h3 : 0 < height δ := hδ.2
      omega
  have hinj : Function.Injective
      (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
    intro i j h
    by_contra hij
    have := congrFun h i
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij] at this
    exact one_ne_zero this
  have hcard_image : (Finset.univ.image
      (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ))).card = 6 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    rfl
  have hcard_simple : (simpleRoots Ψ).card = 6 := by
    rw [← compRank_eq_card hΨ, rckTwAut_compRank_E6]
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_simple, hcard_image])

private theorem rckTwAut_permLattice_symm_apply (π : Equiv.Perm (Fin Tag.E6.rank))
    (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := Tag.E6) π.symm (permLattice (τ := Tag.E6) π v) = v := by
  ext j
  simp [permLattice, Function.comp_apply]

private theorem rckTwAut_permLattice_apply_symm (π : Equiv.Perm (Fin Tag.E6.rank))
    (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := Tag.E6) π (permLattice (τ := Tag.E6) π.symm v) = v := by
  ext j
  simp [permLattice, Function.comp_apply]

private theorem rckTwAut_permLattice_neg (π : Equiv.Perm (Fin Tag.E6.rank))
    (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := Tag.E6) π (-v) = -permLattice (τ := Tag.E6) π v := by
  ext j
  simp [permLattice]

private theorem rckTwAut_permLattice_one (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := Tag.E6) (1 : Equiv.Perm (Fin Tag.E6.rank)) v = v := by
  ext j
  simp [permLattice, Equiv.Perm.one_symm]

private theorem rckTwAut_iform_permLattice_E6
    {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : ∀ i j, Tag.E6.cartan (π i) (π j) = Tag.E6.cartan i j)
    (x y : Fin Tag.E6.rank → ℤ) :
    CFSG.LieType.Steinberg.Adjoint.iform (permLattice (τ := Tag.E6) π x)
      (permLattice (τ := Tag.E6) π y) = CFSG.LieType.Steinberg.Adjoint.iform x y := by
  have hB : ∀ i j, Tag.E6.symmetrizedCartan (π i) (π j) = Tag.E6.symmetrizedCartan i j := by
    intro i j
    rw [rckIo_symmetrizedCartan_eq_E6, rckIo_symmetrizedCartan_eq_E6]
    exact hπ i j
  simp only [CFSG.LieType.Steinberg.Adjoint.iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp π (fun i => ∑ j, x (π.symm i) * Tag.E6.symmetrizedCartan i j *
    y (π.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp π (fun j => x (π.symm (π i)) *
    Tag.E6.symmetrizedCartan (π i) j * y (π.symm j))]
  simp [hB]

private theorem rckTwAut_excDiagramSigmaE6_eq_perm :
    excDiagramSigmaE6 = TwistTag.E6.perm := rfl

private theorem rckTwAut_permLattice_e6Rho_involutive (v : Fin Tag.E6.rank → ℤ) :
    permLattice (τ := Tag.E6) TwistTag.E6.perm
      (permLattice (τ := Tag.E6) TwistTag.E6.perm v) = v := by
  ext j
  simp only [permLattice, Function.comp_apply]
  congr 1
  fin_cases j <;> decide

private theorem rckTwAut_isIsometry_comp {Ψ : Set (Fin Tag.E6.rank → ℤ)}
    {f g : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}
    (hf : IsIsometry Ψ f) (hg : IsIsometry Ψ g) :
    IsIsometry Ψ (fun γ => f (g γ)) := by
  refine ⟨hf.bijOn.comp hg.bijOn, ?_, ?_⟩
  · intro γ hγ δ hδ
    rw [hf.iform_eq (g γ) (hg.bijOn.mapsTo hγ) (g δ) (hg.bijOn.mapsTo hδ),
      hg.iform_eq γ hγ δ hδ]
  · intro γ hγ
    rw [hg.neg γ hγ, hf.neg (g γ) (hg.bijOn.mapsTo hγ)]

theorem rckTw_aut_E6
    {α : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hbij : Set.BijOn α {γ | IsRoot Tag.E6 γ} {γ | IsRoot Tag.E6 γ})
    (hneg : ∀ γ, IsRoot Tag.E6 γ → α (-γ) = -α γ)
    (hform : ∀ γ δ, IsRoot Tag.E6 γ → IsRoot Tag.E6 δ →
      CFSG.LieType.Steinberg.Adjoint.iform (α γ) (α δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ) :
    (∃ w : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → α γ = w • γ) ∨
      (∃ w : WeylGroup Tag.E6, ∀ γ, IsRoot Tag.E6 γ → α γ = w • permLattice (τ := Tag.E6) TwistTag.E6.perm γ) := by
  classical
  let Ψ : Set (Fin Tag.E6.rank → ℤ) := {γ | IsRoot Tag.E6 γ}
  have hΨ : IsRootComponent Ψ := rckTwAut_isRootComponent_E6
  let α' : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ := Function.invFunOn α Ψ
  have hinv : Set.InvOn α' α Ψ Ψ := Set.BijOn.invOn_invFunOn hbij
  have hbij' : Set.BijOn α' Ψ Ψ := hbij.symm hinv.symm
  have hα'α : ∀ x ∈ Ψ, α' (α x) = x := hinv.1
  have hαα' : ∀ y ∈ Ψ, α (α' y) = y := hinv.2
  have hf : IsIsometry Ψ α' := by
    refine ⟨hbij', ?_, ?_⟩
    · intro γ hγ δ hδ
      have h := hform (α' γ) (α' δ) (hbij'.mapsTo hγ) (hbij'.mapsTo hδ)
      rw [hαα' γ hγ, hαα' δ hδ] at h
      exact h.symm
    · intro γ hγ
      apply hbij.injOn (hbij'.mapsTo (hΨ.neg_mem γ hγ)) (hΨ.neg_mem _ (hbij'.mapsTo hγ))
      rw [hαα' (-γ) (hΨ.neg_mem γ hγ), hneg (α' γ) (hbij'.mapsTo hγ), hαα' γ hγ]
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ (fun γ => α' (w • γ)) := hf.comp_smul hΨ hw
  have hsimple : Finset.univ.image
      (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = simpleRoots Ψ :=
    rckTwAut_simpleRoots_E6
  have hsimple_mem : ∀ i : Fin Tag.E6.rank,
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ simpleRoots Ψ := by
    intro i
    rw [← hsimple]
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
  have himage : ∀ i, α' (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈
      Finset.univ.image (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
    intro i
    rw [hsimple]
    exact hf'.apply_mem_simpleRoots hΨ hpos (hsimple_mem i)
  let σ : Fin Tag.E6.rank → Fin Tag.E6.rank := fun i => (Finset.mem_image.1 (himage i)).choose
  have hσ : ∀ i, α' (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = Pi.single (σ i) 1 :=
    fun i => ((Finset.mem_image.1 (himage i)).choose_spec.2).symm
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h_eq : α' (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) =
        α' (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by rw [hσ i, hσ j, hij]
    have hsingle : (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = Pi.single j 1 :=
      hf'.bijOn.injOn (IsRoot.basis i) (IsRoot.basis j) h_eq
    by_contra hne
    have := congrFun hsingle i
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  let σe : Equiv.Perm (Fin Tag.E6.rank) :=
    Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hσM : ∀ i j, Tag.E6.cartan (σe i) (σe j) = Tag.E6.cartan i j := by
    intro i j
    change Tag.E6.cartan (σ i) (σ j) = Tag.E6.cartan i j
    rw [← rckTwAut_iform_single_single_E6 (σ i) (σ j), ← hσ i, ← hσ j,
      hf'.iform_eq (Pi.single i 1) (IsRoot.basis i) (Pi.single j 1) (IsRoot.basis j),
      rckTwAut_iform_single_single_E6 i j]
  have hwe : ∀ i, w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = α (Pi.single (σ i) 1) := by
    intro i
    have hmem : w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ Ψ :=
      smul_mem_of_mem_componentWeylGroup hΨ hw (Pi.single i 1) (IsRoot.basis i)
    have h1 : α (α' (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = α (Pi.single (σ i) 1) :=
      congrArg α (hσ i)
    rw [hαα' (w • (Pi.single i 1)) hmem] at h1
    exact h1
  have hformΨ : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ,
      CFSG.LieType.Steinberg.Adjoint.iform (α γ) (α δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ := by
    intro γ hγ δ hδ
    exact hform γ δ hγ hδ
  have hα_iso : IsIsometry Ψ α := ⟨hbij, hformΨ, hneg⟩
  have hperm : IsIsometry Ψ (fun γ => permLattice (τ := Tag.E6) σe γ) := by
    have hmaps : Set.MapsTo (fun γ => permLattice (τ := Tag.E6) σe γ) Ψ Ψ :=
      fun γ hγ => IsRoot.permLattice hσM hγ
    have hmaps' : Set.MapsTo (fun γ => permLattice (τ := Tag.E6) σe.symm γ) Ψ Ψ :=
      fun γ hγ => IsRoot.permLattice (cartan_perm_symm hσM) hγ
    refine ⟨?_, ?_, ?_⟩
    · refine Set.InvOn.bijOn ⟨?_, ?_⟩ hmaps hmaps'
      · intro γ _
        exact rckTwAut_permLattice_symm_apply σe γ
      · intro γ _
        exact rckTwAut_permLattice_apply_symm σe γ
    · intro γ _ δ _
      exact rckTwAut_iform_permLattice_E6 hσM γ δ
    · intro γ _
      exact rckTwAut_permLattice_neg σe γ
  have hw_smul : IsIsometry Ψ (fun γ => w⁻¹ • γ) := by
    have hmaps : Set.MapsTo (fun γ => w⁻¹ • γ) Ψ Ψ :=
      fun γ hγ => smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hw) γ hγ
    have hmaps' : Set.MapsTo (fun γ => w • γ) Ψ Ψ :=
      fun γ hγ => smul_mem_of_mem_componentWeylGroup hΨ hw γ hγ
    refine ⟨?_, ?_, ?_⟩
    · refine Set.InvOn.bijOn ⟨?_, ?_⟩ hmaps hmaps'
      · intro γ _; exact smul_inv_smul w γ
      · intro γ _; exact inv_smul_smul w γ
    · intro γ _ δ _; exact iform_smul w⁻¹ γ δ
    · intro γ _; exact smul_neg w⁻¹ γ
  have hh : IsIsometry Ψ (fun γ => w⁻¹ • α (permLattice (τ := Tag.E6) σe γ)) :=
    rckTwAut_isIsometry_comp hw_smul (rckTwAut_isIsometry_comp hα_iso hperm)
  have hfix : ∀ β ∈ simpleRoots Ψ, (fun γ => w⁻¹ • α (permLattice (τ := Tag.E6) σe γ)) β = β := by
    intro β hβ
    have hβ' : β ∈ Finset.univ.image
        (fun i : Fin Tag.E6.rank => (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := by
      rw [hsimple]; exact hβ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hβ'
    change w⁻¹ • α (permLattice (τ := Tag.E6) σe (Pi.single i 1)) = Pi.single i 1
    rw [permLattice_single]
    change w⁻¹ • α (Pi.single (σ i) 1) = Pi.single i 1
    rw [← hwe i, inv_smul_smul]
  have hId : ∀ γ ∈ Ψ, w⁻¹ • α (permLattice (τ := Tag.E6) σe γ) = γ :=
    fun γ hγ => hh.eq_self_of_simpleRoots hΨ hfix hγ
  have hmain : ∀ γ ∈ Ψ, α (permLattice (τ := Tag.E6) σe γ) = w • γ := by
    intro γ hγ
    have h := hId γ hγ
    calc α (permLattice (τ := Tag.E6) σe γ)
        = w • (w⁻¹ • α (permLattice (τ := Tag.E6) σe γ)) := (smul_inv_smul w _).symm
      _ = w • γ := by rw [h]
  rcases perm_eq_one_or_eq_sigma_of_cartan_E6 σe hσM with h1 | h2
  · left
    refine ⟨w, fun γ hγ => ?_⟩
    have h := hmain γ hγ
    rw [h1, rckTwAut_permLattice_one] at h
    exact h
  · right
    refine ⟨w, fun γ hγ => ?_⟩
    have h2' : σe = TwistTag.E6.perm := h2.trans rckTwAut_excDiagramSigmaE6_eq_perm
    have hγp : permLattice (τ := Tag.E6) σe γ ∈ Ψ := IsRoot.permLattice hσM hγ
    have h := hmain (permLattice (τ := Tag.E6) σe γ) hγp
    have hinv : permLattice (τ := Tag.E6) σe (permLattice (τ := Tag.E6) σe γ) = γ := by
      rw [h2']
      exact rckTwAut_permLattice_e6Rho_involutive γ
    rw [hinv] at h
    rw [h2'] at h
    exact h

private theorem rckTwAut_weyl_transport_converse
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (w : WeylGroup Tag.E6) :
    ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ rootsOfFam β Set.univ, s = rootReflection γ},
      ∀ γ ∈ rootsOfFam β Set.univ,
        u • γ ∈ rootsOfFam β Set.univ ∧ ι (u • γ) = w • ι γ := by
  classical
  obtain ⟨hbij_ι, hsingle, hsum, hneg_ι, hform_ι⟩ := hι
  obtain ⟨hmaps_ι, hinj_ι, hsurj_ι⟩ := hbij_ι
  let Ψ' : Set (Fin τ.rank → ℤ) := rootsOfFam β Set.univ
  let βE : Fin Tag.E6.rank → Fin τ.rank → ℤ := β
  have hsumL : ∀ γ ∈ Ψ', rckIo_L βE (ι γ) = γ := fun γ hγ => hsum γ hγ
  have hτsl : SimplyLacedTag τ := by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hnorm : ∀ {γ : Fin τ.rank → ℤ}, γ ∈ Ψ' → iform γ γ = 2 := by
    intro γ hγ
    have h1 : iform (τ := Tag.E6) (ι γ) (ι γ) = iform γ γ := hform_ι γ hγ γ hγ
    have h2 : iform (τ := Tag.E6) (ι γ) (ι γ) = 2 :=
      rckIo_iform_self_eq_two_sl (Or.inr (Or.inl rfl)) (hmaps_ι hγ)
    rw [h2] at h1
    exact h1.symm
  have hrefl : ∀ {γ₀ : Fin τ.rank → ℤ}, γ₀ ∈ Ψ' → ∀ v,
      rootReflection γ₀ • v = v - iform γ₀ v • γ₀ := by
    intro γ₀ hγ₀ v
    have hcp : corootPair γ₀ v = iform γ₀ v := by
      have := corootPair_mul hγ₀.1 v
      rw [hnorm hγ₀] at this
      omega
    rw [rootReflection_smul hγ₀.1, hcp]
  have hreflE6 : ∀ {γ₀ : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 γ₀ → ∀ v,
      rootReflection γ₀ • v = v - iform γ₀ v • γ₀ := by
    intro γ₀ hγ₀ v
    have hcp : corootPair γ₀ v = iform γ₀ v := by
      have := corootPair_mul hγ₀ v
      rw [rckIo_iform_self_eq_two_sl (Or.inr (Or.inl rfl)) hγ₀] at this
      omega
    rw [rootReflection_smul hγ₀, hcp]
  have hgen : ∀ γ₀ ∈ Ψ', ∀ γ ∈ Ψ',
      rootReflection γ₀ • γ ∈ Ψ' ∧ rootReflection (ι γ₀) • ι γ = ι (rootReflection γ₀ • γ) := by
    intro γ₀ hγ₀ γ hγ
    have hιγ₀ : IsRoot Tag.E6 (ι γ₀) := hmaps_ι hγ₀
    have hιγ : IsRoot Tag.E6 (ι γ) := hmaps_ι hγ
    have hE6 : rootReflection (ι γ₀) • ι γ = ι γ - iform (ι γ₀) (ι γ) • ι γ₀ :=
      hreflE6 hιγ₀ (ι γ)
    have hrootE6 : IsRoot Tag.E6 (rootReflection (ι γ₀) • ι γ) :=
      IsRoot.smul hιγ (rootReflection (ι γ₀))
    obtain ⟨δ, hδ, hδι⟩ := hsurj_ι hrootE6
    have hLrefl : rckIo_L βE (rootReflection (ι γ₀) • ι γ) = rootReflection γ₀ • γ := by
      rw [hE6, rckIo_L_sub, rckIo_L_smul, hsumL γ₀ hγ₀, hsumL γ hγ,
        hform_ι γ₀ hγ₀ γ hγ, hrefl hγ₀ γ]
    have hδeq : rootReflection γ₀ • γ = δ := by
      rw [← hLrefl, ← hδι, hsumL δ hδ]
    refine ⟨?_, ?_⟩
    · rw [hδeq]; exact hδ
    · rw [hδeq]; exact hδι.symm
  have hrefl_simple : ∀ i : Fin Tag.E6.rank,
      rootReflection (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) = simple Tag.E6 i := by
    intro i
    simpa using rootReflection_eq_conj (w := 1) (j := i) (β := Pi.single i 1) (by simp)
  induction w using (coxeterSystem Tag.E6).simple_induction_left with
  | one =>
      exact ⟨1, one_mem _, fun γ hγ =>
        ⟨by rw [one_smul]; exact hγ, by rw [one_smul, one_smul]⟩⟩
  | mul_simple_left w i ih =>
      obtain ⟨u, hu, hP⟩ := ih
      have hβi : β i ∈ Ψ' := (rckA4_mem_rootsOfFam β hroot i).1
      refine ⟨rootReflection (β i) * u,
        mul_mem (Subgroup.subset_closure ⟨β i, hβi, rfl⟩) hu, fun γ hγ => ?_⟩
      obtain ⟨hγmem, hγeq⟩ := hP γ hγ
      obtain ⟨hgenmem, hgeneq⟩ := hgen (β i) hβi (u • γ) hγmem
      refine ⟨by rw [mul_smul]; exact hgenmem, ?_⟩
      rw [mul_smul, ← hgeneq, hγeq, ← mul_smul]
      have hιβi : ι (β i) = (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) := hsingle i
      have hgen_simple : rootReflection (ι (β i)) = simple Tag.E6 i := by
        rw [hιβi, hrefl_simple i]
      rw [hgen_simple]

theorem rckRet_outer_transport
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)}
    (hbij : Set.BijOn ρ (rootsOfFam β Set.univ) (rootsOfFam β Set.univ))
    (hneg : ∀ γ ∈ rootsOfFam β Set.univ, ρ (-γ) = -ρ γ)
    (hform : ∀ γ ∈ rootsOfFam β Set.univ, ∀ δ ∈ rootsOfFam β Set.univ,
      CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    (hout : ¬ twistInner (rootsOfFam β Set.univ) ρ) :
    ∃ w : WeylGroup Tag.E6, ∀ γ ∈ rootsOfFam β Set.univ,
      w • permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ) = ι (ρ γ) := by
  classical
  obtain ⟨hbij_ι, hsingle, hsum, hneg_ι, hform_ι⟩ := hι
  have hbij_ι' : Set.BijOn ι (rootsOfFam β Set.univ) {γ' | IsRoot Tag.E6 γ'} := hbij_ι
  obtain ⟨hmaps_ι, hinj_ι, hsurj_ι⟩ := hbij_ι
  let Ψ' : Set (Fin τ.rank → ℤ) := rootsOfFam β Set.univ
  let βE : Fin Tag.E6.rank → Fin τ.rank → ℤ := β
  have hsumL : ∀ γ ∈ Ψ', rckIo_L βE (ι γ) = γ := fun γ hγ => hsum γ hγ
  let α : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ :=
    fun γ' => ι (ρ (rckIo_L βE γ'))
  have hLinv : Set.LeftInvOn ι (fun γ' => rckIo_L βE γ') {γ' | IsRoot Tag.E6 γ'} := by
    intro γ' hγ'
    obtain ⟨γ, hγ, hγγ'⟩ := hsurj_ι hγ'
    calc ι (rckIo_L βE γ') = ι (rckIo_L βE (ι γ)) := by rw [← hγγ']
      _ = ι γ := by rw [hsumL γ hγ]
      _ = γ' := hγγ'
  have hRinv : Set.RightInvOn ι (fun γ' => rckIo_L βE γ') Ψ' := fun γ hγ => hsumL γ hγ
  have hL_maps : Set.MapsTo (fun γ' => rckIo_L βE γ') {γ' | IsRoot Tag.E6 γ'} Ψ' := by
    intro γ' hγ'
    obtain ⟨γ, hγ, hγγ'⟩ := hsurj_ι hγ'
    change rckIo_L βE γ' ∈ Ψ'
    rw [← hγγ', hsumL γ hγ]
    exact hγ
  have hbij_L : Set.BijOn (fun γ' => rckIo_L βE γ') {γ' | IsRoot Tag.E6 γ'} Ψ' :=
    Set.InvOn.bijOn ⟨hLinv, hRinv⟩ hL_maps hmaps_ι
  have hbij_alpha : Set.BijOn α {γ' | IsRoot Tag.E6 γ'} {γ' | IsRoot Tag.E6 γ'} :=
    Set.BijOn.comp hbij_ι' (Set.BijOn.comp hbij hbij_L)
  have hneg_alpha : ∀ γ', IsRoot Tag.E6 γ' → α (-γ') = -α γ' := by
    intro γ' hγ'
    have hγ'L : rckIo_L βE γ' ∈ Ψ' := hL_maps hγ'
    calc α (-γ') = ι (ρ (rckIo_L βE (-γ'))) := rfl
      _ = ι (ρ (-(rckIo_L βE γ'))) := by rw [rckIo_L_neg]
      _ = ι (-(ρ (rckIo_L βE γ'))) := by rw [hneg _ hγ'L]
      _ = -ι (ρ (rckIo_L βE γ')) := hneg_ι _ (hbij.mapsTo hγ'L)
      _ = -α γ' := rfl
  have hform_alpha : ∀ γ' δ', IsRoot Tag.E6 γ' → IsRoot Tag.E6 δ' →
      CFSG.LieType.Steinberg.Adjoint.iform (α γ') (α δ') =
        CFSG.LieType.Steinberg.Adjoint.iform γ' δ' := by
    intro γ' δ' hγ' hδ'
    have hγ'L : rckIo_L βE γ' ∈ Ψ' := hL_maps hγ'
    have hδ'L : rckIo_L βE δ' ∈ Ψ' := hL_maps hδ'
    have hLL : CFSG.LieType.Steinberg.Adjoint.iform (rckIo_L βE γ') (rckIo_L βE δ') =
        CFSG.LieType.Steinberg.Adjoint.iform γ' δ' := by
      obtain ⟨x, hx, hxγ'⟩ := hsurj_ι hγ'
      obtain ⟨y, hy, hyδ'⟩ := hsurj_ι hδ'
      calc CFSG.LieType.Steinberg.Adjoint.iform (rckIo_L βE γ') (rckIo_L βE δ')
          = CFSG.LieType.Steinberg.Adjoint.iform (rckIo_L βE (ι x)) (rckIo_L βE (ι y)) := by
            rw [← hxγ', ← hyδ']
        _ = CFSG.LieType.Steinberg.Adjoint.iform x y := by rw [hsumL x hx, hsumL y hy]
        _ = CFSG.LieType.Steinberg.Adjoint.iform (ι x) (ι y) := (hform_ι x hx y hy).symm
        _ = CFSG.LieType.Steinberg.Adjoint.iform γ' δ' := by rw [hxγ', hyδ']
    calc CFSG.LieType.Steinberg.Adjoint.iform (α γ') (α δ')
        = CFSG.LieType.Steinberg.Adjoint.iform (ι (ρ (rckIo_L βE γ')))
            (ι (ρ (rckIo_L βE δ'))) := rfl
      _ = CFSG.LieType.Steinberg.Adjoint.iform (ρ (rckIo_L βE γ')) (ρ (rckIo_L βE δ')) :=
            hform_ι _ (hbij.mapsTo hγ'L) _ (hbij.mapsTo hδ'L)
      _ = CFSG.LieType.Steinberg.Adjoint.iform (rckIo_L βE γ') (rckIo_L βE δ') :=
            hform _ hγ'L _ hδ'L
      _ = CFSG.LieType.Steinberg.Adjoint.iform γ' δ' := hLL
  rcases rckTw_aut_E6 hbij_alpha hneg_alpha hform_alpha with ⟨w, hw⟩ | ⟨w, hw⟩
  · exfalso
    obtain ⟨u, hu, huP⟩ := rckTwAut_weyl_transport_converse hτ hroot
      ⟨hbij_ι', hsingle, hsum, hneg_ι, hform_ι⟩ w
    apply hout
    refine ⟨u, hu, fun γ hγ => ?_⟩
    have hE6 : IsRoot Tag.E6 (ι γ) := hmaps_ι hγ
    have h1 : α (ι γ) = w • ι γ := hw (ι γ) hE6
    have h2 : α (ι γ) = ι (ρ γ) := by
      change ι (ρ (rckIo_L βE (ι γ))) = ι (ρ γ)
      rw [hsumL γ hγ]
    have h3 : ι (u • γ) = w • ι γ := (huP γ hγ).2
    have hmem : u • γ ∈ Ψ' := (huP γ hγ).1
    exact hinj_ι (hbij.mapsTo hγ) hmem (h2.symm.trans (h1.trans h3.symm))
  · refine ⟨w, fun γ hγ => ?_⟩
    have hE6 : IsRoot Tag.E6 (ι γ) := hmaps_ι hγ
    have h1 : α (ι γ) = w • permLattice (τ := Tag.E6) TwistTag.E6.perm (ι γ) := hw (ι γ) hE6
    have h2 : α (ι γ) = ι (ρ γ) := by
      change ι (ρ (rckIo_L βE (ι γ))) = ι (ρ γ)
      rw [hsumL γ hγ]
    rw [← h1, h2]

end CFSG.StandardType.RCKRP

end
