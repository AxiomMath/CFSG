module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitEtaCommute
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.LinearAlgebra.SL2CharTwoInvolution
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2W_conj_sl2Diag)
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.QuasithinUnique (IsSylowTwoOf isSylowTwoOf_top_of_sylow)
open TauCeti.Subgroup (normalizerQuotient)

private noncomputable def omegaPlusIota (F : Type) [Field F] (n : ℕ)
    (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3) :
    Fin 4 → SpecialLinearGroup (Fin 2) F →*
      orthElementaryGroup (quadPlus n F) :=
  ![etaMinus i0 i1 h01, etaPlus i0 i1 h01, etaMinus i2 i3 h23, etaPlus i2 i3 h23]

private theorem omegaPlusIota_injective (F : Type) [Field F] (n : ℕ)
    (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3) :
    ∀ i, Function.Injective (omegaPlusIota F n i0 i1 i2 i3 h01 h23 i) := by
  intro i
  fin_cases i
  · exact etaMinus_injective h01
  · exact etaPlus_injective h01
  · exact etaMinus_injective h23
  · exact etaPlus_injective h23

private theorem omegaPlusIota_cross_commute (F : Type) [Field F] (n : ℕ)
    (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3)
    (hdisj : Disjoint ({i0, i1} : Set (Fin n)) ({i2, i3} : Set (Fin n))) :
    (∀ A B : SpecialLinearGroup (Fin 2) F,
        Commute (etaMinus i0 i1 h01 A) (etaMinus i2 i3 h23 B)) ∧
      (∀ A B : SpecialLinearGroup (Fin 2) F,
        Commute (etaMinus i0 i1 h01 A) (etaPlus i2 i3 h23 B)) ∧
      (∀ A B : SpecialLinearGroup (Fin 2) F,
        Commute (etaPlus i0 i1 h01 A) (etaMinus i2 i3 h23 B)) ∧
      (∀ A B : SpecialLinearGroup (Fin 2) F,
        Commute (etaPlus i0 i1 h01 A) (etaPlus i2 i3 h23 B)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    exact commute_eta_of_disjoint_coordIdx (a := Sum.inl i0) (b := Sum.inl i1)
      (c := Sum.inl i2) (d := Sum.inl i3) (coordIdx_inl_ne h01) (coordIdx_inl_ne h23)
      (by simpa using hdisj) A B
  · intro A B
    have h := commute_eta_of_disjoint_coordIdx (a := Sum.inl i0) (b := Sum.inl i1)
      (c := Sum.inl i2) (d := Sum.inr i3) (coordIdx_inl_ne h01) (coordIdx_inl_inr_ne h23)
      (by simpa using hdisj) A B
    change Commute (etaMinus i0 i1 h01 A) (etaPlus i2 i3 h23 B)
    rw [etaPlus_eq]
    change Commute (eta (coordIdx_inl_ne h01) A) (eta (coordIdx_inl_inr_ne h23) B)
    exact h
  · intro A B
    have h := commute_eta_of_disjoint_coordIdx (a := Sum.inl i0) (b := Sum.inr i1)
      (c := Sum.inl i2) (d := Sum.inl i3) (coordIdx_inl_inr_ne h01) (coordIdx_inl_ne h23)
      (by simpa using hdisj) A B
    change Commute (etaPlus i0 i1 h01 A) (etaMinus i2 i3 h23 B)
    rw [etaPlus_eq]
    change Commute (eta (coordIdx_inl_inr_ne h01) A) (eta (coordIdx_inl_ne h23) B)
    exact h
  · intro A B
    have h := commute_eta_of_disjoint_coordIdx (a := Sum.inl i0) (b := Sum.inr i1)
      (c := Sum.inl i2) (d := Sum.inr i3) (coordIdx_inl_inr_ne h01) (coordIdx_inl_inr_ne h23)
      (by simpa using hdisj) A B
    change Commute (etaPlus i0 i1 h01 A) (etaPlus i2 i3 h23 B)
    rw [etaPlus_eq, etaPlus_eq]
    change Commute (eta (coordIdx_inl_inr_ne h01) A) (eta (coordIdx_inl_inr_ne h23) B)
    exact h

private theorem omegaPlusIota_commute (F : Type) [Field F] (n : ℕ)
    (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3)
    (hdisj : Disjoint ({i0, i1} : Set (Fin n)) ({i2, i3} : Set (Fin n))) :
    ∀ i j : Fin 4, i ≠ j → ∀ A B : SpecialLinearGroup (Fin 2) F,
      omegaPlusIota F n i0 i1 i2 i3 h01 h23 i A *
          omegaPlusIota F n i0 i1 i2 i3 h01 h23 j B =
        omegaPlusIota F n i0 i1 i2 i3 h01 h23 j B *
          omegaPlusIota F n i0 i1 i2 i3 h01 h23 i A := by
  obtain ⟨hcross_e01_e23, hcross_e01_s23, hcross_s01_e23, hcross_s01_s23⟩ :=
    omegaPlusIota_cross_commute F n i0 i1 i2 i3 h01 h23 hdisj
  intro i j hij A B
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change etaMinus i0 i1 h01 A * etaPlus i0 i1 h01 B =
      etaPlus i0 i1 h01 B * etaMinus i0 i1 h01 A
    exact (commute_etaMinus_etaPlus h01 A B).eq
  · change etaMinus i0 i1 h01 A * etaMinus i2 i3 h23 B =
      etaMinus i2 i3 h23 B * etaMinus i0 i1 h01 A
    exact (hcross_e01_e23 A B).eq
  · change etaMinus i0 i1 h01 A * etaPlus i2 i3 h23 B =
      etaPlus i2 i3 h23 B * etaMinus i0 i1 h01 A
    exact (hcross_e01_s23 A B).eq
  · change etaPlus i0 i1 h01 A * etaMinus i0 i1 h01 B =
      etaMinus i0 i1 h01 B * etaPlus i0 i1 h01 A
    exact (commute_etaMinus_etaPlus h01 B A).eq.symm
  · exact absurd rfl hij
  · change etaPlus i0 i1 h01 A * etaMinus i2 i3 h23 B =
      etaMinus i2 i3 h23 B * etaPlus i0 i1 h01 A
    exact (hcross_s01_e23 A B).eq
  · change etaPlus i0 i1 h01 A * etaPlus i2 i3 h23 B =
      etaPlus i2 i3 h23 B * etaPlus i0 i1 h01 A
    exact (hcross_s01_s23 A B).eq
  · change etaMinus i2 i3 h23 A * etaMinus i0 i1 h01 B =
      etaMinus i0 i1 h01 B * etaMinus i2 i3 h23 A
    exact (hcross_e01_e23 B A).eq.symm
  · change etaMinus i2 i3 h23 A * etaPlus i0 i1 h01 B =
      etaPlus i0 i1 h01 B * etaMinus i2 i3 h23 A
    exact (hcross_s01_e23 B A).eq.symm
  · exact absurd rfl hij
  · change etaMinus i2 i3 h23 A * etaPlus i2 i3 h23 B =
      etaPlus i2 i3 h23 B * etaMinus i2 i3 h23 A
    exact (commute_etaMinus_etaPlus h23 A B).eq
  · change etaPlus i2 i3 h23 A * etaMinus i0 i1 h01 B =
      etaMinus i0 i1 h01 B * etaPlus i2 i3 h23 A
    exact (hcross_e01_s23 B A).eq.symm
  · change etaPlus i2 i3 h23 A * etaPlus i0 i1 h01 B =
      etaPlus i0 i1 h01 B * etaPlus i2 i3 h23 A
    exact (hcross_s01_s23 B A).eq.symm
  · change etaPlus i2 i3 h23 A * etaMinus i2 i3 h23 B =
      etaMinus i2 i3 h23 B * etaPlus i2 i3 h23 A
    exact (commute_etaMinus_etaPlus h23 B A).eq.symm
  · exact absurd rfl hij

private theorem omegaPlusIota_sl2Diag_mem_flagStab (F : Type) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 4 ≤ n) (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3)
    (ζ : Fˣ) (i : Fin 4) :
    omegaPlusIota F n i0 i1 i2 i3 h01 h23 i (sl2Diag ζ) ∈
      (flagStab n F).subgroupOf (orthElementaryGroup (quadPlus n F)) := by
  have hmem : ∀ d : Fin n → Fˣ, torusElt n F d ∈ flagStab n F := by
    intro d
    refine mem_flagStab.2 ⟨torusElt_mem_orthElementaryGroup (r := n) (K := F) (by omega) d,
      fun i _ _ => (mem_posBorel.1 (torusElt_mem_posBorel d)).2 i⟩
  fin_cases i
  · rw [Subgroup.mem_subgroupOf]
    change ((etaMinus i0 i1 h01 (sl2Diag ζ) :
      orthElementaryGroup (quadPlus n F)) :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) ∈ flagStab n F
    rw [coe_etaMinus_sl2Diag]
    exact hmem _
  · rw [Subgroup.mem_subgroupOf]
    change ((etaPlus i0 i1 h01 (sl2Diag ζ) :
      orthElementaryGroup (quadPlus n F)) :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) ∈ flagStab n F
    rw [coe_etaPlus_sl2Diag]
    exact hmem _
  · rw [Subgroup.mem_subgroupOf]
    change ((etaMinus i2 i3 h23 (sl2Diag ζ) :
      orthElementaryGroup (quadPlus n F)) :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) ∈ flagStab n F
    rw [coe_etaMinus_sl2Diag]
    exact hmem _
  · rw [Subgroup.mem_subgroupOf]
    change ((etaPlus i2 i3 h23 (sl2Diag ζ) :
      orthElementaryGroup (quadPlus n F)) :
      (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) ∈ flagStab n F
    rw [coe_etaPlus_sl2Diag]
    exact hmem _

private theorem omegaPlusIota_closure_le_normalizer (F : Type) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 4 ≤ n) (i0 i1 i2 i3 : Fin n) (h01 : i0 ≠ i1) (h23 : i2 ≠ i3)
    (ζ : Fˣ) (S₀ : Sylow 2 ↥(orthElementaryGroup (quadPlus n F)))
    (hS₀ : (S₀ : Subgroup ↥(orthElementaryGroup (quadPlus n F))) =
      (posUnip n F).subgroupOf (orthElementaryGroup (quadPlus n F)))
    (hNorm : Subgroup.normalizer ((posUnip n F).subgroupOf
        (orthElementaryGroup (quadPlus n F)) :
        Set ↥(orthElementaryGroup (quadPlus n F))) =
      (flagStab n F).subgroupOf (orthElementaryGroup (quadPlus n F))) :
    Subgroup.closure (Set.range fun i : Fin 4 =>
        omegaPlusIota F n i0 i1 i2 i3 h01 h23 i (sl2Diag ζ)) ≤
      Subgroup.normalizer ((S₀ : Subgroup ↥(orthElementaryGroup (quadPlus n F))) :
        Set ↥(orthElementaryGroup (quadPlus n F))) := by
  rw [show (S₀ : Subgroup ↥(orthElementaryGroup (quadPlus n F))) =
      (posUnip n F).subgroupOf (orthElementaryGroup (quadPlus n F)) from hS₀, hNorm]
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact omegaPlusIota_sl2Diag_mem_flagStab F n hn i0 i1 i2 i3 h01 h23 ζ i

private theorem exists_four_coordinates (n : ℕ) (hn : 4 ≤ n) :
    ∃ (i0 i1 i2 i3 : Fin n), i0 ≠ i1 ∧ i2 ≠ i3 ∧
      Disjoint ({i0, i1} : Set (Fin n)) ({i2, i3} : Set (Fin n)) := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  refine ⟨i0, i1, i2, i3, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  · intro h
    have := congrArg Fin.val h
    simp [i2, i3] at this
  · rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have hx' : (x : ℕ) = 0 ∨ (x : ℕ) = 1 := by
      rcases hx with h | h
      · left; simpa [i0] using congrArg Fin.val h
      · right; simpa [i1] using congrArg Fin.val h
    have hy' : (x : ℕ) = 2 ∨ (x : ℕ) = 3 := by
      rcases hy with h | h
      · left; simpa [i2] using congrArg Fin.val h
      · right; simpa [i3] using congrArg Fin.val h
    omega

private theorem omegaPlus_witness {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn4 : 4 ≤ n) {K : Type} [Group K] [Finite K]
    (e : K ⧸ Subgroup.center K ≃* ↥(orthElementaryGroup (quadPlus n F)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ζ : Fˣ} (hζo : orderOf ζ = r)
    (S : Subgroup K) (hS : IsSylowTwoOf S ⊤) :
    3 < CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  classical
  let T := ↥(orthElementaryGroup (quadPlus n F))
  haveI : Finite ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)) :=
    Finite.of_injective (fun g : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) =>
      (g : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F))) fun _ _ h =>
      LinearEquiv.ext fun x => congrFun h x
  haveI : Finite T := by dsimp [T]; infer_instance
  let φ : K →* T := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker_eq : φ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkerle : φ.ker ≤ Subgroup.center K := le_of_eq hker_eq
  have hζ : ζ ^ r = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨i0, i1, i2, i3, h01, h23, hdisj⟩ := exists_four_coordinates n hn4
  have hord : orderOf (sl2Diag ζ) = r := by
    rw [CFSG.LinearAlgebra.orderOf_sl2Diag, hζo]
  have hinv : (sl2W : SpecialLinearGroup (Fin 2) F) * sl2Diag ζ * sl2W⁻¹ =
      (sl2Diag ζ)⁻¹ := by
    rw [← map_inv]
    exact sl2W_conj_sl2Diag ζ
  let ι : Fin 4 → SpecialLinearGroup (Fin 2) F →* T :=
    omegaPlusIota F n i0 i1 i2 i3 h01 h23
  let D : Subgroup T := Subgroup.closure (Set.range fun i : Fin 4 => ι i (sl2Diag ζ))
  obtain ⟨hDabelian, hDcard, hDcomm⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_inversion_package (φ := φ) hφ hkerle
      ι (omegaPlusIota_injective F n i0 i1 i2 i3 h01 h23)
      (omegaPlusIota_commute F n i0 i1 i2 i3 h01 h23 hdisj) hr hr2 hord hinv
  obtain ⟨⟨S₀, hS₀⟩, hNorm, -⟩ :=
    orthogonal_geometry_split_Sylow_flag_normalizer (K := F) (r := n) 2 (by omega)
  let U : Subgroup T := (S₀ : Subgroup T)
  have hU : IsSylowTwoOf U ⊤ := isSylowTwoOf_top_of_sylow S₀
  have hDU : D ≤ Subgroup.normalizer (U : Set T) :=
    omegaPlusIota_closure_le_normalizer F n hn4 i0 i1 i2 i3 h01 h23 ζ S₀ hS₀ hNorm
  have hbound := le_pRank_normalizerQuotient_of_comap_comm (φ := φ) hφ hkerle hr hr2
    hDabelian.2 hDcomm (k := 4) (by rw [hDcard]) hU hDU S hS
  omega

theorem k_CartanRankLarge_pomegaPlus :
    ∀ (K : Type) [Group K] [Finite K] (n f : ℕ),
      CFSG.Open.StatedLieAdmissible .POmegaPlus n 2 f → 2 < 2 ^ f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus n 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .POmegaPlus n →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  intro K _ _ n f _ h2f hL _ _ S hS hrank
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at h2f
  obtain ⟨F, hFld, hFin, hChar, hFcard, hn4, ⟨e⟩⟩ :=
    exists_mulEquiv_elementaryGroup_of_lieModel hL
  letI := hFld
  letI := hFin
  letI := hChar
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  have hrdvd' : r ∣ Nat.card F - 1 := by rw [hFcard]; exact hrdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rwa [Nat.card_units])
  exact ⟨r, hr, hr2, hrdvd, omegaPlus_witness n hn4 e hr hr2 hζo S hS⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
