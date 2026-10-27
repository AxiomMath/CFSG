module

public import CFSG.Quasithin.Background.Sp4InfAbs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin

namespace B69

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open Module Subgroup

variable {K : Type} [Field K]

@[expose] def TypePresSp (φ : MulAut (StatedProj (StatedSp 2 K))) : Prop :=
  ∀ W : Submodule K (Fin 2 ⊕ Fin 2 → K), finrank K W = 1 →
    ∃ W' : Submodule K (Fin 2 ⊕ Fin 2 → K), finrank K W' = 1 ∧
      (projStabilizer 2 K W).map (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) =
        projStabilizer 2 K W'

theorem exists_eq_span_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module K V]
    {W : Submodule K V} (hW : finrank K W = 1) : ∃ w : V, w ≠ 0 ∧ W = Submodule.span K {w} := by
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp hW
  have hv : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  exact ⟨(v : V), hv, eq_span_singleton_of_mem_of_finrank_eq_one hW v.2 hv⟩

theorem isTotallyIsotropic_of_finrank_eq_one {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hW : finrank K W = 1) : IsTotallyIsotropic (pairedSympForm K 2) W := by
  obtain ⟨w, -, rfl⟩ := exists_eq_span_of_finrank_eq_one hW
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp only [map_smul, LinearMap.smul_apply, pairedSympForm_self, smul_zero]

theorem typePresSp_conjAut_mul_fieldAut (A : gsp 2 K) (σ : K ≃+* K) :
    TypePresSp (conjAut 2 K A * fieldAut 2 K σ) := by
  intro W hW
  obtain ⟨w, hw0, rfl⟩ := exists_eq_span_of_finrank_eq_one hW
  refine ⟨(spCoordImage σ (Submodule.span K {w})).map (Matrix.mulVecLin ((A : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)), ?_,
    map_projStabilizer_conjAut_mul_fieldAut A σ _⟩
  rw [spCoordImage_span_singleton, Submodule.map_span, Set.image_singleton]
  apply finrank_span_singleton
  intro h
  have hinj : Function.Injective (Matrix.mulVecLin ((A : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :=
    Matrix.mulVec_injective_iff_isUnit.2 A.1.isUnit
  have h0 : (fun i => σ (w i)) = 0 := hinj (by rw [h, map_zero])
  apply hw0
  funext i
  have := congrFun h0 i
  simpa using this

section Geometry

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem isCoatom_le_eq_projStabilizer {F : ℕ → Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hF : IsCompleteIsotropicFlag (pairedSympForm K 2) 2 F)
    {M : Subgroup (StatedProj (StatedSp 2 K))} (hM : IsCoatom M)
    (hle : projIsoFlagStabilizer 2 K F ≤ M) :
    M = projStabilizer 2 K (F 1) ∨ M = projStabilizer 2 K (F 2) := by
  obtain ⟨g, hg⟩ := exists_map_flag_eq hF
  have hB₀ := projIsoFlagStabilizer_eq_map_conj hg
  set e := MulEquiv.mapSubgroup (MulAut.conj (proj 2 K g)) with he
  have hM' : IsCoatom (e.symm M) := by
    rw [← OrderIso.isCoatom_iff e, OrderIso.apply_symm_apply]
    exact hM
  have hBM' : projBorel 2 K ≤ e.symm M := by
    rw [← e.le_iff_le, OrderIso.apply_symm_apply]
    rw [hB₀] at hle
    exact hle
  obtain ⟨d, hd, hdr, hMd⟩ := eq_projStabilizer_of_isCoatom hM' hBM'
  have hMe : M = projStabilizer 2 K ((flag 2 K d).map (spAct g)) := by
    rw [projStabilizer_map_spAct, ← hMd]
    change M = e (e.symm M)
    rw [OrderIso.apply_symm_apply]
  rw [hg d hd hdr] at hMe
  interval_cases d
  · exact Or.inl hMe
  · exact Or.inr hMe

theorem exists_two_parabolics_sp (S₀ : Sylow 2 (StatedProj (StatedSp 2 K))) :
    ∃ Q₁ Q₂ : Subgroup (StatedProj (StatedSp 2 K)), IsCoatom Q₁ ∧ IsCoatom Q₂ ∧ Q₁ ≠ Q₂ ∧
      (S₀ : Subgroup (StatedProj (StatedSp 2 K))) ≤ Q₁ ∧
      (S₀ : Subgroup (StatedProj (StatedSp 2 K))) ≤ Q₂ ∧
      ∀ φ : MulAut (StatedProj (StatedSp 2 K)),
        (S₀ : Subgroup (StatedProj (StatedSp 2 K))).map
            (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) = S₀ →
        TypePresSp φ →
          Q₁.map (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) = Q₁ ∧
            Q₂.map (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) = Q₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcoatom, hinj⟩ := maximal_parabolics (r := 2) (K := K) 2 (by norm_num)
  have hB₀mem : normalizer ((S₀ : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) ∈
        LinearFlag.sylowNormalizers (StatedProj (StatedSp 2 K)) 2 := ⟨S₀, rfl⟩
  rw [(sylow_normalizers (r := 2) (K := K) 2 (by norm_num)).2.2.1] at hB₀mem
  obtain ⟨F, hF, hB₀⟩ := hB₀mem
  set B₀ := normalizer ((S₀ : Subgroup (StatedProj (StatedSp 2 K))) :
      Set (StatedProj (StatedSp 2 K))) with hB₀def
  have hF1 : finrank K (F 1) = 1 := hF.1 1 (by norm_num)
  have hF2 : finrank K (F 2) = 2 := hF.1 2 (by norm_num)
  have hF1ne : F 1 ≠ ⊥ := fun h => by rw [h, finrank_bot] at hF1; omega
  have hF2ne : F 2 ≠ ⊥ := fun h => by rw [h, finrank_bot] at hF2; omega
  have hQ₁ : IsCoatom (projStabilizer 2 K (F 1)) := hcoatom _ hF1ne (hF.2.2 1 (by norm_num))
  have hQ₂ : IsCoatom (projStabilizer 2 K (F 2)) := hcoatom _ hF2ne (hF.2.2 2 (by norm_num))
  have hBQ : ∀ i, 1 ≤ i → i ≤ 2 → B₀ ≤ projStabilizer 2 K (F i) := by
    intro i hi1 hi2
    rw [hB₀, projIsoFlagStabilizer, projStabilizer]
    refine map_mono fun x hx => ?_
    exact (mem_isoFlagStabilizer.mp hx) i hi1 hi2
  have hQ12 : projStabilizer 2 K (F 1) ≠ projStabilizer 2 K (F 2) := by
    intro h
    have := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => finrank K W)
      (hinj _ _ hF1ne (hF.2.2 1 (by norm_num)) hF2ne (hF.2.2 2 (by norm_num)) h)
    omega
  have hS₀B : (S₀ : Subgroup (StatedProj (StatedSp 2 K))) ≤ B₀ := Subgroup.le_normalizer
  refine ⟨projStabilizer 2 K (F 1), projStabilizer 2 K (F 2), hQ₁, hQ₂, hQ12,
    hS₀B.trans (hBQ 1 le_rfl (by norm_num)), hS₀B.trans (hBQ 2 (by norm_num) le_rfl),
    fun φ hφS hφ => ?_⟩
  have hφB : B₀.map (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) = B₀ := by
    rw [hB₀def]
    have h1 : ((normalizer ((S₀ : Subgroup (StatedProj (StatedSp 2 K))) :
        Set (StatedProj (StatedSp 2 K)))).map φ.toMonoidHom) =
        normalizer (((S₀ : Subgroup (StatedProj (StatedSp 2 K))).map φ.toMonoidHom :
          Subgroup (StatedProj (StatedSp 2 K))) : Set (StatedProj (StatedSp 2 K))) :=
      Subgroup.map_equiv_normalizer_eq _ φ
    have h2 : (S₀ : Subgroup (StatedProj (StatedSp 2 K))).map φ.toMonoidHom = S₀ := hφS
    rw [h2] at h1
    exact h1
  have hcoatom_map : ∀ Q : Subgroup (StatedProj (StatedSp 2 K)), IsCoatom Q →
      IsCoatom (Q.map (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K))) := fun Q hQ =>
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ) Q).mpr hQ
  have hle_map : ∀ i, 1 ≤ i → i ≤ 2 →
      B₀ ≤ (projStabilizer 2 K (F i)).map
        (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) := fun i hi1 hi2 => by
    rw [← hφB]
    exact map_mono (hBQ i hi1 hi2)
  have hQ₁φ : (projStabilizer 2 K (F 1)).map
      (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) = projStabilizer 2 K (F 1) := by
    obtain ⟨W', hW'1, hW'⟩ := hφ (F 1) hF1
    rcases isCoatom_le_eq_projStabilizer hF (hcoatom_map _ hQ₁) (by rw [← hB₀]; exact hle_map 1 le_rfl (by norm_num)) with h | h
    · exact h
    · exfalso
      have hW'ne : W' ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW'1; omega
      have := congrArg (fun W : Submodule K (Fin 2 ⊕ Fin 2 → K) => finrank K W)
        (hinj _ _ hW'ne (isTotallyIsotropic_of_finrank_eq_one hW'1) hF2ne (hF.2.2 2 (by norm_num))
          (hW'.symm.trans h))
      omega
  refine ⟨hQ₁φ, ?_⟩
  rcases isCoatom_le_eq_projStabilizer hF (hcoatom_map _ hQ₂) (by rw [← hB₀]; exact hle_map 2 (by norm_num) le_rfl) with h | h
  · exfalso
    apply hQ12
    have h' : (projStabilizer 2 K (F 2)).map
        (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) =
        (projStabilizer 2 K (F 1)).map
          (φ : StatedProj (StatedSp 2 K) →* StatedProj (StatedSp 2 K)) := h.trans hQ₁φ.symm
    exact (Subgroup.map_injective φ.injective h').symm
  · exact h

theorem swapGeo_sp4 : SwapGeo (StatedProj (StatedSp 2 K)) TypePresSp := by
  refine swapGeo_of_two_parabolics fun S₀ => ?_
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hQ12, hS₁, hS₂, hfix⟩ := exists_two_parabolics_sp S₀
  refine ⟨Q₁, Q₂, hQ₁.1, hQ₂.1, ?_, hS₁, hS₂, hfix⟩
  rcases hQ₁.le_iff.1 (le_sup_left : Q₁ ≤ Q₁ ⊔ Q₂) with h | h
  · exact h
  · exfalso
    have hle : Q₂ ≤ Q₁ := h ▸ le_sup_right
    rcases hQ₂.le_iff.1 hle with h' | h'
    · exact hQ₁.1 h'
    · exact hQ12 h'

omit [Finite K] in
theorem even_natCard_statedProj_sp : Even (Nat.card (StatedProj (StatedSp 2 K))) := by
  classical
  set g : StatedSp 2 K := SymplecticFour.tau (SymplecticFour.sym2_transpose (1 : K) 0 0) with hgdef
  have hg2 : g ^ 2 = 1 := SymplecticFour.tau_sq _
  have hg1 : proj 2 K g ≠ 1 := by
    intro h
    have hker : g ∈ (proj 2 K).ker := h
    rw [ker_proj, spScalars, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hker
    obtain ⟨c, hc⟩ := hker
    have h1 := congrArg (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inr 0)) hc
    simp [hgdef, SymplecticFour.coe_tau, SymplecticFour.sym2] at h1
  have hord : orderOf (proj 2 K g) = 2 := by
    refine orderOf_eq_prime ?_ hg1
    rw [← map_pow, hg2, map_one]
  have hdvd := orderOf_dvd_natCard (proj 2 K g)
  rw [hord] at hdvd
  exact even_iff_two_dvd.2 hdvd

end Geometry

end B69

end CFSG.Quasithin
