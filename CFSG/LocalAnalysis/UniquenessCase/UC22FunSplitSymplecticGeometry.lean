module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step23
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

open CFSG.ComponentClassification.AS81.Sec2

theorem eq_stdPlane_of_orthogonal_to_other_planes
    {F : Type} [Field F] {n : ℕ} (k : Fin n)
    {U : Submodule F (Fin n ⊕ Fin n → F)} (hU : IsHyperbolicPlane U)
    (horth : ∀ j : Fin n, j ≠ k → ∀ u ∈ U, ∀ v ∈ stdPlane F n j, form u v = 0) :
    U = stdPlane F n k := by
  have hle : U ≤ stdPlane F n k := by
    intro u hu
    rw [mem_stdPlane_iff]
    intro a ha
    rcases a with j | j
    · have hj : j ≠ k := fun h => ha (h ▸ inl_mem_coords k)
      have h := horth j hj u hu (Pi.single (Sum.inr j) 1)
        (Submodule.subset_span (by simp))
      simpa [form_single_right] using h
    · have hj : j ≠ k := fun h => ha (h ▸ inr_mem_coords k)
      have h := horth j hj u hu (Pi.single (Sum.inl j) 1)
        (Submodule.subset_span (by simp))
      simpa [form_single_right] using h
  apply Submodule.eq_of_le_of_finrank_eq hle
  exact (isHyperbolicPlane_iff.mp hU).1.trans
    (isHyperbolicPlane_iff.mp (isHyperbolicPlane_stdPlane k)).1.symm

theorem planeGroup_eq_longRootSp2_of_commutes_other_planes
    {F : Type} [Field F] {n : ℕ} (h2 : (2 : F) ≠ 0) (k : Fin n)
    {U : Submodule F (Fin n ⊕ Fin n → F)} (hU : IsHyperbolicPlane U)
    (hcomm : ∀ j : Fin n, j ≠ k →
      Commutes (planeGroup U) (longRootSp2 F n j)) :
    planeGroup U = longRootSp2 F n k := by
  have horth : ∀ j : Fin n, j ≠ k → ∀ u ∈ U, ∀ v ∈ stdPlane F n j, form u v = 0 := by
    intro j hj
    have hne : planeGroup U ≠ planeGroup (stdPlane F n j) := by
      intro heq
      have hc := hcomm j hj
      rw [planeGroup_stdPlane] at heq
      rw [heq] at hc
      have e : longRootSp2 F n j ≃* SL(2, F) :=
        (MonoidHom.ofInjective (longBlock_injective j)).symm
      obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
        (MonoidHom.id (StatedSp n F)) (by simp) e
      exact hab (hc a ha b hb)
    apply forall_form_eq_zero_of_commute_planeGroup h2 hU
      (isHyperbolicPlane_stdPlane j) hne
    rw [planeGroup_stdPlane]
    exact hcomm j hj
  rw [eq_stdPlane_of_orthogonal_to_other_planes k hU horth, planeGroup_stdPlane]

theorem exists_conj_map_longRootSp2_permutation
    {F X : Type} [Field F] [Group X] {n : ℕ}
    (ψ : StatedSp n F →* X) (σ : Equiv.Perm (Fin n)) :
    ∃ x : X, ∀ k : Fin n,
      ((longRootSp2 F n k).map ψ).map (MulAut.conj x).toMonoidHom =
        (longRootSp2 F n (σ k)).map ψ := by
  refine ⟨ψ (CFSG.SeitzReduction.SymplecticPilot.permSp F σ), fun k => ?_⟩
  rw [Subgroup.map_map]
  have hhom : (MulAut.conj (ψ (CFSG.SeitzReduction.SymplecticPilot.permSp F σ))).toMonoidHom.comp ψ =
      ψ.comp (MulAut.conj (CFSG.SeitzReduction.SymplecticPilot.permSp F σ)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply]
  rw [hhom, ← Subgroup.map_map,
    CFSG.SeitzReduction.SymplecticPilot.map_conj_permSp_longRootSp2]

theorem surjective_conjPermHom_of_indexed_conjugations
    {X ι : Type} [Group X] {Δ : Set (Subgroup X)}
    (e : ι ≃ Δ)
    (hperm : ∀ σ : Equiv.Perm ι, ∃ x : X, ∀ i : ι,
      (e i : Subgroup X).map (MulAut.conj x).toMonoidHom = (e (σ i) : Subgroup X)) :
    Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) := by
  intro τ
  let σ : Equiv.Perm ι := e.trans (τ.trans e.symm)
  obtain ⟨x, hx⟩ := hperm σ
  have hxStab : x ∈ conjSetStab Δ := by
    apply (inv_mem_iff (H := conjSetStab Δ)).mp
    rw [mem_conjSetStab]
    intro L
    constructor
    · intro hL
      obtain ⟨i, hi⟩ := e.surjective ⟨L, hL⟩
      have hi' : (e i : Subgroup X) = L := congrArg Subtype.val hi
      have hx' := hx i
      have hm : L.map (MulAut.conj x).toMonoidHom ∈ Δ := by
        rw [← hi', hx']
        exact (e (σ i)).2
      simpa [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate] using hm
    · intro hL
      obtain ⟨j, hj⟩ := e.surjective
        ⟨CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate L x⁻¹, hL⟩
      have hj' : (e j : Subgroup X) =
          L.map (MulAut.conj x).toMonoidHom := by
        simpa [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate] using
          congrArg Subtype.val hj
      have hmap : (e (σ.symm j) : Subgroup X).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj x).toMonoidHom := by
        rw [hx, σ.apply_symm_apply, hj']
      have heq : (e (σ.symm j) : Subgroup X) = L :=
        Subgroup.map_injective (MulAut.conj x).injective hmap
      exact heq ▸ (e (σ.symm j)).2
  refine ⟨⟨x, hxStab⟩, Equiv.ext fun L => Subtype.ext ?_⟩
  obtain ⟨i, rfl⟩ := e.surjective L
  rw [conjPermHom_apply]
  simp only [CFSG.ComponentClassification.AschbacherTightEmbedding.rightConjugate,
    inv_inv]
  change (e i : Subgroup X).map (MulAut.conj x).toMonoidHom = (τ (e i) : Subgroup X)
  rw [hx]
  simp [σ]

theorem nonempty_equiv_perm_of_coordinate_symplectic_frame
    {F X : Type} [Field F] [Group X] {n : ℕ}
    (ψ : StatedSp n F →* X) (hker : ψ.ker ≤ center (StatedSp n F)) :
    let Δ := Set.range (fun k : Fin n => (longRootSp2 F n k).map ψ)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin n)) := by
  classical
  intro Δ
  let f : Fin n → Δ := fun k => ⟨(longRootSp2 F n k).map ψ, ⟨k, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k l hkl
      by_contra hne
      have hneMap := F14.map_ne_of_commuting_of_equiv_sl2 ψ hker
        ((MonoidHom.ofInjective (longBlock_injective k)).symm)
        (fun a ha b hb => (commute_longRootSp2 hne ha hb).eq)
      exact hneMap (congrArg Subtype.val hkl)
    · rintro ⟨L, k, rfl⟩
      exact ⟨k, rfl⟩
  let e : Fin n ≃ Δ := Equiv.ofBijective f hf
  have hρ : Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) :=
    surjective_conjPermHom_of_indexed_conjugations e fun σ => by
      obtain ⟨x, hx⟩ := exists_conj_map_longRootSp2_permutation ψ σ
      exact ⟨x, hx⟩
  have htop := MonoidHom.range_eq_top.mpr hρ
  exact ⟨(MulEquiv.subgroupCongr htop).trans
    (Subgroup.topEquiv.trans e.symm.permCongrHom)⟩


theorem map_symplectic_fundamental_eq_of_commutes_other_coordinates
    {X : Type} [Group X] {p n f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f)
    (ψ : StatedSp n (GaloisField p f) →* X)
    (hker : ψ.ker ≤ center (StatedSp n (GaloisField p f)))
    {R : Subgroup (StatedSp n (GaloisField p f))}
    (hR : R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p f Fact.out).D)
    (k : Fin n)
    (hcomm : ∀ j : Fin n, j ≠ k →
      Commutes (R.map ψ) ((longRootSp2 (GaloisField p f) n j).map ψ)) :
    R.map ψ = (longRootSp2 (GaloisField p f) n k).map ψ := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  obtain ⟨U, hU, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
  have hc : ∀ j : Fin n, j ≠ k →
      Commutes (planeGroup U) (longRootSp2 (GaloisField p f) n j) := fun j hj =>
    commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψ hker hR (hcomm j hj)
  rw [planeGroup_eq_longRootSp2_of_commutes_other_planes h2 k hU hc]

theorem centralizingLayer_eq_coordinate_symplectic_member
    {X : Type} [Group X] [Finite X] {p n f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f)
    (ψ : StatedSp n (GaloisField p f) →* X)
    (hker : ψ.ker ≤ center (StatedSp n (GaloisField p f)))
    {Ω : Set (Subgroup X)}
    (hreal : ∀ L ∈ Ω, ∃ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p f Fact.out).D,
      L = R.map ψ)
    (hΩ : ∀ k : Fin n, (longRootSp2 (GaloisField p f) n k).map ψ ∈ Ω)
    (k : Fin n) :
    centralizingLayer Ω {x : X | ∃ j : Fin n, j ≠ k ∧
      x ∈ (longRootSp2 (GaloisField p f) n j).map ψ} =
        (longRootSp2 (GaloisField p f) n k).map ψ := by
  let Γ := {x : X | ∃ j : Fin n, j ≠ k ∧
    x ∈ (longRootSp2 (GaloisField p f) n j).map ψ}
  have hcentral : (longRootSp2 (GaloisField p f) n k).map ψ ≤ centralizer Γ := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨j, hj, hb⟩
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using (congrArg ψ (commute_longRootSp2 hj.symm ha₀ hb₀).eq).symm
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨R, hR, rfl⟩ := hreal L hL.1
    have hc : ∀ j : Fin n, j ≠ k →
        Commutes (R.map ψ) ((longRootSp2 (GaloisField p f) n j).map ψ) := by
      intro j hj a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b ⟨j, hj, hb⟩).symm
    rw [map_symplectic_fundamental_eq_of_commutes_other_coordinates hp2 hadm ψ hker hR k hc]
  · exact le_centralizingLayer ⟨hΩ k, hcentral⟩


theorem exists_full_coordinate_frame_funSet_psp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f) (hX : CFSG.Blueprint.LieModel X .PSp n p f)
    (ψ : StatedSp n (GaloisField p f) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (StatedSp n (GaloisField p f))) (P : Sylow 2 X) :
    ∃ c : X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        Set.range (fun k : Fin n =>
          ((longRootSp2 (GaloisField p f) n k).map ψ).map (MulAut.conj c).toMonoidHom) := by
  let F := GaloisField p f
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hmodel : ∀ k : Fin n, longRootSp2 F n k ∈
      fundamentalSubgroups .PSp (modelUniv .PSp n p f hp.out).D := fun k =>
    (CFSG.ClassicalInvolution.ModelFacts.fund_iff_isLongRootSp2 hadm h2 _).mpr
      ⟨longInv F n k, isLongRootSp2_standard k⟩
  let A : Fin n → Subgroup X := fun k => (longRootSp2 F n k).map ψ
  have hA : ∀ k, IsFundamentalOver (p ^ f) (A k) := fun k =>
    ⟨.PSp, n, p, f, hp.out, hp2, rfl, trivial, hadm, ψ, hψ, hker,
      longRootSp2 F n k, hmodel k, rfl⟩
  have hcomm : ∀ k j, k ≠ j → Commutes (A k) (A j) := by
    intro k j hkj a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using congrArg ψ (commute_longRootSp2 hkj ha₀ hb₀).eq
  have hnorm : ∀ k j, A j ≤ normalizer (A k : Set X) := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
      exact Subgroup.le_normalizer
    · have hc : A j ≤ centralizer (A k : Set X) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm k j hkj b hb a ha
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A hA hnorm P
  let ψc : StatedSp n F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (StatedSp n F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (longRootSp2 F n k).map ψc ∈
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    simpa [A, ψc, Subgroup.map_map] using hc k
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_two hadm.2.2.1
  let k0 : Fin n := ⟨0, hn⟩
  obtain ⟨hZ, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) (hc' k0).1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSp, n, f, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (longRootSp2 F n k).map ψc := by
      intro k heq
      apply hnot
      exact ⟨k, by simpa [A, ψc, Subgroup.map_map] using heq.symm⟩
    obtain ⟨R, hR, hLR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hL.1
    let R' : Subgroup (StatedSp n F) := R
    have hR' : R' ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p f hp.out).D := hR
    have hLR' : L = R'.map ψc := hLR
    have hcR : ∀ k, Commutes (R'.map ψc) ((longRootSp2 F n k).map ψc) := by
      intro k
      rw [← hLR']
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
    have heq := map_symplectic_fundamental_eq_of_commutes_other_coordinates
      hp2 hadm ψc hkerC hR' k0 (fun j _ => hcR j)
    exact hne k0 (hLR'.trans heq)
  · rintro ⟨k, rfl⟩
    exact hc k

theorem nonempty_equiv_perm_funSet_psp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f) (hX : CFSG.Blueprint.LieModel X .PSp n p f)
    (P : Sylow 2 X) :
    let Δ := F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin n)) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSp n p f hp.out hp2 (by trivial) hadm X hX
  let ψ : StatedSp n (GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center (StatedSp n (GaloisField p f)) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psp hp2 hadm hX ψ hψ hker P
  let ψc : StatedSp n (GaloisField p f) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center (StatedSp n (GaloisField p f)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin n => (longRootSp2 (GaloisField p f) n k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  rw [hfull']
  exact nonempty_equiv_perm_of_coordinate_symplectic_frame ψc hkerC

theorem centralizingLayer_funSet_eq_of_psp
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p n f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSp n p f) (hX : CFSG.Blueprint.LieModel X .PSp n p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSp n p f hp.out hp2 (by trivial) hadm X hX
  let ψ : StatedSp n (GaloisField p f) →* X := ψ0
  have hψ : Function.Surjective ψ := hψ0
  have hker : ψ.ker ≤ center (StatedSp n (GaloisField p f)) := hker0
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psp hp2 hadm hX ψ hψ hker P
  let F := GaloisField p f
  let ψc : StatedSp n F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (StatedSp n F) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin n => (longRootSp2 F n k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  have hKrange : K ∈ Set.range (fun k : Fin n => (longRootSp2 F n k).map ψc) := hfull' ▸ hK
  obtain ⟨k, rfl⟩ := hKrange
  have hinj : Function.Injective (fun j : Fin n => (longRootSp2 F n j).map ψc) := by
    intro i j heq
    by_contra hij
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
      ((MonoidHom.ofInjective (longBlock_injective i)).symm)
      (fun a ha b hb => (commute_longRootSp2 hij ha hb).eq) heq
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ (longRootSp2 F n k).map ψc ∧ x ∈ L} =
      {x : X | ∃ j : Fin n, j ≠ k ∧ x ∈ (longRootSp2 F n j).map ψc} := by
    ext x
    constructor
    · rintro ⟨L, hL, hne, hx⟩
      rw [hfull'] at hL
      obtain ⟨j, rfl⟩ := hL
      exact ⟨j, fun h => hne (h ▸ rfl), hx⟩
    · rintro ⟨j, hne, hx⟩
      exact ⟨(longRootSp2 F n j).map ψc, hfull'.symm ▸ ⟨j, rfl⟩,
        fun h => hne (hinj h), hx⟩
  obtain ⟨_, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) hK.1
  have hreal : ∀ L ∈ {L : Subgroup X | IsFundamentalOver (p ^ f) L},
      ∃ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n p f hp.out).D, L = R.map ψc := by
    intro L hL
    obtain ⟨R, hR, heq, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hL
    exact ⟨R, hR, heq⟩
  have hΩ : ∀ j : Fin n, (longRootSp2 F n j).map ψc ∈
      {L : Subgroup X | IsFundamentalOver (p ^ f) L} := fun j =>
    (show (longRootSp2 F n j).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) from
      hfull'.symm ▸ ⟨j, rfl⟩).1
  rw [hΓ]
  exact centralizingLayer_eq_coordinate_symplectic_member hp2 hadm ψc hkerC hreal hΩ k

end CFSG.LocalAnalysis.UniquenessCase.UC22
