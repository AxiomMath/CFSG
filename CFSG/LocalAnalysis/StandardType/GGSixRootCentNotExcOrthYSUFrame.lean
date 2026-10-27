module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace OrthYSU

open CFSG.ClassicalGroups.UnitaryFlag

theorem isSolvable_suBlock_of_card_le_three {m : ℕ}
    {Q : GL (Fin (m + 1)) (GaloisField 2 (2 * 1))}
    (hQ : UFusion.IsUFrame (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q)
    {I : Finset (Fin (m + 1))} (hI : I.card ≤ 3) :
    Group.IsSolvable
      ↥(UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I) := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 :=
    card_galoisField_two_mul 2 1 le_rfl
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1
      (GaloisField 2 (2 * 1)) := TableBU.unitaryFieldData_of_card hF le_rfl
  let f0 : ↥(UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I) →*
      ↥(unitarySU 2 1 (GaloisField 2 (2 * 1)) (m + 1)) :=
    (SURep.ggFrameEquiv hF Q hQ).toMonoidHom.comp
      (UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I).subtype
  have hmem : ∀ u : ↥(UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I),
      f0 u ∈ TableBUE.blockSU (n := 1) (K := GaloisField 2 (2 * 1)) I := by
    intro u
    rw [TableBUE.mem_blockSU]
    have hu : Q * (u.1 : GL (Fin (m + 1)) (GaloisField 2 (2 * 1))) * Q⁻¹ ∈
        UFusion.glBlock I := UFusion.mem_suBlock.mp u.2
    have hval : ((SURep.ggFrameEquiv hF Q hQ u.1 :
        ↥(unitarySU 2 1 (GaloisField 2 (2 * 1)) (m + 1))) :
        GL (Fin (m + 1)) (GaloisField 2 (2 * 1))) =
        Q * (u.1 : GL (Fin (m + 1)) (GaloisField 2 (2 * 1))) * Q⁻¹ := by
      have h1 := SURep.coe_ggFrameEquiv_symm hF Q hQ (SURep.ggFrameEquiv hF Q hQ u.1)
      rw [MulEquiv.symm_apply_apply] at h1
      rw [h1]
      group
    have hf0u : f0 u = SURep.ggFrameEquiv hF Q hQ u.1 := rfl
    rw [hf0u, hval]
    exact UFusion.mem_glBlock.mp hu
  let f : ↥(UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I) →*
      ↥(TableBUE.blockSU (n := 1) (K := GaloisField 2 (2 * 1)) I) :=
    f0.codRestrict _ hmem
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : (SURep.ggFrameEquiv hF Q hQ a.1) = SURep.ggFrameEquiv hF Q hQ b.1 := by
      simpa [f, f0] using congrArg Subtype.val hab
    exact Subtype.ext ((SURep.ggFrameEquiv hF Q hQ).injective h2)
  let g : ↥(UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I) →*
      ↥(unitarySU 2 1 (GaloisField 2 (2 * 1)) I.card) :=
    (TableBUE.blockSUEquiv I hU).symm.toMonoidHom.comp f
  have hg : Function.Injective g := fun a b hab =>
    hf ((TableBUE.blockSUEquiv I hU).symm.injective hab)
  haveI : Group.IsSolvable ↥(unitarySU 2 1 (GaloisField 2 (2 * 1)) I.card) := by
    rcases Nat.eq_zero_or_pos I.card with h0 | hpos
    · rw [h0]
      infer_instance
    · exact SmallU.isSolvable_unitarySU_small hU hpos hI
  exact Group.isSolvable_of_isSolvable_injective hg

end OrthYSU

section Inputs

theorem ggSUSix_exists_d_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G}
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 6 →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J
      (Unitary.rootDatum (card_galoisField_two_mul 2 1 le_rfl) 6) .PSU 6 1 ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hp : p = 3) :
    ∃ (d : G) (Q : GL (Fin 6) (GaloisField 2 (2 * 1)))
      (e : Fin 6 → (GaloisField 2 (2 * 1))ˣ) (j₁ j₂ : Fin 6),
      d ∈ D ∧ d ≠ 1 ∧ UFusion.IsUFrame (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q ∧
        (d, LinFusion.ggFrameDiag Q e) ∈ UFusion.suInducedPairs ψ ∧ j₁ ≠ j₂ ∧ e j₁ = e j₂ ∧
        ∀ i i', i ≠ j₁ → i ≠ j₂ → i' ≠ j₁ → i' ≠ j₂ → e i = e i' := by
  classical
  have hpdvd : p ∣ 2 ^ 1 + 1 := by rw [hp]; norm_num
  obtain ⟨Q, hQ, hBT⟩ :=
    ggUnitaryBstarFrameInput_holds G p B Bs x L D J 5 1 le_rfl ψ hctx s1 hpdvd
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact s1.1
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hctx.range_eq]
    exact hctx.j_isComponentOf_inf
  obtain ⟨I₀, hJI, hDI⟩ :=
    ggUnitarySemisimpleComponentInput_holds G 5 1 le_rfl ψ hctx.2.2.2.2.1.2 Q hQ D
      (fun g hg => hBT (hctx.d_le_bstar hg)) J hJ
  have hIcard4 : 4 ≤ I₀.card := by
    by_contra hlt
    have hI3 : I₀.card ≤ 3 := by omega
    have hsolSU : Group.IsSolvable ↥(UFusion.suBlock
        (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) Q I₀) :=
      OrthYSU.isSolvable_suBlock_of_card_le_three hQ hI3
    have hsolMap : Group.IsSolvable ↥(UFusion.uFrameBlock ψ Q I₀) := by
      have h1 : Group.IsSolvable
          ↥((ψ.comp (UFusion.suBlock (σ := unitaryInvolution (GaloisField 2 (2 * 1)) 2 1)
            Q I₀).subtype).range) :=
        solvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
      rw [MonoidHom.range_comp, Subgroup.range_subtype] at h1
      exact h1
    haveI : Group.IsSolvable ↥(UFusion.uFrameBlock ψ Q I₀) := hsolMap
    have hsolJ : Group.IsSolvable ↥J :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hJI)
    exact SmallU.not_isComponentOf_of_solvable hJ hsolJ
  have hcardD : Nat.card D = 9 := by
    rw [hctx.card_d, hp]
    norm_num
  have hcardF : Nat.card (GaloisField 2 (2 * 1))ˣ = 3 := by
    rw [Nat.card_units, card_galoisField_two_mul 2 1 le_rfl]
    norm_num
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < I₀.card)
  let eD : ↥D → Fin 6 → (GaloisField 2 (2 * 1))ˣ :=
    fun g => (hDI (g : G) g.2).choose
  have eD_spec : ∀ g : ↥D,
      ((g : G), LinFusion.ggFrameDiag Q (eD g)) ∈ UFusion.suInducedPairs ψ ∧
        ∀ i ∈ I₀, ∀ j ∈ I₀, eD g i = eD g j :=
    fun g => (hDI (g : G) g.2).choose_spec
  let Φ : ↥D → ({j : Fin 6 // j ∉ I₀} → (GaloisField 2 (2 * 1))ˣ) :=
    fun g j => eD g j.1 * (eD g i₀)⁻¹
  have hinj : Function.Injective Φ := by
    rintro ⟨g, hg⟩ ⟨h, hh⟩ hΦ
    have hgpair := (eD_spec ⟨g, hg⟩).1
    have hgconst := (eD_spec ⟨g, hg⟩).2
    have hhpair := (eD_spec ⟨h, hh⟩).1
    have hhconst := (eD_spec ⟨h, hh⟩).2
    obtain ⟨hAg, hag⟩ := UFusion.mem_suInducedPairs.mp hgpair
    obtain ⟨hAh, hah⟩ := UFusion.mem_suInducedPairs.mp hhpair
    set c : (GaloisField 2 (2 * 1))ˣ := eD ⟨g, hg⟩ i₀ * (eD ⟨h, hh⟩ i₀)⁻¹
    have heq : ∀ j : Fin 6, eD ⟨g, hg⟩ j = c * eD ⟨h, hh⟩ j := by
      intro j
      by_cases hj : j ∈ I₀
      · rw [hgconst j hj i₀ hi₀, hhconst j hj i₀ hi₀]
        simp only [c]
        group
      · have h1 : eD ⟨g, hg⟩ j * (eD ⟨g, hg⟩ i₀)⁻¹ =
            eD ⟨h, hh⟩ j * (eD ⟨h, hh⟩ i₀)⁻¹ := by
          simpa [Φ] using congrFun hΦ ⟨j, hj⟩
        calc eD ⟨g, hg⟩ j
            = (eD ⟨g, hg⟩ j * (eD ⟨g, hg⟩ i₀)⁻¹) * eD ⟨g, hg⟩ i₀ := by group
          _ = (eD ⟨h, hh⟩ j * (eD ⟨h, hh⟩ i₀)⁻¹) * eD ⟨g, hg⟩ i₀ := by rw [h1]
          _ = c * eD ⟨h, hh⟩ j := by
              simp only [c]
              ac_rfl
    have hdiag : LinFusion.ggFrameDiag Q (eD ⟨g, hg⟩) =
        LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) *
          LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩) := by
      rw [← LinFusion.ggFrameDiag_mul]
      congr 1
      funext j
      exact heq j
    have hDcen : InnerDiagA.diagGL (fun _ : Fin 6 => c) ∈
        Subgroup.center (GL (Fin 6) (GaloisField 2 (2 * 1))) := by
      rw [Subgroup.mem_center_iff]
      intro X
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL]
      ext i j
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      exact mul_comm _ _
    have hCcen : LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) ∈
        Subgroup.center (GL (Fin 6) (GaloisField 2 (2 * 1))) := by
      have hkey : Q⁻¹ * InnerDiagA.diagGL (fun _ : Fin 6 => c) * Q =
          InnerDiagA.diagGL (fun _ : Fin 6 => c) := by
        calc Q⁻¹ * InnerDiagA.diagGL (fun _ : Fin 6 => c) * Q
            = Q⁻¹ * (InnerDiagA.diagGL (fun _ : Fin 6 => c) * Q) := by rw [mul_assoc]
          _ = Q⁻¹ * (Q * InnerDiagA.diagGL (fun _ : Fin 6 => c)) := by
              rw [(Subgroup.mem_center_iff.mp hDcen) Q]
          _ = (Q⁻¹ * Q) * InnerDiagA.diagGL (fun _ : Fin 6 => c) := by rw [← mul_assoc]
          _ = InnerDiagA.diagGL (fun _ : Fin 6 => c) := by rw [inv_mul_cancel, one_mul]
      rw [LinFusion.ggFrameDiag, hkey]
      exact hDcen
    have hCtriv : ∀ X : GL (Fin 6) (GaloisField 2 (2 * 1)),
        LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) * X *
          (LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c))⁻¹ = X := by
      intro X
      have h1 := (Subgroup.mem_center_iff.mp hCcen) X
      rw [← h1]
      group
    have hconj : ∀ u : SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 6,
        InnerDiagSU.conjSU (LinFusion.ggFrameDiag Q (eD ⟨g, hg⟩)) hAg u =
          InnerDiagSU.conjSU (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩)) hAh u := by
      intro u
      apply Subtype.ext
      rw [InnerDiagSU.coe_conjSU, InnerDiagSU.coe_conjSU]
      calc LinFusion.ggFrameDiag Q (eD ⟨g, hg⟩) * (u : GL (Fin 6) (GaloisField 2 (2 * 1))) *
            (LinFusion.ggFrameDiag Q (eD ⟨g, hg⟩))⁻¹
          = (LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) *
              LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩)) * (u : GL (Fin 6) (GaloisField 2 (2 * 1))) *
              (LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) *
                LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩))⁻¹ := by rw [hdiag]
        _ = LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c) *
              (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩) * (u : GL (Fin 6) (GaloisField 2 (2 * 1))) *
                (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩))⁻¹) *
              (LinFusion.ggFrameDiag Q (fun _ : Fin 6 => c))⁻¹ := by group
        _ = LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩) * (u : GL (Fin 6) (GaloisField 2 (2 * 1))) *
              (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩))⁻¹ :=
            hCtriv (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩) *
              (u : GL (Fin 6) (GaloisField 2 (2 * 1))) *
              (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩))⁻¹)
    have hEq : ∀ u : SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 6,
        g * ψ u * g⁻¹ = h * ψ u * h⁻¹ := by
      intro u
      calc g * ψ u * g⁻¹
          = ψ (InnerDiagSU.conjSU (LinFusion.ggFrameDiag Q (eD ⟨g, hg⟩)) hAg u) := hag u
        _ = ψ (InnerDiagSU.conjSU (LinFusion.ggFrameDiag Q (eD ⟨h, hh⟩)) hAh u) := by
            rw [hconj u]
        _ = h * ψ u * h⁻¹ := (hah u).symm
    have hmem : h⁻¹ * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨u, rfl⟩
      have h1 : (h⁻¹ * g) * ψ u * (h⁻¹ * g)⁻¹ = ψ u := by
        calc (h⁻¹ * g) * ψ u * (h⁻¹ * g)⁻¹
            = h⁻¹ * (g * ψ u * g⁻¹) * h := by group
          _ = h⁻¹ * (h * ψ u * h⁻¹) * h := by rw [hEq u]
          _ = ψ u := by group
      have h2 : (h⁻¹ * g) * ψ u = ψ u * (h⁻¹ * g) := by
        calc (h⁻¹ * g) * ψ u
            = (h⁻¹ * g) * ψ u * (h⁻¹ * g)⁻¹ * (h⁻¹ * g) := by group
          _ = ψ u * (h⁻¹ * g) := by rw [h1]
      exact h2.symm
    rw [hC, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
  have hcomplcard : Nat.card {j : Fin 6 // j ∉ I₀} = 6 - I₀.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
    congr 1
    rw [← Fintype.card_coe I₀]
  have hfun : Nat.card ({j : Fin 6 // j ∉ I₀} → (GaloisField 2 (2 * 1))ˣ) =
      3 ^ (6 - I₀.card) := by
    rw [Nat.card_fun, hcardF, hcomplcard]
  have hle : 9 ≤ 3 ^ (6 - I₀.card) := by
    have h1 := Nat.card_le_card_of_injective Φ hinj
    rwa [hcardD, hfun] at h1
  have hI4 : I₀.card = 4 := by
    have h2 : 2 ≤ 6 - I₀.card :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hle)
    have h6 : I₀.card ≤ 6 := by simpa using Finset.card_le_univ I₀
    omega
  have hfun9 : Nat.card ({j : Fin 6 // j ∉ I₀} → (GaloisField 2 (2 * 1))ˣ) = 9 := by
    rw [hfun, hI4]
    norm_num
  have hbij : Function.Bijective Φ :=
    hinj.bijective_of_nat_card_le (by rw [hfun9, hcardD])
  have hJcard : (Finset.univ \ I₀).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hI4]
  obtain ⟨j₁, j₂, hjne, hJeq⟩ := Finset.card_eq_two.mp hJcard
  have hj₁ : j₁ ∉ I₀ := by
    have h : j₁ ∈ (Finset.univ \ I₀) := by
      rw [hJeq]
      exact Finset.mem_insert_self _ _
    exact (Finset.mem_sdiff.mp h).2
  have hj₂ : j₂ ∉ I₀ := by
    have h : j₂ ∈ (Finset.univ \ I₀) := by
      rw [hJeq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (Finset.mem_sdiff.mp h).2
  haveI : Fintype (GaloisField 2 (2 * 1))ˣ := Fintype.ofFinite _
  have hunits : 1 < Fintype.card (GaloisField 2 (2 * 1))ˣ := by
    rw [← Nat.card_eq_fintype_card, hcardF]
    norm_num
  obtain ⟨μ, hμ⟩ := Fintype.exists_ne_of_one_lt_card hunits
    (Φ ⟨1, D.one_mem⟩ ⟨j₂, hj₂⟩)
  have hconstne : (fun _ : {j : Fin 6 // j ∉ I₀} => μ) ≠ Φ ⟨1, D.one_mem⟩ := by
    intro h
    exact hμ (congrFun h ⟨j₂, hj₂⟩)
  obtain ⟨d, hd⟩ := hbij.2 (fun _ => μ)
  have hΦd : ∀ j : {j : Fin 6 // j ∉ I₀},
      eD d j.1 * (eD d i₀)⁻¹ = μ := by
    intro j
    have h1 := congrFun hd j
    simpa [Φ] using h1
  have hdne : (d : G) ≠ 1 := by
    intro h1
    have hd1 : d = ⟨1, D.one_mem⟩ := Subtype.ext h1
    have h2 : Φ d = Φ ⟨1, D.one_mem⟩ := by rw [hd1]
    rw [hd] at h2
    exact hconstne h2
  have hej₁ : eD d j₁ = μ * eD d i₀ := by
    have h1 := hΦd ⟨j₁, hj₁⟩
    calc eD d j₁ = (eD d j₁ * (eD d i₀)⁻¹) * eD d i₀ := by group
      _ = μ * eD d i₀ := by rw [h1]
  have hej₂ : eD d j₂ = μ * eD d i₀ := by
    have h1 := hΦd ⟨j₂, hj₂⟩
    calc eD d j₂ = (eD d j₂ * (eD d i₀)⁻¹) * eD d i₀ := by group
      _ = μ * eD d i₀ := by rw [h1]
  have hout : ∀ i i', i ≠ j₁ → i ≠ j₂ → i' ≠ j₁ → i' ≠ j₂ →
      eD d i = eD d i' := by
    intro i i' hi1 hi2 hi1' hi2'
    have hiI : i ∈ I₀ := by
      by_contra hi
      have hmem : i ∈ (Finset.univ \ I₀) := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hJeq] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hi1 h
      · exact hi2 (Finset.mem_singleton.mp h)
    have hi'I : i' ∈ I₀ := by
      by_contra hi
      have hmem : i' ∈ (Finset.univ \ I₀) := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hJeq] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hi1' h
      · exact hi2' (Finset.mem_singleton.mp h)
    exact (eD_spec d).2 i hiI i' hi'I
  exact ⟨d, Q, eD d, j₁, j₂, d.2, hdne, hQ, (eD_spec d).1, hjne,
    hej₁.trans hej₂.symm, hout⟩

end Inputs

end CFSG.StandardType
