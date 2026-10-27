module

public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull

theorem isSolvable_of_normal_of_not_three_dvd {H : Type} [Group H] [Finite H]
    {J : Subgroup H} (hJ : J ∈ CFSG.RankThree.thetaComponents 3 H)
    (h3J : 3 ∣ Nat.card ↥J)
    {N : Subgroup ↥J} [N.Normal] (hN_not_three : ¬ 3 ∣ Nat.card N) : Group.IsSolvable ↥N := by
  obtain ⟨hJ_perfect, hJ_subnormal, hJ_quasisimple⟩ := hJ
  set θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥J with hθ
  have hθ_solvable : Group.IsSolvable θ := by
    exact (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := ↥J) (p := 3) (by norm_num)).1
  have hθ_not_three : ¬ 3 ∣ Nat.card θ := by
    exact (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := ↥J) (p := 3) (by norm_num)).2.2.1
  have hθ_normal : θ.Normal := by infer_instance
  set Q := ↥J ⧸ θ with hQ
  have h3Q : 3 ∣ Nat.card Q := by
    have hcard : Nat.card ↥J = Nat.card θ * Nat.card Q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ, hQ, Nat.mul_comm]
    have hdvd : 3 ∣ Nat.card θ * Nat.card Q := hcard ▸ h3J
    rcases (by norm_num : Nat.Prime 3).dvd_mul.mp hdvd with h | h
    · exact absurd h hθ_not_three
    · exact h
  have hNQ_normal : (N.map (QuotientGroup.mk' θ)).Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) _ (QuotientGroup.mk'_surjective _)
  have hNQ_not_three : ¬ 3 ∣ Nat.card (N.map (QuotientGroup.mk' θ)) := by
    intro hdvd
    exact hN_not_three (hdvd.trans (Subgroup.card_map_dvd _ _))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hJ_quasisimple hNQ_normal with htop | hcenter
  · exfalso
    have hdvd : Nat.card Q ∣ Nat.card N := by
      have h := Subgroup.card_map_dvd (QuotientGroup.mk' θ) (H := N)
      rw [htop, Subgroup.card_top] at h
      exact h
    exact hN_not_three (h3Q.trans hdvd)
  · have hθN_normal : (θ.subgroupOf N).Normal := hθ_normal.subgroupOf N
    have hθN_solvable : Group.IsSolvable (θ.subgroupOf N) := by
      let f : ↥(θ.subgroupOf N) →* ↥θ :=
        { toFun := fun x => ⟨(x.1 : ↥N).1, Subgroup.mem_subgroupOf.mp x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun y : ↥θ => y.1) hab
      exact Group.isSolvable_of_isSolvable_injective hf
    have hquot_solvable : Group.IsSolvable (↥N ⧸ θ.subgroupOf N) := by
      let f : ↥N →* Q := (QuotientGroup.mk' θ).comp N.subtype
      have hfker : f.ker = θ.subgroupOf N := by
        ext x
        exact (QuotientGroup.eq_one_iff (x : ↥J)).trans Subgroup.mem_subgroupOf.symm
      have hrange_central : f.range ≤ Subgroup.center Q := by
        rintro _ ⟨x, rfl⟩
        exact hcenter ⟨x, x.2, rfl⟩
      have hrange_comm : ∀ a b : ↥f.range, a * b = b * a := by
        intro a b
        apply Subtype.ext
        have ha : (a : Q) ∈ Subgroup.center Q := hrange_central a.2
        exact (Subgroup.mem_center_iff.mp ha (b : Q)).symm
      have hrange_solvable : Group.IsSolvable ↥f.range := Group.isSolvable_of_comm hrange_comm
      have hquot_iso : (↥N ⧸ θ.subgroupOf N) ≃* ↥f.range :=
        (QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
          (QuotientGroup.quotientKerEquivRange f)
      have hφ_inj : Function.Injective hquot_iso.toMonoidHom := hquot_iso.injective
      exact Group.isSolvable_of_isSolvable_injective hφ_inj
    have : (θ.subgroupOf N).Normal := hθN_normal
    have : Group.IsSolvable (θ.subgroupOf N) := hθN_solvable
    have : Group.IsSolvable (↥N ⧸ θ.subgroupOf N) := hquot_solvable
    exact Group.isSolvable_of_subgroup_quotient (θ.subgroupOf N)

theorem not_three_dvd_card_of_mem_thetaComponents_of_isSolvable {H : Type} [Group H] [Finite H]
    (hsol : Group.IsSolvable
      ↥(CFSG.GH74.GLS.oPrimeResidual 3 (H ⧸ CFSG.pPrimeCore 3 H)))
    {J : Subgroup H} (hJ : J ∈ CFSG.RankThree.thetaComponents 3 H) : ¬ 3 ∣ Nat.card J := by
  classical
  intro h3J
  obtain ⟨hJ_perfect, hJ_subnormal, hJ_quasisimple⟩ := hJ
  set θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥J with hθ
  have hθ_solvable : Group.IsSolvable θ := by
    exact (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := ↥J) (p := 3) (by norm_num)).1
  have hθ_not_three : ¬ 3 ∣ Nat.card θ := by
    exact (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := ↥J) (p := 3) (by norm_num)).2.2.1
  have hQ : CFSG.IsQuasisimple (↥J ⧸ θ) := hJ_quasisimple
  have h3Q : 3 ∣ Nat.card (↥J ⧸ θ) := by
    have hcard : Nat.card ↥J = Nat.card θ * Nat.card (↥J ⧸ θ) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ, Nat.mul_comm]
    have hdvd : 3 ∣ Nat.card θ * Nat.card (↥J ⧸ θ) := hcard ▸ h3J
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hθ_not_three
    · exact h
  let N : Subgroup ↥J := (CFSG.pPrimeCore 3 H).subgroupOf J
  have hN_normal : N.Normal := (CFSG.pPrimeCore_normal (p := 3) (G := H)).subgroupOf J
  have hN_dvd : Nat.card N ∣ Nat.card (CFSG.pPrimeCore 3 H) := by
    let g : ↥N →* ↥(CFSG.pPrimeCore 3 H) :=
      { toFun := fun x => ⟨(x.1 : ↥J).1, Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥(CFSG.pPrimeCore 3 H) => y.1) hab
    exact Subgroup.card_dvd_of_injective g hg
  have hN_not_three : ¬ 3 ∣ Nat.card N := by
    intro hdvd
    have hdvdP : 3 ∣ Nat.card (CFSG.pPrimeCore 3 H) := hdvd.trans hN_dvd
    have hcop := CFSG.pPrimeCore_coprime_card (p := 3) (G := H)
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mp hcop hdvdP
  have hN_solvable : Group.IsSolvable N :=
    isSolvable_of_normal_of_not_three_dvd ⟨hJ_perfect, hJ_subnormal, hJ_quasisimple⟩ h3J
      hN_not_three
  let f : ↥J →* H ⧸ CFSG.pPrimeCore 3 H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp J.subtype
  let K : Subgroup ↥J := CFSG.GH74.GLS.oPrimeResidual 3 ↥J
  have hK_image_le : K.map f ≤ CFSG.GH74.GLS.oPrimeResidual 3 (H ⧸ CFSG.pPrimeCore 3 H) := by
    have hK_def : K = Subgroup.closure {x : ↥J | ∃ k : ℕ, x ^ (3 ^ k) = 1} := rfl
    rw [hK_def, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨x, ⟨k, hk⟩, rfl⟩
    exact Subgroup.subset_closure ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hKmap_solvable : Group.IsSolvable ↥(K.map f) := by
    have : Group.IsSolvable ↥(CFSG.GH74.GLS.oPrimeResidual 3 (H ⧸ CFSG.pPrimeCore 3 H)) := hsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hK_image_le) (Subgroup.inclusion_injective hK_image_le)
  have hker_eq : f.ker = N := by
    ext x
    change (QuotientGroup.mk' (CFSG.pPrimeCore 3 H) (x : H) = 1) ↔
      x ∈ (CFSG.pPrimeCore 3 H).subgroupOf J
    rw [Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : H)
  have hker_solvable : Group.IsSolvable ↥(f.ker.subgroupOf K) := by
    rw [hker_eq]
    let g : ↥(N.subgroupOf K) →* ↥N :=
      { toFun := fun x => ⟨(x.1 : ↥J), Subgroup.mem_subgroupOf.mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥N => y.1) hab
    exact Group.isSolvable_of_isSolvable_injective hg
  have hK_solvable : Group.IsSolvable ↥K := by
    let g : ↥K →* ↥(K.map f) := f.subgroupMap K
    have hgker : g.ker = f.ker.subgroupOf K := by
      rw [Subgroup.ker_subgroupMap]
    have hle : g.ker ≤ (Subgroup.subtype (f.ker.subgroupOf K)).range := by
      rw [hgker, Subgroup.range_subtype]
    have : Group.IsSolvable ↥(f.ker.subgroupOf K) := hker_solvable
    have : Group.IsSolvable ↥(K.map f) := hKmap_solvable
    exact solvable_of_ker_le_range (Subgroup.subtype _) g hle
  have hKQ_eq : K.map (QuotientGroup.mk' θ) = CFSG.GH74.GLS.oPrimeResidual 3 (↥J ⧸ θ) :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oPrimeResidual _ (QuotientGroup.mk'_surjective _)
      (by norm_num)
  have hKQ_normal : (CFSG.GH74.GLS.oPrimeResidual 3 (↥J ⧸ θ)).Normal :=
    CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal 3 _
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hKQ_normal with htop | hcenter
  · exfalso
    have hQsolv : Group.IsSolvable (↥J ⧸ θ) := by
      have hsurj : Function.Surjective ((QuotientGroup.mk' θ).comp K.subtype) := by
        rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hKQ_eq]
        exact htop
      exact Group.isSolvable_of_surjective hsurj
    have : Nontrivial (↥J ⧸ θ) := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    exact Group.IsPerfect.not_isSolvable (↥J ⧸ θ) hQsolv
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : Group.IsPerfect (↥J ⧸ θ) := hQ.1
    have hP_center : ∀ (P : Sylow 3 (↥J ⧸ θ)),
        (P : Subgroup (↥J ⧸ θ)) ≤ Subgroup.center (↥J ⧸ θ) := by
      intro P x hx
      have hx3 : x ∈ CFSG.GH74.GLS.oPrimeResidual 3 (↥J ⧸ θ) := by
        have hx_pgroup : IsPGroup 3 ↥(P : Subgroup (↥J ⧸ θ)) := P.isPGroup'
        obtain ⟨k, hk⟩ := hx_pgroup ⟨x, hx⟩
        exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩
      exact hcenter hx3
    obtain ⟨P⟩ : Nonempty (Sylow 3 (↥J ⧸ θ)) := Sylow.nonempty
    exact CFSG.ComponentClassification.GrSLit.not_dvd_card_of_perfect_of_sylow_le_center P
      (hP_center P) h3Q

theorem not_three_dvd_card_of_mem_thetaComponents_of_card_648 {H : Type} [Group H] [Finite H]
    (h648 : Nat.card ↥(CFSG.GH74.GLS.oPrimeResidual 3 (H ⧸ CFSG.pPrimeCore 3 H)) = 648)
    {J : Subgroup H} (hJ : J ∈ CFSG.RankThree.thetaComponents 3 H) : ¬ 3 ∣ Nat.card J := by
  apply not_three_dvd_card_of_mem_thetaComponents_of_isSolvable (J := J) (hJ := hJ)
  have : Fintype ↥(CFSG.GH74.GLS.oPrimeResidual 3 (H ⧸ CFSG.pPrimeCore 3 H)) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 3) (b := 4)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, h648]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull
