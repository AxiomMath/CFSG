module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Quot
public import CFSG.RankThree.PartTwo.Sec13.Item13Res4ProofCensus
import CFSG.RankThree.PartTwo.Sec14.Ronan148HPointK
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec18.Item189KType
public import CFSG.RankThree.PartTwo.Sec18.Item189K0Setting

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A B X M : Subgroup G} {c : G}

private theorem k0Center_map_theta_eq_bot {L : Subgroup G}
    (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    {J : Type} [Group J] [Finite J] (ρ : J →* ↥L ⧸ aschbacherSolvableCore 3 ↥L)
    (hρ : Function.Surjective ρ) (hJs : Group.IsSolvable ↥(aschbacherSolvableCore 3 J))
    (hJ3 : ¬ 3 ∣ Nat.card ↥(aschbacherSolvableCore 3 J)) :
    (aschbacherSolvableCore 3 J).map ρ = ⊥ := by
  obtain ⟨hLs, -, hLn, hLmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hRn : ((aschbacherSolvableCore 3 J).map ρ).Normal :=
    Subgroup.Normal.map (aschbacherSolvableCore_normal 3 J) ρ hρ
  have hRs : Group.IsSolvable ↥((aschbacherSolvableCore 3 J).map ρ) :=
    Group.isSolvable_of_surjective (ρ.subgroupMap_surjective (aschbacherSolvableCore 3 J))
  have hRp : ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 J).map ρ) :=
    fun h => hJ3 (h.trans ((aschbacherSolvableCore 3 J).card_map_dvd ρ))
  have hRc : (aschbacherSolvableCore 3 J).map ρ ≤
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hRn with h | h
    · exfalso
      rw [h] at hRs
      haveI := CFSG.LocalCores.isQuasisimple_nontrivial hLq
      haveI : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
      exact Group.IsPerfect.not_isSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L)
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) ≃*
            (↥L ⧸ aschbacherSolvableCore 3 ↥L)).toMonoidHom) (MulEquiv.surjective _))
    · exact h
  exact central_normal_eq_bot (aschbacherSolvableCore 3 ↥L) hLs hLn hLmax _ hRc hRp

private theorem k0Center_ker_le_theta {L Z : Subgroup G} (hZL : Z ≤ L)
    (ρ : ↥Z →* ↥L ⧸ aschbacherSolvableCore 3 ↥L)
    (hker : ∀ z : Z, z ∈ ρ.ker ↔ (z : G) ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    ρ.ker ≤ aschbacherSolvableCore 3 ↥Z := by
  have hmax := (solvable_prime_complement_core_characterization (H := ↥Z) Nat.prime_three).2.2.2.1
  obtain ⟨hθsol, hθ3⟩ := Sec6.theta_solvable_and_not_dvd L
  set ι : ρ.ker →* inSubgroup (aschbacherSolvableCore 3) L :=
    { toFun := fun z => ⟨((z : Z) : G), (hker z).mp z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    exact h
  have hsol : Group.IsSolvable ρ.ker := Group.isSolvable_of_isSolvable_injective hι
  have hle : ρ.ker.map Z.subtype ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hker z).mp hz
  have h3 : ¬ 3 ∣ Nat.card ρ.ker := fun h => by
    have h' := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective Z.subtype_injective] at h'
    exact hθ3 (h.trans h')
  exact hmax _ (MonoidHom.normal_ker ρ) hsol h3

theorem nonempty_thetaQuot_equiv_residual_inf_centralizer {L D : Subgroup G}
    (hLp : Group.IsPerfect L) (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hD3 : IsPGroup 3 D) (hDC : D ≤ Sec4.thetaQuotCentralizer L) :
    Nonempty (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G))) ⧸
        aschbacherSolvableCore 3
          ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G)))
      ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  set Z := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set G))
  have hZL : Z ≤ L := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  set ρ : ↥Z →* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)).comp (Subgroup.inclusion hZL)
  have hcov := Sec6.le_residual_inf_centralizer_sup_theta hLp hD3 hDC
  have hsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) q
    have hl : (l : G) ∈ (Z : Set G) * (inSubgroup (aschbacherSolvableCore 3) L : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z _
        (hZL.trans (Sec6.le_normalizer_theta L))]
      exact hcov l.2
    obtain ⟨z, hz, t, ht, hzt⟩ := hl
    refine ⟨⟨z, hz⟩, ?_⟩
    change QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (Subgroup.inclusion hZL ⟨z, hz⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨t', ht', rfl⟩ := ht
    have : (Subgroup.inclusion hZL ⟨z, hz⟩)⁻¹ * l = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hzt]
      simp
    rw [this]
    exact ht'
  have hker : ∀ z : Z, z ∈ ρ.ker ↔ (z : G) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
    intro z
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (Subgroup.inclusion hZL z) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : w = Subgroup.inclusion hZL z := Subtype.ext hwz
      rwa [← this]
  have hkθ : ρ.ker ≤ aschbacherSolvableCore 3 ↥Z := k0Center_ker_le_theta hZL ρ hker
  obtain ⟨hθZs, -, hθZ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Z) Nat.prime_three
  have hθZ : aschbacherSolvableCore 3 ↥Z ≤ ρ.ker := by
    intro z hz
    have hm : ρ z ∈ (aschbacherSolvableCore 3 ↥Z).map ρ := Subgroup.mem_map_of_mem ρ hz
    rw [k0Center_map_theta_eq_bot hLq ρ hsurj hθZs hθZ3, Subgroup.mem_bot] at hm
    exact MonoidHom.mem_ker.mpr hm
  have hkeq : ρ.ker = aschbacherSolvableCore 3 ↥Z := le_antisymm hkθ hθZ
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkeq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)⟩

theorem K0Setting.isList46_imM (h46 : Sec4.Item4_6) (h : K0Setting G A B X M c)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) (hB : B ≤ Sec4.thetaQuotCentralizer K) :
    Sec4.IsList46 ↥(imM M K) := by
  obtain ⟨b, hbB, hb1, hb3⟩ := h.exists_mem_B
  have hDC : Subgroup.zpowers b ≤ Sec4.thetaQuotCentralizer K :=
    (Subgroup.zpowers_le.mpr hbB).trans hB
  have hD3 : IsPGroup 3 (Subgroup.zpowers b) := (CFSG.Open.isElemAbelian_zpowers hb3).isPGroup
  have hKp : Group.IsPerfect K := CFSG.RankThree.PartTwo.isPerfect_of_mem_thetaComponentsIn hK
  have hKq := quasisimple_of_mem_thetaComponentsIn hK
  have hsub : ({b} : Set G) ⊆ ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers b)
  set J := inSubgroup perfectResidual
    (K ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G))
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) :=
    (Sec6.inSubgroup_perfectResidual_le _).trans (inf_le_right.trans (Subgroup.centralizer_le hsub))
  have hJp : Group.IsPerfect J := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJq := Sec6.isQuasisimple_residual_inf_centralizer hKp hKq hD3 hDC
  have h1 := Sec14.Ronan148H.isList46_of_perfect_le_centralizer h46 h.thm4 hb3 hb1 hJb hJp hJq
  obtain ⟨e1⟩ := nonempty_thetaQuot_equiv_residual_inf_centralizer hKp hKq hD3 hDC
  obtain ⟨e2⟩ := nonempty_thetaQuot_equiv_imM hK
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv (e1.trans e2) h1

theorem K0Setting.card_center_imM (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (h : K0Setting G A B X M c)
    {K : Subgroup G} (hK : K ∈ thetaComponentsIn M) (hB : B ≤ Sec4.thetaQuotCentralizer K) :
    3 ∣ Nat.card (Subgroup.center ↥(imM M K)) → Nat.card (Subgroup.center ↥(imM M K)) = 3 :=
  fun h3 => hC ↥(imM M K) (h.isList46_imM h46 hK hB) (imM_isQuasisimple hK) h3

end CFSG.RankThree.PartTwo.Sec18
