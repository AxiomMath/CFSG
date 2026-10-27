module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ul
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup P22k2

variable {G : Type} [Group G] [Finite G]

theorem rad118_subnormal (D : Data G) :
    ∀ K : Subgroup G, pCoreOf 2 D.M ≤ K → K ≤ rad118 D →
      K ≤ preMbar D (pCoreOf 3 (mbarImage D.M D.U (proofN D))) → (K.subgroupOf D.M).IsSubnormal := by
  intro K hQK hKR hKΘ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hNbn : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal D.M D.U _ (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  set T3 : Subgroup (MBar D.M D.U) := pCoreOf 3 (mbarImage D.M D.U (proofN D))
  haveI hT3n : T3.Normal := by
    change ((CFSG.pCore 3 ↥(mbarImage D.M D.U (proofN D))).map (mbarImage D.M D.U (proofN D)).subtype).Normal
    infer_instance
  have hT3p : IsPGroup 3 ↥T3 :=
    (CFSG.pCore_isPGroup (p := 3) (G := ↥(mbarImage D.M D.U (proofN D)))).map _
  let ψ₀ : ↥D.M →* MBar D.M D.U := QuotientGroup.mk' (kerAct D.M D.U).normalCore
  have hQker : CFSG.pCore 2 ↥D.M ≤ ψ₀.ker := by
    intro m hm
    have hmK : (m : G) ∈ K := hQK ⟨m, hm, rfl⟩
    obtain ⟨hmM, hmT⟩ := (P22x.mem_preMbar D).1 (hKΘ hmK)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)) ⟨m, hm⟩
    obtain ⟨j, hj⟩ := hT3p ⟨ψ₀ m, hmT⟩
    have hk' : (ψ₀ m) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have h1 : m ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [h1, map_one]
    have hj' : (ψ₀ m) ^ 3 ^ j = 1 := congrArg Subtype.val hj
    have h1 : orderOf (ψ₀ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf (ψ₀ m) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have hcop : Nat.Coprime (2 ^ k) (3 ^ j) := Nat.Coprime.pow k j (by norm_num)
    have h3 : orderOf (ψ₀ m) ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  haveI : (CFSG.pCore 2 ↥D.M).Normal := CFSG.pCore_normal
  let ψ : Bar2 D.M →* MBar D.M D.U := QuotientGroup.lift (CFSG.pCore 2 ↥D.M) ψ₀ hQker
  have hψπ : ∀ m : ↥D.M, ψ (uc22p21cPi D.M m) = ψ₀ m := fun m => rfl
  let Z : Subgroup (Bar2 D.M) := centralizer (fStar D : Set (Bar2 D.M)) ⊓ T3.comap ψ
  haveI hZn : Z.Normal := by
    haveI := centralizer_fStar_normal D
    haveI : (T3.comap ψ).Normal := hT3n.comap ψ
    infer_instance
  have hZnil : Group.IsNilpotent ↥Z := by
    refine uc22p22u_isNilpotent_of_isPGroup_map ψ 3 Z ?_ ?_
    · exact hT3p.to_le (by rintro _ ⟨z, hz, rfl⟩; exact hz.2)
    · intro u hu hψu v hv
      obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective D.M u
      have hmker : m ∈ (kerAct D.M D.U).normalCore := by
        have h1 : ψ₀ m = 1 := hψπ m ▸ hψu
        exact (QuotientGroup.eq_one_iff m).1 h1
      have hmC : (m : G) ∈ centralizer (D.U : Set G) :=
        Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hmker)
      have hmN : uc22p21cPi D.M m ∈ cStar D := uc22p21c_mem_barImage.2 ⟨m, ⟨m.2, hmC⟩, rfl⟩
      have hmF : uc22p21cPi D.M m ∈ fStar D :=
        uc22p22u_inf_centralizer_fstar_le (cStar D) ⟨hmN, hu.1⟩
      exact (Subgroup.mem_centralizer_iff.1 hv.1 _ hmF).symm
  set Ks : Subgroup (Bar2 D.M) := (K.subgroupOf D.M).map (uc22p21cPi D.M)
  have hKsZ : Ks ≤ Z := by
    rintro _ ⟨k, hk, rfl⟩
    have hkK : (k : G) ∈ K := hk
    obtain ⟨hkM, hkF⟩ := uc22p21c_mem_barPreimage.1 (hKR hkK)
    obtain ⟨hkM', hkT⟩ := (P22x.mem_preMbar D).1 (hKΘ hkK)
    exact ⟨hkF, hkT⟩
  have hsn : Ks.IsSubnormal :=
    Subgroup.IsSubnormal.trans hKsZ (CFSG.GorensteinWalter.isSubnormal_of_nilpotent hZnil Ks hKsZ)
      (Subgroup.Normal.isSubnormal hZn)
  have hcomap : Ks.comap (uc22p21cPi D.M) = K.subgroupOf D.M := by
    ext m
    constructor
    · rintro ⟨k, hk, hkm⟩
      have h1 : k⁻¹ * m ∈ CFSG.pCore 2 ↥D.M := by
        refine (QuotientGroup.eq_one_iff _).1 ?_
        change uc22p21cPi D.M _ = 1
        rw [map_mul, map_inv, hkm, inv_mul_cancel]
      have h2 : (((k⁻¹ * m : ↥D.M)) : G) ∈ K := hQK ⟨_, h1, rfl⟩
      have h3 : (m : G) = (k : G) * (((k⁻¹ * m : ↥D.M)) : G) := by simp
      exact Subgroup.mem_subgroupOf.2 (h3 ▸ K.mul_mem hk h2)
    · intro hm
      exact ⟨m, hm, rfl⟩
  rw [← hcomap]
  exact hsn.comap _

end CFSG.LocalAnalysis.UniquenessCase.UC22
