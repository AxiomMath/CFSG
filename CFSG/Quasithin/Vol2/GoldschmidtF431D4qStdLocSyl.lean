module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocBase
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutKb
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Res
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Quasithin.H13.F431.D4q.Out CFSG.QuasithinUnique
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem syl_of_card_mul {S H : Subgroup G} (hSH : S ≤ H) (hp : IsPGroup 2 S) {m : ℕ}
    (hm : ¬ 2 ∣ m) (hc : Nat.card H = Nat.card S * m) : IsSylowTwoOf S H := by
  refine ⟨hSH, hp, ?_⟩
  have h := Subgroup.relIndex_mul_card S H
  rw [inf_of_le_left hSH, hc] at h
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h1 : S.relIndex H = m := Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  show ¬ 2 ∣ S.relIndex H
  rw [h1]
  exact hm

theorem syl_of_le {P S H : Subgroup G} (hP : IsSylowTwoOf P H) (hPS : P ≤ S) (hSH : S ≤ H)
    (hp : IsPGroup 2 S) : IsSylowTwoOf S H := by
  refine ⟨hSH, hp, fun hdvd => hP.2.2 ?_⟩
  exact hdvd.trans (Subgroup.relIndex_dvd_of_le_left H hPS)

end Generic

section Core


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem syl_Ma_le_cent :
    d4Ma K σ ≤ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (d4Ma_commute_d4x₄ σ x hx 1).symm

theorem syl_U0t_le_U : d4U0t K σ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
  inf_le_left.trans (graphFixedSimpleComplement_le _)

theorem syl_U0t_le_cent :
    d4U0t K σ ≤ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) := inf_le_right

theorem syl_Ma_le_normalizer :
    d4Ma K σ ≤ Subgroup.normalizer (d4U0t K σ : Set (ModGL TwistTag.D4.tag K)) := by
  have key : ∀ m ∈ d4Ma K σ, ∀ u ∈ d4U0t K σ, m * u * m⁻¹ ∈ d4U0t K σ := by
    intro m hm u hu
    have hmC := syl_Ma_le_cent σ hm
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hmC hu2) (inv_mem hmC)⟩
    exact (Subgroup.mem_normalizer_iff.1
      (orbitRankOneGroup_le_normalizer_d4 σ ⟨1, by decide⟩ hm) u).1 hu1
  intro m hm
  exact mem_normalizer_of_conj_mem (key m hm) fun u hu => by
    simpa using key m⁻¹ (inv_mem hm) u hu

theorem syl_disjoint : Disjoint (d4U0t K σ) (d4Ma K σ) :=
  Disjoint.mono_left inf_le_left
    (disjoint_iff.2 (complement_inf_orbitRankOneGroup_d4 σ ⟨1, by decide⟩))

theorem syl_card_X2 {n : ℕ}
    (hk : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = n) :
    Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ) = n := by
  rw [← hk]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) =>
      (⟨(orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K),
        orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom ⟨1, by decide⟩ c,
        Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)⟩ :
          ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ))) ⟨?_, ?_⟩)).symm
  · intro c c' h
    have h1 := congrArg Subtype.val h
    simp only [coe_orbitX_one_d4] at h1
    exact Subtype.ext (pinnedX_injective _ _ _ h1)
  · rintro ⟨x, hxU, hxM⟩
    obtain ⟨c, hc⟩ := eq_orbitX_of_mem_d4 σ ⟨1, by decide⟩ hxM hxU
    exact ⟨c, Subtype.ext hc.symm⟩

theorem syl_isPGroup_U : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
  have hle := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  exact (CFSG.Quasithin.H13.Sec53F.TriD4.d4_sylow σ).2.1.of_injective
    (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem syl_odd_sq_sub_one {f : ℕ} (hf : 1 ≤ f) : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.two_pow_pos f)
  have h2 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  omega

include hσ in
theorem syl_sylow_modgl {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ 2 ^ f) :
    IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)))
      (d4C K σ ⊓ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K))) := by
  have hσE3 : σ ^ 3 = 1 := ringEquiv_cube_d4 σ hσ
  obtain ⟨-, -, -, hL2, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσE3
  have hk : Nat.card ↥(d4k K σ) = 2 ^ f := card_d4k_of_card σ hf hK hσq
  have hk' : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) = 2 ^ f := by
    rw [hL2]
    exact hk
  have hMa : Nat.card ↥(d4Ma K σ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (d4MaEquiv σ hσE3).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk']
  have hX2 := syl_card_X2 σ hk'
  have hH0 := centralizer_d4t_eq σ hσ
  have hcH : Nat.card ↥(d4C K σ ⊓ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)))
      = Nat.card ↥(d4U0t K σ) * (2 ^ f * ((2 ^ f) ^ 2 - 1)) := by
    rw [hH0, ← hMa]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (syl_Ma_le_normalizer σ) (syl_disjoint σ)
  have hcP : Nat.card ↥(d4U0t K σ ⊔
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ)) =
      Nat.card ↥(d4U0t K σ) * 2 ^ f := by
    rw [← hX2]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (inf_le_right.trans (syl_Ma_le_normalizer σ))
      (Disjoint.mono_right inf_le_right (syl_disjoint σ))
  have hPU : d4U0t K σ ⊔ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ) ≤
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    sup_le (syl_U0t_le_U σ) inf_le_left
  have hpU := syl_isPGroup_U σ
  have hPH : d4U0t K σ ⊔ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ) ≤
      d4C K σ ⊓ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) := by
    rw [hH0]
    exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  have hSylP := syl_of_card_mul hPH (hpU.to_le hPU) (syl_odd_sq_sub_one hf)
    (by rw [hcH, hcP, mul_assoc])
  have hPS : d4U0t K σ ⊔ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓ d4Ma K σ) ≤
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) :=
    le_inf hPU (sup_le (syl_U0t_le_cent σ) (inf_le_right.trans (syl_Ma_le_cent σ)))
  have hSH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) ≤
      d4C K σ ⊓ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) := fun x hx =>
    ⟨graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom hx.1, hx.2⟩
  exact syl_of_le hSylP hPS hSH (hpU.to_le inf_le_left)

theorem syl_mem_cent_tC {x : Cm σ} :
    x ∈ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) ↔
      (x : ModGL TwistTag.D4.tag K) ∈
        Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K)) := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ] at h1
    exact h1
  · intro h
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ]
    exact h

include hσ in
theorem sylow_t_d4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσq : ∀ c, σ.toRingHom c = c ^ 2 ^ f) :
    IsSylowTwoOf (Ust σ ⊓ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)))
      (Subgroup.centralizer ({tC σ hσ} : Set (Cm σ))) := by
  have hmod := syl_sylow_modgl σ hσ hf hK hσq
  have hle := graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have h := isSylowTwoOf_subgroupOf (Kb := d4C K σ) (inf_le_left.trans hle) inf_le_left hmod
  have e1 : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K))).subgroupOf (d4C K σ) =
        Ust σ ⊓ Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, syl_mem_cent_tC σ hσ]
  have e2 : (d4C K σ ⊓ Subgroup.centralizer ({d4t K σ} : Set (ModGL TwistTag.D4.tag K))).subgroupOf
      (d4C K σ) = Subgroup.centralizer ({tC σ hσ} : Set (Cm σ)) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, syl_mem_cent_tC σ hσ]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [e1, e2] at h
  exact h

end Core

end CFSG.Quasithin.H13.F431.D4q.StdLoc
