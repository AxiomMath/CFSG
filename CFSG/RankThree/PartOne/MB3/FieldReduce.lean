module

public import CFSG.RankThree.PartOne.S11d.FixedRes

public import CFSG.RankThree.PartOne.MB3.FieldSetting
public import CFSG.RankThree.PartOne.MB3.Orbit
public import CFSG.RankThree.PartOne.S11d.Facts11
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.S12.Sec12TwoAssembly

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.Blueprint (EvenLieType)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_of_mem_zpowers_of_pow {p : ℕ} (hp : p.Prime) {c d : G} (hcp : c ^ p = 1)
    (hd : d ∈ Subgroup.zpowers c) (hd1 : d ≠ 1) : c ∈ Subgroup.zpowers d := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hd
  have hjp : ¬ (p : ℤ) ∣ j := by
    rintro ⟨m, hm⟩
    apply hd1
    rw [← hj, hm, zpow_mul, zpow_natCast, hcp, one_zpow]
  rw [← hj]
  exact mem_zpowers_zpow_of_not_dvd hp hcp hjp

theorem fieldSetting_of_tail
    (hS : SchreierFor InCatalog)
    (hPE : FieldFixedPElements) {p : ℕ} {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ}
    (cfg : Sec109.Config p A c L B n) {b : G} {S K : Subgroup G} (hW : Sec109.Witness A c B b S)
    (hK : K ∈ sectionTenAt p (sectionTenZeroStar p A) b) (hSK : S ≤ K)
    (hEven : EvenLieType (K ⧸ Subgroup.center K)) (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {a d : G} (haA : a ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hAeq : A = Subgroup.zpowers a ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers d)
    (hdK : Subgroup.zpowers d = A ⊓ K) (hfa : InducesFieldAut p a K)
    (hc : c ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers d) (hcind : InducesFieldAut p c K) :
    FieldSetting p A c L B n b S K
      (inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) a d := by
  have hp : p.Prime := cfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := sectionTenSetup_three_lt cfg.setup
    by_contra hlt
    have : p = 4 := by omega
    exact absurd (this ▸ hp) (by decide)
  have hbB : b ∈ B := hW.b_mem
  have hbA : b ∈ A := cfg.B_le_A hbB
  have hb1 : b ≠ 1 := hW.b_ne_one
  have hKθ : K ∈ thetaComponentsAt p b := hK.2
  have hKF : K ≤ Subgroup.centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hKθ).1
  have hq : CFSG.IsQuasisimple ↥K :=
    S11d.isQuasisimple_of_evenLie (isPerfect_of_mem_thetaComponentsAt hKθ) hEven
  have hEq : CFSG.IsQuasisimple ↥(inSubgroup perfectResidual
      (K ⊓ Subgroup.centralizer ({c} : Set G))) := fixedRes_isQuasisimple hcind
  set E := inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)) with hE
  have hev : CFSG.Assembly.evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq cfg.setup).le
  have hcp : c ^ p = 1 := cfg.pow_p_eq_one cfg.c_mem
  have hbC : b ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKF hg)
  have hFAS : FieldAutSetting p K c :=
    ⟨hp, hp5, hq, hEven, (Sec9A.evenRank_subgroup_le _).trans hev, hZ, hcind⟩
  have hFAR : FieldAutRank p K c :=
    ⟨hev, b, hbC, hb1, cfg.pow_p_eq_one hbA, cfg.A_comm c cfg.c_mem b hbA⟩
  have hdK' : d ∈ K := (Subgroup.mem_inf.mp (hdK ▸ Subgroup.mem_zpowers d)).2
  have hdc : d ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (cfg.A_comm c cfg.c_mem d hdA).symm
  have hdord : orderOf d = p := orderOf_eq_prime (cfg.pow_p_eq_one hdA) hd1
  have hdE : d ∈ E := hPE G p K c hFAS hcp hFAR d ⟨hdK', hdc⟩ ⟨1, by rw [pow_one, hdord]⟩
  obtain ⟨K₀, hK₀, hEK₀⟩ :=
    exists_thetaComponent_ge_fixedRes hS cfg.setup hbA hb1 cfg.c_mem cfg.c_ne_one hKθ hEq
  obtain ⟨hqL, hAL, hDc⟩ :=
    moving_maximal_data_at hS cfg.setup cfg.L_mem.1 cfg.c_mem cfg.c_ne_one cfg.L_mem.2
  have hK₀L : K₀ = L := by
    by_contra hne
    have hdK₀ : d ∈ K₀ := hEK₀ hdE
    have hcent := Sec12TwoAssembly.le_centralizer_of_mem_thetaComponentsAt_ne hp hK₀ cfg.L_mem.2
      hqL hne (B := Subgroup.zpowers d) (Subgroup.zpowers_le.mpr hdK₀)
      (Subgroup.zpowers_le.mpr (hAL hdA))
    have hdL : d ∈ Subgroup.centralizer (L : Set G) := hcent (Subgroup.mem_zpowers d)
    have hdD : d ∈ thetaQuotientCentralizer p A L := by
      rw [mem_thetaQuotientCentralizer_iff]
      refine ⟨hdA, hAL hdA, fun l hl => ?_⟩
      have h := Subgroup.mem_centralizer_iff.mp hdL l hl
      have : d * l * d⁻¹ * l⁻¹ = 1 := by
        rw [← h]
        group
      rw [this]
      exact Subgroup.one_mem _
    rw [hDc] at hdD
    exact hc (Subgroup.mem_sup_right
      (mem_zpowers_of_mem_zpowers_of_pow hp hcp hdD hd1))
  have hEL : E ≤ L := hK₀L ▸ hEK₀
  have hEK : E ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  have hEb : E ≤ Subgroup.centralizer ({b} : Set G) := hEK.trans hKF
  have hEV : E ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := le_inf hEL hEb
  have hcomp : CFSG.IsComponent (E.subgroupOf (L ⊓ Subgroup.centralizer ({b} : Set G))) := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hEV).symm hEq, ?_⟩
    set V := L ⊓ Subgroup.centralizer ({b} : Set G) with hV
    have hKsn : (K.subgroupOf (Subgroup.centralizer ({b} : Set G))).IsSubnormal :=
      isSubnormal_of_mem_thetaComponentsAt hKθ
    let ι : ↥V →* ↥(Subgroup.centralizer ({b} : Set G)) :=
      Subgroup.inclusion (inf_le_right : V ≤ Subgroup.centralizer ({b} : Set G))
    set Z' : Subgroup ↥V := (K.subgroupOf (Subgroup.centralizer ({b} : Set G))).comap ι with hZ'
    have hZ'sn : Z'.IsSubnormal := hKsn.comap ι
    have hZ'mem : ∀ g : ↥V, g ∈ Z' ↔ (g : G) ∈ K := fun g => Iff.rfl
    set Z : Subgroup ↥V := E.subgroupOf V with hZ
    have hZmem : ∀ g : ↥V, g ∈ Z ↔ (g : G) ∈ E := fun g => Iff.rfl
    have hZZ' : Z ≤ Z' := fun g hg => (hZ'mem g).mpr (hEK ((hZmem g).mp hg))
    have hnorm : (Z.subgroupOf Z').Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (((n : ↥Z') : ↥V) : G) ∈ E := (hZmem _).mp (Subgroup.mem_subgroupOf.mp hn)
      have hg' : (((g : ↥Z') : ↥V) : G) ∈ K ⊓ Subgroup.centralizer ({c} : Set G) :=
        ⟨(hZ'mem _).mp g.2, cfg.L_le_centralizer ((g : ↥V).2.1)⟩
      rw [Subgroup.mem_subgroupOf, hZmem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_mem_inSubgroup_perfectResidual hg' hn'
    exact Subgroup.IsSubnormal.trans hZZ' hnorm.isSubnormal hZ'sn
  exact
    { config := cfg, witness := hW, K_mem := hK, S_le := hSK, K_even := hEven, K_center := hZ,
      K_qs := hq, a_mem := haA, d_mem := hdA, d_ne_one := hd1, A_eq := hAeq, d_K := hdK,
      a_field := hfa, c_notMem := hc, c_field := hcind, E_eq := rfl, E_qs := hEq,
      d_mem_E := hdE, E_le_L := hEL, E_comp := hcomp }

end CFSG.RankThree.PartOne.MB3
