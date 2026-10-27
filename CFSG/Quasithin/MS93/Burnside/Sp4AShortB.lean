module

public import CFSG.Quasithin.MS93.S512NCoc
import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S4ABasic
public import CFSG.Quasithin.MS93.S4L5Flat

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

@[expose] def burnsideSp4A_LemmaC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (_ : PUHyp M T L) (k : ℕ) (F : Type)
    [Field F] [Fintype F] [CharP F 2], Fintype.card F = 2 ^ k → 1 ≤ k →
    ∀ φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F), Function.Surjective φ →
    IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1 →
    ∀ w : G, w ∈ pCoreOf 2 M → (∀ l ∈ L, ⁅l, w⁆ ∈ Uq M T L ⊔ Dq M L) →
    ∀ Y : Subgroup G, Y ≤ L ⊔ pCoreOf 2 M → pCoreOf 2 M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, y * w = w * y) → S512N.Rigid ((Y.subgroupOf (L ⊔ pCoreOf 2 M)).map φ) →
    w ∈ Uq M T L ⊔ Dq M L

@[expose] def burnsideSp4A_LemmaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L) (k : ℕ) (F : Type)
    [Field F] [Fintype F] [CharP F 2], Fintype.card F = 2 ^ k → 2 ≤ k →
    ∀ φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F), Function.Surjective φ →
    IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1 →
    ∀ ν : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) ν (baseA _) →
    S33.pre h.le (ZM _ ν) ≤ L ⊔ pCoreOf 2 M →
    S512N.Rigid (((S33.pre h.le (ZM _ ν)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] noncomputable def burnsideSp4A_ycrit (h : PUHyp M T L) :
    Subgroup (puAmalgam h.le).Universal :=
  ⨆ (ν : Vtx (puAmalgam h.le)) (_ : IsCritical (puAmalgam h.le) ν (baseA _) ∧
    geo (puAmalgam h.le) (baseA _) ν 1 = baseB _), ZM (puAmalgam h.le) ν

theorem burnsideSp4A_zm_le_ycrit (h : PUHyp M T L) {ν : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) ν (baseA _))
    (hνβ : geo (puAmalgam h.le) (baseA _) ν 1 = baseB _) :
    ZM (puAmalgam h.le) ν ≤ burnsideSp4A_ycrit h :=
  le_iSup₂_of_le (f := fun ν (_ : IsCritical (puAmalgam h.le) ν (baseA _) ∧
    geo (puAmalgam h.le) (baseA _) ν 1 = baseB _) => ZM (puAmalgam h.le) ν) ν ⟨hc, hνβ⟩ le_rfl

theorem burnsideSp4A_ycrit_le_imM_T (h : PUHyp M T L) :
    burnsideSp4A_ycrit h ≤ imM h.le T := by
  refine iSup₂_le fun ν hν => ?_
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hν.1
  rw [← hEim]
  exact imM_mono h.le (S34E.pre_zm_le_not_le h hν.1 hν.2).1

theorem burnsideSp4A_ycrit_le_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) :
    burnsideSp4A_ycrit h ≤ imM h.le (L ⊔ pCoreOf 2 M) := by
  refine iSup₂_le fun ν hν => ?_
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hν.1
  rw [← hEim]
  exact imM_mono h.le (pre_zm_le_flat_sp h hU hν.1 hν.2)

theorem burnsideSp4A_qv_le_normalizer_ycrit (h : PUHyp M T L) :
    Qv (puAmalgam h.le) (baseA _) ≤
      Subgroup.normalizer (burnsideSp4A_ycrit h : Set (puAmalgam h.le).Universal) := by
  have hα := PU.isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp (qv_le_stab _ _ hg)
  have hgβ : g • baseB (puAmalgam h.le) = baseB _ :=
    (mem_stab _).mp (qv_le_stab _ _ (qv_le_qv _ h.hyp20 hα hαβ hg))
  rw [burnsideSp4A_ycrit, Subgroup.map_iSup]
  refine iSup_le fun ν => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hν => ?_
  rw [← zm_smul]
  refine burnsideSp4A_zm_le_ycrit h ?_ ?_
  · have := (isCritical_smul (puAmalgam h.le) g ν (baseA _)).mpr hν.1
    rwa [hgα] at this
  · rw [← hgα, geo_smul, hν.2, hgβ]

theorem burnsideSp4A_exists_crit (h : PUHyp M T L) :
    ∃ ν : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) ν (baseA _) ∧
      geo (puAmalgam h.le) (baseA _) ν 1 = baseB _ := by
  obtain ⟨ν, hc, hνβ⟩ := exists_isCritical_geo (puAmalgam h.le) h.hyp20 h.critDist_pos
    (PU.isMVtx_baseA (puAmalgam h.le)) (adj_baseA_baseB (puAmalgam h.le))
  exact ⟨ν, ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc, hνβ⟩

theorem burnsideSp4A_pCoreOf_le_normalizer_pre_ycrit (h : PUHyp M T L) :
    pCoreOf 2 M ≤ Subgroup.normalizer (S33.pre h.le (burnsideSp4A_ycrit h) : Set G) := by
  have hQ := burnsideSp4A_qv_le_normalizer_ycrit h
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hQ
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hqM : q ∈ M := pCoreOf_le' M hq
  have hq' : (puAmalgam h.le).ofA ⟨q, hqM⟩ ∈ imM h.le (pCoreOf 2 M) :=
    (S33.ofA_mem_imM_iff h.le _).2 hq
  have hn := Subgroup.mem_normalizer_iff.mp (hQ hq')
  constructor
  · intro hy
    obtain ⟨m, hm, rfl⟩ := (S33.mem_pre_iff' h.le).1 hy
    refine (S33.mem_pre_iff' h.le).2 ⟨⟨q, hqM⟩ * m * ⟨q, hqM⟩⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact (hn _).1 hm
  · intro hy
    obtain ⟨m, hm, hme⟩ := (S33.mem_pre_iff' h.le).1 hy
    have hye : y = q⁻¹ * (m : G) * q := by rw [hme]; group
    have hyM : y ∈ M := by
      rw [hye]
      exact M.mul_mem (M.mul_mem (M.inv_mem hqM) m.2) hqM
    refine (S33.mem_pre_iff' h.le).2 ⟨⟨y, hyM⟩, ?_, rfl⟩
    refine (hn _).2 ?_
    have hm' : (puAmalgam h.le).ofA m = (puAmalgam h.le).ofA ⟨q, hqM⟩ *
        (puAmalgam h.le).ofA ⟨y, hyM⟩ * ((puAmalgam h.le).ofA ⟨q, hqM⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hme]
    rw [← hm']
    exact hm

theorem burnsideSp4A_rigid_pre_ycrit (hR : burnsideSp4A_LemmaR) (h : PUHyp M T L)
    (hU : S34F.IsSp4UEven M T L) {k : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (hcard : Fintype.card F = 2 ^ k) (hk : 2 ≤ k)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1) :
    S512N.Rigid (((S33.pre h.le (burnsideSp4A_ycrit h)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) := by
  obtain ⟨ν, hc, hνβ⟩ := burnsideSp4A_exists_crit h
  have hRν := hR G M T L h k F hcard hk φ hφs hφ ν hc (pre_zm_le_flat_sp h hU hc hνβ)
  refine hRν.mono (Subgroup.map_mono fun x hx => ?_)
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨m, hm, hme⟩ := (S33.mem_pre_iff' h.le).1 hx
  exact (S33.mem_pre_iff' h.le).2 ⟨m, burnsideSp4A_zm_le_ycrit h hc hνβ hm, hme⟩

theorem burnsideSp4A_omega_le (hC : burnsideSp4A_LemmaC) (hR : burnsideSp4A_LemmaR)
    (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) :
    omegaOneCenterOf T ≤ Uq M T L ⊔ Dq M L := by
  obtain ⟨m, F, _, _, φ, hm, hcard, hφs, hφ⟩ := IsSp4UEven.exists_natural_flat h hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hYT : S33.pre h.le (burnsideSp4A_ycrit h) ≤ T :=
    S33.pre_le_of_le_imM h (burnsideSp4A_ycrit_le_imM_T h)
  have hYK : S33.pre h.le (burnsideSp4A_ycrit h) ≤ L ⊔ pCoreOf 2 M :=
    S33.pre_le_of_le_imM h (burnsideSp4A_ycrit_le_flat h hU)
  have hYR := burnsideSp4A_rigid_pre_ycrit hR h hU hcard' (by omega) hφs hφ
  have hΩC : omegaOneCenterOf T ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  intro z hz
  have hzZ : z ∈ Z0q M T := omegaOneCenterOf_le_Z0q M T h.le hz
  refine hC G M T L h (2 * m) F hcard' (by omega) φ hφs hφ z (h.Z0q_le_pCoreOf hzZ) ?_ _ hYK
    (burnsideSp4A_pCoreOf_le_normalizer_pre_ycrit h) ?_ hYR
  · intro l hl
    refine Subgroup.mem_sup_left ?_
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hzZ hl)
  · intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hΩC hz) y (hYT hy)

theorem burnsideSp4A_zq_le (hC : burnsideSp4A_LemmaC) (hR : burnsideSp4A_LemmaR)
    (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) :
    Z0q M T ≤ Uq M T L ⊔ Dq M L := by
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have hDM : Dq M L ≤ M := inf_le_left.trans (pCoreOf_le' M)
  have hN : ((Uq M T L ⊔ Dq M L).subgroupOf M).Normal := by
    rw [Subgroup.subgroupOf_sup hUM hDM]
    haveI := S4A.Uq_normal h
    haveI := S4A.Dq_normal h
    infer_instance
  exact normalClosureIn_le_of (sup_le hUM hDM) hN
    (inf_le_left.trans (burnsideSp4A_omega_le hC hR h hU))

end CFSG.Quasithin.MS93.S4L
