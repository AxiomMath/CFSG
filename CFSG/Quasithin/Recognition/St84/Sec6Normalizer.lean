module

public import CFSG.GroupTheory.GroupAction.PGroupFixedPoints
public import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.GroupTheory.PResidualLocalFinite
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6Cover
public import CFSG.GroupTheory.TwoElementGeneration
public import CFSG.Quasithin.Recognition.St84.Sec6SK
public import CFSG.Quasithin.Recognition.St84.Sec6S5

import CFSG.Quasithin.Recognition.St84.Gen.OddTransGen
import CFSG.Quasithin.Recognition.St84.Gen.PushZL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F6Faithful
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
open CFSG.Quasithin.F6 (sqClosure)

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

@[expose] def M (U : Subgroup G) : Subgroup G := Subgroup.normalizer (U : Set G)

namespace Setup

variable (X : Setup Γ G)

@[expose] def E (U : Subgroup G) (i : ℤ) : Subgroup G := X.Q i ⊓ M U

@[expose] def Lst (U : Subgroup G) (i : ℤ) : Subgroup G := oTwoPrime (X.normGi U i)

@[expose] def Yst (U : Subgroup G) (i : ℤ) : Subgroup G := pResidualOf 2 (X.Lst U i)

theorem E_eq_Q_inf_normGi (U : Subgroup G) (i : ℤ) :
    X.E U i = X.Q i ⊓ X.normGi U i := by
  ext x
  simp only [Setup.E, M, Setup.normGi, Subgroup.mem_inf]
  constructor
  · rintro ⟨hxQ, hxN⟩
    exact ⟨hxQ, hxN, X.Q_le_Gi i hxQ⟩
  · rintro ⟨hxQ, hxN, -⟩
    exact ⟨hxQ, hxN⟩

private theorem conjSub_Q_zero_of_mem {m : G} (hm : m ∈ X.Gi 0) :
    conjSub m (X.Q 0) = X.Q 0 := by
  rw [Setup.Q, ← pCoreOf_conjSub, conjSub_eq_of_mem hm]

private theorem pow_not_mem_of_sq_mem {H : Subgroup G} {y : G} (hy : y ∉ H)
    (hy2 : y ^ 2 ∈ H) : ∀ m : ℕ, Odd m → y ^ m ∉ H := by
  intro m hm
  obtain ⟨k, rfl⟩ := hm
  have hpow : y ^ (2 * k + 1) = (y ^ 2) ^ k * y := by
    rw [pow_succ, pow_mul]
  rw [hpow]
  intro hmem
  apply hy
  have hk : (y ^ 2) ^ k ∈ H := H.pow_mem hy2 k
  convert H.mul_mem (H.inv_mem hk) hmem using 1
  group

private theorem relIndex_normGi_zero_inf_one {U : Subgroup G} (hU : X.IsSK U) :
    (X.normGi U 0 ⊓ X.Gi 1).relIndex (X.normGi U 1) = 2 := by
  let A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1
  obtain ⟨g, hgM1, hg02, -⟩ := hU.exists_swap₁
  have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hgA : g ∉ A := by
    intro hg
    have hgG0 : g ∈ X.Gi 0 := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
    exact h02 (hg02.symm.trans (MulAction.mem_stabilizer_iff.mp hgG0)).symm
  have hA' : A = X.normGi U 1 ⊓ X.Gi 0 := by
    simp only [A, Setup.normGi]
    ac_rfl
  have horbit : MulAction.orbit ↥(X.normGi U 1) (X.vert 0) = {X.vert 0, X.vert 2} := by
    ext w
    constructor
    · rintro ⟨m, rfl⟩
      exact hU.pair (m : G) m.2
    · intro hw
      have hw' : w = X.vert (0 : ℤ) ∨ w = X.vert 2 := by simpa using hw
      rcases hw' with rfl | rfl
      · exact MulAction.mem_orbit_self _
      · exact ⟨⟨g, hgM1⟩, hg02⟩
  change A.relIndex (X.normGi U 1) = 2
  rw [hA', Subgroup.inf_relIndex_left,
    FanTree.relIndex_stabilizer_eq_ncard_orbit (H := X.normGi U 1) (b := X.vert 0),
    horbit, Set.ncard_pair h02]

private theorem exists_mem_normGi_one_normalizer_K {U : Subgroup G} (hU : X.IsSK U) :
    ∃ y ∈ X.normGi U 1, y ∉ X.normGi U 0 ⊓ X.Gi 1 ∧
      y ∈ Subgroup.normalizer (X.K : Set G) := by
  let A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1
  have hKA : X.K ≤ A := le_inf (hU.K_le_normGi 0) (X.K_le_Gi 1)
  have hAGi : A ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (inf_le_left.trans (X.normGi_le_Gi U 0)) inf_le_right
  have hpc := X.pCoreOf_eq_inf_edgeSylow 0 hKA hAGi
  have hP : X.skP U = pCoreOf 2 A := skP_eq_pCoreOf X hU
  have hPinf : X.skP U = A ⊓ X.edgeSylow 0 := hP.trans hpc.1
  have hPleA : X.skP U ≤ A := hP.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 A)
  haveI : Finite ↥A := finite_of_le_stabilizer X.hyp (hAGi.trans inf_le_left)
  have hSylow : IsSylowTwoOf (X.skP U) A := by
    rw [hPinf]
    exact X.isSylowTwoOf_inf_edgeSylow 0 hKA hAGi
  have hPnorm : ((X.skP U).subgroupOf A).Normal := by
    rw [hP]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A)
  have hPsup : X.skP U ⊔ X.K = A := by
    rw [hP, sup_comm, hpc.2]
  have hPinfK : X.skP U ⊓ X.K = ⊥ := by
    rw [hPinf, inf_assoc, inf_comm (X.edgeSylow 0) X.K, X.K_inf_edgeSylow 0]
    exact inf_bot_eq A
  obtain ⟨g, hgM1, hg02, -⟩ := hU.exists_swap₁
  have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hgA : g ∉ A := by
    intro hg
    have hgG0 : g ∈ X.Gi 0 := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
    exact h02 (hg02.symm.trans (MulAction.mem_stabilizer_iff.mp hgG0)).symm
  have hgN : g ∈ Subgroup.normalizer (A : Set G) :=
    normGi_zero_inf_one_normal_in_one X hU hgM1
  have hAeq : conjSub g A = A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hKg : conjSub g X.K ≤ A := (conjSub_mono g hKA).trans hAeq.le
  have hPg : conjSub g (X.skP U) = X.skP U := by
    rw [hP, ← pCoreOf_conjSub, hAeq]
  have hNK : X.skP U ⊔ conjSub g X.K = A := by
    have h := congrArg (conjSub g) hPsup
    rw [conjSub_sup, hPg, hAeq] at h
    exact h
  have hNK' : X.skP U ⊓ conjSub g X.K = ⊥ := by
    have hPg' : conjSub g⁻¹ (X.skP U) = X.skP U := by
      have h := congrArg (conjSub g⁻¹) hPg
      rw [conjSub_conjSub_inv] at h
      exact h.symm
    have hmain : conjSub g⁻¹ (X.skP U ⊓ conjSub g X.K) = ⊥ := by
      rw [conjSub_inf, hPg', conjSub_conjSub_inv, hPinfK]
    rwa [conjSub_eq_bot_iff] at hmain
  obtain ⟨n, hnP, hnK⟩ := exists_conj_eq_of_complement (F := A) hPleA hPnorm hSylow
    hKA hKg hPsup hNK hPinfK hNK'
  have hAM1 : A ≤ X.normGi U 1 := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hyM1 : n * g ∈ X.normGi U 1 :=
    (X.normGi U 1).mul_mem (hAM1 (hPleA hnP)) hgM1
  have hyA : n * g ∉ A := by
    intro hmem
    exact hgA (by
      have := A.mul_mem (A.inv_mem (hPleA hnP)) hmem
      simpa using this)
  have hyK : n * g ∈ Subgroup.normalizer (X.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub (n * g) X.K = X.K
    rw [conjSub_mul, hnK, conjSub_inv_conjSub]
  exact ⟨n * g, hyM1, hyA, hyK⟩

theorem IsSK.exists_t {U : Subgroup G} (hU : X.IsSK U) :
    ∃ t : G, t ∈ X.normGi U 1 ⊓ Subgroup.normalizer (X.K : Set G) ∧
      t • X.vert 0 = X.vert 2 ∧ (∃ m : ℕ, t ^ 2 ^ m = 1) ∧ t ^ 2 ∈ X.skP U := by
  let A : Subgroup G := X.normGi U 0 ⊓ X.Gi 1
  obtain ⟨y, hyM1, hyA, hyK⟩ := exists_mem_normGi_one_normalizer_K X hU
  have hA' : A = X.normGi U 1 ⊓ X.Gi 0 := by
    simp only [A, Setup.normGi]
    ac_rfl
  have hrel : A.relIndex (X.normGi U 1) = 2 := relIndex_normGi_zero_inf_one X hU
  have hsqA : ∀ z ∈ X.normGi U 1, z ∉ A → z ^ 2 ∈ A := by
    intro z hz hzA
    have hindex : (A.subgroupOf (X.normGi U 1)).index = 2 := hrel
    have hz' : (⟨z, hz⟩ : ↥(X.normGi U 1)) ^ 2 ∈ A.subgroupOf (X.normGi U 1) :=
      Subgroup.sq_mem_of_index_two hindex _
    simpa [Subgroup.mem_subgroupOf] using hz'
  have h02 : X.vert (0 : ℤ) ≠ X.vert 2 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  have hyfin : IsOfFinOrder y := by
    haveI : Finite ↥(X.Gi 1) := X.hyp.finite_stab (X.vert 1)
    obtain ⟨k, hkpos, hk⟩ := (isOfFinOrder_of_finite
      (⟨y, X.normGi_le_Gi U 1 hyM1⟩ : ↥(X.Gi 1))).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k, hkpos, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨a, m, hm_odd, hord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (ne_of_gt hyfin.orderOf_pos)
  have htM1 : y ^ m ∈ X.normGi U 1 := (X.normGi U 1).pow_mem hyM1 m
  have htA : y ^ m ∉ A :=
    pow_not_mem_of_sq_mem (H := A) hyA (hsqA y hyM1 hyA) m hm_odd
  have ht02 : (y ^ m) • X.vert 0 = X.vert 2 := by
    have hp := hU.pair (y ^ m) htM1
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp) with h | h
    · exact absurd h (by
        intro hfix
        exact htA (by
          rw [hA']
          exact Subgroup.mem_inf.mpr ⟨htM1, MulAction.mem_stabilizer_iff.mpr hfix⟩))
    · exact h
  have ht2A : (y ^ m) ^ 2 ∈ A := hsqA (y ^ m) htM1 htA
  have ht2G0 : (y ^ m) ^ 2 ∈ X.Gi 0 :=
    (inf_le_left.trans (X.normGi_le_Gi U 0)) ht2A
  have ht2G1 : (y ^ m) ^ 2 ∈ X.Gi 1 := (inf_le_right : A ≤ X.Gi 1) ht2A
  have htpow : (y ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, Nat.mul_comm, ← hord, pow_orderOf_eq_one]
  have h2elem : ∃ j : ℕ, ((y ^ m) ^ 2) ^ 2 ^ j = 1 := by
    refine ⟨a, ?_⟩
    rw [← pow_mul, show 2 * 2 ^ a = 2 ^ a * 2 from by ring, pow_mul, htpow, one_pow]
  have hfix0 : ((y ^ m) ^ 2) • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp ht2G0
  have hfix2 : ((y ^ m) ^ 2) • X.vert 2 = X.vert 2 := by
    rw [← ht02, ← mul_smul, ← pow_succ, pow_succ', mul_smul, hfix0]
  have hQ1 : ((y ^ m) ^ 2) ∈ X.Q 1 :=
    mem_pCoreOf_of_fixes_two X.hyp ht2G1 h2elem (X.adj 0).symm (X.adj 1) h02 hfix0 hfix2
  refine ⟨y ^ m, ?_, ht02, ⟨a, htpow⟩, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨htM1, (Subgroup.normalizer (X.K : Set G)).pow_mem hyK m⟩
  · refine Subgroup.mem_inf.mpr ⟨hQ1, ?_⟩
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normalizer (U : Set G)).pow_mem
        ((Subgroup.normalizer (U : Set G)).pow_mem hyM1.1 m) 2, ht2G0⟩

theorem conjSub_normGi_of_mem_normalizer {U : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {i j : ℤ} (h : t • X.vert i = X.vert j) :
    conjSub t (X.normGi U i) = X.normGi U j := by
  rw [Setup.normGi, Setup.normGi, conjSub_inf, conjSub_eq_of_mem ht,
    ← stabilizer_smul_eq_conjSub, h]

theorem conjSub_E_of_mem_normalizer {U : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (U : Set G)) {i j : ℤ} (h : t • X.vert i = X.vert j) :
    conjSub t (X.E U i) = X.E U j := by
  show conjSub t (X.Q i ⊓ Subgroup.normalizer (U : Set G)) =
    X.Q j ⊓ Subgroup.normalizer (U : Set G)
  rw [conjSub_inf, conjSub_eq_of_mem ht, Setup.Q, Setup.Q, ← pCoreOf_conjSub,
    ← stabilizer_smul_eq_conjSub, h]

theorem IsSK.conjSub_normGi_zero {U : Subgroup G} {t : G} (ht : t ∈ X.normGi U 1)
    (ht02 : t • X.vert 0 = X.vert 2) :
    conjSub t (X.normGi U 0) = X.normGi U 2 :=
  conjSub_normGi_of_mem_normalizer X ht.1 ht02

theorem IsSK.conjSub_E_zero {U : Subgroup G} {t : G} (ht : t ∈ X.normGi U 1)
    (ht02 : t • X.vert 0 = X.vert 2) :
    conjSub t (X.E U 0) = X.E U 2 :=
  conjSub_E_of_mem_normalizer X ht.1 ht02

theorem IsSK.conjSub_skP {U : Subgroup G} {t : G}
    (ht : t ∈ X.normGi U 1) (ht02 : t • X.vert 0 = X.vert 2) :
    conjSub t (X.skP U) = X.skP U := by
  have hQ1 : conjSub t (X.Q 1) = X.Q 1 := by
    rw [Setup.Q, ← pCoreOf_conjSub, ← stabilizer_smul_eq_conjSub,
      MulAction.mem_stabilizer_iff.mp ht.2]
  have hQ0 : X.Q 1 ≤ X.Gi 0 := by
    have h := X.Q_le_edgeSylow_right 1
    rw [show (1 : ℤ) - 1 = 0 from by norm_num] at h
    exact h.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  have hQ2 : X.Q 1 ≤ X.Gi 2 := by
    have h := X.Q_le_edgeSylow_left 1
    exact h.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
  rw [Setup.skP, conjSub_inf, hQ1, IsSK.conjSub_normGi_zero X ht ht02]
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQ, hxM⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_inf.mpr ⟨hxM.1, hQ0 hxQ⟩⟩
  · intro x hx
    obtain ⟨hxQ, hxM⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_inf.mpr ⟨hxM.1, hQ2 hxQ⟩⟩

theorem not_skP_le_Q_zero_of_isSKMax {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥) : ¬ X.skP U ≤ X.Q 0 := by
  haveI : Finite ↥(X.normGi U 0) :=
    finite_of_le_stabilizer X.hyp (X.normGi_le_Gi U 0)
  intro hle
  have hP_M : IsSylowTwoOf (X.skP U) (X.normGi U 0) := isSylowTwoOf_skP_zero X hU.1
  have hNQ : ∀ m ∈ X.normGi U 0,
      conjSub m (X.Q 0 ⊓ X.normGi U 0) = X.Q 0 ⊓ X.normGi U 0 := by
    intro m hm
    obtain ⟨hmM, hmG⟩ := Subgroup.mem_inf.mp hm
    rw [conjSub_inf, X.conjSub_Q_zero_of_mem hmG, conjSub_eq_of_mem hm]
  have hQ2 : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  have hE2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.normGi U 0) := hQ2.to_le inf_le_left
  have hEnorm : X.normGi U 0 ≤
      Subgroup.normalizer (X.Q 0 ⊓ X.normGi U 0 : Set G) := by
    intro m hm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hNQ m hm)
  have hinf_le_P : X.Q 0 ⊓ X.normGi U 0 ≤ X.skP U :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hEnorm hE2).trans
      (pCoreOf_le_of_isSylowTwoOf hP_M)
  have hEq : X.skP U = X.Q 0 ⊓ X.normGi U 0 :=
    le_antisymm (le_inf hle inf_le_right) hinf_le_P
  have hM0norm : X.normGi U 0 ≤ Subgroup.normalizer (X.skP U : Set G) := by
    rw [hEq]
    intro m hm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hNQ m hm)
  exact IsSKMax.noCharNormal X hU (X.skP U) le_rfl hP
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hM0norm

theorem not_skP_le_Q_zero_or_of_isSKMax {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) :
    ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
  hP.imp_left (X.not_skP_le_Q_zero_of_isSKMax hU)

private theorem mem_map_Lst_of_involution {H : Type*} [Group H] {U : Subgroup G}
    (ρ : ↥(X.Gi 0) →* H) {σ : H} (hσ : σ ∈ ((X.normGi U 0).subgroupOf (X.Gi 0)).map ρ)
    (hσ2 : σ * σ = 1) : σ ∈ ((X.Lst U 0).subgroupOf (X.Gi 0)).map ρ := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  obtain ⟨m, hmM, hm_eq⟩ := Subgroup.mem_map.mp hσ
  obtain ⟨m', hm'M, ⟨c, hc⟩, hm'eq⟩ :=
    CFSG.GroupTheory.exists_twoElem_mem_map ρ hmM (by rw [hm_eq]; exact hσ2)
  refine Subgroup.mem_map.mpr ⟨m', ?_, hm'eq.trans hm_eq⟩
  rw [Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure
    ⟨Subgroup.mem_subgroupOf.mp hm'M, ⟨c, by simpa using congrArg Subtype.val hc⟩⟩

private theorem card_nbrAction_of_n_eq_one (hn0 : X.n 0 = 1) :
    Nat.card ↥(X.nbrAction 0) = 3 := by
  have hΔcard : Nat.card ↥(X.nbrAction 0) = 3 := by
    have hval : Nat.card (Γ.neighborSet (X.vert 0)) = 3 := by
      simpa [show nOf Γ (X.vert 0) = 1 from hn0] using (X.hyp.valency (X.vert 0)).2
    calc Nat.card ↥(X.nbrAction 0) = Nat.card (Γ.neighborSet (X.vert 0)) :=
          Nat.card_congr
            { toFun := fun x => ⟨x.1, X.mem_nbrAction.mp x.2⟩
              invFun := fun x => ⟨x.1, X.mem_nbrAction.mpr x.2⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
      _ = 3 := hval
  exact hΔcard

private theorem two_dvd_card_map_normGi {U : Subgroup G} (hn0 : X.n 0 = 1)
    (hP : ¬ X.skP U ≤ X.Q 0) :
    2 ∣ Nat.card ↥(((X.normGi U 0).subgroupOf (X.Gi 0)).map
      (MulAction.toPermHom (↥(X.Gi 0)) ↥(X.nbrAction 0))) := by
  haveI : Finite ↥(Γ.neighborSet (X.vert 0)) := X.hyp.finite_neighborSet (X.vert 0)
  haveI : Finite ↥(X.nbrAction 0) :=
    Finite.of_injective (fun x : ↥(X.nbrAction 0) =>
      (⟨x.1, X.mem_nbrAction.mp x.2⟩ : Γ.neighborSet (X.vert 0)))
      (fun a b h => Subtype.ext
        (congrArg (fun z : Γ.neighborSet (X.vert 0) => z.1) h))
  let ρ : ↥(X.Gi 0) →* Equiv.Perm ↥(X.nbrAction 0) :=
    MulAction.toPermHom (↥(X.Gi 0)) ↥(X.nbrAction 0)
  let M0 : Subgroup ↥(X.Gi 0) := (X.normGi U 0).subgroupOf (X.Gi 0)
  let H : Subgroup (Equiv.Perm ↥(X.nbrAction 0)) := M0.map ρ
  have hΔcard := card_nbrAction_of_n_eq_one X hn0
  obtain ⟨x, hxP, hxQ⟩ := SetLike.not_le_iff_exists.mp hP
  have hxM0 : x ∈ X.normGi U 0 := (Subgroup.mem_inf.mp hxP).2
  have hxG0 : x ∈ X.Gi 0 := (Subgroup.mem_inf.mp hxM0).2
  have hP2 : IsPGroup 2 (X.skP U) := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  obtain ⟨c, hc⟩ := hP2 ⟨x, hxP⟩
  have hx2 : x ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
  have hxL : x ∈ X.L 0 := Subgroup.subset_closure ⟨hxG0, ⟨c, hx2⟩⟩
  have hρx_ne : ρ ⟨x, hxG0⟩ ≠ 1 := by
    intro h1
    have hfix : ∀ w : V, Γ.Adj (X.vert 0) w → x • w = w := by
      intro w hw
      have h2 : ρ ⟨x, hxG0⟩ ⟨w, X.mem_nbrAction.mpr hw⟩ =
          ⟨w, X.mem_nbrAction.mpr hw⟩ := by
        rw [h1]; rfl
      exact congrArg Subtype.val h2
    have hxQ' := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).N_fixes_neighbors_mem_Q
      X.hyp.adj_smul (X.hyp.finite_stab (X.vert 0))
      (X.hyp.valency (X.vert 0)).2 (X.hyp.valency (X.vert 0)).1
      (x := ⟨x, hxL⟩) hfix
    exact hxQ hxQ'
  have hord2 : orderOf (ρ ⟨x, hxG0⟩) ∣ 2 := by
    have h1 : orderOf (ρ ⟨x, hxG0⟩) ∣ orderOf (⟨x, hxG0⟩ : ↥(X.Gi 0)) :=
      orderOf_map_dvd ρ _
    have h2 : orderOf (⟨x, hxG0⟩ : ↥(X.Gi 0)) ∣ 2 ^ c := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hx2
    have h3' : orderOf (ρ ⟨x, hxG0⟩) ∣ 6 := by
      have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (Equiv.Perm ↥(X.nbrAction 0)))
        (Subgroup.mem_top (ρ ⟨x, hxG0⟩))
      rwa [Subgroup.card_top, Nat.card_perm, hΔcard] at h
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exfalso
        have hx1 : x = 1 := by simpa [h0] using hx2
        exact hxQ (hx1 ▸ (X.Q 0).one_mem)
      · exact h0
    have hc3 : Nat.Coprime (2 ^ c) 3 := by
      rw [Nat.coprime_pow_left_iff hcpos]
      norm_num
    have hcop : Nat.Coprime (orderOf (ρ ⟨x, hxG0⟩)) 3 :=
      Nat.Coprime.of_dvd_left (h1.trans h2) hc3
    exact hcop.dvd_of_dvd_mul_right (by rwa [show (6 : ℕ) = 2 * 3 by norm_num] at h3')
  have h2dvd : 2 ∣ Nat.card ↥H := by
    have hord : orderOf (ρ ⟨x, hxG0⟩) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hρx_ne
      · exact h
    have h := Subgroup.orderOf_dvd_natCard H
      (Subgroup.mem_map.mpr ⟨⟨x, hxG0⟩, hxM0, rfl⟩)
    rwa [hord] at h
  exact h2dvd

private theorem Lst_covers_one {U : Subgroup G} (hU : X.IsSK U) (hn0 : X.n 0 = 1)
    (hP : ¬ X.skP U ≤ X.Q 0) :
    ∀ l ∈ X.L 0, ∃ l' ∈ X.Lst U 0,
      ∀ w : V, Γ.Adj (X.vert 0) w → l' • w = l • w := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  haveI : Finite ↥(Γ.neighborSet (X.vert 0)) := X.hyp.finite_neighborSet (X.vert 0)
  haveI : Finite ↥(X.nbrAction 0) :=
    Finite.of_injective (fun x : ↥(X.nbrAction 0) =>
      (⟨x.1, X.mem_nbrAction.mp x.2⟩ : Γ.neighborSet (X.vert 0)))
      (fun a b h => Subtype.ext
        (congrArg (fun z : Γ.neighborSet (X.vert 0) => z.1) h))
  let ρ : ↥(X.Gi 0) →* Equiv.Perm ↥(X.nbrAction 0) :=
    MulAction.toPermHom (↥(X.Gi 0)) ↥(X.nbrAction 0)
  let M0 : Subgroup ↥(X.Gi 0) := (X.normGi U 0).subgroupOf (X.Gi 0)
  let H : Subgroup (Equiv.Perm ↥(X.nbrAction 0)) := M0.map ρ
  have hΔcard := card_nbrAction_of_n_eq_one X hn0
  have htrans : ∀ a b : ↥(X.nbrAction 0), ∃ h ∈ H, h • a = b := by
    intro a b
    obtain ⟨m, hmM, hmab⟩ := hU.trans0 a.1 b.1
      (X.mem_nbrAction.mp a.2) (X.mem_nbrAction.mp b.2)
    refine ⟨ρ ⟨m, X.normGi_le_Gi U 0 hmM⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨m, X.normGi_le_Gi U 0 hmM⟩, hmM, rfl⟩
    · exact Subtype.ext hmab
  have h3 : 3 ∣ Nat.card ↥H := by
    let a0 : ↥(X.nbrAction 0) := ⟨X.vert 1, X.mem_nbrAction.mpr (X.adj 0)⟩
    haveI : MulAction.IsPretransitive ↥H ↥(X.nbrAction 0) := ⟨fun a b => by
      obtain ⟨h, hh, e⟩ := htrans a b
      exact ⟨⟨h, hh⟩, e⟩⟩
    have h := (MulAction.stabilizer ↥H a0).index_dvd_card
    rwa [MulAction.index_stabilizer_of_transitive ↥H a0, hΔcard] at h
  have h2dvd : 2 ∣ Nat.card ↥H := by
    simpa only [H, M0, ρ] using two_dvd_card_map_normGi X hn0 hP
  have hHtop : H = ⊤ := by
    have hdvd6 : Nat.card ↥H ∣ 6 := by
      have h := Subgroup.card_dvd_of_le (H := H) (K := ⊤) le_top
      rwa [Subgroup.card_top, Nat.card_perm, hΔcard] at h
    have h6 : 6 ∣ Nat.card ↥H :=
      (by norm_num : Nat.Coprime 3 2).mul_dvd_of_dvd_of_dvd h3 h2dvd
    have hcard : Nat.card ↥H = 6 := Nat.dvd_antisymm hdvd6 h6
    rw [← Subgroup.card_eq_iff_eq_top, hcard, Nat.card_perm, hΔcard]
    norm_num
  have hρLst_top : ((X.Lst U 0).subgroupOf (X.Gi 0)).map ρ = ⊤ := by
    rw [eq_top_iff, ← CFSG.GroupTheory.closure_involutions_perm_eq_top (Δ := ↥(X.nbrAction 0)),
      Subgroup.closure_le]
    rintro σ hσ
    have hσH : σ ∈ H := by rw [hHtop]; exact Subgroup.mem_top σ
    exact mem_map_Lst_of_involution X ρ (by simpa only [H, M0] using hσH) hσ
  intro l hl
  have hlG : l ∈ X.Gi 0 := oTwoPrime_le (X.Gi 0) hl
  have hρl : ρ ⟨l, hlG⟩ ∈ ((X.Lst U 0).subgroupOf (X.Gi 0)).map ρ := by
    rw [hρLst_top]
    exact Subgroup.mem_top _
  obtain ⟨l', hl'Lst, hl'eq⟩ := Subgroup.mem_map.mp hρl
  refine ⟨(l' : G), Subgroup.mem_subgroupOf.mp hl'Lst, ?_⟩
  intro w hw
  let δ : ↥(X.nbrAction 0) := ⟨w, X.mem_nbrAction.mpr hw⟩
  have h1 : ρ l' δ = ρ ⟨l, hlG⟩ δ := by rw [hl'eq]
  exact congrArg Subtype.val h1

theorem L_eq_Lst_sup_Q {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    X.L 0 = X.Lst U 0 ⊔ X.Q 0 := by
  haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
  have hN : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hLst_le_L : X.Lst U 0 ≤ X.L 0 := oTwoPrime_mono (X.normGi_le_Gi U 0)
  have hQ_le_L : X.Q 0 ≤ X.L 0 := hN.oTwo_le
  have hker : ∀ x ∈ X.L 0, (∀ w : V, Γ.Adj (X.vert 0) w → x • w = w) → x ∈ X.Q 0 := by
    intro x hxL hfix
    exact hN.N_fixes_neighbors_mem_Q X.hyp.adj_smul (X.hyp.finite_stab (X.vert 0))
      (X.hyp.valency (X.vert 0)).2 (X.hyp.valency (X.vert 0)).1
      (x := ⟨x, hxL⟩) (by intro a ha; exact hfix a ha)
  have hcover : ∀ l ∈ X.L 0, ∃ l' ∈ X.Lst U 0,
      ∀ w : V, Γ.Adj (X.vert 0) w → l' • w = l • w := by
    rcases (show X.n 0 = 1 ∨ 2 ≤ X.n 0 from by
      rcases Nat.lt_or_eq_of_le (X.hyp.valency (X.vert 0)).1 with h | h
      · exact Or.inr h
      · exact Or.inl h.symm) with h1 | h2
    · exact Lst_covers_one X hU h1 (hP.resolve_right (by rw [h1]; norm_num))
    · exact X.covers_of_two_le (H := X.normGi U 0) 0 h2 (X.normGi_le_Gi U 0)
        (hU.K_le_normGi 0) (fun a b ha hb => hU.trans0 a b ha hb)
  refine le_antisymm ?_ (sup_le hLst_le_L hQ_le_L)
  intro l hl
  obtain ⟨l', hl', hact⟩ := hcover l hl
  have hmem : l'⁻¹ * l ∈ X.Q 0 := by
    refine hker (l'⁻¹ * l) ?_ ?_
    · exact (X.L 0).mul_mem ((X.L 0).inv_mem (hLst_le_L hl')) hl
    · intro w hw
      rw [mul_smul, ← hact w hw, inv_smul_smul]
  have hprod : l = l' * (l'⁻¹ * l) := by group
  rw [hprod]
  exact (X.Lst U 0 ⊔ X.Q 0).mul_mem (Subgroup.mem_sup_left hl')
    (Subgroup.mem_sup_right hmem)

private theorem exists_Lst_smul_eq {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) {a b : V}
    (ha : Γ.Adj (X.vert 0) a) (hb : Γ.Adj (X.vert 0) b) :
    ∃ w ∈ X.Lst U 0, w • a = b := by
  obtain ⟨l, hlL, hlab⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans a b ha hb
  have hLstQ : X.Lst U 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (oTwoPrime_le (X.normGi U 0)).trans ((X.normGi_le_Gi U 0).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hcoe : (↑(X.Q 0 ⊔ X.Lst U 0) : Set G) =
      (X.Q 0 : Set G) * (X.Lst U 0 : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) (X.Lst U 0) hLstQ
  have hlmem : l ∈ (X.Q 0 : Set G) * (X.Lst U 0 : Set G) := by
    rw [← hcoe, sup_comm, ← L_eq_Lst_sup_Q X hU hP]
    exact hlL
  obtain ⟨q, hq, l', hl', hql⟩ := hlmem
  have hl'G0 : l' ∈ X.Gi 0 :=
    (oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0) hl'
  have hw : Γ.Adj (X.vert 0) (l' • a) := by
    have h := (X.hyp.adj_smul l' (X.vert 0) a).2 ha
    rwa [MulAction.mem_stabilizer_iff.mp hl'G0] at h
  refine ⟨l', hl', ?_⟩
  calc l' • a = q • (l' • a) := (X.Q_fixes_neighbors_vert 0 (l' • a) hw q hq).symm
    _ = (q * l') • a := (mul_smul q l' a).symm
    _ = l • a := by
      congr 1
    _ = b := hlab

private theorem pCoreOf_normGi_fixes_neighbors {U : Subgroup G} (hU : X.IsSK U) :
    ∀ a : V, Γ.Adj (X.vert 0) a → ∀ q ∈ pCoreOf 2 (X.normGi U 0), q • a = a := by
  classical
  let M₀ : Subgroup G := X.normGi U 0
  haveI : Finite ↥M₀ := finite_of_le_stabilizer X.hyp (X.normGi_le_Gi U 0)
  let Δ : SubMulAction ↥M₀ V :=
    { carrier := Γ.neighborSet (X.vert 0)
      smul_mem' := by
        intro m a ha
        rw [SimpleGraph.mem_neighborSet] at ha ⊢
        have hm : (m : G) ∈ X.Gi 0 := X.normGi_le_Gi U 0 m.2
        have hfix : (m : G) • X.vert 0 = X.vert 0 := MulAction.mem_stabilizer_iff.mp hm
        rw [← hfix]
        exact (X.hyp.adj_smul (m : G) (X.vert 0) a).mpr ha }
  have htrans : MulAction.IsPretransitive ↥M₀ Δ := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg, hgxy⟩ := hU.trans0 x.1 y.1 x.2 y.2
    exact ⟨⟨g, hg⟩, Subtype.ext hgxy⟩
  haveI := htrans
  let QN : Subgroup ↥M₀ := (pCoreOf 2 M₀).subgroupOf M₀
  have hQNnormal : QN.Normal := by
    rw [show QN = CFSG.pCore 2 ↥M₀ from CFSG.openPCoreOf_subgroupOf 2 M₀]
    infer_instance
  haveI : QN.Normal := hQNnormal
  have hQNp : IsPGroup 2 QN := by
    rw [show QN = CFSG.pCore 2 ↥M₀ from CFSG.openPCoreOf_subgroupOf 2 M₀]
    exact CFSG.pCore_isPGroup (G := ↥M₀) (p := 2)
  haveI : Finite ↥(Γ.neighborSet (X.vert 0)) := (X.hyp.finite_neighborSet _).to_subtype
  haveI : Finite Δ := inferInstance
  have hΔcard : Nat.card Δ = 2 ^ X.n 0 + 1 := by
    have h1 : Nat.card Δ = Nat.card (Γ.neighborSet (X.vert 0)) :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1]
    simpa using (X.hyp.valency (X.vert 0)).2
  have hOdd : Odd (2 ^ X.n 0 + 1) := by
    have hn : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    have heven : Even (2 ^ X.n 0) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact heven.add_odd odd_one
  have hp : ¬ 2 ∣ Nat.card Δ := by
    rw [hΔcard]
    exact fun h => Nat.not_even_iff_odd.mpr hOdd (even_iff_two_dvd.mpr h)
  intro a ha q hq
  have hqM : q ∈ M₀ := (CFSG.LieType.BorelTits.pCoreOf_le 2 M₀) hq
  let aΔ : Δ := ⟨a, ha⟩
  let qN : QN := ⟨⟨q, hqM⟩, hq⟩
  have h := CFSG.GroupTheory.smul_eq_self_of_isPGroup_of_normal (p := 2) (Q := QN) hQNp hp
    qN.2 aΔ
  have h' : (qN : ↥M₀) • a = a := congrArg Subtype.val h
  simpa [qN, MulAction.subgroup_smul_def] using h'

private theorem normGi_pCoreOf_le_Q {U : Subgroup G} (hU : X.IsSK U) :
    pCoreOf 2 (X.normGi U 0) ≤ X.Q 0 := by
  let M₀ : Subgroup G := X.normGi U 0
  haveI : Finite ↥M₀ := finite_of_le_stabilizer X.hyp (X.normGi_le_Gi U 0)
  have hfix := pCoreOf_normGi_fixes_neighbors X hU
  have hT0 : X.vert (-1 : ℤ) ≠ X.vert 1 := by
    intro h
    have := X.vert_injective h
    norm_num at this
  refine le_pCoreOf_of_isPGroup_fixes_two X.hyp (pCoreOf_isPGroup' M₀)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 M₀).trans (X.normGi_le_Gi U 0))
    (a := X.vert (-1)) (b := X.vert 1) (by simpa using (X.adj (-1)).symm) (X.adj 0) hT0 ?_ ?_
  · intro y hy
    exact hfix (X.vert (-1)) (by simpa using (X.adj (-1)).symm) y hy
  · intro y hy
    exact hfix (X.vert 1) (X.adj 0) y hy

theorem E_eq_pCoreOf {U : Subgroup G} (hU : X.IsSK U) :
    X.E U 0 = pCoreOf 2 (X.normGi U 0) := by
  have hE_le : X.E U 0 ≤ X.normGi U 0 :=
    le_inf inf_le_right (inf_le_left.trans (X.Q_le_Gi 0))
  have hEnorm : X.normGi U 0 ≤ Subgroup.normalizer (X.E U 0 : Set G) := by
    intro m hm
    obtain ⟨hmM, hmG⟩ := Subgroup.mem_inf.mp hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub m (pCoreOf 2 (X.Gi 0) ⊓ Subgroup.normalizer (U : Set G)) =
      pCoreOf 2 (X.Gi 0) ⊓ Subgroup.normalizer (U : Set G)
    rw [conjSub_inf, ← pCoreOf_conjSub, conjSub_eq_of_mem hmG, conjSub_eq_of_mem hmM]
  have hEp : IsPGroup 2 (X.E U 0) := (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hE_le hEnorm hEp
  · exact le_inf (normGi_pCoreOf_le_Q X hU)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (X.normGi U 0)).trans inf_le_left)

theorem E_eq_inf_skP {U : Subgroup G} (hU : X.IsSK U) :
    X.E U 0 = X.Q 0 ⊓ X.skP U := by
  haveI : Finite ↥(X.normGi U 0) :=
    finite_of_le_stabilizer X.hyp (X.normGi_le_Gi U 0)
  have hEeq : X.E U 0 = pCoreOf 2 (X.normGi U 0) := E_eq_pCoreOf X hU
  have hQ2 : IsPGroup 2 (X.Q 0) := pCoreOf_isPGroup' (X.Gi 0)
  have hE_le_Q : X.E U 0 ≤ X.Q 0 := hEeq ▸ normGi_pCoreOf_le_Q X hU
  have hEnormQ : X.normGi U 0 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.normGi U 0 : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨hmM, hmG⟩ := Subgroup.mem_inf.mp hm
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
      show conjSub m (X.Q 0 ⊓ X.normGi U 0) = X.Q 0 ⊓ X.normGi U 0
      rw [conjSub_inf, X.conjSub_Q_zero_of_mem hmG, conjSub_eq_of_mem hm])
  have hE2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.normGi U 0) := hQ2.to_le inf_le_left
  have hME : X.Q 0 ⊓ X.normGi U 0 ≤ pCoreOf 2 (X.normGi U 0) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hEnormQ hE2
  have hP_eq : X.skP U = pCoreOf 2 (X.normGi U 0 ⊓ X.Gi 1) := skP_eq_pCoreOf X hU
  have hE_le_P : X.E U 0 ≤ X.skP U := by
    rw [hP_eq]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · refine le_inf (hEeq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) ?_
      exact hE_le_Q.trans (((X.Q_le_edgeSylow_left 0).trans
        (X.isSylowTwoOf_edgeSylow 0).1).trans inf_le_right)
    · intro m hm
      rw [hEeq]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi U 0))
        (Subgroup.mem_inf.mp hm).1
    · exact hQ2.to_le hE_le_Q
  refine le_antisymm (le_inf hE_le_Q hE_le_P) ?_
  intro x hx
  obtain ⟨hxQ, hxP⟩ := Subgroup.mem_inf.mp hx
  rw [hEeq]
  exact hME (Subgroup.mem_inf.mpr ⟨hxQ, (inf_le_right : X.skP U ≤ X.normGi U 0) hxP⟩)

theorem pCoreOf_Lst_eq_E {U : Subgroup G} (hU : X.IsSK U) :
    pCoreOf 2 (X.Lst U 0) = X.E U 0 := by
  rw [E_eq_pCoreOf X hU]
  have hLM : X.Lst U 0 ≤ X.normGi U 0 := oTwoPrime_le _
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ (pCoreOf_isPGroup' _)
    · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Lst U 0)).trans hLM
    · exact (le_normalizer_oTwoPrime (X.normGi U 0)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X.Lst U 0))
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ (pCoreOf_isPGroup' _)
    · exact le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' _)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.normGi U 0))
    · exact hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.normGi U 0))

private theorem pCore_Lst_eq_E {U : Subgroup G} (hU : X.IsSK U) :
    CFSG.pCore 2 ↥(X.Lst U 0) = (X.E U 0).subgroupOf (X.Lst U 0) := by
  rw [← CFSG.openPCoreOf_subgroupOf 2 (X.Lst U 0), pCoreOf_Lst_eq_E X hU]

theorem Lst_inf_kernel {U : Subgroup G} :
    X.Lst U 0 ⊓ kernelOnNeighbors Γ G (X.vert 0) = X.E U 0 := by
  have hEeq := X.E_eq_Q_inf_normGi U 0
  have hE_le_Lst : X.E U 0 ≤ X.Lst U 0 := by
    rw [hEeq]
    exact le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left) inf_le_right
  have hE_le_Q : X.E U 0 ≤ X.Q 0 := by
    rw [hEeq]
    exact inf_le_left
  have hLst_le_L : X.Lst U 0 ≤ X.L 0 := oTwoPrime_mono (X.normGi_le_Gi U 0)
  have hLst_inf_Q : X.Lst U 0 ⊓ X.Q 0 = X.E U 0 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxL, hxQ⟩ := Subgroup.mem_inf.mp hx
      rw [hEeq]
      exact Subgroup.mem_inf.mpr ⟨hxQ, oTwoPrime_le (X.normGi U 0) hxL⟩
    · exact le_inf hE_le_Lst hE_le_Q
  have hQ_le_kernel : X.Q 0 ≤ kernelOnNeighbors Γ G (X.vert 0) :=
    (X.kernelOnNeighbors_inf_edgeSylow 0).ge.trans inf_le_left
  have hL₀ : X.L 0 ⊓ kernelOnNeighbors Γ G (X.vert 0) = X.Q 0 :=
    inf_kernelOnNeighbors_eq_pCoreOf X.hyp (X.hyp.isLocL2_oTwoPrime (X.vert 0))
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxL, hxK⟩ := Subgroup.mem_inf.mp hx
    have hxQ : x ∈ X.Q 0 := by
      have hmem : x ∈ X.L 0 ⊓ kernelOnNeighbors Γ G (X.vert 0) := ⟨hLst_le_L hxL, hxK⟩
      rwa [hL₀] at hmem
    have hxQ' : x ∈ X.Lst U 0 ⊓ X.Q 0 := ⟨hxL, hxQ⟩
    rwa [hLst_inf_Q] at hxQ'
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨hE_le_Lst hx, hQ_le_kernel (hE_le_Q hx)⟩

private theorem nonempty_Lst_quot_mulEquiv_L_quot {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0)
    [hNdomA : ((X.E U 0).subgroupOf (X.Lst U 0)).Normal]
    [hNcodA : ((X.Q 0).subgroupOf (X.L 0)).Normal] :
    Nonempty (↥(X.Lst U 0) ⧸ (X.E U 0).subgroupOf (X.Lst U 0) ≃*
      ↥(X.L 0) ⧸ (X.Q 0).subgroupOf (X.L 0)) := by
  have hL : X.L 0 = X.Lst U 0 ⊔ X.Q 0 := L_eq_Lst_sup_Q X hU hP
  let hN := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hLst_le_L : X.Lst U 0 ≤ X.L 0 := oTwoPrime_mono (X.normGi_le_Gi U 0)
  have hE_eq_pCore : X.E U 0 = pCoreOf 2 (X.normGi U 0) := E_eq_pCoreOf X hU
  have hE_le_Q : X.E U 0 ≤ X.Q 0 := by
    rw [hE_eq_pCore]; exact normGi_pCoreOf_le_Q X hU
  have hE_normal : X.normGi U 0 ≤ Subgroup.normalizer (X.E U 0 : Set G) := by
    rw [hE_eq_pCore]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hpCore := pCore_Lst_eq_E X hU
  let Ndom : Subgroup ↥(X.Lst U 0) := (X.E U 0).subgroupOf (X.Lst U 0)
  let Ncod : Subgroup ↥(X.L 0) := (X.Q 0).subgroupOf (X.L 0)
  haveI hNdom : Ndom.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le (X.normGi U 0)).trans hE_normal)
  haveI hNcod : Ncod.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le (X.Gi 0)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  let f : ↥(X.Lst U 0) →* ↥(X.L 0) := Subgroup.inclusion hLst_le_L
  have hfmap : Ndom ≤ Ncod.comap f := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hE_le_Q (Subgroup.mem_subgroupOf.mp hx))
  let g : ↥(X.Lst U 0) ⧸ Ndom →* ↥(X.L 0) ⧸ Ncod := QuotientGroup.map Ndom Ncod f hfmap
  have hg_inj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [MonoidHom.mem_ker, QuotientGroup.map_mk] at hq
      rw [QuotientGroup.eq_one_iff]
      have hq' : f x ∈ Ncod := (QuotientGroup.eq_one_iff (f x)).mp hq
      have hxQ : ((f x : ↥(X.L 0)) : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hq'
      have hxMU : ((x : ↥(X.Lst U 0)) : G) ∈ Subgroup.normalizer (U : Set G) :=
        ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_normalizer U 0)) x.2
      exact Subgroup.mem_subgroupOf.mpr ⟨hxQ, hxMU⟩
  have hg_surj : Function.Surjective g := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      haveI : Finite ↥(X.Gi 0) := X.hyp.finite_stab (X.vert 0)
      have hLs' : X.Lst U 0 ≤ X.Gi 0 :=
        (oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0)
      have hQnormal : ((X.Q 0).subgroupOf (X.Gi 0)).Normal :=
        Subgroup.normal_subgroupOf_of_le_normalizer
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
      haveI := hQnormal
      have hsup' : (X.Lst U 0).subgroupOf (X.Gi 0) ⊔ (X.Q 0).subgroupOf (X.Gi 0) =
          (X.L 0).subgroupOf (X.Gi 0) := by
        rw [← Subgroup.subgroupOf_sup hLs' (X.Q_le_Gi 0), hL]
      let y' : ↥(X.Gi 0) := ⟨(y : G), oTwoPrime_le (X.Gi 0) y.2⟩
      have hy'mem : y' ∈ (X.L 0).subgroupOf (X.Gi 0) := y.2
      rw [← hsup'] at hy'mem
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hy'mem
      refine ⟨QuotientGroup.mk ⟨(a : G), ha⟩, ?_⟩
      rw [QuotientGroup.map_mk, QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hbQ : (b : G) ∈ X.Q 0 := Subgroup.mem_subgroupOf.mp hb
      have hb' : (b : G) = (a : G)⁻¹ * (y : G) := by
        have h := congrArg (fun z : ↥(X.Gi 0) => (z : G)) hab
        change (a : G) * (b : G) = (y : G) at h
        rw [← h]
        group
      show (a : G)⁻¹ * (y : G) ∈ X.Q 0
      rw [← hb']
      exact hbQ
  have hg : Nonempty (↥(X.Lst U 0) ⧸ Ndom ≃* ↥(X.L 0) ⧸ Ncod) :=
    ⟨MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩⟩
  exact ⟨MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩⟩

theorem isL2Quot_Lst {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    IsL2Quot (X.n 0) (oTwoQuot ↥(X.Lst U 0)) := by
  let hN := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hE_eq_pCore : X.E U 0 = pCoreOf 2 (X.normGi U 0) := E_eq_pCoreOf X hU
  have hE_normal : X.normGi U 0 ≤ Subgroup.normalizer (X.E U 0 : Set G) := by
    rw [hE_eq_pCore]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  haveI hNdomA : ((X.E U 0).subgroupOf (X.Lst U 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le (X.normGi U 0)).trans hE_normal)
  haveI hNcodA : ((X.Q 0).subgroupOf (X.L 0)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((oTwoPrime_le (X.Gi 0)).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hpCore := pCore_Lst_eq_E X hU
  let Ncod : Subgroup ↥(X.L 0) := (X.Q 0).subgroupOf (X.L 0)
  have hNcod : CFSG.pCore 2 ↥(X.L 0) = Ncod := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 (X.L 0), hN.pCoreOf_eq]
  obtain ⟨e⟩ := hN.quot
  obtain ⟨e0⟩ := nonempty_Lst_quot_mulEquiv_L_quot X hU hP
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpCore).trans
    (e0.trans ((QuotientGroup.quotientMulEquivOfEq hNcod).symm.trans e))⟩

theorem normGi_eq_Lst_sup_K {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    X.normGi U 0 = X.Lst U 0 ⊔ X.K := by
  have hLs_G0 : X.Lst U 0 ≤ X.Gi 0 :=
    (oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0)
  have hMS_le_L : X.normGi U 0 ⊓ X.edgeSylow 0 ≤ X.Lst U 0 := by
    have hP2 : IsPGroup 2 ↥(X.normGi U 0 ⊓ X.edgeSylow 0) :=
      (pCoreOf_isPGroup' (X.Gi 0 ⊓ X.Gi 1)).to_le
        (fun x hx => (Subgroup.mem_inf.mp hx).2)
    exact le_oTwoPrime_of_isPGroup (X := X.normGi U 0) hP2 (fun x hx => (Subgroup.mem_inf.mp hx).1)
  have hdecomp : X.normGi U 0 ⊓ X.Gi 1 = (X.normGi U 0 ⊓ X.edgeSylow 0) ⊔ X.K := by
    have hKA : X.K ≤ X.normGi U 0 ⊓ X.Gi 1 := le_inf (hU.K_le_normGi 0) (X.K_le_Gi 1)
    have hAGi : X.normGi U 0 ⊓ X.Gi 1 ≤ X.Gi 0 ⊓ X.Gi 1 :=
      inf_le_inf_right _ (X.normGi_le_Gi U 0)
    obtain ⟨h1, h2⟩ := X.pCoreOf_eq_inf_edgeSylow 0 hKA hAGi
    rw [← h2, h1, sup_comm, inf_assoc]
    rw [show X.Gi 1 ⊓ X.edgeSylow 0 = X.edgeSylow 0 from
      inf_eq_right.mpr (by simpa using (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right)]
  refine le_antisymm ?_ (sup_le (oTwoPrime_le (X.normGi U 0)) (hU.K_le_normGi 0))
  intro m hm
  obtain ⟨hmM, hmG⟩ := Subgroup.mem_inf.mp hm
  have hlt : Γ.Adj (X.vert 0) (m • X.vert 1) := by
    have h := (X.hyp.adj_smul m (X.vert 0) (X.vert 1)).mpr (X.adj 0)
    rwa [MulAction.mem_stabilizer_iff.mp hmG] at h
  obtain ⟨l, hlL, hlw⟩ := exists_Lst_smul_eq X hU hP
    (a := X.vert 1) (b := m • X.vert 1) (by simpa using X.adj 0) hlt
  have hlM : l ∈ X.normGi U 0 := (oTwoPrime_le (X.normGi U 0)) hlL
  have hlN : l ∈ Subgroup.normalizer (U : Set G) := (Subgroup.mem_inf.mp hlM).1
  have hlG : l ∈ X.Gi 0 := hLs_G0 hlL
  have hlm : l⁻¹ * m ∈ X.normGi U 0 ⊓ X.Gi 1 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).inv_mem hlN) hmM
    · exact (X.Gi 0).mul_mem ((X.Gi 0).inv_mem hlG) hmG
    · show (l⁻¹ * m) • X.vert 1 = X.vert 1
      calc (l⁻¹ * m) • X.vert 1 = l⁻¹ • (m • X.vert 1) := mul_smul _ _ _
        _ = l⁻¹ • (l • X.vert 1) := by rw [hlw]
        _ = X.vert 1 := inv_smul_smul _ _
  rw [hdecomp] at hlm
  have hmul : m = l * (l⁻¹ * m) := by group
  rw [hmul]
  exact (X.Lst U 0 ⊔ X.K).mul_mem (Subgroup.mem_sup_left hlL)
    (sup_le_sup_right hMS_le_L X.K hlm)

theorem isSylowTwoOf_skP_Lst {U : Subgroup G} (hU : X.IsSK U) :
    IsSylowTwoOf (X.skP U) (X.Lst U 0) := by
  have hP_M : IsSylowTwoOf (X.skP U) (X.normGi U 0) := isSylowTwoOf_skP_zero X hU
  have hP2 : IsPGroup 2 (X.skP U) := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  have hPL : X.skP U ≤ X.Lst U 0 :=
    le_oTwoPrime_of_isPGroup hP2 (inf_le_right : X.skP U ≤ X.normGi U 0)
  refine ⟨hPL, hP2, ?_⟩
  intro h2
  change 2 ∣ (X.skP U).relIndex (X.Lst U 0) at h2
  apply hP_M.2.2
  change 2 ∣ (X.skP U).relIndex (X.normGi U 0)
  rw [← Subgroup.relIndex_mul_relIndex (X.skP U) (X.Lst U 0) (X.normGi U 0) hPL
    (oTwoPrime_le (X.normGi U 0))]
  exact dvd_mul_of_dvd_left h2 _

theorem Lst_eq_Yst_sup_skP {U : Subgroup G} (hU : X.IsSK U) :
    X.Lst U 0 = X.Yst U 0 ⊔ X.skP U := by
  haveI : Finite ↥(X.Lst U 0) :=
    finite_of_le_stabilizer X.hyp
      ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0))
  have hSyl : IsSylowTwoOf (X.skP U) (X.Lst U 0) := isSylowTwoOf_skP_Lst X hU
  have hsup : CFSG.Quasithin.opResidual 2 (X.Lst U 0) ⊔ X.skP U = X.Lst U 0 :=
    CFSG.GroupTheory.opResidual_sup_eq_of_finite hSyl.1 hSyl.2.2
  have hYst : X.Yst U 0 = CFSG.Quasithin.opResidual 2 (X.Lst U 0) := by
    rw [Setup.Yst, CFSG.GroupTheory.pResidualOf_eq_opResidual_of_finite]
  rw [hYst, hsup]

theorem normGi_eq_Yst_sup_K_sup_skP {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    X.normGi U 0 = X.Yst U 0 ⊔ X.K ⊔ X.skP U := by
  rw [normGi_eq_Lst_sup_K X hU hP, Lst_eq_Yst_sup_skP X hU]
  ac_rfl

private theorem sylow_two_psl_sq_eq_one {f : ℕ} (hf : 1 ≤ f)
    (S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 f)))
    {u : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)}
    (hu : u ∈ (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 f)))) : u ^ 2 = 1 := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨eadd⟩ :=
    CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
      (F := GaloisField 2 f) (p := 2) hK S
  have h1 : (eadd.symm ⟨u, hu⟩) ^ 2 = 1 := by
    obtain ⟨x, hx⟩ : ∃ x : GaloisField 2 f, Multiplicative.ofAdd x = eadd.symm ⟨u, hu⟩ :=
      Multiplicative.ofAdd.surjective (eadd.symm ⟨u, hu⟩)
    rw [← hx]
    have h2 : (Multiplicative.ofAdd x) ^ 2 = Multiplicative.ofAdd (x + x) := by
      rw [pow_two]; rfl
    rw [h2]
    haveI : CharP (GaloisField 2 f) 2 := inferInstance
    rw [CharTwo.add_self_eq_zero, ofAdd_zero]
  have h3 : eadd ((eadd.symm ⟨u, hu⟩) ^ 2) = 1 := by rw [h1, map_one]
  rw [map_pow, MulEquiv.apply_symm_apply] at h3
  exact Subtype.ext_iff.mp h3

theorem sqClosure_skP_le_E {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    sqClosure (X.skP U) ≤ X.E U 0 := by
  have hP2 : IsPGroup 2 ↥(X.skP U) := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  have hP_le_Lst : X.skP U ≤ X.Lst U 0 :=
    le_oTwoPrime_of_isPGroup hP2 inf_le_right
  have hpCore := pCore_Lst_eq_E X hU
  let Q := oTwoQuot ↥(X.Lst U 0)
  let f : ↥(X.Lst U 0) →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥(X.Lst U 0))
  have himg2 : IsPGroup 2 ↥(((X.skP U).subgroupOf (X.Lst U 0)).map f) :=
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le_Lst).symm).map f
  obtain ⟨e⟩ := isL2Quot_Lst X hU hP
  have himg2' : IsPGroup 2 ↥((((X.skP U).subgroupOf (X.Lst U 0)).map f).map e.toMonoidHom) :=
    himg2.map e.toMonoidHom
  have hf : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
  obtain ⟨S, hS⟩ := himg2'.exists_le_sylow
  have hsq : ∀ v ∈ ((X.skP U).subgroupOf (X.Lst U 0)).map f, v ^ 2 = 1 := by
    intro v hv
    have hv' : e v ∈ (((X.skP U).subgroupOf (X.Lst U 0)).map f).map e.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
    have h2 : (e v) ^ 2 = 1 := sylow_two_psl_sq_eq_one hf S (hS hv')
    exact e.injective (by simpa using h2)
  rw [sqClosure, Subgroup.closure_le]
  rintro x ⟨a, haP, rfl⟩
  have hfa : f ⟨a, hP_le_Lst haP⟩ ∈ ((X.skP U).subgroupOf (X.Lst U 0)).map f :=
    Subgroup.mem_map.mpr ⟨⟨a, hP_le_Lst haP⟩, haP, rfl⟩
  have h2 : (f ⟨a, hP_le_Lst haP⟩) ^ 2 = 1 := hsq _ hfa
  have hmap : f ⟨a ^ 2, hP_le_Lst (pow_mem haP 2)⟩ = 1 := by
    have h1 : f ⟨a, hP_le_Lst haP⟩ ^ 2 = f ⟨a ^ 2, hP_le_Lst (pow_mem haP 2)⟩ := by
      rw [← map_pow]
      rfl
    rw [← h1]
    exact h2
  have hker : ⟨a ^ 2, hP_le_Lst (pow_mem haP 2)⟩ ∈ (X.E U 0).subgroupOf (X.Lst U 0) := by
    rw [← hpCore]
    exact (QuotientGroup.eq_one_iff _).mp hmap
  exact Subgroup.mem_subgroupOf.mp hker

theorem relIndex_E_skP {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) :
    (X.E U 0).relIndex (X.skP U) = 2 ^ X.n 0 := by
  haveI : Finite ↥(X.Lst U 0) :=
    finite_of_le_stabilizer X.hyp
      ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0))
  have hSyl : IsSylowTwoOf (X.skP U) (X.Lst U 0) := isSylowTwoOf_skP_Lst X hU
  have hpCore := pCore_Lst_eq_E X hU
  let Q := oTwoQuot ↥(X.Lst U 0)
  let f : ↥(X.Lst U 0) →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥(X.Lst U 0))
  let g : ↥(X.skP U) →* Q := f.comp (Subgroup.inclusion hSyl.1)
  have hg_ker : g.ker = (X.E U 0).subgroupOf (X.skP U) := by
    rw [show g = f.comp (Subgroup.inclusion hSyl.1) from rfl, ← MonoidHom.comap_ker]
    rw [show f.ker = CFSG.pCore 2 ↥(X.Lst U 0) from
      QuotientGroup.ker_mk' (N := CFSG.pCore 2 ↥(X.Lst U 0)), hpCore]
    exact Subgroup.comap_inclusion_subgroupOf hSyl.1 (X.E U 0)
  have hrange : g.range = ((X.skP U).subgroupOf (X.Lst U 0)).map f := by
    rw [show g = f.comp (Subgroup.inclusion hSyl.1) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range]
  have hSylQ : IsSylowTwoOf g.range ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hSyl.2.1.of_surjective g.rangeRestrict g.rangeRestrict_surjective
    · rw [CFSG.QuasithinUnique.index_subgroupOf_top]
      have hdvd : g.range.index ∣ (X.skP U).relIndex (X.Lst U 0) := by
        rw [hrange]
        exact Subgroup.index_map_dvd ((X.skP U).subgroupOf (X.Lst U 0))
          (QuotientGroup.mk'_surjective _)
      exact fun h2 => hSyl.2.2 (h2.trans hdvd)
  have hcard_range : Nat.card ↥g.range = 2 ^ X.n 0 := by
    rw [hSylQ.card_eq]
    obtain ⟨e⟩ := isL2Quot_Lst X hU hP
    have htwo : twoPart (⊤ : Subgroup Q) =
        twoPart (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
          (GaloisField 2 (X.n 0)))) := by
      rw [twoPart, twoPart, Subgroup.card_top, Subgroup.card_top, Nat.card_congr e.toEquiv]
    rw [htwo]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hf : 1 ≤ X.n 0 := (X.hyp.valency (X.vert 0)).1
    obtain ⟨S⟩ := Sylow.nonempty (p := 2)
      (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (X.n 0)))
    have hS : Nat.card (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 (X.n 0)))) = 2 ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup
          (Fin 2) (GaloisField 2 (X.n 0)))).factorization 2 :=
      Sylow.card_eq_multiplicity S
    have hU2 : Nat.card (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 (X.n 0)))) = 2 ^ X.n 0 := psl2_sylow_two_card hf S
    rw [twoPart, Subgroup.card_top, ← hS, hU2]
  have hrel : (X.E U 0).relIndex (X.skP U) = Nat.card ↥g.range := by
    have h1 : g.ker.relIndex ⊤ = Nat.card ↥g.range := by
      rw [Subgroup.relIndex_ker, ← MonoidHom.range_eq_map]
    rw [hg_ker, Subgroup.relIndex_top_right] at h1
    exact h1
  rw [hrel, hcard_range]

theorem eq_skP_of_K_invariant_zero {U A : Subgroup G}
    (hE : X.E U 0 ≤ A) (hA : A ≤ X.skP U)
    (hK : X.K ≤ Subgroup.normalizer (A : Set G)) (hne : ¬ A ≤ X.E U 0) :
    A = X.skP U := by
  have hPE : X.Q 0 ⊓ X.skP U ≤ X.E U 0 := by
    intro x hx
    obtain ⟨hxQ, hxP⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxQ, (Subgroup.mem_inf.mp hxP).2.1⟩
  have hnot : ¬ A ≤ X.Q 0 := fun h => hne (le_trans (le_inf h hA) hPE)
  have hAedge : A ≤ X.edgeSylow 0 :=
    hA.trans (inf_le_left.trans (X.Q_le_edgeSylow_right 1))
  have hsup : A ⊔ X.Q 0 = X.edgeSylow 0 :=
    X.sup_Q_eq_edgeSylow_of_left_gen 0 (inf_le_left.trans hK) hAedge hnot
  have hPle : X.skP U ≤ A ⊔ X.Q 0 := by
    rw [hsup]
    exact inf_le_left.trans (X.Q_le_edgeSylow_right 1)
  have hS0G0 : X.edgeSylow 0 ≤ X.Gi 0 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 0 ⊓ X.Gi 1)).trans inf_le_left
  have hAnorm : A ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hAedge.trans (hS0G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hcoe : (↑(X.Q 0 ⊔ A) : Set G) = (X.Q 0 : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (X.Q 0) A hAnorm
  refine le_antisymm hA ?_
  intro x hxP
  have hxsup : x ∈ X.Q 0 ⊔ A := by rw [sup_comm]; exact hPle hxP
  have hx' : x ∈ (X.Q 0 : Set G) * (A : Set G) := hcoe ▸ hxsup
  obtain ⟨q, hq, a, ha, hqa⟩ := hx'
  have hqP : q ∈ X.skP U := by
    have hqeq : q = x * a⁻¹ := by rw [← hqa]; group
    rw [hqeq]
    exact (X.skP U).mul_mem hxP ((X.skP U).inv_mem (hA ha))
  have hqE : q ∈ X.E U 0 := hPE (Subgroup.mem_inf.mpr ⟨hq, hqP⟩)
  rw [← hqa]
  exact A.mul_mem (hE hqE) ha

theorem eq_skP_of_K_invariant_two {U A : Subgroup G} (hU : X.IsSK U)
    (hE : X.E U 2 ≤ A) (hA : A ≤ X.skP U)
    (hK : X.K ≤ Subgroup.normalizer (A : Set G)) (hne : ¬ A ≤ X.E U 2) :
    A = X.skP U := by
  obtain ⟨t, ht, ht02, -, -⟩ := IsSK.exists_t X hU
  have htM1 : t ∈ X.normGi U 1 := ht.1
  have htK : t ∈ Subgroup.normalizer (X.K : Set G) := ht.2
  have hE0 : X.E U 0 ≤ conjSub t⁻¹ A := by
    have hEeq : X.E U 0 = conjSub t⁻¹ (X.E U 2) := by
      rw [← IsSK.conjSub_E_zero X htM1 ht02, conjSub_conjSub_inv]
    rw [hEeq]
    exact conjSub_mono t⁻¹ hE
  have hA0 : conjSub t⁻¹ A ≤ X.skP U := by
    have hPeq : X.skP U = conjSub t⁻¹ (X.skP U) := by
      conv_rhs => rw [← IsSK.conjSub_skP X htM1 ht02]
      rw [conjSub_conjSub_inv]
    rw [hPeq]
    exact conjSub_mono t⁻¹ hA
  have hK0 : X.K ≤ Subgroup.normalizer (conjSub t⁻¹ A : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub k (conjSub t⁻¹ A) = conjSub t⁻¹ A
    rw [← conjSub_mul k t⁻¹ A]
    have hkt : t * k * t⁻¹ ∈ X.K := (Subgroup.mem_normalizer_iff.mp htK k).mp hk
    have hfix : conjSub (t * k * t⁻¹) A = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK hkt)
    rw [show k * t⁻¹ = t⁻¹ * (t * k * t⁻¹) by group, conjSub_mul, hfix]
  have hne0 : ¬ conjSub t⁻¹ A ≤ X.E U 0 := by
    intro h
    apply hne
    have h1 := conjSub_mono t h
    rwa [conjSub_inv_conjSub, IsSK.conjSub_E_zero X htM1 ht02] at h1
  have hzero := eq_skP_of_K_invariant_zero X hE0 hA0 hK0 hne0
  have h1 := congrArg (conjSub t) hzero
  rwa [conjSub_inv_conjSub, IsSK.conjSub_skP X htM1 ht02] at h1

private theorem sq_mem_inf_centralizer_sup_E {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0)
    (hCE : ¬ X.Lst U 0 ⊓ Subgroup.centralizer (X.E U 0 : Set G) ≤ X.E U 0)
    {x : G} (hx : x ∈ X.Lst U 0) :
    x ^ 2 ∈ (X.Lst U 0 ⊓ Subgroup.centralizer (X.E U 0 : Set G)) ⊔ X.E U 0 := by
  let L := X.Lst U 0
  let E := X.E U 0
  let C : Subgroup G := L ⊓ Subgroup.centralizer (E : Set G)
  haveI hLfin : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L)
    ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0))
  have hEeq : pCoreOf 2 L = E := pCoreOf_Lst_eq_E X hU
  have hEpc : CFSG.pCore 2 ↥L = E.subgroupOf L := by
    show CFSG.pCore 2 ↥(X.Lst U 0) = (X.E U 0).subgroupOf (X.Lst U 0)
    exact pCore_Lst_eq_E X hU
  have hE_normal : L ≤ Subgroup.normalizer (E : Set G) :=
    hEeq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hC_normal : L ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conjSub l (L ⊓ Subgroup.centralizer (E : Set G)) =
      L ⊓ Subgroup.centralizer (E : Set G)
    have hEl : conjSub l E = E := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hE_normal hl)
    rw [conjSub_inf, conjSub_eq_of_mem hl, ← conjSub_centralizer, hEl]
  let Q := oTwoQuot ↥L
  let π : ↥L →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let K : Subgroup Q := (C.subgroupOf L).map π
  have hCsub_normal : (C.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hC_normal
  have hKnormal : K.Normal := hCsub_normal.map π (QuotientGroup.mk'_surjective _)
  have hKne : K ≠ ⊥ := by
    intro hbot
    apply hCE
    intro x hx
    have hxL : x ∈ L := (Subgroup.mem_inf.mp hx).1
    have hxK : π ⟨x, hxL⟩ ∈ K :=
      Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot] at hxK
    have hx1 : π ⟨x, hxL⟩ = 1 := Subgroup.mem_bot.mp hxK
    have hxker : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      have h2 : (⟨x, hxL⟩ : ↥L) ∈ π.ker := MonoidHom.mem_ker.mpr hx1
      rwa [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _] at h2
    rw [pCore_Lst_eq_E X hU] at hxker
    exact Subgroup.mem_subgroupOf.mp hxker
  have hmemCE : ∀ y : ↥L, π y ∈ K → (y : G) ∈ C ⊔ E := by
    intro y hyK
    obtain ⟨c, hcC, hc_eq⟩ := Subgroup.mem_map.mp hyK
    have hker : c⁻¹ * y ∈ CFSG.pCore 2 ↥L := by
      have h1 : π (c⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hc_eq]
        simp
      have h2 : (c⁻¹ * y) ∈ π.ker := MonoidHom.mem_ker.mpr h1
      rwa [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _] at h2
    have hE_mem : ((c⁻¹ * y : ↥L) : G) ∈ E := by
      rw [hEpc] at hker
      exact Subgroup.mem_subgroupOf.mp hker
    have hy_eq : (y : G) = (c : G) * ((c : G)⁻¹ * (y : G)) := by group
    rw [hy_eq]
    exact (C ⊔ E).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hcC))
      (Subgroup.mem_sup_right (by simpa using hE_mem))
  have hxL : x ∈ L := hx
  have hx2sup : x ^ 2 ∈ C ⊔ E := by
    have hn : X.n 0 = 1 ∨ 2 ≤ X.n 0 := by
      rcases Nat.lt_or_eq_of_le (X.hyp.valency (X.vert 0)).1 with h | h
      · exact Or.inr h
      · exact Or.inl h.symm
    rcases hn with hn1 | hn2
    ·
      obtain ⟨e3⟩ : Nonempty (Q ≃* Equiv.Perm (Fin 3)) :=
        CFSG.Quasithin.isL2Quot_one_iff_perm3.mp (by
          have h := isL2Quot_Lst X hU hP
          rwa [show X.n 0 = 1 from hn1] at h)
      let K' : Subgroup (Equiv.Perm (Fin 3)) := K.map e3.toMonoidHom
      have hK'normal : K'.Normal := hKnormal.map e3.toMonoidHom e3.surjective
      have hK'ne : K' ≠ ⊥ := by
        intro hbot
        apply hKne
        rw [eq_bot_iff]
        intro k hk
        have hmem : e3 k ∈ K' := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
        rw [hbot] at hmem
        exact e3.injective (by simpa using hmem)
      haveI := hK'normal
      have hsqK' : ∀ y : Equiv.Perm (Fin 3), y ^ 2 ∈ K' := fun y =>
        F53.normal_ge_alt3 K' hK'ne
          (Subgroup.sq_mem_of_index_two alternatingGroup.index_eq_two y)
      have hsqK : (π ⟨x, hxL⟩) ^ 2 ∈ K := by
        have hmem : e3 ((π ⟨x, hxL⟩) ^ 2) ∈ K' := by
          rw [map_pow]
          exact hsqK' _
        obtain ⟨k, hkK, hk_eq⟩ := Subgroup.mem_map.mp hmem
        have hk_eq' : k = (π ⟨x, hxL⟩) ^ 2 := by
          apply e3.injective
          rw [map_pow]
          simpa using hk_eq
        rw [← hk_eq']
        exact hkK
      have h2x : ((⟨x, hxL⟩ ^ 2 : ↥L) : G) = x ^ 2 := rfl
      rw [← h2x]
      exact hmemCE (⟨x, hxL⟩ ^ 2) (by rw [map_pow]; exact hsqK)
    ·
      have hQsimple : IsSimpleGroup Q := by
        obtain ⟨e⟩ := isL2Quot_Lst X hU hP
        have h4 : 4 ≤ Nat.card (GaloisField 2 (X.n 0)) := by
          rw [GaloisField.card 2 (X.n 0) (by omega)]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ X.n 0 := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact (MulEquiv.isSimpleGroup_congr e).mpr
          (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)
      have hKtop : K = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
        · exact absurd h hKne
        · exact h
      have hxK : π ⟨x, hxL⟩ ∈ K := by
        rw [hKtop]
        exact Subgroup.mem_top _
      exact (C ⊔ E).pow_mem (hmemCE ⟨x, hxL⟩ hxK) 2
  exact hx2sup

private theorem exists_two_pow_mem_of_sq_mem_sup {C E : Subgroup G}
    (hCE : C ≤ Subgroup.centralizer (E : Set G))
    (hCnorm : C ≤ Subgroup.normalizer (E : Set G)) (hE2 : IsPGroup 2 E) {x : G}
    (hx : x ^ 2 ∈ C ⊔ E) : ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
  have hcoe : (↑(E ⊔ C) : Set G) = (E : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (E) C hCnorm
  have hx2' : x ^ 2 ∈ (E : Set G) * (C : Set G) := by
    rw [← hcoe, sup_comm]
    exact hx
  obtain ⟨e, heE, c, hcC, hec⟩ := hx2'
  have hcCent : c ∈ Subgroup.centralizer (E : Set G) := hCE hcC
  have hcomm : Commute e c := Subgroup.mem_centralizer_iff.mp hcCent e heE
  obtain ⟨k, hk⟩ := hE2 ⟨e, heE⟩
  have hk' : e ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k + 1, ?_⟩
  have hEq : x ^ 2 ^ (k + 1) = c ^ 2 ^ k := by
    calc x ^ 2 ^ (k + 1) = (x ^ 2) ^ 2 ^ k := by rw [pow_succ', pow_mul]
      _ = (e * c) ^ 2 ^ k := by rw [← hec]
      _ = e ^ 2 ^ k * c ^ 2 ^ k := hcomm.mul_pow _
      _ = c ^ 2 ^ k := by rw [hk', one_mul]
  rw [hEq]
  exact C.pow_mem hcC _

theorem charTwo_Lst {U : Subgroup G} (hU : X.IsSK U)
    (hP : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    CharTwo (X.Lst U 0) := by
  let L := X.Lst U 0
  let E := X.E U 0
  let Y := X.Yst U 0
  let C : Subgroup G := L ⊓ Subgroup.centralizer (E : Set G)
  haveI hLfin : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L)
    ((oTwoPrime_le (X.normGi U 0)).trans (X.normGi_le_Gi U 0))
  have hEeq : pCoreOf 2 L = E := pCoreOf_Lst_eq_E X hU
  have hE2 : IsPGroup 2 E := hEeq ▸ pCoreOf_isPGroup' L
  have hE_normal : L ≤ Subgroup.normalizer (E : Set G) :=
    hEeq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  change L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L
  rw [hEeq]
  by_contra hcon
  have hpow : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
    intro x hxL
    have hx2sup : x ^ 2 ∈ C ⊔ E := by
      simpa only [C, L, E] using sq_mem_inf_centralizer_sup_E X hU hP hcon hxL
    exact exists_two_pow_mem_of_sq_mem_sup (inf_le_right : C ≤ Subgroup.centralizer (E : Set G))
      (inf_le_left.trans hE_normal) hE2 hx2sup
  have hY_le_C : Y ≤ C := by
    have hYop : Y = opResidual 2 L := by
      show pResidualOf 2 L = opResidual 2 L
      exact CFSG.GroupTheory.pResidualOf_eq_opResidual_of_finite
    rw [hYop]
    exact opResidual_le_of_pow_mem hpow
  have hVbot : ⁅E, Y⁆ = ⊥ := by
    have h1 : Y ≤ Subgroup.centralizer (E : Set G) := hY_le_C.trans inf_le_right
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
  exact hV hVbot

theorem skP_ne_Q_one {U : Subgroup G} (hU : X.IsSKMax U)
    (hP : X.skP U ≠ ⊥ ∨ 2 ≤ X.n 0) (hV : ⁅X.E U 0, X.Yst U 0⁆ ≠ ⊥) :
    X.skP U ≠ X.Q 1 := by
  intro hPeq
  have hP' : ¬ X.skP U ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    X.not_skP_le_Q_zero_or_of_isSKMax hU hP
  have hchar : CharTwo (X.Lst U 0) := charTwo_Lst X hU.1 hP' hV
  have hquot : IsL2Quot (X.n 0) (oTwoQuot ↥(X.Lst U 0)) := isL2Quot_Lst X hU.1 hP'
  have hLst_le_M0 : X.Lst U 0 ≤ X.normGi U 0 := oTwoPrime_le _
  have hPL : X.skP U ≤ X.Lst U 0 :=
    le_oTwoPrime_of_isPGroup ((pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left) inf_le_right
  have hnc : NoCharNormal (X.Q 1) (X.Lst U 0) := by
    rw [← hPeq]
    exact IsSKMax.noCharNormal_of_le X hU hPL hLst_le_M0
      (normGi_eq_Lst_sup_K X hU.1 hP')
  have hT : IsSylowTwoOf (X.Q 1) (X.Lst U 0) := by
    rw [← hPeq]
    exact isSylowTwoOf_skP_Lst X hU.1
  have hWtr : ∀ a b : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) b →
      ∃ w ∈ X.Lst U 0, w • a = b :=
    fun a b ha hb => exists_Lst_smul_eq X hU.1 hP' ha hb
  obtain ⟨x, hxG1, hxodd, hxtr⟩ := X.hyp.exists_odd_transitive_gen (X.vert 1)
  have hxQ : x ∈ Subgroup.normalizer (X.Q 1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1) hxG1
  exact lemmaR_L2 X.hyp (α := X.vert 1) (β := X.vert 0) (X.adj 0).symm
    (X.hyp.valency (X.vert 0)).1
    (hLst_le_M0.trans (X.normGi_le_Gi U 0)) hWtr hchar hquot hT
    (X.Q_le_Gi 1) hnc hxG1 hxQ hxodd hxtr

private theorem exists_lift_of_fixed_order_two {G : Type*} [Group G]
    {P N : Subgroup G} [hNnormal : (P.subgroupOf N).Normal] {t : G}
    (α : Subgroup.zpowers t →* MulAut ↥N)
    (hα : ∀ (a : Subgroup.zpowers t) (n : ↥N),
      ((α a n : ↥N) : G) = (a : G) * (n : G) * (a : G)⁻¹)
    (β : Subgroup.zpowers t →* MulAut (↥N ⧸ P.subgroupOf N))
    (hβ : ∀ (a : Subgroup.zpowers t) (n : ↥N),
      β a (QuotientGroup.mk n) = QuotientGroup.mk (α a n))
    {w : ↥N ⧸ P.subgroupOf N}
    (hwfix : ∀ a : Subgroup.zpowers t, β a w = w) (hworder : orderOf w = 2) :
    ∃ n : ↥N, (n : G) ∉ P ∧ (n : G) ^ 2 ∈ P ∧ ⁅t, (n : G)⁆ ∈ P ∧
      QuotientGroup.mk n = w := by
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_surjective w
  have hnP : (n : G) ∉ P := by
    intro hnP'
    have h1 : QuotientGroup.mk (s := P.subgroupOf N) n = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hnP'
    rw [hn_eq] at h1
    have h2 : orderOf w = 1 := by
      rw [h1]
      simp
    omega
  have hn2P : (n : G) ^ 2 ∈ P := by
    have h1 : (QuotientGroup.mk (s := P.subgroupOf N) n) ^ 2 = 1 := by
      rw [hn_eq]
      exact orderOf_dvd_iff_pow_eq_one.mp (hworder.symm ▸ dvd_refl 2)
    have h2 : QuotientGroup.mk (s := P.subgroupOf N) (n ^ 2) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h1
    rw [QuotientGroup.eq_one_iff] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hcommP : ⁅t, (n : G)⁆ ∈ P := by
    have hfixA' : QuotientGroup.mk (s := P.subgroupOf N)
        (α ⟨t, Subgroup.mem_zpowers t⟩ n) =
        QuotientGroup.mk (s := P.subgroupOf N) n := by
      rw [← hβ ⟨t, Subgroup.mem_zpowers t⟩ n, hn_eq]
      exact hwfix _
    have h1 : QuotientGroup.mk (s := P.subgroupOf N)
        (α ⟨t, Subgroup.mem_zpowers t⟩ n * n⁻¹) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hfixA']
      simp
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : (((α ⟨t, Subgroup.mem_zpowers t⟩ n * n⁻¹ : ↥N)) : G) ∈ P :=
      Subgroup.mem_subgroupOf.mp h1
    have hcomm : ⁅t, (n : G)⁆ =
        ((α ⟨t, Subgroup.mem_zpowers t⟩ n : ↥N) : G) * (n : G)⁻¹ := by
      rw [hα, commutatorElement_def]
    rwa [hcomm]
  exact ⟨n, hnP, hn2P, hcommP, hn_eq⟩

theorem exists_t' {U : Subgroup G} (hU : X.IsSK U)
    {t : G} (ht : t ∈ X.normGi U 1) (ht2 : t ^ 2 ∈ X.skP U) (hlt : X.skP U ≠ X.Q 1) :
    ∃ t' : G, t' ∈ X.Q 1 ∧ t' ∉ X.normGi U 0 ∧
      t' ∈ Subgroup.normalizer (X.skP U : Set G) ∧ t' ^ 2 ∈ X.skP U ∧ ⁅t, t'⁆ ∈ X.skP U := by
  let P := X.skP U
  let N : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ X.Q 1
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  have hQ1_2 : IsPGroup 2 (X.Q 1) := pCoreOf_isPGroup' (X.Gi 1)
  have hPleQ1 : P ≤ X.Q 1 := inf_le_left
  have hPleN : P ≤ N := le_inf Subgroup.le_normalizer hPleQ1
  have hPN : P < N := by
    haveI : Finite ↥(X.Q 1) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 1)
    have hlt' : P < X.Q 1 := lt_of_le_of_ne hPleQ1 hlt
    have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) (P := X.Q 1) (S := P)
      hQ1_2 hlt'
    simpa [N, inf_comm] using h
  have htG1 : t ∈ X.Gi 1 := ht.2
  have htQ1 : t ∈ Subgroup.normalizer (X.Q 1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1) htG1
  have htP : t ∈ Subgroup.normalizer (P : Set G) := by
    have hA := X.normGi_zero_inf_one_normal_in_one hU ht
    have hP_eq : P = pCoreOf 2 (X.normGi U 0 ⊓ X.Gi 1) := skP_eq_pCoreOf X hU
    rw [hP_eq]
    exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _) hA
  have htN : t ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr
        ⟨Subgroup.le_normalizer (H := Subgroup.normalizer (P : Set G)) htP, htQ1⟩)
  obtain ⟨k, hk⟩ := hP2 ⟨t ^ 2, ht2⟩
  have hk' : (t ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have htpow : t ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul]
    exact hk'
  let A : Subgroup G := Subgroup.zpowers t
  have hA2 : IsPGroup 2 A := isPGroup_zpowers_of_pow_two htpow
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := Subgroup.zpowers_le.mpr htN
  let α : A →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom (H := N)).comp (Subgroup.inclusion hAN)
  have hPNnormal : (P.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left
  have hPNinv : ∀ a : A, ∀ n ∈ P.subgroupOf N, α a n ∈ P.subgroupOf N := by
    intro a n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have ha : (a : G) ∈ Subgroup.normalizer (P : Set G) :=
      (Subgroup.zpowers_le.mpr htP) a.2
    have hconj : (a : G) * (n : G) * (a : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp ha (n : G)).mp hn
    have hval : ((α a n : ↥N) : G) = (a : G) * (n : G) * (a : G)⁻¹ := by
      simp [α]
    rwa [hval]
  let Q := ↥N ⧸ P.subgroupOf N
  let β : A →* MulAut Q :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (P.subgroupOf N) hPNinv
  let : MulDistribMulAction A Q := MulDistribMulAction.compHom Q β
  have hN2 : IsPGroup 2 N := hQ1_2.to_le inf_le_right
  have hQ2 : IsPGroup 2 Q :=
    hN2.of_surjective (QuotientGroup.mk' (P.subgroupOf N)) (QuotientGroup.mk'_surjective _)
  haveI hNfin : Finite ↥N :=
    finite_of_le_stabilizer X.hyp (H := N) (inf_le_right.trans (X.Q_le_Gi 1))
  haveI hQfin : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' (P.subgroupOf N)) (QuotientGroup.mk'_surjective _)
  have hQne : Nontrivial Q := by
    obtain ⟨x, hxN, hxP⟩ := SetLike.exists_of_lt hPN
    refine ⟨⟨QuotientGroup.mk (s := P.subgroupOf N) ⟨x, hxN⟩, 1, ?_⟩⟩
    intro h
    apply hxP
    have hx1 : QuotientGroup.mk (s := P.subgroupOf N) ⟨x, hxN⟩ = 1 := h
    rw [QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_subgroupOf.mp hx1
  haveI : Nontrivial Q := hQne
  obtain ⟨w, hworder, hwfix⟩ :=
    CFSG.GroupTheory.exists_orderOf_eq_forall_smul_eq (A := A) (p := 2) hA2 hQ2
  have hwfixβ : ∀ a : Subgroup.zpowers t, β a w = w := fun a => hwfix a
  obtain ⟨n, hnP, hn2P, hcommP, -⟩ :=
    exists_lift_of_fixed_order_two α (by intro a n; simp [α]) β
      (fun a n => CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk α
        (P.subgroupOf N) hPNinv a n) hwfixβ hworder
  refine ⟨(n : G), ?_, ?_, ?_, ?_, hcommP⟩
  · exact (inf_le_right : N ≤ X.Q 1) n.2
  · intro hnm
    exact hnP (Subgroup.mem_inf.mpr ⟨(inf_le_right : N ≤ X.Q 1) n.2, hnm⟩)
  · exact (inf_le_left : N ≤ Subgroup.normalizer (P : Set G)) n.2
  · exact hn2P

end Setup

end CFSG.Quasithin.St84
