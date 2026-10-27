module

public import CFSG.Quasithin.Recognition.St84.Sec5Tree
public import CFSG.Quasithin.Recognition.St84.Sec5GoldschmidtSmall

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

theorem J_add (Y : Setup Γ G) (m i : ℤ) :
    Y.J (i + 2 * m) = (Y.J i).map (MulAut.conj (Y.τ ^ m)).toMonoidHom := by
  have hτN : Y.τ ^ m ∈ Y.N := Subgroup.zpow_mem Y.N Y.τ_norm m
  have hconjK : conjSub (Y.τ ^ m) Y.K = Y.K := by
    ext x
    rw [mem_conjSub]
    exact (Subgroup.mem_normalizer_iff''.mp hτN x).symm
  have hN : conjSub (Y.τ ^ m) Y.N = Y.N := by
    show conjSub (Y.τ ^ m) (Subgroup.normalizer (Y.K : Set G)) =
      Subgroup.normalizer (Y.K : Set G)
    rw [← conjSub_normalizer, hconjK]
  show oTwoPrime (Y.N ⊓ Y.Gi (i + 2 * m)) =
    (oTwoPrime (Y.N ⊓ Y.Gi i)).map (MulAut.conj (Y.τ ^ m)).toMonoidHom
  calc oTwoPrime (Y.N ⊓ Y.Gi (i + 2 * m))
      = oTwoPrime (Y.N ⊓ conjSub (Y.τ ^ m) (Y.Gi i)) := by rw [Y.Gi_add]
    _ = oTwoPrime (conjSub (Y.τ ^ m) (Y.N ⊓ Y.Gi i)) := by rw [conjSub_inf, hN]
    _ = conjSub (Y.τ ^ m) (oTwoPrime (Y.N ⊓ Y.Gi i)) := (conjSub_oTwoPrime _ _).symm
    _ = (oTwoPrime (Y.N ⊓ Y.Gi i)).map (MulAut.conj (Y.τ ^ m)).toMonoidHom := rfl

private theorem card_L_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card ↥(Y.L 1) = 6 * Nat.card ↥(Y.Q 1) := by
  have hN : IsLocL2 Γ G (Y.vert 1) (Y.n 1) (Y.L 1) := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
  have hquot := hN.quot.some
  have hcardq : Nat.card (↥(Y.L 1) ⧸ CFSG.pCore 2 ↥(Y.L 1)) = 6 := by
    rw [Nat.card_congr hquot.toEquiv, H.n_one, card_psl_two_gf2_one]
  have hindex : (CFSG.pCore 2 ↥(Y.L 1)).index = 6 := by
    rw [← hcardq]
    exact Subgroup.index_eq_card _
  have hmul := Subgroup.index_mul_card (CFSG.pCore 2 ↥(Y.L 1))
  rw [hindex] at hmul
  have hpceq : CFSG.Open.pCoreOf 2 (Y.L 1) = Y.Q 1 := hN.pCoreOf_eq
  have hcard : Nat.card ↥(CFSG.Open.pCoreOf 2 (Y.L 1)) =
      Nat.card ↥(CFSG.pCore 2 ↥(Y.L 1)) :=
    Subgroup.card_map_of_injective Subtype.coe_injective
  rw [hpceq] at hcard
  rw [← hcard] at hmul
  exact hmul.symm

theorem J_le_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.J 1 ≤ Subgroup.centralizer (Y.K : Set G) := by
  have hKQ := Y.K_inf_Q_eq_bot 1
  rw [Setup.J, oTwoPrime, Subgroup.closure_le]
  rintro x ⟨hx, n, hxn⟩
  change ∀ k ∈ (Y.K : Set G), k * x = x * k
  intro k hk
  have hxN : x ∈ Subgroup.normalizer (Y.K : Set G) := hx.1
  have hxG : x ∈ Y.Gi 1 := hx.2
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxn)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hxL : x ∈ Y.L 1 :=
    le_oTwoPrime_of_isPGroup (P := Subgroup.zpowers x) hzp (Subgroup.zpowers_le.mpr hxG)
      (Subgroup.mem_zpowers x)
  have hxk : x * k * x⁻¹ ∈ Y.K :=
    (Subgroup.mem_normalizer_iff.mp hxN k).mp hk
  have hxk' : x * k⁻¹ * x⁻¹ ∈ Y.K := by
    have h := Y.K.inv_mem hxk
    rw [mul_assoc]
    simpa using h
  have hcommK : ⁅k, x⁆ ∈ Y.K := by
    rw [commutatorElement_def]
    have e : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
    rw [e]
    exact Y.K.mul_mem hk hxk'
  have hcommQ : ⁅k, x⁆ ∈ Y.Q 1 :=
    comm_K_L_one_le Y H (Subgroup.commutator_mem_commutator hk hxL)
  have hcomm1 : ⁅k, x⁆ = 1 := by
    have : ⁅k, x⁆ ∈ (⊥ : Subgroup G) := hKQ ▸ Subgroup.mem_inf.mpr ⟨hcommK, hcommQ⟩
    simpa using this
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1

private theorem J_le_L_and_C (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.J 1 ≤ Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) := by
  refine le_inf ?_ (J_le_centralizer Y H)
  show oTwoPrime (Y.N ⊓ Y.Gi 1) ≤ oTwoPrime (Y.Gi 1)
  exact oTwoPrime_mono inf_le_right

theorem S_le_L_one (Y : Setup Γ G) : Y.S ≤ Y.L 1 := by
  have h := (Y.isSylowTwoOf_edgeSylow_L_succ 0).1
  simpa [Y.edgeSylow_zero] using h

private theorem S_relIndex_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Q 1).relIndex Y.S = 2 := by
  simpa [Y.edgeSylow_zero, H.n_one] using Y.relIndex_Q_succ_edgeSylow 0

private theorem exists_mem_centralizer_coset_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {X : Subgroup G} (hQX : Y.Q 1 ≤ X) (hXL : X ≤ Y.L 1)
    (hKX : Y.K ≤ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ X) :
    ∃ c ∈ X ⊓ Subgroup.centralizer (Y.K : Set G), c⁻¹ * x ∈ Y.Q 1 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hXfin : Finite ↥X :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := X) (hXL.trans (Y.L_le_Gi 1))
  haveI hKfin : Finite ↥(Y.K) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.K) (Y.K_le_Gi 1)
  haveI hKnorm : Y.K.Normalizes X := ⟨hKX⟩
  let N : Subgroup ↥X := (Y.Q 1).subgroupOf X
  have hLN : X ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    hXL.trans ((Y.L_le_Gi 1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)))
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hLN
  haveI : N.Normal := hNnormal
  have hNinv : CFSG.IsInvariant ↥Y.K ↥X N := by
    refine ⟨fun k y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) (Y.K_le_Gi 1 k.2))
        (y : G)).mp hy
    · rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hy' : (k : G) * (y : G) * (k : G)⁻¹ ∈ Y.Q 1 := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hy
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) (Y.K_le_Gi 1 k.2))
        (y : G)).mpr hy'
  haveI hQfin : Finite ↥(Y.Q 1) :=
    Finite.of_injective (Subgroup.inclusion (Y.Q_le_Gi 1)) (Subgroup.inclusion_injective _)
  have hNcard : Nat.card ↥N = Nat.card ↥(Y.Q 1) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv
  haveI hNfin : Finite ↥N :=
    Finite.of_injective (Subgroup.subtype N) (Subgroup.subtype_injective N)
  have hNp : IsPGroup 2 ↥N := by
    have h := pCoreOf_isPGroup' (Y.Gi 1)
    rw [IsPGroup.iff_card] at h ⊢
    obtain ⟨a, ha⟩ := h
    exact ⟨a, by rw [hNcard, ha]⟩
  haveI hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNnil : Group.IsNilpotent ↥N := IsPGroup.isNilpotent (p := 2) hNp
  have hNsolv : Group.IsSolvable ↥N := inferInstance
  have hKodd : Odd (Nat.card ↥Y.K) := Y.odd_card_K
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup' (Y.Gi 1)).exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥Y.K) (Nat.card ↥N) := by
    rw [hNcard, ha]
    exact (hKodd.coprime_two_right).pow_right a
  let x' : ↥X := ⟨x, hx⟩
  obtain ⟨c, hc, hcn⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed N hNinv hNsolv hcop x'
    (by
      intro k
      rw [Subgroup.mem_subgroupOf]
      have hkm : ((k • x' : ↥X) : G) = (k : G) * (x : G) * (k : G)⁻¹ :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := Y.K) (K := X) k x'
      show (x : G)⁻¹ * (((k • x' : ↥X) : G)) ∈ Y.Q 1
      rw [hkm]
      have hcomm : ⁅(k : G), (x : G)⁆ ∈ Y.Q 1 :=
        comm_K_L_one_le Y H (Subgroup.commutator_mem_commutator k.2 (hXL hx))
      have heq : (x : G)⁻¹ * ((k : G) * (x : G) * (k : G)⁻¹) =
          (x : G)⁻¹ * ⁅(k : G), (x : G)⁆ * (x : G) := by
        rw [commutatorElement_def]; group
      rw [heq]
      exact (Subgroup.mem_normalizer_iff''.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)
          (Y.L_le_Gi 1 (hXL hx)))
        ⁅(k : G), (x : G)⁆).mp hcomm)
  have hcC : (c : G) ∈ Subgroup.centralizer (Y.K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hfix : (⟨k, hk⟩ : ↥Y.K) • c = c := hc ⟨k, hk⟩
    have hval : ((⟨k, hk⟩ : ↥Y.K) • c : ↥X) =
        ⟨(k : G) * (c : G) * (k : G)⁻¹, by
          exact (Subgroup.mem_normalizer_iff.mp (hKX hk) (c : G)).mp c.2⟩ := rfl
    have h5 := congrArg (fun z : ↥X => (z : G)) hfix
    simp only [hval] at h5
    calc k * (c : G) = (k * (c : G) * k⁻¹) * k := by group
      _ = (c : G) * k := by rw [h5]
  refine ⟨(c : G), ⟨c.2, hcC⟩, ?_⟩
  show (c : G)⁻¹ * x ∈ Y.Q 1
  exact Subgroup.mem_subgroupOf.mp hcn

private theorem inf_centralizer_sup_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {X : Subgroup G} (hQX : Y.Q 1 ≤ X) (hXL : X ≤ Y.L 1)
    (hKX : Y.K ≤ Subgroup.normalizer (X : Set G)) :
    X ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Y.Q 1 = X := by
  refine le_antisymm (sup_le inf_le_left hQX) fun x hx => ?_
  obtain ⟨c, hc, hcx⟩ := exists_mem_centralizer_coset_Q_one Y H hQX hXL hKX hx
  rw [show x = c * (c⁻¹ * x) by group]
  exact Subgroup.mul_mem_sup hc hcx

private theorem S_eq_centralizer_sup_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Y.Q 1 = Y.S :=
  inf_centralizer_sup_Q_one Y H (Y.Q_le_edgeSylow_right 1) (S_le_L_one Y)
    (Y.K_le_inf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1)))

private theorem Qs_one_eq_inf (Y : Setup Γ G) {X : Subgroup G} (hQX : Y.Q 1 ≤ X) :
    Y.Qs 1 = Y.Q 1 ⊓ (X ⊓ Subgroup.centralizer (Y.K : Set G)) := by
  rw [Setup.Qs, ← inf_assoc, inf_eq_left.mpr hQX]

private theorem Qs_one_le_S_centralizer (Y : Setup Γ G) :
    Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
  inf_le_inf_right _ (Y.Q_le_edgeSylow_right 1)

private theorem Qs_relIndex_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Qs 1).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 := by
  have hT : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.normalizer (Y.Q 1 : Set G) :=
    inf_le_left.trans ((S_le_L_one Y).trans ((Y.L_le_Gi 1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))))
  rw [Qs_one_eq_inf Y (X := Y.S) (Y.Q_le_edgeSylow_right 1), Subgroup.inf_relIndex_right,
    ← F1.relIndex_sup_eq_of_le_normalizer hT, S_eq_centralizer_sup_Q Y H,
    S_relIndex_Q_one Y H]

private theorem card_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 * Nat.card ↥(Y.Qs 1) := by
  have hle : Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    Qs_one_le_S_centralizer Y
  have hm := Subgroup.relIndex_mul_card (H := Y.Qs 1)
    (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
  rw [inf_eq_left.mpr hle, Qs_relIndex_S_centralizer Y H] at hm
  exact hm.symm

private theorem Gi0_relIndex_M (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Gi 0).relIndex (Y.N ⊓ Y.Gi 1) = 3 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  have hrel := FanTree.relIndex_stabilizer_eq_ncard_orbit (G := G) (V := V)
    (H := Y.N ⊓ Y.Gi 1) (b := Y.vert 0)
  have horb : MulAction.orbit (↥(Y.N ⊓ Y.Gi 1)) (Y.vert 0) =
      Γ.neighborSet (Y.vert 1) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨m, rfl⟩
      have h1 : Γ.Adj (m • Y.vert 1) (m • Y.vert 0) :=
        (Y.hyp.adj_smul (m : G) (Y.vert 1) (Y.vert 0)).mpr (by simpa using (Y.adj 0).symm)
      have h2 : (m : G) • Y.vert 1 = Y.vert 1 :=
        MulAction.mem_stabilizer_iff.mp (by simpa using m.2.2)
      show Γ.Adj (Y.vert 1) ((m : G) • Y.vert 0)
      rw [← h2]
      exact h1
    · intro w hw
      obtain ⟨m, hm, hmw⟩ := Y.exists_normalizer_K_one H (by simpa using (Y.adj 0).symm) hw
      exact ⟨⟨m, hm⟩, hmw⟩
  have h3 : Nat.card (Γ.neighborSet (Y.vert 1)) = 3 := by
    rw [(Y.hyp.valency (Y.vert 1)).2]
    rw [show nOf Γ (Y.vert 1) = 1 from H.n_one]
    norm_num
  rw [horb, ← Nat.card_coe_set_eq, h3] at hrel
  simpa using hrel

private theorem L_one_eq_centralizer_sup_Q (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Y.Q 1 = Y.L 1 :=
  inf_centralizer_sup_Q_one Y H (Y.Q_le_L 1) le_rfl
    ((Y.K_le_Gi 1).trans (le_normalizer_oTwoPrime (Y.Gi 1)))

private theorem Q_one_relIndex_L_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Q 1).relIndex (Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G)) = 6 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  have hT' : Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.normalizer (Y.Q 1 : Set G) :=
    inf_le_left.trans ((Y.L_le_Gi 1).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)))
  rw [← F1.relIndex_sup_eq_of_le_normalizer (D := Y.Q 1) hT',
    L_one_eq_centralizer_sup_Q Y H]
  have hLcard : Nat.card ↥(Y.L 1) = 6 * Nat.card ↥(Y.Q 1) := card_L_one Y H
  haveI hQfin : Finite ↥(Y.Q 1) :=
    Finite.of_injective (Subgroup.inclusion (Y.Q_le_Gi 1)) (Subgroup.inclusion_injective _)
  have hqpos : 0 < Nat.card ↥(Y.Q 1) := Nat.card_pos
  have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.L 1)
  rw [inf_eq_left.mpr (Y.Q_le_L 1), hLcard] at h
  exact Nat.eq_of_mul_eq_mul_right hqpos h

private theorem Qs_relIndex_L_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Qs 1).relIndex (Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G)) = 6 := by
  rw [Qs_one_eq_inf Y (Y.Q_le_L 1), Subgroup.inf_relIndex_right]
  exact Q_one_relIndex_L_centralizer Y H

private theorem M_inf_Gi0_eq (Y : Setup Γ G) :
    Y.N ⊓ Y.Gi 1 ⊓ Y.Gi 0 = (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.K := by
  have hjoin : Y.Gi 0 ⊓ Y.Gi 1 = Y.S ⊔ Y.K := by
    rw [← Y.K_sup, sup_comm]
  have hSle : Y.S ≤ Y.Gi 0 ⊓ Y.Gi 1 := by
    rw [hjoin]; exact le_sup_left
  have hKS : Y.K ⊓ Y.S = ⊥ := by
    rw [← Y.edgeSylow_zero]
    exact Y.K_inf_edgeSylow 0
  have hLHS : Y.N ⊓ Y.Gi 1 ⊓ Y.Gi 0 = Y.N ⊓ (Y.Gi 0 ⊓ Y.Gi 1) := by
    rw [inf_assoc, inf_comm (Y.Gi 1) (Y.Gi 0)]
  haveI hSnormal01 : (Y.S.subgroupOf (Y.Gi 0 ⊓ Y.Gi 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))
  refine le_antisymm ?_ ?_
  · rw [hLHS]
    rintro x ⟨hxN, hx01⟩
    let x' : ↥(Y.Gi 0 ⊓ Y.Gi 1) := ⟨x, hx01⟩
    have hsup' : Y.K.subgroupOf (Y.Gi 0 ⊓ Y.Gi 1) ⊔
        Y.S.subgroupOf (Y.Gi 0 ⊓ Y.Gi 1) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup Y.K_le_inf hSle, Y.K_sup, Subgroup.subgroupOf_self]
    have hmem : x' ∈ Y.K.subgroupOf (Y.Gi 0 ⊓ Y.Gi 1) ⊔
        Y.S.subgroupOf (Y.Gi 0 ⊓ Y.Gi 1) := by
      rw [hsup']; exact Subgroup.mem_top x'
    obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    have hkK : (k : G) ∈ Y.K := Subgroup.mem_subgroupOf.mp hk
    have hsS : (s : G) ∈ Y.S := Subgroup.mem_subgroupOf.mp hs
    have hksG : (k : G) * (s : G) = x := congrArg Subtype.val hks
    have hsN : (s : G) ∈ Subgroup.normalizer (Y.K : Set G) := by
      have hk' : (k : G) ∈ Subgroup.normalizer (Y.K : Set G) := Subgroup.le_normalizer hkK
      have hsinv : (s : G) = (k : G)⁻¹ * x := by rw [← hksG]; group
      rw [hsinv]
      exact (Subgroup.normalizer (Y.K : Set G)).mul_mem
        ((Subgroup.normalizer (Y.K : Set G)).inv_mem hk') hxN
    have hscent : (s : G) ∈ Subgroup.centralizer (Y.K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      have hcommK : ⁅(s : G), k'⁆ ∈ Y.K := by
        rw [commutatorElement_def]
        exact Y.K.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN k').mp hk') (Y.K.inv_mem hk')
      have hcommS : ⁅(s : G), k'⁆ ∈ Y.S := by
        rw [commutatorElement_def]
        have h1 : (s : G) * k' * (s : G)⁻¹ * k'⁻¹ =
            (s : G) * (k' * (s : G)⁻¹ * k'⁻¹) := by group
        rw [h1]
        have hk'N : k' ∈ Subgroup.normalizer (Y.S : Set G) :=
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))
            (Y.K_le_inf hk')
        exact Y.S.mul_mem hsS ((Subgroup.mem_normalizer_iff.mp hk'N ((s : G)⁻¹)).mp
          (Y.S.inv_mem hsS))
      have hbot : ⁅(s : G), k'⁆ = 1 := by
        have hmem0 : ⁅(s : G), k'⁆ ∈ (⊥ : Subgroup G) := by
          rw [← hKS]
          exact Subgroup.mem_inf.mpr ⟨hcommK, hcommS⟩
        simpa using hmem0
      have h1 : (s : G) * k' * (s : G)⁻¹ * k'⁻¹ = 1 := by
        rw [← commutatorElement_def]; exact hbot
      have h2 : (s : G) * k' * (s : G)⁻¹ = k' := by
        have := congrArg (fun z => z * k') h1
        simpa [mul_assoc] using this
      calc k' * (s : G) = ((s : G) * k' * (s : G)⁻¹) * (s : G) := by rw [h2]
        _ = (s : G) * k' := by group
    rw [← hksG]
    exact ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.K).mul_mem
      (Subgroup.mem_sup_right hkK)
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hsS, hscent⟩))
  · rw [hLHS]
    refine sup_le ?_ ?_
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.centralizer_le_normalizer (Y.K : Set G) hx.2, hSle hx.1⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, Y.K_le_inf hx⟩

private theorem isPGroup_S_centralizer (Y : Setup Γ G) :
    IsPGroup 2 ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
  (pCoreOf_isPGroup' (Y.Gi 0 ⊓ Y.Gi 1)).to_le inf_le_left

private theorem S_centralizer_le_Gi_one (Y : Setup Γ G) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi 1 :=
  (inf_le_left.trans (S_le_L_one Y)).trans (Y.L_le_Gi 1)

private theorem card_normalizer_K_inf_Gi_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card ↥(Y.N ⊓ Y.Gi 1) = 6 * Nat.card ↥(Y.Qs 1) * Nat.card ↥Y.K := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hMfin : Finite ↥(Y.N ⊓ Y.Gi 1) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  haveI hKfin : Finite ↥Y.K :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.K) (Y.K_le_Gi 1)
  haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
      (S_centralizer_le_Gi_one Y)
  have hKNS : Y.K ≤ Subgroup.normalizer (Y.S : Set G) :=
    Y.K_le_inf.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0 ⊓ Y.Gi 1))
  have hconj_mem : ∀ (k : G) (hk : k ∈ Y.K), ∀ c ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G),
      k * c * k⁻¹ ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    intro k hk c hc
    have hcS : c ∈ Y.S := hc.1
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hKNS hk) c).mp hcS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k' hk'
    have hc' : (k⁻¹ * k' * k) * c = c * (k⁻¹ * k' * k) :=
      Subgroup.mem_centralizer_iff.mp hc.2 (k⁻¹ * k' * k)
        (Y.K.mul_mem (Y.K.mul_mem (Y.K.inv_mem hk) hk') hk)
    have hconj : (k * c * k⁻¹) * k' * (k * c * k⁻¹)⁻¹ = k' := by
      calc (k * c * k⁻¹) * k' * (k * c * k⁻¹)⁻¹
          = k * (c * (k⁻¹ * k' * k) * c⁻¹) * k⁻¹ := by group
        _ = k * (((k⁻¹ * k' * k) * c) * c⁻¹) * k⁻¹ := by rw [← hc']
        _ = k * (k⁻¹ * k' * k) * k⁻¹ := by group
        _ = k' := by group
    calc k' * (k * c * k⁻¹)
        = ((k * c * k⁻¹) * k' * (k * c * k⁻¹)⁻¹) * (k * c * k⁻¹) := by rw [hconj]
      _ = (k * c * k⁻¹) * k' := by group
  have hKnormal : Y.K ≤ Subgroup.normalizer
      ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
    intro k hk
    change k ∈ Subgroup.normalizer
      (((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hconj_mem k hk c hc
    · intro hc
      have h1 := hconj_mem k⁻¹ (Y.K.inv_mem hk) (k * c * k⁻¹) hc
      have h2 : k⁻¹ * (k * c * k⁻¹) * (k⁻¹)⁻¹ = c := by group
      rwa [h2] at h1
  have hdisj : Disjoint (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) Y.K := by
    rw [disjoint_iff_inf_le]
    intro x hx
    obtain ⟨hxS, hxK⟩ := Subgroup.mem_inf.mp hx
    have hbot : x ∈ (⊥ : Subgroup G) := by
      rw [← (show Y.K ⊓ Y.S = ⊥ from by
        rw [← Y.edgeSylow_zero]; exact Y.K_inf_edgeSylow 0)]
      exact Subgroup.mem_inf.mpr ⟨hxK, hxS.1⟩
    simpa using hbot
  have hcardT : Nat.card ↥((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.K) =
      2 * Nat.card ↥(Y.Qs 1) * Nat.card ↥Y.K := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hKnormal hdisj,
      card_S_centralizer Y H]
  have hM_eq : Y.Gi 0 ⊓ (Y.N ⊓ Y.Gi 1) = (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ⊔ Y.K := by
    rw [inf_comm (Y.Gi 0)]
    exact M_inf_Gi0_eq Y
  have hrel := Subgroup.relIndex_mul_card (H := Y.Gi 0) (K := Y.N ⊓ Y.Gi 1)
  rw [hM_eq, Gi0_relIndex_M Y H, hcardT] at hrel
  rw [hrel.symm]
  ring

private theorem S_centralizer_not_normal_of_trans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {A : Subgroup G} (hA : ∀ w : V, Γ.Adj (Y.vert 1) w → ∃ m ∈ A, m • Y.vert 0 = w) :
    ¬ A ≤ Subgroup.normalizer ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
  intro hN
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  have hfix : ∀ x ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G), ∀ w : V,
      Γ.Adj (Y.vert 1) w → x • w = w := by
    intro x hx w hw
    obtain ⟨m, hm, hmw⟩ := hA w hw
    have hconj : m⁻¹ * x * m ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
      have hmN : m ∈ Subgroup.normalizer
          ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := hN hm
      have h1 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G)).inv_mem hmN)
        x).mp hx
      simpa using h1
    have hx0 : x • Y.vert 0 = Y.vert 0 :=
      MulAction.mem_stabilizer_iff.mp (show x ∈ Y.Gi 0 from
        (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2
          (Y.Gi 0 ⊓ Y.Gi 1) hx.1)).1)
    have hc0 : (m⁻¹ * x * m) • Y.vert 0 = Y.vert 0 :=
      MulAction.mem_stabilizer_iff.mp (show m⁻¹ * x * m ∈ Y.Gi 0 from
        (Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2
          (Y.Gi 0 ⊓ Y.Gi 1) hconj.1)).1)
    calc x • w = x • (m • Y.vert 0) := by rw [hmw]
      _ = (x * m) • Y.vert 0 := (mul_smul x m (Y.vert 0)).symm
      _ = (m * (m⁻¹ * x * m)) • Y.vert 0 := by
          rw [show x * m = m * (m⁻¹ * x * m) by group]
      _ = m • ((m⁻¹ * x * m) • Y.vert 0) := mul_smul m (m⁻¹ * x * m) (Y.vert 0)
      _ = m • Y.vert 0 := by rw [hc0]
      _ = w := hmw
  have hker : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      kernelOnNeighbors Γ G (Y.vert 1) := by
    intro x hx
    rw [mem_kernelOnNeighbors]
    exact ⟨(Y.L_le_Gi 1) ((S_le_L_one Y) hx.1), fun a ha => hfix x hx a ha⟩
  have hQ1 : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Q 1 := by
    have h := inf_kernelOnNeighbors_eq_pCoreOf Y.hyp (Y.hyp.isLocL2_oTwoPrime (Y.vert 1))
    intro x hx
    have hmem : x ∈ Y.L 1 ⊓ kernelOnNeighbors Γ G (Y.vert 1) :=
      ⟨(S_le_L_one Y) hx.1, hker hx⟩
    rwa [h] at hmem
  have hSQs : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊓ Y.Q 1 = Y.Qs 1 := by
    rw [Setup.Qs]
    ext x
    constructor
    · rintro ⟨⟨-, hc⟩, hq⟩
      exact ⟨hq, hc⟩
    · rintro ⟨hq, hc⟩
      exact ⟨⟨Y.Q_le_edgeSylow_right 1 hq, hc⟩, hq⟩
  have heq : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) = Y.Qs 1 := by
    rw [← inf_eq_left.mpr hQ1]
    exact hSQs
  have hc := card_S_centralizer Y H
  rw [heq] at hc
  have hpos : 0 < Nat.card ↥(Y.Qs 1) := Nat.card_pos
  omega

private theorem S_centralizer_le_M (Y : Setup Γ G) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.N ⊓ Y.Gi 1 := by
  intro x hx
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.centralizer_le_normalizer (Y.K : Set G) hx.2,
      (Y.L_le_Gi 1) ((S_le_L_one Y) hx.1)⟩

private theorem S_centralizer_le_J (Y : Setup Γ G) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 :=
  le_oTwoPrime_of_isPGroup (isPGroup_S_centralizer Y) (S_centralizer_le_M Y)

private theorem Qs_le_J (Y : Setup Γ G) : Y.Qs 1 ≤ Y.J 1 := by
  refine le_oTwoPrime_of_isPGroup ?_ ?_
  · exact (pCoreOf_isPGroup' (Y.Gi 1)).to_le inf_le_left
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le_normalizer (Y.K : Set G) hx.2, Y.Q_le_Gi 1 hx.1⟩

private theorem eq_two_or_eq_six_of_dvd_six {x : ℕ} (hx : x ∣ 6) (h2 : 2 ∣ x) :
    x = 2 ∨ x = 6 := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨m, hm⟩ := h2
  rw [hm] at hk
  have h3 : 2 * (m * k) = 2 * 3 := by
    calc 2 * (m * k) = (2 * m) * k := by ring
      _ = 6 := hk.symm
      _ = 2 * 3 := by norm_num
  have h2' : m * k = 3 := Nat.eq_of_mul_eq_mul_left (by norm_num) h3
  have hm3 : m ∣ 3 := ⟨k, h2'.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h4
  · left; rw [hm, h1]
  · right; rw [hm, h4]

private theorem J_eq_L_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.J 1 = Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  have hJle : Y.J 1 ≤ Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) := J_le_L_and_C Y H
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective (Subgroup.inclusion (hJle.trans inf_le_left))
      (Subgroup.inclusion_injective _)
  have hMS : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.N ⊓ Y.Gi 1 :=
    S_centralizer_le_M Y
  have hSJ : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 :=
    S_centralizer_le_J Y
  have hQsJ : Y.Qs 1 ≤ Y.J 1 := Qs_le_J Y
  have hQsS : Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    Qs_one_le_S_centralizer Y
  have hQsX : Y.Qs 1 ≤ Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G) := hQsJ.trans hJle
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  haveI hXfin : Finite ↥(Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (inf_le_left.trans (Y.L_le_Gi 1))
  have hdvd : (Y.Qs 1).relIndex (Y.J 1) ∣ 6 := by
    refine ⟨(Y.J 1).relIndex (Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G)), ?_⟩
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1) (K := Y.J 1)
      (L := Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G)) hQsJ hJle
    rw [Qs_relIndex_L_centralizer Y H] at h
    exact h.symm
  have heven : (Y.Qs 1).relIndex (Y.J 1) =
      2 * (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1) := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1)
      (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (L := Y.J 1) hQsS hSJ
    rw [Qs_relIndex_S_centralizer Y H] at h
    exact h.symm
  have h2dvd : 2 ∣ (Y.Qs 1).relIndex (Y.J 1) := ⟨_, heven⟩
  have hcases : (Y.Qs 1).relIndex (Y.J 1) = 2 ∨ (Y.Qs 1).relIndex (Y.J 1) = 6 :=
    eq_two_or_eq_six_of_dvd_six hdvd h2dvd
  rcases hcases with h2 | h6
  ·
    exfalso
    have hJcard : Nat.card ↥(Y.J 1) = 2 * Nat.card ↥(Y.Qs 1) := by
      have h := Subgroup.relIndex_mul_card (H := Y.Qs 1) (K := Y.J 1)
      rw [inf_eq_left.mpr hQsJ, h2] at h
      exact h.symm
    haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
      finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
        (S_centralizer_le_Gi_one Y)
    have heqS' : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) = Y.J 1 := by
      refine Subgroup.eq_of_le_of_card_ge hSJ ?_
      rw [hJcard, card_S_centralizer Y H]
    have heqS : Y.J 1 = Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := heqS'.symm
    have hJnormal : Y.N ⊓ Y.Gi 1 ≤ Subgroup.normalizer (Y.J 1 : Set G) :=
      le_normalizer_oTwoPrime (Y.N ⊓ Y.Gi 1)
    have hSnormal : Y.N ⊓ Y.Gi 1 ≤
        Subgroup.normalizer ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
      change Y.N ⊓ Y.Gi 1 ≤ Subgroup.normalizer
        (((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Subgroup G) : Set G)
      rw [← heqS]
      exact hJnormal
    exact S_centralizer_not_normal_of_trans Y H
        (fun w hw => Y.exists_normalizer_K_one H (by simpa using (Y.adj 0).symm) hw) hSnormal
  ·
    refine Subgroup.eq_of_le_of_card_ge hJle ?_
    have h1 := Subgroup.relIndex_mul_card (H := Y.Qs 1) (K := Y.J 1)
    rw [inf_eq_left.mpr hQsJ, h6] at h1
    have h2 := Subgroup.relIndex_mul_card (H := Y.Qs 1)
      (K := Y.L 1 ⊓ Subgroup.centralizer (Y.K : Set G))
    rw [inf_eq_left.mpr hQsX, Qs_relIndex_L_centralizer Y H] at h2
    rw [← h1, ← h2]

private theorem S_centralizer_sylow_M (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    IsSylowTwoOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (Y.N ⊓ Y.Gi 1) := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hMfin : Finite ↥(Y.N ⊓ Y.Gi 1) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
      (S_centralizer_le_Gi_one Y)
  have hle : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.N ⊓ Y.Gi 1 := by
    intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.centralizer_le_normalizer (Y.K : Set G) hx.2,
        (Y.L_le_Gi 1) ((S_le_L_one Y) hx.1)⟩
  refine ⟨hle, isPGroup_S_centralizer Y, ?_⟩
  · intro h2
    haveI hQfin : Finite ↥(Y.Qs 1) :=
      Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
        (Subgroup.inclusion_injective _)
    haveI hKfin : Finite ↥Y.K :=
      finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := Y.K) (Y.K_le_Gi 1)
    have hm := Subgroup.relIndex_mul_card (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.N ⊓ Y.Gi 1)
    rw [inf_eq_left.mpr hle, card_normalizer_K_inf_Gi_one Y H, card_S_centralizer Y H] at hm
    have h3 : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.N ⊓ Y.Gi 1) =
        3 * Nat.card ↥Y.K := by
      have hqpos : 0 < Nat.card ↥(Y.Qs 1) := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card ↥(Y.Qs 1) from by positivity) ?_
      calc (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.N ⊓ Y.Gi 1) *
          (2 * Nat.card ↥(Y.Qs 1)) = 6 * Nat.card ↥(Y.Qs 1) * Nat.card ↥Y.K := hm
        _ = (3 * Nat.card ↥Y.K) * (2 * Nat.card ↥(Y.Qs 1)) := by ring
    change 2 ∣ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.N ⊓ Y.Gi 1) at h2
    rw [h3] at h2
    obtain ⟨k, hk⟩ := Y.odd_card_K
    rw [hk] at h2
    have hdvd : 2 ∣ 2 * k + 1 := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 2 3) h2
    omega

private theorem pCoreOf_M_le_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    pCoreOf 2 (Y.N ⊓ Y.Gi 1) ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hMfin : Finite ↥(Y.N ⊓ Y.Gi 1) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
      (S_centralizer_le_Gi_one Y)
  have hSp : IsPGroup 2 ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    isPGroup_S_centralizer Y
  have hQp : IsPGroup 2
      ↥(pCoreOf 2 (Y.N ⊓ Y.Gi 1) ⊔ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    (pCoreOf_isPGroup' (Y.N ⊓ Y.Gi 1)).to_sup_of_normal_left' hSp
      ((S_centralizer_le_M Y).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.N ⊓ Y.Gi 1)))
  have hQH : pCoreOf 2 (Y.N ⊓ Y.Gi 1) ⊔ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Y.N ⊓ Y.Gi 1 :=
    sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.N ⊓ Y.Gi 1)) (S_centralizer_le_M Y)
  haveI hQfin2 : Finite ↥(pCoreOf 2 (Y.N ⊓ Y.Gi 1) ⊔
      Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    Finite.of_injective (Subgroup.inclusion hQH) (Subgroup.inclusion_injective _)
  have heq := CFSG.GroupTheory.eq_of_isSylowTwoOf_of_le (S_centralizer_sylow_M Y H) hQp
    hQH le_sup_right
  exact le_sup_left.trans (le_of_eq heq)

private theorem Qs_relIndex_J (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Qs 1).relIndex (Y.J 1) = 6 := by
  rw [J_eq_L_centralizer Y H]
  exact Qs_relIndex_L_centralizer Y H

theorem pCoreOf_J (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    pCoreOf 2 (Y.J 1) = Y.Qs 1 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1))
      (Subgroup.inclusion_injective _)
  haveI hMfin : Finite ↥(Y.N ⊓ Y.Gi 1) :=
    Finite.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
      (S_centralizer_le_Gi_one Y)
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  have hQs_le : Y.Qs 1 ≤ pCoreOf 2 (Y.J 1) := by
    have hnorm : Y.J 1 ≤
        Subgroup.normalizer ((Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
      intro j hj
      refine Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact ((Y.J_le_L 1).trans
          ((Y.L_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)))) hj
      · exact ((J_le_centralizer Y H).trans (Subgroup.le_normalizer)) hj
    have hp : IsPGroup 2 ↥(Y.Qs 1) := (pCoreOf_isPGroup' (Y.Gi 1)).to_le inf_le_left
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Qs_le_J Y) hnorm hp
  have hO_le : pCoreOf 2 (Y.J 1) ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    have hMnorm : Y.N ⊓ Y.Gi 1 ≤ Subgroup.normalizer ((pCoreOf 2 (Y.J 1)) : Set G) :=
      (le_normalizer_oTwoPrime (Y.N ⊓ Y.Gi 1)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
          (oTwoPrime (Y.N ⊓ Y.Gi 1)))
    have hleM : pCoreOf 2 (Y.J 1) ≤ pCoreOf 2 (Y.N ⊓ Y.Gi 1) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.J 1)).trans
          (oTwoPrime_le (Y.N ⊓ Y.Gi 1)))
        hMnorm (pCoreOf_isPGroup' (Y.J 1))
    exact hleM.trans (pCoreOf_M_le_S_centralizer Y H)
  have hprod : (Y.Qs 1).relIndex (pCoreOf 2 (Y.J 1)) *
      (pCoreOf 2 (Y.J 1)).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1) (K := pCoreOf 2 (Y.J 1))
      (L := Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) hQs_le hO_le
    rw [Qs_relIndex_S_centralizer Y H] at h
    exact h
  have hdvd : (Y.Qs 1).relIndex (pCoreOf 2 (Y.J 1)) ∣ 2 := ⟨_, hprod.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hQs_le
  · exfalso
    rw [h2] at hprod
    have hOrel : (pCoreOf 2 (Y.J 1)).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 1 := by
      omega
    have hSleO : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ pCoreOf 2 (Y.J 1) :=
      Subgroup.relIndex_eq_one.mp hOrel
    have hSeq : pCoreOf 2 (Y.J 1) = Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
      le_antisymm hO_le hSleO
    have hSnormal : Y.N ⊓ Y.Gi 1 ≤
        Subgroup.normalizer ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
      change Y.N ⊓ Y.Gi 1 ≤ Subgroup.normalizer
        (((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Subgroup G) : Set G)
      rw [← hSeq]
      exact (le_normalizer_oTwoPrime (Y.N ⊓ Y.Gi 1)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (oTwoPrime (Y.N ⊓ Y.Gi 1)))
    exact S_centralizer_not_normal_of_trans Y H
        (fun w hw => Y.exists_normalizer_K_one H (by simpa using (Y.adj 0).symm) hw) hSnormal

theorem J_trans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∀ a b : V, Γ.Adj (Y.vert 1) a → Γ.Adj (Y.vert 1) b → ∃ g ∈ Y.J 1, g • a = b := by
  intro a b ha hb
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  obtain ⟨l, hl, hlab⟩ := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).trans a b ha hb
  obtain ⟨c, hc, hcl⟩ := exists_mem_centralizer_coset_Q_one Y H (Y.Q_le_L 1) le_rfl
    ((Y.K_le_Gi 1).trans (le_normalizer_oTwoPrime (Y.Gi 1))) hl
  refine ⟨c, ?_, ?_⟩
  · rw [J_eq_L_centralizer Y H]
    exact hc
  · have hqa : (c⁻¹ * l) • a = a := Y.Q_fixes_neighbors_vert 1 a ha (c⁻¹ * l) hcl
    calc c • a = c • ((c⁻¹ * l) • a) := by rw [hqa]
      _ = (c * (c⁻¹ * l)) • a := (mul_smul c (c⁻¹ * l) a).symm
      _ = l • a := by rw [show c * (c⁻¹ * l) = l by group]
      _ = b := hlab

private def dtAlpha (Y : Setup Γ G) : Y.DtV :=
  ⟨Y.vert (-1), by
    refine ⟨?_, fun k hk => Y.K_fix k hk (-1)⟩
    have h := (Y.adj (-1)).symm
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
    rw [dist_eq_one_iff_adj.mpr h]
    exact ⟨0, by norm_num⟩⟩

@[simp] private theorem dtAlpha_val (Y : Setup Γ G) : (Y.dtAlpha).1 = Y.vert (-1) := rfl

@[simp] private theorem dtV_smul_val (Y : Setup Γ G) (n : ↥Y.N) (u : Y.DtV) :
    (n • u).1 = (n : G) • u.1 := rfl

private theorem dtAlpha_adj_dtBeta (Y : Setup Γ G) :
    Y.dtGraph.Adj Y.dtAlpha Y.dtBase := by
  refine ⟨?_, Y.vert 0, ?_, ?_, fun k hk => Y.K_fix k hk 0⟩
  · intro h
    have h' := congrArg Subtype.val h
    simp only [dtAlpha_val, dtBase_val] at h'
    have h2 := Y.vert_injective h'
    norm_num at h2
  · show Γ.Adj (Y.vert (-1)) (Y.vert 0)
    have h := Y.adj (-1)
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  · show Γ.Adj (Y.vert 0) (Y.vert 1)
    simpa using Y.adj 0

private theorem dtBase_locTrans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∀ a b : Y.DtV, Y.dtGraph.Adj Y.dtBase a → Y.dtGraph.Adj Y.dtBase b →
      ∃ n : ↥Y.N, (n : G) ∈ Y.J 1 ∧ n • a = b := by
  intro a b ha hb
  obtain ⟨wa, h1a, h2a, -⟩ := ha.2
  obtain ⟨wb, h1b, h2b, h3b⟩ := hb.2
  obtain ⟨g, hgJ, hgw⟩ := Y.J_trans H wa wb h1a h1b
  have hgJ' : g ∈ oTwoPrime (Y.N ⊓ Y.Gi 1) := hgJ
  have hgN : g ∈ Y.N := (oTwoPrime_le (Y.N ⊓ Y.Gi 1) hgJ').1
  have hgGi : g ∈ Y.Gi 1 := (oTwoPrime_le (Y.N ⊓ Y.Gi 1) hgJ').2
  refine ⟨⟨g, hgN⟩, hgJ, ?_⟩
  apply Subtype.ext
  show g • a.1 = b.1
  have hgaK : ∀ k ∈ Y.K, k • (g • a.1) = g • a.1 :=
    (kfix_smul_iff Y hgN a.1).mpr a.2.2
  have hne : g • a.1 ≠ Y.vert 1 := by
    intro h
    have h1 : g • a.1 = g • Y.vert 1 := h.trans (MulAction.mem_stabilizer_iff.mp hgGi).symm
    exact ha.1 (Subtype.ext (MulAction.injective g h1).symm)
  have hne' : b.1 ≠ Y.vert 1 := fun h => hb.1 (Subtype.ext h.symm)
  have hadj : Γ.Adj wb (g • a.1) := by
    rw [← hgw]
    exact (Y.hyp.adj_smul g wa a.1).mpr h2a
  exact eq_of_kfix_adj_ne Y H (Y.dtBase).2.1 (Y.dtBase).2.2 h1b h3b hadj hgaK hne h2b
    b.2.2 hne'

private theorem dtAlpha_locTrans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∀ a b : Y.DtV, Y.dtGraph.Adj Y.dtAlpha a → Y.dtGraph.Adj Y.dtAlpha b →
      ∃ n : ↥Y.N, (n : G) ∈ Y.J (-1) ∧ n • a = b := by
  intro a b ha hb
  let t : ↥Y.N := ⟨Y.τ ^ (-1 : ℤ), Y.N.zpow_mem Y.τ_norm (-1)⟩
  have ht : t • Y.dtBase = Y.dtAlpha := by
    apply Subtype.ext
    show (Y.τ ^ (-1 : ℤ)) • Y.vert 1 = Y.vert (-1)
    rw [Y.zpow_smul_vert]
    congr 1
  have ht' : t⁻¹ • Y.dtAlpha = Y.dtBase := by
    rw [← ht, inv_smul_smul]
  have ha' : Y.dtGraph.Adj Y.dtBase (t⁻¹ • a) := by
    rw [← ht']
    exact (Y.dt_adj_smul t⁻¹ Y.dtAlpha a).mpr ha
  have hb' : Y.dtGraph.Adj Y.dtBase (t⁻¹ • b) := by
    rw [← ht']
    exact (Y.dt_adj_smul t⁻¹ Y.dtAlpha b).mpr hb
  obtain ⟨m, hmJ, hmab⟩ := Y.dtBase_locTrans H (t⁻¹ • a) (t⁻¹ • b) ha' hb'
  refine ⟨t * m * t⁻¹, ?_, ?_⟩
  · have hJ : Y.J (-1) = (Y.J 1).map (MulAut.conj (Y.τ ^ (-1 : ℤ))).toMonoidHom := by
      have h := Y.J_add (-1) 1
      rw [show (1 : ℤ) + 2 * (-1 : ℤ) = -1 by norm_num] at h
      exact h
    rw [hJ]
    have hmem := Subgroup.mem_map_of_mem ((MulAut.conj (Y.τ ^ (-1 : ℤ))).toMonoidHom) hmJ
    simpa [t, MulAut.conj_apply] using hmem
  · calc (t * m * t⁻¹) • a = t • (m • (t⁻¹ • a)) := by rw [mul_smul, mul_smul]
      _ = t • (t⁻¹ • b) := by rw [hmab]
      _ = b := smul_inv_smul t b

private theorem locTrans_subgroupOf (Y : Setup Γ G) {X : Subgroup G} {j : ℤ} {u : Y.DtV}
    (hu : u.1 = Y.vert j) (hJN : Y.J j ≤ Subgroup.normalizer (X : Set G))
    (hJloc : ∀ a b : Y.DtV, Y.dtGraph.Adj u a → Y.dtGraph.Adj u b →
      ∃ n : ↥Y.N, (n : G) ∈ Y.J j ∧ n • a = b) :
    ∀ a b : Y.DtV, Y.dtGraph.Adj u a → Y.dtGraph.Adj u b →
      ∃ h ∈ (Subgroup.normalizer (X : Set G)).subgroupOf Y.N ⊓
        MulAction.stabilizer ↥Y.N u, h • a = b := by
  intro a b ha hb
  obtain ⟨n, hnJ, hnab⟩ := hJloc a b ha hb
  have hnJ' : (n : G) ∈ Y.J j := hnJ
  have hnN : (n : G) ∈ Subgroup.normalizer (X : Set G) := hJN hnJ'
  have hnGi : (n : G) ∈ Y.Gi j := (oTwoPrime_le (Y.N ⊓ Y.Gi j) hnJ').2
  have hfixu : n • u = u := by
    apply Subtype.ext
    show (n : G) • u.1 = u.1
    rw [hu]
    exact MulAction.mem_stabilizer_iff.mp hnGi
  exact ⟨n, Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hnN, hfixu⟩, hnab⟩

private theorem H0_locTrans (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {X : Subgroup G}
    (h1 : Y.J 1 ≤ Subgroup.normalizer (X : Set G))
    (hneg : Y.J (-1) ≤ Subgroup.normalizer (X : Set G)) :
    (∀ a b : Y.DtV, Y.dtGraph.Adj Y.dtAlpha a → Y.dtGraph.Adj Y.dtAlpha b →
      ∃ h ∈ (Subgroup.normalizer (X : Set G)).subgroupOf Y.N ⊓
        MulAction.stabilizer ↥Y.N Y.dtAlpha, h • a = b) ∧
    (∀ a b : Y.DtV, Y.dtGraph.Adj Y.dtBase a → Y.dtGraph.Adj Y.dtBase b →
      ∃ h ∈ (Subgroup.normalizer (X : Set G)).subgroupOf Y.N ⊓
        MulAction.stabilizer ↥Y.N Y.dtBase, h • a = b) :=
  ⟨locTrans_subgroupOf Y (X := X) (j := -1) (u := Y.dtAlpha) rfl hneg
      (Y.dtAlpha_locTrans H),
    locTrans_subgroupOf Y (X := X) (j := 1) (u := Y.dtBase) rfl h1 (Y.dtBase_locTrans H)⟩

private theorem H0_edgeTransitive (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {X : Subgroup G}
    (h1 : Y.J 1 ≤ Subgroup.normalizer (X : Set G))
    (hneg : Y.J (-1) ≤ Subgroup.normalizer (X : Set G)) :
    EdgeTransitive Y.dtGraph ((Subgroup.normalizer (X : Set G)).subgroupOf Y.N) := by
  obtain ⟨hα, hβ⟩ := H0_locTrans Y H h1 hneg
  exact edgeTransitive_of_locTrans (Y.dt_isTree H).connected (Y.dt_adj_smul)
    _ Y.dtAlpha_adj_dtBeta hα hβ

private theorem fixes_dtV_of_edgeTransitive (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {X : Subgroup G}
    (hX : X ≤ Y.Gi (-1) ⊓ Y.Gi 1)
    (hET : EdgeTransitive Y.dtGraph ((Subgroup.normalizer (X : Set G)).subgroupOf Y.N)) :
    ∀ x ∈ X, ∀ u : Y.DtV, x • u.1 = u.1 := by
  intro x hx u
  have hpos : 0 < Nat.card (Y.dtGraph.neighborSet u) := by
    rw [Y.dt_card_nbr H u]
    norm_num
  obtain ⟨⟨u', hu'⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨n, hnH, hor⟩ := hET Y.dtAlpha Y.dtBase u u' Y.dtAlpha_adj_dtBeta hu'
  have hnNorm : (n : G) ∈ Subgroup.normalizer (X : Set G) := Subgroup.mem_subgroupOf.mp hnH
  have hconj : (n : G)⁻¹ * x * (n : G) ∈ X :=
    (Subgroup.mem_normalizer_iff''.mp hnNorm x).1 hx
  have hfixneg : ((n : G)⁻¹ * x * (n : G)) • Y.vert (-1) = Y.vert (-1) :=
    MulAction.mem_stabilizer_iff.mp (hX hconj).1
  have hfixone : ((n : G)⁻¹ * x * (n : G)) • Y.vert 1 = Y.vert 1 :=
    MulAction.mem_stabilizer_iff.mp (hX hconj).2
  have key : ∀ v : V, (n : G) • v = u.1 → (v = Y.vert (-1) ∨ v = Y.vert 1) →
      x • u.1 = u.1 := by
    intro v hv hv'
    have hvv : ((n : G)⁻¹ * x * (n : G)) • v = v := by
      rcases hv' with rfl | rfl
      · exact hfixneg
      · exact hfixone
    calc x • u.1 = x • ((n : G) • v) := by rw [hv]
      _ = (x * (n : G)) • v := (mul_smul x (n : G) v).symm
      _ = ((n : G) * ((n : G)⁻¹ * x * (n : G))) • v := by
          rw [show x * (n : G) = (n : G) * ((n : G)⁻¹ * x * (n : G)) by group]
      _ = (n : G) • (((n : G)⁻¹ * x * (n : G)) • v) := mul_smul _ _ _
      _ = (n : G) • v := by rw [hvv]
      _ = u.1 := hv
  rcases hor with ⟨hαu, -⟩ | ⟨-, hβu⟩
  · exact key (Y.vert (-1)) (by simpa using congrArg Subtype.val hαu) (Or.inl rfl)
  · exact key (Y.vert 1) (by simpa using congrArg Subtype.val hβu) (Or.inr rfl)

theorem eq_bot_of_normal_J (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {X : Subgroup G}
    (h2 : IsPGroup 2 X) (h1 : Y.J 1 ≤ Subgroup.normalizer (X : Set G))
    (hneg : Y.J (-1) ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≤ Y.Gi (-1) ⊓ Y.Gi 1) : X = ⊥ := by
  have hfix := fixes_dtV_of_edgeTransitive Y H hX (H0_edgeTransitive Y H h1 hneg)
  have hXK : X ≤ Y.K := fun x hx => Y.dt_kernel H (fun u => hfix x hx u)
  have hbot := inf_eq_bot_of_odd_of_isPGroup (A := Y.K) (B := X) Y.odd_card_K h2
  rwa [inf_eq_right.mpr hXK] at hbot

theorem St_sylow (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    IsSylowTwoOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (Y.J 1) ∧
      (Y.Qs 1).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 ∧
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1) = 3 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1))
      (Subgroup.inclusion_injective _)
  haveI hCfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
      (S_centralizer_le_Gi_one Y)
  have hSJ : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 := S_centralizer_le_J Y
  have hQsS : Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    Qs_one_le_S_centralizer Y
  have hSp : IsPGroup 2 ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    isPGroup_S_centralizer Y
  have h2 : (Y.Qs 1).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 :=
    Qs_relIndex_S_centralizer Y H
  have h6 : (Y.Qs 1).relIndex (Y.J 1) = 6 := Qs_relIndex_J Y H
  have h3 : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1) = 3 := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1)
      (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (L := Y.J 1) hQsS hSJ
    rw [h2, h6] at h
    omega
  refine ⟨⟨hSJ, hSp, ?_⟩, h2, h3⟩
  change ¬ 2 ∣ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1)
  rw [h3]
  norm_num

theorem exists_J_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    ∃ d ∈ Y.J 1, orderOf d = 3 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1))
      (Subgroup.inclusion_injective _)
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  have h3dvd : 3 ∣ Nat.card ↥(Y.J 1) := by
    have hm := Subgroup.relIndex_mul_card (H := Y.Qs 1) (K := Y.J 1)
    rw [inf_eq_left.mpr (Qs_le_J Y), Qs_relIndex_J Y H] at hm
    exact ⟨2 * Nat.card ↥(Y.Qs 1), by rw [← hm]; ring⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  refine ⟨(d : G), d.2, ?_⟩
  rw [← hd]
  exact Subgroup.orderOf_coe d

theorem J_one_le_normalizer_Qs_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.J 1 ≤ Subgroup.normalizer (Y.Qs 1 : Set G) := by
  rw [← pCoreOf_J Y H]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.J 1)

private theorem S_centralizer_le_Gi_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi (-1) := by
  intro s hs
  obtain ⟨hsS, hsC⟩ := Subgroup.mem_inf.mp hs
  obtain ⟨hs0, hs1⟩ :=
    Subgroup.mem_inf.mp (CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.Gi 0 ⊓ Y.Gi 1) hsS)
  have hsN : s ∈ Y.N := Subgroup.centralizer_le_normalizer (Y.K : Set G) hsC
  have hKfix : ∀ k ∈ Y.K, k • (s • Y.vert (-1)) = s • Y.vert (-1) := by
    intro k hk
    have hconj : s⁻¹ * k * s ∈ Y.K := (Subgroup.mem_normalizer_iff''.mp hsN k).mp hk
    calc k • (s • Y.vert (-1)) = (k * s) • Y.vert (-1) := (mul_smul k s _).symm
      _ = (s * (s⁻¹ * k * s)) • Y.vert (-1) := by
          rw [show k * s = s * (s⁻¹ * k * s) by group]
      _ = s • ((s⁻¹ * k * s) • Y.vert (-1)) := mul_smul s _ _
      _ = s • Y.vert (-1) := by rw [Y.K_fix (s⁻¹ * k * s) hconj (-1)]
  have hadj : Γ.Adj (s • Y.vert (-1)) (Y.vert 0) := by
    have h := Y.adj (-1)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
    have h2 := (Y.hyp.adj_smul s (Y.vert (-1)) (Y.vert 0)).mpr h
    rwa [MulAction.mem_stabilizer_iff.mp hs0] at h2
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Y.K_ne_bot H)
  have hkK : (k : G) ∈ Y.K := k.2
  have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkKi : (k : G) ∈ Y.Ki 0 := ⟨hkK, Y.K_le_L_zero H hkK⟩
  have hn0 : 2 ≤ Y.n 0 := by rw [H.n_zero]; exact H.two_le
  have hmem : s • Y.vert (-1) = Y.vert (-1) := by
    rcases (Y.torus_fixed 0 hn0 hkKi hk1' (s • Y.vert (-1)) hadj.symm).mp (hKfix k hkK) with h | h
    · exact h
    · exfalso
      have h' : Y.vert (-1) = Y.vert 1 := by
        have h1 : s • Y.vert (-1) = Y.vert 1 := by simpa using h
        calc Y.vert (-1) = s⁻¹ • (s • Y.vert (-1)) := (inv_smul_smul s _).symm
          _ = s⁻¹ • Y.vert 1 := by rw [h1]
          _ = Y.vert 1 := by
              rw [show s⁻¹ • Y.vert 1 = s⁻¹ • (s • Y.vert 1) from by
                    rw [MulAction.mem_stabilizer_iff.mp hs1], inv_smul_smul]
      have h2 := Y.vert_injective h'
      norm_num at h2
  exact MulAction.mem_stabilizer_iff.mpr hmem

private theorem S_centralizer_sup_zpowers_eq_J (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d = Y.J 1 := by
  haveI hStfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (S_centralizer_le_Gi_one Y)
  have hStJ : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 := (St_sylow Y H).1.1
  have hStrel : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1) = 3 :=
    (St_sylow Y H).2.2
  have hd_not_St : d ∉ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    intro hdS
    have hdvd : orderOf d ∣ Nat.card ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
      (Subgroup.orderOf_coe ⟨d, hdS⟩).symm ▸ orderOf_dvd_natCard _
    rw [hd3] at hdvd
    obtain ⟨k, hk⟩ := (St_sylow Y H).1.2.1.exists_card_eq
    rw [hk] at hdvd
    exact absurd ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdvd) (by norm_num)
  have hle : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d ≤ Y.J 1 :=
    sup_le hStJ (Subgroup.zpowers_le.mpr hd)
  have hdiv : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d) ∣ 3 := by
    have h := Subgroup.relIndex_mul_relIndex
      (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d)
      (L := Y.J 1) le_sup_left hle
    rw [hStrel] at h
    exact ⟨_, h.symm⟩
  have hne1 : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d) ≠ 1 := by
    intro h1
    apply hd_not_St
    have hleS : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d ≤
        Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := Subgroup.relIndex_eq_one.mp h1
    exact hleS (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have h3' : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d) = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdiv with h | h
    · exact absurd h hne1
    · exact h
  have hone : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d).relIndex
      (Y.J 1) = 1 := by
    have h := Subgroup.relIndex_mul_relIndex
      (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d)
      (L := Y.J 1) le_sup_left hle
    rw [h3', hStrel] at h
    omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

private theorem J_one_le_normalizer_Qs_sup_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    Y.J 1 ≤ Subgroup.normalizer ((Y.Qs 1 ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  have hQsJ : Y.Qs 1 ≤ Y.J 1 := Qs_le_J Y
  have hQsN : Y.J 1 ≤ Subgroup.normalizer (Y.Qs 1 : Set G) := J_one_le_normalizer_Qs_one Y H
  have hrelQsJ : (Y.Qs 1).relIndex (Y.J 1) = 6 := Qs_relIndex_J Y H
  set A : Subgroup G := Y.Qs 1 ⊔ Subgroup.zpowers d with hAdef
  have hAJ : A ≤ Y.J 1 := sup_le hQsJ (Subgroup.zpowers_le.mpr hd)
  have hArel : (Y.Qs 1).relIndex A = 3 := by
    have hdisj : Disjoint (Y.Qs 1) (Subgroup.zpowers d) := by
      rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨hxQ, hxd⟩ := Subgroup.mem_inf.mp hx
      have hxdvd : orderOf x ∣ 3 := by
        have hnat : Nat.card ↥(Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hd3]
        have h := (Subgroup.orderOf_coe (⟨x, hxd⟩ : ↥(Subgroup.zpowers d))).symm
          ▸ orderOf_dvd_natCard (⟨x, hxd⟩ : ↥(Subgroup.zpowers d))
        rwa [hnat] at h
      have hx2 : IsPGroup 2 ↥(Y.Qs 1) :=
        (pCoreOf_isPGroup' (Y.Gi 1)).to_le (inf_le_left : Y.Qs 1 ≤ Y.Q 1)
      have hxdvd2 : orderOf x ∣ Nat.card ↥(Y.Qs 1) :=
        (Subgroup.orderOf_coe ⟨x, hxQ⟩).symm ▸ orderOf_dvd_natCard _
      obtain ⟨m, hm⟩ := hx2.exists_card_eq
      rw [hm] at hxdvd2
      have hcop : Nat.Coprime 3 (2 ^ m) := (by norm_num : Nat.Coprime 3 2).pow_right m
      have h1 : orderOf x ∣ 1 := by
        rw [← hcop]
        exact Nat.dvd_gcd hxdvd hxdvd2
      rw [Subgroup.mem_bot, orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)]
    have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Y.Qs 1) (Subgroup.zpowers d) (Subgroup.zpowers_le.mpr (hQsN hd)) hdisj
    have hA3 : Nat.card ↥(Y.Qs 1 ⊔ Subgroup.zpowers d) = 3 * Nat.card ↥(Y.Qs 1) := by
      rw [hcard, Nat.card_zpowers, hd3, mul_comm]
    have h := Subgroup.relIndex_mul_card (H := Y.Qs 1) (K := Y.Qs 1 ⊔ Subgroup.zpowers d)
    rw [inf_eq_left.mpr le_sup_left, hA3] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(Y.Qs 1))) h
  have hArelJ : A.relIndex (Y.J 1) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1) (K := A) (L := Y.J 1)
      le_sup_left hAJ
    rw [hArel, hrelQsJ] at h
    omega
  have hAnormal : (A.subgroupOf (Y.J 1)).Normal := by
    refine Subgroup.normal_of_index_eq_two ?_
    show A.relIndex (Y.J 1) = 2
    exact hArelJ
  have h := (Subgroup.normal_subgroupOf_iff_le_normalizer hAJ).mp hAnormal
  simpa [hAdef] using h

private theorem S_centralizer_eq_Qs_sup_zpowers (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {t : G}
    (ht : t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (htQs : t ∉ Y.Qs 1) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) = Y.Qs 1 ⊔ Subgroup.zpowers t := by
  have hrelQsSt : (Y.Qs 1).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 :=
    (St_sylow Y H).2.1
  have hle : Y.Qs 1 ⊔ Subgroup.zpowers t ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    sup_le (Qs_one_le_S_centralizer Y) (Subgroup.zpowers_le.mpr ht)
  have hdiv : (Y.Qs 1).relIndex (Y.Qs 1 ⊔ Subgroup.zpowers t) ∣ 2 := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1)
      (K := Y.Qs 1 ⊔ Subgroup.zpowers t) (L := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      le_sup_left hle
    rw [hrelQsSt] at h
    exact ⟨_, h.symm⟩
  have hne1 : (Y.Qs 1).relIndex (Y.Qs 1 ⊔ Subgroup.zpowers t) ≠ 1 := by
    intro h1
    exact htQs ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers t)))
  have h2' : (Y.Qs 1).relIndex (Y.Qs 1 ⊔ Subgroup.zpowers t) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact absurd h hne1
    · exact h
  have hone : (Y.Qs 1 ⊔ Subgroup.zpowers t).relIndex
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 1 := by
    have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs 1)
      (K := Y.Qs 1 ⊔ Subgroup.zpowers t) (L := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      le_sup_left hle
    rw [h2', hrelQsSt] at h
    omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hle

private theorem mem_normalizer_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {t d q : G} (ht : t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (htQs : t ∉ Y.Qs 1)
    (hd : d ∈ Y.J 1) (hq : q ∈ Y.Qs 1) (htd : t * d * t⁻¹ = q * d) :
    d ∈ Subgroup.normalizer ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
  haveI hStfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (S_centralizer_le_Gi_one Y)
  have hSt_eq := S_centralizer_eq_Qs_sup_zpowers Y H ht htQs
  have hQsN : Y.J 1 ≤ Subgroup.normalizer (Y.Qs 1 : Set G) := J_one_le_normalizer_Qs_one Y H
  have hQs_le_St : Y.Qs 1 ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    Qs_one_le_S_centralizer Y
  have ha : t * d * t⁻¹ = q * d := htd
  have hdt : d * t * d⁻¹ = q⁻¹ * t := by
    have h1' : t * d = q * d * t := by
      calc t * d = (t * d * t⁻¹) * t := by group
        _ = (q * d) * t := by rw [ha]
    calc d * t * d⁻¹ = q⁻¹ * (q * (d * t * d⁻¹)) := by group
      _ = q⁻¹ * (q * d * t * d⁻¹) := by group
      _ = q⁻¹ * (t * d * d⁻¹) := by rw [← h1']
      _ = q⁻¹ * t := by group
  have hdtSt : q⁻¹ * t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    rw [hSt_eq]
    exact Subgroup.mul_mem_sup ((Y.Qs 1).inv_mem hq) (Subgroup.mem_zpowers t)
  have hpre : Y.Qs 1 ⊔ Subgroup.zpowers t ≤
      Subgroup.comap (MulAut.conj d).toMonoidHom
        (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap]
      change d * x * d⁻¹ ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)
      exact hQs_le_St ((Subgroup.mem_normalizer_iff.mp (hQsN hd) x).mp hx)
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_comap]
      show MulAut.conj d (t ^ k) ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G)
      rw [map_zpow]
      have hconjt : MulAut.conj d t = q⁻¹ * t := by
        rw [MulAut.conj_apply]; exact hdt
      rw [hconjt]
      exact (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).zpow_mem hdtSt k
  have hconj_le : conjSub d (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ≤
      Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
    have hpre' : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
        Subgroup.comap (MulAut.conj d).toMonoidHom
          (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) := by
      conv_lhs => rw [hSt_eq]
      exact hpre
    exact (Subgroup.map_le_iff_le_comap).mpr hpre'
  refine (Subgroup.mem_normalizer_iff_map_conj_eq
    (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))).mpr ?_
  exact Subgroup.eq_of_le_of_card_ge hconj_le
    (Subgroup.card_map_of_injective (MulAut.conj d).injective
      (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))).ge

private theorem J_neg_one_eq (Y : Setup Γ G) :
    Y.J (-1) = (Y.J 1).map (MulAut.conj (Y.τ ^ (-1 : ℤ))).toMonoidHom := by
  have h := Y.J_add (-1) 1
  rw [show (1 : ℤ) + 2 * (-1 : ℤ) = -1 by norm_num] at h
  exact h

private theorem Qs_neg_one_eq (Y : Setup Γ G) :
    Y.Qs (-1) = (Y.Qs 1).map (MulAut.conj (Y.τ ^ (-1 : ℤ))).toMonoidHom := by
  have h := Y.Qs_add (-1) 1
  rw [show (1 : ℤ) + 2 * (-1 : ℤ) = -1 by norm_num] at h
  exact h

private theorem S_centralizer_relIndex_J_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J (-1) ∧
      (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J (-1)) = 3 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1 |>.trans (Y.L_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  haveI hStfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (S_centralizer_le_Gi_one Y)
  have hSt2 : IsPGroup 2 ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    (St_sylow Y H).1.2.1
  have hStJ1 : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 := (St_sylow Y H).1.1
  have hrelSt : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J 1) = 3 :=
    (St_sylow Y H).2.2
  have hStneg : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.Gi (-1) :=
    S_centralizer_le_Gi_neg_one Y H
  have hStN : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.N :=
    (inf_le_right : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.centralizer (Y.K : Set G)).trans
      (Subgroup.centralizer_le_normalizer (Y.K : Set G))
  have hStJneg : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J (-1) :=
    le_oTwoPrime_of_isPGroup hSt2 (le_inf hStN hStneg)
  have hJneg := J_neg_one_eq Y
  have hcardJneg : Nat.card ↥(Y.J (-1)) = Nat.card ↥(Y.J 1) := by
    rw [hJneg]
    exact Subgroup.card_map_of_injective (MulAut.conj (Y.τ ^ (-1 : ℤ))).injective
      (K := Y.J 1)
  have hcardSt1 : Nat.card ↥(Y.J 1) = 3 * Nat.card ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) := by
    have h := Subgroup.relIndex_mul_card (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.J 1)
    rw [inf_eq_left.mpr hStJ1, hrelSt] at h
    exact h.symm
  have hrelSt_neg : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.J (-1)) = 3 := by
    have h := Subgroup.relIndex_mul_card
      (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (K := Y.J (-1))
    rw [inf_eq_left.mpr hStJneg] at h
    rw [hcardJneg, hcardSt1] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos
      (α := ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)))) h
  exact ⟨hStJneg, hrelSt_neg⟩


private theorem Qs_neg_one_le_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Qs (-1) ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1 |>.trans (Y.L_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  haveI hStfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (S_centralizer_le_Gi_one Y)
  haveI hJnegfin : Finite ↥(Y.J (-1)) := by
    have hcard : Nat.card ↥(Y.J (-1)) = Nat.card ↥(Y.J 1) := by
      rw [J_neg_one_eq Y]
      exact Subgroup.card_map_of_injective (MulAut.conj (Y.τ ^ (-1 : ℤ))).injective
        (K := Y.J 1)
    exact Nat.finite_of_card_ne_zero
      (by rw [hcard]; exact (Nat.card_pos (α := ↥(Y.J 1))).ne')
  have hSt2 : IsPGroup 2 ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
    (St_sylow Y H).1.2.1
  have hStJneg : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J (-1) :=
    (S_centralizer_relIndex_J_neg_one Y H).1
  have hrelSt_neg : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J (-1)) = 3 :=
    (S_centralizer_relIndex_J_neg_one Y H).2
  have hQsneg := Qs_neg_one_eq Y
  have hJneg := J_neg_one_eq Y
  have hQ' : Y.J (-1) ≤ Subgroup.normalizer (Y.Qs (-1) : Set G) := by
    rw [hQsneg, hJneg]
    exact conjSub_le_normalizer (J_one_le_normalizer_Qs_one Y H)
  have hpCore_neg : pCoreOf 2 (Y.J (-1)) = Y.Qs (-1) := by
    rw [hJneg]
    show pCoreOf 2 (conjSub (Y.τ ^ (-1 : ℤ)) (Y.J 1)) = Y.Qs (-1)
    rw [pCoreOf_conjSub, pCoreOf_J Y H]
    exact hQsneg.symm
  have hQs2neg : IsPGroup 2 (Y.Qs (-1)) := hpCore_neg ▸ pCoreOf_isPGroup' (Y.J (-1))
  have hStNQs : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤
      Subgroup.normalizer (Y.Qs (-1) : Set G) := hStJneg.trans hQ'
  have hsup2 : IsPGroup 2 ↥(Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) :=
    hQs2neg.to_sup_of_normal_left' hSt2 hStNQs
  have hsupJ : Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ≤ Y.J (-1) :=
    sup_le (hpCore_neg ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 (Y.J (-1))) hStJneg
  have hdiv3 : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) ∣ 3 := by
    have h := Subgroup.relIndex_mul_relIndex
      (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)))
      (L := Y.J (-1)) le_sup_right hsupJ
    rw [hrelSt_neg] at h
    exact ⟨_, h.symm⟩
  haveI hsupfin : Finite ↥(Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) :=
    Finite.of_injective (Subgroup.inclusion hsupJ) (Subgroup.inclusion_injective _)
  obtain ⟨k, hk⟩ := hsup2.exists_card_eq
  have hdiv2 : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) ∣ 2 ^ k := by
    have h := Subgroup.relIndex_mul_card
      (H := Y.S ⊓ Subgroup.centralizer (Y.K : Set G))
      (K := Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)))
    have hinf : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) ⊓
        (Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) =
        Y.S ⊓ Subgroup.centralizer (Y.K : Set G) := inf_eq_left.mpr le_sup_right
    rw [hinf, hk] at h
    exact ⟨Nat.card ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)), h.symm⟩
  have hone : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex
      (Y.Qs (-1) ⊔ (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) = 1 := by
    have hcop : Nat.Coprime 3 (2 ^ k) := (by norm_num : Nat.Coprime 3 2).pow_right k
    refine Nat.dvd_one.mp ?_
    rw [← hcop]
    exact Nat.dvd_gcd hdiv3 hdiv2
  exact le_sup_left.trans (Subgroup.relIndex_eq_one.mp hone)

private theorem Qs_neg_one_relIndex_S_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Qs (-1)).relIndex (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) = 2 := by
  have hQsneg := Qs_neg_one_eq Y
  have hJneg := J_neg_one_eq Y
  have hQsJneg : (Y.Qs (-1)).relIndex (Y.J (-1)) = 6 := by
    rw [hQsneg, hJneg,
      Subgroup.relIndex_map_map_of_injective (Y.Qs 1) (Y.J 1)
        (MulAut.conj (Y.τ ^ (-1 : ℤ))).injective]
    exact Qs_relIndex_J Y H
  have hQsneg_le : Y.Qs (-1) ≤ Y.S ⊓ Subgroup.centralizer (Y.K : Set G) :=
    Qs_neg_one_le_S_centralizer Y H
  have hStJneg : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J (-1) :=
    (S_centralizer_relIndex_J_neg_one Y H).1
  have hrelSt_neg : (Y.S ⊓ Subgroup.centralizer (Y.K : Set G)).relIndex (Y.J (-1)) = 3 :=
    (S_centralizer_relIndex_J_neg_one Y H).2
  have h := Subgroup.relIndex_mul_relIndex (H := Y.Qs (-1))
    (K := Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) (L := Y.J (-1)) hQsneg_le hStJneg
  rw [hQsJneg, hrelSt_neg] at h
  omega

theorem J_sup_Q_and_inv (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.L 1 = Y.J 1 ⊔ Y.Q 1 ∧
      ∀ t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G), t ∉ Y.Qs 1 →
        ∀ d ∈ Y.J 1, orderOf d = 3 → t * d * t⁻¹ * d ∈ Y.Qs 1 := by
  constructor
  · rw [J_eq_L_centralizer Y H]
    exact (L_one_eq_centralizer_sup_Q Y H).symm
  · intro t htSt htQs d hdJ hd3
    haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
    haveI hJfin : Finite ↥(Y.J 1) :=
      Finite.of_injective
        (Subgroup.inclusion (Y.J_le_L 1 |>.trans (Y.L_le_Gi 1)))
        (Subgroup.inclusion_injective _)
    haveI hQfin : Finite ↥(Y.Qs 1) :=
      Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
        (Subgroup.inclusion_injective _)
    haveI hStfin : Finite ↥(Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) :=
      finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _)
        (S_centralizer_le_Gi_one Y)
    haveI : Finite ↥(Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G)) := hQfin
    have hQsJ : Y.Qs 1 ≤ Y.J 1 := Qs_le_J Y
    have hQsN : Y.J 1 ≤ Subgroup.normalizer (Y.Qs 1 : Set G) := J_one_le_normalizer_Qs_one Y H
    have hStJ : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ≤ Y.J 1 := (St_sylow Y H).1.1
    have hd3d : d ^ (3 : ℤ) = 1 := by
      have h := pow_orderOf_eq_one d
      rw [hd3] at h
      simpa using h
    have hsupd : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) ⊔ Subgroup.zpowers d = Y.J 1 :=
      S_centralizer_sup_zpowers_eq_J Y H hdJ hd3
    set A : Subgroup G := Y.Qs 1 ⊔ Subgroup.zpowers d with hAdef
    have hAJ : A ≤ Y.J 1 := sup_le hQsJ (Subgroup.zpowers_le.mpr hdJ)
    have hAJN : Y.J 1 ≤ Subgroup.normalizer (A : Set G) := by
      simpa [hAdef] using J_one_le_normalizer_Qs_sup_zpowers Y H hdJ hd3
    have htdt : t * d * t⁻¹ ∈ Y.Qs 1 ⊔ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp (hAJN (hStJ htSt)) d).mp
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
    have hsub_sup : (Y.Qs 1).subgroupOf A ⊔ (Subgroup.zpowers d).subgroupOf A = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self A
    haveI hQsnormalA : ((Y.Qs 1).subgroupOf A).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (hAJ.trans hQsN)
    have hmemA : (⟨t * d * t⁻¹, htdt⟩ : ↥A) ∈
        (Y.Qs 1).subgroupOf A ⊔ (Subgroup.zpowers d).subgroupOf A := by
      rw [hsub_sup]
      exact Subgroup.mem_top _
    obtain ⟨q', hq', z', hz', hqz'⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := (Y.Qs 1).subgroupOf A)
        (t := (Subgroup.zpowers d).subgroupOf A)).mp hmemA
    set q : G := (q' : A).1 with hqdef
    set z : G := (z' : A).1 with hzdef
    have hq : q ∈ Y.Qs 1 := by rw [hqdef]; exact Subgroup.mem_subgroupOf.mp hq'
    have hz : z ∈ Subgroup.zpowers d := by rw [hzdef]; exact Subgroup.mem_subgroupOf.mp hz'
    have hqz : q * z = t * d * t⁻¹ := by
      have h := congrArg (fun y : ↥A => (y : G)) hqz'
      simpa [hqdef, hzdef] using h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hord_a : orderOf (t * d * t⁻¹) = 3 := by
      have h1 : t * d * t⁻¹ = MulAut.conj t d := by rw [MulAut.conj_apply]
      rw [h1]
      exact (orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective d).trans hd3
    have hred : q * d ^ i = q * d ^ (i % 3) := by rw [zpow_eq_zpow_emod i hd3d]
    have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by
      have h1 := Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0)
      have h2 := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 3)
      omega
    have hSt_eq : Y.S ⊓ Subgroup.centralizer (Y.K : Set G) =
        Y.Qs 1 ⊔ Subgroup.zpowers t :=
      S_centralizer_eq_Qs_sup_zpowers Y H htSt htQs
    rcases hcases with h0 | h1 | h2'
    ·
      exfalso
      have haQ : t * d * t⁻¹ ∈ Y.Qs 1 := by
        have : t * d * t⁻¹ = q := by rw [← hqz, ← hi, hred, h0, zpow_zero, mul_one]
        rw [this]; exact hq
      have hdvd : orderOf (t * d * t⁻¹) ∣
          Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G)) :=
        (Subgroup.orderOf_coe ⟨_, haQ⟩).symm ▸ orderOf_dvd_natCard _
      rw [hord_a] at hdvd
      obtain ⟨k, hk⟩ := ((pCoreOf_isPGroup' (Y.Gi 1)).to_le
        (inf_le_left : Y.Qs 1 ≤ Y.Q 1)).exists_card_eq
      rw [hk] at hdvd
      exact absurd ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdvd) (by norm_num)
    ·
      exfalso
      have ha : t * d * t⁻¹ = q * d := by rw [← hqz, ← hi, hred, h1, zpow_one]
      have hdN : d ∈ Subgroup.normalizer
          ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) :=
        mem_normalizer_S_centralizer Y H htSt htQs hdJ hq ha
      have hJN : Y.J 1 ≤ Subgroup.normalizer
          ((Y.S ⊓ Subgroup.centralizer (Y.K : Set G)) : Set G) := by
        rw [← hsupd]
        exact sup_le (Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hdN)
      exact S_centralizer_not_normal_of_trans Y H
        (fun w hw => J_trans Y H (Y.vert 0) w (by simpa using (Y.adj 0).symm) hw) hJN
    ·
      have ha : t * d * t⁻¹ = q * d ^ (2 : ℤ) := by rw [← hqz, ← hi, hred, h2']
      have hEq : t * d * t⁻¹ * d = q := by
        rw [ha]
        calc (q * d ^ (2 : ℤ)) * d = q * (d ^ (2 : ℤ) * d) := by group
          _ = q * (d ^ (2 : ℤ) * d ^ (1 : ℤ)) := by rw [zpow_one]
          _ = q * d ^ ((2 : ℤ) + 1) := by rw [zpow_add]
          _ = q * d ^ (3 : ℤ) := by rw [show (2 : ℤ) + 1 = 3 by norm_num]
          _ = q := by rw [hd3d, mul_one]
      rw [hEq]
      exact hq

theorem goldschmidt_small_apply (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    IsMulCommutative (Y.Qs 1) ∧
      Nat.card ↥(Y.Qs 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G)) ≤ 2 ∧
      Nat.card (centerOf (Y.S ⊓ Subgroup.centralizer (Y.K : Set G))) ≤ 4 ∧
        (4 ≤ Nat.card (Y.Qs 1) → IsElemAbelian 2 (Y.Qs 1) ∧
          Nat.card ↥(⁅Y.Qs 1, Subgroup.zpowers d⁆) = 4 ∧
          Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) =
            Y.Qs 1 ⊓ Subgroup.centralizer (Y.J 1 : Set G) ∧
          Y.J 1 ≤ Subgroup.normalizer ((⁅Y.Qs 1, Subgroup.zpowers d⁆ : Subgroup G) : Set G) ∧
          ∀ t ∈ Y.S ⊓ Subgroup.centralizer (Y.K : Set G), t ∉ Y.Qs 1 →
            Nat.card ↥(⁅Y.Qs 1, Subgroup.zpowers d⁆ ⊓
              Subgroup.centralizer ({t} : Set G)) = 2) := by
  set St : Subgroup G := Y.S ⊓ Subgroup.centralizer (Y.K : Set G) with hStdef
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hJfin : Finite ↥(Y.J 1) :=
    Finite.of_injective
      (Subgroup.inclusion (Y.J_le_L 1 |>.trans (Y.L_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  haveI hCfin : Finite ↥St := by
    rw [hStdef]
    exact finite_of_le_stabilizer Y.hyp (α := Y.vert 1) (H := _) (S_centralizer_le_Gi_one Y)
  haveI hGnegfin : Finite ↥(Y.Gi (-1)) := Y.hyp.finite_stab (Y.vert (-1))
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  haveI hQsnegfin : Finite ↥(Y.Qs (-1)) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi (-1))))
      (Subgroup.inclusion_injective _)
  have hSt2 : IsPGroup 2 ↥St := (St_sylow Y H).1.2.1
  have hStJ1 : St ≤ Y.J 1 := (St_sylow Y H).1.1
  have hrelSt : St.relIndex (Y.J 1) = 3 := (St_sylow Y H).2.2
  have hrelQs : (Y.Qs 1).relIndex St = 2 := (St_sylow Y H).2.1
  have hStneg : St ≤ Y.Gi (-1) := by
    rw [hStdef]
    exact S_centralizer_le_Gi_neg_one Y H
  have hStJneg : St ≤ Y.J (-1) := by
    rw [hStdef]
    exact (S_centralizer_relIndex_J_neg_one Y H).1
  have hJneg := J_neg_one_eq Y
  have hQsneg := Qs_neg_one_eq Y

  have hQ' : Y.J (-1) ≤ Subgroup.normalizer (Y.Qs (-1) : Set G) := by
    rw [hQsneg, hJneg]
    exact conjSub_le_normalizer (J_one_le_normalizer_Qs_one Y H)
  have hQsneg_le : Y.Qs (-1) ≤ St := by
    rw [hStdef]
    exact Qs_neg_one_le_S_centralizer Y H
  have hQsneg_rel : (Y.Qs (-1)).relIndex St = 2 := by
    rw [hStdef]
    exact Qs_neg_one_relIndex_S_centralizer Y H
  have hsupd : St ⊔ Subgroup.zpowers d = Y.J 1 := by
    rw [hStdef]
    exact S_centralizer_sup_zpowers_eq_J Y H hd hd3
  have hQs_le_St : Y.Qs 1 ≤ St := by
    rw [hStdef]
    exact Qs_one_le_S_centralizer Y
  have hJd : Y.J 1 = St ⊔ Subgroup.zpowers d ⊔ Y.Qs 1 := by
    refine le_antisymm ?_ ?_
    · rw [hsupd]
      exact le_sup_left
    · calc St ⊔ Subgroup.zpowers d ⊔ Y.Qs 1 ≤ St ⊔ Subgroup.zpowers d :=
            sup_le le_rfl (hQs_le_St.trans le_sup_left)
        _ = Y.J 1 := hsupd
  have hStGi : St ≤ Y.Gi 1 := by
    rw [hStdef]
    exact S_centralizer_le_Gi_one Y
  have hc : ∀ X : Subgroup G, X ≤ St →
      Y.J 1 ≤ Subgroup.normalizer (X : Set G) →
      Y.J (-1) ≤ Subgroup.normalizer (X : Set G) → X = ⊥ := by
    intro X hX h1 hneg
    exact eq_bot_of_normal_J Y H (hSt2.to_le hX) h1 hneg (hX.trans (le_inf hStneg hStGi))
  exact goldschmidt_small (J := Y.J 1) (J' := Y.J (-1)) (Qs := Y.Qs 1) (Qs' := Y.Qs (-1))
    (St := St) (d := d)
    (J_one_le_normalizer_Qs_one Y H) hQ' (sup_le hQs_le_St hQsneg_le)
    (le_inf hStJ1 hStJneg) hSt2 hrelSt
    hrelQs hQsneg_rel hJd hd3 ⟨Y.τ ^ (-1 : ℤ), hJneg.symm, hQsneg.symm⟩ hc (card_Qs_le Y H)

theorem card_Qs_inf_centralizer (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {d : G}
    (hd : d ∈ Y.J 1) (hd3 : orderOf d = 3) :
    Nat.card ↥(Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 := by
  haveI hGfin : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective _)
  by_cases h4 : 4 ≤ Nat.card (Y.Qs 1)
  · have h := goldschmidt_small_apply Y H hd hd3
    rw [(h.2.2.2 h4).2.2.1]
    exact h.2.1
  · push Not at h4
    have hQs2 : IsPGroup 2 (Y.Qs 1) :=
      (pCoreOf_isPGroup' (Y.Gi 1)).to_le (inf_le_left : Y.Qs 1 ≤ Y.Q 1)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQs2
    have hk2 : k ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have hge : 4 ≤ 2 ^ k := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hQle : Nat.card ↥(Y.Qs 1) ≤ 2 := by
      rw [hk]
      interval_cases k <;> norm_num
    calc Nat.card ↥(Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G))
        ≤ Nat.card ↥(Y.Qs 1) :=
          Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective inf_le_left)
      _ ≤ 2 := hQle

end Setup

end CFSG.Quasithin.St84
