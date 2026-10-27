module

public import CFSG.Quasithin.Vol2.E2TenSix
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.SimsE210

open CFSG.Open CFSG.QuasithinUnique

theorem conjSubgroup_eq_conjSub {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    conjSubgroup A g = B6.conjSub g⁻¹ A := by
  ext x
  rw [mem_conjSubgroup_iff, B6.mem_conjSub, inv_inv]

theorem isSylowTwoOf_pCoreOf_of_isTwoClosed {G : Type*} [Group G] [Finite G] {J : Subgroup G}
    (h : E1.IsTwoClosed J) : IsSylowTwoOf (pCoreOf 2 J) J := by
  obtain ⟨P, hP, hPn⟩ := h
  have hQJ : pCoreOf 2 J ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hQn : ((pCoreOf 2 J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  have h1 : P ≤ pCoreOf 2 J := CFSG.LieType.BorelTits.le_pCoreOf 2 hP.le hPn hP.isPGroup
  have h2 : pCoreOf 2 J ≤ P :=
    hP.le_of_normal hQJ hQn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
  rw [← le_antisymm h1 h2]
  exact hP

theorem natCard_star_eq_relIndex {Γ : Type} [Group Γ] {M X V : Subgroup Γ} (hVX : V ≤ X) :
    Nat.card (E2.star M X V) = (kerIn M X ⊓ V).relIndex V := by
  have h := Subgroup.relIndex_ker (V.subgroupOf X) (QuotientGroup.mk' ((kerIn M X).subgroupOf X))
  rw [QuotientGroup.ker_mk', Subgroup.relIndex_subgroupOf hVX] at h
  rw [Subgroup.inf_relIndex_right]
  exact h.symm

theorem pair_of_data {Γ : Type} [Group Γ] [Finite Γ] {X M T V : Subgroup Γ} {g : Γ}
    (hT : IsSylowIn 2 T X) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set Γ))
    (hV : IsElemAbelian 2 V) (hNM : X ⊓ Subgroup.normalizer (V : Set Γ) ≤ M) (hMX : M ≤ X)
    (hVM : V ≤ pCoreOf 2 M) (hJ2 : E1.IsTwoClosed (kerIn M X)) (hg : g ∈ X)
    (hgen : X = V ⊔ conjSubgroup V g) : E2.Pair X T M V g⁻¹ where
  sylow := hT
  le_T := hVT
  normal_T := hTV
  elem := hV
  normalizer_le := hNM
  le_X := hMX
  le_pCoreOf := hVM
  closed := isSylowTwoOf_pCoreOf_of_isTwoClosed hJ2
  mem := X.inv_mem hg
  gen := by rw [← conjSubgroup_eq_conjSub]; exact hgen

private theorem exists_two_pow_mem_sup {Γ : Type*} [Group Γ] {D J : Subgroup Γ}
    (hDJ : D ≤ Subgroup.normalizer (J : Set Γ)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ J) :
    ∀ y ∈ D ⊔ J, ∃ k : ℕ, y ^ 2 ^ k ∈ J := by
  intro y hy
  have hy' : y ∈ (↑(D ⊔ J) : Set Γ) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D J hDJ] at hy'
  obtain ⟨d, hd, j, hj, rfl⟩ := hy'
  obtain ⟨k, hk⟩ := hD d hd
  refine ⟨k, ?_⟩
  have key : ∀ n : ℕ, ∃ j' ∈ J, (d * j) ^ n = d ^ n * j' := by
    intro n
    induction n with
    | zero => exact ⟨1, J.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨j', hj', hn⟩ := ih
      have hconj : d⁻¹ * j' * d ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp (hDJ (D.inv_mem hd)) j').mp hj'
        simpa using this
      refine ⟨d⁻¹ * j' * d * j, J.mul_mem hconj hj, ?_⟩
      rw [pow_succ, hn, pow_succ]
      group
  obtain ⟨j', hj', h⟩ := key (2 ^ k)
  rw [h]
  exact J.mul_mem hk hj'

private theorem le_normalizer_sup_of_le {Γ : Type*} [Group Γ] {X D J : Subgroup Γ}
    (hD : X ≤ Subgroup.normalizer (D : Set Γ)) (hJ : X ≤ Subgroup.normalizer (J : Set Γ)) :
    X ≤ Subgroup.normalizer ((D ⊔ J : Subgroup Γ) : Set Γ) := by
  intro x hx
  have hD' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD hx)
  have hJ' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hJ hx)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by rw [Subgroup.map_sup, hD', hJ'])

theorem e2_10_parts (Γ : Type) [Group Γ] [Finite Γ] (X M T V : Subgroup Γ) (g : Γ)
    (hT : IsSylowIn 2 T X) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set Γ))
    (hV : IsElemAbelian 2 V) (hNM : X ⊓ Subgroup.normalizer (V : Set Γ) ≤ M) (hMX : M ≤ X)
    (hVM : V ≤ pCoreOf 2 M) (hJ2 : E1.IsTwoClosed (kerIn M X)) (hg : g ∈ X)
    (hgen : X = V ⊔ conjSubgroup V g)
    (J B P Z : Subgroup Γ) (hJ : J = kerIn M X) (hB : B = J ⊓ V)
    (hP : P = B ⊔ conjSubgroup B g) (hZ : Z = V ⊓ conjSubgroup V g) :
    (((P : Set Γ) = (B : Set Γ) * (conjSubgroup B g : Set Γ)) ∧
      X ≤ Subgroup.normalizer (P : Set Γ) ∧ Z ≤ P ∧
      Z ≤ Subgroup.centralizer (X : Set Γ)) ∧
    ((∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z ∧ x ^ 2 ∈ Z) ∧
      (B ⊔ Z) ⊓ (conjSubgroup B g ⊔ Z) = Z ∧ ⁅⁅P, V⁆, V⁆ ≤ Z ∧
      ∀ x ∈ P, (∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ Z) ↔ x ∈ B ⊔ Z) ∧
    H13.IsO2Trivial X J ∧
    ⁅X, J⁆ ≤ P ∧
    ⁅⁅⁅V, conjSubgroup B g⁆, conjSubgroup B g⁆, conjSubgroup B g⁆ = ⊥ ∧
    (Nat.card (E2.star M X V) = 2 →
      P = pCoreOf 2 X ∧ pCoreOf 2 X = J ∧
        ∃ m : ℕ, Odd m ∧ Nonempty (E2.StarQuot M X ≃* DihedralGroup m) ∧
          ∀ [(P.subgroupOf X).Normal],
            Nonempty (↥X ⧸ P.subgroupOf X ≃* E2.StarQuot M X)) ∧
    (V < X → CharTwo X → ⁅V, conjSubgroup B g⁆ ≠ ⊥) := by
  have hp : E2.Pair X T M V g⁻¹ := pair_of_data hT hVT hTV hV hNM hMX hVM hJ2 hg hgen
  subst hJ hB hP hZ
  rw [conjSubgroup_eq_conjSub (kerIn M X ⊓ V) g, conjSubgroup_eq_conjSub V g]
  set B : Subgroup Γ := kerIn M X ⊓ V with hBdef
  set A : Subgroup Γ := B6.conjSub g⁻¹ B with hAdef
  set Z : Subgroup Γ := V ⊓ B6.conjSub g⁻¹ V with hZdef
  set P : Subgroup Γ := B ⊔ A with hPdef
  have hPQ : P ≤ pCoreOf 2 X := hp.P_le_pCoreOf
  have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hPX : X ≤ Subgroup.normalizer (P : Set Γ) := hp.le_normalizer_P
  have hZB : Z ≤ B := hp.inf_conj_le_kerIn_inf
  have hZA : Z ≤ A := hp.inf_conj_le_conjSub
  have hAP : A ≤ P := le_sup_right
  have hAX : A ≤ X := hp.A_le_pCoreOf.trans hQX
  refine ⟨⟨?_, hPX, hp.inf_conj_le_P, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [SetLike.mem_coe, Set.mem_mul]
    exact hp.mem_P_iff
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    exact fun x hx => (hp.mem_center hz hx).symm
  · exact fun x hx y hy => hp.commutator_sq_mem_Z hx hy
  · rw [sup_eq_left.2 hZB, sup_eq_left.2 hZA]
    exact hp.B_inf_A
  · have hPV : ⁅P, V⁆ ≤ B := by
      refine Subgroup.commutator_le.2 fun p hpP v hv => ?_
      have h1 := hp.commutator_mem_B hv (hPQ hpP)
      have e : ⁅p, v⁆ = (v * p * v⁻¹ * p⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact B.inv_mem h1
    refine Subgroup.commutator_le.2 fun x hx v hv => ?_
    have hxB : x ∈ B := hPV hx
    have hcomm : x * v = v * x := hp.comm hxB.2 hv
    have e : ⁅x, v⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [hcomm]
      group
    rw [e]
    exact Z.one_mem
  · intro x hx
    rw [sup_eq_left.2 hZB]
    constructor
    · intro h
      refine hp.mem_B_of_commutator_mem_Z hx fun v hv => ?_
      have e : v * x * v⁻¹ * x⁻¹ = (x * v * x⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact Z.inv_mem (h v hv)
    · intro hxB v hv
      have hcomm : x * v = v * x := hp.comm hxB.2 hv
      have e : x * v * x⁻¹ * v⁻¹ = 1 := by
        rw [hcomm]
        group
      rw [e]
      exact Z.one_mem
  · intro D hDX hXD hD
    have hJn : X ≤ Subgroup.normalizer (kerIn M X : Set Γ) := le_normalizer_kerIn M X
    have h := hp.le_kerIn_of_isTwoQuotient (D := D ⊔ kerIn M X)
      (sup_le hDX (kerIn_le.trans hMX)) (le_normalizer_sup_of_le hXD hJn) le_sup_right
      (exists_two_pow_mem_sup (hDX.trans hJn) hD)
    exact le_sup_left.trans h
  · refine Subgroup.commutator_le.2 fun x hx j hj => ?_
    exact hp.commutator_kerIn_mem_P hx hj
  · have h1 : ⁅V, A⁆ ≤ P := by
      refine Subgroup.commutator_le.2 fun v hv a ha => ?_
      have h2 := (Subgroup.mem_normalizer_iff.mp (hPX (hp.V_le hv)) a).mp (hAP ha)
      exact P.mul_mem h2 (P.inv_mem (hAP ha))
    have h2 : ⁅⁅V, A⁆, A⁆ ≤ Z := by
      refine Subgroup.commutator_le.2 fun x hx a ha => ?_
      exact (hp.commutator_sq_mem_Z (h1 hx) (hAP ha)).1
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.2 fun x hx a ha => ?_
    have hcomm : x * a = a * x := hp.mem_center (h2 hx) (hAX ha)
    have e : ⁅x, a⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [hcomm]
      group
    rw [e]
    exact Subgroup.one_mem _
  · intro hcard
    obtain ⟨h1, h2, m, hm, ⟨e⟩⟩ : P = pCoreOf 2 X ∧ pCoreOf 2 X = kerIn M X ∧
        ∃ m : ℕ, Odd m ∧ Nonempty (E2.StarQuot M X ≃* DihedralGroup m) :=
      hp.e2_10_six ((natCard_star_eq_relIndex hp.V_le).symm.trans hcard)
    refine ⟨h1, h2, m, hm, ⟨e⟩, ?_⟩
    intro hN
    exact ⟨QuotientGroup.quotientMulEquivOfEq (by rw [h1, h2])⟩
  · intro hVX hchar hbot
    refine hp.not_le_centralizer hchar hVX.ne' ?_
    rw [Subgroup.commutator_comm] at hbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot

end CFSG.Quasithin.SimsE210
