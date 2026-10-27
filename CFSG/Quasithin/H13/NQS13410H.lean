module

public import CFSG.Quasithin.H13.U3L14Blk
public import CFSG.Quasithin.H13.U3S1344A

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.U3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_sylow_L1T (S : A6.Setting134 G T L V) :
    IsSylowTwoOf T (L₁Of L (fsuV1 T V) ⊔ T) :=
  A5.isSylowTwoOf_of_le S.h13.sylow le_sup_right

theorem s134_R_le_T (S : A6.Setting134 G T L V) :
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
  pCoreOf_two_le_of_sylowIn le_sup_right (s134_sylow_L1T S).2.1 (s134_sylow_L1T S).2.2

theorem s134_pCoreOf_L1_le_R (S : A6.Setting134 G T L V) :
    pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      ((s134_T_le_normalizer_L1 S).trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)))
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem s134_comm_R_mem (S : A6.Setting134 G T L V) {r y : G}
    (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hy : y ∈ L₁Of L (fsuV1 T V)) :
    r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  have h1 : r * y * r⁻¹ * y⁻¹ ∈ L₁ :=
    mul_mem ((mem_normalizer_iff.mp (s134_T_le_normalizer_L1 S (s134_R_le_T S hr)) y).mp hy)
      (inv_mem hy)
  have h2 : r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (L₁ ⊔ T) := by
    have h3 : y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 (L₁ ⊔ T) :=
      (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T)
        (mem_sup_left hy)) _).mp (inv_mem hr)
    have : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
    rw [this]
    exact mul_mem hr h3
  have hle : L₁ ⊓ pCoreOf 2 (L₁ ⊔ T) ≤ pCoreOf 2 L₁ :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => inf_normalizer_le_normalizer_inf ⟨le_normalizer hl,
        LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hl)⟩)
      ((LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ T)).to_le inf_le_right)
  exact hle (mem_inf.2 ⟨h1, h2⟩)

theorem s134_pCoreOf_L_le_R (S : A6.Setting134 G T L V) :
    pCoreOf 2 L ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := (oTwoRes_le _).trans inf_le_left
  have hnL : L ⊔ T ≤ normalizer (pCoreOf 2 L : Set G) :=
    sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (S.T_le_NL.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hQT : pCoreOf 2 L ≤ T :=
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hnL
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)).trans
      (pCoreOf_two_le_of_sylowIn le_sup_right (U3.s134_sylow_LT S).2.1 (U3.s134_sylow_LT S).2.2)
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (sup_le (hL1L.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 L)) (le_sup_right.trans hnL))
    (LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem s134_V_le_blockU (S : A6.Setting134 G T L V) : V ≤ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : V ≤ L := by
    rw [← S.irr.2.2.2.1]
    exact le_normalizer_iff_commutator_le_right.mp (S.V_le_T.trans S.T_le_NL)
  have hVQ : V ≤ pCoreOf 2 L :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL S.irr.2.2.1 S.isPGroup_V
  rw [← S.irr.2.2.2.1]
  exact commutator_mono hVQ le_rfl

theorem s134_relIndex_R_le_sixteen (S : A6.Setting134 G T L V) (hB : H13.IsA6Block L) {x : G}
    (hx : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) :
    (centralizer ({x} : Set G)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUZ, hLQ⟩ := block_cards (Or.inr hB)
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set Q := pCoreOf 2 L with hQ
  set C := centralizer ({x} : Set G) with hC
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hxL : x ∈ L := hL1L hx
  have hQ2 : IsPGroup 2 Q := LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hLQn : L ≤ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hUQ : blockU L ≤ Q := le_normalizer_iff_commutator_le_left.mp hLQn
  have hU2 : IsPGroup 2 (blockU L) := hQ2.to_le hUQ
  have hxQ : x ∈ normalizer (Q : Set G) := hLQn hxL
  have hxU : x ∈ normalizer (blockU L : Set G) :=
    mem_normalizer_commutator (hLQn hxL) (le_normalizer hxL)
  have hQU : Q ≤ normalizer (blockU L : Set G) := fun q hq =>
    mem_normalizer_commutator (le_normalizer hq)
      (le_normalizer (LieType.BorelTits.pCoreOf_le 2 L hq))
  have hxV1 : x ∈ centralizer (fsuV1 T V : Set G) :=
    s134_centralizes_V1 S (S.frame.L_le hxL) (mem_inf.1 (oTwoRes_le _ hx)).2
  have hV1U : fsuV1 T V ≤ blockU L := inf_le_left.trans (s134_V_le_blockU S)
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZV1C : blockZ L ⊔ fsuV1 T V ≤ C ⊓ blockU L := by
    refine sup_le (le_inf (fun z hz => ?_) hZU) (le_inf (fun v hv => ?_) hV1U)
    · rw [hC, mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp (mem_inf.mp hz).2) x hxL).symm
    · rw [hC, mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hxV1) v hv
  have hcU8 : C.relIndex (blockU L) ≤ 8 := by
    have h1 := relIndex_mul_relIndex (blockZ L) (blockZ L ⊔ fsuV1 T V) (blockU L) le_sup_left
      (sup_le hZU hV1U)
    have h2 : 2 ≤ (blockZ L).relIndex (blockZ L ⊔ fsuV1 T V) := by
      have h3 : (blockZ L).relIndex (blockZ L ⊔ fsuV1 T V) ≠ 1 := fun h3 => by
        have h4 := relIndex_eq_one.mp h3
        have h5 : fsuV1 T V ≤ V ⊓ centralizer (L : Set G) :=
          le_inf inf_le_left (fun v hv => (mem_inf.mp (h4 (mem_sup_right hv))).2)
        have h6 := Subgroup.card_le_of_le h5
        rw [S.card_V1, S.card_ZV] at h6
        omega
      have h4 : (blockZ L).relIndex (blockZ L ⊔ fsuV1 T V) ≠ 0 :=
        index_ne_zero_of_finite (H := (blockZ L).subgroupOf (blockZ L ⊔ fsuV1 T V))
      omega
    have h5 : (blockZ L ⊔ fsuV1 T V).relIndex (blockU L) ≤ 8 := by
      by_contra h6
      have : 16 < (blockZ L).relIndex (blockU L) := by
        rw [← h1]
        nlinarith
      omega
    calc C.relIndex (blockU L) = (C ⊓ blockU L).relIndex (blockU L) :=
          (inf_relIndex_right C (blockU L)).symm
      _ ≤ (blockZ L ⊔ fsuV1 T V).relIndex (blockU L) :=
          relIndex_le_of_le_left hZV1C
            (index_ne_zero_of_finite (H := (blockZ L ⊔ fsuV1 T V).subgroupOf (blockU L)))
      _ ≤ 8 := h5
  have hcU : C.relIndex (blockU L) ≤ 4 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU2
    exact le_four_of_le_eight (relIndex_centralizer_modEq_one hx3 hxU hU2)
      (hn ▸ index_dvd_card _) hcU8
  have hcommQ : ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ blockU L := by
    intro q hq
    have h := commutator_mem_commutator hxL hq
    rw [commutator_comm] at h
    rwa [commutatorElement_def] at h
  have hcQ : C.relIndex Q = C.relIndex (blockU L) := by
    have h1 := sup_inf_centralizer_eq hx3 hU2 hUQ hQU hxU hcommQ
    have hmul := relIndex_centralizer_eq_mul (x := x) hUQ hQU
    rw [h1, relIndex_self, one_mul] at hmul
    exact hmul
  have hQRL : Q ≤ R ⊓ L := le_inf (s134_pCoreOf_L_le_R S) (LieType.BorelTits.pCoreOf_le 2 L)
  have hRL2 : IsPGroup 2 ↥(R ⊓ L) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 (L₁ ⊔ T)).to_le inf_le_left
  have hRLQ : R ⊓ L ≤ normalizer (Q : Set G) := inf_le_right.trans hLQn
  have hxRL : x ∈ normalizer ((R ⊓ L : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T)
      (mem_sup_left hx), le_normalizer hxL⟩
  have h8 : Q.relIndex (R ⊓ L) ≤ 8 := by
    have h1 := relIndex_mul_relIndex Q (R ⊓ L) L hQRL inf_le_right
    have hdvd : Q.relIndex (R ⊓ L) ∣ Q.relIndex L := Dvd.intro _ h1
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hRL2
    have hdvd2 : Q.relIndex (R ⊓ L) ∣ 2 ^ n := hn ▸ index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    rw [hk] at hdvd ⊢
    by_contra h9
    have hk4 : 4 ≤ k := by
      by_contra h10
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h16 : 2 ^ 4 ∣ Q.relIndex L := (Nat.pow_dvd_pow 2 hk4).trans hdvd
    rcases hLQ with h | h <;> rw [h] at h16 <;> norm_num at h16
  have hcRL : C.relIndex (R ⊓ L) ≤ 4 * C.relIndex Q := by
    rw [relIndex_centralizer_eq_mul (x := x) hQRL hRLQ]
    exact Nat.mul_le_mul_right _ (relIndex_sup_le_four hx3 hRL2 hQRL hRLQ hxQ hxRL h8)
  have hRn : R ≤ normalizer ((R ⊓ L : Subgroup G) : Set G) := fun r hr =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hr, S.T_le_NL (s134_R_le_T S hr)⟩
  have hcommR : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ R ⊓ L := by
    intro r hr
    have h := s134_comm_R_mem S hr hx
    have h' : x * r * x⁻¹ * r⁻¹ = (r * x * r⁻¹ * x⁻¹)⁻¹ := by group
    rw [h']
    exact mem_inf.mpr ⟨s134_pCoreOf_L1_le_R S (inv_mem h),
      hL1L (LieType.BorelTits.pCoreOf_le 2 L₁ (inv_mem h))⟩
  have hcR : C.relIndex R = C.relIndex (R ⊓ L) := by
    have h2 := sup_inf_centralizer_eq hx3 hRL2 inf_le_left hRn hxRL hcommR
    have hmul := relIndex_centralizer_eq_mul (x := x) (inf_le_left : R ⊓ L ≤ R) hRn
    rw [h2, relIndex_self, one_mul] at hmul
    exact hmul
  rw [hcR]
  omega

end CFSG.Quasithin.H13.NQS134
