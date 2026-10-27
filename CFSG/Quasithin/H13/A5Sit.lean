module

public import CFSG.Quasithin.H13.A5HBar
public import CFSG.Quasithin.EmptyFaithful.QTKELocal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff piQ_eq_iff preQ mem_preQ
  preQ_le le_normalizer_preQ perm3_cube_of_odd)

structure A5Sit (G : Type) [Group G] [Finite G] (T V V₁ V₃ L₁ H : Subgroup G) where
  L : Subgroup G
  h13 : QTH13 G T L
  hF : HypF91 T V L V₁ V₃ H
  L1_eq : L₁ = L₁Of L V₁
  card_V : Nat.card V = 16
  card_V3 : Nat.card V₃ = 8
  nonabelian : ¬ IsElemAbelian 2 (conjClosure V₃ H)
  isPGroup_sup : ∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V)
  comm_centralizer : ⁅V, H ⊓ Subgroup.centralizer (V₃ : Set G)⁆ ≤ V₁
  commutator_V_L1 : ⁅V, L₁⁆ = V₃
  commutator_V3_L1 : ⁅V₃, L₁⁆ = V₃
  NV_le : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem V_le_H : V ≤ H := S.hF.V_le_H

theorem T_le_H : T ≤ H := S.hF.T_le_H

theorem V1_le_V3 : V₁ ≤ V₃ := S.hF.V₁_le_Vp

theorem V3_le_V : V₃ ≤ V := S.hF.Vp_le_V

theorem V1_le_V : V₁ ≤ V := S.hF.V₁_le_V

theorem card_V1 : Nat.card V₁ = 2 := S.hF.card_V₁

theorem elemAbelian_V : IsElemAbelian 2 V := S.hF.elemAbelian

theorem isPGroup_T : IsPGroup 2 T := S.hF.sylow.2.1

theorem sq_eq_one_of_mem_V {v : G} (hv : v ∈ V) : v * v = 1 := by
  rw [← pow_two]
  exact S.elemAbelian_V.2 v hv

theorem L1_le_H : L₁ ≤ H := by
  rw [S.L1_eq]
  exact le_sup_left.trans S.hF.L₁T_le_H

theorem T_le_normalizer_L1 : T ≤ Subgroup.normalizer (L₁ : Set G) := by
  rw [S.L1_eq]
  exact A5.le_normalizer_oTwoRes_of_le_normalizer
    (F7.le_normalizer_inf S.hF.normalizes_L (S.hF.T_normalizes_V₁.trans Subgroup.le_normalizer))

theorem relIndex_V3 : V₃.relIndex V = 2 := by
  have h := Subgroup.relIndex_mul_card V₃ V
  rw [inf_eq_left.2 S.V3_le_V, S.card_V3, S.card_V] at h
  omega

theorem not_V_le : ¬ V ≤ pCoreOf 2 H := fun h => S.nonabelian (S.hF.F94_1 h)

theorem Q_le_T : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf S.hF.sylow_H

theorem U_le_Q : conjClosure V₃ H ≤ pCoreOf 2 H := S.hF.conjClosure_Vp_le_pCoreOf

theorem pCoreOf_H_ne_bot : pCoreOf 2 H ≠ ⊥ := fun h =>
  S.hF.V₁_ne_bot (le_bot_iff.1 (h ▸ S.hF.V₁_le_pCoreOf))

theorem pRank_H_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p H ≤ 2 :=
  pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke S.pCoreOf_H_ne_bot hp hp2

theorem pCore_two_Hstar : CFSG.Open.pCore 2 (Hstar H) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := S.hF
  set P := CFSG.Open.pCore 2 (Hstar H)
  have hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set D := preQ H P
  have hDQ : D ≤ pCoreOf 2 H := by
    rw [hF.F92_3.1]
    refine hF.F92_1_reduced (preQ_le H P) (le_normalizer_preQ H P) fun d hd => ?_
    obtain ⟨hdH, hdP⟩ := mem_preQ.1 hd
    obtain ⟨k, hk⟩ := hPp ⟨_, hdP⟩
    refine ⟨k, ?_⟩
    rw [← hF.F92_3.1]
    have h1 : piQ H (⟨d, hdH⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    exact (piQ_eq_one_iff _).1 h1
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨x, rfl⟩ := piQ_surjective H a
  rw [Subgroup.mem_bot, piQ_eq_one_iff]
  exact hDQ (mem_preQ.2 ⟨x.2, ha⟩)

theorem pRank_Hstar_le_two : CFSG.Open.pRank 3 (⊤ : Subgroup (Hstar H)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 3 ∣ Nat.card ↥((pCoreOf 2 H).subgroupOf H) := by
    have hp : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf H) :=
      (pCoreOf_isPGroup 2 H).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).symm
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN, pRank_top_subtype]
  exact S.pRank_H_le_two Nat.prime_three (by norm_num)

theorem F956 (hF956 : A5.StmtF956i) {h : G} (hh : h ∈ H)
    (hI : ¬ ∀ y ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 H) :
    IsQ8Sq ↥(V₃ ⊔ conjSub h⁻¹ V₃) ∧
      ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
        Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
          Equiv.Perm (Fin 3)) :=
  hF956 G T V S.L V₁ V₃ H S.hF S.relIndex_V3 S.not_V_le S.isPGroup_sup S.comm_centralizer
    (S.card_V.trans (by norm_num)) h hh hI

theorem I_S3 (hF956 : A5.StmtF956i) {h : G} (hh : h ∈ H)
    (hI : ¬ ∀ y ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 H) :
    ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
      Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
        Equiv.Perm (Fin 3)) :=
  (S.F956 hF956 hh hI).2

theorem cube_mem_of_odd (hF956 : A5.StmtF956i) {h : G} (hh : h ∈ H)
    (hI : ¬ ∀ y ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, y ^ 2 ^ n ∈ pCoreOf 2 H)
    {y : G} (hy : y ∈ V ⊔ conjSub h⁻¹ V) {m : ℕ} (hm : Odd m) (hym : y ^ m ∈ pCoreOf 2 H) :
    y ^ 3 ∈ pCoreOf 2 H := by
  obtain ⟨hN, ⟨e⟩⟩ := S.I_S3 hF956 hh hI
  set I := V ⊔ conjSub h⁻¹ V
  set π := QuotientGroup.mk' ((pCoreOf 2 H).subgroupOf I)
  have hπ1 : ∀ z : ↥I, π z = 1 ↔ (z : G) ∈ pCoreOf 2 H := fun z => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hm1 : e (π ⟨y, hy⟩) ^ m = 1 := by
    rw [← map_pow, ← map_pow, (hπ1 _).2 (by simpa using hym), map_one]
  rcases perm3_cube_of_odd (e (π ⟨y, hy⟩)) with h3 | h2
  · rw [← map_pow, ← map_pow] at h3
    have := (hπ1 _).1 (e.injective (h3.trans (map_one e).symm))
    simpa using this
  · have hσ : e (π ⟨y, hy⟩) = 1 := by
      obtain ⟨k, hk⟩ := hm
      rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at hm1
      exact hm1
    have h1 : π ⟨y, hy⟩ = 1 := e.injective (hσ.trans (map_one e).symm)
    have := (hπ1 _).1 h1
    have hy1 : y ∈ pCoreOf 2 H := by simpa using this
    exact Subgroup.pow_mem _ hy1 3

theorem comm_V_L1_mem_Q {v l : G} (hv : v ∈ V) (hl : l ∈ L₁) :
    v * l * v⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
  have h := Subgroup.commutator_mem_commutator hv hl
  rw [S.commutator_V_L1, commutatorElement_def] at h
  exact S.U_le_Q (le_conjClosure _ _ h)

theorem piQ_V_comm_L1 {v l : G} (hv : v ∈ V) (hl : l ∈ L₁) :
    piQ H ⟨v, S.V_le_H hv⟩ * piQ H ⟨l, S.L1_le_H hl⟩ =
      piQ H ⟨l, S.L1_le_H hl⟩ * piQ H ⟨v, S.V_le_H hv⟩ := by
  rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    ← map_mul, piQ_eq_one_iff]
  exact S.comm_V_L1_mem_Q hv hl

end A5Sit

end CFSG.Quasithin.H13
