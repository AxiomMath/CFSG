module

public import CFSG.Quasithin.H13.U3L14Kp
public import CFSG.Quasithin.H13.U3L14C
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.H13.U3L14G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def CharNormal (B X : Subgroup G) : Prop :=
  ∃ C : Subgroup G, C ≤ B ∧ C ≠ ⊥ ∧ (C.subgroupOf B).Characteristic ∧
    X ≤ normalizer (C : Set G)

@[expose] def Stmt13_3_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V Lp : Subgroup G), QTH13 G T L →
    IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V → V ⊓ centralizer (L : Set G) = ⊥ →
    (A6.IsHatA6 L → Lp = A6.l1plus T L V) → (¬ A6.IsHatA6 L → Lp = L₁Of L (fsuV1 T V)) →
    ((Nonempty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 6))) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
      (CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) ∨ H13.IsA6Block L ∨ IsG2Block L) ∧
      (IsG2Block L →
        normalizer (baum (pCoreOf 2 (Lp ⊔ T)) : Set G) ≤ normalizer (L : Set G))) ∧
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 →
      CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) ∨ IsLnBlock L 3)

variable [Finite G]

theorem card_altD6 : Nat.card (↥(FFModel.altDn 6).sec ⧸
    (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) = 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
    Explicit.card_dnZ (by norm_num), Explicit.card_coreMod (by norm_num)] at h
  have h6 : (if Even 6 then 2 else 1) = 2 := by decide
  rw [h6] at h
  show Nat.card (↥(G6.coreMod 6) ⧸
    ((Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6).subgroupOf (G6.coreMod 6))) = 16
  have h32 : (2 : ℕ) ^ (6 - 1) = 32 := by norm_num
  omega

omit [Finite G] in
theorem relIndex_pCoreOf_eq_card (L : Subgroup G) :
    (pCoreOf 2 L).relIndex L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have heq : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    ext x
    rw [mem_subgroupOf]
    exact coe_mem_pCoreOf_iff
  rw [relIndex, heq, index_eq_card]

omit [Finite G] in
theorem block_cards {L : Subgroup G} (hB : IsLnBlock L 3 ∨ H13.IsA6Block L) :
    (blockZ L).relIndex (blockU L) ≤ 16 ∧
      ((pCoreOf 2 L).relIndex L = 168 ∨ (pCoreOf 2 L).relIndex L = 360) := by
  rw [relIndex_pCoreOf_eq_card]
  rcases hB with ⟨-, α, hα, hker, β, hβ, hβker, -⟩ | ⟨-, ⟨e⟩, hU, hnat⟩
  · refine ⟨?_, Or.inl ?_⟩
    · have := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβ).toEquiv
      rw [hβker] at this
      rw [relIndex, index_eq_card, this]
      change Nat.card (Fin 3 → ZMod 2) ≤ 16
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      norm_num
    · have := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv
      rw [hker] at this
      rw [this, card_statedSL_three_two]
  · refine ⟨?_, Or.inr ?_⟩
    · obtain ⟨π, -, -, -, -, -, -, -, β, hβ, hβker, -⟩ := hnat
      set β' := β.comp (Subgroup.topEquiv (G := ↥(blockU L))).symm.toMonoidHom with hβ'
      have hβ's : Function.Surjective β' := fun y => by
        obtain ⟨u, hu⟩ := hβ y
        refine ⟨(u : ↥(blockU L)), ?_⟩
        rw [hβ', MonoidHom.comp_apply,
          show (Subgroup.topEquiv (G := ↥(blockU L))).symm.toMonoidHom (u : ↥(blockU L)) = u from
            Subtype.ext rfl, hu]
      have hker : β'.ker = (blockZ L).subgroupOf (blockU L) := by
        ext u
        rw [MonoidHom.mem_ker, hβ', MonoidHom.comp_apply, hβker]
        rfl
      have := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β' hβ's).toEquiv
      rw [hker, card_altD6] at this
      rw [relIndex, index_eq_card, this]
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl

theorem le_four_of_le_eight {r n : ℕ} (hr : r ≡ 1 [MOD 3]) (hdvd : r ∣ 2 ^ n) (h8 : r ≤ 8) :
    r ≤ 4 := by
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases k with _ | _ | _ | _ | k
  · norm_num
  · exact absurd hr (by decide)
  · norm_num
  · exact absurd hr (by decide)
  · have : 2 ^ 4 ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem V_le_blockU : V ≤ blockU L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVL : V ≤ L := by
    rw [← S.irr.2.2.2.1]
    exact le_normalizer_iff_commutator_le_right.mp (S.V_T.trans S.T_L)
  have hV2 : IsPGroup 2 V := fun v => ⟨1, Subtype.ext (by simpa using S.sq_V v.2)⟩
  have hVQ : V ≤ pCoreOf 2 L :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL S.irr.2.2.1 hV2
  rw [← S.irr.2.2.2.1]
  exact commutator_mono hVQ le_rfl

theorem pCoreOf_L_le_R1 : pCoreOf 2 L ≤ pCoreOf 2 (Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnL : L ⊔ T ≤ normalizer (pCoreOf 2 L : Set G) :=
    sup_le (LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (S.T_L.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hQT : pCoreOf 2 L ≤ T :=
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hnL
      (LieType.BorelTits.pCoreOf_isPGroup 2 L)).trans
      (pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ L ⊔ T)).2.1
        (S.syl (le_sup_right : T ≤ L ⊔ T)).2.2)
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
    (sup_le (S.Lp_L.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 L)) (le_sup_right.trans hnL))
    (LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem relIndex_R1_le_sixteen (hB : IsLnBlock L 3 ∨ H13.IsA6Block L) {x : G} (hx : x ∈ Lp)
    (hx3 : x ^ 3 = 1) :
    (centralizer ({x} : Set G)).relIndex (pCoreOf 2 (Lp ⊔ T)) ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUZ, hLQ⟩ := block_cards hB
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  set Q := pCoreOf 2 L with hQ
  set C := centralizer ({x} : Set G) with hC
  have hxL : x ∈ L := S.Lp_L hx
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
  have hV1Z : fsuV1 T V ⊓ blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hvZ⟩ := mem_inf.mp hv
    have : v ∈ V ⊓ centralizer (L : Set G) :=
      mem_inf.mpr ⟨le1V hv1, (mem_inf.mp hvZ).2⟩
    rw [S.zv] at this
    exact this
  have hV1U : fsuV1 T V ≤ blockU L := le1V.trans S.V_le_blockU
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZV1C : blockZ L ⊔ fsuV1 T V ≤ C ⊓ blockU L := by
    refine sup_le (le_inf (fun z hz => ?_) hZU) (le_inf (fun v hv => ?_) hV1U)
    · rw [hC, mem_centralizer_singleton_iff]
      exact ((mem_centralizer_iff.mp (mem_inf.mp hz).2) x hxL).symm
    · rw [hC, mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (S.mem_centralizer_V1 (S.Lp_G1 hx))) v hv
  have hcU8 : C.relIndex (blockU L) ≤ 8 := by
    have h1 := relIndex_mul_relIndex (blockZ L) (blockZ L ⊔ fsuV1 T V) (blockU L) le_sup_left
      (sup_le hZU hV1U)
    have h2 : 2 ≤ (blockZ L).relIndex (blockZ L ⊔ fsuV1 T V) := by
      have h3 : (blockZ L).relIndex (blockZ L ⊔ fsuV1 T V) ≠ 1 := fun h3 => by
        have h4 := relIndex_eq_one.mp h3
        have h5 : fsuV1 T V ≤ fsuV1 T V ⊓ blockZ L := le_inf le_rfl (le_sup_right.trans h4)
        rw [hV1Z] at h5
        have := S.card1
        rw [le_bot_iff.mp h5, card_bot] at this
        exact absurd this (by norm_num)
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
  have hQRL : Q ≤ R ⊓ L := le_inf S.pCoreOf_L_le_R1 (LieType.BorelTits.pCoreOf_le 2 L)
  have hRL2 : IsPGroup 2 ↥(R ⊓ L) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)).to_le inf_le_left
  have hRLQ : R ⊓ L ≤ normalizer (Q : Set G) := inf_le_right.trans hLQn
  have hxRL : x ∈ normalizer ((R ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (LieType.BorelTits.le_normalizer_pCoreOf 2 (Lp ⊔ T) (mem_sup_left hx))
      (le_normalizer hxL)
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
    mem_normalizer_inf (le_normalizer hr) (S.T_L (S.R1_le_T hr))
  have hcommR : ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ R ⊓ L := by
    intro r hr
    have h := S.comm_R1_mem hr hx
    have h' : x * r * x⁻¹ * r⁻¹ = (r * x * r⁻¹ * x⁻¹)⁻¹ := by group
    rw [h']
    exact mem_inf.mpr ⟨S.pCoreOf_Lp_le_R1 (inv_mem h),
      S.Lp_L (LieType.BorelTits.pCoreOf_le 2 Lp (inv_mem h))⟩
  have hcR : C.relIndex R = C.relIndex (R ⊓ L) := by
    have h2 := sup_inf_centralizer_eq hx3 hRL2 inf_le_left hRn hxRL hcommR
    have hmul := relIndex_centralizer_eq_mul (x := x) (inf_le_left : R ⊓ L ≤ R) hRn
    rw [h2, relIndex_self, one_mul] at hmul
    exact hmul
  rw [hcR]
  omega


end Set14

end CFSG.Quasithin.H13.U3
