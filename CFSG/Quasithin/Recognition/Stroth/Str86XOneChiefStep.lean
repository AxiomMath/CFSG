module

public import CFSG.Quasithin.Recognition.Stroth.Str86XOneChief
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat2
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneUpper2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_exists_chiefStep_X1_z1
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hL2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)) (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k)
    (hY : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3)
    (hX1' : ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S)
    (hX1Q1 : ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S) :
    ∃ L N : Subgroup G, IsChiefStep (L1 ⊔ S) (u3X1 L1 L2 S) L N ∧
      N ⊓ Z1 L1 L2 S = L ∧ N ⊔ Z1 L1 L2 S = u3X1 L1 L2 S := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSeq : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hSH : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hSeq
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hcent : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (sup_le le_sup_left hSH).trans hZI
  have hZH : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hZcentral : ∀ h ∈ (L1 ⊔ S : Subgroup G), ∀ z ∈ Z1 L1 L2 S, h * z = z * h := by
    intro h hh z hz
    exact (Subgroup.mem_centralizer_iff.mp (hcent hh) z hz).symm
  have hZX : Z1 L1 L2 S ≤ u3X1 L1 L2 S := u3Z1_le_u3X1 hF hSB h1 hB2 h2 hZI
  have hXH : u3X1 L1 L2 S ≤ L1 ⊔ S :=
    (u3X1_le_q1 (L1 := L1) (L2 := L2) (S := S)).trans (hQ1S.trans le_sup_right)
  have hNX : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF hg) x).mp hx⟩
  obtain ⟨c, hser⟩ :=
    D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S) (U := u3X1 L1 L2 S)
      (u3X1 L1 L2 S) hNX
  have hc : c = 1 := str86_chief_count_eq_one hF hSB hk hFc hU3 hL2 hZQ hser
  obtain ⟨L, N, hstep, hnc, hNleX⟩ := exists_noncentral_chiefStep hser hc
  have hZL : Z1 L1 L2 S ⊓ N ≤ L :=
    inf_le_lower_of_noncentral hXH hstep hnc hZX hZH hZcentral
  have hZL' : N ⊓ Z1 L1 L2 S ≤ L := by rw [inf_comm]; exact hZL
  obtain ⟨hE, hNat⟩ :=
    str86_X1_chiefFactor_natural hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
      hX1Q1 hstep hnc hZL
  letI : CommGroup ↥(Ch3z.chiefMod L N) := commGroupOfElemAbelian hE
  have hgeChief : (2 ^ k) ^ 6 ≤ Nat.card (Ch3z.chiefMod L N) := by
    obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ := hNat
    letI : Field K := hKfield
    letI : Finite K := hKfin
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨-, -, -, -, -, -, -, β, hβsurj, -, -⟩ := hπ
    have hcard := Nat.card_le_card_of_surjective β hβsurj
    change Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) ≤
      Nat.card (↥(⊤ : Subgroup (Ch3z.chiefMod L N))) at hcard
    have htop : (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤ = ⊥ := by simp
    have hcod : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
        (⊥ : Subgroup (Multiplicative (Fin 3 → K))).subgroupOf ⊤) = Nat.card K ^ 3 := by
      rw [htop]
      calc Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))) ⧸
            (⊥ : Subgroup ↥(⊤ : Subgroup (Multiplicative (Fin 3 → K))))) =
            Nat.card (Multiplicative (Fin 3 → K)) :=
          Nat.card_congr (QuotientGroup.quotientBot.trans Subgroup.topEquiv).toEquiv
        _ = Nat.card (Fin 3 → K) := Nat.card_congr Multiplicative.toAdd
        _ = Nat.card K ^ 3 := by rw [Nat.card_pi]; simp
    have hdom : Nat.card (↥(⊤ : Subgroup (Ch3z.chiefMod L N))) =
        Nat.card (Ch3z.chiefMod L N) :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hdom, hcod, hKcard, ← pow_mul] at hcard
    simpa using hcard
  have hLN : L ≤ N := hstep.2.2.1.le
  have hNXle : N ≤ u3X1 L1 L2 S := hNleX
  have hNH : N ≤ L1 ⊔ S := hNXle.trans hXH
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hNH.trans hHL
  have hsecBot : secImg (Subgroup.normalizer (L : Set G)) L L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hb
  have hcardChief : Nat.card (Ch3z.chiefMod L N) = L.relIndex N := by
    have hrel := relIndex_secImg (A := Subgroup.normalizer (L : Set G)) (B := L)
      (T := L) (H := N) le_rfl hLN hNL
    rw [hsecBot, Subgroup.relIndex_bot_left] at hrel
    exact hrel
  have hNZn : N ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := hNH.trans hZH
  have hsubEq : (N ⊓ Z1 L1 L2 S).subgroupOf N = (Z1 L1 L2 S).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨x.2, h⟩
  have hrelNZ : (N ⊓ Z1 L1 L2 S).relIndex N = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := by
    haveI : ((Z1 L1 L2 S).subgroupOf N).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hNZn
    haveI : ((Z1 L1 L2 S).subgroupOf (N ⊔ Z1 L1 L2 S)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le hNZn Subgroup.le_normalizer)
    have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient N (Z1 L1 L2 S) hNZn
    have hcard := Nat.card_congr (MulEquiv.toEquiv hiso)
    rw [Subgroup.relIndex, Subgroup.relIndex, hsubEq]
    exact hcard
  have hsupX : N ⊔ Z1 L1 L2 S ≤ u3X1 L1 L2 S := sup_le hNXle hZX
  have hrelMon : (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) ≤
      (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
    Subgroup.relIndex_le_of_le_right hsupX (D15Proof.relIndex_ne_zero _ _)
  have hub := str86_X1_upper_bound hF hSB hk hFc hU3 hB2 h2 hZI hZQ hL2 hZ2 hZ1 hY hX1'
    hX1Q1
  have hq6 : Nat.card (u3M L1 L2 S) = (2 ^ k) ^ 6 := by
    have hge : (2 ^ k) ^ 6 ≤ Nat.card (u3M L1 L2 S) := by
      calc (2 ^ k) ^ 6 ≤ Nat.card (Ch3z.chiefMod L N) := hgeChief
        _ = L.relIndex N := hcardChief
        _ ≤ (N ⊓ Z1 L1 L2 S).relIndex N :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
              (Subgroup.relIndex_dvd_of_le_left N hZL')
        _ = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := hrelNZ
        _ ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := hrelMon
        _ = Nat.card (u3M L1 L2 S) := rfl
    exact le_antisymm hub hge
  have hcardChiefEq : Nat.card (Ch3z.chiefMod L N) = (2 ^ k) ^ 6 := by
    have hle : Nat.card (Ch3z.chiefMod L N) ≤ (2 ^ k) ^ 6 := by
      calc Nat.card (Ch3z.chiefMod L N) = L.relIndex N := hcardChief
        _ ≤ (N ⊓ Z1 L1 L2 S).relIndex N :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
              (Subgroup.relIndex_dvd_of_le_left N hZL')
        _ = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := hrelNZ
        _ ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := hrelMon
        _ = Nat.card (u3M L1 L2 S) := rfl
        _ = (2 ^ k) ^ 6 := hq6
    exact le_antisymm hle hgeChief
  have h1' : L.relIndex N = (2 ^ k) ^ 6 := by
    rw [← hcardChief]
    exact hcardChiefEq
  have h3' : (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = (2 ^ k) ^ 6 := by
    rw [show (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = Nat.card (u3M L1 L2 S) from rfl, hq6]
  have hEq13 : L.relIndex N = (N ⊓ Z1 L1 L2 S).relIndex N := by
    have hle : L.relIndex N ≤ (N ⊓ Z1 L1 L2 S).relIndex N :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
        (Subgroup.relIndex_dvd_of_le_left N hZL')
    refine le_antisymm hle ?_
    calc (N ⊓ Z1 L1 L2 S).relIndex N = (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) := hrelNZ
      _ ≤ (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := hrelMon
      _ = (2 ^ k) ^ 6 := h3'
      _ = L.relIndex N := h1'.symm
  have hLeq : N ⊓ Z1 L1 L2 S = L := by
    have h := Subgroup.relIndex_mul_relIndex (N ⊓ Z1 L1 L2 S) L N hZL' hLN
    rw [← hEq13] at h
    have hpos : 0 < L.relIndex N := Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    have hone : (N ⊓ Z1 L1 L2 S).relIndex L = 1 := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      rw [one_mul]
      exact h
    exact le_antisymm hZL' (Subgroup.relIndex_eq_one.mp hone)
  have hXeq : N ⊔ Z1 L1 L2 S = u3X1 L1 L2 S := by
    have h34 : (Z1 L1 L2 S).relIndex (N ⊔ Z1 L1 L2 S) =
        (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) := by
      rw [← hrelNZ, ← hEq13, h1', h3']
    have h := Subgroup.relIndex_mul_relIndex (Z1 L1 L2 S) (N ⊔ Z1 L1 L2 S)
      (u3X1 L1 L2 S) le_sup_right hsupX
    rw [h34] at h
    have hpos : 0 < (Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) :=
      Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _)
    have hone : (N ⊔ Z1 L1 L2 S).relIndex (u3X1 L1 L2 S) = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [mul_one]
      exact h
    exact le_antisymm hsupX (Subgroup.relIndex_eq_one.mp hone)
  exact ⟨L, N, hstep, hLeq, hXeq⟩

end CFSG.Quasithin.Stroth

end
