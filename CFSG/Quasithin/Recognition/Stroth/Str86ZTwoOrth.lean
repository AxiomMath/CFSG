module

public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertex
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoChain

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

abbrev u3H (L1 L2 S : Subgroup G) : Subgroup G := L2 ⊔ Q2 L1 L2 S

theorem q2_le_u3H (L1 L2 S : Subgroup G) : Q2 L1 L2 S ≤ u3H L1 L2 S := le_sup_right

theorem l2_le_u3H (L1 L2 S : Subgroup G) : L2 ≤ u3H L1 L2 S := le_sup_left

theorem u3H_le_p2 (L1 L2 S : Subgroup G) : u3H L1 L2 S ≤ P2 L1 L2 S :=
  sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))

theorem str86_s_le_u3H {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) : S ≤ u3H L1 L2 S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
    _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right

theorem str86_pCoreOf_u3H {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S) : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := by
  have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  simpa [P1, P2, Q1, Q2, bigB_comm L1 L2 S] using h

noncomputable def str86_oTwoQuot_u3H_equiv
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) :
    oTwoQuot ↥(u3H L1 L2 S) ≃* oTwoQuot ↥L2 := by
  have hq : Q1 L2 L1 S = Q2 L1 L2 S := by
    unfold Q1 Q2 P1 P2
    rw [bigB_comm L1 L2 S]
  have h := oTwoQuotSupEquiv (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  rw [hq] at h
  exact h

theorem str86_isL2Quot_u3H {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) :
    IsL2Quot n (oTwoQuot ↥(u3H L1 L2 S)) := by
  obtain ⟨e⟩ := hL2
  exact ⟨(str86_oTwoQuot_u3H_equiv hF).trans e⟩

theorem str86_z2_normal_u3H (L1 L2 S : Subgroup G) :
    u3H L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
  (u3H_le_p2 L1 L2 S).trans
    ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)))

theorem str86_centralizer_u3H_z2 {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z2 L1 L2 S ⊓ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) = ⊥ := by
  have h := (str86_caseI_basics hF hSB h1 hB2 h2 hZI).2.2.1
  simpa [u3H] using h

theorem str86_exists_chiefStep_u3H {L1 L2 S : Subgroup G} {k : ℕ}
    {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ∃ W : Subgroup G, W ≤ Z2 L1 L2 S ∧
      IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W ∧
      ¬ IsCentralStep (u3H L1 L2 S) ⊥ W := by
  classical
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨hZ1eq, hZ1Z2, -, -, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := fun h =>
    hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq h)))
  have hnorm : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) (Z2 L1 L2 S) := by
    refine ⟨omegaOneCenterOf_le (Q2 L1 L2 S), fun g hg x hx => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (str86_z2_normal_u3H L1 L2 S hg) x).mp hx
  obtain ⟨W, hWmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun M : Subgroup G =>
      IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) M ∧ M ≤ Z2 L1 L2 S ∧ M ≠ ⊥)
    (fun M : Subgroup G => Nat.card M) ⟨Z2 L1 L2 S, hnorm, le_rfl, hZ2ne⟩
  obtain ⟨hWN, hWZ2, hWne⟩ := hWmin.prop
  refine ⟨W, hWZ2, ?_, ?_⟩
  · refine ⟨hWN, CFSG.Quasithin.D15Proof.isNormalIn_bot _ _, bot_lt_iff_ne_bot.mpr hWne, ?_⟩
    intro K hK hbotK hKW
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · right
      by_contra hKW'
      exact hWmin.not_lt ⟨hK, hKW.trans hWZ2, hKbot⟩
        (Subgroup.card_lt_of_lt (lt_of_le_of_ne hKW hKW'))
  · intro hc
    have hWcent : W ≤ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 : g * w * g⁻¹ * w⁻¹ = 1 := by
        have := hc g hg w hw
        rwa [Subgroup.mem_bot] at this
      have h2 : g * w * g⁻¹ = w := by
        have := congrArg (fun t => t * w) h1
        simpa [mul_assoc] using this
      calc g * w = (g * w * g⁻¹) * g := by group
        _ = w * g := by rw [h2]
    have hle : W ≤ Z2 L1 L2 S ⊓
        Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := le_inf hWZ2 hWcent
    rw [str86_centralizer_u3H_z2 hF hSB h1 hB2 h2 hZI] at hle
    exact hWne (le_bot_iff.mp hle)

theorem str86_q_sq_le_r
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) : (2 ^ k) ^ 2 ≤ 2 ^ n := by
  have hN : IsNormalIn (L1 ⊔ S) (u3X1 L1 L2 S) (u3X1 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_u3X1_sup hF hg) x).mp hx⟩
  obtain ⟨c, hser⟩ := CFSG.Quasithin.D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S)
    (U := u3X1 L1 L2 S) (N := u3X1 L1 L2 S) hN
  have h := str86_chief_count_bound hF hSB hk hFc hU3 hn hL2 hZQ hser
  have hle : (2 ^ k) ^ 2 ≤ ((2 ^ k) ^ 2) ^ c :=
    calc (2 ^ k) ^ 2 = ((2 ^ k) ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ ((2 ^ k) ^ 2) ^ c := Nat.pow_le_pow_right (by positivity) h.1
  exact hle.trans h.2

theorem str86_card_chiefStep_ge
    {L1 L2 S : Subgroup G} {n : ℕ} (hF : F112HypW L1 L2 S)
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    {L N : Subgroup G} (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L N)
    (hnc : ¬ IsCentralStep (u3H L1 L2 S) L N) :
    (2 ^ n) ^ 2 ≤ L.relIndex N := by
  have hUH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hU : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hE : IsElemAbelian 2 (Ch3z.chiefMod L N) := isElemAbelian_chiefMod hstep hUH hU
  obtain ⟨e₀⟩ := str86_isL2Quot_u3H hF hL2
  let e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 n) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 n))
  have h := l2ChiefSectionRep_sq_le_card hn hstep hUH hE e hnc
  have hcard : Nat.card (Additive (Ch3z.chiefMod L N)) = Nat.card (Ch3z.chiefMod L N) :=
    Nat.card_congr Additive.ofMul
  rw [hcard] at h
  have hHL : u3H L1 L2 S ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hNA : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hB : secImg (Subgroup.normalizer (L : Set G)) L L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hb
  have hsec : Nat.card (Ch3z.chiefMod L N) = L.relIndex N := by
    have hrel := relIndex_secImg (A := Subgroup.normalizer (L : Set G)) (B := L)
      (T := L) (H := N) le_rfl hstep.2.2.1.le hNA
    rw [hB, Subgroup.relIndex_bot_left] at hrel
    exact hrel
  rwa [hsec] at h

theorem str86_card_z2_le
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2) :
    Nat.card (Z2 L1 L2 S) ≤ (2 ^ n) ^ 3 := by
  have hqr : (2 ^ k) ^ 2 ≤ 2 ^ n :=
    str86_q_sq_le_r hF hSB hk hFc hU3 hn hL2 hZQ
  calc Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2 := h376
    _ = (2 ^ k) ^ 2 * (2 ^ n) ^ 2 := by ring
    _ ≤ 2 ^ n * (2 ^ n) ^ 2 := Nat.mul_le_mul_right _ hqr
    _ = (2 ^ n) ^ 3 := by ring

end CFSG.Quasithin.Stroth
