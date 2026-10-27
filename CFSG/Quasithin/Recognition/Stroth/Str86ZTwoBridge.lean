module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoMain
public import CFSG.Quasithin.Recognition.Stroth.Str86XOneUpper
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelAbstract

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem chiefModBot_commutator_eq {H U W : Subgroup G} {m : ℕ}
    (hstep : IsChiefStep H U ⊥ W) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 m))
    (hW2 : ∀ w : ↥W, w * w = 1) (h : ↥H) (w : ↥W) (x : ↥W)
    (hx : (x : G) = (w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    Additive.ofMul (chiefModBotMulEquiv W x) =
      ((l2ChiefSectionRep hstep hUH hE e) (e (QuotientGroup.mk h)) - 1)
        (Additive.ofMul (chiefModBotMulEquiv W w)) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let cw : ↥W :=
    ⟨(h : G) * (w : G) * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp
        ((D14.le_normalizer_of_isNormalIn hstep.1) h.2) (w : G)).mp w.2⟩
  have hw_invW : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW2 w)
  have hw_inv : (w : G)⁻¹ = (w : G) := by simpa using congrArg Subtype.val hw_invW
  have hxw : x = w * cw := by
    apply Subtype.ext
    rw [hx, Subgroup.coe_mul]
    change (w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹ =
      (w : G) * ((h : G) * (w : G) * (h : G)⁻¹)
    rw [hw_inv]
    group
  have hcw : l2ChiefSectionAction hstep hE h (chiefModBotMulEquiv W w) =
      chiefModBotMulEquiv W cw :=
    chiefModBotMulEquiv_conj hstep hUH hE h w
  rw [hxw, map_mul]
  change Additive.ofMul (chiefModBotMulEquiv W w) +
      Additive.ofMul (chiefModBotMulEquiv W cw) =
    ((l2ChiefSectionRep hstep hUH hE e) (e (QuotientGroup.mk h)) - 1)
      (Additive.ofMul (chiefModBotMulEquiv W w))
  rw [LinearMap.sub_apply, Module.End.one_apply, l2ChiefSectionRep_apply_mk, hcw,
    sub_eq_add_neg, CFSG.QuasithinUnique.Setup.SL2Modules.neg_eq_self_of_charTwo (ZMod 2), add_comm]

theorem commutator_z2_s_le_u3Y
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hQ1sup : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S) :
    ⁅Z2 L1 L2 S, S⁆ ≤ u3Y L1 L2 S := by
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2N : Q2 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hQ2S.trans (le_normalizer_q1_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hcent : ∀ q ∈ Q2 L1 L2 S, ∀ z ∈ Z2 L1 L2 S, q * z = z * q := by
    intro q hq z hz
    exact (Subgroup.mem_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) z hz).symm
  rw [Subgroup.commutator_le]
  intro z hz s hs
  have hs' : s ∈ Q2 L1 L2 S ⊔ Q1 L1 L2 S := by
    rw [sup_comm, hQ1sup]
    exact hs
  obtain ⟨q, hq, q1, hq1, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_le_normalizer hQ2N).mp hs'
  have hqz : q * z = z * q := hcent q hq z hz
  have hcZ : z * q1 * z⁻¹ * q1⁻¹ ∈ Z2 L1 L2 S := by
    have h1 : q1 * z⁻¹ * q1⁻¹ ∈ Z2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S) (hQ1S hq1))
        z⁻¹).mp ((Z2 L1 L2 S).inv_mem hz)
    have h2 : z * (q1 * z⁻¹ * q1⁻¹) ∈ Z2 L1 L2 S :=
      (Z2 L1 L2 S).mul_mem hz h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hzq1Z : ⁅z, q1⁆ ∈ Z2 L1 L2 S := by
    simpa [commutatorElement_def, mul_assoc] using hcZ
  have hqcomm : q * (z * q1 * z⁻¹ * q1⁻¹) * q⁻¹ = z * q1 * z⁻¹ * q1⁻¹ := by
    have h : q * (z * q1 * z⁻¹ * q1⁻¹) = (z * q1 * z⁻¹ * q1⁻¹) * q :=
      hcent q hq (z * q1 * z⁻¹ * q1⁻¹) hcZ
    rw [h]
    group
  have heq : ⁅z, q * q1⁆ = ⁅z, q1⁆ := by
    rw [commutatorElement_def]
    calc z * (q * q1) * z⁻¹ * (q * q1)⁻¹
        = q * (z * q1 * z⁻¹ * q1⁻¹) * q⁻¹ := by
          rw [mul_inv_rev]
          calc z * (q * q1) * z⁻¹ * (q1⁻¹ * q⁻¹)
              = q * z * q1 * z⁻¹ * q1⁻¹ * q⁻¹ := by rw [hqz]; group
            _ = q * (z * q1 * z⁻¹ * q1⁻¹) * q⁻¹ := by group
      _ = ⁅z, q1⁆ := by rw [hqcomm]; rfl
  rw [heq]
  have hcomm' : ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ ≤ u3Y L1 L2 S := by
    rw [Subgroup.commutator_comm]
    exact u3_commutator_q1_z2_le_u3Y hF
  exact hcomm' (Subgroup.commutator_mem_commutator hz hq1)

private theorem commutator_u3Y_s_eq_of_sup
    {L1 L2 S E : Subgroup G} (hF : F112Hyp L1 L2 S)
    (hES : E ≤ S) (hEsup : E ⊔ Q2 L1 L2 S = S) :
    ⁅u3Y L1 L2 S, E⁆ = ⁅u3Y L1 L2 S, S⁆ := by
  apply le_antisymm
  · exact Subgroup.commutator_mono le_rfl hES
  · rw [Subgroup.commutator_le]
    intro y hy s hs
    have hQ2S : Q2 L1 L2 S ≤ S :=
      CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
    have hEN : E ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hES.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hs' : s ∈ E ⊔ Q2 L1 L2 S := by
      rw [hEsup]
      exact hs
    obtain ⟨e, he, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hEN).mp hs'
    have hqcent : q * y = y * q := by
      have hyZ : y ∈ Z2 L1 L2 S := u3Y_le_z2 hy
      exact (Subgroup.mem_centralizer_iff.mp
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) y hyZ).symm
    have hqinv : q * y⁻¹ * q⁻¹ = y⁻¹ := by
      have h1 : y * q⁻¹ = q⁻¹ * y := by
        calc y * q⁻¹ = q⁻¹ * (q * y) * q⁻¹ := by group
          _ = q⁻¹ * (y * q) * q⁻¹ := by rw [hqcent]
          _ = q⁻¹ * y := by group
      have h2 : q * y⁻¹ = y⁻¹ * q := by
        calc q * y⁻¹ = (y * q⁻¹)⁻¹ := by group
          _ = (q⁻¹ * y)⁻¹ := by rw [h1]
          _ = y⁻¹ * q := by group
      rw [h2]
      group
    have heq : ⁅y, e * q⁆ = ⁅y, e⁆ := by
      rw [commutatorElement_def]
      calc y * (e * q) * y⁻¹ * (e * q)⁻¹
          = y * e * (q * y⁻¹ * q⁻¹) * e⁻¹ := by
            rw [mul_inv_rev]
            group
        _ = y * e * y⁻¹ * e⁻¹ := by rw [hqinv]
        _ = ⁅y, e⁆ := rfl
    rw [heq]
    exact Subgroup.commutator_mem_commutator hy he

end CFSG.Quasithin.Stroth

end

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86YCommBridge_of_caseI
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    Str86YCommBridge L1 L2 S := by
  classical
  intro E hES hEsup
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2 :=
    str86_card_z2_le_sq hF hSB hk hFc hU3 hn hL2 hZQ hB2 hZI
  obtain ⟨W, hWZ2, hstepW, hncW⟩ :=
    str86_exists_chiefStep_u3H hF hSB hk hFc hU3 hB2 ⟨n, hL2⟩ hZI
  have hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W :=
    str86_z2_commutator_eq_chief hF hSB hk hFc hU3 hn hL2 hZQ h376 hstepW hncW hWZ2
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W) :=
    isElemAbelian_chiefMod hstepW hUH (pCoreOf_isPGroup 2 (P2 L1 L2 S))
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  obtain ⟨e₀⟩ := str86_isL2Quot_u3H hF.toW hL2
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 n) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 n))
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hHP2 : H ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hSylH : IsSylowTwoOf S H :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSleH hHP2
  let Tsub : Subgroup (oTwoQuot ↥H) := CFSG.Quasithin.imageOTwoQuot H S
  have hT2 : IsPGroup 2 Tsub :=
    CFSG.Quasithin.Stroth.isPGroup_imageOTwoQuot_of_isSylow hSylH
  have hTidx : ¬ 2 ∣ Tsub.index :=
    CFSG.Quasithin.Stroth.not_two_dvd_index_imageOTwoQuot hSylH
  let T : Sylow 2 (oTwoQuot ↥H) := hT2.toSylow hTidx
  have hTcoe : (T : Subgroup (oTwoQuot ↥H)) = Tsub := IsPGroup.toSylow_coe hT2 hTidx
  let A : Subgroup (SL(2, GaloisField 2 n)) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hTcard : Nat.card ↥Tsub = 2 ^ n := by
    rw [← hTcoe]
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
  have hAcard : Nat.card A = 2 ^ n := by
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥Tsub := by rw [hTcoe]
      _ = 2 ^ n := hTcard
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstepW hUH hE e hncW
  have hirr : ρ.IsIrreducible := l2ChiefSectionRep_irreducible hstepW hUH hE e
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hWcardEq : Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
    calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
          Nat.card_congr (chiefModBotMulEquiv W).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
          Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)
  have hWlt : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) < 2 ^ (4 * n) := by
    rw [← hWcardEq]
    have hZle : Nat.card W ≤ Nat.card (Z2 L1 L2 S) := Subgroup.card_le_of_le hWZ2
    have hZ3 : Nat.card (Z2 L1 L2 S) ≤ 2 ^ (3 * n) := by
      have := str86_card_z2_le hF hSB hk hFc hU3 hn hL2 hZQ h376
      simpa [pow_mul, mul_comm] using this
    have hlt : 3 * n < 4 * n := by omega
    exact lt_of_le_of_lt (hZle.trans hZ3) (Nat.pow_lt_pow_right (by norm_num) hlt)
  have hcardGF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have htri := isNaturalModule_or_isOrthModule_or_of_card_lt (by omega) hcardGF
    ρ hnt A hA2 hAcard hWlt
  rcases htri with hnat | ⟨l, hl, hn2l, horth⟩ | ⟨l, hn3l, hWcard3, hfix3⟩
  · exact (str86_natural_case_false hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hnat).elim
  ·
    have hcards := str86_orth_case_cards hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hl horth
    have hn2k : n = 2 * k := hcards.1
    have hZ2W : Z2 L1 L2 S = W :=
      str86_orth_case_z2_eq hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376 hstepW hncW
        hWZ2 hcomm hE e hl hn2l horth
    have hlk : l = k := by omega
    obtain ⟨-, hZ2card, hZ1card, hYcard⟩ :=
      str86_prop377 hF hSB hk hFc hU3 hB2 ⟨n, hL2⟩ hZI hZQ
    have hAcard2l : Nat.card A = 2 ^ (2 * l) := by
      rw [hAcard, hn2l]
    have hQ1sup : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S :=
      str86_pCoreOf_sup_pCoreOf hF.toW hSB (Or.inr h1) hn hL2
    have hW2 : ∀ w : ↥W, w * w = 1 := by
      intro w
      apply Subtype.ext
      simpa [pow_two] using
        (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 (w : G) (hWZ2 w.2)
    have hWSleY : ⁅W, S⁆ ≤ u3Y L1 L2 S := by
      rw [← hZ2W]
      exact commutator_z2_s_le_u3Y hF hQ1sup
    have hWSleW : ⁅W, S⁆ ≤ W := by
      have h := hWSleY.trans u3Y_le_z2
      rwa [hZ2W] at h
    have hYcard' : Nat.card (u3Y L1 L2 S) = (2 ^ k) ^ 3 := by
      simpa [u3Y] using hYcard
    have hcase := str86_caseI_basics hF hSB h1 hB2 ⟨n, hL2⟩ hZI
    have hZ1eq : Z1 L1 L2 S = Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) :=
      hcase.2.2.2.2.symm
    have hAdef : Subgroup.map e.toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥H)) (S.subgroupOf H)) = A := by
      dsimp [A]
      rw [hTcoe]
      rfl
    have hA_lift : ∀ a ∈ A, ∃ s : G, ∃ hs : s ∈ S,
        e (QuotientGroup.mk (⟨s, hSleH hs⟩ : ↥H)) = a := by
      intro a ha
      rw [← hAdef] at ha
      obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp ha
      obtain ⟨h, hh, hth⟩ := Subgroup.mem_map.mp ht
      refine ⟨(h : G), Subgroup.mem_subgroupOf.mp hh, ?_⟩
      rw [← hta, ← hth]
      rfl
    let θ := chiefModBotMulEquiv W
    let Φ : ↥⁅W, S⁆ →* ↥(Ch3z.chiefMod ⊥ W) :=
      θ.toMonoidHom.comp (Subgroup.inclusion hWSleW)
    have hΦinj : Function.Injective Φ := by
      intro x y hxy
      have h' : Subgroup.inclusion hWSleW x = Subgroup.inclusion hWSleW y :=
        θ.injective (by simpa [Φ] using hxy)
      exact Subtype.ext (by simpa using congrArg Subtype.val h')
    let Ksub : Subgroup ↥(Ch3z.chiefMod ⊥ W) := Φ.range
    have hKsub_card : Nat.card ↥Ksub = Nat.card ↥⁅W, S⁆ := by
      have hKsub_eq : Ksub = Subgroup.map Φ ⊤ := by
        dsimp [Ksub]
        rw [MonoidHom.range_eq_map]
      rw [hKsub_eq, Subgroup.card_map_of_injective (f := Φ) hΦinj]
      simp
    have hKsub_le : Nat.card ↥Ksub ≤ (2 ^ k) ^ 3 := by
      rw [hKsub_card]
      exact (Subgroup.card_le_of_le hWSleY).trans (by rw [hYcard'])
    have hcommSub_card : Nat.card ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) =
        (2 ^ k) ^ 3 := by
      have h := IsOrthModule.card_commSub (hF := hl) horth A hA2 hAcard2l
      rw [hlk] at h
      rw [h]
      ring
    have hcommSub_le_Ksub : ∀ v ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A,
        Additive.toMul v ∈ Ksub := by
      intro v hv
      refine CFSG.QuasithinUnique.Setup.X7.commSub_induction ρ A
        (P := fun v => Additive.toMul v ∈ Ksub) ?_ ?_ ?_ hv
      · intro a ha v
        obtain ⟨s, hs, hsaeq⟩ := hA_lift a ha
        let h : ↥H := ⟨s, hSleH hs⟩
        let w : ↥W := θ.symm (Additive.toMul v)
        have hv : Additive.ofMul (θ w) = v := by
          dsimp [w]
          simp
        rw [← hv]
        have hxW : (w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹ ∈ W :=
          hWSleW (Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := S) w.2 hs)
        let x : ↥W := ⟨(w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹, hxW⟩
        have hxmem : (x : G) ∈ ⁅W, S⁆ :=
          Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := S) w.2 hs
        have hform := chiefModBot_commutator_eq hstepW hUH hE e hW2 h w x rfl
        have haeq : e (QuotientGroup.mk h) = a := by
          simpa [h] using hsaeq
        rw [haeq] at hform
        rw [← hform]
        exact ⟨⟨x, hxmem⟩, rfl⟩
      · exact Ksub.one_mem
      · intro x y hx hy
        have hxy : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        rw [hxy]
        exact Ksub.mul_mem hx hy
    have hcommSub_le_Ksub_card : Nat.card ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) ≤
        Nat.card ↥Ksub :=
      Nat.card_le_card_of_injective
        (fun v : ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) =>
          (⟨Additive.toMul v, hcommSub_le_Ksub v v.2⟩ : ↥Ksub))
        (by
          intro x y hxy
          apply Subtype.ext
          exact Additive.toMul.injective
            (congrArg (fun a : ↥Ksub => (a : ↥(Ch3z.chiefMod ⊥ W))) hxy))
    have hKsub_card_eq : Nat.card ↥Ksub = (2 ^ k) ^ 3 :=
      le_antisymm hKsub_le (by rw [← hcommSub_card]; exact hcommSub_le_Ksub_card)
    let C : Set ↥(Ch3z.chiefMod ⊥ W) :=
      {m | Additive.ofMul m ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A}
    have hC_ncard : C.ncard = Nat.card ↥(CFSG.QuasithinUnique.Setup.X7.commSub ρ A) := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr
        { toFun := fun m =>
            ⟨Additive.ofMul (m : ↥(Ch3z.chiefMod ⊥ W)), m.2⟩
          invFun := fun v =>
            ⟨Additive.toMul (v : Additive ↥(Ch3z.chiefMod ⊥ W)), v.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hC_subset : C ⊆ (Ksub : Set ↥(Ch3z.chiefMod ⊥ W)) := by
      intro m hm
      exact hcommSub_le_Ksub (Additive.ofMul m) hm
    have hCeq : C = (Ksub : Set ↥(Ch3z.chiefMod ⊥ W)) := by
      apply Set.eq_of_subset_of_ncard_le hC_subset
      rw [hC_ncard, hcommSub_card]
      show (Ksub : Set ↥(Ch3z.chiefMod ⊥ W)).ncard ≤ (2 ^ k) ^ 3
      rw [← Nat.card_coe_set_eq]
      change Nat.card ↥Ksub ≤ (2 ^ k) ^ 3
      rw [hKsub_card_eq]
    have hKsub_le_commSub : ∀ y : G, ∀ hy : y ∈ ⁅W, S⁆,
        Additive.ofMul (θ ⟨y, hWSleW hy⟩) ∈
          CFSG.QuasithinUnique.Setup.X7.commSub ρ A := by
      intro y hy
      have hmemK : θ ⟨y, hWSleW hy⟩ ∈ Ksub := ⟨⟨y, hy⟩, rfl⟩
      have hmemC : θ ⟨y, hWSleW hy⟩ ∈ C := by
        rw [hCeq]
        exact hmemK
      exact hmemC
    have hWS_card : Nat.card ↥⁅W, S⁆ = (2 ^ k) ^ 3 := by
      rw [← hKsub_card, hKsub_card_eq]
    have hYeq : u3Y L1 L2 S = ⁅W, S⁆ := by
      exact (Subgroup.eq_of_le_of_card_ge hWSleY (by rw [hWS_card, hYcard'])).symm
    have hZ1fix : ∀ z : ↥W, (z : G) ∈ Z1 L1 L2 S ↔
        Additive.ofMul (θ z) ∈ fixedSub ρ A := by
      intro z
      have hmem : (z : G) ∈ Z1 L1 L2 S ↔
          (z : G) ∈ Z2 L1 L2 S ∧ (z : G) ∈ Subgroup.centralizer (S : Set G) := by
        rw [hZ1eq, Subgroup.mem_inf]
      rw [hmem]
      have hfixiff := mem_fixSub_chiefMod_bot_iff hstepW hUH hE e (S.subgroupOf H) z
      rw [hAdef, Subgroup.map_subgroupOf_eq_of_le hSleH] at hfixiff
      constructor
      · rintro ⟨-, hcent⟩
        exact hfixiff.mpr hcent
      · intro hfix
        exact ⟨hWZ2 z.2, hfixiff.mp hfix⟩
    have hcommYS_le : ⁅u3Y L1 L2 S, S⁆ ≤ Z1 L1 L2 S := by
      rw [Subgroup.commutator_le]
      intro y hy s hs
      have hyWS : y ∈ ⁅W, S⁆ := by
        rw [← hYeq]
        exact hy
      let w : ↥W := ⟨y, hWSleW hyWS⟩
      let h : ↥H := ⟨s, hSleH hs⟩
      have hθw_comm : Additive.ofMul (θ w) ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A :=
        hKsub_le_commSub y hyWS
      have haA : e (QuotientGroup.mk h) ∈ A := by
        rw [← hAdef]
        exact Subgroup.mem_map_of_mem e.toMonoidHom
          (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H))
            (Subgroup.mem_subgroupOf.mpr hs))
      have hxW : y * s * y⁻¹ * s⁻¹ ∈ W :=
        hWSleW (Subgroup.commutator_mem_commutator (H₁ := W) (H₂ := S) w.2 hs)
      let x : ↥W := ⟨y * s * y⁻¹ * s⁻¹, hxW⟩
      have hform := chiefModBot_commutator_eq hstepW hUH hE e hW2 h w x rfl
      have hgen : ((ρ (e (QuotientGroup.mk h)) - 1) (Additive.ofMul (θ w))) ∈
          IsOrthModule.commCommSub ρ A := by
        rw [IsOrthModule.commCommSub]
        exact Submodule.subset_span
          ⟨e (QuotientGroup.mk h), haA, Additive.ofMul (θ w), hθw_comm, rfl⟩
      have hfix : Additive.ofMul (θ x) ∈ fixedSub ρ A := by
        rw [hform, IsOrthModule.fixedSub_eq_span_commSub (hF := hl) horth A hA2 hAcard2l]
        exact hgen
      exact (hZ1fix x).mpr hfix
    have hYWSleY : ⁅u3Y L1 L2 S, S⁆ ≤ u3Y L1 L2 S := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_right).mp
        (le_normalizer_u3Y_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hYWSleW : ⁅u3Y L1 L2 S, S⁆ ≤ W := by
      rw [← hZ2W]
      exact hYWSleY.trans u3Y_le_z2
    let ΦY : ↥⁅u3Y L1 L2 S, S⁆ →* ↥(Ch3z.chiefMod ⊥ W) :=
      θ.toMonoidHom.comp (Subgroup.inclusion hYWSleW)
    let KbridgeSub : Subgroup ↥(Ch3z.chiefMod ⊥ W) := ΦY.range
    let Kbridge : Submodule (ZMod 2) (Additive ↥(Ch3z.chiefMod ⊥ W)) :=
      AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup' KbridgeSub)
    have hgen_mem_Kbridge : ∀ a ∈ A, ∀ v ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A,
        (ρ a - 1) v ∈ Kbridge := by
      intro a ha v hv
      obtain ⟨s, hs, hsaeq⟩ := hA_lift a ha
      have hvKsub : Additive.toMul v ∈ Ksub := by
        have hmemC : Additive.toMul v ∈ C := by
          show Additive.ofMul (Additive.toMul v) ∈
            CFSG.QuasithinUnique.Setup.X7.commSub ρ A
          simpa using hv
        rwa [hCeq] at hmemC
      obtain ⟨yWS, hyWS_eq⟩ := MonoidHom.mem_range.mp hvKsub
      let w : ↥W := θ.symm (Additive.toMul v)
      have hθw : Additive.ofMul (θ w) = v := by
        dsimp [w]
        simp
      have hw_eq : w = ⟨(yWS : G), hWSleW yWS.2⟩ := by
        apply θ.injective
        apply Additive.ofMul.injective
        rw [hθw]
        have h' := congrArg Additive.ofMul hyWS_eq
        have hincl : (Subgroup.inclusion hWSleW yWS : ↥W) =
            ⟨(yWS : G), hWSleW yWS.2⟩ := rfl
        simpa [Φ, θ, hincl] using h'.symm
      have hyY : (w : G) ∈ u3Y L1 L2 S := by
        rw [hw_eq, hYeq]
        exact yWS.2
      let h : ↥H := ⟨s, hSleH hs⟩
      have hxmem : (w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹ ∈
          ⁅u3Y L1 L2 S, S⁆ :=
        Subgroup.commutator_mem_commutator (H₁ := u3Y L1 L2 S) (H₂ := S) hyY hs
      let x : ↥W := ⟨(w : G) * (h : G) * (w : G)⁻¹ * (h : G)⁻¹,
        hYWSleW hxmem⟩
      have hform := chiefModBot_commutator_eq hstepW hUH hE e hW2 h w x rfl
      have haeq : e (QuotientGroup.mk h) = a := by
        simpa [h] using hsaeq
      rw [haeq] at hform
      rw [← hθw, ← hform]
      exact (AddSubgroup.mem_toZModSubmodule 2).mpr
        ((Subgroup.mem_toAddSubgroup' KbridgeSub (Additive.ofMul (θ x))).mpr
          ⟨⟨x, hxmem⟩, rfl⟩)
    have hcommComm_le : IsOrthModule.commCommSub ρ A ≤ Kbridge := by
      change Submodule.span (ZMod 2)
        {x | ∃ a ∈ A, ∃ v ∈ CFSG.QuasithinUnique.Setup.X7.commSub ρ A,
          x = (ρ a - 1) v} ≤ Kbridge
      exact Submodule.span_le.mpr (by
        rintro x ⟨a, ha, v, hv, rfl⟩
        exact hgen_mem_Kbridge a ha v hv)
    have hfixed_le : fixedSub ρ A ≤ Kbridge := by
      rw [IsOrthModule.fixedSub_eq_span_commSub (hF := hl) horth A hA2 hAcard2l]
      exact hcommComm_le
    have hZ1_le : Z1 L1 L2 S ≤ ⁅u3Y L1 L2 S, S⁆ := by
      intro z hz
      have hz' : z ∈ Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) := by
        rwa [← hZ1eq]
      have hzW : z ∈ W := by
        rw [← hZ2W]
        exact (Subgroup.mem_inf.mp hz').1
      let w : ↥W := ⟨z, hzW⟩
      have hzfix : Additive.ofMul (θ w) ∈ fixedSub ρ A := (hZ1fix w).mp hz
      have hzK : Additive.ofMul (θ w) ∈ Kbridge := hfixed_le hzfix
      have hzK' : Additive.ofMul (θ w) ∈ Subgroup.toAddSubgroup' KbridgeSub :=
        (AddSubgroup.mem_toZModSubmodule 2).mp hzK
      have hzKsub : θ w ∈ KbridgeSub :=
        (Subgroup.mem_toAddSubgroup' KbridgeSub (Additive.ofMul (θ w))).mp hzK' 
      obtain ⟨yYS, hyYS_eq⟩ := MonoidHom.mem_range.mp hzKsub
      have hθeq : θ w = θ ⟨yYS, hYWSleW yYS.2⟩ := by
        have h := hyYS_eq.symm
        have hincl : (Subgroup.inclusion hYWSleW yYS : ↥W) =
            ⟨yYS, hYWSleW yYS.2⟩ := rfl
        simpa [ΦY, hincl] using h
      have hweq : w = ⟨yYS, hYWSleW yYS.2⟩ := θ.injective hθeq
      have hz_eq : z = (yYS : G) := by
        have := congrArg Subtype.val hweq
        simpa [w] using this
      rw [hz_eq]
      exact yYS.2
    have hcommYS : ⁅u3Y L1 L2 S, S⁆ = Z1 L1 L2 S :=
      le_antisymm hcommYS_le hZ1_le
    exact (commutator_u3Y_s_eq_of_sup hF hES hEsup).trans hcommYS
  · have hWcard3' : Nat.card W = 2 ^ (8 * l) := by
      rw [hWcardEq]
      exact hWcard3
    exact (str86_third_case_false hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hE e T hTcoe hn3l hWcard3' hfix3).elim

theorem str86_l2_eq_and_z2
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    IsL2Quot (2 * k) (oTwoQuot ↥L2) ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4 ∧
      Nat.card (Z1 L1 L2 S) = 2 ^ k ∧
      Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3 ∧
      ⁅u3X1 L1 L2 S, u3X1 L1 L2 S⁆ = Z1 L1 L2 S ∧
      ⁅u3X1 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S :=
  str86_l2_eq_and_z2_of_bridge hF hSB hk hFc hU3 hB2 h2 hZI hZQ
    (str86YCommBridge_of_caseI hF hSB hk hFc hU3 hB2 h2 hZI hZQ)

end CFSG.Quasithin.Stroth

end
