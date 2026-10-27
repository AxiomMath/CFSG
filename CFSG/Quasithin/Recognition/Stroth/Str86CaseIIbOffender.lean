module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.Background.Harris.R1.Q8Ker
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexM6
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoBound

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_inf_centralizer_z2_of_caseIIb
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {m : ℕ} (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ ≠ ⊥) :
    S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S := by
  classical
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hQS : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hSH : S ≤ u3H L1 L2 S := str86_s_le_u3H hF hSB hm hL2
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hZcentQ : Z2 L1 L2 S ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S)).trans
      (A4.centerOf_le_centralizer (Q2 L1 L2 S))
  have hQcent : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    Subgroup.le_centralizer_iff.mp hZcentQ
  let H : Subgroup G := u3H L1 L2 S
  let K : Subgroup G := H ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)
  have hKH : K ≤ H := inf_le_left
  have hHnorm : H ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hHnormC : H ≤
      Subgroup.normalizer (Subgroup.centralizer (Z2 L1 L2 S : Set G) : Set G) :=
    hHnorm.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S))
  have hKn : ∀ h ∈ H, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    intro h hh x hx
    exact (Subgroup.mem_normalizer_iff.mp
      (A4.mem_normalizer_inf (Subgroup.le_normalizer hh) (hHnormC hh)) x).mp hx
  have hQK : Q2 L1 L2 S ≤ K := le_inf hQH hQcent
  have hpCore : pCoreOf 2 H = Q2 L1 L2 S := str86_pCoreOf_u3H hF
  have hsimple : IsSimpleGroup (oTwoQuot ↥H) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hm (str86_isL2Quot_u3H hF hL2)
  rcases CFSG.Quasithin.Background.Harris.R1.normal_eq_pCore_or_top hsimple hKH hKn
    (by rw [hpCore]; exact hQK) with hK | hK
  · rw [hpCore] at hK
    refine le_antisymm ?_ (le_inf hQS hQcent)
    calc S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)
        ≤ H ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) := inf_le_inf_right _ hSH
      _ = K := rfl
      _ = Q2 L1 L2 S := hK
  · exfalso
    apply hJZ
    have hJcent : thompsonJ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      (thompsonJ_le_self S).trans (hSH.trans (hK.trans inf_le_right))
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hJcent

theorem str86_caseIIb_offender
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {m : ℕ} (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJZ : ⁅Z2 L1 L2 S, thompsonJ S⁆ ≠ ⊥) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ A ⊔ Q2 L1 L2 S = S ∧
      (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m ∧
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ m ∧
      Nat.card (Z2 L1 L2 S) =
        (A ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex A *
          Nat.card (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
  classical
  let H : Subgroup G := u3H L1 L2 S
  let Q : Subgroup G := Q2 L1 L2 S
  let Z : Subgroup G := Z2 L1 L2 S
  have hS2 : S = (S ⊓ L2) ⊔ Q := by
    simpa [Q] using
      eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hQS : Q ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hSH : S ≤ H := str86_s_le_u3H hF hSB hm hL2
  have hQH : Q ≤ H := q2_le_u3H L1 L2 S
  have hZH : Z ≤ H := (A4.omegaOneCenterOf_le Q).trans hQH
  have hZQ : Z ≤ Q := A4.omegaOneCenterOf_le Q
  have hZleS : Z ≤ S := hZQ.trans hQS
  have hZea : IsElemAbelian 2 Z := B2F.isElemAbelian_omegaOneCenterOf Q
  have hZcentQ : Z ≤ Subgroup.centralizer (Q : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf Q).trans (A4.centerOf_le_centralizer Q)
  have hQcent : Q ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp hZcentQ
  have hL2H : IsL2Quot m (oTwoQuot ↥H) := str86_isL2Quot_u3H hF hL2
  have hpCore : pCoreOf 2 H = Q := str86_pCoreOf_u3H hF
  have hnormZ : H ≤ Subgroup.normalizer (Z : Set G) := str86_z2_normal_u3H L1 L2 S
  have hCZ : S ⊓ Subgroup.centralizer (Z : Set G) = Q :=
    str86_inf_centralizer_z2_of_caseIIb hF hSB hm hL2 hII hJZ
  have hex : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ⁅Z, A⁆ ≠ ⊥ := by
    by_contra h
    have hzero : ∀ A : Subgroup G, IsMaxElemAbelian S A → ⁅Z, A⁆ = ⊥ := by
      intro A hA
      by_contra hne
      exact h ⟨A, hA, hne⟩
    have hJcent : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) := by
      rw [thompsonJ]
      refine iSup_le fun A => ?_
      refine iSup_le fun hA => ?_
      exact Subgroup.le_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Z) (H₂ := A)).mp
          (hzero A hA))
    exact hJZ (by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hJcent)
  obtain ⟨A, hA, hAZ⟩ := hex
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAS : A ≤ S := hA.1
  have hAH : A ≤ H := hAS.trans hSH
  have hAQ : ¬ A ≤ Q := by
    intro hAle
    exact hAZ (by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hAle.trans hQcent))
  have hnotsub : ¬ (A : Set G) ⊆ (Q : Set G) := hAQ
  obtain ⟨t, htA, htQ⟩ := Set.not_subset.mp hnotsub
  have ht2 : t * t ∈ pCoreOf 2 H := by
    have hsq : t * t = 1 := hAe.mul_self_eq_one htA
    rw [hsq]
    exact (pCoreOf 2 H).one_mem
  have htO : t ∉ pCoreOf 2 H := by
    rw [hpCore]
    exact htQ
  have hnorm : IsNormalIn H Z Z := by
    refine ⟨le_rfl, fun g hg x hx => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hnormZ hg) x).mp hx
  obtain ⟨c, hser⟩ :=
    CFSG.Quasithin.D15Proof.exists_isChiefSeriesFrom (H := H) (U := Z) Z hnorm
  have hsupH : oTwoUpper H ⊔ Q = H := by
    haveI hperf : Group.IsPerfect (oTwoQuot ↥H) := isPerfect_of_isL2Quot hm hL2H
    let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    have htop : oTwoUpper (⊤ : Subgroup (oTwoQuot ↥H)) = ⊤ :=
      C2Nine.oTwoUpper_eq_of_perfect (Subgroup.commutator_eq_self (H := ⊤))
    have hmap := oTwoUpper_map (G' := oTwoQuot ↥H) π (⊤ : Subgroup ↥H)
    rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hsurj, htop] at hmap
    have hKtop : Subgroup.map π (oTwoUpper (⊤ : Subgroup ↥H)) = ⊤ := hmap.symm
    have hsup' : oTwoUpper (⊤ : Subgroup ↥H) ⊔ π.ker = ⊤ := by
      have h := Subgroup.comap_map_eq (f := π) (H := oTwoUpper (⊤ : Subgroup ↥H))
      rw [hKtop, Subgroup.comap_top] at h
      exact h.symm
    have hker : π.ker = CFSG.pCore 2 ↥H := QuotientGroup.ker_mk' _
    have hmap2 : (oTwoUpper (⊤ : Subgroup ↥H) ⊔ CFSG.pCore 2 ↥H).map H.subtype = H := by
      rw [hker] at hsup'
      rw [hsup', Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, ← oTwoUpper_map H.subtype (⊤ : Subgroup ↥H), Subgroup.map_top,
      Subgroup.range_subtype] at hmap2
    have hp : Subgroup.map H.subtype (CFSG.pCore 2 ↥H) = Q := by
      simpa [pCoreOf] using hpCore
    rw [hp] at hmap2
    exact hmap2
  have hc1 : 1 ≤ c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    have hzero : ⁅Z, oTwoUpper H⁆ = ⊥ :=
      CFSG.Quasithin.D14.commutator_eq_bot_of_zero hZea.isPGroup hser hc0
    have hO2cent : oTwoUpper H ≤ Subgroup.centralizer (Z : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (by
        rw [Subgroup.commutator_comm]
        exact hzero)
    have hHcent : H ≤ Subgroup.centralizer (Z : Set G) := by
      rw [← hsupH]
      exact sup_le hO2cent hQcent
    have hJcent : thompsonJ S ≤ Subgroup.centralizer (Z : Set G) :=
      (thompsonJ_le_self S).trans (hSH.trans hHcent)
    exact hJZ (by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hJcent)
  have hM6 : (2 ^ m) ^ c ≤
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Z :=
    l2_pow_sq_le_relIndex_centralizer (H := H) (U := Z) hm hL2H hZea.isPGroup hZH hser
      (hSH (hAS htA)) ht2 htO
  have hpow : 2 ^ m ≤ (2 ^ m) ^ c := by
    have h := Nat.pow_le_pow_right (Nat.one_le_pow m 2 (by norm_num)) hc1
    simpa using h
  have h1 : 2 ^ m ≤
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Z :=
    hpow.trans hM6
  have hconv : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Z =
      (Z ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Z := by
    rw [← Subgroup.inf_relIndex_right
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) Z, inf_comm]
  rw [hconv] at h1
  have hmono : Z ⊓ Subgroup.centralizer (A : Set G) ≤
      Z ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    inf_le_inf_left Z (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htA))
  have h2 : (Z ⊓ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex Z ≤
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z :=
    Subgroup.relIndex_le_of_le_left hmono (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
  have h6 : 2 ^ m ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := h1.trans h2
  have hTR := card_le_relIndex_mul_card hZea hZleS hA
  have hZcard : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z *
      Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) = Nat.card Z := by
    have h := Subgroup.relIndex_mul_card (H := Z ⊓ Subgroup.centralizer (A : Set G)) (K := Z)
    rwa [inf_eq_left.mpr inf_le_left] at h
  have h3 : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z ≤
      (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A := by
    refine Nat.le_of_mul_le_mul_right ?_
      (Nat.card_pos (α := ↥(Z ⊓ Subgroup.centralizer (A : Set G))))
    calc (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z *
          Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G)
        = Nat.card Z := hZcard
      _ ≤ (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A *
          Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hTR
  have h4 : (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A =
      (A ⊓ Q).relIndex A := by
    have hAC : A ⊓ Subgroup.centralizer (Z : Set G) =
        A ⊓ (S ⊓ Subgroup.centralizer (Z : Set G)) := by
      rw [← inf_assoc, inf_eq_left.mpr hAS]
    rw [hAC, hCZ]
  have h5 : (A ⊓ Q).relIndex A ≤ 2 ^ m := by
    have h := relIndex_inf_pCoreOf_le_two_pow (H := H) (A := A) hm hL2H hAH hAe
    rwa [hpCore] at h
  have hle_chain : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z ≤ 2 ^ m :=
    h3.trans (h4.trans_le h5)
  have hZrel : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = 2 ^ m :=
    le_antisymm hle_chain h6
  have hAreal : (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A = 2 ^ m := by
    refine le_antisymm (h4 ▸ h5) ?_
    calc 2 ^ m = (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := hZrel.symm
      _ ≤ (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A := h3
  have hAQrel : (A ⊓ Q).relIndex A = 2 ^ m := by
    rw [← h4]
    exact hAreal
  have hAnorm : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAS.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hrelAQ : Q.relIndex (A ⊔ Q) = 2 ^ m := by
    have h1 : Q.relIndex (A ⊔ Q) = Q.relIndex A :=
      F1.relIndex_sup_eq_of_le_normalizer hAnorm
    have h2 : Q.relIndex A = 2 ^ m := by
      rw [← Subgroup.inf_relIndex_right (H := Q) (K := A), inf_comm]
      exact hAQrel
    exact h1.trans h2
  have hrelS : Q.relIndex S = 2 ^ m := str86_relIndex_q2_s hF hSB hm hL2
  have hAQle : A ⊔ Q ≤ S := sup_le hAS hQS
  have hcardX : Nat.card ↥(A ⊔ Q) = Nat.card ↥S := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := A ⊔ Q)
    have h2 := Subgroup.relIndex_mul_card (H := Q) (K := S)
    rw [inf_eq_left.mpr le_sup_right] at h1
    rw [inf_eq_left.mpr hQS] at h2
    rw [hrelAQ] at h1
    rw [hrelS] at h2
    rw [← h1, ← h2]
  have hAQeq : A ⊔ Q = S := Subgroup.eq_of_le_of_card_ge hAQle hcardX.ge
  refine ⟨A, hA, ?_, ?_, ?_, ?_⟩
  · simpa [Q] using hAQeq
  · simpa [Q] using hAQrel
  · simpa [Z] using hZrel
  · have hZcard' : Nat.card Z =
        (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z *
          Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hZcard.symm
    calc Nat.card Z
        = (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z *
            Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := hZcard'
      _ = 2 ^ m * Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
            rw [hZrel]
      _ = (A ⊓ Subgroup.centralizer (Z : Set G)).relIndex A *
            Nat.card (Z ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := by
            rw [hAreal]

end CFSG.Quasithin.Stroth

end
