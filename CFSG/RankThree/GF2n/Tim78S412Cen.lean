module

public import CFSG.RankThree.GF2n.Tim78S412Torus
import CFSG.RankThree.GF2n.Tim78S4Closing
import CFSG.RankThree.GF2n.Tim78Frattini

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.Timmesfeld
open scoped commutatorElement

section General

variable {G : Type} [Group G]

@[expose] def normCommSub (N X : Subgroup G) (R : Set G)
    (hN : N ≤ Subgroup.normalizer (X : Set G)) : Subgroup G where
  carrier := {x | x ∈ N ∧ ∀ r ∈ R, ⁅x, r⁆ ∈ X}
  one_mem' := ⟨N.one_mem, fun r _ => by
    rw [commutatorElement_one_left]
    exact X.one_mem⟩
  mul_mem' := by
    rintro x x' ⟨hx, hxr⟩ ⟨hx', hx'r⟩
    refine ⟨N.mul_mem hx hx', fun r hr => ?_⟩
    have e : ⁅x * x', r⁆ = x * ⁅x', r⁆ * x⁻¹ * ⁅x, r⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hx) _).mp (hx'r r hr)) (hxr r hr)
  inv_mem' := by
    rintro x ⟨hx, hxr⟩
    refine ⟨N.inv_mem hx, fun r hr => ?_⟩
    have e : ⁅x⁻¹, r⁆ = x⁻¹ * ⁅x, r⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hN (N.inv_mem hx)) _).mp (X.inv_mem (hxr r hr))
    rwa [inv_inv] at this

end General

namespace Hyp4

variable {G : Type} [Group G] [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Root

section Mutual

variable (hmut : MutualPFull M B P g)
include hmut

theorem pair_B_le_Mg : B ≤ conjSubgroup g M := by
  rw [← H.normalizer_conj_eq g]
  exact le_normalizer_of_comm fun b hb a ha => H.outer_comm_B hmut.outer b hb a ha

theorem pair_B_not_mem_Qg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {x : G}
    (hx : x ∈ B) (hx1 : x ≠ 1) : x ∉ conjSubgroup g Q := by
  refine (H.conj g).outer_not_mem_Q hCen hU (H.outer_conj_of_mutual hmut).notLeP ?_ hx1
  rw [conjSubgroup_inv_conjSubgroup]
  exact hx

theorem pair_L_inf_P (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {l : G}
    (hl : l ∈ B ⊔ conjSubgroup g B) (hlP : l ∈ P) : l ∈ B := by
  have hAB : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_comm fun a ha b hb => (H.outer_comm_B hmut.outer b hb a ha).symm
  obtain ⟨b, hb, a, ha, rfl⟩ := exists_mul_of_mem_sup hAB hl
  have haP : a ∈ P := by
    have := P.mul_mem (P.inv_mem (H.B_le_P hb)) hlP
    rwa [inv_mul_cancel_left] at this
  have h1 : a ∈ conjSubgroup g B ⊓ P := ⟨ha, haP⟩
  rw [H.outer_inf_P hmut.outer hCen hU, Subgroup.mem_bot] at h1
  rw [h1, mul_one]
  exact hb

theorem pair_commutator_mem_L {a : G} (ha : a ∈ P ⊓ conjSubgroup g T) :
    ∀ x ∈ P ⊔ conjSubgroup g P, ⁅x, a⁆ ∈ B ⊔ conjSubgroup g B := by
  have hP : P ≤ normCommSub (Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G))
      (B ⊔ conjSubgroup g B) {a} le_rfl := fun p hp =>
    ⟨H.outer_P_le_normalizer_L hmut.outer hp, fun r hr => by
      rw [Set.mem_singleton_iff.mp hr]
      exact Subgroup.mem_sup_left (H.commutator_mem (H.P_le_Q hp) (H.P_le_Q ha.1))⟩
  have hPg : conjSubgroup g P ≤ normCommSub
      (Subgroup.normalizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G))
      (B ⊔ conjSubgroup g B) {a} le_rfl := fun u hu =>
    ⟨H.pair_Pg_le_normalizer_L hmut hu, fun r hr => by
      rw [Set.mem_singleton_iff.mp hr]
      have h1 : u * a = a * u := (H.conj_T_le_centralizer_conj_P g a ha.2 u hu).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr h1]
      exact one_mem _⟩
  intro x hx
  exact (sup_le hP hPg hx).2 a rfl

theorem pair_comm_of_normalizes (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {a x : G} (ha : a ∈ P ⊓ conjSubgroup g T) (hxH : x ∈ P ⊔ conjSubgroup g P)
    (hxB : conjSubgroup x B = B)
    (hxA : conjSubgroup x (conjSubgroup g B) = conjSubgroup g B) : x * a = a * x := by
  have hxM : x ∈ M := by
    rw [← H.normalizer_B]
    exact conjSubgroup_eq_self_iff.mp hxB
  have hxMg : x ∈ conjSubgroup g M := by
    rw [← H.normalizer_conj_eq g]
    exact conjSubgroup_eq_self_iff.mp hxA
  have h1 : ⁅x, a⁆ ∈ P := by
    have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := rfl
    rw [e]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P hxM) a).mp ha.1)
      (P.inv_mem ha.1)
  have h2 : ⁅x, a⁆ ∈ conjSubgroup g T := by
    have hxN : x ∈ Subgroup.normalizer (conjSubgroup g T : Set G) :=
      mem_normalizer_conj_of_mem_conj H.M_le_normalizer_T hxMg
    have e : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := rfl
    rw [e]
    exact (conjSubgroup g T).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN a).mp ha.2)
      ((conjSubgroup g T).inv_mem ha.2)
  have h3 : ⁅x, a⁆ ∈ B :=
    H.pair_L_inf_P hmut hCen hU (H.pair_commutator_mem_L hmut ha x hxH) h1
  have h4 : ⁅x, a⁆ ∈ B ⊓ conjSubgroup g T := ⟨h3, h2⟩
  rw [H.inf_B_conj_T_eq_bot hCen hU (H.outer_ne_B hmut.outer), Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4

theorem pair_inf_PTg (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    P ⊓ conjSubgroup g T = ⊥ := by
  obtain ⟨w, hwH, τ, hτH, ⟨hwB, hwA⟩, ⟨hτB, hτA, hτL⟩⟩ := H.pair_weyl_torus hmut hCen hU
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have hτa : τ * a = a * τ := H.pair_comm_of_normalizes hmut hCen hU ha hτH hτB hτA
  have hwB' : conjSubgroup w⁻¹ (conjSubgroup g B) = B := by
    rw [← hwB, conjSubgroup_inv_conjSubgroup]
  have hwA' : conjSubgroup w⁻¹ B = conjSubgroup g B := by
    calc conjSubgroup w⁻¹ B = conjSubgroup w⁻¹ (conjSubgroup w (conjSubgroup g B)) := by
          rw [hwA]
      _ = conjSubgroup g B := conjSubgroup_inv_conjSubgroup w _
  have hwτ : w⁻¹ * τ * w ∈ P ⊔ conjSubgroup g P :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwH) hτH) hwH
  have hB' : conjSubgroup (w⁻¹ * τ * w) B = B := by
    rw [conjSubgroup_mul, conjSubgroup_mul, hwB, hτA, hwB']
  have hA' : conjSubgroup (w⁻¹ * τ * w) (conjSubgroup g B) = conjSubgroup g B := by
    rw [conjSubgroup_mul, conjSubgroup_mul, hwA, hτB, hwA']
  have hτ' : (w⁻¹ * τ * w) * a = a * (w⁻¹ * τ * w) :=
    H.pair_comm_of_normalizes hmut hCen hU ha hwτ hB' hA'
  have hl : (w * a * w⁻¹) * a⁻¹ ∈ B ⊔ conjSubgroup g B :=
    H.pair_commutator_mem_L hmut ha w hwH
  have hwa : w * a * w⁻¹ = a := by
    have h1 : τ * (w * a * w⁻¹) * τ⁻¹ = w * a * w⁻¹ := by
      calc τ * (w * a * w⁻¹) * τ⁻¹ = w * ((w⁻¹ * τ * w) * a) * w⁻¹ * τ⁻¹ := by group
        _ = w * (a * (w⁻¹ * τ * w)) * w⁻¹ * τ⁻¹ := by rw [hτ']
        _ = w * a * w⁻¹ := by group
    have h2 : τ * a * τ⁻¹ = a := by
      rw [hτa]
      group
    have hfix : τ * ((w * a * w⁻¹) * a⁻¹) * τ⁻¹ = (w * a * w⁻¹) * a⁻¹ := by
      calc τ * ((w * a * w⁻¹) * a⁻¹) * τ⁻¹
          = (τ * (w * a * w⁻¹) * τ⁻¹) * (τ * a * τ⁻¹)⁻¹ := by group
        _ = (w * a * w⁻¹) * a⁻¹ := by rw [h1, h2]
    exact mul_inv_eq_one.mp (hτL _ hl hfix)
  have hPw : conjSubgroup w (conjSubgroup g P) = P := by
    have := H.conj_P_eq_of_conj_B_eq (x := w * g) (y := 1)
      (by rw [conjSubgroup_mul, hwA, conjSubgroup_one])
    rwa [conjSubgroup_mul, conjSubgroup_one] at this
  have hcomm : ∀ p ∈ P, a * p = p * a := by
    intro p hp
    have hu : w⁻¹ * p * w ∈ conjSubgroup g P := by
      have : p ∈ conjSubgroup w (conjSubgroup g P) := by
        rw [hPw]
        exact hp
      exact mem_conjSubgroup.mp this
    have hau : a * (w⁻¹ * p * w) = (w⁻¹ * p * w) * a :=
      H.conj_T_le_centralizer_conj_P g a ha.2 _ hu
    have hp' : p = w * (w⁻¹ * p * w) * w⁻¹ := by group
    calc a * p = a * (w * (w⁻¹ * p * w) * w⁻¹) := by rw [← hp']
      _ = (w * a * w⁻¹) * (w * (w⁻¹ * p * w) * w⁻¹) := by rw [hwa]
      _ = w * (a * (w⁻¹ * p * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * p * w) * a) * w⁻¹ := by rw [hau]
      _ = (w * (w⁻¹ * p * w) * w⁻¹) * (w * a * w⁻¹) := by group
      _ = p * a := by rw [← hp', hwa]
  have haB : a ∈ B := H.center_P_le_B a ha.1 hcomm
  have h5 : a ∈ B ⊓ conjSubgroup g T := ⟨haB, ha.2⟩
  rw [H.inf_B_conj_T_eq_bot hCen hU (H.outer_ne_B hmut.outer), Subgroup.mem_bot] at h5
  exact h5

theorem pair_centP_sq (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) {c : G}
    (hc : c ∈ centP B P g) : c * c = 1 := by
  by_contra hc2
  have hcP : c ∈ P := (mem_centP.mp hc).1
  have hb₀ : c * c ∈ B := by
    have := H.sq_mem (H.P_le_Q hcP)
    rwa [sq] at this
  have hcMg : c ∈ conjSubgroup g M := by
    obtain ⟨y, hy, hy1⟩ := H.exists_ne_one_mem_conj g
    exact H.centralizer_le_conj hy hy1 (Subgroup.mem_centralizer_singleton_iff.mpr
      ((mem_centP.mp hc).2 y hy))
  have hBN : conjSubgroup g B ≤ conjSubgroup g T := (H.conj g).B_le_T
  have hNQ : conjSubgroup g T ≤ conjSubgroup g Q := (H.conj g).T_le_Q
  have hMN : conjSubgroup g M ≤ Subgroup.normalizer (conjSubgroup g T : Set G) :=
    (H.conj g).M_le_normalizer_T
  have hΦ : inSubgroup frattini (conjSubgroup g T) = conjSubgroup g B :=
    (H.conj g).frattini_eq_B_of_ne hBN hNQ hMN (H.conj g).B_ne_T
  have hZ : conjSubgroup g T ⊓ Subgroup.centralizer (conjSubgroup g T : Set G) =
      conjSubgroup g B := (H.conj g).inf_centralizer_eq_B hBN hNQ hMN
  have hC : conjSubgroup g T ⊓ Subgroup.centralizer ({c} : Set G) =
      conjSubgroup g T ⊓ Subgroup.centralizer ({c ^ 2} : Set G) := by
    apply le_antisymm
    · intro t ht
      refine ⟨ht.1, ?_⟩
      have h1 : t * c = c * t := Subgroup.mem_centralizer_singleton_iff.mp ht.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.pow_right (show Commute t c from h1) 2).eq
    · intro t ht
      refine ⟨ht.1, ?_⟩
      obtain ⟨htT, htC⟩ := ht
      have htc2 : c * c * t = t * (c * c) := by
        rw [← sq]
        exact (Subgroup.mem_centralizer_singleton_iff.mp htC).symm
      have htM : t ∈ M :=
        H.normalizer_eq_and_centralizer_le.2 (c * c) hb₀ hc2
          (Subgroup.mem_centralizer_singleton_iff.mpr htc2.symm)
      have htQ : t ∈ conjSubgroup g Q := hNQ htT
      have htB : ∀ b ∈ B, b * t = t * b := by
        intro b hb
        have hbN : b ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) :=
          mem_normalizer_conj_of_mem_conj H.M_le_normalizer_Q (H.pair_B_le_Mg hmut hb)
        have h1 : ⁅b, t⁆ ∈ B := by
          have e : ⁅b, t⁆ = b * (t * b⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
          rw [e]
          exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_B htM) b⁻¹).mp
            (B.inv_mem hb))
        have h2 : ⁅b, t⁆ ∈ conjSubgroup g Q :=
          (conjSubgroup g Q).mul_mem ((Subgroup.mem_normalizer_iff.mp hbN t).mp htQ)
            ((conjSubgroup g Q).inv_mem htQ)
        by_contra hne
        exact H.pair_B_not_mem_Qg hmut hCen hU h1
          (fun h => hne (commutatorElement_eq_one_iff_mul_comm.mp h)) h2
      have hct : ⁅c, t⁆ ∈ P ⊓ conjSubgroup g T := by
        refine ⟨?_, ?_⟩
        · have e : ⁅c, t⁆ = c * (t * c⁻¹ * t⁻¹) := by simp only [commutatorElement_def]; group
          rw [e]
          exact P.mul_mem hcP ((Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_P htM) c⁻¹).mp
            (P.inv_mem hcP))
        · have hcN : c ∈ Subgroup.normalizer (conjSubgroup g T : Set G) := hMN hcMg
          have e : ⁅c, t⁆ = (c * t * c⁻¹) * t⁻¹ := rfl
          rw [e]
          exact (conjSubgroup g T).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN t).mp htT)
            ((conjSubgroup g T).inv_mem htT)
      rw [H.pair_inf_PTg hmut hCen hU, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at hct
      exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
  obtain ⟨-, hβ⟩ := tim78_2_2 (S := conjSubgroup g T) ((H.conj g).isPGroup_Q.to_le hNQ)
    (hΦ.trans hZ.symm).le (hMN hcMg)
    ⟨2, by
      rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul]
      exact H.sq_eq_one _ (H.sq_mem (H.P_le_Q hcP))⟩ hC
  rw [hΦ, sq] at hβ
  have hN : conjSubgroup g Q ≤ Subgroup.normalizer (conjSubgroup g B : Set G) := by
    rw [H.normalizer_conj_eq g]
    exact Subgroup.map_mono H.Q_le_M
  have hPgle : conjSubgroup g P ≤
      normCommSub (conjSubgroup g Q) (conjSubgroup g B) {c * c} hN :=
    fun u hu => ⟨Subgroup.map_mono H.P_le_Q hu, fun r hr => by
      rw [Set.mem_singleton_iff.mp hr, ← commutatorElement_inv]
      exact (conjSubgroup g B).inv_mem (hmut.partner _ hb₀ u hu)⟩
  have hTgle : conjSubgroup g T ≤
      normCommSub (conjSubgroup g Q) (conjSubgroup g B) {c * c} hN :=
    fun s hs => ⟨hNQ hs, fun r hr => by
      rw [Set.mem_singleton_iff.mp hr, ← commutatorElement_inv]
      have hsN : s ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := hN (hNQ hs)
      have e : ⁅c * c, s⁆ = s * (s⁻¹ * ((c * c) * s * (c * c)⁻¹)) * s⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (conjSubgroup g B).inv_mem ((Subgroup.mem_normalizer_iff.mp hsN _).mp (hβ s hs))⟩
  have hQg : ∀ r ∈ conjSubgroup g Q, ⁅r, c * c⁆ ∈ conjSubgroup g B := by
    intro r hr
    have hr' : r ∈ conjSubgroup g P ⊔ conjSubgroup g T := by
      rw [← (H.conj g).Q_eq_sup]
      exact hr
    exact (sup_le hPgle hTgle hr').2 (c * c) rfl
  have hMg : conjSubgroup g M ≤ Subgroup.normalizer (conjSubgroup g B : Set G) :=
    (H.normalizer_conj_eq g).ge
  have hb₀Z : c * c ∈ normCommSub (conjSubgroup g M) (conjSubgroup g B)
      (conjSubgroup g Q : Set G) hMg := ⟨H.pair_B_le_Mg hmut hb₀, fun r hr => by
    rw [← commutatorElement_inv]
    exact (conjSubgroup g B).inv_mem (hQg r hr)⟩
  have hzp := Subgroup.zpowers_le.mpr hb₀Z
  have hst : Subgroup.zpowers (c * c) ≤ conjSubgroup g Q :=
    (H.conj g).le_Q_of_stabilizes (A := Subgroup.zpowers (c * c))
      (Subgroup.zpowers_le.mpr (H.pair_B_le_Mg hmut hb₀)) fun m hm a ha r hr => by
      have h1 := hzp (mem_conjSubgroup.mp ha)
      have hmN : m⁻¹ ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) :=
        Subgroup.inv_mem _ (mem_normalizer_conj_of_mem_conj H.M_le_normalizer_Q hm)
      have h2 : m⁻¹ * r * m ∈ conjSubgroup g Q := by
        have := (Subgroup.mem_normalizer_iff.mp hmN r).mp hr
        rwa [inv_inv] at this
      have h3 := h1.2 _ h2
      have e : ⁅a, r⁆ = m * ⁅m⁻¹ * a * m, m⁻¹ * r * m⁆ * m⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hMg hm) _).mp h3
  exact H.pair_B_not_mem_Qg hmut hCen hU hb₀ hc2 (hst (Subgroup.mem_zpowers _))

end Mutual

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
