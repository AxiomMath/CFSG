module

import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.Quasithin.EmptyFaithful.S151ZA
public import CFSG.Quasithin.EmptyFaithful.S151ZB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem zb_two_pow {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hS2 : IsPGroup 2 ↥S) :
    ∀ x ∈ P ⊔ S, ∃ k : ℕ, x ^ 2 ^ k ∈ P := by
  intro x hx
  obtain ⟨p, hp, s, hs, rfl⟩ := zb_mem_sup hSP hx
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  refine ⟨k, ?_⟩
  obtain ⟨q, hq, hqe⟩ := zb_mul_pow_mem (hSP hs) hp (2 ^ k)
  have hsk : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hqe, hsk, mul_one]
  exact hq

theorem zb_charTwo_sup [Finite G] {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hS2 : IsPGroup 2 ↥S) (hP : CharTwo P) : CharTwo (P ⊔ S) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hP hS2 hSP

theorem zb_charTwo_of_le [Finite G] {L P : Subgroup G} (hL : CharTwo L) (hRP : pCoreOf 2 L ≤ P)
    (hPL : P ≤ L) : CharTwo P := CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hL hPL hRP

theorem zb_isMinParabolic_of [Finite G] {S H : Subgroup G} (hSH : IsSylowTwoOf S H)
    (hnn : ¬ H ≤ Subgroup.normalizer (S : Set G)) (hmax : ∀ K : Subgroup G, S ≤ K → K ≤ H → K = S ∨ K = H) :
    IsMinParabolicOf H H := by
  have hlt : S < H := lt_of_le_of_ne hSH.1 fun he => hnn (by rw [← he]; exact Subgroup.le_normalizer)
  have hmax' : IsMaxSubgroupIn H S := by
    refine ⟨hlt, fun K hSK hKH => ?_⟩
    rcases hmax K hSK.le hKH with h' | h'
    · exact absurd h' (ne_of_gt hSK)
    · exact h'
  have huniq : IsUniqueMaxOver H S S := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmax', le_rfl⟩, fun N hN => ?_⟩
    rcases hmax N hN.2 hN.1.1.le with h' | h'
    · exact h'
    · exact absurd h' (ne_of_lt hN.1.1)
  exact (minParabolic_iff.mp ⟨hSH, hnn, huniq⟩).1

structure SMin (L S P : Subgroup G) : Prop where
  le : P ≤ L
  sl : S ⊓ L ≤ P
  ne : S ⊓ L ≠ P
  sP : S ≤ Subgroup.normalizer (P : Set G)
  minimal : ∀ K : Subgroup G, S ≤ Subgroup.normalizer (K : Set G) → S ⊓ L ≤ K → K ≤ P →
    K = S ⊓ L ∨ K = P

variable {L S P : Subgroup G}

theorem SMin.inf_eq (h : SMin L S P) : P ⊓ S = S ⊓ L := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.2, h.le hx.1⟩
  · intro x hx
    exact ⟨h.sl hx, hx.1⟩

theorem SMin.S_maximal (h : SMin L S P) {K : Subgroup G} (hSK : S ≤ K) (hKH : K ≤ P ⊔ S) :
    K = S ∨ K = P ⊔ S := by
  have hSKn : S ≤ Subgroup.normalizer ((K ⊓ P : Subgroup G) : Set G) := by
    intro s hs
    exact zb_mem_normalizer_inf (show s ∈ Subgroup.normalizer (K : Set G) from
      Subgroup.le_normalizer (hSK hs)) (h.sP hs)
  have hBK : S ⊓ L ≤ K ⊓ P := le_inf (inf_le_left.trans hSK) h.sl
  rcases h.minimal (K ⊓ P) hSKn hBK inf_le_right with h1 | h1
  · left
    refine le_antisymm (fun k hk => ?_) hSK
    obtain ⟨p, hp, s, hs, rfl⟩ := zb_mem_sup h.sP (hKH hk)
    have hpK : p ∈ K := by
      have := K.mul_mem hk (K.inv_mem (hSK hs))
      simpa [mul_assoc] using this
    have hpB : p ∈ S ⊓ L := by
      rw [← h1]
      exact ⟨hpK, hp⟩
    exact S.mul_mem hpB.1 hs
  · right
    have hPK : P ≤ K := by
      rw [← h1]
      exact inf_le_left
    exact le_antisymm hKH (sup_le hPK hSK)

theorem SMin.isMinParabolic [Finite G] (h : SMin L S P) (hS2 : IsPGroup 2 ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (hselfN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L) :
    IsMinParabolicOf (P ⊔ S) (P ⊔ S) := by
  have hBP : IsSylowTwoOf (S ⊓ L) P := ya7_isSylowTwoOf_restrict hsyl h.sl h.le
  have e1 := zb_relIndex_sup h.sP
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ L) P (P ⊔ S) h.sl le_sup_left
  have e3 := Subgroup.relIndex_mul_relIndex (S ⊓ L) S (P ⊔ S) inf_le_left le_sup_right
  have e4 : (S ⊓ L).relIndex S = P.relIndex S := by
    rw [← h.inf_eq]
    exact Subgroup.inf_relIndex_right P S
  have hr : P.relIndex S ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card P S
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥S)).ne' h1.symm
  have e5 : S.relIndex (P ⊔ S) = (S ⊓ L).relIndex P := by
    rw [e1] at e2
    rw [e4] at e3
    have : (S ⊓ L).relIndex P * P.relIndex S = P.relIndex S * S.relIndex (P ⊔ S) := by
      rw [e2, e3]
    rw [mul_comm (P.relIndex S)] at this
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr) this).symm
  have hSH : IsSylowTwoOf S (P ⊔ S) := by
    refine ⟨le_sup_right, hS2, ?_⟩
    have h3 : (S.subgroupOf (P ⊔ S)).index = (S ⊓ L).relIndex P := e5
    rw [h3]
    exact hBP.2.2
  refine zb_isMinParabolic_of hSH ?_ fun K hSK hKH => h.S_maximal hSK hKH
  intro hH
  apply h.ne
  have hPN : P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    fun x hx => zb_mem_normalizer_inf (hH (Subgroup.mem_sup_left hx)) (Subgroup.le_normalizer (h.le hx))
  exact le_antisymm h.sl (fun x hx => (hselfN ⟨h.le hx, hPN hx⟩))

theorem bang_of_good [Finite G] (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G} (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) (hPL : P ≤ L)
    (hchar : CharTwo (P ⊔ s1516 T Z₁)) (hmin : IsMinParabolicOf (P ⊔ s1516 T Z₁) (P ⊔ s1516 T Z₁))
    (hno3 : ¬ C126Third (P ⊔ s1516 T Z₁) (s1516 T Z₁)) : P ≤ M ∨ P ≤ mZ1516 Mc Z₁ := by
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hHG : P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le (hPL.trans hLG) (s1516_le_g1 T Z₁)
  rcases star_general h118 h126 hc le_sup_right hHG hchar hmin hno3 with h | h
  · exact Or.inl (le_sup_left.trans h)
  · exact Or.inr (le_sup_left.trans h)

theorem zb_oPrime_mono {p : ℕ} {A B : Subgroup G} (h : A ≤ B) :
    oPrimeResidualOf p A ≤ oPrimeResidualOf p B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem centS15122_of [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G}
    (hc : Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L) (hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G))
    (hzl : ZL2 (s1516 T Z₁) L) (hPML : P ≤ M ⊓ L) (hnot : ¬ P ≤ mZ1516 Mc Z₁)
    (hoP : oPrimeResidualOf 3 P ⊔ (s1516 T Z₁ ⊓ L) = P) : CentS15122 T M Z₁ L := by
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hSMZ : S ≤ mZ1516 Mc Z₁ := fun x hx => ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hZS : quasithinOmegaOneCenter T ≤ S := fun z hz =>
    ⟨(zb_omega_le_center T hz).1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 y (hZ₁T hy)⟩
  have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ c ∈ S, z * c = c * z := fun z hz c hc' =>
    (Subgroup.mem_centralizer_iff.mp (zb_omega_le_center T hz).2 c (s1516_le T Z₁ hc')).symm
  have hSX : S ≤ Subgroup.normalizer ((oPrimeResidualOf 3 (M ⊓ L) : Subgroup G) : Set G) := by
    intro s hs
    exact zb_normalizes_oPrime (zb_mem_normalizer_inf (Subgroup.le_normalizer (hSM hs)) (hSN hs))
  have hX : ¬ ∀ x ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ z ∈ quasithinOmegaOneCenter T, x * z = z * x := by
    intro hall
    apply hnot
    have hXML : oPrimeResidualOf 3 (M ⊓ L) ≤ mZ1516 Mc Z₁ := by
      intro x hx
      have hxL : x ∈ L := (zb_oPrime_le hx).2
      have hxC : x ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun z hz => (hall x hx z hz).symm
      exact ⟨hLG hxL, hq.centralizer_le_mc hxC⟩
    have hBML : S ⊓ L ≤ mZ1516 Mc Z₁ := inf_le_left.trans hSMZ
    rw [← hoP]
    exact sup_le ((zb_oPrime_mono hPML).trans hXML) hBML
  unfold CentS15122
  exact centS_of_zl2 hSN hS2 (zb_oPrime_le.trans inf_le_right) hSX hZS (zb_omega_sq T) hZc hzl hX

end CFSG.Quasithin
