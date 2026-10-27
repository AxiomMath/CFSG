module

public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146A0
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Setting146.relIndex_pCoreOf_of_isOFourPlusOn (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : IsOFourPlusOn T M H) : (pCoreOf 2 H).relIndex H = 72 := by
  obtain ⟨⟨hc16, q, hq1, hq2, hq3, hq4⟩, hker⟩ := h
  have h91 := (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have huK_le : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have huKN : uK T M H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (huK_le.trans hUQ).trans ((pCoreOf_le 2 H).trans hHN)
  have hHuK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  have hcard := card_autOn_secImg hHN huKN hHuK
  have hcard' : Nat.card (autOn (tildeOf (quasithinOmegaOneCenter T) H)
      (tildeOf (quasithinOmegaOneCenter T) (uK T M H))) = (pCoreOf 2 H).relIndex H := by
    unfold tildeOf
    rw [hcard]
    unfold uK at hker ⊢
    rw [hker]
  have hel : IsElemAbelian 2 (tildeOf (quasithinOmegaOneCenter T) (uK T M H)) :=
    F7.isElemAbelian_mono h91.isElemAbelian_tilde (secImg_mono huK_le)
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (uK T M H)) := commGroupOfElemAbelian hel
  have hexp : ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (uK T M H)), w * w = 1 := fun w =>
    Subtype.ext (by simpa [pow_two] using hel.2 w w.2)
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hc16 hq1 hq2 hq3
  rw [← hcard', hq4]
  exact hS.card_X

theorem Setting146.four_lt_relIndex_of_isOFourPlusOn (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : IsOFourPlusOn T M H) : 4 < (pCoreOf 2 H).relIndex T := by
  have h72 := S.relIndex_pCoreOf_of_isOFourPlusOn hH h
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hTsyl
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) T H hQT hTH
  have hodd : ¬ 2 ∣ T.relIndex H := hTsyl.2.2
  have hdvd : (pCoreOf 2 H).relIndex T ∣ Nat.card T := by
    have := Subgroup.index_dvd_card ((pCoreOf 2 H).subgroupOf T)
    exact this
  obtain ⟨n, hn⟩ := (S.hyp.sylow.1).exists_card_eq
  rw [hn] at hdvd
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [ha, h72] at hmul
  have ha6 : a ≤ 6 := by
    by_contra hlt
    have : 2 ^ 7 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ a ∣ 72 := ⟨T.relIndex H, hmul.symm⟩
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [ha]
  interval_cases a <;> simp_all <;> omega

end CFSG.Quasithin
