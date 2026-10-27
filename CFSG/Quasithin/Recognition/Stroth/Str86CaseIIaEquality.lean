module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaExchange

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem centralizer_zpowers_eq_singleton (t : G) :
    Subgroup.centralizer (Subgroup.zpowers t : Set G) =
      Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem relIndex_cjSub {A B : Subgroup G} (g : G) :
    (cjSub g A).relIndex (cjSub g B) = A.relIndex B := by
  unfold cjSub
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

private theorem le_centralizer_conjClosure_of_conj {B Z H : Subgroup G}
    (h : ∀ g ∈ H, B ≤ Subgroup.centralizer (cjSub g Z : Set G)) :
    B ≤ Subgroup.centralizer (conjClosure Z H : Set G) := by
  intro b hb
  have hle : conjClosure Z H ≤ Subgroup.centralizer ({b} : Set G) := by
    refine conjClosure_le fun g hg z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.mp (h g hg hb) (g * z * g⁻¹)
      (mem_cjSub.mpr (by
        show g⁻¹ * (g * z * g⁻¹) * g ∈ Z
        rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group]))).symm
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) b rfl).symm

private theorem cjSub_le_centralizer_of_le_centralizer {Q Z : Subgroup G} {g : G}
    (h : Q ≤ Subgroup.centralizer (Z : Set G)) :
    cjSub g Q ≤ Subgroup.centralizer (cjSub g Z : Set G) := by
  rw [← B2F.cjSub_centralizer]
  exact cjSub_mono h

theorem str86_isSzU3Quot_of_statedSU {L1 : Subgroup G} {k : ℕ} (hk : 2 ≤ k) {F : Type}
    [Field F] [Finite F] (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) :
    IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
  Or.inr ⟨k, hk, rfl, F, inferInstance, inferInstance, hFc, hU3⟩

theorem str86_isL2Quot_sup_of_caseII
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm2, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  obtain ⟨eL2⟩ := hL2
  rw [hsup2, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ Q1 L2 L1 S by rw [Q1, Q2, P1, P2, bigB_comm]]
  exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL2⟩

theorem str86_pCoreOf_sup_eq_q2
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm2, hL2⟩))
  rw [sup_eq_of_S_eq_right hS2]
  have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

theorem str86_q2_le_s
    {L1 L2 S : Subgroup G} {m : ℕ}
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hm2 : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    Q2 L1 L2 S ≤ S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm2, hL2⟩))
  conv_rhs => rw [hS2]
  exact le_sup_right

theorem str86_l2sup_le_normalizer_q2 {L1 L2 S : Subgroup G} :
    L2 ⊔ S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
  (sup_le le_sup_left
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))

theorem str86_two_equality_chain
    {L1 L2 S : Subgroup G} {k m : ℕ}
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k)) (hm2 : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hUe : IsElemAbelian 2 (str86U L1 L2 S))
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) (hAQ2 : ¬ A ≤ Q2 L1 L2 S) :
    (Subgroup.centralizer ((A ⊓ Q2 L1 L2 S : Subgroup G) : Set G)).relIndex
        (str86U L1 L2 S) = (2 ^ m) ^ 2 ∧
      (Subgroup.centralizer (A : Set G)).relIndex (str86U L1 L2 S) = (2 ^ m) ^ 2 ∧
      (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex (A ⊓ Q2 L1 L2 S) = 2 ^ m ∧
      (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m := by
  let U : Subgroup G := str86U L1 L2 S
  have hUe' : IsElemAbelian 2 U := hUe
  have hU2 : IsPGroup 2 U := hUe'.isPGroup
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) := str86_isL2Quot_sup_of_caseII hF.toW hB hm2 hL2
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := str86_pCoreOf_sup_eq_q2 hF.toW hB hm2 hL2
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hB hm2 hL2
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAS : A ≤ S := hA.1
  have hAH : A ≤ L2 ⊔ S := hAS.trans le_sup_right
  have hUQ2 : U ≤ Q2 L1 L2 S := by
    refine conjClosure_le fun g hg z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (str86_l2sup_le_normalizer_q2 hg) z).mp (hZ hz)
  have hUS : U ≤ S := hUQ2.trans hQ2S
  have hUH : U ≤ L2 ⊔ S := hUS.trans le_sup_right
  set B0 : Subgroup G := A ⊓ Q2 L1 L2 S with hB0def
  have hB0A : B0 ≤ A := by rw [hB0def]; exact inf_le_left
  have hB0Q2 : B0 ≤ Q2 L1 L2 S := by rw [hB0def]; exact inf_le_right
  have hB0e : IsElemAbelian 2 B0 := hAe.mono hB0A
  obtain ⟨t, htA, htQ2⟩ := Set.not_subset.mp hAQ2
  have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) (hAS htA)
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    exact hAe.2 t htA
  have htO : t ∉ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  have htQ : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [ht2]
    exact (pCoreOf 2 (L2 ⊔ S)).one_mem
  set a : ℕ := (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A with hadef
  set b : ℕ := (Subgroup.centralizer (U : Set G)).relIndex B0 with hbdef
  set x : ℕ := (Subgroup.centralizer (A : Set G)).relIndex U with hxdef
  have hCU_A : U ⊓ Subgroup.centralizer (A : Set G) = A ⊓ U := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨hyU, hyC⟩ := hy
      refine ⟨?_, hyU⟩
      have hy2 : y ^ 2 = 1 := by rw [hUe'.2 y hyU]
      have hEA : IsElemAbelian 2 (A ⊔ Subgroup.zpowers y) :=
        IsElemAbelian.sup_of_commute hAe (isElemAbelian_zpowers hy2)
          (fun a ha b hb =>
            Subgroup.mem_centralizer_iff.mp
              (Subgroup.zpowers_le.mpr hyC hb) a ha)
      have hEAS : A ⊔ Subgroup.zpowers y ≤ S :=
        sup_le hAS (Subgroup.zpowers_le.mpr (hUS hyU))
      have hmax := hA.2.2 (A ⊔ Subgroup.zpowers y) hEAS hEA
      have heq : A = A ⊔ Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge le_sup_left hmax
      rw [heq]
      exact (le_sup_right : Subgroup.zpowers y ≤ A ⊔ Subgroup.zpowers y)
        (Subgroup.mem_zpowers y)
    · rintro y ⟨hyA, hyU⟩
      exact ⟨hyU, fun a ha => IsElemAbelian.comm hAe ha hyA⟩
  have hxeq : x = A.relIndex U := by
    rw [hxdef]
    calc (Subgroup.centralizer (A : Set G)).relIndex U
        = (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U :=
            (Subgroup.inf_relIndex_left U (Subgroup.centralizer (A : Set G))).symm
      _ = (A ⊓ U).relIndex U := by rw [hCU_A]
      _ = A.relIndex U := Subgroup.inf_relIndex_right A U
  have hTR := card_le_relIndex_mul_card hUe' hUS hA
  have hTR' : A.relIndex U * Nat.card ↥(A ⊓ U) ≤ a * Nat.card ↥(A ⊓ U) := by
    calc A.relIndex U * Nat.card ↥(A ⊓ U) = Nat.card U :=
          Subgroup.relIndex_mul_card A U
      _ ≤ (A ⊓ Subgroup.centralizer (U : Set G)).relIndex A *
            Nat.card ↥(U ⊓ Subgroup.centralizer (A : Set G)) := hTR
      _ = a * Nat.card ↥(A ⊓ U) := by rw [hCU_A]
  have hxa : x ≤ a := by
    have h := Nat.le_of_mul_le_mul_right hTR' Nat.card_pos
    rwa [← hxeq] at h
  have hale : a ≤ B0.relIndex A * b := by
    set C : Subgroup G := A ⊓ Subgroup.centralizer (U : Set G) with hCdef
    have hCa : C ≤ A := by rw [hCdef]; exact inf_le_left
    have hsupA : B0 ⊔ C ≤ A := sup_le hB0A hCa
    have hB0le : B0 ≤ B0 ⊔ C := le_sup_left
    have hCle : C ≤ B0 ⊔ C := le_sup_right
    have hCN : B0 ≤ Subgroup.normalizer (C : Set G) := by
      have hB0C : B0 ≤ Subgroup.centralizer (C : Set G) := by
        intro bb hbb
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        have hcA : c ∈ A := by rw [hCdef] at hc; exact hc.1
        exact IsElemAbelian.comm hAe hcA (hB0A hbb)
      exact hB0C.trans (Subgroup.centralizer_le_normalizer (C : Set G))
    have hsup : C.relIndex (B0 ⊔ C) = C.relIndex B0 :=
      A4.relIndex_sup_eq_of_le_normalizer' hCN
    have hmul : C.relIndex (B0 ⊔ C) * (B0 ⊔ C).relIndex A = C.relIndex A :=
      Subgroup.relIndex_mul_relIndex C (B0 ⊔ C) A hCle hsupA
    have hle : (B0 ⊔ C).relIndex A ≤ B0.relIndex A :=
      Subgroup.relIndex_le_of_le_left hB0le (Subgroup.index_ne_zero_of_finite)
    have hCb : C.relIndex B0 = b := by
      rw [hbdef]
      calc C.relIndex B0 = (C ⊓ B0).relIndex B0 :=
            (Subgroup.inf_relIndex_right C B0).symm
        _ = (Subgroup.centralizer (U : Set G) ⊓ B0).relIndex B0 := by
            congr 1
            ext y
            simp only [hCdef, Subgroup.mem_inf]
            constructor
            · rintro ⟨⟨hyA, hyC⟩, hyB⟩
              exact ⟨hyC, hyB⟩
            · rintro ⟨hyC, hyB⟩
              exact ⟨⟨hB0A hyB, hyC⟩, hyB⟩
        _ = (Subgroup.centralizer (U : Set G)).relIndex B0 :=
            Subgroup.inf_relIndex_right _ B0
    calc a = C.relIndex A := rfl
      _ = C.relIndex (B0 ⊔ C) * (B0 ⊔ C).relIndex A := hmul.symm
      _ = C.relIndex B0 * (B0 ⊔ C).relIndex A := by rw [hsup]
      _ ≤ C.relIndex B0 * B0.relIndex A := Nat.mul_le_mul_left _ hle
      _ = B0.relIndex A * b := by rw [hCb]; ring
  have hB0rel : B0.relIndex A ≤ 2 ^ m := by
    have hpow := relIndex_inf_pCoreOf_le_two_pow hm2 hL2sup hAH hAe
    rwa [hpCore2, ← hB0def] at hpow
  have hb2x : b ^ 2 ≤ x := by
    have h := (str86_exchange_bound hF hB hq hm2 hL2 hII hZ hB0Q2 hB0e).1
    rw [hbdef, hxdef]
    refine h.trans ?_
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le hB0A) (Subgroup.index_ne_zero_of_finite)
  have hbm : b ≤ 2 ^ m := by
    have hbpos : 0 < b := by
      rw [hbdef]
      exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    refine Nat.le_of_mul_le_mul_right ?_ hbpos
    calc b * b = b ^ 2 := (pow_two b).symm
      _ ≤ x := hb2x
      _ ≤ a := hxa
      _ ≤ B0.relIndex A * b := hale
      _ ≤ 2 ^ m * b := Nat.mul_le_mul_right b hB0rel
  have hl2 := l2_pow_sq_le_relIndex_centralizer hm2 hL2sup hU2 hUH hc htH htQ htO
  have hl2x : (Subgroup.centralizer (Subgroup.zpowers t : Set G)).relIndex U ≤ x := by
    rw [hxdef]
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htA))
      (Subgroup.index_ne_zero_of_finite)
  have hrx : (2 ^ m) ^ 2 ≤ x := hl2.trans hl2x
  have hb_ge : 2 ^ m ≤ b := by
    have hrpos : 0 < 2 ^ m := by positivity
    have h1 : 2 ^ m * 2 ^ m ≤ 2 ^ m * b := by
      calc 2 ^ m * 2 ^ m = (2 ^ m) ^ 2 := (pow_two _).symm
        _ ≤ x := hrx
        _ ≤ a := hxa
        _ ≤ B0.relIndex A * b := hale
        _ ≤ 2 ^ m * b := Nat.mul_le_mul_right b hB0rel
    exact Nat.le_of_mul_le_mul_left h1 hrpos
  have hb : b = 2 ^ m := le_antisymm hbm hb_ge
  have hx2 : x ≤ (2 ^ m) ^ 2 := by
    calc x ≤ a := hxa
      _ ≤ B0.relIndex A * b := hale
      _ ≤ 2 ^ m * 2 ^ m := by rw [hb]; exact Nat.mul_le_mul_right _ hB0rel
      _ = (2 ^ m) ^ 2 := by ring
  have hx_eq : x = (2 ^ m) ^ 2 := le_antisymm hx2 hrx
  have hUB0 : (Subgroup.centralizer (B0 : Set G)).relIndex U = (2 ^ m) ^ 2 := by
    have h := (str86_exchange_bound hF hB hq hm2 hL2 hII hZ hB0Q2 hB0e).1
    have h2 : (Subgroup.centralizer (B0 : Set G)).relIndex U ≤ x := by
      rw [hxdef]
      exact Subgroup.relIndex_le_of_le_left
        (Subgroup.centralizer_le hB0A) (Subgroup.index_ne_zero_of_finite)
    refine le_antisymm (h2.trans (le_of_eq hx_eq)) ?_
    rw [← hb]
    exact h
  have hB0A_eq : B0.relIndex A = 2 ^ m := by
    refine le_antisymm hB0rel ?_
    have h1 : 2 ^ m * 2 ^ m ≤ B0.relIndex A * 2 ^ m := by
      calc 2 ^ m * 2 ^ m = (2 ^ m) ^ 2 := (pow_two _).symm
        _ = x := hx_eq.symm
        _ ≤ a := hxa
        _ ≤ B0.relIndex A * b := hale
        _ = B0.relIndex A * 2 ^ m := by rw [hb]
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  exact ⟨hUB0, hx_eq, hb, hB0A_eq⟩

theorem str86_caseIIa_two_small_involution
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2) :
    ∃ t ∈ Q2 L1 L2 S, t ∉ Q1 L1 L2 S ∧ t * t = 1 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) ≤ (2 ^ k) ^ 2 := by
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) := str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hm2 : 2 ≤ m := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hUe : IsElemAbelian 2 (str86U L1 L2 S) :=
    isElemAbelian_str86U_of_caseII hF hB hq hm2 hL2 hII hZ
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S := not_thompsonJ_le_Q2_of_caseII hF.toW hB hB1 hII
  have hAexists : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q2 L1 L2 S := by
    by_contra h
    have hall : ∀ A : Subgroup G, IsMaxElemAbelian S A → A ≤ Q2 L1 L2 S := by
      intro A hA
      by_contra hAQ
      exact h ⟨A, hA, hAQ⟩
    exact hJQ2 (by
      rw [thompsonJ]
      exact iSup₂_le hall)
  obtain ⟨A, hA, hAQ2⟩ := hAexists
  obtain ⟨hUB0, -, hb, -⟩ := str86_two_equality_chain hF hB hq hm2 hL2 hII hZ hUe hc hA hAQ2
  have hB0nc : ¬ (A ⊓ Q2 L1 L2 S) ≤
      Subgroup.centralizer (str86U L1 L2 S : Set G) := by
    intro hle
    have h1 : (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex
        (A ⊓ Q2 L1 L2 S) = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hb] at h1
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨g, hgH, hg⟩ : ∃ g ∈ L2 ⊔ S,
      ¬ (A ⊓ Q2 L1 L2 S) ≤ Subgroup.centralizer (cjSub g (Z1 L1 L2 S) : Set G) := by
    by_contra h
    apply hB0nc
    refine le_centralizer_conjClosure_of_conj ?_
    intro g' hg'
    by_contra h'
    exact h ⟨g', hg', h'⟩
  have hQ2inv : cjSub g⁻¹ (Q2 L1 L2 S) = Q2 L1 L2 S :=
    B2F.cjSub_eq_of_mem_normalizer (str86_l2sup_le_normalizer_q2 ((L2 ⊔ S).inv_mem hgH))
  have hUinv : cjSub g⁻¹ (str86U L1 L2 S) = str86U L1 L2 S :=
    B2F.cjSub_eq_of_mem_normalizer (le_normalizer_conjClosure (Z1 L1 L2 S) (L2 ⊔ S)
      ((L2 ⊔ S).inv_mem hgH))
  have hUinv' : cjSub g (str86U L1 L2 S) = str86U L1 L2 S := by
    have h := congrArg (cjSub g) hUinv
    rw [cjSub_cjSub_inv] at h
    exact h.symm
  set Zg : Subgroup G := cjSub g (Z1 L1 L2 S) with hZg
  set B1 : Subgroup G := cjSub g⁻¹ (A ⊓ Q2 L1 L2 S) with hB1def
  have hB1Q2 : B1 ≤ Q2 L1 L2 S := by
    rw [hB1def]
    calc cjSub g⁻¹ (A ⊓ Q2 L1 L2 S) ≤ cjSub g⁻¹ (Q2 L1 L2 S) :=
          cjSub_mono inf_le_right
      _ = Q2 L1 L2 S := hQ2inv
  have hB1e : IsElemAbelian 2 B1 := isElemAbelian_cjSub (hA.2.1.mono inf_le_left)
  have hB0_eq : cjSub g B1 = A ⊓ Q2 L1 L2 S := by
    rw [hB1def]
    exact cjSub_cjSub_inv g (A ⊓ Q2 L1 L2 S)
  have hC_B1 : cjSub g (Subgroup.centralizer (B1 : Set G)) =
      Subgroup.centralizer ((A ⊓ Q2 L1 L2 S : Subgroup G) : Set G) := by
    rw [B2F.cjSub_centralizer, hB0_eq]
  have hC_U : cjSub g (Subgroup.centralizer (str86U L1 L2 S : Set G)) =
      Subgroup.centralizer (str86U L1 L2 S : Set G) := by
    rw [B2F.cjSub_centralizer, hUinv']
  have hmain := (str86_exchange_bound hF hB hq hm2 hL2 hII hZ hB1Q2 hB1e).2
  have e1 : (Subgroup.centralizer (B1 : Set G)).relIndex (Z1 L1 L2 S) =
      (Subgroup.centralizer ((A ⊓ Q2 L1 L2 S : Subgroup G) : Set G)).relIndex Zg := by
    rw [← relIndex_cjSub (A := Subgroup.centralizer (B1 : Set G))
      (B := Z1 L1 L2 S) g, hC_B1]
  have e2 : (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex B1 =
      (Subgroup.centralizer (str86U L1 L2 S : Set G)).relIndex
        (A ⊓ Q2 L1 L2 S) := by
    rw [← relIndex_cjSub (A := Subgroup.centralizer (str86U L1 L2 S : Set G))
      (B := B1) g, hC_U, hB0_eq]
  have e3 : (Subgroup.centralizer (B1 : Set G)).relIndex (str86U L1 L2 S) =
      (Subgroup.centralizer ((A ⊓ Q2 L1 L2 S : Subgroup G) : Set G)).relIndex
        (str86U L1 L2 S) := by
    rw [← relIndex_cjSub (A := Subgroup.centralizer (B1 : Set G))
      (B := str86U L1 L2 S) g, hC_B1, hUinv']
  rw [e1, e2, e3, hb, hUB0] at hmain
  have hrel1 : (Subgroup.centralizer ((A ⊓ Q2 L1 L2 S : Subgroup G) : Set G)).relIndex Zg ≤
      (2 ^ k) ^ 2 :=
    Nat.le_of_mul_le_mul_right hmain (by positivity)
  have hQ1Z : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hQ1gZ : cjSub g (Q1 L1 L2 S) ≤ Subgroup.centralizer (Zg : Set G) := by
    rw [hZg]
    exact cjSub_le_centralizer_of_le_centralizer hQ1Z
  obtain ⟨t1, ht1B0, ht1nc⟩ := Set.not_subset.mp hg
  have ht1Q1g : t1 ∉ cjSub g (Q1 L1 L2 S) := fun h => ht1nc (hQ1gZ h)
  have ht1A : t1 ∈ A := (inf_le_left : A ⊓ Q2 L1 L2 S ≤ A) ht1B0
  refine ⟨g⁻¹ * t1 * g, ?_, ?_, ?_, ?_⟩
  · rw [← hQ2inv]
    refine mem_cjSub.mpr ?_
    show g⁻¹⁻¹ * (g⁻¹ * t1 * g) * g⁻¹ ∈ Q2 L1 L2 S
    have he : g⁻¹⁻¹ * (g⁻¹ * t1 * g) * g⁻¹ = t1 := by group
    rw [he]
    exact ht1B0.2
  · intro hmem
    exact ht1Q1g (mem_cjSub.mpr hmem)
  · have ht1sq : t1 * t1 = 1 := by
      have h := hA.2.1.2 t1 ht1A
      simpa [pow_two] using h
    show (g⁻¹ * t1 * g) * (g⁻¹ * t1 * g) = 1
    calc (g⁻¹ * t1 * g) * (g⁻¹ * t1 * g) = g⁻¹ * (t1 * t1) * g := by group
      _ = 1 := by rw [ht1sq]; group
  · rw [← centralizer_zpowers_eq_singleton]
    have hZp : cjSub g (Subgroup.zpowers (g⁻¹ * t1 * g)) = Subgroup.zpowers t1 := by
      rw [cjSub, MonoidHom.map_zpowers]
      congr 1
      show (MulAut.conj g) (g⁻¹ * t1 * g) = t1
      rw [MulAut.conj_apply]
      group
    have e4 : (Subgroup.centralizer (Subgroup.zpowers (g⁻¹ * t1 * g) : Set G)).relIndex
        (Z1 L1 L2 S) =
        (Subgroup.centralizer (Subgroup.zpowers t1 : Set G)).relIndex Zg := by
      rw [← relIndex_cjSub (A := Subgroup.centralizer
        (Subgroup.zpowers (g⁻¹ * t1 * g) : Set G)) (B := Z1 L1 L2 S) g,
        B2F.cjSub_centralizer, hZp, ← hZg]
    rw [e4]
    exact (Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr ht1B0))
      (Subgroup.index_ne_zero_of_finite)).trans hrel1


theorem str86_caseIIa_two_z1_series
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2) :
    IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1 := by
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) := str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hB1 : VSzBig L1 ∨ VU3Big L1 := vSzBig_or_vU3Big_of_isSzU3Quot hq
  have hm2 : 2 ≤ m := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hqS : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hq
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1S : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hZ1H : Z1 L1 L2 S ≤ L1 ⊔ S := hZ1S.trans le_sup_right
  have hZ1e : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hZ1pg : IsPGroup 2 (Z1 L1 L2 S) := hZ1e.isPGroup
  have hnormZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (sup_le le_sup_left
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  have hNI : IsNormalIn (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hnormZ1 hg) x).mp hx⟩
  obtain ⟨c, hser⟩ :=
    D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S) (U := Z1 L1 L2 S)
      (Z1 L1 L2 S) hNI
  have hne0 : c ≠ 0 := by
    intro hc0
    have hcomm : ⁅Z1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
      D14.commutator_eq_bot_of_zero hZ1pg hser hc0
    have hO2C : oTwoUpper (L1 ⊔ S) ≤
        Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hmem : ⁅x, z⁆ ∈ (⊥ : Subgroup G) := by
        rw [← hcomm, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hx hz
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem.symm
    have hD : ∀ d ∈ (L1 ⊔ S), ∃ k : ℕ,
        d ^ 2 ^ k ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
      intro d hd
      obtain ⟨n, hn⟩ := exists_pow_mem_oTwoUpper (L1 ⊔ S) hd
      exact ⟨n, hO2C hn⟩
    have hle := (isTwoReducedIn_z1_of_caseII hF.toW hB hB1 hII).2.2.2 (L1 ⊔ S) le_rfl
      (fun x hx => Subgroup.le_normalizer hx) hD
    exact hII (by rwa [hsup1] at hle)
  obtain ⟨t, htQ2, htQ1, ht2, hbound⟩ :=
    str86_caseIIa_two_small_involution hF hB hk hFc hU3 hB2 hL2 hII hIIa hZ hc
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hB hm2 hL2
  have htH1 : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) (hQ2S htQ2)
  have ht2' : t * t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hpCore1, ht2]
    exact (Q1 L1 L2 S).one_mem
  have htO' : t ∉ pCoreOf 2 (L1 ⊔ S) := by rwa [hpCore1]
  have hpow := pow_sq_le_relIndex_centralizer hqS hZ1pg hZ1H hser htH1 ht2' htO'
  have hpow2 : ((2 ^ k) ^ 2) ^ c ≤ (2 ^ k) ^ 2 := by
    rw [centralizer_zpowers_eq_singleton] at hpow
    exact hpow.trans hbound
  have hcle : c ≤ 1 := by
    have hb : 1 < (2 ^ k) ^ 2 := by
      rw [← pow_mul]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    refine (Nat.pow_le_pow_iff_right hb).mp ?_
    simpa using hpow2
  have hc1 : c = 1 := by omega
  rwa [hc1] at hser

end CFSG.Quasithin.Stroth

end
