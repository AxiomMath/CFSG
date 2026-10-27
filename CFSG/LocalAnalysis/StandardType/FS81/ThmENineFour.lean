module

public import CFSG.Open.LocalVocabulary
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration
import CFSG.LieType.BorelTits.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Open.Defs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.SignalizerFunctorTheorem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private lemma conj_eq_self_of_mem_centralizer_zpowers {t c x : G}
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) (hx : x ∈ Subgroup.zpowers t) :
    c * x * c⁻¹ = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hct : c * t * c⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  rw [← conj_zpow, hct]

theorem pCoreOf_centralizer_le_zpowers_of_hyperplane_conj {t e : G} {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hE1 : E ≠ ⊥) (hEt : E ≤ Subgroup.centralizer ({t} : Set G))
    (hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) →
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.zpowers t)
    (hconj : ∀ H ∈ Coprime.hyperplanes 3 E,
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * e * c⁻¹ ∈ H) :
    pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ Subgroup.zpowers t := by
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  set P : Subgroup G := pCoreOf 2 C with hPdef
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hPC : P ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hCN : C ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hE3 : 3 ≤ Nat.card E := by
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hx3 : (x : G) ^ 3 = 1 := hE.2 x x.2
    have hxord : orderOf (x : G) = 3 := orderOf_eq_prime hx3 (by simpa using hx1)
    have hdvd : 3 ∣ Nat.card E := by
      rw [← hxord]
      exact Subgroup.orderOf_dvd_natCard E x.2
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := hEt.trans hCN
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes
    (p := 3) Nat.prime_three hE hE3 hEP hcop
  rw [← hgen]
  refine iSup_le fun B => iSup_le fun hB => ?_
  intro x hx
  obtain ⟨hxP, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨c, hcC, hcB⟩ := hconj B hB
  set y : G := c⁻¹ * x * c with hydef
  have hyP : y ∈ P := by
    rw [hydef]
    simpa using (Subgroup.mem_normalizer_iff.mp (hCN (C.inv_mem hcC)) x).mp hxP
  have hye : y ∈ Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxcomm : (c * e * c⁻¹) * x = x * (c * e * c⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hxB (c * e * c⁻¹) hcB
    calc y * e = c⁻¹ * (x * (c * e * c⁻¹)) * c := by
          rw [hydef]; group
      _ = c⁻¹ * ((c * e * c⁻¹) * x) * c := by rw [← hxcomm]
      _ = e * y := by rw [hydef]; group
  set Q : Subgroup G := P ⊓ Subgroup.centralizer ({e} : Set G) with hQdef
  have hQ2 : IsPGroup 2 Q := by
    rw [hQdef]
    exact hP2.to_le inf_le_left
  have hQD : Q ≤ C ⊓ Subgroup.centralizer ({e} : Set G) := by
    rw [hQdef]
    exact le_inf (inf_le_left.trans hPC) inf_le_right
  have hDnorm : C ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact (le_inf (inf_le_left.trans hCN) (inf_le_right.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := P)
        (K := Subgroup.centralizer ({e} : Set G)))
  have hyQ : y ∈ Q := by
    rw [hQdef]
    exact Subgroup.mem_inf.mpr ⟨hyP, hye⟩
  have hyZ : y ∈ Subgroup.zpowers t := hO2 Q hQ2 hQD hDnorm hyQ
  have hxeq : x = y := by
    calc x = c * y * c⁻¹ := by rw [hydef]; group
      _ = y := conj_eq_self_of_mem_centralizer_zpowers hcC hyZ
  rwa [hxeq]

theorem not_isCharTwoType_of_hyperplane_conj {t e : G} (ht : orderOf t = 2) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hE1 : E ≠ ⊥) (hEt : E ≤ Subgroup.centralizer ({t} : Set G))
    (hO2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) →
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
        Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.zpowers t)
    (hconj : ∀ H ∈ Coprime.hyperplanes 3 E,
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), c * e * c⁻¹ ∈ H) :
    ¬ IsCharTwoType G := by
  intro hchar
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  set Z : Subgroup G := Subgroup.zpowers t with hZdef
  set N : Subgroup G := Subgroup.normalizer (Z : Set G) with hNdef
  have ht2 : t ^ 2 = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht] at h
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hZ2 : IsPGroup 2 Z := by
    apply IsPGroup.of_card (p := 2) (G := Z) (n := 1)
    simp [hZdef, Nat.card_zpowers, ht]
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card Z = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hZdef, Nat.card_zpowers, ht] at hcard
    omega
  have hnorm : Subgroup.normalizer (Z : Set G) = C := by
    rw [hZdef, hCdef]
    have hconj : ∀ x : G, x * t = t * x → ∀ k : ℤ, x * t ^ k * x⁻¹ = t ^ k := by
      intro x hx k
      have h1 : x * t * x⁻¹ = t := by rw [hx, mul_inv_cancel_right]
      rw [← conj_zpow, h1]
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((h t).mp (Subgroup.mem_zpowers t))
      rw [zpow_eq_zpow_emod' k ht2] at hk
      simp only [Nat.cast_ofNat] at hk
      rcases Int.emod_two_eq_zero_or_one k with h0 | h0
      · exfalso
        rw [h0, zpow_zero] at hk
        apply ht1
        have h1 : x * t * x⁻¹ * x = x := by rw [← hk, one_mul]
        simpa [mul_assoc] using h1
      · rw [h0, zpow_one] at hk
        calc x * t = (x * t * x⁻¹) * x := by group
          _ = t * x := by rw [← hk]
    · intro hx y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨k, (hconj x hx k).symm⟩
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        have hk' : t ^ k = x * y * x⁻¹ := hk
        have hcomm := hconj x hx k
        show t ^ k = y
        have h2 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        rw [h2, ← hk']
        calc t ^ k = x⁻¹ * (x * t ^ k * x⁻¹) * x := by group
          _ = x⁻¹ * t ^ k * x := by rw [hcomm]
  have hNloc : IsTwoLocal N := ⟨Z, hZne, hZ2, hNdef⟩
  have hNC : N = C := hNdef.trans hnorm
  have hPN : pCoreOf 2 N ≤ Subgroup.zpowers t := by
    rw [hNC]
    exact pCoreOf_centralizer_le_zpowers_of_hyperplane_conj hE hE1 hEt hO2 hconj
  have hEN : E ≤ N := by
    rw [hNC]
    exact hEt
  have hEcent : E ≤ Subgroup.centralizer (pCoreOf 2 N : Set G) := by
    intro x hxE
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    have hyZ : y ∈ Subgroup.zpowers t := hPN hyP
    have hxy : x * y = y * x := by
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by
              rw [conj_eq_self_of_mem_centralizer_zpowers (hEt hxE) hyZ]
    exact hxy.symm
  have hEcore : E ≤ pCoreOf 2 N := by
    intro x hxE
    exact hchar N hNloc (Subgroup.mem_inf.mpr ⟨hEN hxE, hEcent hxE⟩)
  have hEZ : E ≤ Subgroup.zpowers t := hEcore.trans hPN
  have hEbot : E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxE
    have hx2 : x ^ 2 = 1 := by
      have hdvd : orderOf x ∣ 2 := by
        have h := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers t) (hEZ hxE)
        rwa [Nat.card_zpowers, ht] at h
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have ho1 : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2) with h1 | h2
      · exact h1
      · rw [h2] at hdvd3
        norm_num at hdvd3
    exact orderOf_eq_one_iff.mp ho1
  exact hE1 hEbot

end CFSG.StandardType.FrameRoute.FS81

end
