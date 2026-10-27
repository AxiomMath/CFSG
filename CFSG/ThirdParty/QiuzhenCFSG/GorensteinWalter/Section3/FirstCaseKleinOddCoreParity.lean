module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreFiberCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem even_card_of_mem_involution
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) {s : G} (hsM : s ∈ M) (hs : IsInvolution s) :
    Even (Nat.card M) := by
  have hdiv : orderOf s ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hsM
  have horder : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  rw [horder] at hdiv
  exact even_iff_two_dvd.mpr hdiv

/-!
The order-three odd-core fibre from restriction (6) is normalized by the
centralizing involution selected there.  Consequently both its centralizer
and its normalizer inside `Ĥ` have even order, exactly the parity interface
needed by restriction (7).
-/

public theorem firstCase_klein_oddCore_parity
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {w s : G} (hw : IsInvolution w) (hwH : w ∉ c.Hhat)
    (hs : IsInvolution s)
    (hsD : s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat w))
    (hsw : s * w = w * s)
    {x : G}
    (hxO : x ∈ oddCoreOf
      (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G))
    (hxne : x ≠ 1) (hxord : orderOf x = 3)
    (hxinv : x ∈ invertedElements
      (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w)
    (hfib : Nat.card {z : G // z ∈ invertedElements
      (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w} = 3) :
    ∃ X : Subgroup G,
      X ≠ ⊥ ∧ X ≤ c.Hhat ∧ Nat.Coprime 2 (Nat.card X) ∧
      (∀ z : G, z ∈ X → z ∈ invertedElements c.Hhat w) ∧
      Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
      Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) := by
  classical
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat w
  let O : Subgroup G := oddCoreOf D
  have hDle : D ≤ c.Hhat := inf_le_left
  have hOleD : O ≤ D := by
    dsimp [O, oddCoreOf]
    exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
  have hOnormD : IsNormalIn O D := by
    refine ⟨hOleD, ?_⟩
    intro d hd o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(⟨d, hd⟩ : D) * o0 *
      (⟨d, hd⟩ : D)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := D)).conj_mem o0 ho0
      (⟨d, hd⟩ : D)
  have hsH : s ∈ c.Hhat := hDle hsD
  have hsNormO : s ∈ Subgroup.normalizer (O : Set G) :=
    (le_normalizer_of_isNormalIn hOnormD) hsD
  let R : Subgroup G := Subgroup.zpowers x
  have hRleO : R ≤ O := by
    apply (Subgroup.zpowers_le).2
    exact hxO
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hRin : ∀ z : G, z ∈ R → z ∈ invertedElements O w := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
    rw [← hn]
    refine ⟨O.zpow_mem hxO n, ?_⟩
    calc
      w * x ^ n * w⁻¹ = (w * x * w⁻¹) ^ n := by exact conj_zpow.symm
      _ = (x⁻¹) ^ n := by rw [hxinv.2]
      _ = (x ^ n)⁻¹ := by simp
  let F : Type u := {z : G // z ∈ invertedElements O w}
  let e : R → F := fun z => ⟨z, hRin z z.2⟩
  let : Fintype R := Fintype.ofFinite R
  let : Fintype F := Fintype.ofFinite F
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : F => (z : G)) hab
  have he_card : Fintype.card R = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hRcard.trans hfib.symm
  have he_bij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2 ⟨he_inj, he_card⟩
  have hRconj : ∀ z : G, z ∈ R → s * z * s⁻¹ ∈ R := by
    intro z hz
    have hzF : z ∈ invertedElements O w := hRin z hz
    have hconjO : s * z * s⁻¹ ∈ O :=
      ((Subgroup.mem_normalizer_iff.mp hsNormO) z).1 (hRleO hz)
    have hconjInv : w * (s * z * s⁻¹) * w⁻¹ =
        (s * z * s⁻¹)⁻¹ := by
      calc
        w * (s * z * s⁻¹) * w⁻¹ =
            (w * s) * z * (w * s)⁻¹ := by group
        _ = (s * w) * z * (s * w)⁻¹ := by rw [← hsw]
        _ = s * (w * z * w⁻¹) * s⁻¹ := by group
        _ = s * z⁻¹ * s⁻¹ := by rw [hzF.2]
        _ = (s * z * s⁻¹)⁻¹ := by group
    obtain ⟨r, hr⟩ := he_bij.2 ⟨s * z * s⁻¹, ⟨hconjO, hconjInv⟩⟩
    have hrEq : (r : G) = s * z * s⁻¹ :=
      congrArg (fun q : F => (q : G)) hr
    exact hrEq.symm ▸ r.2
  have hconjX : s * x * s⁻¹ ∈ R := hRconj x (Subgroup.mem_zpowers x)
  have hconjXne : s * x * s⁻¹ ≠ 1 := by
    intro h
    apply hxne
    calc
      x = s⁻¹ * (s * x * s⁻¹) * s := by group
      _ = 1 := by rw [h]; simp
  have hconj_cases : s * x * s⁻¹ = x ∨ s * x * s⁻¹ = x⁻¹ := by
    rcases Subgroup.mem_zpowers_iff.mp hconjX with ⟨n, hn⟩
    have hmod : n % (3 : ℤ) = 0 ∨ n % (3 : ℤ) = 1 ∨ n % (3 : ℤ) = 2 := by
      have hnonneg : 0 ≤ n % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
      have hlt : n % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
      omega
    have hpowmod : x ^ (n % (3 : ℤ)) = s * x * s⁻¹ := by
      calc
        x ^ (n % (3 : ℤ)) = x ^ n := by
          simpa [hxord] using zpow_mod_orderOf x n
        _ = s * x * s⁻¹ := hn
    rcases hmod with h0 | h1 | h2
    · exfalso
      apply hconjXne
      simpa [h0] using hpowmod.symm
    · left
      simpa [h1] using hpowmod.symm
    · right
      have hx2 : x ^ (2 : ℕ) = x⁻¹ := by
        have hcube : x ^ 3 = 1 := by
          rw [← hxord]
          exact pow_orderOf_eq_one x
        have hmul : x ^ (2 : ℕ) * x = 1 := by
          calc
            x ^ (2 : ℕ) * x = x ^ 3 := by group
            _ = 1 := hcube
        exact eq_inv_of_mul_eq_one_left hmul
      have hx2z : x ^ (2 : ℤ) = x⁻¹ := by
        rw [zpow_ofNat]
        exact hx2
      simpa [h2, hx2z] using hpowmod.symm
  have hXinv : ∀ z : G, z ∈ R → z ∈ invertedElements c.Hhat w := by
    intro z hz
    exact ⟨(hOleD.trans inf_le_left) (hRleO hz), (hRin z hz).2⟩
  have hXne : R ≠ ⊥ := by
    intro hbot
    have : x = 1 := by
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        rw [← hbot]
        exact Subgroup.mem_zpowers x
      exact Subgroup.mem_bot.mp hxbot
    exact hxne this
  have hXodd : Nat.Coprime 2 (Nat.card R) := by rw [hRcard]; norm_num
  have hNormR : s ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hRconj z
    · intro hz
      have hback := hRconj (s * z * s⁻¹) hz
      have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      have heq : s * (s * z * s⁻¹) * s⁻¹ = z := by
        rw [hsinv]
        calc
          s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by rw [hs2]; simp
      rw [heq] at hback
      exact hback
  have hNormEven : Even (Nat.card
      (Subgroup.normalizer (R : Set G) ⊓ c.Hhat : Subgroup G)) :=
    even_card_of_mem_involution _ ⟨hNormR, hsH⟩ hs
  have hCentEven : Even (Nat.card (Subgroup.centralizer (R : Set G))) := by
    have hcentralizer_of_generator : ∀ z : G, z ∈ R →
        s * z * s⁻¹ = z → s * z = z * s := by
      intro z hz hfix
      have hmul := congrArg (fun q : G => q * s) hfix
      simpa [mul_assoc] using hmul
    rcases hconj_cases with hfix | hinv
    · have hsCent : s ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hcentralizer_of_generator z hz (by
          rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
          rw [← hn, ← conj_zpow, hfix])).symm
      exact even_card_of_mem_involution _ hsCent hs
    · let sw : G := s * w
      have hswI : IsInvolution sw := by
        refine ⟨?_, ?_⟩
        · intro h
          have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
          dsimp [sw] at h
          have hw_eq : w = s := by
            calc
              w = (s * s) * w := by rw [hs2]; simp
              _ = s * (s * w) := by group
              _ = s * 1 := by rw [h]
              _ = s := by simp
          exact hwH (hw_eq ▸ hsH)
        · have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
          have hw2 : w * w = 1 := by simpa [pow_two] using hw.2
          calc
            (s * w) ^ 2 = s * (w * s) * w := by simp [pow_two, mul_assoc]
            _ = s * (s * w) * w := by rw [hsw]
            _ = (s * s) * (w * w) := by group
            _ = 1 := by rw [hs2, hw2]; simp
      have hswCent : sw ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
        have hconj_sw : (s * w) * x * (s * w)⁻¹ = x := by
          calc
            (s * w) * x * (s * w)⁻¹ =
                s * (w * x * w⁻¹) * s⁻¹ := by group
            _ = s * x⁻¹ * s⁻¹ := by rw [hxinv.2]
            _ = x := by
              calc
                s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
                _ = (x⁻¹)⁻¹ := by rw [hinv]
                _ = x := by simp
        have hconj_pow : (s * w) * x ^ n * (s * w)⁻¹ = x ^ n := by
          rw [← conj_zpow, hconj_sw]
        dsimp [sw]
        rw [← hn]
        have hcomm : (s * w) * x ^ n = x ^ n * (s * w) := by
          calc
            (s * w) * x ^ n =
                ((s * w) * x ^ n * (s * w)⁻¹) * (s * w) := by group
            _ = x ^ n * (s * w) := by rw [hconj_pow]
        exact hcomm.symm
      exact even_card_of_mem_involution _ hswCent hswI
  exact ⟨R, hXne, hRleO.trans (hOleD.trans inf_le_left), hXodd,
    hXinv, hCentEven, hNormEven⟩

end CFSG.GorensteinWalter
